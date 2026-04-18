// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::format_ident;
use quote::quote;
use std::collections::HashSet;
use syn::{Data, DeriveInput, Fields, Type, parse_macro_input};

// ===========================================================================
// RecFunctor — derive for a single functor type
// ===========================================================================

#[proc_macro_derive(RecFunctor)]
pub fn derive_rec_functor(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match derive_rec_functor_impl(&input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn derive_rec_functor_impl(input: &DeriveInput) -> syn::Result<TokenStream2> {
    let enum_name = &input.ident;
    let data = match &input.data {
        Data::Enum(data) => data,
        _ => {
            return Err(syn::Error::new_spanned(
                input,
                "RecFunctor only works on enums",
            ));
        }
    };
    let type_param =
        input.generics.type_params().next().ok_or_else(|| {
            syn::Error::new_spanned(input, "RecFunctor requires one type parameter")
        })?;
    let r_ident = &type_param.ident;
    let mut arms = Vec::new();
    let mut ref_arms = Vec::new();
    for variant in &data.variants {
        let vname = &variant.ident;
        match &variant.fields {
            Fields::Unit => {
                arms.push(quote! { #enum_name::#vname => #enum_name::#vname });
                ref_arms.push(quote! { #enum_name::#vname => #enum_name::#vname });
            }
            Fields::Unnamed(fields) => {
                let bindings: Vec<_> = (0..fields.unnamed.len())
                    .map(|i| format_ident!("f{}", i))
                    .collect();
                let is_r: Vec<bool> = fields
                    .unnamed
                    .iter()
                    .map(|f| {
                        let Type::Path(tp) = &f.ty else { return false };
                        tp.path.is_ident(r_ident)
                    })
                    .collect();
                let mapped: Vec<TokenStream2> = bindings
                    .iter()
                    .zip(is_r.iter())
                    .map(|(b, &is)| {
                        if is {
                            quote! { __f(#b) }
                        } else {
                            quote! { #b }
                        }
                    })
                    .collect();
                let ref_mapped: Vec<TokenStream2> = bindings
                    .iter()
                    .zip(is_r.iter())
                    .map(|(b, &is)| {
                        if is {
                            quote! { __f(#b) }
                        } else {
                            quote! { #b.clone() }
                        }
                    })
                    .collect();
                arms.push(quote! { #enum_name::#vname(#(#bindings),*) => #enum_name::#vname(#(#mapped),*) });
                ref_arms.push(quote! { #enum_name::#vname(#(#bindings),*) => #enum_name::#vname(#(#ref_mapped),*) });
            }
            Fields::Named(_) => {
                return Err(syn::Error::new_spanned(
                    variant,
                    "named fields not supported",
                ));
            }
        }
    }
    let mut children_arms = Vec::new();
    for variant in &data.variants {
        let vname = &variant.ident;
        match &variant.fields {
            Fields::Unit => children_arms.push(quote! { #enum_name::#vname => {} }),
            Fields::Unnamed(fields) => {
                let bindings: Vec<_> = (0..fields.unnamed.len())
                    .map(|i| format_ident!("f{}", i))
                    .collect();
                let is_r: Vec<bool> = fields
                    .unnamed
                    .iter()
                    .map(|f| {
                        let Type::Path(tp) = &f.ty else { return false };
                        tp.path.is_ident(r_ident)
                    })
                    .collect();
                let pushes: Vec<TokenStream2> = bindings
                    .iter()
                    .zip(is_r.iter())
                    .filter_map(|(b, &is)| {
                        if is {
                            Some(quote! { __buf.push(*#b); })
                        } else {
                            None
                        }
                    })
                    .collect();
                children_arms
                    .push(quote! { #enum_name::#vname(#(#bindings),*) => { #(#pushes)* } });
            }
            Fields::Named(_) => {}
        }
    }

    Ok(quote! {
        impl<#r_ident> ::semi_persistent_traversals::Functor<#r_ident> for #enum_name<#r_ident> {
            type Mapped<__S> = #enum_name<__S>;
            fn map<__S>(self, mut __f: impl FnMut(#r_ident) -> __S) -> #enum_name<__S> {
                match self { #(#arms),* }
            }
            fn map_ref<__S>(&self, mut __f: impl FnMut(&#r_ident) -> __S) -> #enum_name<__S> {
                match self { #(#ref_arms),* }
            }
            fn children_into(&self, __buf: &mut ::smallvec::SmallVec<[#r_ident; 8]>) where #r_ident: Copy {
                __buf.clear();
                match self { #(#children_arms),* }
            }
        }
    })
}

// ===========================================================================
// rec_family!
// ===========================================================================

#[proc_macro]
pub fn rec_family(input: TokenStream) -> TokenStream {
    let raw = parse_macro_input!(input as RawFamilyDef);
    match resolve_and_gen(&raw) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

struct RawFamilyDef {
    vis: syn::Visibility,
    fam_name: syn::Ident,
    sorts: Vec<RawSortDef>,
}
struct RawSortDef {
    name: syn::Ident,
    variants: Vec<RawVariantDef>,
}
struct RawVariantDef {
    name: syn::Ident,
    fields: Vec<syn::Type>,
}

impl syn::parse::Parse for RawFamilyDef {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let vis: syn::Visibility = input.parse()?;
        let kw: syn::Ident = input.parse()?;
        if kw != "family" {
            return Err(syn::Error::new(kw.span(), "expected `family`"));
        }
        let fam_name: syn::Ident = input.parse()?;
        let _: syn::Token![;] = input.parse()?;
        let mut sorts = Vec::new();
        while !input.is_empty() {
            let _: syn::Token![enum] = input.parse()?;
            let name: syn::Ident = input.parse()?;
            let content;
            syn::braced!(content in input);
            let mut variants = Vec::new();
            while !content.is_empty() {
                let vname: syn::Ident = content.parse()?;
                let fields = if content.peek(syn::token::Paren) {
                    let inner;
                    syn::parenthesized!(inner in content);
                    let p: syn::punctuated::Punctuated<syn::Type, syn::Token![,]> =
                        inner.parse_terminated(syn::Type::parse, syn::Token![,])?;
                    p.into_iter().collect()
                } else {
                    Vec::new()
                };
                variants.push(RawVariantDef {
                    name: vname,
                    fields,
                });
                if content.peek(syn::Token![,]) {
                    let _: syn::Token![,] = content.parse()?;
                }
            }
            sorts.push(RawSortDef { name, variants });
        }
        if sorts.len() < 2 {
            return Err(syn::Error::new(
                fam_name.span(),
                "a family needs at least 2 sorts",
            ));
        }
        Ok(RawFamilyDef {
            vis,
            fam_name,
            sorts,
        })
    }
}

// ---------------------------------------------------------------------------
// Resolution
// ---------------------------------------------------------------------------

#[derive(Clone)]
#[allow(clippy::large_enum_variant)]
enum FieldKind {
    Child(usize),
    VariadicChild(usize),
    Data(syn::Type),
}

struct ResolvedVariant {
    name: syn::Ident,
    fields: Vec<FieldKind>,
}
struct ResolvedSort {
    name: syn::Ident,
    sort_idx: usize,
    variants: Vec<ResolvedVariant>,
}

fn resolve_fields(raw: &RawFamilyDef) -> Vec<ResolvedSort> {
    let sort_names: Vec<String> = raw.sorts.iter().map(|s| s.name.to_string()).collect();
    raw.sorts
        .iter()
        .enumerate()
        .map(|(si, sort)| {
            let variants = sort
                .variants
                .iter()
                .map(|v| {
                    let fields = v
                        .fields
                        .iter()
                        .map(|ty| {
                            if let Type::Path(tp) = ty {
                                // Check Variadic<SortName>
                                if let Some(seg) = tp.path.segments.last()
                                    && seg.ident == "Variadic"
                                    && let syn::PathArguments::AngleBracketed(args) = &seg.arguments
                                    && let Some(syn::GenericArgument::Type(Type::Path(inner))) =
                                        args.args.first()
                                    && let Some(inner_ident) = inner.path.get_ident()
                                    && let Some(idx) =
                                        sort_names.iter().position(|s| inner_ident == s)
                                {
                                    return FieldKind::VariadicChild(idx);
                                }
                                // Check plain SortName
                                if let Some(ident) = tp.path.get_ident()
                                    && let Some(idx) = sort_names.iter().position(|s| ident == s)
                                {
                                    return FieldKind::Child(idx);
                                }
                            }
                            FieldKind::Data(ty.clone())
                        })
                        .collect();
                    ResolvedVariant {
                        name: v.name.clone(),
                        fields,
                    }
                })
                .collect();
            ResolvedSort {
                name: sort.name.clone(),
                sort_idx: si,
                variants,
            }
        })
        .collect()
}

fn used_sort_params(sort: &ResolvedSort) -> HashSet<usize> {
    let mut used = HashSet::new();
    for v in &sort.variants {
        for f in &v.fields {
            match f {
                FieldKind::Child(i) | FieldKind::VariadicChild(i) => {
                    used.insert(*i);
                }
                _ => {}
            }
        }
    }
    used
}

// ---------------------------------------------------------------------------
// Code generation
// ---------------------------------------------------------------------------

fn resolve_and_gen(raw: &RawFamilyDef) -> syn::Result<TokenStream2> {
    let sorts = resolve_fields(raw);
    let fam_name = &raw.fam_name;
    let n = sorts.len();
    let vis: TokenStream2 = {
        let v = &raw.vis;
        quote! { #v }
    };

    // All N sort type params
    let sp: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__S{}", i)).collect();
    let result_name = format_ident!("{}Res", fam_name);
    let cata_fn = format_ident!(
        "fold_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let fold_all_fn = format_ident!(
        "fold_all_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let all_usize: Vec<TokenStream2> = (0..n).map(|_| quote! { usize }).collect();

    // Per-sort: which params does each sort actually use?
    let sort_used: Vec<HashSet<usize>> = sorts.iter().map(used_sort_params).collect();
    // Per-sort: the subset of type params used
    let sort_own_params: Vec<Vec<&syn::Ident>> = sort_used
        .iter()
        .map(|used| {
            let mut indices: Vec<usize> = used.iter().copied().collect();
            indices.sort();
            indices.iter().map(|&i| &sp[i]).collect()
        })
        .collect();

    // ---- Coproduct enum <__S0, __S1, ...> ----------------------------------
    let mut coprod_variants: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            sort.variants.iter().map(|v| {
                let pv = format_ident!("{}{}", sort.name, v.name);
                let tys: Vec<TokenStream2> = v.fields.iter().map(|fk| fk_type(fk, &sp)).collect();
                if tys.is_empty() {
                    quote! { #pv }
                } else {
                    quote! { #pv(#(#tys),*) }
                }
            })
        })
        .collect();

    // Coproduct may not use all params if some sorts are isolated.
    // Add PhantomData variant for any unused params.
    let coprod_used: HashSet<usize> = sorts
        .iter()
        .flat_map(|s| {
            s.variants.iter().flat_map(|v| {
                v.fields.iter().filter_map(|f| match f {
                    FieldKind::Child(i) | FieldKind::VariadicChild(i) => Some(*i),
                    _ => None,
                })
            })
        })
        .collect();
    let coprod_unused: Vec<usize> = (0..n).filter(|i| !coprod_used.contains(i)).collect();
    if !coprod_unused.is_empty() {
        let phantom_tys: Vec<TokenStream2> = coprod_unused
            .iter()
            .map(|i| {
                let p = &sp[*i];
                quote! { std::marker::PhantomData<#p> }
            })
            .collect();
        coprod_variants.push(quote! {
            #[doc(hidden)]
            __Phantom(#(#phantom_tys),*)
        });
    }
    let _has_phantom = !coprod_unused.is_empty();

    // ---- Per-sort enums: only their own params -----------------------------
    let sort_enums: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(si, sort)| {
            let sn = &sort.name;
            let own = &sort_own_params[si];
            let vs: Vec<TokenStream2> = sort
                .variants
                .iter()
                .map(|v| {
                    let vn = &v.name;
                    let tys: Vec<TokenStream2> =
                        v.fields.iter().map(|fk| fk_type(fk, &sp)).collect();
                    if tys.is_empty() {
                        quote! { #vn }
                    } else {
                        quote! { #vn(#(#tys),*) }
                    }
                })
                .collect();
            quote! {
                #[derive(Clone, PartialEq, Eq, Hash, Debug)]
                #vis enum #sn<#(#own),*> { #(#vs),* }
            }
        })
        .collect();

    // ---- Functor<R> for Fam<R,R,...> (Arena compat) ------------------------
    let all_r: Vec<TokenStream2> = (0..n).map(|_| quote! { R }).collect();
    let all_s: Vec<TokenStream2> = (0..n).map(|_| quote! { __S }).collect();
    let mut functor_arms: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            sort.variants.iter().map(|v| {
                map_arm(
                    fam_name,
                    &format_ident!("{}{}", sort.name, v.name),
                    &v.fields,
                )
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        functor_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    let mut functor_ref_arms: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            sort.variants.iter().map(|v| {
                map_ref_arm(
                    fam_name,
                    &format_ident!("{}{}", sort.name, v.name),
                    &v.fields,
                )
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        functor_ref_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    let mut children_into_arms: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            sort.variants.iter().map(|v| {
                children_into_arm(
                    fam_name,
                    &format_ident!("{}{}", sort.name, v.name),
                    &v.fields,
                )
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        children_into_arms.push(quote! { #fam_name::__Phantom(..) => {} });
    }

    // ---- sort_of -----------------------------------------------------------
    let mut sort_of_arms: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            sort.variants.iter().map(move |v| {
                let pv = format_ident!("{}{}", sort.name, v.name);
                let si = sort.sort_idx;
                if v.fields.is_empty() {
                    quote! { #fam_name::#pv => #si }
                } else {
                    quote! { #fam_name::#pv(..) => #si }
                }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        sort_of_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    // ---- dispatch (uniform: all sorts -> T) --------------------------------
    // Per-sort enums have their own params. When dispatching from the coproduct
    // (which has all N params), we need to construct per-sort values.
    // But the per-sort enum only has the params it uses.
    // In the dispatch context, all params are available from the coproduct.
    let dispatch_params: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(si, sort)| {
            let sn = &sort.name;
            let own = &sort_own_params[si];
            let p = format_ident!("__f_{}", sn.to_string().to_lowercase());
            quote! { mut #p: impl FnMut(#sn<#(#own),*>) -> __T }
        })
        .collect();
    let mut dispatch_arms: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            let p = format_ident!("__f_{}", sort.name.to_string().to_lowercase());
            let sn = &sort.name;
            sort.variants.iter().map(move |v| {
                let pv = format_ident!("{}{}", sort.name, v.name);
                let vn = &v.name;
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                if bs.is_empty() {
                    quote! { #fam_name::#pv => #p(#sn::#vn) }
                } else {
                    quote! { #fam_name::#pv(#(#bs),*) => #p(#sn::#vn(#(#bs),*)) }
                }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        dispatch_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    // ---- multi_map: per-sort child mapping ---------------------------------
    let dp: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__D{}", i)).collect();
    let mm_fn_params: Vec<TokenStream2> = (0..n)
        .map(|i| {
            let p = format_ident!("__mf{}", i);
            let s = &sp[i];
            let d = &dp[i];
            quote! { mut #p: impl FnMut(#s) -> #d }
        })
        .collect();
    let mut mm_arms: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            sort.variants.iter().map(|v| {
                let pv = format_ident!("{}{}", sort.name, v.name);
                if v.fields.is_empty() {
                    return quote! { #fam_name::#pv => #fam_name::#pv };
                }
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                let mapped: Vec<TokenStream2> = bs
                    .iter()
                    .zip(v.fields.iter())
                    .map(|(b, fk)| match fk {
                        FieldKind::Child(si) => {
                            let f = format_ident!("__mf{}", si);
                            quote! { #f(#b) }
                        }
                        FieldKind::VariadicChild(si) => {
                            let f = format_ident!("__mf{}", si);
                            quote! { #b.map_all(&mut #f) }
                        }
                        FieldKind::Data(_) => quote! { #b },
                    })
                    .collect();
                quote! { #fam_name::#pv(#(#bs),*) => #fam_name::#pv(#(#mapped),*) }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        mm_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    // ---- multi_map_ref: borrow data, map children by ref -------------------
    let mm_ref_fn_params: Vec<TokenStream2> = (0..n)
        .map(|i| {
            let p = format_ident!("__mf{}", i);
            let s = &sp[i];
            let d = &dp[i];
            quote! { mut #p: impl FnMut(&#s) -> #d }
        })
        .collect();
    let mut mm_ref_arms: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            sort.variants.iter().map(|v| {
                let pv = format_ident!("{}{}", sort.name, v.name);
                if v.fields.is_empty() {
                    return quote! { #fam_name::#pv => #fam_name::#pv };
                }
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                let mapped: Vec<TokenStream2> = bs
                    .iter()
                    .zip(v.fields.iter())
                    .map(|(b, fk)| match fk {
                        FieldKind::Child(si) => {
                            let f = format_ident!("__mf{}", si);
                            quote! { #f(#b) }
                        }
                        FieldKind::VariadicChild(si) => {
                            let f = format_ident!("__mf{}", si);
                            quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(&mut #f).collect()) }
                        }
                        FieldKind::Data(_) => quote! { #b.clone() },
                    })
                    .collect();
                quote! { #fam_name::#pv(#(#bs),*) => #fam_name::#pv(#(#mapped),*) }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        mm_ref_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    // ---- dispatch_ref: not needed, multi_map_ref + dispatch is sufficient --

    // ---- Result enum -------------------------------------------------------
    let ap: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();
    let res_variants: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let sn = &sort.name;
            let a = &ap[i];
            quote! { #sn(#a) }
        })
        .collect();
    let unwrap_fns: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let sn = &sort.name;
            let a = &ap[i];
            let fn_name = format_ident!("unwrap_{}", sort.name.to_string().to_lowercase());
            let fn_ref = format_ident!("unwrap_{}_ref", sort.name.to_string().to_lowercase());
            quote! {
                #vis fn #fn_name(self) -> #a {
                    match self { #result_name::#sn(v) => v, _ => panic!("sort mismatch") }
                }
                #vis fn #fn_ref(&self) -> &#a {
                    match self { #result_name::#sn(v) => v, _ => panic!("sort mismatch") }
                }
            }
        })
        .collect();

    // ---- Helper: sort's own __A params (sorted) ------------------------------
    let sort_own_as: Vec<Vec<&syn::Ident>> = (0..n)
        .map(|i| {
            let mut indices: Vec<usize> = sort_used[i].iter().copied().collect();
            indices.sort();
            indices.iter().map(|&j| &ap[j]).collect()
        })
        .collect();

    // ---- Helper: build algebra params for a scheme --------------------------
    // child_wrapper: given sort index j, wraps __Aj in the child type
    //   cata: __Aj, para: (Id, __Aj), histo: &Ann<__Aj>
    let make_alg_params = |child_wrapper: &dyn Fn(usize) -> TokenStream2| -> Vec<TokenStream2> {
        sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| {
                let sn = &sort.name;
                let p = format_ident!("__alg{}", i);
                let a = &ap[i];
                let own: Vec<TokenStream2> = {
                    let mut indices: Vec<usize> = sort_used[i].iter().copied().collect();
                    indices.sort();
                    indices.iter().map(|&j| child_wrapper(j)).collect()
                };
                quote! { #p: impl Fn(#sn<#(#own),*>) -> #a }
            })
            .collect()
    };

    // ---- cata_family -------------------------------------------------------
    let alg_params = make_alg_params(&|j| {
        let a = &ap[j];
        quote! { #a }
    });

    // ---- ref algebra params: children are &Aj --------------------------------
    let alg_ref_params: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let sn = &sort.name;
            let p = format_ident!("__alg{}", i);
            let a = &ap[i];
            let own: Vec<TokenStream2> = {
                let mut indices: Vec<usize> = sort_used[i].iter().copied().collect();
                indices.sort();
                indices
                    .iter()
                    .map(|&j| {
                        let aj = &ap[j];
                        quote! { &'__rf #aj }
                    })
                    .collect()
            };
            quote! { #p: impl for<'__rf> Fn(#sn<#(#own),*>) -> #a }
        })
        .collect();

    let fold_all_ref_fn = format_ident!(
        "fold_all_ref_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let fold_ref_fn = format_ident!(
        "fold_ref_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );

    // ---- fused fold_all arms: match on &node, look up per-sort results, call algebra ----
    let sort_res_names: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__r{}", i)).collect();
    let _sort_names: Vec<&syn::Ident> = sorts.iter().map(|s| &s.name).collect();

    let mut fused_fold_all_arms: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .flat_map(|(si, sort)| {
            let alg = format_ident!("__alg{}", si);
            let sn = sort.name.clone();
            let res_name = sort_res_names[si].clone();
            let srn = sort_res_names.clone();
            sort.variants.iter().map(move |v| {
                let pv = format_ident!("{}{}", sn, v.name);
                let vn = &v.name;
                if v.fields.is_empty() {
                    return quote! { #fam_name::#pv => { #res_name[__i] = Some(#alg(#sn::#vn)); } };
                }
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                let mapped: Vec<TokenStream2> = bs
                    .iter()
                    .zip(v.fields.iter())
                    .map(|(b, fk)| match fk {
                        FieldKind::Child(child_sort) => {
                            let cr = &srn[*child_sort];
                            quote! { #cr[*#b].as_ref().unwrap().clone() }
                        }
                        FieldKind::VariadicChild(child_sort) => {
                            let cr = &srn[*child_sort];
                            quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| #cr[*__c].as_ref().unwrap().clone()).collect()) }
                        }
                        FieldKind::Data(_) => quote! { #b.clone() },
                    })
                    .collect();
                quote! { #fam_name::#pv(#(#bs),*) => { #res_name[__i] = Some(#alg(#sn::#vn(#(#mapped),*))); } }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        fused_fold_all_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    // ---- fused fold_all single-vec arms: match on &node, construct sort enum directly ----
    let mut fused_fold_all_single_arms: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .flat_map(|(si, sort)| {
            let alg = format_ident!("__alg{}", si);
            let sn = sort.name.clone();
            let res_sn = sort.name.clone();
            let child_fn_refs: Vec<syn::Ident> = (0..n)
                .map(|j| format_ident!("unwrap_{}_ref", sorts[j].name.to_string().to_lowercase()))
                .collect();
            let rn = result_name.clone();
            sort.variants.iter().map(move |v| {
                let pv = format_ident!("{}{}", sn, v.name);
                let vn = &v.name;
                if v.fields.is_empty() {
                    return quote! { #fam_name::#pv => { __res.push(#rn::#res_sn(#alg(#sn::#vn))); } };
                }
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                let mapped: Vec<TokenStream2> = bs
                    .iter()
                    .zip(v.fields.iter())
                    .map(|(b, fk)| match fk {
                        FieldKind::Child(child_sort) => {
                            let fr = &child_fn_refs[*child_sort];
                            quote! { __res[*#b].#fr().clone() }
                        }
                        FieldKind::VariadicChild(child_sort) => {
                            let fr = &child_fn_refs[*child_sort];
                            quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| __res[*__c].#fr().clone()).collect()) }
                        }
                        FieldKind::Data(_) => quote! { #b.clone() },
                    })
                    .collect();
                quote! { #fam_name::#pv(#(#bs),*) => { __res.push(#rn::#res_sn(#alg(#sn::#vn(#(#mapped),*)))); } }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        fused_fold_all_single_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }
    let mut fused_fold_arms: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .flat_map(|(si, sort)| {
            let alg = format_ident!("__alg{}", si);
            let sn = sort.name.clone();
            let res_name = sort_res_names[si].clone();
            let srn = sort_res_names.clone();
            sort.variants.iter().map(move |v| {
                let pv = format_ident!("{}{}", sn, v.name);
                let vn = &v.name;
                if v.fields.is_empty() {
                    return quote! { #fam_name::#pv => { #res_name[__i] = Some(#alg(#sn::#vn)); } };
                }
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                let mapped: Vec<TokenStream2> = bs
                    .iter()
                    .zip(v.fields.iter())
                    .map(|(b, fk)| match fk {
                        FieldKind::Child(child_sort) => {
                            let cr = &srn[*child_sort];
                            quote! { #cr[*#b].as_ref().unwrap().clone() }
                        }
                        FieldKind::VariadicChild(child_sort) => {
                            let cr = &srn[*child_sort];
                            quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| #cr[*__c].as_ref().unwrap().clone()).collect()) }
                        }
                        FieldKind::Data(_) => quote! { #b.clone() },
                    })
                    .collect();
                quote! { #fam_name::#pv(#(#bs),*) => { #res_name[__i] = Some(#alg(#sn::#vn(#(#mapped),*))); } }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        fused_fold_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    // ---- fused ref arms: zero-clone, pass &A to algebra ----
    let mut fused_ref_all_arms: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .flat_map(|(si, sort)| {
            let alg = format_ident!("__alg{}", si);
            let sn = sort.name.clone();
            let res_sn = sort.name.clone();
            let child_fn_refs: Vec<syn::Ident> = (0..n)
                .map(|j| format_ident!("unwrap_{}_ref", sorts[j].name.to_string().to_lowercase()))
                .collect();
            let rn = result_name.clone();
            sort.variants.iter().map(move |v| {
                let pv = format_ident!("{}{}", sn, v.name);
                let vn = &v.name;
                if v.fields.is_empty() {
                    return quote! { #fam_name::#pv => { __res.push(#rn::#res_sn(#alg(#sn::#vn))); } };
                }
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                let mapped: Vec<TokenStream2> = bs
                    .iter()
                    .zip(v.fields.iter())
                    .map(|(b, fk)| match fk {
                        FieldKind::Child(child_sort) => {
                            let fr = &child_fn_refs[*child_sort];
                            quote! { __res[*#b].#fr() }
                        }
                        FieldKind::VariadicChild(child_sort) => {
                            let fr = &child_fn_refs[*child_sort];
                            quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| __res[*__c].#fr()).collect()) }
                        }
                        FieldKind::Data(_) => quote! { #b.clone() },
                    })
                    .collect();
                quote! { #fam_name::#pv(#(#bs),*) => { __res.push(#rn::#res_sn(#alg(#sn::#vn(#(#mapped),*)))); } }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        fused_ref_all_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    // ---- fused ref subtree arms: for fold_ref (Vec<Option<Res>>) ----
    let mut fused_ref_subtree_arms: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .flat_map(|(si, sort)| {
            let alg = format_ident!("__alg{}", si);
            let sn = sort.name.clone();
            let res_sn = sort.name.clone();
            let child_fn_refs: Vec<syn::Ident> = (0..n)
                .map(|j| format_ident!("unwrap_{}_ref", sorts[j].name.to_string().to_lowercase()))
                .collect();
            let rn = result_name.clone();
            sort.variants.iter().map(move |v| {
                let pv = format_ident!("{}{}", sn, v.name);
                let vn = &v.name;
                if v.fields.is_empty() {
                    return quote! { #fam_name::#pv => { __res[__i] = Some(#rn::#res_sn(#alg(#sn::#vn))); } };
                }
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                let mapped: Vec<TokenStream2> = bs
                    .iter()
                    .zip(v.fields.iter())
                    .map(|(b, fk)| match fk {
                        FieldKind::Child(child_sort) => {
                            let fr = &child_fn_refs[*child_sort];
                            quote! { __res[*#b].as_ref().unwrap().#fr() }
                        }
                        FieldKind::VariadicChild(child_sort) => {
                            let fr = &child_fn_refs[*child_sort];
                            quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| __res[*__c].as_ref().unwrap().#fr()).collect()) }
                        }
                        FieldKind::Data(_) => quote! { #b.clone() },
                    })
                    .collect();
                quote! { #fam_name::#pv(#(#bs),*) => { __res[__i] = Some(#rn::#res_sn(#alg(#sn::#vn(#(#mapped),*)))); } }
            })
        })
        .collect();
    if !coprod_unused.is_empty() {
        fused_ref_subtree_arms.push(quote! { #fam_name::__Phantom(..) => unreachable!() });
    }

    let _mm_closures: Vec<TokenStream2> = (0..n)
        .map(|i| {
            let fn_name = format_ident!("unwrap_{}", sorts[i].name.to_string().to_lowercase());
            quote! { |__c: usize| __res[__c].as_ref().unwrap().clone().#fn_name() }
        })
        .collect();

    // mm_ref_closures: borrow &usize, clone only the sort's result (not the whole enum)
    let mm_ref_closures: Vec<TokenStream2> = (0..n)
        .map(|i| {
            let fn_ref = format_ident!("unwrap_{}_ref", sorts[i].name.to_string().to_lowercase());
            quote! { |__c: &usize| __res[*__c].as_ref().unwrap().#fn_ref().clone() }
        })
        .collect();

    // mm_ref_all_closures: for fold_all (Vec<Res>, not Vec<Option<Res>>)
    let _mm_ref_all_closures: Vec<TokenStream2> = (0..n)
        .map(|i| {
            let fn_ref = format_ident!("unwrap_{}_ref", sorts[i].name.to_string().to_lowercase());
            quote! { |__c: &usize| __res[*__c].#fn_ref().clone() }
        })
        .collect();

    let dispatch_alg_closures: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let sn = &sort.name;
            let alg = format_ident!("__alg{}", i);
            quote! { |__node| #result_name::#sn(#alg(__node)) }
        })
        .collect();

    // ---- para_family -------------------------------------------------------
    let para_fn = format_ident!(
        "fold_with_ids_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let para_alg_params = make_alg_params(&|j| {
        let a = &ap[j];
        quote! { (::semi_persistent_traversals::Id, #a) }
    });
    let _para_mm_closures: Vec<TokenStream2> = (0..n).map(|i| {
        let fn_name = format_ident!("unwrap_{}", sorts[i].name.to_string().to_lowercase());
        quote! { |__c: usize| (::semi_persistent_traversals::Id(__c), __res[__c].as_ref().unwrap().clone().#fn_name()) }
    }).collect();
    let para_mm_ref_closures: Vec<TokenStream2> = (0..n).map(|i| {
        let fn_ref = format_ident!("unwrap_{}_ref", sorts[i].name.to_string().to_lowercase());
        quote! { |__c: &usize| (::semi_persistent_traversals::Id(*__c), __res[*__c].as_ref().unwrap().#fn_ref().clone()) }
    }).collect();

    // ---- histo_family --------------------------------------------------------
    let histo_fn = format_ident!(
        "fold_with_history_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let histo_alg_params = make_alg_params(&|j| {
        let a = &ap[j];
        quote! { ::semi_persistent_traversals::Ann<#a> }
    });
    let _histo_mm_closures: Vec<TokenStream2> = (0..n)
        .map(|i| {
            let fn_name = format_ident!("unwrap_{}", sorts[i].name.to_string().to_lowercase());
            quote! { |__c: usize| {
                let __ann = __ann_res[__c].as_ref().unwrap();
                ::semi_persistent_traversals::Ann {
                    value: __ann.value.clone().#fn_name(),
                    children: __ann.children.clone(),
                }
            }}
        })
        .collect();
    let histo_mm_ref_closures: Vec<TokenStream2> = (0..n)
        .map(|i| {
            let fn_ref = format_ident!("unwrap_{}_ref", sorts[i].name.to_string().to_lowercase());
            quote! { |__c: &usize| {
                let __ann = __ann_res[*__c].as_ref().unwrap();
                ::semi_persistent_traversals::Ann {
                    value: __ann.value.#fn_ref().clone(),
                    children: __ann.children.clone(),
                }
            }}
        })
        .collect();

    // ---- zygo_family -------------------------------------------------------
    let _zygo_fn = format_ident!(
        "fold_with_aux_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );

    // ---- coelgot_family ----------------------------------------------------
    let coelgot_fn = format_ident!(
        "fold_with_original_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let coelgot_alg_params: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let sn = &sort.name;
            let p = format_ident!("__alg{}", i);
            let a = &ap[i];
            let own: Vec<&syn::Ident> = sort_own_as[i].clone();
            let own_usize: Vec<TokenStream2> = own.iter().map(|_| quote! { usize }).collect();
            quote! { #p: impl Fn(&#sn<#(#own_usize),*>, #sn<#(#own),*>) -> #a }
        })
        .collect();
    let coelgot_dispatch_closures: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let sn = &sort.name;
            let alg = format_ident!("__alg{}", i);
            let own_usize: Vec<TokenStream2> = sort_own_params[i]
                .iter()
                .map(|_| quote! { usize })
                .collect();
            quote! { |__folded_node| {
                let __orig_sort: #sn<#(#own_usize),*> = __orig.clone().try_into().unwrap();
                #result_name::#sn(#alg(&__orig_sort, __folded_node))
            }}
        })
        .collect();

    // ---- prefold_family ----------------------------------------------------
    let prefold_fn = format_ident!(
        "prefold_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let prefold_pre_params: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(si, sort)| {
            let sn = &sort.name;
            let p = format_ident!("__pre{}", si);
            let own_usize: Vec<TokenStream2> = sort_own_params[si]
                .iter()
                .map(|_| quote! { usize })
                .collect();
            quote! { #p: impl Fn(#sn<#(#own_usize),*>) -> #fam_name<#(#all_usize),*> }
        })
        .collect();
    let prefold_pre_dispatch: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(si, _)| {
            let pre = format_ident!("__pre{}", si);
            quote! { |__node| #pre(__node) }
        })
        .collect();
    let alg_fwd: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__alg{}", i)).collect();

    // ---- elgot_family ------------------------------------------------------
    let elgot_fn = format_ident!(
        "fold_short_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let elgot_alg_params: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let sn = &sort.name;
            let p = format_ident!("__alg{}", i);
            let a = &ap[i];
            let own: Vec<&syn::Ident> = sort_own_as[i].clone();
            quote! { #p: impl Fn(#sn<#(#own),*>) -> Result<#a, #a> }
        })
        .collect();
    let elgot_dispatch_closures: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let sn = &sort.name;
            let alg = format_ident!("__alg{}", i);
            quote! { |__node| match #alg(__node) {
                Ok(__v) => Ok(#result_name::#sn(__v)),
                Err(__v) => Err(#result_name::#sn(__v)),
            }}
        })
        .collect();

    // ---- transform_family --------------------------------------------------
    let transform_fn = format_ident!(
        "transform_{}",
        format!("{}_multi", fam_name.to_string().to_lowercase())
    );
    let transform_params: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(si, sort)| {
            let sn = &sort.name;
            let own = &sort_own_params[si];
            let p = format_ident!("__rule{}", si);
            let own_usize: Vec<TokenStream2> = own.iter().map(|_| quote! { usize }).collect();
            quote! { #p: impl Fn(#sn<#(#own_usize),*>) -> #fam_name<#(#all_usize),*> }
        })
        .collect();
    let transform_dispatch_closures: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(si, _sort)| {
            let rule = format_ident!("__rule{}", si);
            quote! { |__node| #rule(__node) }
        })
        .collect();

    // ---- From impls (for all sorts) ----------------------------------------
    let from_impls: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(si, sort)| {
            let sn = &sort.name;
            let own = &sort_own_params[si];
            let arms: Vec<TokenStream2> = sort
                .variants
                .iter()
                .map(|v| {
                    let vn = &v.name;
                    let pv = format_ident!("{}{}", sort.name, v.name);
                    let bs: Vec<syn::Ident> = (0..v.fields.len())
                        .map(|i| format_ident!("__x{}", i))
                        .collect();
                    if bs.is_empty() {
                        quote! { #sn::#vn => #fam_name::#pv }
                    } else {
                        quote! { #sn::#vn(#(#bs),*) => #fam_name::#pv(#(#bs),*) }
                    }
                })
                .collect();
            quote! {
                impl<#(#sp),*> From<#sn<#(#own),*>> for #fam_name<#(#sp),*> {
                    fn from(s: #sn<#(#own),*>) -> Self {
                        match s { #(#arms),* }
                    }
                }
            }
        })
        .collect();

    // ---- TryFrom: coproduct -> sort (projection) ----------------------------
    let try_from_impls: Vec<TokenStream2> = sorts
        .iter()
        .enumerate()
        .map(|(si, sort)| {
            let sn = &sort.name;
            let own = &sort_own_params[si];
            let ok_arms: Vec<TokenStream2> = sort
                .variants
                .iter()
                .map(|v| {
                    let vn = &v.name;
                    let pv = format_ident!("{}{}", sort.name, v.name);
                    let bs: Vec<syn::Ident> = (0..v.fields.len())
                        .map(|i| format_ident!("__x{}", i))
                        .collect();
                    if bs.is_empty() {
                        quote! { #fam_name::#pv => Ok(#sn::#vn) }
                    } else {
                        quote! { #fam_name::#pv(#(#bs),*) => Ok(#sn::#vn(#(#bs),*)) }
                    }
                })
                .collect();
            quote! {
                impl<#(#sp),*> TryFrom<#fam_name<#(#sp),*>> for #sn<#(#own),*> {
                    type Error = #fam_name<#(#sp),*>;
                    fn try_from(c: #fam_name<#(#sp),*>) -> Result<Self, Self::Error> {
                        match c {
                            #(#ok_arms,)*
                            __other => Err(__other),
                        }
                    }
                }
            }
        })
        .collect();

    // ---- HasVariadic impl: resolve Variadic::Span fields ----------------
    let variadic_arms: Vec<TokenStream2> = sorts
        .iter()
        .flat_map(|sort| {
            sort.variants.iter().filter_map(|v| {
                // Find variadic field positions
                let var_positions: Vec<usize> = v
                    .fields
                    .iter()
                    .enumerate()
                    .filter_map(|(i, f)| {
                        if matches!(f, FieldKind::VariadicChild(_)) {
                            Some(i)
                        } else {
                            None
                        }
                    })
                    .collect();
                if var_positions.is_empty() {
                    return None;
                }
                let pv = format_ident!("{}{}", sort.name, v.name);
                let bs: Vec<syn::Ident> = (0..v.fields.len())
                    .map(|i| format_ident!("__x{}", i))
                    .collect();
                let pats: Vec<TokenStream2> = bs
                    .iter()
                    .enumerate()
                    .map(|(i, b)| {
                        if var_positions.contains(&i) {
                            quote! { #b }
                        } else {
                            quote! { _ }
                        }
                    })
                    .collect();
                let resolves: Vec<TokenStream2> = var_positions.iter().map(|&i| {
                let b = &bs[i];
                quote! {
                    if let ::semi_persistent_traversals::Variadic::Span { start, len } = #b {
                        let s = *start as usize;
                        *#b = ::semi_persistent_traversals::Variadic::Resolved(pool[s..s + *len as usize].into());
                    }
                }
            }).collect();
                Some(quote! { #fam_name::#pv(#(#pats),*) => { #(#resolves)* } })
            })
        })
        .collect();

    let has_variadic_body = if variadic_arms.is_empty() {
        quote! { let _ = pool; }
    } else {
        quote! { match self { #(#variadic_arms,)* _ => {} } }
    };

    Ok(quote! {
        #[derive(Clone, PartialEq, Eq, Hash, Debug)]
        #vis enum #fam_name<#(#sp),*> { #(#coprod_variants),* }

        #(#sort_enums)*

        impl<R> ::semi_persistent_traversals::Functor<R> for #fam_name<#(#all_r),*> {
            type Mapped<__S> = #fam_name<#(#all_s),*>;
            fn map<__S>(self, mut __f: impl FnMut(R) -> __S) -> #fam_name<#(#all_s),*> {
                match self { #(#functor_arms),* }
            }
            fn map_ref<__S>(&self, mut __f: impl FnMut(&R) -> __S) -> #fam_name<#(#all_s),*> {
                match self { #(#functor_ref_arms),* }
            }
            fn children_into(&self, __buf: &mut ::smallvec::SmallVec<[R; 8]>) where R: Copy {
                __buf.clear();
                match self { #(#children_into_arms),* }
            }
        }

        #[allow(clippy::too_many_arguments)]
        impl<#(#sp),*> #fam_name<#(#sp),*> {
            #vis fn sort_of(&self) -> usize {
                match self { #(#sort_of_arms),* }
            }

            #vis fn dispatch<__T>(self, #(#dispatch_params),*) -> __T {
                match self { #(#dispatch_arms),* }
            }

            #vis fn multi_map<#(#dp),*>(self, #(#mm_fn_params),*) -> #fam_name<#(#dp),*> {
                match self { #(#mm_arms),* }
            }

            /// Like multi_map but borrows &self. Clones data fields, maps children by ref.
            #vis fn multi_map_ref<#(#dp),*>(&self, #(#mm_ref_fn_params),*) -> #fam_name<#(#dp),*> {
                match self { #(#mm_ref_arms),* }
            }
        }

        #[derive(Clone, Debug)]
        #vis enum #result_name<#(#ap),*> { #(#res_variants),* }

        impl<#(#ap),*> #result_name<#(#ap),*> {
            #(#unwrap_fns)*
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #cata_fn<#(#ap: Clone),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            __root: ::semi_persistent_traversals::Id,
            #(#alg_params),*
        ) -> #result_name<#(#ap),*>
        {
            enum Task { Enter(usize), Eval(usize) }
            let mut __res: Vec<Option<#result_name<#(#ap),*>>> =
                (0..__arena.len()).map(|_| None).collect();
            let mut __stack = vec![Task::Enter(__root.0)];
            let mut __ch = ::smallvec::SmallVec::<[usize; 8]>::new();
            while let Some(__task) = __stack.pop() {
                match __task {
                    Task::Enter(__i) => {
                        if __res[__i].is_some() { continue; }
                        __stack.push(Task::Eval(__i));
                        ::semi_persistent_traversals::Functor::<usize>::children_into(__arena.get(::semi_persistent_traversals::Id(__i)), &mut __ch);
                        for &c in __ch.iter().rev() {
                            if __res[c].is_none() { __stack.push(Task::Enter(c)); }
                        }
                    }
                    Task::Eval(__i) => {
                        if __res[__i].is_some() { continue; }
                        let __mapped = __arena.get(::semi_persistent_traversals::Id(__i))
                            .multi_map_ref(#(#mm_ref_closures),*);
                        __res[__i] = Some(__mapped.dispatch(#(#dispatch_alg_closures),*));
                    }
                }
            }
            __res[__root.0].take().unwrap()
        }

        /// Fold every node in the arena in a single O(n) linear scan.
        /// Children always have lower indices than parents (push order),
        /// so no topo sort needed. Returns a Vec of results indexed by node id.
        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #fold_all_fn<#(#ap: Clone),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            #(#alg_params),*
        ) -> Vec<#result_name<#(#ap),*>>
        {
            let __n = __arena.len();
            let mut __res: Vec<#result_name<#(#ap),*>> = Vec::with_capacity(__n);
            for __i in 0..__n {
                match __arena.get(::semi_persistent_traversals::Id(__i)) {
                    #(#fused_fold_all_single_arms)*
                }
            }
            __res
        }

        /// Zero-clone fold_all: algebra receives borrowed children.
        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #fold_all_ref_fn<#(#ap),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            #(#alg_ref_params),*
        ) -> Vec<#result_name<#(#ap),*>>
        {
            let __n = __arena.len();
            let mut __res: Vec<#result_name<#(#ap),*>> = Vec::with_capacity(__n);
            for __i in 0..__n {
                match __arena.get(::semi_persistent_traversals::Id(__i)) {
                    #(#fused_ref_all_arms)*
                }
            }
            __res
        }

        /// Zero-clone subtree fold: algebra receives borrowed children.
        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #fold_ref_fn<#(#ap),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            __root: ::semi_persistent_traversals::Id,
            #(#alg_ref_params),*
        ) -> #result_name<#(#ap),*>
        {
            enum Task { Enter(usize), Eval(usize) }
            let mut __res: Vec<Option<#result_name<#(#ap),*>>> =
                (0..__arena.len()).map(|_| None).collect();
            let mut __stack = vec![Task::Enter(__root.0)];
            let mut __ch = ::smallvec::SmallVec::<[usize; 8]>::new();
            while let Some(__task) = __stack.pop() {
                match __task {
                    Task::Enter(__i) => {
                        if __res[__i].is_some() { continue; }
                        __stack.push(Task::Eval(__i));
                        ::semi_persistent_traversals::Functor::<usize>::children_into(__arena.get(::semi_persistent_traversals::Id(__i)), &mut __ch);
                        for &c in __ch.iter().rev() {
                            if __res[c].is_none() { __stack.push(Task::Enter(c)); }
                        }
                    }
                    Task::Eval(__i) => {
                        if __res[__i].is_some() { continue; }
                        match __arena.get(::semi_persistent_traversals::Id(__i)) {
                            #(#fused_ref_subtree_arms)*
                        }
                    }
                }
            }
            __res[__root.0].take().unwrap()
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #para_fn<#(#ap: Clone),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            __root: ::semi_persistent_traversals::Id,
            #(#para_alg_params),*
        ) -> #result_name<#(#ap),*>
        {
            enum Task { Enter(usize), Eval(usize) }
            let mut __res: Vec<Option<#result_name<#(#ap),*>>> =
                (0..__arena.len()).map(|_| None).collect();
            let mut __stack = vec![Task::Enter(__root.0)];
            let mut __ch = ::smallvec::SmallVec::<[usize; 8]>::new();
            while let Some(__task) = __stack.pop() {
                match __task {
                    Task::Enter(__i) => {
                        if __res[__i].is_some() { continue; }
                        __stack.push(Task::Eval(__i));
                        ::semi_persistent_traversals::Functor::<usize>::children_into(__arena.get(::semi_persistent_traversals::Id(__i)), &mut __ch);
                        for &c in __ch.iter().rev() {
                            if __res[c].is_none() { __stack.push(Task::Enter(c)); }
                        }
                    }
                    Task::Eval(__i) => {
                        if __res[__i].is_some() { continue; }
                        let __mapped = __arena.get(::semi_persistent_traversals::Id(__i))
                            .multi_map_ref(#(#para_mm_ref_closures),*);
                        __res[__i] = Some(__mapped.dispatch(#(#dispatch_alg_closures),*));
                    }
                }
            }
            __res[__root.0].take().unwrap()
        }

        /// Multi-sorted elgot: fold with early exit. Algebras return `Result<Ai, Ai>`.
        /// `Ok` continues, `Err` short-circuits and returns immediately.
        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #elgot_fn<#(#ap: Clone),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            __root: ::semi_persistent_traversals::Id,
            #(#elgot_alg_params),*
        ) -> #result_name<#(#ap),*>
        {
            enum Task { Enter(usize), Eval(usize) }
            let mut __res: Vec<Option<#result_name<#(#ap),*>>> =
                (0..__arena.len()).map(|_| None).collect();
            let mut __stack = vec![Task::Enter(__root.0)];
            let mut __ch = ::smallvec::SmallVec::<[usize; 8]>::new();
            while let Some(__task) = __stack.pop() {
                match __task {
                    Task::Enter(__i) => {
                        if __res[__i].is_some() { continue; }
                        __stack.push(Task::Eval(__i));
                        ::semi_persistent_traversals::Functor::<usize>::children_into(__arena.get(::semi_persistent_traversals::Id(__i)), &mut __ch);
                        for &c in __ch.iter().rev() {
                            if __res[c].is_none() { __stack.push(Task::Enter(c)); }
                        }
                    }
                    Task::Eval(__i) => {
                        if __res[__i].is_some() { continue; }
                        let __mapped = __arena.get(::semi_persistent_traversals::Id(__i))
                            .multi_map_ref(#(#mm_ref_closures),*);
                        let __result = __mapped.dispatch(#(#elgot_dispatch_closures),*);
                        match __result {
                            Ok(__v) => { __res[__i] = Some(__v); }
                            Err(__v) => return __v,
                        }
                    }
                }
            }
            __res[__root.0].take().unwrap()
        }

        /// Multi-sorted bottom-up transform: one rewrite rule per sort.
        /// Each rule receives the sort node with children already remapped,
        /// and returns a (possibly rewritten) coproduct node.
        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #transform_fn(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            __root: ::semi_persistent_traversals::Id,
            #(#transform_params),*
        ) -> (::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>, ::semi_persistent_traversals::Id)
        {
            use ::semi_persistent_traversals::Functor;
            enum Task { Enter(usize), Eval(usize) }
            let mut __new: ::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>> = ::semi_persistent_traversals::Arena::new();
            let mut __mapping: Vec<usize> = vec![0; __arena.len()];
            let mut __visited = vec![false; __arena.len()];
            let mut __stack = vec![Task::Enter(__root.0)];
            let mut __ch = ::smallvec::SmallVec::<[usize; 8]>::new();
            while let Some(__task) = __stack.pop() {
                match __task {
                    Task::Enter(__i) => {
                        if __visited[__i] { continue; }
                        __visited[__i] = true;
                        __stack.push(Task::Eval(__i));
                        ::semi_persistent_traversals::Functor::<usize>::children_into(__arena.get(::semi_persistent_traversals::Id(__i)), &mut __ch);
                        for &c in __ch.iter().rev() {
                            if !__visited[c] { __stack.push(Task::Enter(c)); }
                        }
                    }
                    Task::Eval(__i) => {
                        let __remapped = __arena.get(::semi_persistent_traversals::Id(__i))
                            .map_ref(|c: &usize| __mapping[*c]);
                        let __rewritten = __remapped.dispatch(#(#transform_dispatch_closures),*);
                        let __id = __new.push(__rewritten);
                        __mapping[__i] = __id.0;
                    }
                }
            }
            (__new, ::semi_persistent_traversals::Id(__mapping[__root.0]))
        }

        /// Multi-sorted fold with history: children carry `&Ann<Ai>`.
        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #histo_fn<#(#ap: Clone),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            __root: ::semi_persistent_traversals::Id,
            #(#histo_alg_params),*
        ) -> #result_name<#(#ap),*>
        {
            use ::semi_persistent_traversals::Functor;
            enum Task { Enter(usize), Eval(usize) }
            let mut __ann_res: Vec<Option<::semi_persistent_traversals::Ann<#result_name<#(#ap),*>>>> =
                (0..__arena.len()).map(|_| None).collect();
            let mut __stack = vec![Task::Enter(__root.0)];
            let mut __ch = ::smallvec::SmallVec::<[usize; 8]>::new();
            while let Some(__task) = __stack.pop() {
                match __task {
                    Task::Enter(__i) => {
                        if __ann_res[__i].is_some() { continue; }
                        __stack.push(Task::Eval(__i));
                        ::semi_persistent_traversals::Functor::<usize>::children_into(__arena.get(::semi_persistent_traversals::Id(__i)), &mut __ch);
                        for &c in __ch.iter().rev() {
                            if __ann_res[c].is_none() { __stack.push(Task::Enter(c)); }
                        }
                    }
                    Task::Eval(__i) => {
                        if __ann_res[__i].is_some() { continue; }
                        let __node = __arena.get(::semi_persistent_traversals::Id(__i));
                        let __children = ::semi_persistent_traversals::collect_children(__node);
                        let __mapped = __node.multi_map_ref(#(#histo_mm_ref_closures),*);
                        let __value = __mapped.dispatch(#(#dispatch_alg_closures),*);
                        __ann_res[__i] = Some(::semi_persistent_traversals::Ann { value: __value, children: __children });
                    }
                }
            }
            __ann_res[__root.0].take().unwrap().value
        }

        /// Multi-sorted fold with original: algebra sees raw node + folded node.
        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #coelgot_fn<#(#ap: Clone),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            __root: ::semi_persistent_traversals::Id,
            #(#coelgot_alg_params),*
        ) -> #result_name<#(#ap),*>
        {
            use ::semi_persistent_traversals::Functor;
            enum Task { Enter(usize), Eval(usize) }
            let mut __res: Vec<Option<#result_name<#(#ap),*>>> =
                (0..__arena.len()).map(|_| None).collect();
            let mut __stack = vec![Task::Enter(__root.0)];
            let mut __ch = ::smallvec::SmallVec::<[usize; 8]>::new();
            while let Some(__task) = __stack.pop() {
                match __task {
                    Task::Enter(__i) => {
                        if __res[__i].is_some() { continue; }
                        __stack.push(Task::Eval(__i));
                        ::semi_persistent_traversals::Functor::<usize>::children_into(__arena.get(::semi_persistent_traversals::Id(__i)), &mut __ch);
                        for &c in __ch.iter().rev() {
                            if __res[c].is_none() { __stack.push(Task::Enter(c)); }
                        }
                    }
                    Task::Eval(__i) => {
                        if __res[__i].is_some() { continue; }
                        let __orig = __arena.get(::semi_persistent_traversals::Id(__i));
                        let __folded = __orig.multi_map_ref(#(#mm_ref_closures),*);
                        let __orig_sort = __orig.sort_of();
                        __res[__i] = Some(__folded.dispatch(#(#coelgot_dispatch_closures),*));
                    }
                }
            }
            __res[__root.0].take().unwrap()
        }

        /// Multi-sorted prefold: transform each layer, then fold.
        #[allow(non_snake_case, clippy::too_many_arguments)]
        #vis fn #prefold_fn<#(#ap: Clone),*>(
            __arena: &::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>>,
            __root: ::semi_persistent_traversals::Id,
            #(#prefold_pre_params,)*
            #(#alg_params),*
        ) -> #result_name<#(#ap),*>
        {
            use ::semi_persistent_traversals::Functor;
            enum Task { Enter(usize), Eval(usize) }
            let mut __new: ::semi_persistent_traversals::Arena<#fam_name<#(#all_usize),*>> = ::semi_persistent_traversals::Arena::new();
            let mut __mapping: Vec<usize> = vec![0; __arena.len()];
            let mut __visited = vec![false; __arena.len()];
            let mut __stack = vec![Task::Enter(__root.0)];
            let mut __ch = ::smallvec::SmallVec::<[usize; 8]>::new();
            while let Some(__task) = __stack.pop() {
                match __task {
                    Task::Enter(__i) => {
                        if __visited[__i] { continue; }
                        __visited[__i] = true;
                        __stack.push(Task::Eval(__i));
                        ::semi_persistent_traversals::Functor::<usize>::children_into(__arena.get(::semi_persistent_traversals::Id(__i)), &mut __ch);
                        for &c in __ch.iter().rev() {
                            if !__visited[c] { __stack.push(Task::Enter(c)); }
                        }
                    }
                    Task::Eval(__i) => {
                        let __remapped = __arena.get(::semi_persistent_traversals::Id(__i))
                            .map_ref(|c: &usize| __mapping[*c]);
                        let __normalized = __remapped.dispatch(#(#prefold_pre_dispatch),*);
                        let __id = __new.push(__normalized);
                        __mapping[__i] = __id.0;
                    }
                }
            }
            #cata_fn(&__new, ::semi_persistent_traversals::Id(__mapping[__root.0]), #(#alg_fwd),*)
        }

        #(#from_impls)*

        #(#try_from_impls)*

        impl ::semi_persistent_traversals::HasVariadic for #fam_name<#(#all_usize),*> {
            fn resolve_spans(&mut self, pool: &[usize]) {
                #has_variadic_body
            }
        }
    })
}

fn fk_type(fk: &FieldKind, params: &[syn::Ident]) -> TokenStream2 {
    match fk {
        FieldKind::Child(i) => {
            let p = &params[*i];
            quote! { #p }
        }
        FieldKind::VariadicChild(i) => {
            let p = &params[*i];
            quote! { ::semi_persistent_traversals::Variadic<#p> }
        }
        FieldKind::Data(ty) => quote! { #ty },
    }
}

fn map_arm(enum_name: &syn::Ident, variant: &syn::Ident, fields: &[FieldKind]) -> TokenStream2 {
    if fields.is_empty() {
        return quote! { #enum_name::#variant => #enum_name::#variant };
    }
    let bs: Vec<syn::Ident> = (0..fields.len())
        .map(|i| format_ident!("__x{}", i))
        .collect();
    let mapped: Vec<TokenStream2> = bs
        .iter()
        .zip(fields.iter())
        .map(|(b, fk)| match fk {
            FieldKind::Child(_) => quote! { __f(#b) },
            FieldKind::VariadicChild(_) => quote! { #b.map_all(&mut __f) },
            FieldKind::Data(_) => quote! { #b },
        })
        .collect();
    quote! { #enum_name::#variant(#(#bs),*) => #enum_name::#variant(#(#mapped),*) }
}

fn map_ref_arm(enum_name: &syn::Ident, variant: &syn::Ident, fields: &[FieldKind]) -> TokenStream2 {
    if fields.is_empty() {
        return quote! { #enum_name::#variant => #enum_name::#variant };
    }
    let bs: Vec<syn::Ident> = (0..fields.len())
        .map(|i| format_ident!("__x{}", i))
        .collect();
    let mapped: Vec<TokenStream2> = bs
        .iter()
        .zip(fields.iter())
        .map(|(b, fk)| match fk {
            FieldKind::Child(_) => quote! { __f(#b) },
            FieldKind::VariadicChild(_) => {
                quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(&mut __f).collect()) }
            }
            FieldKind::Data(_) => quote! { #b.clone() },
        })
        .collect();
    quote! { #enum_name::#variant(#(#bs),*) => #enum_name::#variant(#(#mapped),*) }
}

fn children_into_arm(
    enum_name: &syn::Ident,
    variant: &syn::Ident,
    fields: &[FieldKind],
) -> TokenStream2 {
    if fields.is_empty() {
        return quote! { #enum_name::#variant => {} };
    }
    let bs: Vec<syn::Ident> = (0..fields.len())
        .map(|i| format_ident!("__x{}", i))
        .collect();
    let pushes: Vec<TokenStream2> = bs
        .iter()
        .zip(fields.iter())
        .filter_map(|(b, fk)| match fk {
            FieldKind::Child(_) => Some(quote! { __buf.push(*#b); }),
            FieldKind::VariadicChild(_) => Some(quote! { __buf.extend(#b.iter().copied()); }),
            FieldKind::Data(_) => None,
        })
        .collect();
    quote! { #enum_name::#variant(#(#bs),*) => { #(#pushes)* } }
}
