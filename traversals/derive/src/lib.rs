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
#[derive(Clone)]
struct RawSortDef {
    name: syn::Ident,
    variants: Vec<RawVariantDef>,
}
#[derive(Clone)]
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

// ===========================================================================
// partition! — partitioned per-type arenas
// ===========================================================================

#[proc_macro]
pub fn partition(input: TokenStream) -> TokenStream {
    let raw = parse_macro_input!(input as PartitionDef);
    match gen_partition(&raw) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

struct PartitionDef {
    vis: syn::Visibility,
    fam_name: syn::Ident,
    store_name: syn::Ident,
    sorts: Vec<RawSortDef>,
}

impl syn::parse::Parse for PartitionDef {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let vis: syn::Visibility = input.parse()?;
        let kw: syn::Ident = input.parse()?;
        if kw != "family" {
            return Err(syn::Error::new(kw.span(), "expected `family`"));
        }
        let fam_name: syn::Ident = input.parse()?;
        let _: syn::Token![=>] = input.parse()?;
        let store_name: syn::Ident = input.parse()?;
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
                variants.push(RawVariantDef { name: vname, fields });
                if content.peek(syn::Token![,]) {
                    let _: syn::Token![,] = content.parse()?;
                }
            }
            sorts.push(RawSortDef { name, variants });
        }
        if sorts.len() < 2 {
            return Err(syn::Error::new(fam_name.span(), "a family needs at least 2 sorts"));
        }
        Ok(PartitionDef { vis, fam_name, store_name, sorts })
    }
}

// ---------------------------------------------------------------------------
// partition! code generation
// ---------------------------------------------------------------------------

fn resolve_partition_fields(sorts: &[RawSortDef]) -> Vec<ResolvedSort> {
    let sort_names: Vec<String> = sorts.iter().map(|s| s.name.to_string()).collect();
    sorts.iter().enumerate().map(|(si, sort)| {
        let variants = sort.variants.iter().map(|v| {
            let fields = v.fields.iter().map(|ty| {
                if let Type::Path(tp) = ty {
                    if let Some(seg) = tp.path.segments.last()
                        && seg.ident == "Variadic"
                        && let syn::PathArguments::AngleBracketed(args) = &seg.arguments
                        && let Some(syn::GenericArgument::Type(Type::Path(inner))) = args.args.first()
                        && let Some(inner_ident) = inner.path.get_ident()
                        && let Some(idx) = sort_names.iter().position(|s| inner_ident == s)
                    {
                        return FieldKind::VariadicChild(idx);
                    }
                    if let Some(ident) = tp.path.get_ident()
                        && let Some(idx) = sort_names.iter().position(|s| ident == s)
                    {
                        return FieldKind::Child(idx);
                    }
                }
                FieldKind::Data(ty.clone())
            }).collect();
            ResolvedVariant { name: v.name.clone(), fields }
        }).collect();
        ResolvedSort { name: sort.name.clone(), sort_idx: si, variants }
    }).collect()
}

fn gen_partition(def: &PartitionDef) -> syn::Result<TokenStream2> {
    let sorts = resolve_partition_fields(&def.sorts);
    let n = sorts.len();
    let vis = &def.vis;
    let store = &def.store_name;
    let _fam = &def.fam_name;

    let sort_names: Vec<&syn::Ident> = sorts.iter().map(|s| &s.name).collect();
    let sort_lowers: Vec<syn::Ident> = sort_names.iter()
        .map(|n| format_ident!("{}", n.to_string().to_lowercase()))
        .collect();

    // Collect which child sort indices each sort references (for variadic pools)
    let sort_variadic_child_sorts: Vec<Vec<usize>> = sorts.iter().map(|sort| {
        let mut child_sorts: Vec<usize> = sort.variants.iter()
            .flat_map(|v| v.fields.iter().filter_map(|f| match f {
                FieldKind::VariadicChild(i) => Some(*i),
                _ => None,
            }))
            .collect();
        child_sorts.sort();
        child_sorts.dedup();
        child_sorts
    }).collect();

    let id_newtypes = gen_id_newtypes(vis, &sorts, &sort_names, &sort_lowers);
    let root_enum = gen_root_enum(vis, store, &sorts, &sort_names);
    let node_enums = gen_node_enums(vis, &sorts, &sort_names);
    let mapped_enums = gen_mapped_enums(vis, &sorts, &sort_names, n);
    let map_children_impls = gen_map_children(vis, &sorts, &sort_names, n);
    let container = gen_container(vis, store, &sorts, &sort_names, &sort_lowers, &sort_variadic_child_sorts);
    let view = gen_view(vis, store);
    let fold_impl = gen_fold(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let fold_all_impl = gen_fold_all(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let para_impl = gen_para(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let transform_impl = gen_transform(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let histo_impl = gen_histo(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let zygo_impl = gen_zygo(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let fold_short_impl = gen_fold_short(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let fold_original_impl = gen_fold_with_original(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let unfold_impl = gen_unfold(vis, store, &sorts, &sort_names, &sort_lowers, n, &sort_variadic_child_sorts);
    let unfold_short_impl = gen_unfold_short(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let fold_pair_impl = gen_fold_pair(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let prefold_impl = gen_prefold(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let postunfold_impl = gen_postunfold(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let rewrite_down_impl = gen_rewrite_down(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let zipper_impl = gen_zipper(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let refold_impl = gen_refold(vis, store, &sorts, &sort_names, &sort_lowers, n);
    let rewrite_impl = gen_rewrite(vis, store, &sorts, &sort_names, &sort_lowers, n);

    Ok(quote! {
        #id_newtypes
        #root_enum
        #node_enums
        #mapped_enums
        #map_children_impls
        #container
        #view
        #fold_impl
        #fold_all_impl
        #para_impl
        #transform_impl
        #histo_impl
        #zygo_impl
        #fold_short_impl
        #fold_original_impl
        #unfold_impl
        #unfold_short_impl
        #fold_pair_impl
        #prefold_impl
        #postunfold_impl
        #rewrite_down_impl
        #zipper_impl
        #refold_impl
        #rewrite_impl
    })
}

// ---------------------------------------------------------------------------
// partition! generators
// ---------------------------------------------------------------------------

fn gen_id_newtypes(
    vis: &syn::Visibility,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
) -> TokenStream2 {
    let ids: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let id_name = format_ident!("{}Id", sort_names[i]);
        quote! {
            #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
            #vis struct #id_name(pub usize);
        }
    }).collect();
    quote! { #(#ids)* }
}

fn gen_root_enum(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let variants: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let sn = sort_names[i];
        let id_name = format_ident!("{}Id", sn);
        quote! { #sn(#id_name) }
    }).collect();
    let result_name = format_ident!("{}FoldResult", store);
    let aps: Vec<syn::Ident> = (0..sorts.len()).map(|i| format_ident!("__A{}", i)).collect();
    let res_variants: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let sn = sort_names[i];
        let a = &aps[i];
        quote! { #sn(#a) }
    }).collect();
    let unwrap_fns: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let sn = sort_names[i];
        let a = &aps[i];
        let fn_name = format_ident!("unwrap_{}", sort_names[i].to_string().to_lowercase());
        quote! {
            #vis fn #fn_name(self) -> #a {
                match self { #result_name::#sn(v) => v, _ => panic!("sort mismatch") }
            }
        }
    }).collect();
    quote! {
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        #vis enum #root_name { #(#variants),* }

        #[derive(Clone, Debug)]
        #vis enum #result_name<#(#aps),*> { #(#res_variants),* }

        impl<#(#aps),*> #result_name<#(#aps),*> {
            #(#unwrap_fns)*
        }
    }
}

fn partition_field_type(fk: &FieldKind, sort_names: &[&syn::Ident]) -> TokenStream2 {
    match fk {
        FieldKind::Child(i) => {
            let id = format_ident!("{}Id", sort_names[*i]);
            quote! { #id }
        }
        FieldKind::VariadicChild(i) => {
            let id = format_ident!("{}Id", sort_names[*i]);
            quote! { ::semi_persistent_traversals::Variadic<#id> }
        }
        FieldKind::Data(ty) => quote! { #ty },
    }
}

fn gen_node_enums(
    vis: &syn::Visibility,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
) -> TokenStream2 {
    let enums: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let node_name = format_ident!("{}Node", sort_names[i]);
        let variants: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            let tys: Vec<TokenStream2> = v.fields.iter()
                .map(|fk| partition_field_type(fk, sort_names))
                .collect();
            if tys.is_empty() {
                quote! { #vn }
            } else {
                quote! { #vn(#(#tys),*) }
            }
        }).collect();
        quote! {
            #[derive(Clone, PartialEq, Eq, Hash, Debug)]
            #vis enum #node_name { #(#variants),* }
        }
    }).collect();
    quote! { #(#enums)* }
}

fn gen_mapped_enums(
    vis: &syn::Visibility,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    n: usize,
) -> TokenStream2 {
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();
    let enums: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let mapped_name = format_ident!("{}NodeMapped", sort_names[si]);
        // Collect which sort params this sort actually uses
        let mut used: Vec<usize> = sort.variants.iter()
            .flat_map(|v| v.fields.iter().filter_map(|f| match f {
                FieldKind::Child(i) | FieldKind::VariadicChild(i) => Some(*i),
                _ => None,
            }))
            .collect();
        used.sort();
        used.dedup();
        let params: Vec<&syn::Ident> = used.iter().map(|&i| &aps[i]).collect();
        let variants: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            let tys: Vec<TokenStream2> = v.fields.iter().map(|fk| match fk {
                FieldKind::Child(i) => { let a = &aps[*i]; quote! { #a } }
                FieldKind::VariadicChild(i) => { let a = &aps[*i]; quote! { ::semi_persistent_traversals::Variadic<#a> } }
                FieldKind::Data(ty) => quote! { #ty },
            }).collect();
            if tys.is_empty() { quote! { #vn } } else { quote! { #vn(#(#tys),*) } }
        }).collect();
        quote! {
            #[derive(Clone, Debug)]
            #vis enum #mapped_name<#(#params),*> { #(#variants),* }
        }
    }).collect();
    quote! { #(#enums)* }
}

fn gen_map_children(
    vis: &syn::Visibility,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    n: usize,
) -> TokenStream2 {
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();
    let impls: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let node_name = format_ident!("{}Node", sort_names[si]);
        let mapped_name = format_ident!("{}NodeMapped", sort_names[si]);
        // Which sorts does this sort reference as children?
        let mut child_sorts: Vec<usize> = sort.variants.iter()
            .flat_map(|v| v.fields.iter().filter_map(|f| match f {
                FieldKind::Child(i) | FieldKind::VariadicChild(i) => Some(*i),
                _ => None,
            }))
            .collect();
        child_sorts.sort();
        child_sorts.dedup();
        let fn_params: Vec<TokenStream2> = child_sorts.iter().map(|&j| {
            let p = format_ident!("__f{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            let a = &aps[j];
            quote! { #p: &mut impl FnMut(&#id) -> #a }
        }).collect();
        let result_params: Vec<&syn::Ident> = child_sorts.iter().map(|&j| &aps[j]).collect();
        let arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => #mapped_name::#vn };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let mapped: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).map(|(b, fk)| match fk {
                FieldKind::Child(j) => { let f = format_ident!("__f{}", j); quote! { #f(#b) } }
                FieldKind::VariadicChild(j) => {
                    let f = format_ident!("__f{}", j);
                    quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| #f(__c)).collect()) }
                }
                FieldKind::Data(_) => quote! { #b.clone() },
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => #mapped_name::#vn(#(#mapped),*) }
        }).collect();
        quote! {
            impl #node_name {
                #vis fn map_children<#(#result_params),*>(
                    &self,
                    #(#fn_params),*
                ) -> #mapped_name<#(#result_params),*> {
                    match self { #(#arms),* }
                }
            }
        }
    }).collect();
    quote! { #(#impls)* }
}

fn gen_container(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    sort_variadic_child_sorts: &[Vec<usize>],
) -> TokenStream2 {
    let mark_name = format_ident!("{}Mark", store);
    let root_name = format_ident!("{}Root", store);

    // Fields: one Vec per sort arena
    let arena_fields: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_nodes", sort_lowers[i]);
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #field: Vec<#node> }
    }).collect();

    // Fields: one Option<FxHashMap<Node, usize>> per sort for dedup
    let dedup_fields: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_dedup", sort_lowers[i]);
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #field: Option<::semi_persistent_traversals::FxHashMap<#node, usize>> }
    }).collect();

    // Fields: variadic pools — one Vec<SortId> per (owning_sort, child_sort) pair
    let pool_fields: Vec<TokenStream2> = sorts.iter().enumerate().flat_map(|(si, _)| {
        sort_variadic_child_sorts[si].iter().map(move |&ci| {
            let field = format_ident!("{}_pool_{}", sort_lowers[si], sort_lowers[ci]);
            let id = format_ident!("{}Id", sort_names[ci]);
            quote! { #field: Vec<#id> }
        })
    }).collect();

    // Mark struct fields
    let mark_arena_fields: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_len", sort_lowers[i]);
        quote! { #field: usize }
    }).collect();
    let mark_pool_fields: Vec<TokenStream2> = sorts.iter().enumerate().flat_map(|(si, _)| {
        sort_variadic_child_sorts[si].iter().map(move |&ci| {
            let field = format_ident!("{}_pool_{}_len", sort_lowers[si], sort_lowers[ci]);
            quote! { #field: usize }
        })
    }).collect();

    // push_* methods — dedup if index present
    let push_methods: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let method = format_ident!("push_{}", sort_lowers[i]);
        let node = format_ident!("{}Node", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        let field = format_ident!("{}_nodes", sort_lowers[i]);
        let dedup = format_ident!("{}_dedup", sort_lowers[i]);
        quote! {
            #vis fn #method(&mut self, node: #node) -> #id {
                if let Some(ref idx_map) = self.#dedup {
                    if let Some(&existing) = idx_map.get(&node) {
                        return #id(existing);
                    }
                }
                let idx = self.#field.len();
                self.#field.push(node.clone());
                if let Some(ref mut idx_map) = self.#dedup {
                    idx_map.insert(node, idx);
                }
                #id(idx)
            }
        }
    }).collect();

    // get_* methods
    let get_methods: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let method = format_ident!("get_{}", sort_lowers[i]);
        let node = format_ident!("{}Node", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        let field = format_ident!("{}_nodes", sort_lowers[i]);
        quote! {
            #vis fn #method(&self, id: #id) -> &#node { &self.#field[id.0] }
        }
    }).collect();

    // len_* methods
    let len_methods: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let method = format_ident!("len_{}", sort_lowers[i]);
        let field = format_ident!("{}_nodes", sort_lowers[i]);
        quote! { #vis fn #method(&self) -> usize { self.#field.len() } }
    }).collect();

    // alloc_children_* methods (one per (owning_sort, child_sort) variadic pair)
    let alloc_methods: Vec<TokenStream2> = sorts.iter().enumerate().flat_map(|(si, _)| {
        sort_variadic_child_sorts[si].iter().map(move |&ci| {
            let method = format_ident!("alloc_{}_{}", sort_lowers[si], sort_lowers[ci]);
            let pool_field = format_ident!("{}_pool_{}", sort_lowers[si], sort_lowers[ci]);
            let id = format_ident!("{}Id", sort_names[ci]);
            quote! {
                #vis fn #method(&mut self, children: &[#id]) -> ::semi_persistent_traversals::Variadic<#id> {
                    let start = self.#pool_field.len() as u32;
                    self.#pool_field.extend_from_slice(children);
                    ::semi_persistent_traversals::Variadic::Span { start, len: children.len() as u32 }
                }
            }
        })
    }).collect();

    // mark
    let mark_arena_inits: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_len", sort_lowers[i]);
        let arena_field = format_ident!("{}_nodes", sort_lowers[i]);
        quote! { #field: self.#arena_field.len() }
    }).collect();
    let mark_pool_inits: Vec<TokenStream2> = sorts.iter().enumerate().flat_map(|(si, _)| {
        sort_variadic_child_sorts[si].iter().map(move |&ci| {
            let field = format_ident!("{}_pool_{}_len", sort_lowers[si], sort_lowers[ci]);
            let pool_field = format_ident!("{}_pool_{}", sort_lowers[si], sort_lowers[ci]);
            quote! { #field: self.#pool_field.len() }
        })
    }).collect();

    // restore
    let restore_arenas: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_len", sort_lowers[i]);
        let arena_field = format_ident!("{}_nodes", sort_lowers[i]);
        quote! { self.#arena_field.truncate(mark.#field); }
    }).collect();
    let restore_pools: Vec<TokenStream2> = sorts.iter().enumerate().flat_map(|(si, _)| {
        sort_variadic_child_sorts[si].iter().map(move |&ci| {
            let field = format_ident!("{}_pool_{}_len", sort_lowers[si], sort_lowers[ci]);
            let pool_field = format_ident!("{}_pool_{}", sort_lowers[si], sort_lowers[ci]);
            quote! { self.#pool_field.truncate(mark.#field); }
        })
    }).collect();

    // Default field inits
    let arena_defaults: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_nodes", sort_lowers[i]);
        quote! { #field: Vec::new() }
    }).collect();
    let pool_defaults: Vec<TokenStream2> = sorts.iter().enumerate().flat_map(|(si, _)| {
        sort_variadic_child_sorts[si].iter().map(move |&ci| {
            let field = format_ident!("{}_pool_{}", sort_lowers[si], sort_lowers[ci]);
            quote! { #field: Vec::new() }
        })
    }).collect();
    let dedup_defaults_none: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_dedup", sort_lowers[i]);
        quote! { #field: None }
    }).collect();
    let dedup_defaults_some: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_dedup", sort_lowers[i]);
        quote! { #field: Some(::semi_persistent_traversals::FxHashMap::default()) }
    }).collect();

    // On restore, drop nodes beyond the mark AND invalidate dedup entries pointing past the mark.
    let restore_dedup_prune: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let field = format_ident!("{}_dedup", sort_lowers[i]);
        let len_field = format_ident!("{}_len", sort_lowers[i]);
        quote! {
            if let Some(ref mut idx_map) = self.#field {
                idx_map.retain(|_, v| *v < mark.#len_field);
            }
        }
    }).collect();

    quote! {
        #[derive(Clone, Debug)]
        #vis struct #mark_name {
            #(#mark_arena_fields,)*
            #(#mark_pool_fields,)*
        }

        #[derive(Clone)]
        #vis struct #store {
            #(#arena_fields,)*
            #(#pool_fields,)*
            #(#dedup_fields,)*
        }

        impl #store {
            #vis fn new() -> Self {
                Self { #(#arena_defaults,)* #(#pool_defaults,)* #(#dedup_defaults_none,)* }
            }

            /// Build a deduplicating store. `push_*` returns an existing id if a structurally
            /// identical node has already been pushed (hash-consing).
            #vis fn new_dedup() -> Self {
                Self { #(#arena_defaults,)* #(#pool_defaults,)* #(#dedup_defaults_some,)* }
            }

            #(#push_methods)*
            #(#get_methods)*
            #(#len_methods)*
            #(#alloc_methods)*

            #vis fn mark(&self) -> #mark_name {
                #mark_name { #(#mark_arena_inits,)* #(#mark_pool_inits,)* }
            }

            #vis fn restore(&mut self, mark: &#mark_name) {
                #(#restore_arenas)*
                #(#restore_pools)*
                #(#restore_dedup_prune)*
            }
        }
    }
}

// Helper: for a given sort, collect the sorted-deduped child sort indices
fn child_sort_indices(sort: &ResolvedSort) -> Vec<usize> {
    let mut cs: Vec<usize> = sort.variants.iter()
        .flat_map(|v| v.fields.iter().filter_map(|f| match f {
            FieldKind::Child(i) | FieldKind::VariadicChild(i) => Some(*i),
            _ => None,
        }))
        .collect();
    cs.sort();
    cs.dedup();
    cs
}

// Helper: generate children_into arms for a node enum (pushes typed IDs into per-sort buffers)
fn gen_children_into_arms(
    sort: &ResolvedSort,
    sort_names: &[&syn::Ident],
    si: usize,
) -> Vec<TokenStream2> {
    let node_name = format_ident!("{}Node", sort_names[si]);
    sort.variants.iter().map(|v| {
        let vn = &v.name;
        if v.fields.is_empty() {
            return quote! { #node_name::#vn => {} };
        }
        let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
        let pushes: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).filter_map(|(b, fk)| {
            match fk {
                FieldKind::Child(j) => {
                    let buf = format_ident!("__ch{}", j);
                    Some(quote! { #buf.push(*#b); })
                }
                FieldKind::VariadicChild(j) => {
                    let buf = format_ident!("__ch{}", j);
                    Some(quote! { for __c in #b.iter() { #buf.push(*__c); } })
                }
                FieldKind::Data(_) => None,
            }
        }).collect();
        quote! { #node_name::#vn(#(#bs),*) => { #(#pushes)* } }
    }).collect()
}

fn gen_fold(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let result_name = format_ident!("{}FoldResult", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();

    // Algebra params: one per sort
    let alg_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__alg{}", i);
        let a = &aps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<&syn::Ident> = cs.iter().map(|&j| &aps[j]).collect();
        quote! { #p: impl Fn(#mapped<#(#params),*>) -> #a }
    }).collect();
    let alg_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__alg{}", i)).collect();

    // Task enum variants: one Enter + one Eval per sort
    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    // Per-sort memo tables (M::Memo<A>)
    let memo_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let a = &aps[i];
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #memo: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> as ::semi_persistent_traversals::MemoOps<#a>>::new(__store.#len_method()); }
    }).collect();

    // Per-sort child buffers
    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    // Enter arms: push Eval, then push children
    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let memo_child = format_ident!("__memo{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if <M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                        || ::semi_persistent_traversals::MemoOps::get(&#memo_child, __c.0).is_none()
                    {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match __store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    // Eval arms: map_children with memo lookups, call algebra
    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let alg = format_ident!("__alg{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap().clone() }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                let __mapped = __store.#get_method(__id).map_children(#(#closure_args),*);
                ::semi_persistent_traversals::MemoOps::set(&mut #memo, __id.0, #alg(__mapped));
            }
        }
    }).collect();

    // Return: match on root, extract from appropriate memo
    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let memo = format_ident!("__memo{}", i);
        quote! { #root_name::#sn(__id) => #result_name::#sn(::semi_persistent_traversals::MemoOps::take(&mut #memo, __id.0).unwrap()) }
    }).collect();

    // Initial stack push
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn fold<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                let __store = self.store;
                enum __Task { #(#task_variants),* }
                #(#memo_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                match __root { #(#return_arms),* }
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn fold<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().fold(__root, #(#alg_args),*)
            }
        }
    }
}

fn gen_fold_all(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let result_name = format_ident!("{}FoldResult", store);
    let root_name = format_ident!("{}Root", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();
    let alg_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__alg{}", i);
        let a = &aps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<&syn::Ident> = cs.iter().map(|&j| &aps[j]).collect();
        quote! { #p: impl Fn(#mapped<#(#params),*>) -> #a }
    }).collect();

    let cache_name = format_ident!("{}FoldCache", store);
    let cache_fields: Vec<TokenStream2> = (0..n).map(|i| {
        let field = format_ident!("{}", sort_lowers[i]);
        let a = &aps[i];
        quote! { #vis #field: Vec<#a> }
    }).collect();
    let cache_index_impls: Vec<TokenStream2> = (0..n).map(|i| {
        let field = format_ident!("{}", sort_lowers[i]);
        let a = &aps[i];
        let id = format_ident!("{}Id", sort_names[i]);
        quote! {
            impl<#(#aps),*> std::ops::Index<#id> for #cache_name<#(#aps),*> {
                type Output = #a;
                fn index(&self, id: #id) -> &#a { &self.#field[id.0] }
            }
        }
    }).collect();

    // fold_all: fold every node in every sort. Use the rooted fold for each node.
    // Actually, the most efficient approach: allocate per-sort result vecs,
    // then iterate all nodes of all sorts using the worklist.
    // Simpler: just call fold for every node. But that's O(n^2) in the worst case.
    // Better: single worklist pass over all nodes.

    let alg_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__alg{}", i)).collect();

    let memo_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let a = &aps[i];
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #memo: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> as ::semi_persistent_traversals::MemoOps<#a>>::new(__store.#len_method()); }
    }).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let memo_child = format_ident!("__memo{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if <M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                        || ::semi_persistent_traversals::MemoOps::get(&#memo_child, __c.0).is_none()
                    {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match __store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let alg = format_ident!("__alg{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap().clone() }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                let __mapped = __store.#get_method(__id).map_children(#(#closure_args),*);
                ::semi_persistent_traversals::MemoOps::set(&mut #memo, __id.0, #alg(__mapped));
            }
        }
    }).collect();

    // Seed the worklist with all nodes of all sorts
    let seed_all: Vec<TokenStream2> = (0..n).map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { for __i in 0..__store.#len_method() { __stack.push(__Task::#enter(#id(__i))); } }
    }).collect();

    // Collect results into cache using MemoOps::take on every index
    let collect_results: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let field = format_ident!("{}", sort_lowers[i]);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { #field: (0..__store.#len_method()).map(|__k| ::semi_persistent_traversals::MemoOps::take(&mut #memo, __k).unwrap()).collect() }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #vis struct #cache_name<#(#aps),*> { #(#cache_fields),* }
        #(#cache_index_impls)*

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn fold_all<#(#aps: Clone),*>(
                &self,
                #(#alg_params),*
            ) -> #cache_name<#(#aps),*> {
                let __store = self.store;
                enum __Task { #(#task_variants),* }
                #(#memo_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                #(#seed_all)*
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                #cache_name { #(#collect_results),* }
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn fold_all<#(#aps: Clone),*>(
                &self,
                #(#alg_params),*
            ) -> #cache_name<#(#aps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().fold_all(#(#alg_args),*)
            }
        }
    }
}

fn gen_para(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let result_name = format_ident!("{}FoldResult", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();

    // Para algebra: children are (SortId, A)
    let alg_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__alg{}", i);
        let a = &aps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<TokenStream2> = cs.iter().map(|&j| {
            let id = format_ident!("{}Id", sort_names[j]);
            let aj = &aps[j];
            quote! { (#id, #aj) }
        }).collect();
        quote! { #p: impl Fn(#mapped<#(#params),*>) -> #a }
    }).collect();

    let alg_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__alg{}", i)).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    let memo_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let a = &aps[i];
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #memo: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> as ::semi_persistent_traversals::MemoOps<#a>>::new(__store.#len_method()); }
    }).collect();

    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let memo_child = format_ident!("__memo{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if <M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                        || ::semi_persistent_traversals::MemoOps::get(&#memo_child, __c.0).is_none()
                    {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match __store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let alg = format_ident!("__alg{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| (*__c, ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap().clone()) }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                let __mapped = __store.#get_method(__id).map_children(#(#closure_args),*);
                ::semi_persistent_traversals::MemoOps::set(&mut #memo, __id.0, #alg(__mapped));
            }
        }
    }).collect();

    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let memo = format_ident!("__memo{}", i);
        quote! { #root_name::#sn(__id) => #result_name::#sn(::semi_persistent_traversals::MemoOps::take(&mut #memo, __id.0).unwrap()) }
    }).collect();
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn fold_with_ids<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                let __store = self.store;
                enum __Task { #(#task_variants),* }
                #(#memo_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                match __root { #(#return_arms),* }
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn fold_with_ids<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().fold_with_ids(__root, #(#alg_args),*)
            }
        }
    }
}

fn gen_transform(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);

    let rule_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let p = format_ident!("__rule{}", i);
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #p: impl Fn(#node) -> #node }
    }).collect();
    let rule_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__rule{}", i)).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    // Mapping: store raw usize (new id inside the new store), wrap in typed id at read.
    // Using M::Mapping keeps dense/sparse options.
    let mapping_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let m = format_ident!("__map{}", i);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #m: <M as ::semi_persistent_traversals::MemoStrategy>::Mapping = <<M as ::semi_persistent_traversals::MemoStrategy>::Mapping as ::semi_persistent_traversals::MappingOps>::new(self.store.#len_method()); }
    }).collect();
    let visited_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let v = format_ident!("__vis{}", i);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #v: <M as ::semi_persistent_traversals::MemoStrategy>::Visit = <<M as ::semi_persistent_traversals::MemoStrategy>::Visit as ::semi_persistent_traversals::VisitOps>::new(self.store.#len_method()); }
    }).collect();

    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let vis_si = format_ident!("__vis{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let vis_j = format_ident!("__vis{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if !::semi_persistent_traversals::VisitOps::visited(&#vis_j, __c.0) {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if ::semi_persistent_traversals::VisitOps::visited(&#vis_si, __id.0) { continue; }
                ::semi_persistent_traversals::VisitOps::mark(&mut #vis_si, __id.0);
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match self.store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let rule = format_ident!("__rule{}", si);
        let map_si = format_ident!("__map{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let push_method = format_ident!("push_{}", sort_lowers[si]);
        let node_name = format_ident!("{}Node", sort_names[si]);
        let remap_arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => #node_name::#vn };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let mapped: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let m = format_ident!("__map{}", j);
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { #jid(::semi_persistent_traversals::MappingOps::get(&#m, #b.0)) }
                }
                FieldKind::VariadicChild(j) => {
                    let m = format_ident!("__map{}", j);
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| #jid(::semi_persistent_traversals::MappingOps::get(&#m, __c.0))).collect()) }
                }
                FieldKind::Data(_) => quote! { #b.clone() },
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => #node_name::#vn(#(#mapped),*) }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                let __remapped = match self.store.#get_method(__id) { #(#remap_arms),* };
                let __new_id = __new.#push_method(#rule(__remapped));
                ::semi_persistent_traversals::MappingOps::set(&mut #map_si, __id.0, __new_id.0);
            }
        }
    }).collect();

    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let m = format_ident!("__map{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { #root_name::#sn(__id) => #root_name::#sn(#id(::semi_persistent_traversals::MappingOps::get(&#m, __id.0))) }
    }).collect();
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn transform(
                &self,
                __root: #root_name,
                #(#rule_params),*
            ) -> (#store, #root_name) {
                enum __Task { #(#task_variants),* }
                let mut __new = #store::new();
                #(#mapping_decls)*
                #(#visited_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                let __new_root = match __root { #(#return_arms),* };
                (__new, __new_root)
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn transform(
                &self,
                __root: #root_name,
                #(#rule_params),*
            ) -> (#store, #root_name) {
                self.with_strategy::<::semi_persistent_traversals::Dense>().transform(__root, #(#rule_args),*)
            }
        }
    }
}

fn gen_histo(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let result_name = format_ident!("{}FoldResult", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();

    // Histo algebra: children are Ann<A> where Ann carries value + child indices
    // For partition, we use a per-sort Ann that wraps the result
    let alg_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__alg{}", i);
        let a = &aps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<TokenStream2> = cs.iter().map(|&j| {
            let aj = &aps[j];
            quote! { ::semi_persistent_traversals::Ann<#aj> }
        }).collect();
        quote! { #p: impl Fn(#mapped<#(#params),*>) -> #a }
    }).collect();

    let alg_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__alg{}", i)).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    let memo_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let a = &aps[i];
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #memo: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<::semi_persistent_traversals::Ann<#a>> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<::semi_persistent_traversals::Ann<#a>> as ::semi_persistent_traversals::MemoOps<::semi_persistent_traversals::Ann<#a>>>::new(__store.#len_method()); }
    }).collect();

    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let memo_child = format_ident!("__memo{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if <M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                        || ::semi_persistent_traversals::MemoOps::get(&#memo_child, __c.0).is_none()
                    {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match __store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let alg = format_ident!("__alg{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| {
                let __ann = ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap();
                ::semi_persistent_traversals::Ann { value: __ann.value.clone(), children: __ann.children.clone() }
            }}
        }).collect();
        let collect_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let extend_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { for &__c in #buf.iter() { __all_children.push(__c.0); } }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                #(#collect_children)*
                match __store.#get_method(__id) { #(#children_arms)* }
                let mut __all_children = ::smallvec::SmallVec::<[usize; 8]>::new();
                #(#extend_children)*
                let __mapped = __store.#get_method(__id).map_children(#(#closure_args),*);
                let __value = #alg(__mapped);
                ::semi_persistent_traversals::MemoOps::set(&mut #memo, __id.0, ::semi_persistent_traversals::Ann { value: __value, children: __all_children });
            }
        }
    }).collect();

    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let memo = format_ident!("__memo{}", i);
        quote! { #root_name::#sn(__id) => #result_name::#sn(::semi_persistent_traversals::MemoOps::take(&mut #memo, __id.0).unwrap().value) }
    }).collect();
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn fold_with_history<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                let __store = self.store;
                enum __Task { #(#task_variants),* }
                #(#memo_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                match __root { #(#return_arms),* }
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn fold_with_history<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().fold_with_history(__root, #(#alg_args),*)
            }
        }
    }
}

fn gen_zygo(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let result_name = format_ident!("{}FoldResult", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();
    let bps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__B{}", i)).collect();

    // Aux algebra: children are B
    let aux_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__aux{}", i);
        let b = &bps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<&syn::Ident> = cs.iter().map(|&j| &bps[j]).collect();
        quote! { #p: impl Fn(#mapped<#(#params),*>) -> #b }
    }).collect();

    // Main algebra: children are (A, B)
    let main_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__main{}", i);
        let a = &aps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<TokenStream2> = cs.iter().map(|&j| {
            let aj = &aps[j];
            let bj = &bps[j];
            quote! { (#aj, #bj) }
        }).collect();
        quote! { #p: impl Fn(#mapped<#(#params),*>) -> #a }
    }).collect();

    let aux_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__aux{}", i)).collect();
    let main_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__main{}", i)).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    let memo_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let a = &aps[i];
        let b = &bps[i];
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #memo: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<(#a, #b)> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<(#a, #b)> as ::semi_persistent_traversals::MemoOps<(#a, #b)>>::new(__store.#len_method()); }
    }).collect();

    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let memo_child = format_ident!("__memo{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if <M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                        || ::semi_persistent_traversals::MemoOps::get(&#memo_child, __c.0).is_none()
                    {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match __store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let alg_aux = format_ident!("__aux{}", si);
        let alg_main = format_ident!("__main{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let aux_closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap().1.clone() }
        }).collect();
        let main_closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap().clone() }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                let __b = #alg_aux(__store.#get_method(__id).map_children(#(#aux_closure_args),*));
                let __a = #alg_main(__store.#get_method(__id).map_children(#(#main_closure_args),*));
                ::semi_persistent_traversals::MemoOps::set(&mut #memo, __id.0, (__a, __b));
            }
        }
    }).collect();

    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let memo = format_ident!("__memo{}", i);
        quote! { #root_name::#sn(__id) => #result_name::#sn(::semi_persistent_traversals::MemoOps::take(&mut #memo, __id.0).unwrap().0) }
    }).collect();
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn fold_with_aux<#(#aps: Clone,)* #(#bps: Clone),*>(
                &self,
                __root: #root_name,
                #(#aux_params,)*
                #(#main_params),*
            ) -> #result_name<#(#aps),*> {
                let __store = self.store;
                enum __Task { #(#task_variants),* }
                #(#memo_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                match __root { #(#return_arms),* }
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn fold_with_aux<#(#aps: Clone,)* #(#bps: Clone),*>(
                &self,
                __root: #root_name,
                #(#aux_params,)*
                #(#main_params),*
            ) -> #result_name<#(#aps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().fold_with_aux(__root, #(#aux_args,)* #(#main_args),*)
            }
        }
    }
}

fn gen_fold_short(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let result_name = format_ident!("{}FoldResult", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();

    let alg_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__alg{}", i);
        let a = &aps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<&syn::Ident> = cs.iter().map(|&j| &aps[j]).collect();
        quote! { #p: impl Fn(#mapped<#(#params),*>) -> Result<#a, #a> }
    }).collect();
    let alg_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__alg{}", i)).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    let memo_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let a = &aps[i];
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #memo: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> as ::semi_persistent_traversals::MemoOps<#a>>::new(__store.#len_method()); }
    }).collect();

    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let memo_child = format_ident!("__memo{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if <M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                        || ::semi_persistent_traversals::MemoOps::get(&#memo_child, __c.0).is_none()
                    {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match __store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let alg = format_ident!("__alg{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let sn = sort_names[si];
        let cs = child_sort_indices(sort);
        let closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap().clone() }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                let __mapped = __store.#get_method(__id).map_children(#(#closure_args),*);
                match #alg(__mapped) {
                    Ok(__v) => { ::semi_persistent_traversals::MemoOps::set(&mut #memo, __id.0, __v); }
                    Err(__v) => return #result_name::#sn(__v),
                }
            }
        }
    }).collect();

    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let memo = format_ident!("__memo{}", i);
        quote! { #root_name::#sn(__id) => #result_name::#sn(::semi_persistent_traversals::MemoOps::take(&mut #memo, __id.0).unwrap()) }
    }).collect();
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn fold_short<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                let __store = self.store;
                enum __Task { #(#task_variants),* }
                #(#memo_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                match __root { #(#return_arms),* }
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn fold_short<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().fold_short(__root, #(#alg_args),*)
            }
        }
    }
}

fn gen_fold_with_original(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let result_name = format_ident!("{}FoldResult", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();

    let alg_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__alg{}", i);
        let a = &aps[i];
        let node = format_ident!("{}Node", sort_names[i]);
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<&syn::Ident> = cs.iter().map(|&j| &aps[j]).collect();
        quote! { #p: impl Fn(&#node, #mapped<#(#params),*>) -> #a }
    }).collect();

    let alg_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__alg{}", i)).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    let memo_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let a = &aps[i];
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #memo: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<#a> as ::semi_persistent_traversals::MemoOps<#a>>::new(__store.#len_method()); }
    }).collect();

    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let memo_child = format_ident!("__memo{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if <M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                        || ::semi_persistent_traversals::MemoOps::get(&#memo_child, __c.0).is_none()
                    {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match __store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let alg = format_ident!("__alg{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap().clone() }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                let __orig = __store.#get_method(__id);
                let __mapped = __orig.map_children(#(#closure_args),*);
                ::semi_persistent_traversals::MemoOps::set(&mut #memo, __id.0, #alg(__orig, __mapped));
            }
        }
    }).collect();

    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let memo = format_ident!("__memo{}", i);
        quote! { #root_name::#sn(__id) => #result_name::#sn(::semi_persistent_traversals::MemoOps::take(&mut #memo, __id.0).unwrap()) }
    }).collect();
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn fold_with_original<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                let __store = self.store;
                enum __Task { #(#task_variants),* }
                #(#memo_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                match __root { #(#return_arms),* }
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn fold_with_original<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().fold_with_original(__root, #(#alg_args),*)
            }
        }
    }
}

fn gen_unfold(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
    _sort_variadic_child_sorts: &[Vec<usize>],
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let seed_name = format_ident!("{}Seed", store);
    let layer_name = format_ident!("{}Layer", store);
    let skel_name = format_ident!("__{}Skel", store);

    let seed_variants: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        quote! { #sn(S) }
    }).collect();
    let layer_variants: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #sn(#node, Vec<#seed_name<S>>) }
    }).collect();
    let skel_variants: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #sn(#node) }
    }).collect();

    let expand_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        quote! {
            #layer_name::#sn(__node, __child_seeds) => {
                let __nc = __child_seeds.len();
                __nodes.push((__nc, #skel_name::#sn(__node)));
                __work.push(__AnaTask::Build);
                for __cs in __child_seeds.into_iter().rev() {
                    __work.push(__AnaTask::Expand(__cs));
                }
            }
        }
    }).collect();

    let build_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let sn = sort_names[si];
        let push_method = format_ident!("push_{}", sort_lowers[si]);
        let node_name = format_ident!("{}Node", sort_names[si]);
        let remap_arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => #node_name::#vn };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let mapped: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let jsn = sort_names[*j];
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { match __child_results[__ci] { #root_name::#jsn(__id) => { __ci += 1; __id }, _ => panic!("sort mismatch") } }
                }
                FieldKind::VariadicChild(j) => {
                    let jsn = sort_names[*j];
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { {
                        let __vlen = #b.len();
                        let __v: ::smallvec::SmallVec<[#jid; 4]> = (0..__vlen).map(|_| {
                            match __child_results[__ci] { #root_name::#jsn(__id) => { __ci += 1; __id }, _ => panic!("sort mismatch") }
                        }).collect();
                        ::semi_persistent_traversals::Variadic::Resolved(__v)
                    }}
                }
                FieldKind::Data(_) => quote! { #b.clone() },
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => #node_name::#vn(#(#mapped),*) }
        }).collect();
        quote! {
            #skel_name::#sn(__skel) => {
                let mut __ci = 0usize;
                let __remapped = match __skel { #(#remap_arms),* };
                let __new_id = __store.#push_method(__remapped);
                __results.push(#root_name::#sn(__new_id));
            }
        }
    }).collect();

    quote! {
        #[derive(Clone, Debug)]
        #vis enum #seed_name<S> { #(#seed_variants),* }
        #[derive(Clone, Debug)]
        #vis enum #layer_name<S> { #(#layer_variants),* }

        #[allow(non_snake_case, clippy::too_many_arguments, unreachable_patterns)]
        impl #store {
            #vis fn unfold<S>(
                &mut self,
                seed: #seed_name<S>,
                coalg: impl Fn(#seed_name<S>) -> #layer_name<S>,
            ) -> #root_name {
                enum #skel_name { #(#skel_variants),* }
                enum __AnaTask<S> { Expand(S), Build }
                let __store = self;
                let mut __work: Vec<__AnaTask<#seed_name<S>>> = Vec::new();
                let mut __results: Vec<#root_name> = Vec::new();
                let mut __nodes: Vec<(usize, #skel_name)> = Vec::new();
                __work.push(__AnaTask::Expand(seed));
                while let Some(__task) = __work.pop() {
                    match __task {
                        __AnaTask::Expand(__s) => {
                            match coalg(__s) { #(#expand_arms)* }
                        }
                        __AnaTask::Build => {
                            let (__nc, __tagged) = __nodes.pop().unwrap();
                            let __start = __results.len() - __nc;
                            let __child_results: Vec<#root_name> = __results.drain(__start..).collect();
                            match __tagged { #(#build_arms)* }
                        }
                    }
                }
                __results.pop().unwrap()
            }
        }
    }
}


fn gen_refold(
    _vis: &syn::Visibility,
    _store: &syn::Ident,
    _sorts: &[ResolvedSort],
    _sort_names: &[&syn::Ident],
    _sort_lowers: &[syn::Ident],
    _n: usize,
) -> TokenStream2 {
    quote! {}
}

fn gen_rewrite(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);

    // One rule per sort: takes (remapped node, &mut Store) -> SortId
    let rule_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, _)| {
        let p = format_ident!("__rule{}", i);
        let node = format_ident!("{}Node", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { #p: impl Fn(#node, &mut #store) -> #id }
    }).collect();
    let rule_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__rule{}", i)).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    let mapping_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let m = format_ident!("__map{}", i);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #m: <M as ::semi_persistent_traversals::MemoStrategy>::Mapping = <<M as ::semi_persistent_traversals::MemoStrategy>::Mapping as ::semi_persistent_traversals::MappingOps>::new(self.store.#len_method()); }
    }).collect();
    let visited_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let v = format_ident!("__vis{}", i);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #v: <M as ::semi_persistent_traversals::MemoStrategy>::Visit = <<M as ::semi_persistent_traversals::MemoStrategy>::Visit as ::semi_persistent_traversals::VisitOps>::new(self.store.#len_method()); }
    }).collect();
    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let vis_si = format_ident!("__vis{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let vis_j = format_ident!("__vis{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if !::semi_persistent_traversals::VisitOps::visited(&#vis_j, __c.0) {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if ::semi_persistent_traversals::VisitOps::visited(&#vis_si, __id.0) { continue; }
                ::semi_persistent_traversals::VisitOps::mark(&mut #vis_si, __id.0);
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match self.store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let rule = format_ident!("__rule{}", si);
        let map_si = format_ident!("__map{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let node_name = format_ident!("{}Node", sort_names[si]);
        let remap_arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => #node_name::#vn };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let mapped: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let m = format_ident!("__map{}", j);
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { #jid(::semi_persistent_traversals::MappingOps::get(&#m, #b.0)) }
                }
                FieldKind::VariadicChild(j) => {
                    let m = format_ident!("__map{}", j);
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| #jid(::semi_persistent_traversals::MappingOps::get(&#m, __c.0))).collect()) }
                }
                FieldKind::Data(_) => quote! { #b.clone() },
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => #node_name::#vn(#(#mapped),*) }
        }).collect();
        quote! {
            __Task::#eval(__id) => {
                let __remapped = match self.store.#get_method(__id) { #(#remap_arms),* };
                let __new_id = #rule(__remapped, &mut __new);
                ::semi_persistent_traversals::MappingOps::set(&mut #map_si, __id.0, __new_id.0);
            }
        }
    }).collect();

    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let m = format_ident!("__map{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { #root_name::#sn(__id) => #root_name::#sn(#id(::semi_persistent_traversals::MappingOps::get(&#m, __id.0))) }
    }).collect();
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn rewrite(
                &self,
                __root: #root_name,
                #(#rule_params),*
            ) -> (#store, #root_name) {
                enum __Task { #(#task_variants),* }
                let mut __new = #store::new();
                #(#mapping_decls)*
                #(#visited_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                let __new_root = match __root { #(#return_arms),* };
                (__new, __new_root)
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn rewrite(
                &self,
                __root: #root_name,
                #(#rule_params),*
            ) -> (#store, #root_name) {
                self.with_strategy::<::semi_persistent_traversals::Dense>().rewrite(__root, #(#rule_args),*)
            }
        }
    }
}


fn gen_unfold_short(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let seed_name = format_ident!("{}Seed", store);
    let apo_name = format_ident!("{}ApoSeed", store);
    let layer_name = format_ident!("{}ApoLayer", store);
    let skel_name = format_ident!("__{}ApoSkel", store);

    let apo_variants: Vec<TokenStream2> = {
        let mut v = vec![quote! { Continue(#seed_name<S>) }];
        for i in 0..n {
            let id = format_ident!("{}Id", sort_names[i]);
            let done = format_ident!("Done{}", sort_names[i]);
            v.push(quote! { #done(#id) });
        }
        v
    };
    let layer_variants: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #sn(#node, Vec<#apo_name<S>>) }
    }).collect();
    let skel_variants: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #sn(#node) }
    }).collect();

    let cont_to_task: Vec<TokenStream2> = {
        let mut v = vec![quote! { #apo_name::Continue(__s) => __ApoTask::Expand(__s) }];
        for i in 0..n {
            let sn = sort_names[i];
            let done = format_ident!("Done{}", sort_names[i]);
            v.push(quote! { #apo_name::#done(__id) => __ApoTask::Literal(#root_name::#sn(__id)) });
        }
        v
    };
    let expand_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let cont_arms = cont_to_task.clone();
        quote! {
            #layer_name::#sn(__node, __child_seeds) => {
                let __nc = __child_seeds.len();
                __nodes.push((__nc, #skel_name::#sn(__node)));
                __work.push(__ApoTask::Build);
                for __cs in __child_seeds.into_iter().rev() {
                    __work.push(match __cs { #(#cont_arms),* });
                }
            }
        }
    }).collect();

    let build_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let sn = sort_names[si];
        let push_method = format_ident!("push_{}", sort_lowers[si]);
        let node_name = format_ident!("{}Node", sort_names[si]);
        let remap_arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => #node_name::#vn };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let mapped: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let jsn = sort_names[*j];
                    quote! { match __child_results[__ci] { #root_name::#jsn(__id) => { __ci += 1; __id }, _ => panic!("sort mismatch") } }
                }
                FieldKind::VariadicChild(j) => {
                    let jsn = sort_names[*j];
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { {
                        let __vlen = #b.len();
                        let __v: ::smallvec::SmallVec<[#jid; 4]> = (0..__vlen).map(|_| {
                            match __child_results[__ci] { #root_name::#jsn(__id) => { __ci += 1; __id }, _ => panic!("sort mismatch") }
                        }).collect();
                        ::semi_persistent_traversals::Variadic::Resolved(__v)
                    }}
                }
                FieldKind::Data(_) => quote! { #b.clone() },
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => #node_name::#vn(#(#mapped),*) }
        }).collect();
        quote! {
            #skel_name::#sn(__skel) => {
                let mut __ci = 0usize;
                let __remapped = match __skel { #(#remap_arms),* };
                let __new_id = __store.#push_method(__remapped);
                __results.push(#root_name::#sn(__new_id));
            }
        }
    }).collect();

    quote! {
        #[derive(Clone, Debug)]
        #vis enum #apo_name<S> { #(#apo_variants),* }
        #[derive(Clone, Debug)]
        #vis enum #layer_name<S> { #(#layer_variants),* }

        #[allow(non_snake_case, clippy::too_many_arguments, unreachable_patterns)]
        impl #store {
            #vis fn unfold_short<S>(
                &mut self,
                seed: #seed_name<S>,
                coalg: impl Fn(#seed_name<S>) -> #layer_name<S>,
            ) -> #root_name {
                enum #skel_name { #(#skel_variants),* }
                enum __ApoTask<S> { Expand(S), Build, Literal(#root_name) }
                let __store = self;
                let mut __work: Vec<__ApoTask<#seed_name<S>>> = Vec::new();
                let mut __results: Vec<#root_name> = Vec::new();
                let mut __nodes: Vec<(usize, #skel_name)> = Vec::new();
                __work.push(__ApoTask::Expand(seed));
                while let Some(__task) = __work.pop() {
                    match __task {
                        __ApoTask::Expand(__s) => {
                            match coalg(__s) { #(#expand_arms)* }
                        }
                        __ApoTask::Literal(__r) => {
                            __results.push(__r);
                        }
                        __ApoTask::Build => {
                            let (__nc, __tagged) = __nodes.pop().unwrap();
                            let __start = __results.len() - __nc;
                            let __child_results: Vec<#root_name> = __results.drain(__start..).collect();
                            match __tagged { #(#build_arms)* }
                        }
                    }
                }
                __results.pop().unwrap()
            }
        }
    }
}


fn gen_fold_pair(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();
    let bps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__B{}", i)).collect();

    // Two algebra closures per sort: one returns A_i, one returns B_i, both see (A_j, B_j) children.
    let alg_params: Vec<TokenStream2> = sorts.iter().enumerate().flat_map(|(i, sort)| {
        let pa = format_ident!("__alg_a{}", i);
        let pb = format_ident!("__alg_b{}", i);
        let a = &aps[i];
        let b = &bps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let child_tuples: Vec<TokenStream2> = cs.iter().map(|&j| {
            let aj = &aps[j]; let bj = &bps[j];
            quote! { (#aj, #bj) }
        }).collect();
        vec![
            quote! { #pa: impl Fn(#mapped<#(#child_tuples),*>) -> #a },
            quote! { #pb: impl Fn(#mapped<#(#child_tuples),*>) -> #b },
        ]
    }).collect();

    let alg_args: Vec<syn::Ident> = (0..n).flat_map(|i| vec![format_ident!("__alg_a{}", i), format_ident!("__alg_b{}", i)]).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let eval = format_ident!("Eval{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
    }).collect();

    let memo_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let memo = format_ident!("__memo{}", i);
        let a = &aps[i]; let b = &bps[i];
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #memo: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<(#a, #b)> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<(#a, #b)> as ::semi_persistent_traversals::MemoOps<(#a, #b)>>::new(__store.#len_method()); }
    }).collect();

    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let children_arms = gen_children_into_arms(sort, sort_names, si);
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let memo_child = format_ident!("__memo{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if <M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                        || ::semi_persistent_traversals::MemoOps::get(&#memo_child, __c.0).is_none()
                    {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                __stack.push(__Task::#eval(__id));
                #(#clear_bufs)*
                match __store.#get_method(__id) { #(#children_arms)* }
                #(#push_children)*
            }
        }
    }).collect();

    let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let eval = format_ident!("Eval{}", sort_names[si]);
        let memo = format_ident!("__memo{}", si);
        let alg_a = format_ident!("__alg_a{}", si);
        let alg_b = format_ident!("__alg_b{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let closure_args: Vec<TokenStream2> = cs.iter().map(|&j| {
            let memo_j = format_ident!("__memo{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { &mut |__c: &#id| ::semi_persistent_traversals::MemoOps::get(&#memo_j, __c.0).unwrap().clone() }
        }).collect();
        let closure_args2 = closure_args.clone();
        quote! {
            __Task::#eval(__id) => {
                if !<M as ::semi_persistent_traversals::MemoStrategy>::NO_MEMO
                    && ::semi_persistent_traversals::MemoOps::get(&#memo, __id.0).is_some()
                {
                    continue;
                }
                let __for_a = __store.#get_method(__id).map_children(#(#closure_args),*);
                let __for_b = __store.#get_method(__id).map_children(#(#closure_args2),*);
                let __a = #alg_a(__for_a);
                let __b = #alg_b(__for_b);
                ::semi_persistent_traversals::MemoOps::set(&mut #memo, __id.0, (__a, __b));
            }
        }
    }).collect();

    let result_name = format_ident!("{}FoldPairResult", store);
    let res_variants: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let a = &aps[i]; let b = &bps[i];
        quote! { #sn(#a, #b) }
    }).collect();
    let unwrap_fns: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let a = &aps[i]; let b = &bps[i];
        let fn_name = format_ident!("unwrap_{}", sort_names[i].to_string().to_lowercase());
        quote! {
            #vis fn #fn_name(self) -> (#a, #b) {
                match self { #result_name::#sn(__a, __b) => (__a, __b), _ => panic!("sort mismatch") }
            }
        }
    }).collect();

    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let memo = format_ident!("__memo{}", i);
        quote! { #root_name::#sn(__id) => { let (__a, __b) = ::semi_persistent_traversals::MemoOps::take(&mut #memo, __id.0).unwrap(); #result_name::#sn(__a, __b) } }
    }).collect();
    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();

    let a_params_a: Vec<TokenStream2> = aps.iter().map(|a| quote! { #a: Clone }).collect();
    let b_params_b: Vec<TokenStream2> = bps.iter().map(|b| quote! { #b: Clone }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[derive(Clone, Debug)]
        #vis enum #result_name<#(#aps),*, #(#bps),*> { #(#res_variants),* }
        impl<#(#aps),*, #(#bps),*> #result_name<#(#aps),*, #(#bps),*> {
            #(#unwrap_fns)*
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn fold_pair<#(#a_params_a),*, #(#b_params_b),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*, #(#bps),*> {
                let __store = self.store;
                enum __Task { #(#task_variants),* }
                #(#memo_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                match __root { #(#return_arms),* }
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn fold_pair<#(#a_params_a),*, #(#b_params_b),*>(
                &self,
                __root: #root_name,
                #(#alg_params),*
            ) -> #result_name<#(#aps),*, #(#bps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().fold_pair(__root, #(#alg_args),*)
            }
        }
    }
}


fn gen_prefold(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let result_name = format_ident!("{}FoldResult", store);
    let aps: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__A{}", i)).collect();

    // pre: per-sort Node -> Node
    let pre_params: Vec<TokenStream2> = (0..n).map(|i| {
        let p = format_ident!("__pre{}", i);
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #p: impl Fn(#node) -> #node }
    }).collect();

    // alg: per-sort algebras, same shape as fold
    let alg_params: Vec<TokenStream2> = sorts.iter().enumerate().map(|(i, sort)| {
        let p = format_ident!("__alg{}", i);
        let a = &aps[i];
        let mapped = format_ident!("{}NodeMapped", sort_names[i]);
        let cs = child_sort_indices(sort);
        let params: Vec<&syn::Ident> = cs.iter().map(|&j| &aps[j]).collect();
        quote! { #p: impl Fn(#mapped<#(#params),*>) -> #a }
    }).collect();

    let pre_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__pre{}", i)).collect();
    let alg_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__alg{}", i)).collect();

    // Per-sort transform rules: call pre, push to new store
    let transform_rules: Vec<TokenStream2> = (0..n).map(|i| {
        let push_method = format_ident!("push_{}", sort_lowers[i]);
        let p = &pre_args[i];
        quote! { |__node, __new: &mut #store| __new.#push_method(#p(__node)) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn prefold<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#pre_params,)*
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                let (__new_store, __new_root) = self.rewrite(__root, #(#transform_rules),*);
                __new_store.with_strategy::<M>().fold(__new_root, #(#alg_args),*)
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn prefold<#(#aps: Clone),*>(
                &self,
                __root: #root_name,
                #(#pre_params,)*
                #(#alg_params),*
            ) -> #result_name<#(#aps),*> {
                self.with_strategy::<::semi_persistent_traversals::Dense>().prefold(__root, #(#pre_args,)* #(#alg_args),*)
            }
        }
    }
}


fn gen_postunfold(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let seed_name = format_ident!("{}Seed", store);
    let layer_name = format_ident!("{}Layer", store);
    let skel_name = format_ident!("__{}PostSkel", store);

    let skel_variants: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #sn(#node) }
    }).collect();

    let post_params: Vec<TokenStream2> = (0..n).map(|i| {
        let p = format_ident!("__post{}", i);
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #p: impl Fn(#node) -> #node }
    }).collect();

    let expand_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        quote! {
            #layer_name::#sn(__node, __child_seeds) => {
                let __nc = __child_seeds.len();
                __nodes.push((__nc, #skel_name::#sn(__node)));
                __work.push(__AnaTask::Build);
                for __cs in __child_seeds.into_iter().rev() {
                    __work.push(__AnaTask::Expand(__cs));
                }
            }
        }
    }).collect();

    let build_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let sn = sort_names[si];
        let push_method = format_ident!("push_{}", sort_lowers[si]);
        let node_name = format_ident!("{}Node", sort_names[si]);
        let post = format_ident!("__post{}", si);
        let remap_arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => #node_name::#vn };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let mapped: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let jsn = sort_names[*j];
                    quote! { match __child_results[__ci] { #root_name::#jsn(__id) => { __ci += 1; __id }, _ => panic!("sort mismatch") } }
                }
                FieldKind::VariadicChild(j) => {
                    let jsn = sort_names[*j];
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { {
                        let __vlen = #b.len();
                        let __v: ::smallvec::SmallVec<[#jid; 4]> = (0..__vlen).map(|_| {
                            match __child_results[__ci] { #root_name::#jsn(__id) => { __ci += 1; __id }, _ => panic!("sort mismatch") }
                        }).collect();
                        ::semi_persistent_traversals::Variadic::Resolved(__v)
                    }}
                }
                FieldKind::Data(_) => quote! { #b.clone() },
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => #node_name::#vn(#(#mapped),*) }
        }).collect();
        quote! {
            #skel_name::#sn(__skel) => {
                let mut __ci = 0usize;
                let __remapped = match __skel { #(#remap_arms),* };
                let __new_id = __store.#push_method(#post(__remapped));
                __results.push(#root_name::#sn(__new_id));
            }
        }
    }).collect();

    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments, unreachable_patterns)]
        impl #store {
            #vis fn postunfold<S>(
                &mut self,
                seed: #seed_name<S>,
                #(#post_params,)*
                coalg: impl Fn(#seed_name<S>) -> #layer_name<S>,
            ) -> #root_name {
                enum #skel_name { #(#skel_variants),* }
                enum __AnaTask<S> { Expand(S), Build }
                let __store = self;
                let mut __work: Vec<__AnaTask<#seed_name<S>>> = Vec::new();
                let mut __results: Vec<#root_name> = Vec::new();
                let mut __nodes: Vec<(usize, #skel_name)> = Vec::new();
                __work.push(__AnaTask::Expand(seed));
                while let Some(__task) = __work.pop() {
                    match __task {
                        __AnaTask::Expand(__s) => {
                            match coalg(__s) { #(#expand_arms)* }
                        }
                        __AnaTask::Build => {
                            let (__nc, __tagged) = __nodes.pop().unwrap();
                            let __start = __results.len() - __nc;
                            let __child_results: Vec<#root_name> = __results.drain(__start..).collect();
                            match __tagged { #(#build_arms)* }
                        }
                    }
                }
                __results.pop().unwrap()
            }
        }
    }
}


fn gen_rewrite_down(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);

    // One rule per sort
    let rule_params: Vec<TokenStream2> = (0..n).map(|i| {
        let p = format_ident!("__rule{}", i);
        let node = format_ident!("{}Node", sort_names[i]);
        quote! { #p: impl Fn(#node) -> #node }
    }).collect();
    let rule_args: Vec<syn::Ident> = (0..n).map(|i| format_ident!("__rule{}", i)).collect();

    let task_variants: Vec<TokenStream2> = (0..n).flat_map(|i| {
        let enter = format_ident!("Enter{}", sort_names[i]);
        let build = format_ident!("Build{}", sort_names[i]);
        let id = format_ident!("{}Id", sort_names[i]);
        vec![quote! { #enter(#id) }, quote! { #build(#id) }]
    }).collect();

    // Per-sort storage: M::Memo<Node> for rewritten, M::Mapping for old->new id, M::Visit for visited flag
    let rewritten_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let rw = format_ident!("__rw{}", i);
        let node = format_ident!("{}Node", sort_names[i]);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #rw: <M as ::semi_persistent_traversals::MemoStrategy>::Memo<#node> = <<M as ::semi_persistent_traversals::MemoStrategy>::Memo<#node> as ::semi_persistent_traversals::MemoOps<#node>>::new(self.store.#len_method()); }
    }).collect();
    let map_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let m = format_ident!("__map{}", i);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #m: <M as ::semi_persistent_traversals::MemoStrategy>::Mapping = <<M as ::semi_persistent_traversals::MemoStrategy>::Mapping as ::semi_persistent_traversals::MappingOps>::new(self.store.#len_method()); }
    }).collect();
    let visited_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let v = format_ident!("__vis{}", i);
        let len_method = format_ident!("len_{}", sort_lowers[i]);
        quote! { let mut #v: <M as ::semi_persistent_traversals::MemoStrategy>::Visit = <<M as ::semi_persistent_traversals::MemoStrategy>::Visit as ::semi_persistent_traversals::VisitOps>::new(self.store.#len_method()); }
    }).collect();
    let child_buf_decls: Vec<TokenStream2> = (0..n).map(|i| {
        let buf = format_ident!("__ch{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { let mut #buf = ::smallvec::SmallVec::<[#id; 8]>::new(); }
    }).collect();

    let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let enter = format_ident!("Enter{}", sort_names[si]);
        let build = format_ident!("Build{}", sort_names[si]);
        let rule = format_ident!("__rule{}", si);
        let rw = format_ident!("__rw{}", si);
        let vis_si = format_ident!("__vis{}", si);
        let get_method = format_ident!("get_{}", sort_lowers[si]);
        let cs = child_sort_indices(sort);
        let clear_bufs: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            quote! { #buf.clear(); }
        }).collect();
        let node_name = format_ident!("{}Node", sort_names[si]);
        let children_arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => {} };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let pushes: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).filter_map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let buf = format_ident!("__ch{}", j);
                    Some(quote! { #buf.push(*#b); })
                }
                FieldKind::VariadicChild(j) => {
                    let buf = format_ident!("__ch{}", j);
                    Some(quote! { for __c in #b.iter() { #buf.push(*__c); } })
                }
                FieldKind::Data(_) => None,
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => { #(#pushes)* } }
        }).collect();
        let push_children: Vec<TokenStream2> = cs.iter().map(|&j| {
            let buf = format_ident!("__ch{}", j);
            let enter_child = format_ident!("Enter{}", sort_names[j]);
            let vis_j = format_ident!("__vis{}", j);
            quote! {
                for &__c in #buf.iter().rev() {
                    if !::semi_persistent_traversals::VisitOps::visited(&#vis_j, __c.0) {
                        __stack.push(__Task::#enter_child(__c));
                    }
                }
            }
        }).collect();
        quote! {
            __Task::#enter(__id) => {
                if ::semi_persistent_traversals::VisitOps::visited(&#vis_si, __id.0) { continue; }
                ::semi_persistent_traversals::VisitOps::mark(&mut #vis_si, __id.0);
                let __rewritten = #rule(self.store.#get_method(__id).clone());
                #(#clear_bufs)*
                match &__rewritten { #(#children_arms)* }
                ::semi_persistent_traversals::MemoOps::set(&mut #rw, __id.0, __rewritten);
                __stack.push(__Task::#build(__id));
                #(#push_children)*
            }
        }
    }).collect();

    let build_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let build = format_ident!("Build{}", sort_names[si]);
        let rw = format_ident!("__rw{}", si);
        let map_si = format_ident!("__map{}", si);
        let push_method = format_ident!("push_{}", sort_lowers[si]);
        let node_name = format_ident!("{}Node", sort_names[si]);
        let remap_arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => #node_name::#vn };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let mapped: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let m = format_ident!("__map{}", j);
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { #jid(::semi_persistent_traversals::MappingOps::get(&#m, #b.0)) }
                }
                FieldKind::VariadicChild(j) => {
                    let m = format_ident!("__map{}", j);
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| #jid(::semi_persistent_traversals::MappingOps::get(&#m, __c.0))).collect()) }
                }
                FieldKind::Data(_) => quote! { #b.clone() },
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => #node_name::#vn(#(#mapped),*) }
        }).collect();
        quote! {
            __Task::#build(__id) => {
                let __node = ::semi_persistent_traversals::MemoOps::take(&mut #rw, __id.0).unwrap();
                let __remapped = match __node { #(#remap_arms),* };
                let __new_id = __new.#push_method(__remapped);
                ::semi_persistent_traversals::MappingOps::set(&mut #map_si, __id.0, __new_id.0);
            }
        }
    }).collect();

    let init_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let enter = format_ident!("Enter{}", sort_names[i]);
        quote! { #root_name::#sn(__id) => __stack.push(__Task::#enter(__id)) }
    }).collect();
    let return_arms: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let m = format_ident!("__map{}", i);
        let id = format_ident!("{}Id", sort_names[i]);
        quote! { #root_name::#sn(__id) => #root_name::#sn(#id(::semi_persistent_traversals::MappingOps::get(&#m, __id.0))) }
    }).collect();

    let view_name = format_ident!("{}View", store);
    quote! {
        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl<'a, M: ::semi_persistent_traversals::MemoStrategy> #view_name<'a, M> {
            #vis fn rewrite_down(
                &self,
                __root: #root_name,
                #(#rule_params),*
            ) -> (#store, #root_name) {
                enum __Task { #(#task_variants),* }
                let mut __new = #store::new();
                #(#rewritten_decls)*
                #(#map_decls)*
                #(#visited_decls)*
                #(#child_buf_decls)*
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#build_arms)*
                    }
                }
                let __new_root = match __root { #(#return_arms),* };
                (__new, __new_root)
            }
        }

        #[allow(non_snake_case, clippy::too_many_arguments)]
        impl #store {
            #vis fn rewrite_down(
                &self,
                __root: #root_name,
                #(#rule_params),*
            ) -> (#store, #root_name) {
                self.with_strategy::<::semi_persistent_traversals::Dense>().rewrite_down(__root, #(#rule_args),*)
            }
        }
    }
}


fn gen_zipper(
    vis: &syn::Visibility,
    store: &syn::Ident,
    sorts: &[ResolvedSort],
    sort_names: &[&syn::Ident],
    sort_lowers: &[syn::Ident],
    n: usize,
) -> TokenStream2 {
    let root_name = format_ident!("{}Root", store);
    let zipper_name = format_ident!("{}Zipper", store);
    let zipper_mut_name = format_ident!("{}ZipperMut", store);
    let zipper_cow_name = format_ident!("{}ZipperCow", store);

    // children_arms: given a node (borrowed), produce a Vec<Root> of its children in order.
    // One match block per sort.
    let children_root_impls: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let node_name = format_ident!("{}Node", sort_names[si]);
        let fn_name = format_ident!("__zipper_children_{}", sort_lowers[si]);
        let arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => {} };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let pushes: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).filter_map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let jsn = sort_names[*j];
                    Some(quote! { __out.push(#root_name::#jsn(*#b)); })
                }
                FieldKind::VariadicChild(j) => {
                    let jsn = sort_names[*j];
                    Some(quote! { for __c in #b.iter() { __out.push(#root_name::#jsn(*__c)); } })
                }
                FieldKind::Data(_) => None,
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => { #(#pushes)* } }
        }).collect();
        quote! {
            #[allow(non_snake_case)]
            fn #fn_name(node: &#node_name, __out: &mut Vec<#root_name>) {
                match node { #(#arms),* }
            }
        }
    }).collect();

    // Dispatcher: take a Root and get its node's children as a Vec<Root>
    let dispatch_children: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let get_method = format_ident!("get_{}", sort_lowers[i]);
        let fn_name = format_ident!("__zipper_children_{}", sort_lowers[i]);
        quote! { #root_name::#sn(__id) => { let mut __out = Vec::new(); #fn_name(__store.#get_method(__id), &mut __out); __out } }
    }).collect();

    // set_focus: take a sort-tagged node enum. We define set_focus_<sort> methods.
    let set_focus_methods: Vec<TokenStream2> = (0..n).map(|i| {
        let sn = sort_names[i];
        let node_name = format_ident!("{}Node", sort_names[i]);
        let fn_name = format_ident!("set_focus_{}", sort_lowers[i]);
        let set_method = format_ident!("set_{}", sort_lowers[i]);
        quote! {
            #vis fn #fn_name(&mut self, node: #node_name) -> bool {
                if let #root_name::#sn(__id) = self.focus {
                    self.store.#set_method(__id, node);
                    true
                } else {
                    false
                }
            }
        }
    }).collect();

    // Per-sort remap helper: given a node and per-sort mappings from old id -> new id,
    // produce a new node with all child ids remapped via the mappings.
    let remap_node_impls: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
        let node_name = format_ident!("{}Node", sort_names[si]);
        let fn_name = format_ident!("__remap_{}", sort_lowers[si]);
        let map_type_params: Vec<syn::Ident> = (0..n).map(|j| format_ident!("__MP{}", j)).collect();
        let map_params: Vec<TokenStream2> = (0..n).map(|j| {
            let p = format_ident!("__map{}", j);
            let tp = &map_type_params[j];
            quote! { #p: &#tp }
        }).collect();
        let map_type_bounds: Vec<TokenStream2> = map_type_params.iter().map(|tp| {
            quote! { #tp: ::semi_persistent_traversals::MappingOps }
        }).collect();
        let arms: Vec<TokenStream2> = sort.variants.iter().map(|v| {
            let vn = &v.name;
            if v.fields.is_empty() {
                return quote! { #node_name::#vn => #node_name::#vn };
            }
            let bs: Vec<syn::Ident> = (0..v.fields.len()).map(|i| format_ident!("__x{}", i)).collect();
            let mapped: Vec<TokenStream2> = bs.iter().zip(v.fields.iter()).map(|(b, fk)| match fk {
                FieldKind::Child(j) => {
                    let m = format_ident!("__map{}", j);
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { #jid(::semi_persistent_traversals::MappingOps::get(#m, #b.0)) }
                }
                FieldKind::VariadicChild(j) => {
                    let m = format_ident!("__map{}", j);
                    let jid = format_ident!("{}Id", sort_names[*j]);
                    quote! { ::semi_persistent_traversals::Variadic::Resolved(#b.iter().map(|__c| #jid(::semi_persistent_traversals::MappingOps::get(#m, __c.0))).collect()) }
                }
                FieldKind::Data(_) => quote! { #b.clone() },
            }).collect();
            quote! { #node_name::#vn(#(#bs),*) => #node_name::#vn(#(#mapped),*) }
        }).collect();
        quote! {
            #[allow(non_snake_case, clippy::too_many_arguments)]
            fn #fn_name<#(#map_type_bounds),*>(node: &#node_name, #(#map_params),*) -> #node_name {
                match node { #(#arms),* }
            }
        }
    }).collect();

    // COW set_focus: traverse reachable tree from root, remap every node into a fresh store,
    // substituting the focused node with the provided replacement.
    // O(reachable_tree_size) — matches single-arena ZipperCow semantics.
    // substituting the focused node with the provided replacement.
    // O(reachable_tree_size) — matches single-arena ZipperCow semantics.
    let cow_set_focus_methods: Vec<TokenStream2> = (0..n).map(|fi| {
        let sn = sort_names[fi];
        let node_name = format_ident!("{}Node", sort_names[fi]);
        let fn_name = format_ident!("set_focus_{}", sort_lowers[fi]);

        // Per-sort enter/eval task handling
        let task_variants: Vec<TokenStream2> = (0..n).flat_map(|j| {
            let enter = format_ident!("Enter{}", sort_names[j]);
            let eval = format_ident!("Eval{}", sort_names[j]);
            let id = format_ident!("{}Id", sort_names[j]);
            vec![quote! { #enter(#id) }, quote! { #eval(#id) }]
        }).collect();

        let map_decls: Vec<TokenStream2> = (0..n).map(|j| {
            let m = format_ident!("__map{}", j);
            let len_method = format_ident!("len_{}", sort_lowers[j]);
            quote! { let mut #m: <M as ::semi_persistent_traversals::MemoStrategy>::Mapping = <<M as ::semi_persistent_traversals::MemoStrategy>::Mapping as ::semi_persistent_traversals::MappingOps>::new(self.src.#len_method()); }
        }).collect();
        let visited_decls: Vec<TokenStream2> = (0..n).map(|j| {
            let v = format_ident!("__vis{}", j);
            let len_method = format_ident!("len_{}", sort_lowers[j]);
            quote! { let mut #v: <M as ::semi_persistent_traversals::MemoStrategy>::Visit = <<M as ::semi_persistent_traversals::MemoStrategy>::Visit as ::semi_persistent_traversals::VisitOps>::new(self.src.#len_method()); }
        }).collect();

        // Enter arms: mark visited, push eval, recurse into children.
        // For the focused node (sort fi, id == focus_id), use the NEW node's children instead.
        let enter_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, sort)| {
            let sn_s = sort_names[si];
            let enter = format_ident!("Enter{}", sort_names[si]);
            let eval = format_ident!("Eval{}", sort_names[si]);
            let vis_s = format_ident!("__vis{}", si);
            let get_method = format_ident!("get_{}", sort_lowers[si]);
            let fn_children = format_ident!("__zipper_children_{}", sort_lowers[si]);
            let is_focused_sort = si == fi;
            // Push children from either __new_node (if focused) or src node
            let focused_case = if is_focused_sort {
                quote! {
                    if __id.0 == __focus_id.0 {
                        #fn_children(&__new_node, &mut __ch_tmp);
                    } else {
                        #fn_children(self.src.#get_method(__id), &mut __ch_tmp);
                    }
                }
            } else {
                quote! {
                    #fn_children(self.src.#get_method(__id), &mut __ch_tmp);
                }
            };
            let push_children_arms: Vec<TokenStream2> = (0..n).map(|j| {
                let sn_j = sort_names[j];
                let enter_j = format_ident!("Enter{}", sort_names[j]);
                let vis_j = format_ident!("__vis{}", j);
                quote! { #root_name::#sn_j(__cid) => { if !::semi_persistent_traversals::VisitOps::visited(&#vis_j, __cid.0) { __stack.push(__Task::#enter_j(*__cid)); } } }
            }).collect();
            quote! {
                __Task::#enter(__id) => {
                    if ::semi_persistent_traversals::VisitOps::visited(&#vis_s, __id.0) { continue; }
                    ::semi_persistent_traversals::VisitOps::mark(&mut #vis_s, __id.0);
                    __stack.push(__Task::#eval(__id));
                    __ch_tmp.clear();
                    #focused_case
                    for __cr in __ch_tmp.iter().rev() {
                        match __cr { #(#push_children_arms),* }
                    }
                }
            }
        }).collect();

        // Eval arms: remap node's children via per-sort mappings, push into new store.
        let eval_arms: Vec<TokenStream2> = sorts.iter().enumerate().map(|(si, _)| {
            let eval = format_ident!("Eval{}", sort_names[si]);
            let get_method = format_ident!("get_{}", sort_lowers[si]);
            let push_method = format_ident!("push_{}", sort_lowers[si]);
            let map_s = format_ident!("__map{}", si);
            let remap_fn = format_ident!("__remap_{}", sort_lowers[si]);
            let map_refs: Vec<TokenStream2> = (0..n).map(|j| {
                let m = format_ident!("__map{}", j);
                quote! { &#m }
            }).collect();
            let is_focused_sort = si == fi;
            let body = if is_focused_sort {
                quote! {
                    let __node_ref = if __id.0 == __focus_id.0 { &__new_node } else { self.src.#get_method(__id) };
                    let __remapped = #remap_fn(__node_ref, #(#map_refs),*);
                }
            } else {
                quote! {
                    let __remapped = #remap_fn(self.src.#get_method(__id), #(#map_refs),*);
                }
            };
            quote! {
                __Task::#eval(__id) => {
                    #body
                    let __new_id = __new.#push_method(__remapped);
                    ::semi_persistent_traversals::MappingOps::set(&mut #map_s, __id.0, __new_id.0);
                }
            }
        }).collect();

        let init_arms: Vec<TokenStream2> = (0..n).map(|j| {
            let sn_j = sort_names[j];
            let enter_j = format_ident!("Enter{}", sort_names[j]);
            quote! { #root_name::#sn_j(__id) => __stack.push(__Task::#enter_j(__id)) }
        }).collect();

        let return_arms: Vec<TokenStream2> = (0..n).map(|j| {
            let sn_j = sort_names[j];
            let m = format_ident!("__map{}", j);
            let id = format_ident!("{}Id", sort_names[j]);
            quote! { #root_name::#sn_j(__id) => { let __v: #id = #id(::semi_persistent_traversals::MappingOps::get(&#m, __id.0)); #root_name::#sn_j(__v) } }
        }).collect();

        let fn_name_with_strategy = format_ident!("set_focus_{}_with_strategy", sort_lowers[fi]);
        quote! {
            #vis fn #fn_name(self, node: #node_name) -> (#store, #root_name) {
                self.#fn_name_with_strategy::<::semi_persistent_traversals::Dense>(node)
            }
            #vis fn #fn_name_with_strategy<M: ::semi_persistent_traversals::MemoStrategy>(self, node: #node_name) -> (#store, #root_name) {
                let __new_node: #node_name = node;
                let __focus_id = match self.focus {
                    #root_name::#sn(__id) => __id,
                    _ => panic!("set_focus sort does not match focus sort"),
                };
                let __root: #root_name = if self.crumbs.is_empty() { self.focus } else { self.crumbs[0].0 };
                let mut __new = #store::new();
                enum __Task { #(#task_variants),* }
                #(#map_decls)*
                #(#visited_decls)*
                let mut __ch_tmp: Vec<#root_name> = Vec::new();
                let mut __stack: Vec<__Task> = Vec::new();
                match __root { #(#init_arms),* }
                while let Some(__task) = __stack.pop() {
                    match __task {
                        #(#enter_arms)*
                        #(#eval_arms)*
                    }
                }
                let __new_root = match __root { #(#return_arms),* };
                (__new, __new_root)
            }
        }
    }).collect();

    // Need a store method set_<sort>(id, node)
    let set_store_methods: Vec<TokenStream2> = (0..n).map(|i| {
        let node_name = format_ident!("{}Node", sort_names[i]);
        let id_name = format_ident!("{}Id", sort_names[i]);
        let set_method = format_ident!("set_{}", sort_lowers[i]);
        let field_name = format_ident!("{}_nodes", sort_lowers[i]);
        quote! {
            #vis fn #set_method(&mut self, id: #id_name, node: #node_name) {
                self.#field_name[id.0] = node;
            }
        }
    }).collect();

    quote! {
        #(#children_root_impls)*
        #(#remap_node_impls)*

        impl #store {
            #(#set_store_methods)*
        }

        #vis struct #zipper_name<'a> {
            store: &'a #store,
            focus: #root_name,
            crumbs: Vec<(#root_name, usize)>,
        }

        impl<'a> #zipper_name<'a> {
            #vis fn new(store: &'a #store, root: #root_name) -> Self {
                Self { store, focus: root, crumbs: Vec::new() }
            }
            #vis fn focus(&self) -> #root_name { self.focus }
            #vis fn focus_id(&self) -> #root_name { self.focus }
            #vis fn depth(&self) -> usize { self.crumbs.len() }
            #vis fn child_count(&self) -> usize {
                let __store = self.store;
                let __kids = match self.focus { #(#dispatch_children),* };
                __kids.len()
            }
            #vis fn down(&mut self, child_index: usize) -> bool {
                let __store = self.store;
                let __kids = match self.focus { #(#dispatch_children),* };
                if child_index >= __kids.len() { return false; }
                self.crumbs.push((self.focus, child_index));
                self.focus = __kids[child_index];
                true
            }
            #vis fn up(&mut self) -> bool {
                match self.crumbs.pop() {
                    Some((__parent, _)) => { self.focus = __parent; true }
                    None => false,
                }
            }
            #vis fn sibling(&mut self, child_index: usize) -> bool {
                if !self.up() { return false; }
                self.down(child_index)
            }
            #vis fn top(&mut self) {
                if !self.crumbs.is_empty() {
                    self.focus = self.crumbs[0].0;
                    self.crumbs.clear();
                }
            }
        }

        #vis struct #zipper_mut_name<'a> {
            store: &'a mut #store,
            focus: #root_name,
            crumbs: Vec<(#root_name, usize)>,
        }

        impl<'a> #zipper_mut_name<'a> {
            #vis fn new(store: &'a mut #store, root: #root_name) -> Self {
                Self { store, focus: root, crumbs: Vec::new() }
            }
            #vis fn focus(&self) -> #root_name { self.focus }
            #vis fn focus_id(&self) -> #root_name { self.focus }
            #vis fn depth(&self) -> usize { self.crumbs.len() }
            #vis fn child_count(&self) -> usize {
                let __store: &#store = self.store;
                let __kids = match self.focus { #(#dispatch_children),* };
                __kids.len()
            }
            #vis fn down(&mut self, child_index: usize) -> bool {
                let __store: &#store = self.store;
                let __kids = match self.focus { #(#dispatch_children),* };
                if child_index >= __kids.len() { return false; }
                self.crumbs.push((self.focus, child_index));
                self.focus = __kids[child_index];
                true
            }
            #vis fn up(&mut self) -> bool {
                match self.crumbs.pop() {
                    Some((__parent, _)) => { self.focus = __parent; true }
                    None => false,
                }
            }
            #(#set_focus_methods)*
        }

        #vis struct #zipper_cow_name<'a> {
            src: &'a #store,
            focus: #root_name,
            crumbs: Vec<(#root_name, usize)>,
        }

        impl<'a> #zipper_cow_name<'a> {
            #vis fn new(src: &'a #store, root: #root_name) -> Self {
                Self { src, focus: root, crumbs: Vec::new() }
            }
            #vis fn focus(&self) -> #root_name { self.focus }
            #vis fn depth(&self) -> usize { self.crumbs.len() }
            #vis fn down(&mut self, child_index: usize) -> bool {
                let __store: &#store = self.src;
                let __kids = match self.focus { #(#dispatch_children),* };
                if child_index >= __kids.len() { return false; }
                self.crumbs.push((self.focus, child_index));
                self.focus = __kids[child_index];
                true
            }
            #vis fn up(&mut self) -> bool {
                match self.crumbs.pop() {
                    Some((__parent, _)) => { self.focus = __parent; true }
                    None => false,
                }
            }
            #(#cow_set_focus_methods)*
        }
    }
}


fn gen_view(
    vis: &syn::Visibility,
    store: &syn::Ident,
) -> TokenStream2 {
    let view_name = format_ident!("{}View", store);
    quote! {
        #vis struct #view_name<'a, M: ::semi_persistent_traversals::MemoStrategy> {
            store: &'a #store,
            _m: ::core::marker::PhantomData<M>,
        }

        impl #store {
            #vis fn with_strategy<M: ::semi_persistent_traversals::MemoStrategy>(&self) -> #view_name<'_, M> {
                #view_name { store: self, _m: ::core::marker::PhantomData }
            }
        }
    }
}
