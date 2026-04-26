// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::format_ident;
use quote::quote;
use syn::{Type, parse_macro_input};

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


// ===========================================================================
// rec_family! — partitioned per-type arenas
// ===========================================================================

#[proc_macro]
pub fn rec_family(input: TokenStream) -> TokenStream {
    let raw = parse_macro_input!(input as FamilyDef);
    match gen_family(&raw) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

struct FamilyDef {
    vis: syn::Visibility,
    fam_name: syn::Ident,
    store_name: syn::Ident,
    sorts: Vec<RawSortDef>,
}

impl syn::parse::Parse for FamilyDef {
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
        Ok(FamilyDef { vis, fam_name, store_name, sorts })
    }
}

// ---------------------------------------------------------------------------
// rec_family! code generation
// ---------------------------------------------------------------------------

fn resolve_family_fields(sorts: &[RawSortDef]) -> Vec<ResolvedSort> {
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

fn gen_family(def: &FamilyDef) -> syn::Result<TokenStream2> {
    let sorts = resolve_family_fields(&def.sorts);
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
// rec_family! generators
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
