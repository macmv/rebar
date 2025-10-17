use quote::quote;

#[proc_macro_derive(FromAnalysis, attributes(invalidates, phase))]
pub fn from_analysis(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
  let ast: syn::DeriveInput = syn::parse(item).unwrap();
  let invalidates_arg = ast.attrs.iter().find(|a| a.path().is_ident("invalidates"));
  let phase_arg = ast.attrs.iter().find(|a| a.path().is_ident("phase"));
  let fields = match ast.data {
    syn::Data::Struct(s) => s,
    _ => panic!("#[derive(FromAnalysis)] can only be used on enums"),
  };

  let requires = fields.fields.iter().map(|f| {
    let ty = match &f.ty {
      syn::Type::Reference(r) => &*r.elem,
      _ => panic!("#[derive(FromAnalysis)] fields must be references"),
    };
    quote!(#ty::ID)
  });

  let invalidates = match invalidates_arg {
    Some(arg) => {
      let args: syn::ExprArray = arg.parse_args().unwrap();

      args
        .elems
        .into_iter()
        .map(|expr| match expr {
          syn::Expr::Path(p) => {
            let ident = &p.path.segments.last().unwrap().ident;
            quote!(#ident::ID)
          }
          _ => panic!("#[invalidates(...)] only accepts identifiers"),
        })
        .collect::<Vec<_>>()
    }
    None => requires.clone().collect::<Vec<_>>(),
  };

  let phase = match phase_arg {
    Some(arg) => {
      let args: syn::Ident = arg.parse_args().unwrap();
      quote!(Phase::#args)
    }
    None => quote!(Phase::Normal),
  };

  let fields = fields.fields.iter().map(|f| {
    let name = &f.ident;
    quote!(#name: analysis.get())
  });

  let lifetime = ast.generics.lifetimes().next();
  let lifetime_param = ast.generics.lifetimes().next().map(|l| quote!(<#l>));
  let lifetime_arg = ast.generics.lifetimes().next().map(|l| quote!(<#l>)).unwrap_or(quote!(<'_>));

  let name = &ast.ident;
  let g = quote! {
    impl #lifetime_param FromAnalysis #lifetime_arg for #name #lifetime_param {
      fn requires() -> &'static [AnalysisPassId] { &[#( #requires ),*] }
      fn invalidates() -> &'static [AnalysisPassId] { &[#( #invalidates ),*] }
      fn phase() -> Phase { #phase }

      fn from_analysis(analysis: & #lifetime Analysis) -> Self {
        Self { #( #fields ),* }
      }
    }
  };
  g.into()
}
