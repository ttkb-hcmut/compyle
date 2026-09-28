open Ppxlib
open Ppxlib_ast.Parsetree
open Ppxlib_ast.Asttypes
open Ppxlib_ast.Ast_helper

module E =
  struct

  class traverse_splits =
    object (self)
    method eval (_ : expression) : [ `str of structure_item | `skip | `ignore_and_save_str of structure_item | `str_and_save_str of structure_item * structure_item | `str_and_save_strs of structure_item * structure ] = `skip
    end

  let split ast_exp k =
    let loc = !default_loc in
    let saves = ref [] in
    let rec split ast_exp k =
      match ast_exp.pexp_desc with
      | Pexp_let (recurse, bindings, body) ->
        let () = match recurse with Nonrecursive -> () | Recursive -> failwith "JAN" in
        let rhs = match bindings with [x] -> x | _ -> failwith "DAS" in
        Str.value Nonrecursive [rhs] :: split body k
      | Pexp_sequence ({ pexp_desc = Pexp_let _ }, _) -> failwith "KMA"
      | Pexp_sequence (a, b) ->
        (
          match k#eval a with
          | `str new_str -> new_str :: split b k
          | `str_and_save_str (str, new_str) -> saves := new_str :: !saves; str :: split b k
          | `str_and_save_strs(str, new_strs)-> saves := (List.rev new_strs) @ !saves; str :: split b k
          | `ignore_and_save_str new_str -> saves := new_str :: !saves; split b k
          | `skip ->
              Str.value Nonrecursive [ Vb.mk (Pat.construct { txt = Longident.Lident "()"; loc } None) a ]
              (* Str.eval a *)
              :: split b k
        )
      | Pexp_construct ({ txt = Longident.Lident "()" }, None) -> []
      | _ -> failwith "KAM"
    in
    let strs = split ast_exp k in
    let saves = List.rev !saves in
    [ [%stri [@@@module' {%unfold|~/u/topcore/dyn|}]]
    ; Str.open_ { popen_loc = loc; popen_attributes = []; popen_override = Fresh; popen_expr = Mod.structure strs } ]
    @ saves

  end

let make_export =
  let loc = !default_loc in
  object inherit E.traverse_splits as base
  method eval e =
    match e.pexp_desc with
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Longident.Ldot (Lident "Stdlib", "ignore") } }, [Nolabel, { pexp_desc = Pexp_tuple [{ pexp_desc = Pexp_variant ("export", None) }; { pexp_desc = Pexp_constant ( Pconst_string (exportname, _, _) ) }; exportvar ] }]) ->
      let new_str = Str.value Nonrecursive [ Vb.mk ~attrs:[Attr.mk { loc; txt = "public" } (PStr [])] (Pat.var { txt = exportname; loc }) exportvar ] in
      `ignore_and_save_str new_str
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Longident.Ldot (Lident "Stdlib", "ignore") } }, [Nolabel, { pexp_desc = Pexp_tuple [{ pexp_desc = Pexp_variant ("export_opaque_value", None) }; ({ pexp_desc = Pexp_constant ( Pconst_string (exportname, _, _) ) } | { pexp_desc = Pexp_apply (_, [Nolabel, { pexp_desc = Pexp_constant ( Pconst_string (exportname, _, _) ) }]) }); _ ] }]) ->
      let new_str = Str.value Nonrecursive [ Vb.mk ~attrs:[Attr.mk { loc; txt = "public" } (PStr [])] (Pat.var { txt = exportname; loc }) [%expr (Obj.magic () : Dyn.val_)] ] in
      `ignore_and_save_str new_str
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Longident.Ldot (Lident "Stdlib", "ignore") } }, [Nolabel, { pexp_desc = Pexp_tuple [{ pexp_desc = Pexp_variant ("export_opaque_value_n", None) }; ({ pexp_desc = Pexp_constant ( Pconst_string (exportname, _, _) ) } | { pexp_desc = Pexp_apply (_, [Nolabel, { pexp_desc = Pexp_constant ( Pconst_string (exportname, _, _) ) }]) }) ] }]) ->
      let new_str = Str.value Nonrecursive [ Vb.mk ~attrs:[Attr.mk { loc; txt = "public" } (PStr [])] (Pat.var { txt = exportname; loc }) [%expr (Obj.magic () : (Dyn.vararg -> Dyn.any) Dyn.val_n)] ] in
      `ignore_and_save_str new_str
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Longident.Ldot (Lident "Stdlib", "ignore") } }, [Nolabel, { pexp_desc = Pexp_tuple [{ pexp_desc = Pexp_variant ("export_opaque_module", None) }; ({ pexp_desc = Pexp_constant ( Pconst_string (exportname, _, _) ) } | { pexp_desc = Pexp_apply (_, [Nolabel, { pexp_desc = Pexp_constant ( Pconst_string (exportname, _, _) ) }]) }) ] }]) ->
      let new_str = Str.value Nonrecursive [ Vb.mk ~attrs:[Attr.mk { loc; txt = "public" } (PStr [])] (Pat.var { txt = exportname; loc }) [%expr (Obj.magic () : Dyn.module_)] ] in
      `ignore_and_save_str new_str
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Longident.Ldot (Lident "Stdlib", "ignore") } }, [Nolabel, { pexp_desc = Pexp_tuple [{ pexp_desc = Pexp_variant ("insert_module", None) };
        ({ pexp_desc = Pexp_constant ( Pconst_string (pmname, _, _) ) });
        ({ pexp_desc = Pexp_constant ( Pconst_string (modname, _, _) ) });
        ({ pexp_desc = Pexp_constant ( Pconst_string (reprcontent, _, _) ) })
      ] }]) ->
      let str = Str.eval @@ Exp.constant @@ Const.string ("<<<"^reprcontent^">>>") in
      let new_strs =
        [
          Str.module_ @@ Mb.mk { loc; txt = Some modname } @@ Mod.ident { loc; txt = Longident.Lident modname };
          (* Str.modtype @@ Mtd.mk ~typ:(Mty.typeof_ @@ Mod.ident { loc; txt = Longident.Lident modname }) { loc; txt = modname }; *)
          (* Str.value Nonrecursive [ Vb.mk ~attrs:[Attr.mk { loc; txt = "public" } (PStr [])] (Pat.var { loc; txt = pmname }) (Exp.constraint_ (Exp.pack @@ Mod.ident { loc; txt = Longident.Lident modname }) (Typ.package { loc; txt = Longident.Lident modname } [])) ]; *)
          Str.type_ Nonrecursive [ Type.mk ~manifest:(Typ.constr { loc; txt = Longident.Ldot (Lident modname, "t") } []) ~kind:Ptype_abstract { loc; txt = pmname } ]
        ]
      in
      `str_and_save_strs (str, new_strs)
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Longident.Ldot (Lident "Stdlib", "ignore") } }, [Nolabel, { pexp_desc = Pexp_tuple [{ pexp_desc = Pexp_variant ("insert_type", None) };
        ({ pexp_desc = Pexp_constant ( Pconst_string (typename, _, _) ) } | { pexp_desc = Pexp_apply (_, [Nolabel, { pexp_desc = Pexp_constant ( Pconst_string (typename, _, _) ) }]) });
        ({ pexp_desc = Pexp_constant ( Pconst_string (reprcontent, _, _) ) } | { pexp_desc = Pexp_apply (_, [Nolabel, { pexp_desc = Pexp_constant ( Pconst_string (reprcontent, _, _) ) }]) })
      ] }]) ->
      let str = Str.eval @@ Exp.constant @@ Const.string ("<<<"^reprcontent^">>>") in
      let new_str = Str.type_ Nonrecursive [ Type.mk ~kind:Ptype_abstract ~manifest:(Typ.constr { loc; txt = Longident.Lident typename } []) { loc; txt = typename }  ] in
      `str_and_save_str (str, new_str)
    | _ -> base#eval e
  end

let of_code c = Ppxlib.Selected_ast.Of_ocaml.copy_expression @@ Codelib.ast_of_code @@ Codelib.close_code ~csp:Codelib.CSP_error @@ c
