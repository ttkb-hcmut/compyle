[@@@module "%/../prgpy-interp.ml" [@prefixed? "prg"]]
[@@@module {%unfold|~/u/topcore/yield|}]
type _ Effect.t += Dynlinker : (Ppxlib.Longident.t * Ppxlib.Longident.t) Effect.t

let get_dynlinker () = Effect.perform Dynlinker

let with_dynlink (er: Ppxlib.Longident.t) (er2: Ppxlib.Longident.t) f =
  match f () with v -> v
  | effect Dynlinker, k -> Effect.Deep.continue k (er, er2)

type f_loo = F_loo : 't Type.Id.t * 'retval Type.Id.t * (('t Trx.code -> 'retval Trx.code) -> ('t -> 'retval) Trx.code) -> f_loo

let plug_fundef_2 : f_loo Lazy.t ref = ref @@ lazy (failwith "plug fundef 2 uninitialized")

let save_plug_fundef_2 : type t retval. t Type.Id.t -> retval Type.Id.t -> ((t Trx.code -> retval Trx.code) -> (t -> retval) Trx.code) -> unit = fun get_type' ret_type' mk ->
  plug_fundef_2 := lazy (F_loo (get_type', ret_type', mk))

let unlock_plug_fundef_2 : type t retval. t Type.Id.t -> retval Type.Id.t -> ((t Trx.code -> retval Trx.code) -> (t -> retval) Trx.code) = fun get_type ret_type ->
  let F_loo (get_type', ret_type', mk) = Lazy.force !plug_fundef_2 in
  match Type.Id.provably_equal get_type get_type' with None -> failwith "mquzt" | Some Type.Equal ->
  match Type.Id.provably_equal ret_type ret_type' with None -> failwith "mqyau" | Some Type.Equal ->
  mk

let eval stri =
  assert begin Toploop.execute_phrase false Format.err_formatter @@ Ppxlib.Selected_ast.To_ocaml.copy_toplevel_phrase @@ Ppxlib_ast.Parsetree.Ptop_def [ stri ] end

open Ppxlib
open Ppxlib_ast.Parsetree
open Ppxlib_ast.Asttypes
open Ppxlib_ast.Ast_helper

let func ~name get_craft_repr get_type ret_craft_repr ret_type =
  let py_interp, prgpy = get_dynlinker () in
  let loc = !default_loc in
  let func = 
      Exp.apply (Exp.ident { loc; txt = Longident.Ldot (prgpy, "save_plug_fundef_2") })
      [
        Nolabel, get_craft_repr py_interp (* Exp.ident { loc; txt = Longident.Ldot (Ldot (py_interp, Py_interp.extract_modname get_repr), "typeid") } *);
        Nolabel, ret_craft_repr py_interp (* Exp.ident { loc; txt = Longident.Ldot (Ldot (py_interp, Py_interp.extract_modname ret_repr), "typeid") } *);
        Nolabel,
        Exp.fun_ Nolabel None (Pat.var { loc; txt = "k" }) @@
        Exp.extension ({ loc; txt = "metaocaml.bracket" }, (PStr [ Str.eval @@
          Exp.fun_ Nolabel None (Pat.var { loc; txt = name }) @@
          Exp.extension ({ loc; txt = "metaocaml.escape" }, (PStr [ Str.eval @@
            Exp.apply (Exp.ident { loc; txt = Longident.Ldot (py_interp, "with_my_locus") })
            [ Nolabel,
              Exp.fun_ Nolabel None (Pat.construct { loc; txt = Longident.Lident "()" } None) @@
              Exp.apply (Exp.ident { loc; txt = Longident.Lident "k" })
              [ Nolabel,
                Exp.extension ({ loc; txt = "metaocaml.bracket" }, (PStr [ Str.eval @@
                  Exp.ident { loc; txt = Longident.Lident name }
                ]))
              ]
            ]
          ]))
        ]))
      ]
  in
  eval @@ Str.eval @@ func;
  unlock_plug_fundef_2 get_type ret_type

let moduleclass ~name (decls : (string * string) list) =
  let name_star = String.capitalize_ascii name in
  let loc = !default_loc in
  let sig_s = Str.modtype @@ Mtd.mk ~typ:(Mty.signature @@ List.map (function name, typename -> Sig.value @@ Val.mk { loc; txt = name } @@ Typ.constr { loc; txt = Longident.Lident typename } []) decls) { loc; txt = "S" } in
  let type_t = Str.type_ Nonrecursive [ Type.mk ~manifest:(Typ.package { loc; txt = Longident.Lident "S" } []) ~kind:Ptype_abstract { loc; txt = "t" } ] in
  (* let type_t = Str.type_ Nonrecursive [ Type.mk ~kind:(Ptype_record (List.map (function name, typename -> Type.field ~mut:Mutable { loc; txt = name } @@ Typ.constr { loc; txt = Longident.Lident typename } []) decls)) { loc; txt = "t" } ] in *)
  let maker = match decls with [] -> Option.some @@ Str.module_ @@ Mb.mk { loc; txt = Some "Make" } @@ Mod.functor_ Unit @@ Mod.structure [] | _ -> None in
  let mod_ = Str.module_ @@ Mb.mk { loc; txt = Some name_star } @@ Mod.structure ((sig_s :: type_t :: []) @ (match maker with Some x -> [x] | None -> [])) in
  let reprcontent = Yield.structure (mod_ :: []) in
  name_star, reprcontent

let dataclass ~name (decls : (string * string) list) =
  let name_star = String.capitalize_ascii name in
  let loc = !default_loc in
  let type_t = Str.type_ Nonrecursive [ Type.mk ~kind:(Ptype_record (List.map (function name, typename -> Type.field ~mut:Mutable { loc; txt = name } @@ Typ.constr { loc; txt = Longident.Lident typename } []) decls)) { loc; txt = "t" } ] in
  let mod_ = Str.module_ @@ Mb.mk { loc; txt = Some name_star } @@ Mod.structure (type_t :: []) in
  let reprcontent = Yield.structure (mod_ :: []) in
  name_star, reprcontent
