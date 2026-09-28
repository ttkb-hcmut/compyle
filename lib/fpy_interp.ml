[@@@module "%/../prgpy-stdlib.ml" [@prefixed? "prg"]]
type _ Effect.t += GetLocus : Codelib.locus option Effect.t

let catchall_nolocus f =
  match f () with v -> v
  | effect GetLocus, k -> Effect.Deep.continue k None

let with_my_locus f =
  Codelib.with_locus @@ fun locus -> 
  match f () with v -> v
  | effect GetLocus, k -> Effect.Deep.continue k (Some locus)

let get_locus_opt () = Effect.perform GetLocus

type e = ..

include struct
module Any =
  struct

  type e += Id : 't Trx.code * int Trx.code -> e

  let make t typenum = Id (t, typenum)

  let name = "?"

  end
  end

module P = Pyclosure

module E = struct type nonrec e = e end

module Hashtbl = Py_stdlib.Hashtbl.Make(E)

type closure_meta = ..

type Py_stdlib.Hashtbl.not_found_meta += Closure of (Hashtbl.t * [`meta of closure_meta Lazy.t])

let closure ?(tag = lazy(failwith "undefined tag")) tbl = Closure (tbl, `meta tag)

module Assoc_list = Py_stdlib.Assoc_list

type _ Effect.t += Return : e -> unit Effect.t

type error_ctx = Error_ctx of { linenum : int ; col : int ; line : string option; srcfile_path : string option }

class virtual type_mismatch =
  object
    method virtual got_type_repr : string
    (* method got_type_repr = failwith "unimplemented" *)
    method virtual expected_type_repr : string
    (* method expected_type_repr = failwith "unimplemented" *)
  end

type type_mismatch_meta = ..

class argument_type_mismatch' (argpos : int) (got_type_repr : string) (expected_type_repr : string) (__meta__ : type_mismatch_meta) =
  object inherit type_mismatch
    method argpos = argpos
    method got_type_repr = got_type_repr
    method expected_type_repr = expected_type_repr
    method __meta__ = __meta__
  end

type exn += Argument_type_mismatch_error of argument_type_mismatch'

let handle_return ~retval f =
  match f () with v -> v
  | effect Return v_ret, k ->
    retval := v_ret; Effect.Deep.continue k ()

let apps : (P.f -> e -> e option) list ref = ref []
let getouts : (P.fu -> e -> unit Trx.code option) list ref = ref []
let cast_unit_s : (kind:(unit -> type_mismatch_meta) -> e -> unit Trx.code option) list ref = ref []
let get_repr_s : (e -> string option) list ref = ref []
let modname_of_repr_s : (string -> string option) list ref = ref []
let to_string_s : (e -> string Trx.code option) list ref = ref []
let cat_s : (e -> e -> e option) list ref = ref []
let force_extract_s : e P.f_iu list ref = ref []
let infer_typenum_s : (e -> int Trx.code option) list ref = ref []
let infer_get_s : e P.f_infer_get list ref = ref []
let infer_make_s : e P.f_infer_make list ref = ref []
let infer_typeable_s : (e -> e option) list ref = ref []

let app f v =
  match List.fold_left (fun acc app -> match acc with None -> app f v | Some res -> Some res) None !apps
  with None -> failwith "couldn't apply code" | Some x -> x

let any_extract_code f v =
  match List.fold_left (fun acc app -> match acc with None -> app f v | Some res -> Some res) None !getouts
  with None -> failwith "couldn't extract code" | Some x -> x

let cast_unit ~kind v =
  match List.fold_left (fun acc cast_unit -> match acc with None -> cast_unit ~kind v | Some res -> Some res) None !cast_unit_s
  with None -> failwith "couldn't cast unit" | Some x -> x

let extract_repr_opt v =
  List.fold_left (fun acc get_opt -> match acc with None -> get_opt v | Some res -> Some res) None !get_repr_s

let extract_repr v =
  match extract_repr_opt v
  with None -> failwith "couldn't extract repr" | Some x -> x

let extract_modname s =
  match List.fold_left (fun acc get_opt -> match acc with None -> get_opt s | Some res -> Some res) None !modname_of_repr_s
  with None -> failwith "couldn't map repr to modname" | Some x -> x

let cast_to_string' v =
  List.fold_left (fun acc get_opt -> match acc with None -> get_opt v | Some res -> Some res) None !to_string_s

let cast_to_string v =
  match cast_to_string' v
  with None -> failwith "couldn't cast to string" | Some x -> x

let cat_opt v1 v2 =
  List.fold_left (fun acc get_opt -> match acc with None -> get_opt v1 v2 | Some res -> Some res) None !cat_s

let infer_typenum v =
  match List.fold_left (fun acc get_opt -> match acc with None -> get_opt v | Some res -> Some res) None !infer_typenum_s
  with None -> failwith "couldn't infer typenum" | Some x -> x

let infer_get v typenum =
  List.fold_left (fun acc get_opt -> match acc with None -> get_opt.P.f_infer_get v typenum | Some res -> Some res) None !infer_get_s

let infer_make v typenum =
  List.fold_left (fun acc get_opt -> match acc with None -> get_opt.P.f_infer_make v typenum | Some res -> Some res) None !infer_make_s

let infer_typeable_opt v =
  List.fold_left (fun acc get_opt -> match acc with None -> get_opt v | Some res -> Some res) None !infer_typeable_s

module Typeable =
  struct

  type e +=
    | Id : { make : 't Trx.code -> e; extract_code_opt : e -> 't Trx.code option; repr : string; typeid : 't Type.Id.t; to_t : e -> 't Trx.code option; craft_repr : Ppxlib.longident -> Ppxlib.expression ; inner: e } -> e

  let make  make extract_code_opt repr typeid to_t craft_repr inner = Id  { make; extract_code_opt; repr; typeid; to_t; craft_repr; inner  }

  let extract v f =
    match v with
    | Id  { make ; extract_code_opt ; repr ; to_t ; craft_repr ; typeid } -> f.P.f_typeable  make extract_code_opt repr typeid to_t craft_repr
    | _ -> failwith "couldn't cast typeable"

  let extract' v f =
    match v with
    | Id  { make ; extract_code_opt ; repr ; to_t ; craft_repr ; typeid } -> f.P.f_typeable  make extract_code_opt repr typeid to_t craft_repr
    | _ -> failwith "couldn't cast typeable"

  let () =
    apps :=
      (fun f v ->
        match v with
        | Id  u ->
          let newinner = List.fold_left (fun acc app -> match acc with None -> app f u.inner | Some res -> Some res) None !apps in
          Option.map (fun inner -> Id { u with inner }) newinner
        | v -> None
      ) :: !apps

  let () =
    getouts :=
      (fun f v ->
        match v with
        | Id  u ->
          List.fold_left (fun acc app -> match acc with None -> app f u.inner | Some res -> Some res) None !getouts
        | v -> None
      ) :: !getouts

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id { repr } -> Some (Printf.sprintf "%s type" repr)
        | _ -> None
      ) :: !get_repr_s

  end

module Lambda1 =
  struct

  type e += | Id : (e list -> e) -> e

  let make f = Id f

  let () =
    apps :=
      (fun f v ->
        match v with
        | Id f -> Some (Id f)
        | v -> None
      ) :: !apps

  let () =
    getouts :=
      (fun f v ->
        match v with
        | Id _ -> Some (f.P.f_u .< () >.)
        | v -> None
      ) :: !getouts

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id _ -> Some "lambda1"
        | _ -> None
      ) :: !get_repr_s

  end

module Make (S : sig
  type code_t
  val name : string
  val modname : string
  val code_to_string : code_t Trx.code -> string Trx.code
  val code_cat : code_t Trx.code -> code_t Trx.code -> code_t Trx.code option
  val try_cast : (e -> code_t Trx.code option) option
end) =
  struct type e += Id : S.code_t Trx.code -> e

  let make c = Id c

  let typeid = (Type.Id.make () : S.code_t Type.Id.t)

  let force (v: e) =
    match v with
    | Id c -> Some c
    | Any.Id (c, typenum) -> Some (Codelib.seq .< assert (Int.equal .~typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~c >.)
    | _ -> None

  let conv = function
    | [Id _ as v] -> v
    | [Any.Id _ as v] -> v
    | _ -> failwith ("not "^S.name)

  let extract_code_opt = function
    | Id c -> Some c
    | Any.Id (c, typenum) -> Some (Codelib.seq .< assert (Int.equal .~typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~c >.)
    | _ -> None

  let repr = S.name

  let cat' = S.code_cat

  let craft_repr =
    Ppxlib.(fun py_interp -> 
      let open Ppxlib_ast.Ast_helper in
      let loc = !default_loc in
      Exp.ident { loc; txt = Longident.Ldot (Ldot (py_interp, S.modname), "typeid") }
    )

  let typeable =
    Typeable.make
      make extract_code_opt repr typeid
      (match S.try_cast with Some f -> f | None -> fun _ -> failwith ("try casting isn't supported yet for " ^ S.name))
      craft_repr
        @@ Lambda1.make @@ conv

  include S

  let () =
    apps :=
      (fun f v ->
        match v with
        | Id c -> Some (Id (f.P.f_f c))
        | v -> None
      ) :: !apps

  let () =
    getouts :=
      (fun f v ->
        match v with
        | Id c -> Some (f.P.f_u c)
        | v -> None
      ) :: !getouts

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id _ -> Some name
        | _ -> None
      ) :: !get_repr_s

  let () =
    modname_of_repr_s :=
      (fun s -> if s = name then Some modname else None
      ) :: !modname_of_repr_s

  let to_string' v =
    match v with
    | Id c -> Some (S.code_to_string c)
    (* | Any.Id (c, typenum) -> Some (S.code_to_string @@ Codelib.seq .< assert (Int.equal .~typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~c >.) *)
    | _ -> None

  let () =
    to_string_s := to_string' :: !to_string_s

  let () =
    cat_s :=
      (fun v1 v2 ->
        match v1 with
        | Id c1 ->
        (
          match v2 with
          | Id c2 -> Some (Id (match S.code_cat c1 c2 with None -> failwith "couldnt cat this" | Some c -> c))
          | Any.Id (c2, typenum2) -> Some (Id (match S.code_cat c1 (Codelib.seq .< assert (Int.equal .~typenum2 .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~c2 >.) with None -> failwith "couldnt cat this" | Some c -> c))
          | _ -> None
        )
        | _ -> None
      ) :: !cat_s

  let () =
    force_extract_s :=
      { P.f_iu = fun v this_typenum ->
        match v with
        | Id c -> Some (Codelib.seq .< assert (Stdlib.Int.equal .~this_typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~c >.)
        | _ -> None
      }
      :: !force_extract_s

  let () =
    infer_typenum_s :=
      ( fun v ->
        match v with
        | Id _ -> Some (Lifts.Lift_int.lift @@ Type.Id.uid typeid)
        | _ -> None
      )
      :: !infer_typenum_s

  let () =
    infer_get_s :=
      { P.f_infer_get = fun v this_typenum ->
        match v with
        | Id c -> Some (Codelib.seq .< assert (Int.equal .~this_typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~c >.)
        | _ -> None
      }
      :: !infer_get_s

  let () =
    infer_make_s :=
      { P.f_infer_make = fun v this_typenum ->
        match v with
        | Id _ -> Some (fun c -> Id (Codelib.seq .< assert (Int.equal .~this_typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~c >.))
        | _ -> None
      }
      :: !infer_make_s

  let () =
    infer_typeable_s :=
      ( fun v ->
        match v with
        | Id _ -> Some typeable
        | _ -> None
      )
      :: !infer_typeable_s
  end

module String =
  struct
  include String
  module A = struct
    type code_t = string
    let name = "string"
    let modname = "String"
    let code_to_string c = c
    let code_cat c1 c2 = Some .< String.cat .~c1 .~c2 >.
    let try_cast = Some cast_to_string'
  end
  include Make(A)
  end

module Float =
  struct include Float
  include Make(struct
    type code_t = float
    let name = "float"
    let modname = "Float"
    let code_to_string c = .< Float.to_string .~c >.
    let code_cat c1 c2 = Some .< Float.add .~c1 .~c2 >.
    let try_cast = None
  end)
  end

module Int =
  struct include Int
  include Make(struct
    type code_t = int
    let name = "int"
    let modname = "Int"
    let code_to_string c = .< Int.to_string .~c >.
    let code_cat c1 c2 = Some .< Int.add .~c1 .~c2 >.
    let try_cast = None
  end)
  end

module Unit =
  struct include Unit
  include Make(struct
    type code_t = unit
    let name = "unit"
    let modname = "Unit"
    let code_to_string c = .< Unit.to_string .~c >.
    let code_cat c1 c2 = None
    let try_cast = None
  end)
  end

module Bytes =
  struct include Bytes
  include Make(struct
    type code_t = bytes
    let name = "bytes"
    let modname = "Bytes"
    let code_to_string c = .< Bytes.to_string .~c >.
    let code_cat c1 c2 = Some .< Bytes.cat .~c1 .~c2 >.
    let try_cast = None
  end)
  end

let () =
  cast_unit_s :=
    (fun ~kind -> function Unit.Id _ as v -> Some (match Unit.force v with Some c -> c | None -> failwith "idk") | _ -> None)
    :: !cast_unit_s

module Compiler =
  struct

  type bind = { bind : 'b. (unit -> 'b Trx.code Trx.code) -> 'b Trx.code Trx.code }

  type 'handled_top bind2 = { bind2 : 'b. (unit -> 'b Trx.code Trx.code) -> 'handled_top -> 'b Trx.code Trx.code }

  type bind_ = { bind_ : 'b. (unit -> 'b Trx.code) -> 'b Trx.code }

  type 'structure bind' = { bind': 'b. (unit -> 'b Trx.code Trx.code) -> ('structure -> 'b Trx.code Trx.code) -> 'b Trx.code Trx.code }

  end

include struct
module Lambda =
  struct

  type e += Id : ('retval Trx.code -> e) * (e -> 't Trx.code option) * string * 't Type.Id.t * 'retval Type.Id.t * (Ppxlib.longident -> Ppxlib.expression) * (Ppxlib.longident -> Ppxlib.expression) * ('t -> 'retval) Trx.code -> e

  let make retmake get get_repr gettype rettype getcraftrepr retcraftrepr cf = Id (retmake, get, get_repr, gettype, rettype, getcraftrepr, retcraftrepr, cf)

  let name = "lambda"

  let modname = "Lambda"

  (** TODO(kinten): typeid of lambda should be hashed by its constituent types *)
  (* let typeid = (Type.Id.make () : lambda1 Type.Id.t) *)

  type pairtbl_binding = B : 'a Type.Id.t * 'b Type.Id.t * ('a -> 'b) Type.Id.t -> pairtbl_binding

  let pairtbl = Stdlib.Hashtbl.create 10

  let typeid : type a b. a Type.Id.t -> b Type.Id.t -> (a -> b) Type.Id.t = fun arg1_type ret_type ->
    match Stdlib.Hashtbl.find pairtbl (Type.Id.uid arg1_type, Type.Id.uid ret_type) with
    | B (a, b, pairid) ->
      (
        match Type.Id.provably_equal a arg1_type with None -> failwith "MQ.M" | Some Type.Equal ->
        match Type.Id.provably_equal b ret_type  with None -> failwith "MQ.N" | Some Type.Equal ->
        pairid
      )
    | exception Not_found ->
      let pairid = Type.Id.make () in
      Stdlib.Hashtbl.add pairtbl (Type.Id.uid arg1_type, Type.Id.uid ret_type) (B (arg1_type, ret_type, pairid));
      pairid

  type 'o f_extract = { f_extract : 't 'ret. (('t -> 'ret) Trx.code * string) option -> 'o }

  let get_code_opt : type t retval. t Type.Id.t -> retval Type.Id.t -> e -> (t -> retval) Trx.code option = fun gettype' rettype' v ->
    match v with
    | Id (_, _, _, gettype, rettype, _, _, cf) ->
      Some
      ( match Type.Id.provably_equal gettype' gettype with None -> failwith "MAPP" | Some Type.Equal ->
        match Type.Id.provably_equal rettype' rettype with None -> failwith "MAPY" | Some Type.Equal ->
        cf
      )
    | _ -> None

  let conv = function
    | [Id _ as v] -> v
    | [Any.Id _ as v] -> v
    | _ -> failwith ("not lambda")

  let extract_code_opt k v =
    match v with
    | Id (_, _, arg1_repr, _, _, _, _, cf) -> k.f_extract (Some (cf, arg1_repr))
    | Any.Id (c, typenum) -> failwith "m010889"
    | _ -> k.f_extract None

  let typeable ret_make arg1_extract arg1_repr arg1_type ret_type arg1_craft_repr ret_craft_repr =
      Typeable.make
        (fun cf -> make ret_make arg1_extract arg1_repr arg1_type ret_type arg1_craft_repr ret_craft_repr cf)
        (fun v -> get_code_opt arg1_type ret_type v)
        "lambda"
        (typeid arg1_type ret_type)
        (fun _ -> failwith "cannot force cast to callable yet")
        Ppxlib.(fun py_interp -> 
          let open Ppxlib_ast.Asttypes in
          let open Ppxlib_ast.Ast_helper in
          let loc = !default_loc in
          Exp.apply
            (Exp.ident { loc; txt = Longident.Ldot (Ldot (py_interp, modname), "typeid") })
            [
              Nolabel, arg1_craft_repr py_interp;
              Nolabel, ret_craft_repr py_interp
            ]
        )
          @@ Lambda1.make @@ conv

  let () =
    apps :=
      (fun f v ->
        match v with
        | Id (retmake, get, get_repr, gettype, rettype, getcraftrepr, retcraftrepr, cf) -> Some (Id (retmake, get, get_repr, gettype, rettype, getcraftrepr, retcraftrepr, f.f_f cf))
        | v -> None
      ) :: !apps

  let () =
    getouts :=
      (fun f v ->
        match v with
        | Id (retmake, get, get_repr, gettype, rettype, _, _, cf) -> Some (f.f_u cf)
        | v -> None
      ) :: !getouts

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id _ -> Some name
        | _ -> None
      ) :: !get_repr_s

  let () =
    modname_of_repr_s :=
      (fun s -> if s = name then Some modname else None
      ) :: !modname_of_repr_s
  
  let () =
    force_extract_s :=
      { P.f_iu = fun v this_typenum ->
        match v with
        | Id (_, _, _, a, b, _, _, cf) -> Some (Codelib.seq .< assert (Stdlib.Int.equal .~this_typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid @@ typeid a b)) >. .< Stdlib.Obj.magic .~cf >.)
        | _ -> None
      }
      :: !force_extract_s

  let () =
    infer_typenum_s :=
      ( fun v ->
        match v with
        | Id (_, _, _, a, b, _, _, _) -> Some (Lifts.Lift_int.lift @@ Type.Id.uid @@ typeid a b)
        | _ -> None
      )
      :: !infer_typenum_s

  let () =
    infer_get_s :=
      { P.f_infer_get = fun v this_typenum ->
        match v with
        | Id (_, _, _, a, b, _, _, cf) -> Some (Codelib.seq .< assert (Int.equal .~this_typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid @@ typeid a b)) >. .< Stdlib.Obj.magic .~cf >.)
        | _ -> None
      }
      :: !infer_get_s

  let () =
    infer_make_s :=
      { P.f_infer_make = fun v this_typenum ->
        match v with
        | Id (a, b, c, d, e, f, g, _) -> Some (fun cf -> Id (a, b, c, d, e, f, g, Codelib.seq .< assert (Int.equal .~this_typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid @@ typeid d e)) >. .< Stdlib.Obj.magic .~cf >.))
        | _ -> None
      }
      :: !infer_make_s

  let () =
    infer_typeable_s :=
      ( fun v ->
        match v with
        | Id (a, b, c, d, e, f, g, _) -> Some (typeable a b c d e f g)
        | _ -> None
      )
      :: !infer_typeable_s

  type _ Effect.t += GetFuncName : string Trx.code Effect.t

  let get_func_name () =
    String.make @@ Effect.perform GetFuncName

  let provide_meta ~name f =
    match f () with v -> v | effect GetFuncName, k -> Effect.Deep.continue k (name : string Trx.code)

  end
  end

include struct
module Any =
  struct include Any

  let () =
    apps :=
      (fun f v ->
        match v with
        | Id (c, typeid) -> Some (Id (f.f_f c, typeid))
        | v -> None
      ) :: !apps

  let () =
    getouts :=
      (fun f v ->
        match v with
        | Id (c, typeid) -> Some (f.f_u c)
        | v -> None
      ) :: !getouts

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id _ -> Some name
        | _ -> None
      ) :: !get_repr_s

  let to_string' v =
    match v with
    | Id _ -> failwith "cannot resolve to_string for an any type. Please fully type this context"
    | _ -> None

  let () =
    to_string_s := to_string' :: !to_string_s

  let force_extract_opt v typenum =
    List.fold_left (fun acc get_opt -> match acc with None -> get_opt.P.f_iu v typenum | Some res -> Some res) None !force_extract_s

  let () =
    force_extract_s :=
      { P.f_iu = fun v this_typenum ->
        match v with
        | Id (c, typenum) -> Some (Codelib.seq .< assert (Stdlib.Int.equal .~this_typenum .~typenum) >. .< Stdlib.Obj.magic .~c >.)
        | _ -> None
      }
      :: !force_extract_s

  let () =
    infer_typenum_s :=
      ( fun v ->
        match v with
        | Id (_, typenum) -> Some typenum
        | _ -> None
      )
      :: !infer_typenum_s

  let () =
    infer_get_s :=
      { P.f_infer_get = fun v this_typenum ->
        match v with
        | Id (c, typenum) -> Some (Codelib.seq .< assert (Int.equal .~this_typenum .~typenum) >. .< Stdlib.Obj.magic .~c >.)
        | _ -> None
      }
      :: !infer_get_s

  let () =
    infer_make_s :=
      { P.f_infer_make = fun v this_typenum ->
        match v with
        | Id (_, typenum) -> Some (fun c -> Id (Codelib.seq .< assert (Int.equal .~this_typenum .~typenum) >. .< Stdlib.Obj.magic .~c >., typenum))
        | _ -> None
      }
      :: !infer_make_s

  end
  end

module Lambda2 =
  struct

  type e += Id : ('t -> int -> int -> 'retval) Trx.code * e P.f_leak -> e

  type 'o f_extract = { f_extract : 't 'ret. ('t -> int -> int -> 'ret) Trx.code option -> 'o }

  type lambda2

  (** TODO(kinten): typeid of lambda should be hashed by its constituent types *)
  let typeid = (Type.Id.make () : lambda2 Type.Id.t)

  let extract_code_opt k v = match v with Id (cf, _) -> k.f_extract (Some cf) | _ -> k.f_extract None

  let () =
    apps :=
      (fun f v ->
        match v with
        | Id (cf, mk) -> Some (Id (f.f_f cf, mk))
        | v -> None
      ) :: !apps

  let () =
    getouts :=
      (fun f v ->
        match v with
        | Id (cf, mk) -> Some (f.f_u cf)
        | v -> None
      ) :: !getouts

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id _ -> Some "lambda2"
        | _ -> None
      ) :: !get_repr_s

  let () =
    force_extract_s :=
      { P.f_iu = fun v this_typenum ->
        match v with
        | Id (cf, _) -> failwith "lambda2: polymorphic inference for arrow types are not yet supported"
        | _ -> None
      }
      :: !force_extract_s

  let () =
    infer_typenum_s :=
      ( fun v ->
        match v with
        | Id _ -> Some (Lifts.Lift_int.lift @@ Type.Id.uid typeid)
        | _ -> None
      )
      :: !infer_typenum_s

  let () =
    infer_get_s :=
      { P.f_infer_get = fun v this_typenum ->
        match v with
        | Id (cf, mk) -> Some (Codelib.seq .< assert (Int.equal .~this_typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~cf >.)
        | _ -> None
      }
      :: !infer_get_s

  let () =
    infer_make_s :=
      { P.f_infer_make = fun v this_typenum ->
        match v with
        | Id (_, mk) -> Some (fun cf -> Id (Codelib.seq .< assert (Int.equal .~this_typenum .~(Lifts.Lift_int.lift @@ Type.Id.uid typeid)) >. .< Stdlib.Obj.magic .~cf >., mk))
        | _ -> None
      }
      :: !infer_make_s

  let make_poly wrap_param (mk : e P.f_leak)
  =
    let cf =
      wrap_param @@ fun arg1 (typenum:int Trx.code) (rettypenum:int Trx.code) ->
      mk.P.f_leak [Any.make arg1 typenum] @@ fun ret_v ->
      (match Any.force_extract_opt ret_v rettypenum with Some c -> c | None -> failwith "AUYF")
    in
    Id (cf, mk)

  end

module Module =
  struct

  type e += Id : (string, e) Assoc_list.t -> e

  let make dict = Id dict

  let extract_opt v =
    match v with
    | Id d -> Some d
    | _ -> None

  let () =
    apps :=
      (fun f v ->
        match v with
        | Id ls -> Some (Id ls)
        | v -> None
      ) :: !apps

  let () =
    getouts :=
      (fun f v ->
        match v with
        | Id _ -> None
        | v -> None
      ) :: !getouts

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id _ -> Some "module"
        | _ -> None
      ) :: !get_repr_s

  end

module Tuple =
  struct

  type e += Id :
    'a Type.Id.t * 'b Type.Id.t *
    string * string *
    (Ppxlib.longident -> Ppxlib.expression) * (Ppxlib.longident -> Ppxlib.expression) *
    ('a * 'b) Trx.code -> e

  let make
    a_typeid b_typeid
    a_repr b_repr
    a_craft_repr b_craft_repr
    c
    =
      Id (
        a_typeid, b_typeid,
        a_repr, b_repr,
        a_craft_repr, b_craft_repr,
        c
      )

  let repr a_repr b_repr = a_repr ^ " * " ^ b_repr

  let name = "tuple"

  let modname = "Tuple"

  let get_code_opt : type a b. a Type.Id.t -> b Type.Id.t -> e -> (a * b) Trx.code option = fun a' b' v ->
    match v with
    | Id (a_typeid, b_typeid, _, _, _, _, c) ->
      Some
      (
        match Type.Id.provably_equal a_typeid a' with None -> failwith "MMMMN" | Some Type.Equal ->
        match Type.Id.provably_equal b_typeid b' with None -> failwith "MMMML" | Some Type.Equal ->
        c
      )
    | _ -> None

  let get_code_opt' : type a b. a Type.Id.t -> b Type.Id.t -> e -> (a * b) Trx.code option = fun a' b' v ->
    match v with
    | Id (a_typeid, b_typeid, _, _, _, _, c) ->
      Some
      (
        Codelib.seq .< assert ((Stdlib.Int.equal .~(Lifts.Lift_int.lift @@ Type.Id.uid a_typeid) .~(Lifts.Lift_int.lift @@ Type.Id.uid a')) && (Stdlib.Int.equal .~(Lifts.Lift_int.lift @@ Type.Id.uid b_typeid) .~(Lifts.Lift_int.lift @@ Type.Id.uid b'))) >. .< Stdlib.Obj.magic .~c >.
      )
    | _ -> None

  let get_code_fst_opt : type a b. a Type.Id.t -> b Type.Id.t -> e -> a Trx.code option = fun a' b' v ->
    match get_code_opt a' b' v with Some c -> Some .< let a, _ = .~c in a >. | None -> None

  let get_code_snd_opt : type a b. a Type.Id.t -> b Type.Id.t -> e -> b Trx.code option = fun a' b' v ->
    match get_code_opt a' b' v with Some c -> Some .< let _, b = .~c in b >. | None -> None

  type pairtbl_binding = B : 'a Type.Id.t * 'b Type.Id.t * ('a * 'b) Type.Id.t -> pairtbl_binding

  (* let typeid = (Type.Id.make () : [`tuple] Type.Id.t) *)

  let pairtbl = Stdlib.Hashtbl.create 10

  let typeid : type a b. a Type.Id.t -> b Type.Id.t -> (a * b) Type.Id.t = fun arg1_type ret_type ->
    match Stdlib.Hashtbl.find pairtbl (Type.Id.uid arg1_type, Type.Id.uid ret_type) with
    | B (a, b, pairid) ->
      (
        match Type.Id.provably_equal a arg1_type with None -> failwith "MQ,,M" | Some Type.Equal ->
        match Type.Id.provably_equal b ret_type  with None -> failwith "MQ,,N" | Some Type.Equal ->
        pairid
      )
    | exception Not_found ->
      let pairid = Type.Id.make () in
      Stdlib.Hashtbl.add pairtbl (Type.Id.uid arg1_type, Type.Id.uid ret_type) (B (arg1_type, ret_type, pairid));
      pairid

  let conv = function
    | [Id _ as v] -> v
    | [Any.Id _ as v] -> v
    | _ -> failwith ("not tuple")

  let typeable arg1_type ret_type arg1_repr ret_repr arg1_craft_repr ret_craft_repr =
    Typeable.make
      (fun cf -> make arg1_type ret_type arg1_repr ret_repr arg1_craft_repr ret_craft_repr cf)
      (fun v -> get_code_opt arg1_type ret_type v)
      (arg1_repr ^ " * " ^ ret_repr)
      (typeid arg1_type ret_type)
      (fun _ -> failwith "cannot force cast to tuple yet")
      Ppxlib.(fun py_interp -> 
        let open Ppxlib_ast.Asttypes in
        let open Ppxlib_ast.Ast_helper in
        let loc = !default_loc in
        Exp.apply
          (Exp.ident { loc; txt = Longident.Ldot (Ldot (py_interp, modname), "typeid") })
          [
            Nolabel, arg1_craft_repr py_interp;
            Nolabel, ret_craft_repr py_interp
          ]
      )
        @@ Lambda1.make @@ conv

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id (_, _, a_repr, b_repr, _, _, _) -> Some (repr a_repr b_repr)
        | _ -> None
      ) :: !get_repr_s

  let () =
    apps :=
      (fun f v ->
        match v with
        | Id (a, b, d, e, a_, b_, c) -> Some (Id (a, b, d, e, a_, b_, f.P.f_f c))
        | v -> None
      ) :: !apps

  let () =
    modname_of_repr_s :=
      (fun s -> if s = name then Some modname else None
      ) :: !modname_of_repr_s

  let () =
    infer_typeable_s :=
      ( fun v ->
        match v with
        | Id (a_type, b_type, a_repr, b_repr, a_craft_repr, b_craft_repr, _) -> Some (typeable a_type b_type a_repr b_repr a_craft_repr b_craft_repr)
        | _ -> None
      )
      :: !infer_typeable_s

  end

module Union =
  struct

  type e += Id : 'a Type.Id.t * 'b Type.Id.t * (Ppxlib.longident -> Ppxlib.expression) * (Ppxlib.longident -> Ppxlib.expression) * ('a, 'b) Either.t Trx.code -> e

  end

let apply ?kind v_fn v_args =
  let v_args () =
    match v_args () with
    | [] -> [ Unit.make .< () >. ]
    | vs -> vs
  in
  match v_fn () with
  | Typeable.Id { make; extract_code_opt; repr; typeid; to_t; inner } ->
    let v_args = v_args () in
    let v1 = match v_args with v1 :: [] -> v1 | v_args -> failwith @@ Printf.sprintf "LJA" in
    make @@
    (match to_t v1 with None -> failwith "sdmads" | Some v -> v)
  | Lambda2.Id (cf, f'') ->
    let v_args = v_args () in
    let v1 = match v_args with v1 :: [] -> v1 | v_args -> failwith @@ Printf.sprintf "lambda2: only 1 argument is supported, but got %d" @@ List.length v_args in
    let get_typeid = infer_typenum v1 in
    let c1 = match infer_get v1 get_typeid with Some v -> v | None -> failwith "sdfmi" in
    let ret_v' = ref None in
    let _ = f''.P.f_leak [v1] @@ fun ret_v -> ret_v' := Some ret_v; .< () >. in
    let ret_v = (match !ret_v' with Some v -> v | None -> failwith "sdman") in
    let ret_typeid = infer_typenum ret_v in
    (match infer_make ret_v ret_typeid with Some f -> f | None -> failwith "zmzmi") @@
    .< .~cf .~c1 .~get_typeid .~ret_typeid >.
  | Lambda.Id (retmake, get, get_repr, _, _, _, _, cf) ->
    let v_args = v_args () in
    let rec v1 v_args =
      match v_args with
      | [] -> failwith @@ Printf.sprintf "lambda: only 1 argument is supported, but got %d" @@ List.length v_args
      | v1 :: [] -> v1
      | a :: b :: [] ->
        let typeable_a = match infer_typeable_opt a with Some x -> x | None -> failwith "uAHYQ" in
        let typeable_b = match infer_typeable_opt b with Some x -> x | None -> failwith "uAHYP" in
        let open Pyclosure in
        Typeable.extract typeable_a
        { f_typeable = fun _ arg1_extract arg1_repr arg1_type _ arg1_craft_repr -> 
          Typeable.extract typeable_b
          { f_typeable = fun _ ret_extract ret_repr ret_type _ ret_craft_repr ->
            Tuple.make arg1_type ret_type arg1_repr ret_repr arg1_craft_repr ret_craft_repr
            (
              match arg1_extract a, ret_extract b with
              | Some c1, Some c2 -> .< .~c1, .~c2 >.
              | _, _ -> failwith "MAL"
            )
          }
        }
      | a :: v_args ->
        let b = v1 v_args in
        let typeable_a = match infer_typeable_opt a with Some x -> x | None -> failwith "10010uAHYQ" in
        let typeable_b = match infer_typeable_opt b with Some x -> x | None -> failwith "197uAHYP" in
        let open Pyclosure in
        Typeable.extract typeable_a
        { f_typeable = fun _ arg1_extract arg1_repr arg1_type _ arg1_craft_repr -> 
          Typeable.extract typeable_b
          { f_typeable = fun _ ret_extract ret_repr ret_type _ ret_craft_repr ->
            Tuple.make arg1_type ret_type arg1_repr ret_repr arg1_craft_repr ret_craft_repr
            (
              match arg1_extract a, ret_extract b with
              | Some c1, Some c2 -> .< .~c1, .~c2 >.
              | _, _ -> failwith "MAL"
            )
          }
        }
    in
    let v1 = v1 v_args in
    let c1 = match get v1 with Some v -> v | None -> raise @@ Argument_type_mismatch_error (new argument_type_mismatch' 0 (extract_repr v1) get_repr (match kind with None -> failwith "MQI" | Some kind -> kind ())) in
    retmake .< .~cf .~c1 >.
  | Lambda1.Id f ->
    f @@ v_args ()
  | Any.Id (cf, cf_typenum) ->
    (* higher-order function as any - any-func *)
    failwith "higher order any-func not supported"
    (* let v_args = v_args () in *)
    (* let v1 = match v_args with v1 :: [] -> v1 | v_args -> failwith @@ Printf.sprintf "any-func: only 1 argument is supported, but got %d" @@ List.length v_args in *)
    (* let get_typeid = infer_typenum v1 in *)
    (* let c1 = match infer_get v1 get_typeid with Some v -> v | None -> failwith "mqiao" in *)
    (* let cf = .< Stdlib.Obj.magic .~cf >. in *)
    (* Any.Id (.< .~cf .~c1 >., cf_typenum) *)
  | u -> failwith @@ Printf.sprintf "not an applicable; got %s" @@ Option.value ~default:"<abstr>" @@ extract_repr_opt u

let () =
  cast_unit_s :=
    (fun ~kind v -> Unit.extract_code_opt v)
    :: !cast_unit_s

let getattr v fieldname =
  match fieldname with
  | ("__add__" as methname) -> 
    let mk v_args =
      let v1 = match v_args with v1 :: [] -> v1 | v_args -> failwith @@ Printf.sprintf "%s: only 1 argument is supported, but got %d" methname (List.length v_args) in
      let retval = match cat_opt v v1 with Some v -> v | None -> failwith @@ Printf.sprintf "failed to perform %s; argument types %s and %s unsupported" methname (extract_repr v) (extract_repr v1) in
      retval
    in
    Lambda1.make mk
  | "__getitem__" ->
    (** TODO(kinten): dynamic dispatch here *)
    let mk v_args = apply (fun () -> v) (fun () -> v_args) in
    Lambda1.make mk
  | fieldname ->
    match v with
    | Module.Id dict -> Assoc_list.get fieldname dict
    | _ -> failwith "not a getattr'able"

let iterattr f v =
  match v with
  | Module.Id dict -> Assoc_list.iter (fun (name, v) -> f (name, v)) dict
  | _ -> failwith "not an iterattr'able"

let selectattr pred v =
  match v with
  | Module.Id dict -> (match Assoc_list.find_map (function (name, v) when pred (name, v) -> Some (name, v) | _ -> None) dict with Some (name, v) -> Module.Id (Assoc_list.imap [name, v] dict) | None -> failwith "fixme")
  | _ -> failwith "not a selectattr'able"

include struct
module Lambda =
  struct include Lambda

  let make_full
  ~kind
  wrap_param
  (ret : e -> 'retval Trx.code option) (getmake : 't Trx.code -> e) (get_repr : string)
  (mk : e -> (e -> 'retval Trx.code) -> 'retval Trx.code)
  (retmake : 'retval Trx.code -> e) (get : e -> 't Trx.code option)
  (gettype : 't Type.Id.t) (rettype : 'retval Type.Id.t)
  getcraftrepr retcraftrepr
  =
    let cf =
      wrap_param @@ fun t ->
      provide_meta ~name:.< failwith "AKJ" >. @@ fun () ->
      mk (getmake t) @@ fun ret_v ->
      (* let ret_v = finalize_fundef ~kind ret ret_v (fun () -> ret_v) @@ retmake in *)
      let ret_c : 'retval Trx.code = match ret ret_v with None -> failwith "make_full failed to cast rettype" | Some c -> c in
      ret_c
    in
    Id (retmake, get, get_repr, gettype, rettype, getcraftrepr, retcraftrepr, cf)

  end
  end

module EList = struct
  type e += Id : e list -> e

  let make es = Id es

  let name = "e-list"

  let extract_opt v =
    match v with
    | Id xs -> Some xs
    | _ -> None

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id _ -> Some name
        | _ -> None
      ) :: !get_repr_s
end

module EInt = struct
  type e += Id : int -> e

  let make x = Id x

  let name = "e-int"

  let extract_opt v =
    match v with
    | Id x -> Some x
    | _ -> None

  let () =
    get_repr_s :=
      (fun v ->
        match v with
        | Id _ -> Some name
        | _ -> None
      ) :: !get_repr_s
end
