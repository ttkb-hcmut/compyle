[@@@module "%/../prgpy-stdlib.ml" [@prefixed? "prg"]]
[@@@module "%/../prgpy-interp.ml" [@prefixed? "prg"]]
[@@@module "%/../prgpy-gen.ml" [@prefixed? "prgpy-"]]
[@@@module "%/../prgpy-sym.ml" [@prefixed? "prgpy-"]]
open Py_stdlib
open Py_interp
open Sym

module P = Pyclosure

type _ Effect.t += GetTop : bool Effect.t

type _ Effect.t += GetEscope : bool Effect.t

type _ Effect.t += GetHashtblReplace : (unit -> (string -> e -> unit) Trx.code option) option Effect.t

type closure_meta +=
  | Pretextobj : closure_meta
  | Textobj : 'expr Type.Id.t * 'expr -> closure_meta

type type_mismatch_meta +=
  | Pretextobj' : type_mismatch_meta
  | Textobj' : 'expr Type.Id.t * 'expr -> type_mismatch_meta

let otextobj = Pretextobj

let pexpr = Type.Id.make ()

let unlock_closure_meta (type a) (pexpr : a Type.Id.t) = function
  | Pretextobj -> failwith "sdf"
  | Textobj (type_, textobj) ->
    ( match Type.Id.provably_equal pexpr type_ with Some Type.Equal -> (textobj : a) | None -> failwith "asdf" )
  | _ -> failwith "sdf"

let typematch () = Pretextobj'

let unlock_type_mismatch_meta : type a. a Type.Id.t -> Py_interp.type_mismatch_meta -> a = fun pexpr -> function
  | Pretextobj' -> failwith "sdf"
  | Textobj' (type_, textobj) ->
    ( match Type.Id.provably_equal pexpr type_ with Some Type.Equal -> textobj | None -> failwith "asdf" )
  | _ -> failwith "sdf"

let on_top f = match f `handled_top with v -> v | effect GetTop, k -> Effect.Deep.continue k true

let on_top' f = match f () with v -> v | effect GetTop, k -> Effect.Deep.continue k true

let not_on_top f = match f `handled_top with v -> v | effect GetTop, k -> Effect.Deep.continue k false

let not_on_top' f = match f () with v -> v | effect GetTop, k -> Effect.Deep.continue k false

let is_on_top () = Effect.perform GetTop

let with_escope f = match f `handled_escope with v -> v | effect GetEscope, k -> Effect.Deep.continue k true

let with_escope' f = fun () -> match f () with v -> v | effect GetEscope, k -> Effect.Deep.continue k true

let with_escope'' f = match f () with v -> v | effect GetEscope, k -> Effect.Deep.continue k true

let ignore_escope f = match f `handled_escope with v -> v | effect GetEscope, k -> Effect.Deep.continue k false

let ignore_escope' f = match f () with v -> v | effect GetEscope, k -> Effect.Deep.continue k false

let is_in_escope () = Effect.perform GetEscope

let ignore_hashtbl_replace' f = match f () with v -> v | effect GetHashtblReplace, k -> Effect.Deep.continue k None

let with_hashtbl_replace' f k = match k () with v -> v | effect GetHashtblReplace, k -> Effect.Deep.continue k @@ Some f

let get_hashtbl_replace_opt () =
  match Effect.perform GetHashtblReplace with None -> .< Option.none >. | Some f -> match f () with Some f -> .< Option.some .~f >. | None -> .< Option.none >.

let get_hashtbl_replace_opt' () = Effect.perform GetHashtblReplace

let reduceme args =
  let args =
    List.fold_left (fun (acc : [`zero | `one of (string * expr) | `two of (expr list)]) x ->
      match acc, x with
      | `zero, (argname1, argtype1) -> `one (argname1, argtype1)
      | `one (_, init), (_, argtype1) -> `two [argtype1; init]
      | `two acc, (_, argtype1) -> `two (argtype1 :: acc)
    ) `zero args
  in
  match args with
  | `zero -> failwith "it's impossible to have a zero-arg argument list"
  | `one (name, arg) -> name, [arg]
  | `two args -> "arg1", List.rev args

let signature args rettype =
  let args =
    List.fold_left (fun (acc : [`dynamic of string list | `static of (string * expr) list] option) arg ->
      match acc, arg with
      | None, `arg(argname1, Some argtype1) -> Some (`static [argname1, argtype1])
      | None, `arg(argname1, None) -> Some (`dynamic [argname1])
      | Some (`static acc), `arg(argname1, Some argtype1) -> Some (`static ((argname1, argtype1) :: acc))
      | Some (`static acc), `arg(argname1, None) -> failwith "unresolvable type hole for static function"
      | Some (`dynamic acc), `arg(argname, Some _) -> failwith "conflictive type annotation for dynamic function"
      | Some (`dynamic acc), `arg(argname1, None) -> Some (`dynamic (argname1 :: acc))
    ) None args
  in
  let sign =
    match args, rettype with
    | None, Some rettype -> `static ([], rettype)
    | None, None -> `dynamic []
    | Some (`static xs), Some rettype -> `static (xs, rettype)
    | Some (`static xs), None -> failwith "static function lacing return type"
    | Some (`dynamic xs), Some _ -> failwith "dynamic function with conflictive return type annotation"
    | Some (`dynamic xs), None -> `dynamic xs
  in
  match sign with
  | `static (args, rettype) -> `static (List.rev args, rettype)
  | `dynamic args -> `dynamic (List.rev args)

let rec implementation ~runtime ~str_extension tr =
  ignore_escope' @@ fun () ->
  on_top' @@ fun () ->
  ignore_hashtbl_replace' @@ fun () ->
  program ~runtime ~str_extension tr

and program ~runtime ~str_extension tr =
  .<
  let heap = Hashtbl.create ~kind:(closure ~tag:(lazy otextobj)) 10 in
  catchall_nolocus @@ fun () ->
  .~(runtime .<heap>.);
  .~(on_top @@ (body ~str_extension ~heap:.<heap>. tr).Compiler.bind2 @@ fun () -> .< .< () >. >.)
  >.

and body ~str_extension ~heap tr = { Compiler.bind2 = fun k `handled_top ->
  List.fold_right (fun str c -> (body_str_linebyline ~str_extension ~heap str).Compiler.bind @@ fun () -> c) tr (k ())
  }

and body_str_linebyline ~str_extension ~heap repr = { Compiler.bind = fun k ->
  (str_extension ~heap repr).Compiler.bind' k @@ fun repr ->
  match repr with
  | Pstr_assign { lhs; lhs_type = None; rhs } ->
    let exporting k' =
      let app = any_extract_code { Pyclosure.f_u = fun c -> .< Stdlib.ignore (`export_opaque_value, lhs, .~c) >. } in
      if is_on_top () then .< Codelib.seq (app @@ Hashtbl.find .~heap lhs) .~(k' ()) >. else k' ()
    in
    let app locus = app { P.f_f = fun c -> Codelib.genlet ~locus ~name:lhs c } in
    .< Codelib.with_locus @@ fun locus -> Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) lhs @@ app locus @@ .~(expr ~heap rhs); .~(exporting k) >.  
  | Pstr_assign { lhs; lhs_type = Some _; rhs } -> failwith "typed assignment is not yet supported"
  | Pstr_eval e -> .< Codelib.seq (cast_unit ~kind:typematch .~(expr ~heap e)) .~(k ()) >.
  | Pstr_def { funname; args; rettype; body = fbody; decorators = f_decorator_s } ->
    let c_of_decs decs c_init = List.fold_right (fun dec c -> .< apply ~kind:typematch (fun () -> .~(expr ~heap dec)) (fun () -> [.~c]) >.) decs c_init in
    let app locus = app { P.f_f = fun c -> Codelib.genlet ~locus ~name:funname c }
    and app' locus = app { P.f_f = fun c -> Codelib.genlet ~locus c } in
    let setup_meta ~locus ~heap =
      let app locus = Py_interp.app { P.f_f = fun c -> Codelib.genlet ~locus ~name:funname c } in
      .<
      Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) funname @@ app .~locus @@ Module.make @@ Assoc_list.of_list ~kind:"module" [
        "__name__", String.make .< funname >.
      ];
      >.
    in
    let setup_args ~heap v_args k =
      match signature args rettype with
      | `static (args, _) ->
        .<
        let v_arg = match .~v_args with v1 :: [] -> v1 | _ -> failwith "oqiah impossible" in
        .~(
        let rec c args v_arg k =
        (
          match args with
          | [] -> k ()
          | (argname, _) :: [] ->
            .<
            Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) argname .~v_arg;
            .~(k ())
            >.
          | (arg1_name, argtype1) :: (arg2_name, argtype2) :: [] ->
            .<
            let typeable_a = .~(argtype1) in
            let typeable_b = .~(argtype2) in
                let open Pyclosure in
                Typeable.extract typeable_a
                { f_typeable = fun arg1_make arg1_extract _ arg1_type _ _ -> 
                  Typeable.extract typeable_b
                  { Pyclosure.f_typeable = fun ret_make ret_extract ret_repr ret_type _ _ ->
                    Codelib.with_locus @@ fun locus -> Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) arg1_name @@ app locus @@ arg1_make (match Tuple.get_code_fst_opt arg1_type ret_type .~v_arg with Some c -> c | None -> failwith "dsma");
                    Codelib.with_locus @@ fun locus -> Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) arg2_name @@ app locus @@ ret_make (match Tuple.get_code_snd_opt arg1_type ret_type .~v_arg with Some c -> c | None -> failwith "dsmb");
                    .~(k ())
                  }
                }
                ;
            >.
          | (arg1_name, argtype1) :: args ->
            let [@warning "-8"] (_, argtype2) :: (_, argtype3) :: _ = args in
            .<
            let typeable_a = .~(argtype1) in
            let typeable_b = .~(argtype2) in
            let typeable_c = .~(argtype3) in
                let open Pyclosure in
                Typeable.extract typeable_a
                { f_typeable = fun arg1_make _ _ arg1_type _ arg1_craft_repr -> 
                  Typeable.extract typeable_b
                  { Pyclosure.f_typeable = fun ret_make _ ret_repr ret_type _ ret_craft_repr ->
                    Typeable.extract typeable_c
                    { Pyclosure.f_typeable = fun ret2_make _ ret2_repr ret2_type _ ret2_craft_repr ->
                      let bc_tuple_typeid = Tuple.typeid ret_type ret2_type in
                      Codelib.with_locus @@ fun locus -> Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) arg1_name @@ app locus @@ arg1_make (match Tuple.get_code_fst_opt arg1_type bc_tuple_typeid .~v_arg with Some c -> c | None -> failwith "dsma");
                      Codelib.with_locus @@ fun locus -> 
                      let nextbundle = Codelib.genlet ~locus (match Tuple.get_code_snd_opt arg1_type bc_tuple_typeid .~v_arg with Some c -> c | None -> failwith "dsmb") in
                      let v_arg = Tuple.make ret_type ret2_type ret_repr ret2_repr ret_craft_repr ret2_craft_repr nextbundle in
                      .~(c args .<v_arg>. k)
                    }
                    
                  }
                  
                }
                ;
            >.
        )
        in
        c (List.map (fun (name, type_) -> (name, Codelib.genlet @@ expr ~heap type_)) args) .<v_arg>. k
        )
        >.
      | `dynamic [] -> k ()
      | `dynamic args ->
        .< List.iter (fun (v_arg, argname) -> Hashtbl.replace .~heap argname v_arg) @@ List.combine .~v_args args; .~(k ()) >.
    in
    let f' =
      .<
      fun v_args k ->
      .~(
      not_on_top' @@ fun () ->
      .<
      let retval = ref (Unit.make .< () >.) in
      let heap = Hashtbl.copy .~heap in
      Codelib.with_locus @@ fun locus ->
      .~(setup_meta ~locus:.<locus>. ~heap:.<heap>.);
      Codelib.seq .< Stdlib.ignore `argsbegin >. @@
      .~(
      setup_args ~heap:.<heap>. .<v_args>. @@ fun () ->
      .<
      Codelib.seq .< Stdlib.ignore `argsend >. @@
      handle_return ~retval @@ fun () ->
      .~(not_on_top @@ (body ~str_extension ~heap:.<heap>. fbody).Compiler.bind2 @@ fun () ->
      .<
      k !retval
      >.
      )
      >.
      )
      >.
      )
      >.
    in
    let f_star mkv =
      .<
      fun v_args k ->
      .~(
      not_on_top' @@ fun () ->
      .< k @@ apply ~kind:typematch (fun () -> .~(mkv ())) (fun () -> v_args) >.
      )
      >.
    in
    (
      let doit argtype1 argname1 rettype =
        let exporting k' =
          let app = { Lambda.f_extract = function Some (cf, arg1_repr) -> .< Stdlib.ignore (`export, funname, .~cf, .~(Lifts.Lift_string.lift arg1_repr)) >. | None -> failwith "wtf" } in
          if is_on_top () then .< Codelib.seq (Lambda.extract_code_opt app @@ Hashtbl.find .~heap funname) .~(k' ()) >. else k' ()
        in
        .<
        let open Pyclosure in
        Typeable.extract .~argtype1
        { f_typeable = fun arg1_make arg1_extract arg1_repr arg1_type _ arg1_craft_repr -> 
          Typeable.extract .~rettype
          { f_typeable = fun ret_make ret_extract ret_repr ret_type _ ret_craft_repr ->
            .~(
              let v f' = .< Lambda.make_full ~kind:typematch (Gen.func ~name:argname1 arg1_craft_repr arg1_type ret_craft_repr ret_type) ret_extract arg1_make arg1_repr (fun v_arg k -> .~f' [v_arg] k) ret_make arg1_extract arg1_type ret_type arg1_craft_repr ret_craft_repr >. in
              match f_decorator_s with
              | [] -> .< Codelib.with_locus @@ fun locus -> Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) funname @@ app locus @@ .~(v f'); .~(exporting k) >.
              | decs ->
                .<
                Codelib.with_locus @@ fun locus -> let fff = app' locus @@ .~(c_of_decs decs @@ v f') in
                Codelib.with_locus @@ fun locus -> Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) funname @@ app locus @@ .~(v @@ f_star @@ fun () -> .<fff>.); .~(exporting k)
                >.
            )
          }
        }
        >.
      in
      match signature args rettype with
      | `static (args, rettype) ->
        (
          let argname, args = reduceme args in
          let rec mk_argtype args =
            match args with
            | [] -> failwith "i18 impossible"
            | argtype1 :: [] -> (expr ~heap argtype1)
            | argtype1 :: argtype2 :: [] ->
              .<
              let typeable_a = .~(expr ~heap argtype1) in
              let typeable_b = .~(expr ~heap argtype2) in
              let open Pyclosure in
              Typeable.extract typeable_a { f_typeable = fun _ arg1_extract arg1_repr arg1_type _ arg1_craft_repr -> 
              Typeable.extract typeable_b { f_typeable = fun ret_make ret_extract ret_repr ret_type _ ret_craft_repr ->
              Tuple.typeable arg1_type ret_type arg1_repr ret_repr arg1_craft_repr ret_craft_repr
              }}
              >.
            | argtype1 :: args ->
              .<
              let typeable_a = .~(expr ~heap argtype1) in
              let typeable_b = .~(mk_argtype args) in
              let open Pyclosure in
              Typeable.extract typeable_a { f_typeable = fun _ arg1_extract arg1_repr arg1_type _ arg1_craft_repr -> 
              Typeable.extract typeable_b { f_typeable = fun ret_make ret_extract ret_repr ret_type _ ret_craft_repr ->
              Tuple.typeable arg1_type ret_type arg1_repr ret_repr arg1_craft_repr ret_craft_repr
              }}
              >.
          in
          doit (mk_argtype args) argname (expr ~heap rettype)
        )
      | `dynamic [argname1] ->
        let exporting k' =
          if is_on_top () then .< Codelib.seq .< Stdlib.ignore (`export_opaque_value_n, funname) >. .~(k' ()) >. else k' ()
        in
        let v f' = .< Lambda2.make_poly (fun k -> .< fun arg1 get_typenum ret_typenum -> .~(k .<arg1>. .<get_typenum>. .<ret_typenum>.) >.) .~f' >. in
        .<
        Codelib.with_locus @@ fun locus -> Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) funname @@ app locus @@ .~(c_of_decs f_decorator_s @@ v .< { Pyclosure.f_leak = .~f' } >.); .~(exporting k)
        >.
      | `dynamic _ ->
        failwith "n-ary dynamic functions are not yet supported"
    )
  | Pstr_return ret_repr ->
    let ret v = Effect.perform @@ Return v in
    .< ret .~(expr ~heap ret_repr); .~(k ()) >.
  | Pstr_assert _ -> failwith "judgements are not yet supported"
  | Pstr_defclass { funname; args; body; decorators } ->
    .<
    let heap' = Hashtbl.copy .~heap in
    let btable = Stdlib.Hashtbl.create 10 in
    Codelib.seq .< Stdlib.ignore (`classbegin, .~(Lifts.Lift_string.lift funname)) >. @@
    .~(
    List.fold_right (fun str c ->
      with_hashtbl_replace' (function () when is_on_top () -> Some .< fun name v -> Stdlib.Hashtbl.replace btable name v >. | () -> None) @@ fun () ->
      (body_str_linebyline ~str_extension ~heap:.<heap'>. str).Compiler.bind @@ fun () -> c
    ) body @@
    .<
    Hashtbl.replace .~heap ?on_replace:.~(get_hashtbl_replace_opt ()) .~(Lifts.Lift_string.lift funname) @@ Module.make @@ Assoc_list.of_seq ~kind:"module" @@ Stdlib.Hashtbl.to_seq btable;
    Codelib.seq .< Stdlib.ignore (`classend, .~(Lifts.Lift_string.lift funname)) >. .~(k ())
    >.
    )
    >.
  (* | Pstr_defclass { funname; args; body; decorators = [] } -> *)
  (*   .< *)
  (*   let heap = Hashtbl.copy .~heap in *)
  (*   let decls = ref [] in *)
  (*   .~(List.fold_right (fun str x -> (class_str_linebyline ~heap:.<heap>. ~decls:.<decls>. str).Compiler.bind_ @@ fun () -> x) body *)
  (*   .< *)
  (*   let funname_star, reprcontent = Gen.moduleclass ~name:.~(Lifts.Lift_string.lift funname) (List.rev !decls) in *)
  (*   Codelib.seq .< Stdlib.ignore (`insert_module, .~(Lifts.Lift_string.lift funname), .~(Lifts.Lift_string.lift funname_star), .~(Lifts.Lift_string.lift reprcontent)) >. .~(k ()) *)
  (*   >.) *)
  (*   >. *)
  (* | Pstr_defclass { funname; args; body; decorators = [Pexp_var ("dataclass", _)] } -> *)
  (*   .< *)
  (*   let heap = Hashtbl.copy .~heap in *)
  (*   let decls = ref [] in *)
  (*   .~(List.fold_right (fun str x -> (class_str_linebyline ~heap:.<heap>. ~decls:.<decls>. str).Compiler.bind_ @@ fun () -> x) body *)
  (*   .< *)
  (*   let funname_star, reprcontent = Gen.dataclass ~name:.~(Lifts.Lift_string.lift funname) (List.rev !decls) in *)
  (*   Codelib.seq .< Stdlib.ignore (`insert_module, .~(Lifts.Lift_string.lift funname), .~(Lifts.Lift_string.lift funname_star), .~(Lifts.Lift_string.lift reprcontent)) >. .~(k ()) *)
  (*   >.) *)
  (*   >. *)
  | Pstr_dummy -> k ()
  | _ -> failwith "unknown structure"
  }

and expr ~heap repr =
  match repr with
  | Pexp_var (rhs, _) -> textobj repr @@ fun () -> .< Hashtbl.find .~heap rhs >.
  | Pexp_fcall (f_repr, arg_repr_s) ->
    let f_c = expr ~heap f_repr in
    let args_c =
      match arg_repr_s with
      | [] -> .< [ Unit.make .< () >. ] >.
      | arg_repr_s -> List.fold_right (fun repr c -> .< .~(expr ~heap repr) :: .~c >.) arg_repr_s .< [] >.
    in
    textobj' repr @@ fun () -> .< apply ~kind:typematch (fun () -> .~f_c) (fun () -> .~args_c) >.
  | Pexp_lambda (args, body_repr) ->
    (* let f' = *)
    (*   .< *)
    (*   fun v_args -> *)
    (*   let heap = Hashtbl.copy .~heap in *)
    (*   let () = *)
    (*     .~( *)
    (*     match args with *)
    (*     | [] -> .< () >. *)
    (*     | args -> .< List.iter (fun (v_arg, `arg(argname, _)) -> Hashtbl.replace heap ?on_replace:.~(get_hashtbl_replace_opt ()) argname v_arg) @@ List.combine v_args args >. *)
    (*     ) in *)
    (*   .~(expr ~heap:(.<heap>.) body_repr) *)
    (*   >. *)
    (* in *)
    (* .< Lambda1.make .~f' >. *)
    failwith "lambda1 is WIP"
  | Pexp_index (receiver_repr, index_reprs) ->
    .< apply ~kind:typematch (fun () -> getattr .~(expr ~heap receiver_repr) .~(Lifts.Lift_string.lift "__getitem__")) (fun () -> .~(with_escope'' @@ fun () -> List.fold_right (fun x acc -> .< .~(expr ~heap x) :: .~acc >.) index_reprs .<[]>.)) >.
  | Pexp_list xs when is_in_escope () ->
    .< EList.make .~(List.fold_right (fun x acc -> .< .~(expr ~heap x) :: .~acc >.) xs .< [] >.) >.
  | Pexp_list el_reprs -> failwith "list expression is WIP"
  | Pexp_tuple xs ->
    (
    let rec makeit xs =
    match xs with
    | [] -> failwith "empty tuple is impossible"
    | _ :: [] -> failwith "one-element tuple is impossible"
    | [a_repr; b_repr] ->
        .<
        let a = .~(expr ~heap a_repr) in
        let b = .~(expr ~heap b_repr) in
        let typeable_a = match infer_typeable_opt a with Some x -> x | None -> failwith "MAHYQ" in
        let typeable_b = match infer_typeable_opt b with Some x -> x | None -> failwith "MAHYP" in
        let open Pyclosure in
        Typeable.extract typeable_a
        { f_typeable = fun _ arg1_extract arg1_repr arg1_type _ arg1_craft_repr -> 
          Typeable.extract typeable_b
          { f_typeable = fun _ ret_extract ret_repr ret_type _ ret_craft_repr ->
            Tuple.make arg1_type ret_type arg1_repr ret_repr arg1_craft_repr ret_craft_repr
            (
              match arg1_extract a, ret_extract b with
              | Some c1, Some c2 -> .< .~c1, .~c2 >.
              | _, _ -> failwith "MbL"
            )
          }
        }
        >.
    | a_repr :: a_s ->
        .<
        let a = .~(expr ~heap a_repr) in
        let b = .~(makeit a_s) in
        let typeable_a = match infer_typeable_opt a with Some x -> x | None -> failwith "MAHYQ" in
        let typeable_b = match infer_typeable_opt b with Some x -> x | None -> failwith "MAHYP" in
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
        >.
    in
    makeit xs
    )
  | Pexp_literal lit when is_in_escope () -> expr_elit lit
  | Pexp_literal lit -> expr_lit lit
  | Pexp_access (receiver_repr, fieldname, _) -> .< getattr .~(expr ~heap receiver_repr) fieldname >.
  | Pexp_bin { opr_left; op = `plus; opr_right } -> .< apply ~kind:typematch (fun () -> getattr .~(expr ~heap opr_left) .~(Lifts.Lift_string.lift "__add__")) (fun () -> [.~(expr ~heap opr_right)]) >.
  | _ -> failwith "unknown expression"

and expr_lit repr =
  let open Py_interp in
  match repr with
  | Plit_int c -> .< Int.make c >.
  | Plit_string c -> .< String.make c >.
  | Plit_float c -> .< Float.make c >.
  | _ -> failwith "unknown literal"

and expr_elit repr =
  let open Py_interp in
  match repr with
  | Plit_int c -> .< EInt.make .~c >.
  | _ -> failwith "unknown literal"

and textobj repr k =
  let app k =
    match k () with v -> v
    | exception Py_stdlib.Hashtbl.Tbl_not_found (requested_name, `meta (lazy (Py_interp.Closure (cl, `meta (lazy Pretextobj))))) ->
      raise  @@ Py_stdlib.Hashtbl.Tbl_not_found (requested_name, `meta (lazy (Py_interp.Closure (cl, `meta (lazy (Textobj (pexpr, repr)))))))
      (* raise exn *)
  in
  .< app @@ fun () -> .~(k ()) >.

and textobj' repr k =
  let app k =
    match k () with v -> v
    | exception Py_interp.Argument_type_mismatch_error o when o#__meta__ = Pretextobj' ->
      (
        match o#__meta__ with
        | Pretextobj' ->
          raise @@ Py_interp.Argument_type_mismatch_error (new Py_interp.argument_type_mismatch' o#argpos o#got_type_repr o#expected_type_repr (Textobj' (pexpr, repr)))
          (* raise exn *)
        | _ -> failwith "IQU"
      )
  in
  .< app @@ fun () -> .~(k ()) >.

