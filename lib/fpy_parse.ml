[@@@module {%unfold|~/u/topcore/cprg|}]
[@@@module {%unfold|~/u/topcore/prgpy-sym|} [@prefixed? "prgpy-"]]
open Cprg
open Cprg.Syntax
open Sym

(** totally not a word-play of bypass *)

let reduce_left f init = function `string s -> String.fold_left f init s | `bytes bs -> Bytes.fold_left f init bs

let reduce_right f v init = match v with `string s -> String.fold_right f s init | `bytes bs -> Bytes.fold_right f bs init

let count_nl = reduce_left (fun n c -> if Char.equal c '\n' then n + 1 else n) 0

let till_prev_nl subln = (fun (st, i) -> i) @@ reduce_right (fun c (st, acc) -> match st with `running when c = '\n' -> `stopped, acc | `running -> `running, acc + 1 | `stopped -> `stopped, acc) subln (`running, 0)

type exn += Syntax_error of { linenum: int; col: int; col_range: int option }

type ctx = { ctx_tab : number }

and number = int

let number_to_int (i : number) = i

let number_increment (n : number) = n + 1

let number_init () = 0

let string s =
  String.to_seq s |> Seq.fold_left (fun acc c -> acc +> lift (fun _ -> ()) (char c)) (return ())

let ws0, ws1 =
  let whitespace = function ' ' | '\t' | '\n' -> true | _ -> false in
  let ws0 = take_while whitespace in
  let ws1 = take_while1 whitespace in
  ws0, ws1

let plus x = fix @@ fun plus ->
  lift2 List.cons x plus
  <|> lift (fun x -> [x]) x

let star x =
  (
  fix @@ fun star ->
  lift2 List.cons x star
  <|> lift (fun x -> [x]) x
  )
  <|> return []

let wrap_paren x = char '(' *> ws0 *> x <* ws0 <* char ')'

let wrap_percent x = char '%' *> ws0 *> x <* ws0 <* char '%'

let wrap_square x = char '[' *> ws0 *> x <* ws0 <* char ']'

let import_ = string "import"

let from_ = string "from"

let comma = ','

let nl = char '\n'

let tabchar = string "  "

let comma = char ','

let binop =
  lift (fun x -> [x])
    (char '+' <|> char '-' <|> char '/')
  <|> (
    let* c = char '*' in
    lift2 (fun a b -> [a; b]) (return c) (char '*')
    <|> lift (fun c -> [c]) (return c)
  )

let tab ctx =
  let c = ref None in
  let range = number_to_int ctx.ctx_tab - 1 in
  for _ = 0 to range do
    match !c with
    | None -> c := Some tabchar
    | Some cval -> c := Some (cval *> tabchar)
  done;
  Option.value ~default:(return ()) @@ Option.map (fun s -> lift ignore s) !c

let lines1 ctx content =
  let ln = lift2 (fun ts c -> c) (tab ctx) content in
  fix @@ fun lines ->
  lift2 List.cons ln (plus nl *> lines)
  <|> lift (fun x -> [x]) ln

let identifier' =
  let first_char k =
    let* c = peek_char_fail in
    match c with
    ('a' .. 'z' | 'A' .. 'Z' | '_') as c -> bind (advance 1) (fun () -> k c)
    | _ -> fail "invalid identifier" in
  let rest first_char = first_char @@ fun c ->
    take_while (function
     'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false)
    >>| function "" -> String.make 1 c | cc -> String.make 1 c ^ cc in
  first_char |> rest

let identifier =
  let* i, s' = (lift get_current_pos @@ return ()) in
  let* s = identifier' in
  match s with
  "class" | "def" | "import" ->
    let subln = match s' with `string s -> `string (String.sub s 0 i) | `bytes bs -> `bytes (Bytes.sub bs 0 i) in
    raise @@ Syntax_error { linenum = (1 + count_nl subln) ; col = (till_prev_nl subln) ; col_range = Some (String.length s) } 
  | s -> return s

let string_lit =
  let c quote =
    let* _ = char quote in
    let* content = take_while (function x when Char.equal x quote -> false | _ -> true) in
    let* () = advance 1 in
    return content
  in
  c '"' <|> c '\''

let integer =
  (
  let first_char k =
    let* c = peek_char_fail in
    match c with '1' .. '9' as c -> bind (advance 1) (fun () -> k c)
    | _ -> fail "invalid identifier" in
  let rest first_char = first_char @@ fun c ->
    take_while (function '0' .. '9' -> true | _ -> false)
    >>| (int_of_string % function "" -> String.make 1 c | cc -> String.make 1 c ^ cc) in
  first_char |> rest
  )
  <|>
  (char '0' *> return 0)

let space0, space1 =
  let whitespace = function ' ' | '\t' -> true | _ -> false in
  let ws0 = take_while whitespace in
  let ws1 = take_while1 whitespace in
  ws0, ws1

let ( *> ) a b = a *> space0 *> b

let ( <* ) a b = a <* space0 <* b

let lift2 f a b = lift2 f a (space0 *> b)

let lift3 f a b c =
  lift2 (fun (a,b) c -> f a b c) (lift2 (fun a b -> a,b) a b) c

let mklist_strict delim el = fix @@ fun arg_list ->
  lift2 List.cons (return () *> el) (delim *> arg_list)
  <|> lift (fun x -> [x]) (return () *> el)
  <|> return []

let mklist_freeform = 
  let ( *> ) a b = a *> ws0 *> b in
  (* let ( <* ) a b = a <* ws0 <* b in *)
  let lift2 f a b = lift2 f a (ws0 *> b) in
  fun delim el -> fix @@ fun arg_list ->
  lift2 List.cons (return () +> el) (delim *> arg_list)
  <|> lift (fun x -> [x]) (el)
  <|> return []

let mklist_freeform1 = 
  let ( *> ) a b = a *> ws0 *> b in
  (* let ( <* ) a b = a <* ws0 <* b in *)
  let lift2 f a b = lift2 f a (ws0 *> b) in
  fun delim el -> fix @@ fun arg_list ->
  lift2 List.cons (return () +> el) (delim *> arg_list)
  <|> lift (fun x -> [x]) (el)

let var =
  lift2
  (fun (i, s') x ->
    let meta = lazy (
      let subln = match s' with `string s -> `string (String.sub s 0 i) | `bytes bs -> `bytes (Bytes.sub bs 0 i) in
      1 + count_nl subln, till_prev_nl subln
    )
    in x, `meta meta)
  (lift get_current_pos (return ())) identifier

let with_index expr simple_expr =
  let* main = simple_expr in
  lift (fun accesses -> Pexp_index (main, accesses)) (wrap_square @@ mklist_freeform comma expr)
  <|> return main

let with_access simple_expr =
  let* main = simple_expr in
  lift (fun accesses -> List.fold_left (fun acc (x, `meta ctx) -> Pexp_access (acc, x, `meta ctx)) main accesses) (plus (char '.' *> var))
  <|> return main

let with_fcall expr simple_expr =
  let* main = simple_expr in
  lift (fun args -> Pexp_fcall (main, args)) (wrap_paren @@ mklist_freeform comma expr)
  <|> return main

let simple_expr expr : (normal, expr) code =
  with_index expr (
  with_access (
  with_fcall expr (
    lift (fun xs -> Pexp_tuple xs) (wrap_paren @@ mklist_freeform1 comma expr)
    <|> wrap_paren expr
    <|> lift (fun xs -> Pexp_list xs) (wrap_square @@ mklist_freeform comma expr)
    <|> lift (fun x -> Pexp_literal (Plit_string (Lifts.Lift_string.lift x))) string_lit
    <|> lift (fun x -> Pexp_literal (Plit_int (Lifts.Lift_int.lift x))) integer
    <|> lift (function x, ctx -> Pexp_var (x, ctx)) var
  )))

let lambda_expr expr =
  lift2 (fun args body -> args, body)
    (string "lambda" *> lift (List.map @@ fun x -> `arg (x, None)) (mklist_strict comma identifier))
    (char ':' *> expr)

let mkop = function
  | ['+'] -> `plus
  | _ -> failwith "unsupported mkop"

let expr () = fix @@ fun expr ->
  let simple_expr' = simple_expr expr in
  lift (fun (args, body) -> Pexp_lambda (args, body)) (lambda_expr expr)
  <|> lift2 (fun func args -> Pexp_fcall (func, args)) simple_expr' (wrap_paren @@ mklist_freeform comma expr)
  <|> lift3 (fun a x b -> Pexp_bin { opr_left = a; op = mkop x; opr_right = b }) simple_expr' binop simple_expr'
  <|> simple_expr'

let assign expr =
  lift3 (fun lhs typ_ rhs -> lhs, Some typ_, rhs) (identifier <* char ':') (expr <* char '=') expr
  <|> lift2 (fun lhs rhs -> lhs, None, rhs) (identifier <* char '=') expr

let attribute_decl expr =
  lift2 (fun lhs typ_ -> lhs, typ_) (identifier <* char ':') expr

let eval expr = lift (fun x -> Pstr_eval x) expr

let funcdef expr body stmt ctx =
  let arg =
    (
      let ( *> ) = Cprg.Syntax.( *> ) in
      let ( <* ) = Cprg.Syntax.( <* ) in
      let lift2  = Cprg.lift2 in
      lift2 (fun x type_ -> `arg(x, Some type_)) (identifier <* ws0 <* char ':') (ws0 *> simple_expr expr)
    )
    <|>
    lift (fun x -> `arg(x, None)) identifier
  in
  let* decorators = star (char '@' *> expr <* plus nl <+ (List.init (number_to_int ctx.ctx_tab) (fun _ -> tabchar ) |> List.fold_left (fun acc tab -> acc <* tab) (return ()) )) in
  let* funname, args, rettype =
    lift3 (fun funname args rettype -> funname, args, rettype)
      (string "def" *> identifier)
      (wrap_paren @@ mklist_freeform comma arg)
      ((lift Option.some (string "->" *> simple_expr expr)
       <|> return None) <* char ':')
  in
  (
    let ctx = { ctx_tab = number_increment ctx.ctx_tab } in
    let* _ = plus nl in
    let* body = body ctx in
    return @@ Pstr_def { funname; args; rettype; body; decorators }
  )
  <|>
  (
    let* stmt = return () *> stmt in
    return @@ Pstr_def { funname; args; rettype; body = [stmt]; decorators }
  )

let return_stmt expr =
  lift (fun x -> Pstr_return x) @@
  string "return" *> expr

let pass_stmt = string "pass" *> return ()

let assert_stmt expr = lift (fun x -> Pstr_assert x) (string "assert" *> expr)

let classdef expr body stmt ctx =
  let* decorators = star (char '@' *> expr <* plus nl <+ (List.init (number_to_int ctx.ctx_tab) (fun _ -> tabchar ) |> List.fold_left (fun acc tab -> acc <* tab) (return ()) )) in
  let* funname, args =
    lift3 (fun classname args _ -> classname, args)
      (string "class" *> identifier)
      ((wrap_paren @@ mklist_freeform comma expr) <|> return [])
      (char ':')
  in
  (
    let ctx = { ctx_tab = number_increment ctx.ctx_tab } in
    let* _ = plus nl in
    let* body = body ctx in
    return @@ Pstr_defclass { funname; args; body; decorators }
  )
  <|>
  (
    let* stmt = return () *> stmt in
    return @@ Pstr_defclass { funname; args; body = [stmt]; decorators }
  )

let stmt stmt_extensions body ctx () =
  let expr = expr () in
  fix @@ fun stmt ->
  stmt_extensions
  <|> assert_stmt expr
  <|> classdef expr (fun ctx -> body ctx) stmt ctx
  <|> lift (fun () -> Pstr_dummy) pass_stmt
  <|> funcdef expr (fun ctx -> body ctx) stmt ctx
  <|> return_stmt expr
  <|> lift (fun (lhs, lhs_type, rhs) -> Pstr_assign { lhs; lhs_type; rhs }) (assign expr)
  <|> lift (fun (lhs, lhs_type) -> Pstr_attribute { lhs; lhs_type }) (attribute_decl expr)
  <|> eval expr

let rec body stmt_extensions ctx () =
  let repeat = (fun ctx -> body stmt_extensions ctx ()) in
  lines1 ctx (stmt stmt_extensions repeat ctx ())

let program stmt_extensions ctx () = body stmt_extensions ctx ()

let langchain stmt_extensions () =
  let ctx = { ctx_tab = number_init () } in
  ws0 *> program stmt_extensions ctx () <* ws0 <* (
    let* i, s' = (lift get_current_pos @@ return ()) in
    let subln = match s' with `string s -> `string (String.sub s 0 i) | `bytes bs -> `bytes (Bytes.sub bs 0 i) in
    end_of_input <|> lift (fun () -> raise @@ Syntax_error { linenum = (1 + count_nl subln) ; col = (till_prev_nl subln) ; col_range = None }) (return ()) 
  )

let comment =
  let open Re in
  seq [alt [char ' '; char '\t'] |> rep |> longest; char '#'; any |> rep |> shortest; group (char '\n')]

let remove_all_exceptsuffix pat =
  Re.replace ~all:true pat ~f:(fun g -> Re.Group.get g 1)

(*

type effect_handle = Effect_handle { parents : tracer list; recipe : jaxpr_eqn_recipe }

class [@pydoc "[partial_val] is either a known value or an unknown (abstract) value.

Represented as a pair :
{ - [(none, <Constant>)] indicates }
  "]
  partial_val (xs : (abstract_value option * Core.value)) =
  object (self) inherit tuple

  method is_known : bool =
    self#at 0 = none

  end

module Partial_val =
  struct

  let known (const : Core.value) : partial_val =
    new partial_val (none, const)

  end

let _ =
  .< 
    let [@comment " TODO(dougalm): remove in favor of [trace_to_jaxpr]"]
      trace_to_jaxpr_dynamic =
      Profiler.annotate_function @@ fun
        ?keep_inputs:(keep_inputs:bool list)
        ?lower:(lower:bool = false_)
        ?auto_dce:(auto_dce:bool = false_)
        (fun_ : Lu.wrapped_fn)
        (in_avals : abstract_value sequence)
        : (jaxpr * abstract_value list * any list)
    ->
      assert (Config.enable_checks#value && fun_#debug_info#assert_arg_names (len in_avals));
      let keep_inputs = List.init (len in_avals) (fun _ -> true_) in
      let parent_trace = Core.Trace_ctx.trace in
      let trace = new dynamic_jaxpr_trace ~parent_trace ~lower ~auto_dce fun_#debug_info in
      let jaxpr =
        Core.ensure_no_leaks trace @@ fun () ->
        Source_info_util.reset_name_stack () @@ fun () ->
        trackback_scope () @@ fun () ->
        let jaxpr, consts = trace#frame#to_jaxpr trace out_tracers fun_#debug_info source_info in
        Object.del' [trace, fun_, in_tracers, out_tracers, ans];
        jaxpr in
      assert (Config.enable_checks#value && Core.check_jaxpr jaxpr);
      jaxpr, (List.map (fun v -> v#aval) jaxpr#outvars), consts
    in
    ()
  >.

let _ = 
  .<
    let cls = Oo.Class.decl () in
    let process_custom_vjp_call self =
    .< fun ~out_trees ~symbolic_zeros prim f fwd bwd tracers ->
      let tracers = List.map self#to_jaxpr_tracer tracers in
      if List.for_all (fun t -> t#is_known ()) tracers then
        let vals = List.map (fun t -> Pair.snd t.pval) tracers in
        Core.set_current_trace self#parent_trace @@ fun () ->
        prim#bind vals ~subfuns:(f, fwd, bwd) ~out_trees ~symbolic_zeros
      else (
      let tracers = List.map self#instantiate_const tracers in
      assert (not @@ any out_knowns);
      let res_tracers_4 = List.map self#instantiate_const @@ List.map self#new_const @@ res in
      let out_tracers_4 = List.map (fun a ->
        new jaxpr_tracer_4 self (Partial_val.unknown a) None) out_avals in
      let closed_jaxpr_1 = convert_constvars_jaxpr_1 jaxpr in
      let fwd_jaxpr_thunk_20 =
        partial_2 Lu.wrap_init ~debug_info:fwd#debug_info @@
        _memoize_2 @@
        fun [%vararg? zeros_1] ->
        let fwd__2 = _interleave_fun_1 (fwd#with_unknown_name_2 ()) zeros_1#all in
        let fwd_jaxpr_9, _, consts_9 = trace_9 in
        fwd_jaxpr_9, consts_9 in
      let name_space = self#_current_truncated_name_stack () in
      let source = Source_info_util.current () in
      let params = {
        call_jaxpr = closed_jaxpr;
        fwd_jaxpr_thunk;
        num_consts = List.length res + List.length env;
        bwd; out_trees; symbolic_zeros
      } in
      let eqn = new_eqn_recipe self in
      List.iter (fun t -> t.recipe <- eqn) out_tracers;
      out_tracers
      )
    >.
    in
    Oo.Class.register_method cls process_custom_vjp_call;
    Oo.Class.finish cls
  >.

let _ =
  .< 
    let rec [@doc {%ocamldoc|
      [dce_jaxpr] runs dead-code elementation on a given jaxpr.

      @param {jaxpr} The jaxpr to DCE.
      @param {used\_outputs} A list
      @return A tuple of [(new_jaxpr * used_inputs)].
    |}]
      dce_jaxpr
      (jaxpr : jaxpr) (used_outputs : (bool, bool sequence) either)
      ?instantiate:(instantiate:(bool, bool sequence) either = Left false_)
      : (jaxpr * bool list)
    =
      let used_outputs = Either.map_left (fun used_outputs ->
        List.init (List.length jaxpr#outvars) (fun _ -> used_outputs, ())) used_outputs in
      let instantiate = Either.map_left (fun instantiate ->
        List.init (List.length jaxpr#invars) (fun _ -> instantiate, ())) instantiate in
      _dce_jaxpr jaxpr used_outputs instantiate

    and dce_jaxpr_closed_call_rule
      (used_outputs : bool list) (eqn : jaxpr_eqn)
      : (bool list * jaxpr_eqn option)
    =
      if (not @@ any used_outputs) && (not @@ has_effects eqn) then
        List.init (List.length eqn#invars) (fun _ -> false_), None
      else
      let jaxpr_ = eqn#params.call_jaxpr in
      let closed_jaxpr, used_inputs = _cached_closed_call_dce jaxpr_ used_outputs in
      let new_invars = List.filter_map (function v, (true as used) -> Some v | _ -> None) @@ List.combine eqn#invars used_inputs in
      let effects = Core.eqn_effects closed_jaxpr new_invars in
      let new_params = { eqn#params with call_japxr = closed_jaxpr } in
      let new_eqn = new_jaxpr_eqn new_invars
        (List.filter_map (function v, (true as used) -> Some v | _ -> None) @@ List.combine eqn#outvars used_outputs)
        eqn#primitive new_params effects eqn#source_info eqn#ctx
      in
      used_inputs, new_eqn

    in ()
  >.

let _ ~dce_jaxpr =
  .<
    let _cached_closed_call_dce =
      weakref_lru_cache @@ fun
        jaxpr_ (used_outputs : (bool * 't))
        : (jaxpr * bool list)
    ->
      dce_jaxpr jaxpr_ used_outputs

    in ()
  >.

class awe =
  object (self) inherit some_ as super
  val foo = foo self
  val bar = bar self
  method foo = foo
  method bar = bar
  end

*)

