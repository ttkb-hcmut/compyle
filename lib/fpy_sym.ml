type body = structure list and structure = .. and expr = .. and lit = .. 

type 't lazy_t = 't Lazy.t

type linenum = int * int

type argument = [`arg of (string * expr option)]

type structure +=
  | Pstr_assign : { lhs:string; lhs_type:(expr option); rhs:expr } -> structure
  | Pstr_eval : expr -> structure
  | Pstr_def : { funname:string; args:(argument list); rettype:(expr option); body:body; decorators:(expr list) } -> structure
  | Pstr_return : expr -> structure
  | Pstr_assert : expr -> structure
  | Pstr_dummy : structure
  | Pstr_defclass : { funname:string; args:(expr list); body:body; decorators:(expr list) } -> structure
  | Pstr_attribute : { lhs:string; lhs_type:expr } -> structure

type op = [`plus]

type expr +=
  | Pexp_var : string * [< `meta of linenum lazy_t | `nometa] -> expr
  | Pexp_fcall : expr * expr list -> expr
  | Pexp_bin : { opr_left:expr; op:op; opr_right:expr } -> expr
  | Pexp_lambda : [`arg of string * expr option] list * expr -> expr
  | Pexp_literal : lit -> expr
  | Pexp_access : expr * string * [< `meta of linenum lazy_t | `nometa] -> expr
  | Pexp_index : expr * expr list -> expr
  | Pexp_list : expr list -> expr
  | Pexp_tuple : expr list -> expr

type lit +=
  | Plit_int of int Trx.code
  | Plit_float of float Trx.code
  | Plit_string of string Trx.code
