type peano = Z | S of peano

val peano_of_int: int -> peano
val int_of_peano: peano -> int

val inc: peano -> peano
val add: peano -> peano -> peano
val sub: peano -> peano -> peano
val mul: peano -> peano -> peano
val power: peano -> peano -> peano

val rev: 'a list -> 'a list
val merge_sort: 'a list -> 'a list

type lambda = Var of string | Abs of string * lambda | App of lambda * lambda

val string_of_lambda: lambda -> string
val lambda_of_string: string -> lambda

val string_of_char: char -> string
val fail_char: string -> int -> char -> lambda * int
val helper_parse_var: string -> int -> bool -> int
val parse_var: string -> int -> lambda * int
val parse_arg: string -> int -> lambda * int
val helper_parse_app: lambda -> string -> int -> lambda * int
val parse_app: string -> int -> lambda * int
val get_var: lambda -> string

val println_string: string -> unit
val println_int: int -> unit

val merge: 'a list -> 'a list -> 'a list 


val split: 'a list -> int -> 'a list * 'a list
