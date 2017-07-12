type unit0 =
| Tt

val negb : bool -> bool

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val eqb : int -> int -> bool

  val leb : int -> int -> bool
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int
 end

module N :
 sig
  val add : n -> n -> n

  val mul : n -> n -> n

  val to_nat : n -> int
 end

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val n_of_digits : bool list -> n

val n_of_ascii : char -> n

val nat_of_ascii : char -> int

type string =
| EmptyString
| String of char * string

val string_dec : string -> string -> bool

val append : string -> string -> string

type id =
  string
  (* singleton inductive, whose constructor was Id *)

val beq_id : id -> id -> bool

type 'a total_map = id -> 'a

val t_empty : 'a1 -> 'a1 total_map

val t_update : 'a1 total_map -> id -> 'a1 -> id -> 'a1

type state = int total_map

val empty_state : state

type aexp =
| ANum of int
| AId of id
| APlus of aexp * aexp
| AMinus of aexp * aexp
| AMult of aexp * aexp

type bexp =
| BTrue
| BFalse
| BEq of aexp * aexp
| BLe of aexp * aexp
| BNot of bexp
| BAnd of bexp * bexp

val aeval : state -> aexp -> int

val beval : state -> bexp -> bool

type com =
| CSkip
| CAss of id * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

val ceval_step : state -> com -> int -> state option

val isWhite : char -> bool

val isLowerAlpha : char -> bool

val isAlpha : char -> bool

val isDigit : char -> bool

type chartype =
| White
| Alpha
| Digit
| Other

val classifyChar : char -> chartype

val list_of_string : string -> char list

val string_of_list : char list -> string

type token = string

val tokenize_helper : chartype -> char list -> char list -> char list list

val tokenize : string -> string list

type 'x optionE =
| SomeE of 'x
| NoneE of string

type 't parser0 = token list -> ('t, token list) prod optionE

val many_helper :
  'a1 parser0 -> 'a1 list -> int -> token list -> ('a1 list, token list) prod
  optionE

val many : 'a1 parser0 -> int -> 'a1 list parser0

val firstExpect : token -> 'a1 parser0 -> 'a1 parser0

val expect : token -> unit0 parser0

val parseIdentifier : token list -> (id, token list) prod optionE

val parseNumber : token list -> (int, token list) prod optionE

val parsePrimaryExp : int -> token list -> (aexp, token list) prod optionE

val parseProductExp : int -> token list -> (aexp, token list) prod optionE

val parseSumExp : int -> token list -> (aexp, token list) prod optionE

val parseAExp : int -> token list -> (aexp, token list) prod optionE

val parseAtomicExp : int -> token list -> (bexp, token list) prod optionE

val parseConjunctionExp : int -> token list -> (bexp, token list) prod optionE

val parseBExp : int -> token list -> (bexp, token list) prod optionE

val parseSimpleCommand : int -> token list -> (com, token list) prod optionE

val parseSequencedCommand :
  int -> token list -> (com, token list) prod optionE

val bignumber : int

val parse : string -> (com, token list) prod optionE
