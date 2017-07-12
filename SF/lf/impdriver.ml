open Imp

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let tweak_string s =
  let ss = explode s in
  let rec loop = function
      [] -> EmptyString
    | h::t -> String (h, loop t)
  in loop ss;;

let test s =
  print_endline s;
  let parse_res = parse (tweak_string s) in
  (match parse_res with
    NoneE _ -> print_endline ("Syntax error");
  | SomeE (Pair (c, _)) ->
      let fuel = 1000 in
      match (ceval_step empty_state c fuel) with
        None -> print_endline ("Still running after " ^ string_of_int fuel ^ " steps")
      | Some res ->
          print_endline ("Result: [" ^ string_of_int (res 0)
                               ^ " " ^ string_of_int (res 1) 
                               ^ " " ^ string_of_int (res 2) 
                               ^ " " ^ string_of_int (res 3) 
                               ^ " ...]"));
  print_newline();
;;

test "true";;
test "SKIP";;
test "SKIP;SKIP";;
test "WHILE true DO SKIP END";;
test "x:=3";;
test "x:=3; WHILE 0<=x DO SKIP END";;
test "x:=3; WHILE 1<=x DO y:=y+1; x:=x-1 END";;
