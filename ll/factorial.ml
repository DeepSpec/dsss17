(* We can think of the semantics of an SSA-style CFG program as a (pure)
   functional program.  Each control-flow graph is a mutually-recursive bundle
   of functions, each of which calls the others only through tail calls.

   - The 'uids' and definitions of the SSA form are simply let-bound identifiers.

   - The right-hand side of each 'let' is a non-nested 

   - [phi] functions become arguments of the basic blocks
    

  See Appel's paper: SSA _is_ Functional Programming 
*)


(* LLVM IR ------------------------------------------------------------------ *)

(*
define i64 @factorial(i64) local_unnamed_addr #0 {
  %2 = icmp sgt i64 %0, 0
  br i1 %2, label %3, label %11

; <label>:3:                                      ; preds = %1
  br label %4

; <label>:4:                                      ; preds = %3, %4
  %5 = phi i64 [ %7, %4 ], [ 1, %3 ]
  %6 = phi i64 [ %8, %4 ], [ %0, %3 ]
  %7 = mul nsw i64 %5, %6
  %8 = add nsw i64 %6, -1
  %9 = icmp sgt i64 %6, 1
  br i1 %9, label %4, label %10

; <label>:10:                                     ; preds = %4
  br label %11

; <label>:11:                                     ; preds = %10, %1
  %12 = phi i64 [ 1, %1 ], [ %7, %10 ]
  ret i64 %12
}
*)


(* Ocaml -------------------------------------------------------------------- *)

let factorial (v0:int) : int =
  let rec entry () =
    let v2 = v0 > 0 in
    if v2 then lbl3 () else lbl11 1

  and lbl3 () = lbl4 1 v0

  and lbl4 v5 v6 =          (* <--- phi "arguments" *)
    let v7 = v5 * v6 in
    let v8 = v6 - 1 in
    let v9 = v6 > 1 in
    if v9 then lbl4 v7 v8 else lbl10 v7

  and lbl10 v7 = lbl11 v7   (* <--- Note: had to provide v7 *)

  and lbl11 v12 =
    v12
  in
  entry ()
    
    
