(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Interpreting CompCert C sources: emulating external function calls *)

open !Format
open Camlcoq
open AST
open Integers
open Values
open Memimpl
open Globalenvs
open Events
open !Ctypes
open !Csyntax

(* Extract a string from a global pointer *)

let extract_string m blk ofs =
  let b = Buffer.create 80 in
  let rec extract blk ofs =
    match Mem.load Mint8unsigned m blk ofs with
    | Some(Vint n) ->
        let c = Char.chr (Z.to_int n) in
        if c = '\000' then begin
          Some(Buffer.contents b)
        end else begin
          Buffer.add_char b c;
          extract blk (Z.succ ofs)
        end
    | _ ->
        None in
  extract blk ofs

(* Emulation of printf *)

(* All ISO C 99 formats *)

let re_conversion = Str.regexp (
  "\\(%[-+0# ]*[0-9]*\\(\\.[0-9]*\\)?\\)" (* group 1: flags, width, precision *)
^ "\\(\\|[lhjztL]\\|hh\\|ll\\)"            (* group 3: length modifier *)
^ "\\([aAcdeEfgGinopsuxX%]\\)"            (* group 4: conversion specifier *)
)

external format_float: string -> float -> string
  = "caml_format_float"
external format_int32: string -> int32 -> string
  = "caml_int32_format"
external format_int64: string -> int64 -> string
  = "caml_int64_format"

let format_value m flags length conv arg =
  match conv.[0], length, arg with
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), Vint i ->
      format_int32 (flags ^ conv) (camlint_of_coqint i)
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), _ ->
      "<int argument expected>"
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), Vlong i ->
       format_int64 (flags ^ conv) (camlint64_of_coqint i)
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), _ ->
      "<long long argument expected"
  | ('f'|'e'|'E'|'g'|'G'|'a'), (""|"l"), Vfloat f ->
      format_float (flags ^ conv) (camlfloat_of_coqfloat f)
  | ('f'|'e'|'E'|'g'|'G'|'a'), "", _ ->
      "<float argument expected"
  | 's', "", Vptr(blk, ofs) ->
      begin match extract_string m blk ofs with
      | Some s -> s
      | None -> "<bad string>"
      end
  | 's', "", _ ->
      "<pointer argument expected>"
  | 'p', "", Vptr(blk, ofs) ->
      Printf.sprintf "<%ld%+ld>" (P.to_int32 blk) (camlint_of_coqint ofs)
  | 'p', "", Vint i ->
      format_int32 (flags ^ "x") (camlint_of_coqint i)
  | 'p', "", _ ->
      "<int or pointer argument expected>"
  | _, _, _ ->
      "<unrecognized format>"

let do_printf m fmt args =

  let b = Buffer.create 80 in
  let len = String.length fmt in

  let opt_search_forward pos =
    try Some(Str.search_forward re_conversion fmt pos)
    with Not_found -> None in

  let rec scan pos args =
    if pos < len then begin
    match opt_search_forward pos with
    | None ->
        Buffer.add_substring b fmt pos (len - pos)
    | Some pos1 ->
        Buffer.add_substring b fmt pos (pos1 - pos);
        let flags = Str.matched_group 1 fmt
        and length = Str.matched_group 3 fmt
        and conv = Str.matched_group 4 fmt
        and pos' = Str.match_end() in
        if conv = "%" then begin
          Buffer.add_char b '%';
          scan pos' args
        end else begin
          match args with
          | [] ->
              Buffer.add_string b "<missing argument>";
              scan pos' []
          | arg :: args' ->
              Buffer.add_string b (format_value m flags length conv arg);
              scan pos' args'
        end
    end
  in scan 0 args; Buffer.contents b

(* Implementation of external functions *)

let (>>=) opt f = match opt with None -> None | Some arg -> f arg

(* Like eventval_of_val, but accepts static globals as well *)
let convert_external_arg ge v t =
  match v with
  | Vint i -> Some (EVint i)
  | Vfloat f -> Some (EVfloat f)
  | Vsingle f -> Some (EVsingle f)
  | Vlong n -> Some (EVlong n)
  | Vptr(b, ofs) ->
      Senv.invert_symbol ge b >>= fun id -> Some (EVptr_global(id, ofs))
  | _ -> None

let rec convert_external_args ge vl tl =
  match vl, tl with
  | [], [] -> Some []
  | v1::vl, t1::tl ->
      convert_external_arg ge v1 t1 >>= fun e1 ->
      convert_external_args ge vl tl >>= fun el -> Some (e1 :: el)
  | _, _ -> None

let do_external_function id sg ge w args m =
 match camlstring_of_coqstring id, args with
  | "printf", Vptr(b, ofs) :: args' ->
      extract_string m b ofs >>= fun fmt ->
      let fmt' = do_printf m fmt args' in
      let len = coqint_of_camlint (Int32.of_int (String.length fmt')) in
      Format.print_string fmt';
      flush stdout;
      convert_external_args ge args sg.sig_args >>= fun eargs ->
      Some(((w, [Event_syscall(id, eargs, EVint len)]), Vint len), m)
  | _ ->
      None
