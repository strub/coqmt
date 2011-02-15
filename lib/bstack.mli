(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: bstack.mli 13323 2010-07-24 15:57:30Z herbelin $ i*)

(* Bounded stacks. If the depth is [None], then there is no depth limit. *)

type 'a t

val create : int -> 'a -> 'a t
val push : 'a t -> 'a -> unit
val app_push : 'a t -> ('a -> 'a) -> unit
val app_repl : 'a t -> ('a -> 'a) -> unit
val pop : 'a t -> unit
val top : 'a t -> 'a
val depth : 'a t -> int
val size : 'a t -> int
