(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: usage.mli 13323 2010-07-24 15:57:30Z herbelin $ i*)

(*s Prints the version number on the standard output and exits (with 0). *)

val version : unit -> 'a

(*s Prints the usage on the error output, preceeded by a user-provided message. *)
val print_usage : string -> unit

(*s Prints the usage on the error output. *)
val print_usage_coqtop : unit -> unit
val print_usage_coqc : unit -> unit

(*s Prints the configuration information *)
val print_config : unit -> unit
