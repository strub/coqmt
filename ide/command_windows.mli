(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: command_windows.mli 13323 2010-07-24 15:57:30Z herbelin $ i*)

class command_window :
  unit ->
  object
    method new_command : ?command:string -> ?term:string -> unit -> unit
    method frame : GBin.frame
  end

 val main : unit -> unit

val command_window : unit -> command_window


