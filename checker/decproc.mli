(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term

type cname = CName of string

type dp_entry =
  | DPE_Constructor of constructor
  | DPE_Constant    of constant
  | DPE_Inductive   of inductive

type dp_opbinding = {
  opb_theory   : cname;
  opb_name     : identifier;
  opb_bsort    : dp_entry;
  opb_bsymbols : (cname * dp_entry) list;
}

type dp_opcode =
  | DP_Load of cname
  | DP_Bind of dp_opbinding

(** {1 Binary checker} *)
val val_dp_cname     : ?name:string -> Obj.t -> unit
val val_dp_entry     : ?name:string -> Obj.t -> unit
val val_dp_opbinding : ?name:string -> Obj.t -> unit
val val_dp_opcode    : ?name:string -> Obj.t -> unit
