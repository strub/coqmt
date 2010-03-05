(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Validate

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
let val_dp_cname = fun ?(name = "dp_cname") data ->
  val_sum name 0 [| [| val_str |] |] data

let val_dp_entry = fun ?(name = "dp_entry") data ->
  val_sum name 0
    [| [| val_cstr |] ;                 (* DPE_Constructor *)
       [| val_kn   |] ;                 (* DPE_Constant    *)
       [| val_ind  |] ; |]              (* DPE_Inductive   *)
    data

let val_dp_opbinding = fun ?(name = "dp_opbinding") ->
  let val_bsymbol = fun data ->
    let name = name ^ "_bsymbols" in
      val_tuple name [| val_dp_cname ~name; val_dp_entry ~name |] data
  in
    fun data ->
      val_tuple name
        [| val_dp_cname ~name:(name ^ "_theory")               ;
           val_id                                              ;
           val_dp_entry ~name:(name ^ "_bsort")                ;
           val_list     ~name:(name ^ "_bsymbols") val_bsymbol ; |]
        data

let val_dp_opcode = fun ?(name = "dp_opcode") data ->
  val_sum name 0
    [| [| val_dp_cname     ?name:None |];   (* DP_Load *)
       [| val_dp_opbinding ?name:None |];|] (* DP_Bind *)
    data
