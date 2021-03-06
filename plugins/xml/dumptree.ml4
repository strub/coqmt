(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module provides the "Dump Tree" command that allows dumping the
    current state of the proof stree in XML format *)

(** Contributed by Cezary Kaliszyk, Radboud University Nijmegen *)

(*i camlp4deps: "parsing/grammar.cma" i*)
open Tacexpr;;
open Decl_mode;;
open Printer;;
open Pp;;
open Environ;;
open Format;;
open Proof_type;;
open Evd;;
open Termops;;
open Ppconstr;;
open Names;;

exception Different

let xmlstream s =
  (* In XML we want to print the whole stream so we can force the evaluation *)
  Stream.of_list (List.map xmlescape (Stream.npeek max_int s))
;;

let thin_sign osign sign =
  Sign.fold_named_context
    (fun (id,c,ty as d) sign ->
       try
        if Sign.lookup_named id osign = (id,c,ty) then sign
         else raise Different
       with Not_found | Different -> Environ.push_named_context_val d sign)
    sign ~init:Environ.empty_named_context_val
;;

let pr_tactic_xml = function
  | TacArg (Tacexp t) -> str "<tactic cmd=\"" ++ xmlstream (Pptactic.pr_glob_tactic (Global.env()) t) ++ str "\"/>"
  | t -> str "<tactic cmd=\"" ++ xmlstream (Pptactic.pr_tactic (Global.env()) t) ++ str "\"/>"
;;

let pr_proof_instr_xml instr =
  Ppdecl_proof.pr_proof_instr (Global.env()) instr
;;

let pr_rule_xml pr = function
  | Prim r -> str "<rule text=\"" ++ xmlstream (pr_prim_rule r) ++ str "\"/>"
  | Nested(cmpd, subtree) ->
      hov 2 (str "<cmpdrule>" ++ fnl () ++
        begin match cmpd with
          Tactic (texp, _) -> pr_tactic_xml texp
        | Proof_instr (_,instr) -> pr_proof_instr_xml instr
        end ++ fnl ()
        ++ pr subtree
      ) ++ fnl () ++ str "</cmpdrule>"
  | Daimon -> str "<daimon/>"
  | Decl_proof _ -> str "<proof/>"
(*  | Change_evars -> str "<chgevars/>"*)
;;

let pr_var_decl_xml env (id,c,typ) =
  let ptyp = print_constr_env env typ in
  match c with
  | None ->
      (str "<hyp id=\"" ++ xmlstream (pr_id id) ++ str "\" type=\"" ++ xmlstream ptyp ++ str "\"/>")
  | Some c ->
      (* Force evaluation *)
      let pb = print_constr_env env c in
      (str "<hyp id=\"" ++ xmlstream (pr_id id) ++ str "\" type=\"" ++ xmlstream ptyp ++ str "\" body=\"" ++
         xmlstream pb ++ str "\"/>")
;;

let pr_rel_decl_xml env (na,c,typ) =
  let pbody = match c with
    | None -> mt ()
    | Some c ->
	(* Force evaluation *)
	let pb = print_constr_env env c in
	  (str" body=\"" ++ xmlstream pb ++ str "\"") in
  let ptyp = print_constr_env env typ in
  let pid =
    match na with
    | Anonymous -> mt ()
    | Name id -> str " id=\"" ++ pr_id id ++ str "\""
  in
  (str "<hyp" ++ pid ++ str " type=\"" ++ xmlstream ptyp ++ str "\"" ++ pbody ++ str "/>")
;;

let pr_context_xml env =
  let sign_env =
    fold_named_context
      (fun env d pp -> pp ++ pr_var_decl_xml env d)
      env ~init:(mt ())
  in
  let db_env =
    fold_rel_context
      (fun env d pp -> pp ++ pr_rel_decl_xml env d)
      env ~init:(mt ())
  in
  (sign_env ++ db_env)
;;

let pr_subgoal_metas_xml metas env=
  let pr_one (meta, typ) =
    fnl () ++ str "<meta index=\"" ++ int meta ++ str " type=\"" ++ xmlstream (pr_ltype_env_at_top env typ) ++
      str "\"/>"
  in
  List.fold_left (++) (mt ()) (List.map pr_one metas)
;;

let pr_goal_xml g =
  let env = try evar_unfiltered_env g with _ -> empty_env in
  if g.evar_extra = None then
    (hov 2 (str "<goal>" ++ fnl () ++ str "<concl type=\"" ++
    xmlstream (pr_ltype_env_at_top env g.evar_concl) ++
    str "\"/>" ++
    (pr_context_xml env)) ++
    fnl () ++ str "</goal>")
  else
    (hov 2 (str "<goal type=\"declarative\">" ++
    (pr_context_xml env)) ++
    fnl () ++ str "</goal>")
;;

let rec print_proof_xml sigma osign pf =
  let hyps = Environ.named_context_of_val pf.goal.evar_hyps in
  let hyps' = thin_sign osign hyps in
  match pf.ref with
    | None -> hov 2 (str "<tree>" ++ fnl () ++ (pr_goal_xml {pf.goal with evar_hyps=hyps'})) ++ fnl () ++ str "</tree>"
    | Some(r,spfl) ->
        hov 2 (str "<tree>" ++ fnl () ++
        (pr_goal_xml {pf.goal with evar_hyps=hyps'}) ++ fnl () ++ (pr_rule_xml (print_proof_xml sigma osign) r) ++
        (List.fold_left (fun x y -> x ++ fnl () ++ y) (mt ()) (List.map (print_proof_xml sigma hyps) spfl))) ++ fnl () ++ str "</tree>"
;;

let print_proof_xml () =
  let pp = print_proof_xml Evd.empty Sign.empty_named_context
      (Tacmach.proof_of_pftreestate (Refiner.top_of_tree (Pfedit.get_pftreestate ())))
  in
  msgnl pp
;;

VERNAC COMMAND EXTEND DumpTree
  [ "Dump" "Tree" ] -> [ print_proof_xml () ]
END
