(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: reduction.ml 11897 2009-02-09 19:28:02Z barras $ *)

open Util
open Names
open Term
open Univ
open Declarations
open Environ
open Closure
open Esubst

type infos_t = {
  if_ids      : Names.Idpred.t;
  if_csts     : Names.Cpred.t;
  if_closure  : Closure.clos_infos;
  if_bindings : Decproc.Bindings.t;
}

let unfold_reference = fun infos k ->
  match k with
  | VarKey   id  when not (Idpred.mem id  infos.if_ids ) -> None
  | ConstKey cst when not (Cpred.mem  cst infos.if_csts) -> None
  | _ -> unfold_reference infos.if_closure k
	  
let rec is_empty_stack = function
    [] -> true
  | Zupdate _::s -> is_empty_stack s
  | Zshift _::s -> is_empty_stack s
  | _ -> false

(* Compute the lift to be performed on a term placed in a given stack *)
let el_stack el stk =
  let n =
    List.fold_left
      (fun i z ->
        match z with
            Zshift n -> i+n
          | _ -> i)
      0
      stk in
  el_shft n el

let compare_stack_shape stk1 stk2 =
  let rec compare_rec bal stk1 stk2 =
  match (stk1,stk2) with
      ([],[]) -> bal=0
    | ((Zupdate _|Zshift _)::s1, _) -> compare_rec bal s1 stk2
    | (_, (Zupdate _|Zshift _)::s2) -> compare_rec bal stk1 s2
    | (Zapp l1::s1, _) -> compare_rec (bal+Array.length l1) s1 stk2
    | (_, Zapp l2::s2) -> compare_rec (bal-Array.length l2) stk1 s2
    | (Zcase(c1,_,_)::s1, Zcase(c2,_,_)::s2) ->
        bal=0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
    | (Zfix(_,a1)::s1, Zfix(_,a2)::s2) ->
        bal=0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
    | (_,_) -> false in
  compare_rec 0 stk1 stk2

type lft_constr_stack_elt =
    Zlapp of (lift * fconstr) array
  | Zlfix of (lift * fconstr) * lft_constr_stack
  | Zlcase of case_info * lift * fconstr * fconstr array
and lft_constr_stack = lft_constr_stack_elt list

let rec zlapp v = function
    Zlapp v2 :: s -> zlapp (Array.append v v2) s
  | s -> Zlapp v :: s

let pure_stack lfts stk =
  let rec pure_rec lfts stk =
    match stk with
        [] -> (lfts,[])
      | zi::s ->
          (match (zi,pure_rec lfts s) with
              (Zupdate _,lpstk)  -> lpstk
            | (Zshift n,(l,pstk)) -> (el_shft n l, pstk)
            | (Zapp a, (l,pstk)) ->
                (l,zlapp (Array.map (fun t -> (l,t)) a) pstk)
            | (Zfix(fx,a),(l,pstk)) ->
                let (lfx,pa) = pure_rec l a in
                (l, Zlfix((lfx,fx),pa)::pstk)
            | (Zcase(ci,p,br),(l,pstk)) ->
                (l,Zlcase(ci,l,p,br)::pstk)) in
  snd (pure_rec lfts stk)

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

let nf_betaiota t =
  norm_val (create_clos_infos betaiota empty_env) (inject t)

let whd_betaiotazeta x =
  match kind_of_term x with
    | (Sort _|Var _|Meta _|Evar _|Const _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> x
    | _ -> whd_val (create_clos_infos betaiotazeta empty_env) (inject x)

let whd_betadeltaiota env t = 
  match kind_of_term t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> t
    | _ -> whd_val (create_clos_infos betadeltaiota env) (inject t)

let whd_betadeltaiota_nolet env t = 
  match kind_of_term t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|LetIn _) -> t
    | _ -> whd_val (create_clos_infos betadeltaiotanolet env) (inject t)

(* Beta *)

let beta_appvect c v =
  let rec stacklam env t stack =
    match kind_of_term t, stack with
        Lambda(_,_,c), arg::stacktl -> stacklam (arg::env) c stacktl
      | _ -> applist (substl env t, stack) in
  stacklam [] c (Array.to_list v)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)
type 'a conversion_function = env -> 'a -> 'a -> Univ.constraints
type 'a trans_conversion_function = transparent_state -> env -> 'a -> 'a -> Univ.constraints

exception NotConvertible
exception NotConvertibleVect of int

let compare_stacks f fmind lft1 stk1 lft2 stk2 cuniv =
  let rec cmp_rec pstk1 pstk2 cuniv =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          let cu1 = cmp_rec s1 s2 cuniv in
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) -> array_fold_right2 f a1 a2 cu1
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                let cu2 = f fx1 fx2 cu1 in
                cmp_rec a1 a2 cu2
            | (Zlcase(ci1,l1,p1,br1),Zlcase(ci2,l2,p2,br2)) ->
                if not (fmind ci1.ci_ind ci2.ci_ind) then
		  raise NotConvertible;
		let cu2 = f (l1,p1) (l2,p2) cu1 in
                array_fold_right2 (fun c1 c2 -> f (l1,c1) (l2,c2)) br1 br2 cu2
            | _ -> assert false)
      | _ -> cuniv in
  if compare_stack_shape stk1 stk2 then
    cmp_rec (pure_stack lft1 stk1) (pure_stack lft2 stk2) cuniv
  else raise NotConvertible

(* Convertibility of sorts *)

(* The sort cumulativity is

    Prop <= Set <= Type 1 <= ... <= Type i <= ...

    and this holds whatever Set is predicative or impredicative
*)

type conv_pb = 
  | CONV 
  | CUMUL

let sort_cmp pb s0 s1 cuniv =
  match (s0,s1) with
    | (Prop c1, Prop c2) ->
        if c1 = Null or c2 = Pos then cuniv   (* Prop <= Set *)
        else raise NotConvertible
    | (Prop c1, Type u) when pb = CUMUL -> assert (is_univ_variable u); cuniv
    | (Type u1, Type u2) ->
	assert (is_univ_variable u2);
	(match pb with
           | CONV -> enforce_eq u1 u2 cuniv
	   | CUMUL -> enforce_geq u2 u1 cuniv)
    | (_, _) -> raise NotConvertible


let conv_sort env s0 s1 = sort_cmp CONV s0 s1 Constraint.empty

let conv_sort_leq env s0 s1 = sort_cmp CUMUL s0 s1 Constraint.empty

let rec no_arg_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_arg_available stk
  | Zshift _ :: stk -> no_arg_available stk
  | Zapp v :: stk -> Array.length v = 0 && no_arg_available stk
  | Zcase _ :: _ -> true
  | Zfix _ :: _ -> true

let rec no_nth_arg_available n = function
  | [] -> true
  | Zupdate _ :: stk -> no_nth_arg_available n stk
  | Zshift _ :: stk -> no_nth_arg_available n stk
  | Zapp v :: stk ->
      let k = Array.length v in
      if n >= k then no_nth_arg_available (n-k) stk
      else false
  | Zcase _ :: _ -> true
  | Zfix _ :: _ -> true

let rec no_case_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_case_available stk
  | Zshift _ :: stk -> no_case_available stk
  | Zapp _ :: stk -> no_case_available stk
  | Zcase _ :: _ -> false
  | Zfix _ :: _ -> true

let in_whnf (t,stk) =
  match fterm_of t with
    | (FLetIn _ | FCases _ | FApp _ | FCLOS _ | FLIFT _ | FCast _) -> false
    | FLambda _ -> no_arg_available stk
    | FConstruct _ -> no_case_available stk
    | FCoFix _ -> no_case_available stk
    | FFix(((ri,n),(_,_,_)),_) -> no_nth_arg_available ri.(n) stk
    | (FFlex _ | FProd _ | FEvar _ | FInd _ | FAtom _ | FRel _) -> true
    | FLOCKED -> assert false

(* Head reduce a couple of terms. This is not equivalent to reducing
 * the first, and then the second term since we have terms sharing.
 *)
let whd_both infos =
  let rec whd_both = fun (t1, stk1) (t2, stk2) ->
    let st1 = whd_stack infos.if_closure t1 stk1 in
    let st2 = whd_stack infos.if_closure t2 stk2 in
      (* Now, whd_stack on second term might have modified st1 (due to
       * sharing), and st1 might not be in whnf anymore.
       *)
      if in_whnf st1 then (st1, st2) else whd_both st1 st2
  in
    whd_both

(* Decision procedures conversion module *)
module DP : sig
  open Decproc

  type state_t

  type xfconstr_t = lift * fconstr * stack
  type xcnv_t     = xfconstr_t -> xfconstr_t -> Univ.constraints -> Univ.constraints

  exception ExtractFailure

  val create   : Bindings.t -> state_t
  val extract  : state_t -> clos_infos -> xfconstr_t -> state_t

  val finalize
    :  xcnv_t
    -> Univ.constraints
    -> state_t
    -> FOTerm.term array * dpinfos * Univ.constraints
end
  =
struct
  open Decproc

  type xfconstr_t = lift * fconstr * stack
  type xcnv_t     = xfconstr_t -> xfconstr_t -> Univ.constraints -> Univ.constraints

  type prefoterm =
    | PFO_Var   of identifier
    | PFO_Rel   of int
    | PFO_Alien of xfconstr_t
    | PFO_Symb  of FOTerm.symbol * prefoterm array

  type state_t = {
    st_bindings : Bindings.t;
    st_theory   : dpinfos option;
    st_terms    : prefoterm list;
  }

  exception ExtractFailure

  let create = fun bindings -> {
    st_bindings = bindings;
    st_theory   = None;
    st_terms    = [];
  }

  exception AlienNotMerged

  let finalize = fun cnv ->
    let rec to_foterm_fold = fun term (aliens, foterms) ->
      let aliens, foterm = to_foterm aliens term in
        (aliens, foterm :: foterms)

    and to_foterm = fun ((cuniv, aliens) as infos) term ->
      match term with
      | PFO_Var x -> (infos, FOTerm.FVar (`Out x))
      | PFO_Rel n -> (infos, FOTerm.FVar (`In n))
      | PFO_Symb (f, ts) ->
          let infos, foterms =
            Array.fold_right to_foterm_fold ts (infos, [])
          in
            (infos, FOTerm.FSymb (f, foterms))

      | PFO_Alien term ->               (* FIXME *)
          let rec merge = fun i aliens ->
            match aliens with
            | [] -> raise AlienNotMerged
            | alien :: aliens ->
                try
                  let cuniv = cnv term alien cuniv in
                    ((cuniv, aliens), FOTerm.FVar (`Alien i))
                with NotConvertible ->
                  merge (i+1) aliens
          in
            try  merge 0 aliens
            with AlienNotMerged ->
              let naliens = List.length aliens in
                ((cuniv, aliens @ [term]), FOTerm.FVar (`Alien naliens))

    in
      fun cuniv state ->
        match state.st_theory with
        | None        -> raise ExtractFailure
        | Some theory ->
            let (cuniv, _), foterms =
              List.fold_right to_foterm_fold state.st_terms ((cuniv, []), [])
            in
              (Array.of_list foterms, theory, cuniv)
  
  let extract = fun state ->
    let entry_of_fterm = function
      | FFlex (ConstKey x) -> Some (Decproc.DPE_Constant    x)
      | FConstruct x       -> Some (Decproc.DPE_Constructor x)
      | FInd x             -> Some (Decproc.DPE_Inductive   x)
      | _                  -> None
  
    and merge_theory = fun th1 th2 ->
      match th1 with
      | None                             -> th2
      | Some th1 when th1 ==(*\phi*) th2 -> th1
      | _                                -> raise ExtractFailure
    in
  
    let rec extract_r = fun theory closure (lift, term, stack) ->
      let (term, stack) = whd_stack closure term stack in
      let el_lift       = el_stack lift stack in
        match entry_of_fterm (fterm_of term) with
        | None -> begin
            match fterm_of term with
            | FFlex (VarKey x) -> (PFO_Var x, theory)
            | FRel n           -> (PFO_Rel (reloc_rel n el_lift), theory) (* ?? *)
            | _                -> (PFO_Alien (lift, term, stack), theory) (* ?? *)
          end
  
        | Some entry -> begin
            match Bindings.revbinding_symbol state.st_bindings entry with
            | None            -> (PFO_Alien (lift, term, stack), theory)
            | Some (bd, symb) ->
                let theory = merge_theory theory bd.dpb_theory in
                  match pure_stack lift stack with
                  | [ Zlapp args ] -> begin
                      if Array.length args <> symb.FOTerm.s_arity then
                        raise ExtractFailure;
                      let foargs =
                        Array.map
                          (fun (alift, arg) ->
                             (fst (extract_r (Some theory) closure (alift, arg, []))))
                          args
                      in
                        (PFO_Symb (symb, foargs), Some theory)
                    end
                  | _ -> assert false
          end
    in
      fun closure xfconstr ->
        let foterm, theory = extract_r state.st_theory closure xfconstr in
          { state with
              st_terms  = foterm :: state.st_terms;
              st_theory = theory; }
end
  
(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb infos lft1 lft2 term1 term2 cuniv = 
  eqappr cv_pb infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv

(* Conversion between [lft1](hd1 st1) and [lft2](hd2 st2),
 * possibly using first-order decision procedures. *)
and eqappr cv_pb infos ((lft1, st1) as t1) ((lft2, st2) as t2) cuniv =
  try
    let foterms, theory, cuniv =
      try
        let state =
          List.fold_left
            (fun state (lft, st) ->
               DP.extract state infos.if_closure (lft, fst st, snd st))
            (DP.create infos.if_bindings)
            [ t1; t2 ]
        in
          DP.finalize
            (fun (lft1, t1, st1) (lft2, t2, st2) c ->
               eqappr CONV infos (lft1, (t1, st2)) (lft2, (t2, st2)) c)
            cuniv state
      with DP.ExtractFailure ->
        raise NotConvertible
    in
      if not (theory.Decproc.dpi_blackbox (foterms.(0), foterms.(1))) then
        raise NotConvertible;
      cuniv
  with NotConvertible ->
    eqappr_noalg cv_pb infos (lft1, st1) (lft2, st2) cuniv

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr_noalg cv_pb infos (lft1,st1) (lft2,st2) cuniv =
  Util.check_for_interrupt ();

  (* First head reduce both terms *)
  let ((hd1, v1), (hd2, v2)) = whd_both infos st1 st2 in
  let appr1 = (lft1, (hd1, v1)) and appr2 = (lft2, (hd2, v2)) in

  (* compute the lifts that apply to the head of the term (hd1 and hd2) *)
  let el1 = el_stack lft1 v1 in
  let el2 = el_stack lft2 v2 in

  match (fterm_of hd1, fterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
	(match kind_of_term a1, kind_of_term a2 with
	   | (Sort s1, Sort s2) -> 
	       assert (is_empty_stack v1 && is_empty_stack v2);
	       sort_cmp cv_pb s1 s2 cuniv
	   | (Meta n, Meta m) ->
               if n=m
	       then convert_stacks infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
	   | _ -> raise NotConvertible)
    | (FEvar ((ev1,args1),env1), FEvar ((ev2,args2),env2)) ->
        if ev1=ev2 then
          let u1 = convert_stacks infos lft1 lft2 v1 v2 cuniv in
          convert_vect infos el1 el2
            (Array.map (mk_clos env1) args1)
            (Array.map (mk_clos env2) args2) u1
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        if reloc_rel n el1 = reloc_rel m el2
        then convert_stacks infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
	(try (* try first intensional equality *)
	  if fl1 = fl2
          then convert_stacks infos lft1 lft2 v1 v2 cuniv
          else raise NotConvertible
        with NotConvertible ->
          (* else the oracle tells which constant is to be expanded *)
          let (app1,app2) =
            if Conv_oracle.oracle_order fl1 fl2 then
              match unfold_reference infos fl1 with
                | Some def1 -> ((lft1, whd_stack infos.if_closure def1 v1), appr2)
                | None ->
                    (match unfold_reference infos fl2 with
                      | Some def2 -> (appr1, (lft2, whd_stack infos.if_closure def2 v2))
		      | None -> raise NotConvertible)
            else
	      match unfold_reference infos fl2 with
                | Some def2 -> (appr1, (lft2, whd_stack infos.if_closure def2 v2))
                | None ->
                    (match unfold_reference infos fl1 with
                    | Some def1 -> ((lft1, whd_stack infos.if_closure def1 v1), appr2)
		    | None -> raise NotConvertible) in
          eqappr cv_pb infos app1 app2 cuniv)

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, _)      ->
        (match unfold_reference infos fl1 with
           | Some def1 -> 
	       eqappr cv_pb infos (lft1, whd_stack infos.if_closure def1 v1) appr2 cuniv
           | None -> raise NotConvertible)
    | (_, FFlex fl2)      ->
        (match unfold_reference infos fl2 with
           | Some def2 ->
	       eqappr cv_pb infos appr1 (lft2, whd_stack infos.if_closure def2 v2) cuniv
           | None -> raise NotConvertible)
	
    (* other constructors *)
    | (FLambda _, FLambda _) ->
        assert (is_empty_stack v1 && is_empty_stack v2);
        let (_,ty1,bd1) = destFLambda mk_clos hd1 in
        let (_,ty2,bd2) = destFLambda mk_clos hd2 in
        let u1 = ccnv CONV infos el1 el2 ty1 ty2 cuniv in
        ccnv CONV infos (el_lift el1) (el_lift el2) bd1 bd2 u1

    | (FProd (_,c1,c2), FProd (_,c'1,c'2)) ->
        assert (is_empty_stack v1 && is_empty_stack v2);
	(* Luo's system *)
        let u1 = ccnv CONV infos el1 el2 c1 c'1 cuniv in
        ccnv cv_pb infos (el_lift el1) (el_lift el2) c2 c'2 u1

    (* Inductive types:  MutInd MutConstruct Fix Cofix *)

     | (FInd ind1, FInd ind2) ->
         if mind_equiv_infos infos.if_closure ind1 ind2
	 then
           convert_stacks infos lft1 lft2 v1 v2 cuniv
         else raise NotConvertible

     | (FConstruct (ind1,j1), FConstruct (ind2,j2)) ->
	 if j1 = j2 && mind_equiv_infos infos.if_closure ind1 ind2
	 then
           convert_stacks infos lft1 lft2 v1 v2 cuniv
         else raise NotConvertible

     | (FFix ((op1,(_,tys1,cl1)),e1), FFix((op2,(_,tys2,cl2)),e2)) ->
	 if op1 = op2
	 then
	   let n = Array.length cl1 in
           let fty1 = Array.map (mk_clos e1) tys1 in
           let fty2 = Array.map (mk_clos e2) tys2 in
           let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
           let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
	   let u1 = convert_vect infos el1 el2 fty1 fty2 cuniv in
           let u2 =
             convert_vect infos 
		 (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 u1 in
           convert_stacks infos lft1 lft2 v1 v2 u2
         else raise NotConvertible

     | (FCoFix ((op1,(_,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2)) ->
         if op1 = op2
         then
	   let n = Array.length cl1 in
           let fty1 = Array.map (mk_clos e1) tys1 in
           let fty2 = Array.map (mk_clos e2) tys2 in
           let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
           let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
           let u1 = convert_vect infos el1 el2 fty1 fty2 cuniv in
           let u2 =
	     convert_vect infos
		 (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 u1 in
           convert_stacks infos lft1 lft2 v1 v2 u2
         else raise NotConvertible

     (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
     | ( (FLetIn _, _) | (FCases _,_) | (FApp _,_) | (FCLOS _,_) | (FLIFT _,_)
       | (_, FLetIn _) | (_,FCases _) | (_,FApp _) | (_,FCLOS _) | (_,FLIFT _)
       | (FLOCKED,_) | (_,FLOCKED) ) -> assert false
    
     (* In all other cases, terms are not convertible *)
     | _ -> raise NotConvertible

and convert_stacks infos lft1 lft2 stk1 stk2 cuniv =
  compare_stacks
    (fun (l1,t1) (l2,t2) c -> ccnv CONV infos l1 l2 t1 t2 c)
    (mind_equiv_infos infos.if_closure)
    lft1 stk1 lft2 stk2 cuniv

and convert_vect infos lft1 lft2 v1 v2 cuniv =
  let lv1 = Array.length v1 in
  let lv2 = Array.length v2 in
  if lv1 = lv2
  then 
    let rec fold n univ = 
      if n >= lv1 then univ
      else
        let u1 = ccnv CONV infos lft1 lft2 v1.(n) v2.(n) univ in
        fold (n+1) u1 in
    fold 0 cuniv
  else raise NotConvertible

let clos_fconv trans cv_pb evars env t1 t2 =
  let infos = {
    if_ids      = fst trans;
    if_csts     = snd trans;
    if_closure  = create_clos_infos ~evars betaiotazeta env;
    if_bindings = Environ.DP.bindings env;
  }
  in ccnv cv_pb infos ELID ELID (inject t1) (inject t2) Constraint.empty

let trans_fconv reds cv_pb evars env t1 t2 =
  if eq_constr t1 t2 then Constraint.empty
  else clos_fconv reds cv_pb evars env t1 t2

let trans_conv_cmp conv reds = trans_fconv reds conv (fun _->None)
let trans_conv ?(evars=fun _->None) reds = trans_fconv reds CONV evars
let trans_conv_leq ?(evars=fun _->None) reds = trans_fconv reds CUMUL evars

let fconv = trans_fconv (Idpred.full, Cpred.full)

let conv_cmp cv_pb = fconv cv_pb (fun _->None)
let conv ?(evars=fun _->None) = fconv CONV evars
let conv_leq ?(evars=fun _->None) = fconv CUMUL evars

let conv_leq_vecti ?(evars=fun _->None) env v1 v2 =
  array_fold_left2_i 
    (fun i c t1 t2 ->
      let c' =
        try conv_leq ~evars env t1 t2 
        with NotConvertible -> raise (NotConvertibleVect i) in
      Constraint.union c c')
    Constraint.empty
    v1
    v2

(* option for conversion *)

let vm_conv = ref (fun cv_pb -> fconv cv_pb (fun _->None))
let set_vm_conv f = vm_conv := f
let vm_conv cv_pb env t1 t2 = 
  try 
    !vm_conv cv_pb env t1 t2
  with Not_found | Invalid_argument _ ->
      (* If compilation fails, fall-back to closure conversion *)
      fconv cv_pb (fun _->None) env t1 t2
  

let default_conv = ref (fun cv_pb -> fconv cv_pb (fun _->None))

let set_default_conv f = default_conv := f

let default_conv cv_pb env t1 t2 = 
  try 
    !default_conv cv_pb env t1 t2
  with Not_found | Invalid_argument _ ->
      (* If compilation fails, fall-back to closure conversion *)
      fconv cv_pb (fun _->None) env t1 t2
  
let default_conv_leq = default_conv CUMUL
(*
let convleqkey = Profile.declare_profile "Kernel_reduction.conv_leq";;
let conv_leq env t1 t2 =
  Profile.profile4 convleqkey conv_leq env t1 t2;;

let convkey = Profile.declare_profile "Kernel_reduction.conv";;
let conv env t1 t2 =
  Profile.profile4 convleqkey conv env t1 t2;;
*)

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

(* pseudo-reduction rule:
 * [hnf_prod_app env s (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env t n =
  match kind_of_term (whd_betadeltaiota env t) with
    | Prod (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_prod_app: Need a product"

let hnf_prod_applist env t nl = 
  List.fold_left (hnf_prod_app env) t nl

(* Dealing with arities *)

let dest_prod env = 
  let rec decrec env m c =
    let t = whd_betadeltaiota env c in
    match kind_of_term t with
      | Prod (n,a,c0) ->
          let d = (n,None,a) in
	  decrec (push_rel d env) (Sign.add_rel_decl d m) c0
      | _ -> m,t
  in 
  decrec env Sign.empty_rel_context

(* The same but preserving lets *)
let dest_prod_assum env = 
  let rec prodec_rec env l ty =
    let rty = whd_betadeltaiota_nolet env ty in
    match kind_of_term rty with
    | Prod (x,t,c)  ->
        let d = (x,None,t) in
	prodec_rec (push_rel d env) (Sign.add_rel_decl d l) c
    | LetIn (x,b,t,c) ->
        let d = (x,Some b,t) in
	prodec_rec (push_rel d env) (Sign.add_rel_decl d l) c
    | Cast (c,_,_)    -> prodec_rec env l c
    | _               -> l,rty
  in
  prodec_rec env Sign.empty_rel_context

let dest_arity env c =
  let l, c = dest_prod_assum env c in
  match kind_of_term c with
    | Sort s -> l,s
    | _ -> error "not an arity"

let is_arity env c =
  try
    let _ = dest_arity env c in
    true
  with UserError _ -> false
