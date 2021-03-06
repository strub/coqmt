(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Rtrigo_fun.v 13323 2010-07-24 15:57:30Z herbelin $ i*)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Open Local Scope R_scope.

(*****************************************************************)
(**           To define transcendental functions                 *)
(**           and exponential function                           *)
(*****************************************************************)

(*********)
Lemma Alembert_exp :
  Un_cv (fun n:nat => Rabs (/ INR (fact (S n)) * / / INR (fact n))) 0.
Proof.
  unfold Un_cv in |- *; intros; elim (Rgt_dec eps 1); intro.
  split with 0%nat; intros; rewrite (simpl_fact n); unfold R_dist in |- *;
    rewrite (Rminus_0_r (Rabs (/ INR (S n))));
      rewrite (Rabs_Rabsolu (/ INR (S n))); cut (/ INR (S n) > 0).
  intro; rewrite (Rabs_pos_eq (/ INR (S n))).
  cut (/ eps - 1 < 0).
  intro; generalize (Rlt_le_trans (/ eps - 1) 0 (INR n) H2 (pos_INR n));
    clear H2; intro; unfold Rminus in H2;
      generalize (Rplus_lt_compat_l 1 (/ eps + -1) (INR n) H2);
        replace (1 + (/ eps + -1)) with (/ eps); [ clear H2; intro | ring ].
  rewrite (Rplus_comm 1 (INR n)) in H2; rewrite <- (S_INR n) in H2;
    generalize (Rmult_gt_0_compat (/ INR (S n)) eps H1 H);
      intro; unfold Rgt in H3;
        generalize (Rmult_lt_compat_l (/ INR (S n) * eps) (/ eps) (INR (S n)) H3 H2);
          intro; rewrite (Rmult_assoc (/ INR (S n)) eps (/ eps)) in H4;
            rewrite (Rinv_r eps (Rlt_dichotomy_converse eps 0 (or_intror (eps < 0) H)))
              in H4; rewrite (let (H1, H2) := Rmult_ne (/ INR (S n)) in H1) in H4;
                rewrite (Rmult_comm (/ INR (S n))) in H4;
                  rewrite (Rmult_assoc eps (/ INR (S n)) (INR (S n))) in H4;
                    rewrite (Rinv_l (INR (S n)) (not_O_INR (S n) (sym_not_equal (O_S n)))) in H4;
                      rewrite (let (H1, H2) := Rmult_ne eps in H1) in H4;
                        assumption.
  apply Rlt_minus; unfold Rgt in a; rewrite <- Rinv_1;
    apply (Rinv_lt_contravar 1 eps); auto;
      rewrite (let (H1, H2) := Rmult_ne eps in H2); unfold Rgt in H;
        assumption.
  unfold Rgt in H1; apply Rlt_le; assumption.
  unfold Rgt in |- *; apply Rinv_0_lt_compat; apply lt_INR_0; apply lt_O_Sn.
(**)
  cut (0 <= up (/ eps - 1))%Z.
  intro; elim (IZN (up (/ eps - 1)) H0); intros; split with x; intros;
    rewrite (simpl_fact n); unfold R_dist in |- *;
      rewrite (Rminus_0_r (Rabs (/ INR (S n))));
        rewrite (Rabs_Rabsolu (/ INR (S n))); cut (/ INR (S n) > 0).
  intro; rewrite (Rabs_pos_eq (/ INR (S n))).
  cut (/ eps - 1 < INR x).
  intro ;
    generalize
      (Rlt_le_trans (/ eps - 1) (INR x) (INR n) H4
        (le_INR x n H2));
      clear H4; intro; unfold Rminus in H4;
        generalize (Rplus_lt_compat_l 1 (/ eps + -1) (INR n) H4);
          replace (1 + (/ eps + -1)) with (/ eps); [ clear H4; intro | ring ].
  rewrite (Rplus_comm 1 (INR n)) in H4; rewrite <- (S_INR n) in H4;
    generalize (Rmult_gt_0_compat (/ INR (S n)) eps H3 H);
      intro; unfold Rgt in H5;
        generalize (Rmult_lt_compat_l (/ INR (S n) * eps) (/ eps) (INR (S n)) H5 H4);
          intro; rewrite (Rmult_assoc (/ INR (S n)) eps (/ eps)) in H6;
            rewrite (Rinv_r eps (Rlt_dichotomy_converse eps 0 (or_intror (eps < 0) H)))
              in H6; rewrite (let (H1, H2) := Rmult_ne (/ INR (S n)) in H1) in H6;
                rewrite (Rmult_comm (/ INR (S n))) in H6;
                  rewrite (Rmult_assoc eps (/ INR (S n)) (INR (S n))) in H6;
                    rewrite (Rinv_l (INR (S n)) (not_O_INR (S n) (sym_not_equal (O_S n)))) in H6;
                      rewrite (let (H1, H2) := Rmult_ne eps in H1) in H6;
                        assumption.
  cut (IZR (up (/ eps - 1)) = IZR (Z_of_nat x));
    [ intro | rewrite H1; trivial ].
  elim (archimed (/ eps - 1)); intros; clear H6; unfold Rgt in H5;
    rewrite H4 in H5; rewrite INR_IZR_INZ; assumption.
  unfold Rgt in H1; apply Rlt_le; assumption.
  unfold Rgt in |- *; apply Rinv_0_lt_compat; apply lt_INR_0; apply lt_O_Sn.
  apply (le_O_IZR (up (/ eps - 1)));
    apply (Rle_trans 0 (/ eps - 1) (IZR (up (/ eps - 1)))).
  generalize (Rnot_gt_le eps 1 b); clear b; unfold Rle in |- *; intro; elim H0;
    clear H0; intro.
  left; unfold Rgt in H;
    generalize (Rmult_lt_compat_l (/ eps) eps 1 (Rinv_0_lt_compat eps H) H0);
      rewrite
        (Rinv_l eps
          (sym_not_eq (Rlt_dichotomy_converse 0 eps (or_introl (0 > eps) H))))
        ; rewrite (let (H1, H2) := Rmult_ne (/ eps) in H1);
          intro; fold (/ eps - 1 > 0) in |- *; apply Rgt_minus;
            unfold Rgt in |- *; assumption.
  right; rewrite H0; rewrite Rinv_1; apply sym_eq; apply Rminus_diag_eq; auto.
  elim (archimed (/ eps - 1)); intros; clear H1; unfold Rgt in H0; apply Rlt_le;
    assumption.
Qed.
