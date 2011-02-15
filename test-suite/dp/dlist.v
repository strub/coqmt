(* -------------------------------------------------------------------- *)
Require Import Arith .

Require Import DP_Peano .

(* -------------------------------------------------------------------- *)
Set Implicit Arguments .

(* -------------------------------------------------------------------- *)
Section DList .
  Variable T : Type .

  Inductive dlist : nat -> Type :=
  | nil  : dlist 0
  | cons : forall n, T -> dlist n -> dlist (S n) .

  Notation "[ :: ]" := nil (at level 0, format "[ :: ]") .

  Notation "x :: s" := (@cons _ x s)
    (at level 60, right associativity, format "x  ::  s") .

  Notation "[:: a ; .. ; b ]" := (a :: .. (b :: [::]) ..) .

  Fixpoint append n₁ n₂ (xs₁ : dlist n₁) (xs₂ : dlist n₂) : dlist (n₁ + n₂) :=
  match xs₁ in dlist n₁ return dlist (n₁ + n₂) with
  | nil => xs₂
  | cons n₁ x xs₁ => cons x (append xs₁ xs₂)
  end .

  Infix "++" := append (at level 60, right associativity) .

  Section AppArith .
    Variables n₁ n₂ n₃ : nat .
  
    Implicit Type xs : dlist n₁ .
    Implicit Type ys : dlist n₂ .
    Implicit Type zs : dlist n₃ .
  
    Lemma apps0 : forall xs, xs ++ nil = xs .
    Proof .
      induction xs as [|n x xs IH]; simpl .
      (**) reflexivity .
      (**) rewrite IH; reflexivity .
    Qed .
  
    Lemma app0s : forall xs, nil ++ xs = xs .
    Proof . reflexivity . Qed .
  
    Lemma appA : forall xs ys zs, (xs ++ ys) ++ zs = xs ++ (ys ++ zs) .
    Proof .
      induction xs as [|n x xs IH]; try trivial; intros ys zs; simpl .
      rewrite IH; reflexivity .
    Qed .
  End AppArith .

  Fixpoint rcons n (xs : dlist n) y :=
  match xs in dlist n return dlist (S n) with
  | nil         => [:: y]
  | cons n x xs => x :: (rcons xs y)
  end .

  Lemma rconsapp : forall x n (xs : dlist n), rcons xs x = xs ++ [:: x] .
  Proof .
    intros x n xs; induction xs as [|y n ys IH];
      simpl; try rewrite IH; reflexivity .
  Qed .

  Fixpoint reverse n (xs : dlist n) : dlist n :=
  match xs in dlist n return dlist n with
  | nil => nil
  | cons n x xs => rcons (reverse xs) x
  end .

  Lemma rev0 : reverse nil = nil .
  Proof . reflexivity . Qed .

  Lemma rev1 : forall x, reverse [:: x] = [:: x] .
  Proof . reflexivity . Qed .

  Lemma apprev :
    forall n₁ n₂ (xs : dlist n₁) (ys : dlist n₂),
      (reverse ys) ++ (reverse xs) = reverse (xs ++ ys) .
  Proof .
    induction xs as [|n₁ x xs IH]; intros ys; simpl .
    (**) rewrite apps0; reflexivity .
    (**) rewrite <- IH; repeat rewrite rconsapp .
         rewrite appA; reflexivity .
  Qed .

  Lemma revI : forall n (xs : dlist n), reverse (reverse xs) = xs .
  Proof .
    intros n xs; induction xs as [|n x xs IH]; simpl .
    (**) reflexivity .
    (**) rewrite rconsapp; rewrite <- apprev .
         simpl; rewrite IH; reflexivity .
  Qed .

  Lemma consappA :
    forall x n₁ (xs₁ : dlist n₁) n₂ (xs₂ : dlist n₂),
      x :: (xs₁ ++ xs₂) = (x :: xs₁) ++ xs₂ .
  Proof . reflexivity . Qed .

  Lemma rconsappAC :
    forall n₁ (xs₁ : dlist n₁) n₂ (xs₂ : dlist n₂) y,
      rcons (xs₁ ++ xs₂) y = xs₁ ++ (rcons xs₂ y) .
  Proof .
    intros until y; induction xs₁ as [|n₁ x xs₁ IH]; simpl .
    (**) reflexivity .
    (**) rewrite IH; reflexivity .
  Qed .

  Lemma appconsAC :
    forall n₁ (xs₁ : dlist n₁) y n₂ (xs₂ : dlist n₂),
      (rcons xs₁ y) ++ xs₂ = xs₁ ++ (y :: xs₂) .
  Proof .
    intros until xs₂; rewrite rconsapp, appA; reflexivity .
  Qed .
End DList .

(**
 ** Local Variables:
 ** coq-prog-name: "../../bin/coqtop.byte"
 ** End:
 **)
