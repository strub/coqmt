(* -------------------------------------------------------------------- *)
Load Theory peano .

Bind Theory peano As peano
  Sort    Binded By nat
  Symbols Binded By
    O    for zero ,
    S    for succ ,
    plus for plus ,
    mult for mult .

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

  Infix "++" := append (at level 35, right associativity) .

  Fixpoint reverse n (xs : dlist n) : dlist n :=
  match xs in dlist n return dlist n with
  | nil => nil
  | cons n x xs => (reverse xs) ++ [:: x]
  end .

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

  Lemma apprev :
    forall n₁ n₂ (xs : dlist n₁) (ys : dlist n₂),
      (reverse ys) ++ (reverse xs) = reverse (xs ++ ys) .
  Proof .
    induction xs as [|n₁ x xs IH]; intros ys; simpl .
    (**) rewrite apps0; reflexivity .
    (**) rewrite <- IH .
         rewrite (appA (reverse ys) (reverse xs) _) . (* PB: unification failure *)
         reflexivity .
  Qed .
End DList .

(**
 ** Local Variables:
 ** coq-prog-name: "../../bin/coqtop.byte"
 ** End:
 **)
