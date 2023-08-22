From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.

Require Import List.
Import ListNotations.

Inductive subst_ind : Type :=
| ind_0 : subst_ind
| ind_1 : subst_ind
| lor_ind : subst_ind -> subst_ind -> subst_ind.

Notation "(0)" := ind_0.
Notation "(1)" := ind_1.
Notation "( x @ y )" := (lor_ind x y).

Lemma subst_eq_dec :
    forall (S1 S2 : subst_ind),
        {S1 = S2} + {S1 <> S2}.
Proof.
induction S1;
destruct S2.
1,5 : apply (left eq_refl).
1-6 : right; discriminate.
case (IHS1_1 S2_1) as [EQ1 | NE1].
case (IHS1_2 S2_2) as [EQ2 | NE2].
- left.
  rewrite EQ1,EQ2.
  reflexivity.
- right.
  intros FAL.
  apply NE2.
  inversion FAL.
  reflexivity.
- right.
  intros FAL.
  apply NE1.
  inversion FAL.
  reflexivity.
Qed.

Fixpoint non_target (A : formula) : subst_ind :=
match A with
| lor B C => lor_ind (non_target B) (non_target C)
| _ => (0)
end.

Fixpoint target (A : formula) : subst_ind :=
match A with
| lor B C => lor_ind (target B) (target C)
| _ => (1)
end.

Fixpoint subst_ind_fit (A : formula) (S : subst_ind) : bool :=
match A, S with
| lor B C, lor_ind S_B S_C =>
    subst_ind_fit B S_B && subst_ind_fit C S_C
| _, lor_ind _ _ => false
| lor _ _, _ => false
| _, _ => true
end.

Fixpoint formula_sub_ind_fit (A D E : formula) (S : subst_ind) : formula :=
match A with
| lor B C =>
  (match S with
  | (S1 @ S2) => lor (formula_sub_ind_fit B D E S1)
                         (formula_sub_ind_fit C D E S2)
  | _ => A
  end)
| _ =>
  (match form_eqb A D, S with
  | true, (1) => E
  | _, _ => A
  end)
end.

Definition formula_sub_ind (A D E : formula) (S : subst_ind) : formula :=
match subst_ind_fit A S with
| false => A
| true => formula_sub_ind_fit A D E S
end.

Fixpoint mass_non_target (L : list formula) : list subst_ind :=
match L with
| [] => []
| hd :: tl => (non_target hd) :: (mass_non_target tl)
end.

Fixpoint mass_target (L : list formula) : list subst_ind :=
match L with
| [] => []
| hd :: tl => (target hd) :: (mass_target tl)
end.

Fixpoint mass_fit (LF : list formula) (LS : list subst_ind) : bool :=
match LF, LS with
| [], [] => true
| a :: LF', s :: LS' => subst_ind_fit a s && mass_fit LF' LS'
| _, _ => false
end.

Fixpoint mass_form_sub_fit (LF : list formula) (LS : list subst_ind) (D E : formula) : list formula :=
match LF, LS with
| a :: LF', s :: LS' => formula_sub_ind_fit a D E s :: mass_form_sub_fit LF' LS' D E
| _, _ => LF
end.

Definition mass_form_sub (LF : list formula) (LS : list subst_ind) (D E : formula) : list formula :=
match mass_fit LF LS with
| false => LF
| true => mass_form_sub_fit LF LS D E
end.

Lemma sub_fit_true :
    forall (A D E : formula) (S : subst_ind),
        subst_ind_fit A S = true ->
            formula_sub_ind A D E S = formula_sub_ind_fit A D E S.
Proof.
intros A D E S FS.
unfold formula_sub_ind.
destruct A;
rewrite FS;
reflexivity.
Qed.

Lemma sub_fit_false :
    forall (A D E : formula) (S : subst_ind),
        subst_ind_fit A S = false ->
            formula_sub_ind A D E S = A.
Proof.
intros A D E S FS.
unfold formula_sub_ind.
destruct A;
rewrite FS;
reflexivity.
Qed.

Lemma formula_sub_ind_fit_0 :
    forall (A D E : formula),
        formula_sub_ind_fit A D E (0) = A.
Proof.
intros A D E.
destruct A;
unfold formula_sub_ind_fit.
4 : case (form_eqb (univ n A) D).
2 : case (form_eqb (neg A) D).
1 : case (form_eqb (atom a) D).
all : reflexivity.
Qed.

Lemma formula_sub_ind_0 :
    forall (A D E : formula),
        formula_sub_ind A D E (0) = A.
Proof.
intros A D E.
case (subst_ind_fit A (0)) eqn:HA;
unfold formula_sub_ind;
rewrite HA.
- rewrite formula_sub_ind_fit_0.
  reflexivity.
- reflexivity.
Qed.

Lemma formula_sub_ind_lor :
    forall (A B D E : formula) (S_A S_B : subst_ind),
        subst_ind_fit A S_A && subst_ind_fit B S_B = true ->
            formula_sub_ind (lor A B) D E (lor_ind S_A S_B) = 
                lor (formula_sub_ind A D E S_A) (formula_sub_ind B D E S_B).
Proof.
intros A B D E S_A S_B FS.
unfold formula_sub_ind.
destruct (and_bool_prop _ _ FS) as [FSA FSB].
rewrite FSA,FSB.
unfold subst_ind_fit; fold subst_ind_fit.
rewrite FS.
unfold formula_sub_ind_fit; fold formula_sub_ind_fit.
reflexivity.
Qed.

Lemma non_target_fit :
    forall (A : formula),
        subst_ind_fit A (non_target A) = true.
Proof.
intros A.
unfold subst_ind_fit, non_target.
induction A.
3 : rewrite IHA1, IHA2.
all : reflexivity.
Qed.

Lemma target_fit :
    forall (A : formula),
        subst_ind_fit A (target A) = true.
Proof.
intros A.
unfold subst_ind_fit, target.
induction A.
3 : rewrite IHA1, IHA2.
all : reflexivity.
Qed.

Lemma non_target_sub_fit :
    forall (A : formula) (n : nat) (t : term),
        subst_ind_fit (substitution A n t) (non_target A) = true.
Proof.
intros A n t.
unfold subst_ind_fit, non_target, substitution.
induction A.
3 : rewrite IHA1, IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.

Lemma target_sub_fit :
    forall (A : formula) (n : nat) (t : term),
        subst_ind_fit (substitution A n t) (target A) = true.
Proof.
intros A n t.
unfold subst_ind_fit, target, substitution.
induction A.
3 : rewrite IHA1, IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.

Lemma non_target_sub' :
    forall (A D E : formula),
        formula_sub_ind_fit A D E (non_target A) = A.
Proof.
intros A D E.
induction A;
unfold non_target, formula_sub_ind_fit;
fold non_target formula_sub_ind_fit.
4 : case (form_eqb (univ n A) D).
3 : rewrite IHA1, IHA2.
2 : case (form_eqb (neg A) D).
1 : case (form_eqb (atom a) D).
all : reflexivity.
Qed.

Lemma non_target_sub :
    forall (A C D : formula),
        formula_sub_ind A C D (non_target A) = A.
Proof.
intros A C D.
unfold formula_sub_ind.
rewrite non_target_fit.
apply non_target_sub'.
Qed.

Lemma non_target_sub_lor :
    forall (A B D E : formula) (S : subst_ind),
        formula_sub_ind (lor A B) D E (lor_ind (non_target A) S) =
            lor A (formula_sub_ind B D E S).
Proof.
intros A B D E S.
unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit;
fold subst_ind_fit formula_sub_ind_fit.
rewrite non_target_fit, non_target_sub'.
case (subst_ind_fit B S) eqn:HB;
reflexivity.
Qed.

Lemma non_target_term_sub :
    forall (A : formula) (n : nat) (t : term),
        non_target A = non_target (substitution A n t).
Proof.
intros A n t.
induction A;
unfold non_target, substitution;
fold non_target substitution.
3 : rewrite IHA1,IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.

Lemma target_term_sub :
    forall (A : formula) (n : nat) (t : term),
        target A = target (substitution A n t).
Proof.
intros A n t.
induction A;
unfold target, substitution;
fold target substitution.
3 : rewrite IHA1,IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.


Lemma non_target_sub_term' :
    forall (A C D: formula) (n : nat) (t : term),
        formula_sub_ind_fit (substitution A n t) C D (non_target A) = (substitution A n t).
Proof.
intros.
rewrite (non_target_term_sub _ n t).
apply non_target_sub'.
Qed.


Lemma non_target_sub_term :
    forall (A C D: formula) (n : nat) (t : term),
        formula_sub_ind (substitution A n t) C D (non_target A) = (substitution A n t).
Proof.
intros.
rewrite (non_target_term_sub _ n t).
apply non_target_sub.
Qed.

Lemma formula_sub_ind_free_list :
    forall (A B C : formula),
        (free_list B = free_list C) ->
            forall (S : subst_ind),
                free_list (formula_sub_ind_fit A B C S) = free_list A.
Proof.
intros A B C FREE.
induction A;
intros S;
unfold formula_sub_ind.

all : unfold formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      try case form_eqb eqn:EQ;
      destruct S;
      try apply form_eqb_eq in EQ;
      try destruct EQ, FREE;
      try reflexivity.

1 : unfold free_list;
    fold free_list.
    rewrite IHA1,IHA2.
    reflexivity.
Qed.

Lemma formula_sub_ind_free_list_sub :
    forall (A B C : formula),
        (incl (free_list C) (free_list B)) ->
            forall (S : subst_ind),
                incl (free_list (formula_sub_ind_fit A B C S)) (free_list A).
Proof.
intros A B C FREE.
induction A;
intros S m IN;
unfold formula_sub_ind.

all : unfold formula_sub_ind_fit in IN;
      try case form_eqb eqn:EQ;
      destruct S;
      try apply form_eqb_eq in EQ;
      fold formula_sub_ind_fit in IN;
      try destruct EQ;
      try apply IN;
      try apply (FREE _ IN).

1 : unfold free_list in *;
    fold free_list in *.
    apply nodup_In.
    apply nodup_In in IN.
    apply in_app_or in IN as [IN1 | IN2].
    apply (in_or_app _ _ _ (or_introl (IHA1 _ _ IN1))).
    apply (in_or_app _ _ _ (or_intror (IHA2 _ _ IN2))).
Qed.

Lemma formula_sub_ind_closed :
    forall (A B C : formula),
        closed A = true ->
            (closed B = true -> closed C = true) ->
                forall (S : subst_ind),
                    closed (formula_sub_ind A B C S) = true.
Proof.
intros A B C.
induction A;
intros CA CBC S;
unfold formula_sub_ind.
4 : case (subst_ind_fit (univ n A) S).
3 : case (subst_ind_fit (lor A1 A2) S) eqn:FS.
2 : case (subst_ind_fit (neg A) S).
1 : case (subst_ind_fit (atom a) S).
all : try apply CA;
      unfold formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      destruct S;
      try apply CA.
7 : { unfold formula_sub_ind, formula_sub_ind_fit, subst_ind_fit, closed in *;
      fold formula_sub_ind formula_sub_ind_fit subst_ind_fit closed in *.
      destruct (and_bool_prop _ _ CA) as [CA1 CA2].
      destruct (and_bool_prop _ _ FS) as [FS1 FS2].
      pose proof (IHA1 CA1 CBC S1) as CFA1.
      rewrite FS1 in CFA1.
      rewrite CFA1.
      pose proof (IHA2 CA2 CBC S2) as CFA2.
      rewrite FS2 in CFA2.
      rewrite CFA2.
      reflexivity. }
7-9 : case (form_eqb (univ n A) B) eqn:EQ.
4-6 : case (form_eqb (neg A) B) eqn:EQ.
1-3 : case (form_eqb (atom a) B) eqn:EQ.
all : try apply CA;
      apply form_eqb_eq in EQ;
      destruct EQ;
      apply (CBC CA).
Qed.

Lemma formula_sub_ind_1 :
    forall (A B : formula),
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind A A B (1) = B.
Proof.
intros A B FS.
destruct A;
unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit.
3 : inversion FS.
all : rewrite form_eqb_refl;
      reflexivity.
Qed.

Theorem lor_sub_right:
    forall C A E,
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind (lor C A) A E (lor_ind (non_target C) (1)) = lor C E.
Proof.
intros C A E FS.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ E FS).
  rewrite non_target_sub.
  reflexivity.
- rewrite non_target_fit.
  apply FS.
Qed.

Theorem lor_sub_left:
    forall A D E,
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind (lor A D) A E (lor_ind (1) (non_target D)) = lor E D.
Proof.
intros A D E FS.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ E FS).
  rewrite non_target_sub.
  reflexivity.
- rewrite FS.
  apply non_target_fit.
Qed.