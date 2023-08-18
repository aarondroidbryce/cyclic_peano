From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.

Require Import List.
Import ListNotations.

Inductive paint_ind : Type :=
| colour : list nat -> paint_ind
| lor_ind : paint_ind -> paint_ind -> paint_ind.

Notation "( 0 )" := (colour [0]).
Notation "( 1 )" := (colour [1]).
Notation "< L |" := (colour L).
Notation "< x , y |" := (lor_ind x y).

Section Paint.

Lemma subst_eq_dec :
    forall (S1 S2 : paint_ind),
        {S1 = S2} + {S1 <> S2}.
Proof.
induction S1;
destruct S2.
case (list_eq_dec nat_eq_dec l l0) as [[] | NE].
1 : apply (left eq_refl).
2-3 : right; discriminate.
2 : case (IHS1_1 S2_1) as [EQ1 | NE].
2 : case (IHS1_2 S2_2) as [EQ2 | NE].
2 : { left.
      rewrite EQ1,EQ2.
      reflexivity. }
all : right;
      intros FAL;
      apply NE;
      inversion FAL;
      reflexivity.
Qed.

Fixpoint coat (A : formula) (L : list nat) : paint_ind :=
match A with
| lor B C => lor_ind (coat B L) (coat C L)
| _ => <L|
end.

Definition non_target (A : formula) := coat A [0].

Definition target (A : formula) := coat A [1].

Fixpoint paint_ind_fit (A : formula) (S : paint_ind) : bool :=
match A, S with
| lor B C, lor_ind S_B S_C =>
    paint_ind_fit B S_B && paint_ind_fit C S_C
| _, lor_ind _ _ => false
| lor _ _, _ => false
| _, _ => true
end.

Fixpoint formula_sub_ind_fit (A D E : formula) (S : paint_ind) : formula :=
match A with
| lor B C =>
  (match S with
  | lor_ind S1 S2 => lor (formula_sub_ind_fit B D E S1)
                         (formula_sub_ind_fit C D E S2)
  | _ => A
  end)
| _ =>
  (match form_eqb A D, S with
  | true, (1) => E
  | _, _ => A
  end)
end.

Definition formula_sub_ind (A D E : formula) (S : paint_ind) : formula :=
match paint_ind_fit A S with
| false => A
| true => formula_sub_ind_fit A D E S
end.

Lemma sub_fit_true :
    forall (A D E : formula) (S : paint_ind),
        paint_ind_fit A S = true ->
            formula_sub_ind A D E S = formula_sub_ind_fit A D E S.
Proof.
intros A D E S FS.
unfold formula_sub_ind.
destruct A;
rewrite FS;
reflexivity.
Qed.

Lemma sub_fit_false :
    forall (A D E : formula) (S : paint_ind),
        paint_ind_fit A S = false ->
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
case (paint_ind_fit A (0)) eqn:HA;
unfold formula_sub_ind;
rewrite HA.
- rewrite formula_sub_ind_fit_0.
  reflexivity.
- reflexivity.
Qed.

Lemma formula_sub_ind_lor :
    forall (A B D E : formula) (S_A S_B : paint_ind),
        paint_ind_fit A S_A && paint_ind_fit B S_B = true ->
            formula_sub_ind (lor A B) D E (lor_ind S_A S_B) = 
                lor (formula_sub_ind A D E S_A) (formula_sub_ind B D E S_B).
Proof.
intros A B D E S_A S_B FS.
unfold formula_sub_ind.
destruct (and_bool_prop _ _ FS) as [FSA FSB].
rewrite FSA,FSB.
unfold paint_ind_fit; fold paint_ind_fit.
rewrite FS.
unfold formula_sub_ind_fit; fold formula_sub_ind_fit.
reflexivity.
Qed.

Lemma coat_fit :
    forall {A : formula} {L : list nat},
        paint_ind_fit A (coat A L) = true.
Proof.
intros A L.
unfold paint_ind_fit, coat.
induction A.
3 : rewrite IHA1, IHA2.
all : reflexivity.
Qed.

Lemma non_target_fit :
    forall {A : formula},
        paint_ind_fit A (non_target A) = true.
Proof.
intros A. apply coat_fit.
Qed.

Lemma target_fit :
    forall {A : formula},
        paint_ind_fit A (target A) = true.
Proof.
intros A. apply coat_fit.
Qed.

Lemma non_target_sub_fit :
    forall {A : formula} {n : nat} {t : term},
        paint_ind_fit (substitution A n t) (non_target A) = true.
Proof.
intros A n t.
unfold paint_ind_fit, non_target, coat, substitution.
induction A.
3 : rewrite IHA1, IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.

Lemma target_sub_fit :
    forall {A : formula} {n : nat} {t : term},
        paint_ind_fit (substitution A n t) (target A) = true.
Proof.
intros A n t.
unfold paint_ind_fit, target, coat, substitution.
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
unfold non_target, coat, formula_sub_ind_fit;
fold coat formula_sub_ind_fit;
try fold (non_target A1) (non_target A2).
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

Lemma non_target_sub_lor_left :
    forall (A B D E : formula) (S : paint_ind),
        formula_sub_ind (lor A B) D E (lor_ind (non_target A) S) =
            lor A (formula_sub_ind B D E S).
Proof.
intros A B D E S.
unfold formula_sub_ind, paint_ind_fit, formula_sub_ind_fit;
fold paint_ind_fit formula_sub_ind_fit.
rewrite non_target_fit, non_target_sub'.
case (paint_ind_fit B S) eqn:HB;
reflexivity.
Qed.

Lemma coat_subst_eq :
    forall {A : formula} {L : list nat} {n : nat} {t : term},
        coat (substitution A n t) L = coat A L.
Proof.
intros A L n t.
induction A;
unfold coat, substitution;
fold coat substitution.
3 : rewrite IHA1,IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.

Lemma non_target_subst_eq :
    forall (A : formula) (n : nat) (t : term),
        non_target (substitution A n t) = non_target A.
Proof.
intros A n t.
apply coat_subst_eq.
Qed.

Lemma target_subst_eq :
    forall (A : formula) (n : nat) (t : term),
        target (substitution A n t) = target A.
Proof.
intros A n t.
apply coat_subst_eq.
Qed.

Lemma formula_sub_ind_free_list :
    forall (A B C : formula),
        (free_list B = free_list C) ->
            forall (S : paint_ind),
                free_list (formula_sub_ind_fit A B C S) = free_list A.
Proof.
intros A B C FREE.
induction A;
intros S;
unfold formula_sub_ind.

all : unfold formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      try case form_eqb eqn:EQ;
      destruct S as [[ | [ | [ | ] ] [ | ] ] | ];
      try apply form_eqb_eq in EQ;
      try destruct EQ, FREE;
      try reflexivity.

1 : unfold free_list;
    fold free_list;
    rewrite IHA1,IHA2;
    reflexivity.
Qed.

Lemma formula_sub_ind_free_list_sub :
    forall (A B C : formula),
        (incl (free_list C) (free_list B)) ->
            forall (S : paint_ind),
                incl (free_list (formula_sub_ind_fit A B C S)) (free_list A).
Proof.
intros A B C FREE.
induction A;
intros S m IN;
unfold formula_sub_ind.

all : unfold formula_sub_ind_fit in IN;
      try case form_eqb eqn:EQ;
      destruct S as [[ | [ | [ | ] ] [ | ] ] | ];
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
                forall (S : paint_ind),
                    closed (formula_sub_ind A B C S) = true.
Proof.
intros A B C.
induction A;
intros CA CBC S;
unfold formula_sub_ind.
4 : case (paint_ind_fit (univ n A) S).
3 : case (paint_ind_fit (lor A1 A2) S) eqn:FS.
2 : case (paint_ind_fit (neg A) S).
1 : case (paint_ind_fit (atom a) S).
all : try apply CA;
      unfold formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      destruct S as [[ | [ | [ | ] ] [ | ] ] | ].
24 : { unfold formula_sub_ind, formula_sub_ind_fit, paint_ind_fit, closed in *;
       fold formula_sub_ind formula_sub_ind_fit paint_ind_fit closed in *.
       destruct (and_bool_prop _ _ CA) as [CA1 CA2].
       destruct (and_bool_prop _ _ FS) as [FS1 FS2].
       pose proof (IHA1 CA1 CBC S1) as CFA1.
       rewrite FS1 in CFA1.
       rewrite CFA1.
       pose proof (IHA2 CA2 CBC S2) as CFA2.
       rewrite FS2 in CFA2.
       rewrite CFA2.
       reflexivity. }
24-31 : case (form_eqb (univ n A) B) eqn:EQ.
9-16 : case (form_eqb (neg A) B) eqn:EQ.
1-8 : case (form_eqb (atom a) B) eqn:EQ.
all : try apply CA;
      apply form_eqb_eq in EQ;
      destruct EQ;
      apply (CBC CA).
Qed.

Lemma formula_sub_ind_1 :
    forall (A B : formula),
        (paint_ind_fit A (1) = true) ->
            formula_sub_ind A A B (1) = B.
Proof.
intros A B FS.
destruct A;
unfold formula_sub_ind, paint_ind_fit, formula_sub_ind_fit.
3 : inversion FS.
all : rewrite form_eqb_refl;
      reflexivity.
Qed.

Theorem lor_sub_right:
    forall C A E,
        (paint_ind_fit A (1) = true) ->
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
        (paint_ind_fit A (1) = true) ->
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

Definition paint_ex_ab (I : paint_ind) : paint_ind :=
match I with
| <Ia, Ib| => <Ib, Ia|
| _ => I
end.

Definition paint_ex_cab (I : paint_ind) : paint_ind :=
match I with
| <<Ic, Ia|, Ib| => <<Ic, Ib|, Ia|
| _ => I
end.

Definition paint_ex_abd (I : paint_ind) : paint_ind :=
match I with
| <<Ia, Ib|, Id| => <<Ib, Ia|, Id|
| _ => I
end.

Definition paint_ex_cabd (I : paint_ind) : paint_ind :=
match I with
| <<<Ic, Ia|, Ib|, Id| => <<<Ic, Ib|, Ia|, Id|
| _ => I
end.

Definition paint_con_a (I : paint_ind) : paint_ind :=
match I with
| <Ia, Ib| => match subst_eq_dec Ia Ib with
    | True => Ia
    end
| _ => I
end.

Definition paint_con_ad (I : paint_ind) : paint_ind :=
match I with
| <<Ia, Ib|, Id| => match subst_eq_dec Ia Ib with
    | True => <Ia, Id|
    end
| _ => I
end.

Definition paint_dem_ab (I1 I2 : paint_ind) : paint_ind :=
match I1,I2 with 
| colour L1, colour L2 => <L1 ++ L2|
| _, _ => I1
end.

Definition paint_dem_abd (I1 I2 : paint_ind) : paint_ind :=
match I1,I2 with 
| <colour L1, Ic|, <colour L2, Id| => match subst_eq_dec Ic Id with
    | True => <<L1 ++ L2|, Id|
    end
| _, _ => I1
end.


End Paint.