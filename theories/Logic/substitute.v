From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.

Require Import List.
Import ListNotations.

(* Defining substitution indicators. When we later define formula substitution,
we will want to take some formula A, and replace any instances of the
subformula E with the formula F. However, we will only want to do this at
certain places in A. Substitution indicators will control this.
For instance, if A is "B \/ (C \/ D)" we might be given a substitution
indicator S that looks like "0 (1 0)" which indicates that we want to
substitute C (if C is E) but leave B,D alone even if they are E. *)
Inductive subst_ind : Type :=
| ind_0 : subst_ind
| ind_1 : subst_ind
| lor_ind : subst_ind -> subst_ind -> subst_ind.

Notation "(0)" := ind_0.
Notation "(1)" := ind_1.
Notation "( x y )" := (lor_ind x y).

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

Definition formula_sub_ind (A D E : formula) (S : subst_ind) : formula :=
match subst_ind_fit A S with
| false => A
| true => formula_sub_ind_fit A D E S
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

(*
Fixpoint leaf_subst (P : ptree) (S : subst_ind) : list subst_ind :=
match P,S with
| deg_up d P', _ => leaf_subst P' S

| ord_up alpha P', _ => leaf_subst P'

| node A, _ => [S]

| exchange_ab A B d alpha P', _ => leaf_subst P' S

| exchange_cab C A B d alpha P', _ => leaf_subst P' S

| exchange_abd A B D d alpha P' => node_extract P'

| exchange_cabd C A B D d alpha P' => node_extract P'

| contraction_a A d alpha P' => node_extract P'

| contraction_ad A D d alpha P' => node_extract P'

| weakening_ad A D d alpha P' => node_extract P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| negation_a A d alpha P' => node_extract P'

| negation_ad A D d alpha P' => node_extract P'

| quantification_a A n t d alpha P' => node_extract P'

| quantification_ad A D n t d alpha P' => node_extract P'

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 =>
    match free_list A with
    | [] => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
    | hd :: [] =>
        match nat_eqb hd n with
        | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        end
    | _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
    end

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => 
    match closed C with
        | true =>
            match free_list A with
            | [] => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            | hd :: [] =>
                match nat_eqb hd n with
                | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                end
            | _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            end
        | false => (univ n A) ::  (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        end

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2 =>
    match closed D with
        | true =>
            match free_list A with
            | [] => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            | hd :: [] =>
                match nat_eqb hd n with
                | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                end
            | _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            end
        | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        end

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2 => 
    match closed C, closed D with
        | true, true =>
            match free_list A with
            | [] => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            | hd :: [] =>
                match nat_eqb hd n with
                | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                end
            | _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            end
        | _, _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        end

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2
end.
*)

(*
Definition tree_trace_form_l (P : ptree) : formula :=
match P with
| deg_up d P'_ => ptree_formula P

| ord_up alpha P' => ptree_formula P

| node A => A

| exchange_ab A B d alpha P' => (lor A B)

| exchange_cab C A B d alpha P' => (lor (lor C A) B)

| exchange_abd A B D d alpha P' => (lor (lor A B) D)

| exchange_cabd C A B D d alpha P' => (lor (lor (lor C A) B) D)

| contraction_a A d alpha P' => (lor A A)

| contraction_ad A D d alpha P' => (lor (lor A A) D)

| weakening_ad A D d alpha P' => D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => (neg A)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => (lor (neg A) D)

| negation_a A d alpha P' => A

| negation_ad A D d alpha P' => lor A D

| quantification_a A n t d alpha P' => (substitution A n (projT1 t))

| quantification_ad A D n t d alpha P' => lor (substitution A n (projT1 t)) D

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => substitution A n (projT1 czero)

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => lor C (substitution A n (projT1 czero))

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2 => substitution A n (projT1 czero)

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2 => lor C (substitution A n (projT1 czero))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => (lor C A)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => A

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => (lor C A)
end.

Definition tree_trace_form_r (P : ptree) : formula :=
match P with
| deg_up d P'_ => ptree_formula P

| ord_up alpha P' => ptree_formula P

| node A => A

| exchange_ab A B d alpha P' => (lor A B)

| exchange_cab C A B d alpha P' => (lor (lor C A) B)

| exchange_abd A B D d alpha P' => (lor (lor A B) D)

| exchange_cabd C A B D d alpha P' => (lor (lor (lor C A) B) D)

| contraction_a A d alpha P' => (lor A A)

| contraction_ad A D d alpha P' => (lor (lor A A) D)

| weakening_ad A D d alpha P' => D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => (neg B)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => (lor (neg B) D)

| negation_a A d alpha P' => A

| negation_ad A D d alpha P' => lor A D

| quantification_a A n t d alpha P' => (substitution A n (projT1 t))

| quantification_ad A D n t d alpha P' => lor (substitution A n (projT1 t)) D

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => substitution A n (succ (var n))

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => (substitution A n (succ (var n)))

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2 => lor (substitution A n (succ (var n))) D

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2 => lor (substitution A n (succ (var n))) D

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => (neg A)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => (lor (neg A) D)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => (lor (neg A) D)
end.

Definition tree_tracer_fit_l (P : ptree) (S : subst_ind) : subst_ind :=
match P, S with
| deg_up d P', _ => S

| ord_up alpha P', _ => S

| node A, _ => S

| exchange_ab A B d alpha P', lor_ind S_B S_A => (lor_ind S_A S_B)

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A => (lor_ind (lor_ind S_C S_A) S_B)

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D => (lor_ind (lor_ind S_A S_B) S_D)

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D => (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D)

| contraction_a A d alpha P', _ => (lor_ind S S)

| contraction_ad A D d alpha P', lor_ind S_A S_D => (lor_ind (lor_ind S_A S_A) S_D)

| weakening_ad A D d alpha P', lor_ind S_A S_D => S_D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => (0)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D => (lor_ind (0) S_D)

| negation_a A d alpha P', _ => (non_target A)

| negation_ad A D d alpha P', lor_ind S_A S_D => (lor_ind (non_target A) S_D)

| quantification_a A n t d alpha P', _ => (non_target A)

| quantification_ad A D n t d alpha P', lor_ind S_A S_D => (lor_ind (non_target A) S_D)

| loop_a A n d1 d2 alpha1 alpha2 P1 P2, _ => non_target A

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2, (lor_ind SC SA) => (lor_ind SC (non_target A))

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2, (lor_ind SA SD) => (non_target A)

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2, (lor_ind (lor_ind SC SA) SD) => (lor_ind SC (non_target A))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ => (lor_ind S (non_target A))

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ => (non_target A)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D => (lor_ind S_C (non_target A))

| _, _ => (0)
end.

Definition tree_tracer_fit_r (P : ptree) (S : subst_ind) : subst_ind :=
match P, S with
| deg_up d P', _ => S

| ord_up alpha P', _ => S

| node A, _ => S

| exchange_ab A B d alpha P', lor_ind S_B S_A => (lor_ind S_A S_B)

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A => (lor_ind (lor_ind S_C S_A) S_B)

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D => (lor_ind (lor_ind S_A S_B) S_D)

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D => (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D)

| contraction_a A d alpha P', _ => (lor_ind S S)

| contraction_ad A D d alpha P', lor_ind S_A S_D => (lor_ind (lor_ind S_A S_A) S_D)

| weakening_ad A D d alpha P', lor_ind S_A S_D => S_D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => (0)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D => (lor_ind (0) S_D)

| negation_a A d alpha P', _ => (non_target A)

| negation_ad A D d alpha P', lor_ind S_A S_D => (lor_ind (non_target A) S_D)

| quantification_a A n t d alpha P', _ => (non_target A)

| quantification_ad A D n t d alpha P', lor_ind S_A S_D => (lor_ind (non_target A) S_D)

| loop_a A n d1 d2 alpha1 alpha2 P1 P2, _ => non_target A

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2, (lor_ind SC SA) => (non_target A)

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2, (lor_ind SA SD) => (lor_ind (non_target A) SD)

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2, (lor_ind (lor_ind SC SA) SD) => (lor_ind (non_target A) SD)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ => (0)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ => (lor_ind (0) S)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D => (lor_ind (0) S_D)

| _, _ => (0)
end.

Definition tree_tracer_l (P : ptree) (S : subst_ind) : subst_ind :=
match subst_ind_fit (ptree_formula P) S with
| false => (0)
| true => (tree_tracer_fit_l P S)
end.

Definition tree_tracer_r (P : ptree) (S : subst_ind) : subst_ind :=
match subst_ind_fit (ptree_formula P) S with
| false => (0)
| true => (tree_tracer_fit_r P S)
end.

Fixpoint target_check (A : formula) (S : subst_ind) : list formula :=
match A,S with
| atom a, (1) => [A]
| neg B, (1) => [A]
| univ n B, (1) => [A]
| lor B C , (lor_ind S1 S2) => (target_check B S1) ++ (target_check C S2)
| _, _ => []
end.

Lemma target_check_non_target :
    forall (A : formula),
        target_check A (non_target A) = [].
Proof.
induction A;
try reflexivity;
simpl.
rewrite IHA1,IHA2.
reflexivity.
Qed.

Lemma target_check_nil :
    forall (A E F : formula) (S : subst_ind),
        target_check A S = [] ->
            formula_sub_ind A E F S = A.
Proof.
induction A;
intros E F S K;
unfold formula_sub_ind;
case subst_ind_fit eqn:FS;
try reflexivity;
unfold target_check in K;
fold target_check in K;
destruct S;
inversion FS as [FS'];
inversion K as [K'];
try apply formula_sub_ind_fit_0.
case (target_check A1 S1) eqn:K1;
case (target_check A2 S2) eqn:K2;
try inversion K.
unfold formula_sub_ind_fit;
fold formula_sub_ind_fit.
apply and_bool_prop in FS' as [FS1 FS2].
pose proof (IHA1 E F S1 K1) as I1.
pose proof (IHA2 E F S2 K2) as I2.
unfold formula_sub_ind in *.
rewrite FS1 in I1.
rewrite FS2 in I2.
rewrite I1,I2.
reflexivity.
Qed.

Lemma target_check_not_mem_idem :
    forall (A E F : formula) (S : subst_ind),
        ~ In E (target_check A S) ->
            formula_sub_ind A E F S = A.
Proof.
induction A;
intros E F S NIN;
unfold formula_sub_ind;
case subst_ind_fit eqn:FS;
try reflexivity;
unfold target_check in NIN;
fold target_check in NIN;
destruct S;
inversion FS as [FS'];
try apply formula_sub_ind_fit_0;
unfold formula_sub_ind_fit;
fold formula_sub_ind_fit;
try case form_eqb eqn:EQ;
try reflexivity;
try apply form_eqb_eq in EQ;
try rewrite EQ in NIN;
try contradict (NIN (or_introl eq_refl)).

apply and_bool_prop in FS' as [FS1 FS2].
pose proof (IHA1 E F S1) as I1.
pose proof (IHA2 E F S2) as I2.
unfold formula_sub_ind in *.
rewrite FS1 in I1.
rewrite FS2 in I2.
rewrite I1,I2.
reflexivity.

all : intros FAL;
      apply NIN, in_app_iff; auto.
Qed.

Lemma target_check_subst_ptree_l : 
    forall (P : ptree) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                subst_ind_fit (tree_trace_form_l P) (tree_tracer_l P S) = true.
Proof.
intros P S PSV FS.
induction P;
unfold tree_trace_form_l, tree_tracer_l, ptree_formula, subst_ind_fit, tree_tracer_fit_l in *;
fold ptree_formula tree_trace_form_l tree_tracer_l subst_ind_fit in *;
try rewrite FS in *;
try rewrite non_target_fit;
try rewrite non_target_sub_fit;
try rewrite FS;
try reflexivity;
destruct S;
inversion FS as [FS'];
try apply and_bool_prop in FS' as [FS1 FS2];
try rewrite FS1;
try rewrite FS2;
try rewrite non_target_fit;
try rewrite non_target_sub_fit;
try reflexivity;
try destruct S1;
try inversion FS as [FS''];
try rewrite FS'';
try apply and_bool_prop in FS1 as [FS1 FS3];
try rewrite FS1;
try rewrite FS2;
try rewrite FS3;
try rewrite non_target_fit;
try rewrite non_target_sub_fit;
try reflexivity;
try destruct S1_1;
inversion FS as [FS'''];
try rewrite FS''';
try apply and_bool_prop in FS1 as [FS1 FS4];
try rewrite FS1;
try rewrite FS2;
try rewrite FS3;
try rewrite FS4;
try reflexivity.
Qed.

Lemma target_check_subst_ptree_r : 
    forall (P : ptree) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                subst_ind_fit (tree_trace_form_r P) (tree_tracer_r P S) = true.
Proof.
intros P S PSV FS.
induction P;
unfold tree_trace_form_r, tree_tracer_r, ptree_formula, subst_ind_fit, tree_tracer_fit_r in *;
fold ptree_formula tree_trace_form_r tree_tracer_r subst_ind_fit in *;
try rewrite FS in *;
try rewrite non_target_fit;
try rewrite non_target_sub_fit;
try rewrite FS;
try reflexivity;
destruct S;
inversion FS as [FS'];
try apply and_bool_prop in FS' as [FS1 FS2];
try rewrite FS1;
try rewrite FS2;
try rewrite non_target_fit;
try rewrite non_target_sub_fit;
try reflexivity;
try destruct S1;
try inversion FS as [FS''];
try rewrite FS'';
try apply and_bool_prop in FS1 as [FS1 FS3];
try rewrite FS1;
try rewrite FS2;
try rewrite FS3;
try rewrite non_target_fit;
try rewrite non_target_sub_fit;
try reflexivity;
try destruct S1_1;
inversion FS as [FS'''];
try rewrite FS''';
try apply and_bool_prop in FS1 as [FS1 FS4];
try rewrite FS1;
try rewrite FS2;
try rewrite FS3;
try rewrite FS4;
try reflexivity.
Qed.
*)

(*
Lemma testi :
    forall (P : ptree) (A : formula),
        ptree_formula P = A ->
            forall (S : subst_ind),
                subst_ind_fit A S = true ->
                    (forall (B : formula), In B (target_check A S) <-> In B (target_check (tree_trace_form_l P) (tree_tracer_l P S))).
Proof.
induction P;
intros A FEQ S FS;
unfold tree_trace_form_l, tree_tracer_l;
unfold ptree_formula in *;
fold ptree_formula in *;
try rewrite FEQ;
try rewrite FS;
unfold tree_tracer_fit_l;
try reflexivity;
try rewrite <- FEQ in FS;
destruct S;
inversion FS as [FS'];
try rewrite <- FEQ;
unfold target_check;
fold target_check.
intros B.
rewrite in_app_comm.*)