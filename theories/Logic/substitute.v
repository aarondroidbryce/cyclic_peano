From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.

Require Import List.
Import ListNotations.

Definition subst_ind : Type := list bool.

Lemma subst_eq_dec :
    forall (S1 S2 : subst_ind),
        {S1 = S2} + {S1 <> S2}.
Proof.
apply list_eq_dec, Bool.bool_dec.
Qed.

Definition non_target (gamma : list formula) : subst_ind := repeat false (length gamma).

Definition target (gamma : list formula) : subst_ind := repeat true (length gamma).

Definition formula_sub (phi A1 A2 : formula) (b : bool) : formula :=
match form_eqb phi A1, b with
| true, true => A2
| _, _ => phi
end.

Fixpoint batch_sub_fit (gamma : list formula) (A1 A2 : formula) (S : subst_ind) : list formula :=
match gamma, S with
| phi :: gamma', b :: S' => (formula_sub phi A1 A2 b) :: batch_sub_fit gamma' A1 A2 S'
| _ , _ => gamma
end.

Definition batch_sub (gamma : list formula) (A1 A2 : formula) (S : subst_ind) : list formula :=
match nat_eqb (length gamma) (length S) with
| false => gamma
| true => batch_sub_fit gamma A1 A2 S
end.

Lemma formula_sub_false {phi A1 A2 : formula} : formula_sub phi A1 A2 false = phi.
Proof. unfold formula_sub. case (form_eqb phi A1); reflexivity. Qed.

Lemma batch_sub_nil :
    forall (gamma : list formula) (A1 A2 : formula),
        batch_sub_fit gamma A1 A2 [] = gamma.
Proof. induction gamma; reflexivity. Qed.

Lemma batch_sub_fit_true :
    forall {gamma : list formula} {A1 A2 : formula} {S : subst_ind},
        nat_eqb (length gamma) (length S) = true ->
            batch_sub_fit gamma A1 A2 S = batch_sub gamma A1 A2 S.
Proof. intros gamma A1 A2 S EQ. unfold batch_sub. rewrite EQ. reflexivity. Qed.

Lemma batch_sub_single :
    forall (phi : formula) (A1 A2 : formula) (b : bool),
            batch_sub [phi] A1 A2 [b] = [formula_sub phi A1 A2 b].
Proof. reflexivity. Qed.

Lemma batch_sub_false_head :
    forall (phi : formula) (gamma : list formula) (A1 A2 : formula) (S : subst_ind),
            batch_sub (phi :: gamma) A1 A2 (false :: S) = phi :: batch_sub gamma A1 A2 S.
Proof.
intros phi gamma A1 A2 S.
unfold batch_sub, length, nat_eqb.
fold nat_eqb (@length formula) (@length bool).
case (nat_eqb (length gamma) (length S));
unfold batch_sub_fit;
try rewrite formula_sub_false;
reflexivity.
Qed.

Lemma batch_app_split :
    forall (gamma1 gamma2 : list formula) (A1 A2 : formula) (S1 S2 : subst_ind),
        length gamma1 = length S1 ->
            length gamma2 = length S2 ->
                batch_sub (gamma1 ++ gamma2) A1 A2 (S1 ++ S2) = batch_sub gamma1 A1 A2 S1 ++ batch_sub gamma2 A1 A2 S2.
Proof.
induction gamma1;
intros gamma2 A1 A2 S1 S2 EQ1 EQ2;
destruct S1;
inversion EQ1 as [EQ].
reflexivity.
unfold batch_sub.
rewrite !app_length, EQ1, EQ2, !nat_eqb_refl, <- !app_comm_cons.
unfold batch_sub_fit;
fold batch_sub_fit.
rewrite !batch_sub_fit_true, IHgamma1.
reflexivity.
5 : rewrite !app_length.
all : try rewrite EQ;
      try rewrite EQ2;
      try rewrite nat_eqb_refl;
      reflexivity.
Qed.

Lemma batch_bury_comm_aux :
    forall (n : nat) (LF : list formula) (S : subst_ind) (A1 A2 : formula),
        bury (batch_sub LF A1 A2 S) n = batch_sub (bury LF n) A1 A2 (bury S n).
Proof.
induction n;
intros LF LS A v;
unfold batch_sub;
rewrite !bury_length;
case (nat_eqb (length LF) (length LS)) eqn:EQ;
try reflexivity;
destruct LF;
destruct LS;
try inversion EQ as [EQ'];
unfold bury;
fold @bury;
unfold batch_sub_fit;
fold batch_sub_fit;
unfold bury;
fold @bury;
try rewrite !batch_sub_fit_true;
try rewrite !batch_app_split;
try rewrite !bury_length;
try apply (nat_eqb_eq _ _ EQ');
try rewrite !app_length;
try apply EQ';
try rewrite batch_sub_single;
try rewrite IHn;
try reflexivity.

unfold length;
fold (@length formula);
fold (@length bool).
rewrite <- !plus_n_Sm, <- !plus_n_O.
apply EQ.
Qed.

Lemma batch_bury_comm :
    forall (LF : list formula) (LS : subst_ind) (n : nat) (A1 A2 : formula),
        bury (batch_sub LF A1 A2 (unbury LS n)) n = batch_sub (bury LF n) A1 A2 LS.
Proof.
intros LF LS n A1 A2.
rewrite <- (@bury_unbury _ LS n) at 2.
apply batch_bury_comm_aux.
Qed.

(*
Lemma sub_fit_true :
    forall (L : list formula) (D E : formula) (S : subst_ind),
        subst_ind_fit L S = true ->
            formula_sub_ind L D E S = formula_sub_ind_fit L D E S.
Proof.
intros L D E S FS.
unfold formula_sub_ind.
rewrite FS.
reflexivity.
Qed.

Lemma sub_fit_false :
    forall (L : list formula) (D E : formula) (S : subst_ind),
        subst_ind_fit L S = false ->
            formula_sub_ind L D E S = L.
Proof.
intros L D E S FS.
unfold formula_sub_ind.
rewrite FS.
reflexivity.
Qed.
*)

(*
Lemma formula_sub_ind_fit_0 :
    forall (L : list formula) (D E : formula),
        formula_sub_ind_fit L D E [] = L.
Proof.
intros L D E.
destruct L;
reflexivity.
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
*)

(*
Lemma non_target_eq_sub_non_target :
    forall (L : list formula) (n : nat) (t : term),
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
*)