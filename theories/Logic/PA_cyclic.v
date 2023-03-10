Require Import Lia.
Require Import Nat.
Require Import Wellfounded.
Require Import List.
Require Import Coq.Arith.Wf_nat.


From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.

Import ListNotations.

Notation nat_eq_dec := PeanoNat.Nat.eq_dec.

Definition PA_cyclic_axiom (A : formula) : bool :=
match A with
| atom a => correct_a a
| neg (atom a) => incorrect_a a
| _ => false
end.

Inductive PA_cyclic_pre : formula -> nat -> ord -> list formula -> Type :=
| deg_incr : forall {A : formula} (d d' : nat) {alpha : ord} {L : list formula},
    PA_cyclic_pre A d alpha L ->
    d' > d ->
    PA_cyclic_pre A d' alpha L

| ord_incr : forall {A : formula} {d : nat} (alpha beta : ord) {L : list formula},
    PA_cyclic_pre A d alpha L ->
    ord_lt alpha beta -> nf beta ->
    PA_cyclic_pre A d beta L

| axiom : forall (A : formula),
    PA_cyclic_pre A 0 Zero [A]

| exchange1 : forall {A B : formula} {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor A B) d alpha L ->
    PA_cyclic_pre (lor B A) d alpha L

| exchange2 : forall {C A B : formula} {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor (lor C A) B) d alpha L ->
    PA_cyclic_pre (lor (lor C B) A) d alpha L

| exchange3 : forall {A B D : formula} {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor (lor A B) D) d alpha L ->
    PA_cyclic_pre (lor (lor B A) D) d alpha L

| exchange4 : forall {C A B D : formula} {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor (lor (lor C A) B) D) d alpha L ->
    PA_cyclic_pre (lor (lor (lor C B) A) D) d alpha L

| contraction1 : forall {A : formula} {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor A A) d alpha L ->
    PA_cyclic_pre A d alpha L

| contraction2 : forall (A : formula) {D : formula} {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor (lor A A) D) d alpha L ->
    PA_cyclic_pre (lor A D) d alpha L

| weakening : forall (A : formula) {D : formula} {d : nat} {alpha : ord} {L : list formula} (FLSub : incl (free_list A) (flat_map free_list L)),
    PA_cyclic_pre D d alpha L ->
    PA_cyclic_pre (lor A D) d (ord_succ alpha) L

| demorgan1 : forall {A B : formula} {d1 d2 : nat}
                     {alpha1 alpha2 : ord} {L1 L2 : list formula},
    PA_cyclic_pre (neg A) d1 alpha1 L1 ->
    PA_cyclic_pre (neg B) d2 alpha2 L2 ->
    PA_cyclic_pre (neg (lor A B)) (max d1 d2) (ord_succ (ord_max alpha1 alpha2)) (L1 ++ L2)

| demorgan2 : forall {A B D : formula} {d1 d2 : nat} {alpha1 alpha2 : ord} {L1 L2 : list formula},
    PA_cyclic_pre (lor (neg A) D) d1 alpha1 L1 ->
    PA_cyclic_pre (lor (neg B) D) d2 alpha2 L2 ->
    PA_cyclic_pre (lor (neg (lor A B)) D)
                     (max d1 d2) (ord_succ (ord_max alpha1 alpha2)) (L1 ++ L2)

| negation1 : forall {A : formula} {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre A d alpha L ->
    PA_cyclic_pre (neg (neg A)) d (ord_succ alpha) L

| negation2 : forall {A D : formula} {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor A D) d alpha L ->
    PA_cyclic_pre (lor (neg (neg A)) D) d (ord_succ alpha) L

| quantification1 : forall {A : formula} {n : nat} {c : c_term}
                           {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (neg (substitution A n (projT1 c))) d alpha L ->
    PA_cyclic_pre (neg (univ n A)) d (ord_succ alpha) L

| quantification2 : forall {A D : formula} {n : nat} {c : c_term}
                           {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor (neg (substitution A n (projT1 c))) D) d alpha L ->
    PA_cyclic_pre (lor (neg (univ n A)) D) d (ord_succ alpha) L

| oneloop1 : forall {A : formula} {n : nat} {d1 d2 : nat} {alpha1 alpha2 : ord} (L1 L2 : list formula) (LSTC : free_list A = [n] \/ free_list A = []),
    PA_cyclic_pre (substitution A n zero) d1 alpha1 L1 ->
    PA_cyclic_pre (substitution A n (succ (var n))) d2 alpha2 L2 ->
    PA_cyclic_pre (univ n A) (max d1 d2) (ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1) ((remove form_eq_dec A L2) ++ L1)

| oneloop2 : forall {C A : formula} {n : nat} {d1 d2 : nat} {alpha1 alpha2 : ord} (L1 L2 : list formula) (LSTC : free_list A = [n] \/ free_list A = []) (CC : closed C = true),
    PA_cyclic_pre (lor C (substitution A n zero)) d1 alpha1 L1 ->
    PA_cyclic_pre (substitution A n (succ (var n))) d2 alpha2 L2 ->
    PA_cyclic_pre (lor C (univ n A)) (max d1 d2) (ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1) ((remove form_eq_dec A L2) ++ L1)

| oneloop3 : forall {A D : formula} {n : nat} {d1 d2 : nat} {alpha1 alpha2 : ord} (L1 L2 : list formula) (LSTC : free_list A = [n] \/ free_list A = []) (CD : closed D = true),
    PA_cyclic_pre (substitution A n zero) d1 alpha1 L1 ->
    PA_cyclic_pre (lor (substitution A n (succ (var n))) D) d2 alpha2 L2 ->
    PA_cyclic_pre (lor (univ n A) D) (max d1 d2) (ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1) ((remove form_eq_dec A L2) ++ L1)

| oneloop4 : forall {C A D : formula} {n : nat} {d1 d2 : nat} {alpha1 alpha2 : ord} (L1 L2 : list formula) (LSTC : free_list A = [n] \/ free_list A = []) (CC : closed C = true) (CD : closed D = true),
    PA_cyclic_pre (lor C (substitution A n zero)) d1 alpha1 L1 ->
    PA_cyclic_pre (lor (substitution A n (succ (var n))) D) d2 alpha2 L2 ->
    PA_cyclic_pre (lor (lor C (univ n A)) D) (max d1 d2) (ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1) ((remove form_eq_dec A L2) ++ L1)

| multloop1 : forall {A : formula} {n : nat} {d1 d2 : nat} {alpha1 alpha2 : ord} (L1 L2 : list formula) (LSTN : free_list A <> [n] /\ free_list A <> []),
    PA_cyclic_pre (substitution A n zero) d1 alpha1 L1 ->
    PA_cyclic_pre (substitution A n (succ (var n))) d2 alpha2 L2 ->
    PA_cyclic_pre (univ n A) (max d1 d2) (ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1) (((univ n A) :: remove form_eq_dec A L2) ++ L1)

| multloop2 : forall {C A : formula} {n : nat} {d1 d2 : nat} {alpha1 alpha2 : ord} (L1 L2 : list formula) (LSTN : (free_list A <> [n] /\ free_list A <> []) \/ closed C = false),
    PA_cyclic_pre (lor C (substitution A n zero)) d1 alpha1 L1 ->
    PA_cyclic_pre (substitution A n (succ (var n))) d2 alpha2 L2 ->
    PA_cyclic_pre (lor C (univ n A)) (max d1 d2) (ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1) (((univ n A) :: remove form_eq_dec A L2) ++ L1)

| multloop3 : forall {A D : formula} {n : nat} {d1 d2 : nat} {alpha1 alpha2 : ord} (L1 L2 : list formula) (LSTN : (free_list A <> [n] /\ free_list A <> []) \/ closed D = false),
    PA_cyclic_pre (substitution A n zero) d1 alpha1 L1 ->
    PA_cyclic_pre (lor (substitution A n (succ (var n))) D) d2 alpha2 L2 ->
    PA_cyclic_pre (lor (univ n A) D) (max d1 d2) (ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1) (((univ n A) :: remove form_eq_dec A L2) ++ L1)

| multloop4 : forall {C A D : formula} {n : nat} {d1 d2 : nat} {alpha1 alpha2 : ord} (L1 L2 : list formula) (LSTN : (free_list A <> [n] /\ free_list A <> []) \/ closed C = false \/ closed D = false),
    PA_cyclic_pre (lor C (substitution A n zero)) d1 alpha1 L1 ->
    PA_cyclic_pre (lor (substitution A n (succ (var n))) D) d2 alpha2 L2 ->
    PA_cyclic_pre (lor (lor C (univ n A)) D) (max d1 d2) (ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1) (((univ n A) :: remove form_eq_dec A L2) ++ L1)

| cut1 : forall (C A : formula) {d1 d2 : nat} {alpha1 alpha2 : ord} {L1 L2 : list formula},
    PA_cyclic_pre (lor C A) d1 alpha1 L1 ->
    PA_cyclic_pre (neg A) d2 alpha2 L2 ->
    PA_cyclic_pre C
                     (max (max d1 d2) (num_conn (neg A)))
                     (ord_succ (ord_max alpha1 alpha2))
                     (L1 ++ L2)

| cut2 : forall (A D : formula) {d1 d2 : nat} {alpha1 alpha2 : ord} {L1 L2 : list formula},
    PA_cyclic_pre A d1 alpha1 L1 ->
    PA_cyclic_pre (lor (neg A) D) d2 alpha2 L2 ->
    PA_cyclic_pre D
                     (max (max d1 d2) (num_conn (neg A)))
                     (ord_succ (ord_succ (ord_max alpha1 alpha2)))
                     (L1 ++ L2)

| cut3 : forall (C A D : formula) {d1 d2 : nat} {alpha1 alpha2 : ord} {L1 L2 : list formula},
    PA_cyclic_pre (lor C A) d1 alpha1 L1 ->
    PA_cyclic_pre (lor (neg A) D) d2 alpha2 L2 ->
    PA_cyclic_pre (lor C D)
                     (max (max d1 d2) (num_conn (neg A)))
                     (ord_succ (ord_max alpha1 alpha2))
                     (L1 ++ L2).

Inductive PA_cyclic_theorem : formula -> nat -> ord -> Type :=
| prune : forall {A : formula} {d : nat} {alpha : ord} {L : list formula}, PA_cyclic_pre A d alpha L -> (forall (B : formula), In B L -> PA_cyclic_axiom B = true) -> PA_cyclic_theorem A d alpha.

Definition true_theorem {A : formula} {d : nat} {alpha : ord} : PA_cyclic_theorem A d alpha -> {L : list formula & {X : PA_cyclic_pre A d alpha L & (forall (B : formula), In B L -> PA_cyclic_axiom B = true)}}.
Proof. intros T. inversion T. exists L, X. apply H. Defined.

Lemma associativity1 :
  forall (C A B : formula) {d : nat} {alpha : ord},
    PA_cyclic_theorem (lor (lor C A) B) d alpha ->
      PA_cyclic_theorem (lor C (lor A B)) d alpha.
Proof.
intros C A B d alpha T. apply true_theorem in T as [L [TS TA]].
apply (prune (exchange1 (exchange2 (exchange3 TS))) TA).
Qed.

Lemma associativity2 :
  forall (C A B : formula) {d : nat} {alpha : ord},
    PA_cyclic_theorem (lor C (lor A B)) d alpha ->
      PA_cyclic_theorem (lor (lor C A) B) d alpha.
Proof.
intros C A B d alpha T. apply true_theorem in T as [L [TS TA]].
apply (prune (exchange3 (exchange2 (exchange1 TS))) TA).
Qed.

Lemma passociativity1 :
  forall (C A B : formula) {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor (lor C A) B) d alpha L ->
      PA_cyclic_pre (lor C (lor A B)) d alpha L.
Proof.
intros C A B d alpha t T.
apply (exchange1 (exchange2 (exchange3 T))).
Qed.

Lemma passociativity2 :
  forall (C A B : formula) {d : nat} {alpha : ord} {L : list formula},
    PA_cyclic_pre (lor C (lor A B)) d alpha L ->
      PA_cyclic_pre (lor (lor C A) B) d alpha L.
Proof.
intros C A B d alpha t T.
apply (exchange3 (exchange2 (exchange1 T))).
Qed.

Lemma weakening_closed :
    forall {A D : formula} {d : nat} {alpha : ord} {L : list formula},
        closed A = true ->
            PA_cyclic_pre D d alpha L ->
                PA_cyclic_pre (lor A D) d (ord_succ alpha) L.
Proof.
intros A D d alpha L CA T.
refine (weakening _ _ T).
rewrite (closed_free_list _ CA).
intros f IN.
inversion IN.
Qed.

Lemma deg_monot :
  forall {A : formula} (d d' : nat) {alpha : ord},
      d' >= d ->
          PA_cyclic_theorem A d alpha ->
              PA_cyclic_theorem A d' alpha.
Proof.
intros A d d' alpha IE T. apply true_theorem in T as [L [TS TA]].
destruct (nat_ge_case_type _ _ IE) as [LT | EQ].

- apply (prune (deg_incr d d' TS LT) TA).

- destruct EQ.
  apply (prune TS TA).
Qed.

Lemma ord_nf_pre :
    forall {A : formula} {d : nat} (alpha : ord) {L : list formula},
        PA_cyclic_pre A d alpha L ->
            nf alpha.
Proof.
intros A d alpha L T.
induction T;
repeat apply nf_nf_succ;
try apply nf_ord_max;
try apply zero_nf;
try apply IHT;
try apply IHT1;
try apply IHT2;
try apply TA.

1 : apply n.

all : refine ((nf_add _ _ (nf_mult _ _ IHT2 _) IHT1));
      repeat apply single_nf;
      apply zero_nf.
Qed.

Lemma ord_nf :
    forall {A : formula} {d : nat} (alpha : ord),
        PA_cyclic_theorem A d alpha ->
            nf alpha.
Proof.
intros A d alpha T.
apply true_theorem in T as [L [TS TA]].
apply (ord_nf_pre _ TS).
Qed.

Lemma ord_monot : forall {A : formula} {d : nat} (alpha beta : ord),
  (((ord_lt alpha beta) /\ (nf beta)) + (alpha = beta)) ->
    PA_cyclic_theorem A d alpha ->
      PA_cyclic_theorem A d beta.
Proof.
intros A d alpha beta [[I N] | EQ] T.
apply true_theorem in T as [L [TS TA]].
- apply (prune (ord_incr alpha _ TS I N) TA).

- destruct EQ.
  apply T.
Qed.

Lemma axiom_atomic : forall (A : formula),
  PA_cyclic_axiom A = true ->
    (exists (a : atomic_formula), A = atom a) \/
    (exists (a : atomic_formula), A = neg (atom a)).
Proof.
intros.
destruct A; try inversion H.
- left. exists a. auto.
- right. destruct A; try inversion H.
  + exists a. auto.
Qed.

Lemma axiom_correct : forall (A : formula),
  PA_cyclic_axiom A = true ->
    (exists (a : atomic_formula), A = atom a /\ correct_a a = true) \/
    (exists (a : atomic_formula), A = neg (atom a) /\ incorrect_a a = true).
Proof.
intros.
destruct A; try inversion H.
- left. exists a. auto.
- right. destruct A; try inversion H.
  + exists a. auto.
Qed.

Lemma axiom_closed : forall (A : formula),
  PA_cyclic_axiom A = true -> closed A = true.
Proof.
intros.
apply axiom_correct in H. destruct H.
- destruct H as [ a [ HA Ha] ]. rewrite HA. unfold closed.
  apply correct_closed. apply Ha.
- destruct H as [ a [ HA Ha] ]. rewrite HA. unfold closed.
  apply incorrect_closed. apply Ha.
Qed.

Lemma valid_empty_free_list : 
    forall {L : list formula},
        (forall B, In B L -> PA_cyclic_axiom B = true) ->
            flat_map free_list L = [].
Proof.
induction L;
intros AX.
- reflexivity.
- unfold flat_map; fold (flat_map free_list).
  rewrite closed_free_list.
  + apply (IHL (fun B INB => AX B (or_intror INB))).
  + apply axiom_closed, AX, or_introl, eq_refl.
Qed.

Lemma valid_closed_formula : 
    forall {L : list formula} {A : formula},
        (forall B, In B L -> PA_cyclic_axiom B = true) ->
            incl (free_list A) (flat_map free_list L) ->
                closed A = true.
Proof.
intros L A AX SUB.
rewrite (valid_empty_free_list AX) in SUB.
apply free_list_closed.
destruct (free_list A).
- reflexivity.
- pose proof (SUB n (or_introl eq_refl)) as FAL.
  inversion FAL.
Qed.

Lemma pre_theorem_closed :
    forall {A : formula} {d : nat} {alpha : ord} {L : list formula},
        PA_cyclic_pre A d alpha L ->
            (forall B : formula, In B L -> PA_cyclic_axiom B = true) ->
                closed A = true.
Proof.
intros A d alpha L TS AX.
induction TS;
try apply IHTS;
try apply AX;
try apply INF;
try pose proof (IHTS AX) as IHC;
try pose proof (IHTS1 (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_introl INB)))) as IHC1;
try pose proof (IHTS2 (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_intror INB)))) as IHC2;
try apply IHC;
unfold closed in *;
fold closed in *;
repeat apply and_bool_prop in IHC as [IHC ?];
repeat apply and_bool_prop in IHC1 as [IHC1 ?];
repeat apply and_bool_prop in IHC2 as [IHC2 ?];
repeat apply andb_true_intro, conj;
auto.
  
- apply axiom_closed, AX, or_introl, eq_refl.

- apply (valid_closed_formula AX FLSub).

- apply (closed_sub_univ _ _ _ (projT2 c) IHC).

- apply (closed_sub_univ _ _ _ (projT2 c) IHC).

- destruct LSTC as [LSTn | LSTe].
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite LSTn in CA.
      inversion CA.
    * rewrite LSTn.
      rewrite nat_eqb_refl, list_eqb_refl.
      reflexivity.
  + rewrite (free_list_closed _ LSTe).
    reflexivity.

- destruct LSTC as [LSTn | LSTe].
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite LSTn in CA.
      inversion CA.
    * rewrite LSTn.
      rewrite nat_eqb_refl, list_eqb_refl.
      reflexivity.
  + rewrite (free_list_closed _ LSTe).
    reflexivity.

- destruct LSTC as [LSTn | LSTe].
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite LSTn in CA.
      inversion CA.
    * rewrite LSTn.
      rewrite nat_eqb_refl, list_eqb_refl.
      reflexivity.
  + rewrite (free_list_closed _ LSTe).
    reflexivity.

- destruct LSTC as [LSTn | LSTe].
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite LSTn in CA.
      inversion CA.
    * rewrite LSTn.
      rewrite nat_eqb_refl, list_eqb_refl.
      reflexivity.
  + rewrite (free_list_closed _ LSTe).
    reflexivity.

- pose proof (AX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (AX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (AX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (AX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (AX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (AX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (AX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

  - pose proof (AX _ (or_introl eq_refl)) as FAL.
  inversion FAL.
Qed.

Lemma theorem_closed : forall (A : formula) (d : nat) (alpha : ord),
  PA_cyclic_theorem A d alpha -> closed A = true.
Proof.
intros A d alpha T.
apply true_theorem in T as [L [TS TAX]].
induction TS;
try apply IHTS;
try apply TAX;
try apply INF;
try pose proof (IHTS TAX) as IHC;
try pose proof (IHTS1 (fun B INB => TAX B (proj2 (in_app_iff _ _ _) (or_introl INB)))) as IHC1;
try pose proof (IHTS2 (fun B INB => TAX B (proj2 (in_app_iff _ _ _) (or_intror INB)))) as IHC2;
try apply IHC;
unfold closed in *;
fold closed in *;
repeat apply and_bool_prop in IHC as [IHC ?];
repeat apply and_bool_prop in IHC1 as [IHC1 ?];
repeat apply and_bool_prop in IHC2 as [IHC2 ?];
repeat apply andb_true_intro, conj;
auto.
  
- apply axiom_closed, TAX, or_introl, eq_refl.

- apply (valid_closed_formula TAX FLSub).

- apply (closed_sub_univ _ _ _ (projT2 c) IHC).

- apply (closed_sub_univ _ _ _ (projT2 c) IHC).

- destruct LSTC as [LSTn | LSTe].
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite LSTn in CA.
      inversion CA.
    * rewrite LSTn.
      rewrite nat_eqb_refl, list_eqb_refl.
      reflexivity.
  + rewrite (free_list_closed _ LSTe).
    reflexivity.

- destruct LSTC as [LSTn | LSTe].
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite LSTn in CA.
      inversion CA.
    * rewrite LSTn.
      rewrite nat_eqb_refl, list_eqb_refl.
      reflexivity.
  + rewrite (free_list_closed _ LSTe).
    reflexivity.

- destruct LSTC as [LSTn | LSTe].
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite LSTn in CA.
      inversion CA.
    * rewrite LSTn.
      rewrite nat_eqb_refl, list_eqb_refl.
      reflexivity.
  + rewrite (free_list_closed _ LSTe).
    reflexivity.

- destruct LSTC as [LSTn | LSTe].
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite LSTn in CA.
      inversion CA.
    * rewrite LSTn.
      rewrite nat_eqb_refl, list_eqb_refl.
      reflexivity.
  + rewrite (free_list_closed _ LSTe).
    reflexivity.

- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.

- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.
Qed.

Lemma closed_sub_theorem :
  forall (A : formula) (n d : nat) (t : term) (alpha : ord),
    closed A = true ->
      PA_cyclic_theorem A d alpha ->
        PA_cyclic_theorem (substitution A n t) d alpha.
Proof.
intros A n d t alpha CA T.
rewrite closed_subst_eq.
apply T.
apply CA.
Qed.

Lemma LEM_atomic :
  forall (a : atomic_formula),
    closed_a a = true ->
      PA_cyclic_theorem (lor (neg (atom a)) (atom a)) 0 (ord_succ Zero).
Proof.
intros a HC.
destruct (correctness_decid _ HC) as [Cor | Inc].
- apply (@prune _ _ _ [atom a]).
  + fold (closed (neg (atom a))) in HC.
    apply (weakening_closed HC), axiom.
  + intros B INB.
    inversion INB as [EQ | FAL].
    * destruct EQ.
      apply Cor.
    * inversion FAL.
- apply (@prune _ _ _ [neg (atom a)]).
  + fold (closed (atom a)) in HC.
    apply exchange1, (weakening_closed HC), axiom.
  + intros B INB.
    inversion INB as [EQ | FAL].
    * destruct EQ.
      apply Inc.
    * inversion FAL.
Qed.


Lemma pre_LEM_atomic :
  forall (a : atomic_formula),
      PA_cyclic_pre (lor (neg (atom a)) (atom a)) 0 (ord_succ Zero) [atom a].
Proof.
intros a. (*weakening should be subset of flatmap freelist instead of closed*)
apply weakening, axiom.
unfold flat_map, free_list.
rewrite app_nil_r.
apply incl_refl.
Qed.

(*
Lemma pre_LEM_empty :
    forall {A : formula},
        ( free_list A = [] ->
            { L : list formula & (PA_cyclic_pre (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A) + (num_conn A)))) L)}) *
        ( forall (n : nat), free_list A = [n] ->
          { L : list formula & prod (PA_cyclic_pre (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A) + (num_conn A)))) L) (incl [n] (flat_map free_list L))}).
Proof.
induction A as [A IND] using (induction_ltof1 _ num_conn);
unfold ltof in IND.
destruct A as [a | A | A1 A2 | m A ];
split;
try intros n FL;
try intros FL.
- unfold num_conn.
  rewrite <- plus_n_O.
  exists [atom a].
  apply pre_LEM_atomic.
- unfold num_conn.
  rewrite <- plus_n_O.
  exists [atom a].
  split.
  + apply pre_LEM_atomic.
  + unfold flat_map. rewrite FL.
    apply incl_refl.
- destruct (fst (IND A (le_n _)) FL) as [L T].
  unfold num_conn; fold num_conn.
  rewrite <- plus_n_Sm, <- ord_succ_nat, plus_Sn_m, <- ord_succ_nat.
  exists L.
  apply negation2, exchange1, (ord_incr _ _ T (ord_succ_monot _)).
  repeat rewrite ord_succ_nat.
  apply nf_nat.
- destruct (snd (IND A (le_n _)) _ FL) as [L [T INCL]].
  unfold num_conn; fold num_conn.
  rewrite <- plus_n_Sm, <- ord_succ_nat, plus_Sn_m, <- ord_succ_nat.
  exists L.
  split.
  + apply negation2, exchange1, (ord_incr _ _ T (ord_succ_monot _)).
    repeat rewrite ord_succ_nat.
    apply nf_nat.
  + apply INCL.
- assert (num_conn A1 < num_conn (lor A1 A2)) as IE1. {unfold num_conn. lia. }
  assert (num_conn A2 < num_conn (lor A1 A2)) as IE2. {unfold num_conn. lia. }
  assert (free_list A1 = []) as FL1.
  { unfold free_list in FL;
    fold free_list in FL.
    apply nodup_nil in FL.
    apply app_eq_nil in FL.
    apply (proj1 FL). }
  assert (free_list A2 = []) as FL2.
  { unfold free_list in FL;
    fold free_list in FL.
    apply nodup_nil in FL.
    apply app_eq_nil in FL.
    apply (proj2 FL). }
  assert ((max 0 0) = 0) as EQ. { lia. }
  destruct EQ.
  assert ((max (num_conn A1 + num_conn A1) (num_conn A2 + num_conn A2)) <= (num_conn A1 + num_conn A2 + (num_conn A1 + num_conn A2))) as IE. { lia. }
  destruct (fst (IND A1 IE1) FL1) as [L1 T1].
  destruct (fst (IND A2 IE2) FL2) as [L2 T2].
  apply (weakening A2), exchange1, passociativity1 in T1.
  apply (weakening A1), exchange1, passociativity1, exchange1, exchange3, exchange1 in T2.
  unfold num_conn; fold num_conn.
  rewrite <- plus_n_Sm, <- ord_succ_nat, plus_Sn_m, <- ord_succ_nat.
  pose proof (demorgan2 T1 T2) as T3.
  repeat rewrite ord_max_succ_succ in T3.
  rewrite ord_max_nat in T3.
  exists (L1 ++ L2).  
  apply nat_ge_case_type in IE as [GT | EQ].
  + refine (ord_incr _ _ T3 _ _).
    * apply ord_lt_succ, ord_lt_succ, ord_lt_succ, nat_ord_lt, GT. 
    * repeat apply nf_nf_succ.
      apply nf_nat.
  + rewrite EQ.
    apply T3.
  + rewrite FL1.
    apply incl_nil_l.
  + rewrite FL2.
    apply incl_nil_l.
- assert (num_conn A1 < num_conn (lor A1 A2)) as IE1. {unfold num_conn. lia. }
  assert (num_conn A2 < num_conn (lor A1 A2)) as IE2. {unfold num_conn. lia. }
  assert ((max 0 0) = 0) as EQ. { lia. }
  destruct EQ.
  assert ((max (num_conn A1 + num_conn A1) (num_conn A2 + num_conn A2)) <= (num_conn A1 + num_conn A2 + (num_conn A1 + num_conn A2))) as IE. { lia. }
  destruct (free_list_lor _ _ _ FL) as [[FL1 | FL1] [FL2 | FL2]];
  try apply closed_free_list in FL1;
  try apply closed_free_list in FL2.
  1 : destruct (snd (IND A1 IE1) _ FL1) as [L1 [T1 INCL1]];
      destruct (snd (IND A2 IE2) _ FL2) as [L2 [T2 INCL2]].
  2 : destruct (snd (IND A1 IE1) _ FL1) as [L1 [T1 INCL1]];
      destruct (fst (IND A2 IE2) FL2) as [L2 T2].
  3 : destruct (fst (IND A1 IE1) FL1) as [L1 T1];
      destruct (snd (IND A2 IE2) _ FL2) as [L2 [T2 INCL2]].
  4 : destruct (fst (IND A1 IE1) FL1) as [L1 T1];
      destruct (fst (IND A2 IE2) FL2) as [L2 T2].
  all : apply (weakening A2), exchange1, passociativity1 in T1.
  1,3,5,7 : apply (weakening A1), exchange1, passociativity1, exchange1, exchange3, exchange1 in T2.
  1,3,5,7 : unfold num_conn; fold num_conn;
            try rewrite <- plus_n_Sm, <- ord_succ_nat, plus_Sn_m, <- ord_succ_nat;
            pose proof (demorgan2 T1 T2) as T3;
            repeat rewrite ord_max_succ_succ in T3;
            rewrite ord_max_nat in T3;
            exists (L1 ++ L2);
            apply nat_ge_case_type in IE as [GT | EQ].
  2,4,6,8 : rewrite EQ; split; try apply T3.
  1,6-8 : split;
          try refine (ord_incr _ _ T3 _ _);
          try apply ord_lt_succ, ord_lt_succ, ord_lt_succ, nat_ord_lt, GT;
          repeat apply nf_nf_succ;
          try apply nf_nat.
  
  all : unfold flat_map; fold (flat_map free_list);
        try rewrite flat_map_app;
        try rewrite FL1; try rewrite FL2;
        try apply incl_nil_l;
        try apply (incl_appl _ INCL1);
        try apply (incl_appr _ INCL2); 
        try apply INCL1;
        try apply INCL2.
  
  + unfold free_list in FL; fold free_list in FL.
    rewrite FL1,FL2 in FL.
    inversion FL.
  + unfold free_list in FL; fold free_list in FL.
    rewrite FL1,FL2 in FL.
    inversion FL.
  + admit.
  + admit.
- assert ((free_list A = []) + {n : nat & free_list A = [n]}) as CASE.
  { pose proof (closed_univ _ _ (free_list_closed _ FL)). }
  destruct CASE as [FLe | [n FLn]].
  + destruct (fst (IND A (le_n _)) FLe) as [L T].
    exists (remove form_eq_dec A L ++ L).
    assert (ord_succ (nat_ord (num_conn (univ m A) + num_conn (univ m A))) = ord_add (ord_mult (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A)))) (wcon (wcon Zero 0 Zero) 0 Zero)) (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))) as FAKE.
    admit.
    rewrite FAKE.
    assert (max 0 0 = 0) as EQ. lia.
    rewrite <- EQ at 1.
    apply contraction2.
    apply exchange2.
    apply oneloop4.
    * right. apply FLe.
    * apply free_list_closed, FL.
    * apply free_list_closed, FL.
    * rewrite <- (closed_subst_eq _ m (projT1 czero)) in T.
      apply (quantification2 T).
      apply free_list_closed.
      simpl.
      rewrite FLe.
      reflexivity.
    * rewrite <- (closed_subst_eq (neg A) m (projT1 czero) (free_list_closed _ FLe)) in T.
      rewrite <- (closed_subst_eq A m (succ (var m)) (free_list_closed _ FLe)) in T at 2.
      apply exchange1, (quantification2 T). 
  + 
- admit.
Admitted.

Lemma pre_LEM :
    forall {A : formula} {n : nat},
        free_list A = [n] ->
            {L : list formula & (PA_cyclic_pre (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A) + (num_conn A)))) L)}.
Proof.
induction A as [A IND] using (induction_ltof1 _ num_conn);
unfold ltof in IND.
intros n FLn.
destruct A as [a | A | A1 A2 | m A ].
- unfold num_conn.
  rewrite <- plus_n_O.
  exists [atom a].
  apply pre_LEM_atomic.
- destruct (IND A (le_n _) n FLn) as [L T].
  unfold num_conn; fold num_conn.
  rewrite <- plus_n_Sm, <- ord_succ_nat, plus_Sn_m, <- ord_succ_nat.
  exists L.
  apply negation2, exchange1, (ord_incr _ _ T (ord_succ_monot _)).
  repeat rewrite ord_succ_nat.
  apply nf_nat.
- assert (num_conn A1 < num_conn (lor A1 A2)) as IE1. {unfold num_conn. lia. }
  assert (num_conn A2 < num_conn (lor A1 A2)) as IE2. {unfold num_conn. lia. }
  assert (free_list A1 = [n] \/ free_list A1 = []) as FL1.
  { destruct (free_list_lor _ _ _ FLn) as [[FL1 | FL1] _].
      * left. apply FL1.
      * right. apply closed_free_list, FL1. }
  assert (free_list A2 = [n] \/ free_list A2 = []) as FL2.
  { destruct FLn as [FLn | FLe].
    + destruct (free_list_lor _ _ _ FLn) as [_ [FL2 | FL2]].
      * left. apply FL2.
      * right. apply closed_free_list, FL2.
    + unfold free_list in FLe;
      fold free_list in FLe.
      apply nodup_nil in FLe.
      apply app_eq_nil in FLe.
      right.
      apply (proj2 FLe). }
  destruct (IND A1 IE1 _ FL1) as [L1 T1].
  destruct (IND A2 IE2 _ FL2) as [L2 T2].
  exists (L1 ++ L2).
  apply (weakening A2) in T1.
  admit.
  admit.

- admit.
Admitted.

Definition P1 (A : formula) : Type :=
  closed A = true ->
    PA_cyclic_theorem (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A) + (num_conn A)))).

Definition P2 (A : formula) (n : nat) : Type :=
  num_conn A = n -> P1 A.

Definition P3 (n : nat) : Type :=
  forall (A : formula), P2 A n.

Lemma P3_0 : P3 0.
Proof.
unfold P3, P2.
intros A NA.
destruct A as [a | | | ];
inversion NA.
unfold P1.
intros HC.
apply LEM_atomic.
apply HC.
Qed.

Lemma P3_strongind_aux :
  P3 0 ->
    (forall n, ((forall m, m <= n -> P3 m) -> P3 (S n))) ->
      (forall n m, m <= n -> P3 m).
Proof.
intros Ind0 Ind.
induction n as [ | n' IHn' ];
intros m IE.
- destruct m.
  + apply Ind0.
  + exfalso.
    inversion IE.
- destruct (nat_ge_case_type _ _ IE) as [LT | EQ].
  + apply IHn'.
    lia.
  + destruct EQ.
    apply (Ind _ IHn').
Qed.

Lemma P3_strongind :
  P3 0 ->
    (forall n, ((forall m, m <= n -> P3 m) -> P3 (S n))) ->
      (forall n, P3 n).
Proof.
intros Ind0 Ind n.
apply (P3_strongind_aux Ind0 Ind n n).
reflexivity.
Qed.

Lemma P3_inductive :
  forall n, (forall m, m <= n -> P3 m) ->
    P3 (S n).
Proof.
unfold P3,P2,P1. intros n Ind A NA CA.
destruct A as [a | B | B C | m B].

- inversion NA.

- inversion NA as [NA1].
  destruct (true_theorem (Ind _ (nat_le_refl _) _ NA1 CA)) as [L [T TAX]].
  refine (prune (ord_incr (ord_succ (ord_succ (nat_ord ((num_conn B) + (num_conn B))))) _ _ _ _) TAX).
  + apply negation2, exchange1, T.
  + apply ord_lt_succ.
    unfold num_conn. fold num_conn.
    repeat rewrite ord_succ_nat.
    apply nat_ord_lt.
    rewrite <- plus_n_Sm.
    unfold lt.
    reflexivity.
  + apply nf_nf_succ.
    apply nf_nat.

- destruct (closed_lor _ _ CA) as [CB CC].
  destruct (num_conn_lor _ _ _ NA) as [NB NC].
  pose proof (true_theorem (Ind (num_conn B) NB B (eq_refl (num_conn B)) CB)) as [L1 [T1 TAX1]].
  apply (weakening_closed CC) in T1.
  apply exchange1 in T1.
  apply passociativity1 in T1.
  pose proof (true_theorem (Ind (num_conn C) NC C (eq_refl (num_conn C)) CC)) as [L2 [T2 TAX2]].
  apply (weakening_closed CB) in T2.
  apply exchange1 in T2.
  apply exchange2 in T2.
  apply passociativity1 in T2.
  pose proof (demorgan2 T1 T2) as T3.
  case (num_conn C) eqn:X1;
  case (num_conn B) eqn:X2;
  unfold num_conn in *; fold num_conn in *;
  rewrite X1,X2.
  + unfold ord_max in T3.
    rewrite ord_ltb_irrefl in T3.
    apply (prune T3).
    intros D IND.
    apply in_app_iff in IND as [IND1 | IND2].
    * apply TAX1, IND1.
    * apply TAX2, IND2.
  + rewrite <- plus_n_O in *.
    repeat rewrite <- plus_n_Sm in *.
    repeat rewrite ord_succ_nat in *.
    rewrite ord_max_ltb_not_l in T3.
    * apply (prune T3).
      intros D IND.
      apply in_app_iff in IND as [IND1 | IND2].
      --  apply TAX1, IND1.
      --  apply TAX2, IND2.
    * apply ord_ltb_asymm.
      apply ord_lt_ltb.
      apply nat_ord_lt.
      lia.
  + unfold add in *. fold add in *.
    repeat rewrite <- plus_n_Sm in *.
    repeat rewrite ord_succ_nat in *.
    rewrite ord_max_symm in T3.
    rewrite ord_max_ltb_not_l in T3.
    * apply (prune T3).
      intros D IND.
      apply in_app_iff in IND as [IND1 | IND2].
      --  apply TAX1, IND1.
      --  apply TAX2, IND2.
    * apply ord_ltb_asymm.
      apply ord_lt_ltb.
      apply nat_ord_lt.
      lia.
  + unfold add in *; fold add in *.
    repeat rewrite <- plus_n_Sm in *.
    repeat rewrite ord_succ_nat in *.
    rewrite plus_assoc.
    rewrite plus_comm.
    rewrite plus_assoc.
    rewrite <- plus_n_Sm.
    rewrite (plus_comm n0).
    rewrite plus_comm.
    rewrite <- plus_n_Sm.
    rewrite plus_assoc.
    rewrite plus_assoc.
    rewrite <- (plus_assoc _ n0 n0).
    rewrite plus_n_Sm.
    rewrite plus_n_Sm.
    rewrite plus_comm.
    repeat rewrite plus_n_Sm in *.
    case (ord_ltb (nat_ord (n1 + S (S (S (S n1))))) (nat_ord (n0 + S (S (S (S n0)))))) eqn:X3.
    * rewrite (ord_max_ltb_is_r _ _ X3) in T3.
      refine (prune (ord_incr _ _ T3 _ _) _).
      --  repeat rewrite ord_succ_nat.
          apply nat_ord_lt.
          lia.
      --  apply nf_nat.
      --  intros D IND.
          apply in_app_iff in IND as [IND1 | IND2].
          ++  apply TAX1, IND1.
          ++  apply TAX2, IND2.
    * rewrite (ord_max_ltb_not_l _ _ X3) in T3. 
      refine (prune (ord_incr _ _ T3 _ _) _).
      --  repeat rewrite ord_succ_nat.
          apply nat_ord_lt.
          lia.
      --  apply nf_nat.
      --  intros D IND.
          apply in_app_iff in IND as [IND1 | IND2].
          ++  apply TAX1, IND1.
          ++  apply TAX2, IND2.

- inversion NA as [NB].
  rewrite <- NB in Ind.
  pose proof (true_theorem (Ind _ (nat_le_refl _) _ (num_conn_sub _ _ _) (closed_univ_sub _ _ CA _ (projT2 czero)))) as [L [T AX]].
  apply quantification2 in T.
  unfold num_conn. fold num_conn.
  rewrite <- plus_n_Sm.
  unfold "+". fold add.
  repeat rewrite <- ord_succ_nat.
  apply loop2.
  apply w_rule2.
  intros c.
  destruct NB.
  rewrite <- (num_conn_sub _ m (projT1 c)).
  apply exchange1.
  apply (quantification2 _ _ _ c).
  apply (Ind _ (nat_le_refl _) _ (num_conn_sub _ _ _) (closed_univ_sub _ _ CA _ (projT2 c))).
Qed.

Lemma P3_lemma :
  forall n, P3 n.
Proof.
apply P3_strongind.
apply P3_0.
apply P3_inductive.
Qed.

Lemma P2_lemma :
  forall (n : nat) (A : formula), P2 A n.
Proof.
apply P3_lemma.
Qed.

Lemma P1_lemma :
  forall (A : formula), P1 A.
Proof.
intros.
pose proof P2_lemma as Lemma.
unfold P2 in Lemma.
apply (Lemma (num_conn A) A).
reflexivity.
Qed.

Lemma LEM :
  forall (A : formula),
    closed A = true ->
      PA_cyclic_theorem (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A) + (num_conn A)))).
Proof.
intros A CA.
apply (P1_lemma A CA).
Qed.

*)

Lemma LEM_term_atomic' :
  forall (s t : term) (a : atomic_formula) (n : nat),
    correct_a (equ s t) = true ->
      PA_cyclic_axiom (substitution (atom a) n s) = true ->
        PA_cyclic_axiom (substitution (atom a) n t) = true.
Proof.
intros s t a n COR T.
unfold PA_cyclic_axiom in *.
unfold substitution in *.
unfold correct_a.
unfold correct_a in T.
case (correctness (substitution_a a n s)) eqn:COR1;
inversion T.
rewrite (eval_eq_subst_cor_eq _ s).
- reflexivity.
- apply (equ_cor_eval_eq _ _ COR).
- apply COR1. 
Qed.

Lemma LEM_term_atomic :
  forall (a : atomic_formula) (n : nat) (s t : term),
    correct_a (equ s t) = true ->
      free_list_a a = [n] ->
        PA_cyclic_theorem (lor (neg (atom (substitution_a a n s)))
                              (atom (substitution_a a n t)))
                          0 (ord_succ Zero).
Proof.
intros a n s t COR FREE.
destruct (correctness_decid (substitution_a a n s)) as [COR1 | COR1].
- apply one_var_free_lemma_a.
  + apply eval_closed.
    destruct (correct_eval s t COR) as [E1 E2].
    apply E1.
  + apply FREE.
- apply (@prune _ _ _ [atom (substitution_a a n t)]).
  apply weakening_closed.
  + apply correct_closed, COR1.
  + apply axiom.
  + intros B INB.
    destruct INB as [EQ | FAL].
    * destruct EQ.
      apply (LEM_term_atomic' _ _ _ _ COR COR1).
    * inversion FAL.
- apply (@prune _ _ _ [neg (atom (substitution_a a n s))]).
  + apply exchange1, weakening_closed.
    * apply (incorrect_subst_closed _ _ s).
      --  apply eval_closed.
          destruct (correct_eval s t COR) as [E1 E2].
          apply E2.
      --  apply COR1.
    * apply axiom.
  + intros B INB.
    destruct INB as [EQ | FAL].
    * destruct EQ.
      apply COR1.
    * inversion FAL.
Qed.

Definition Q1 (A : formula) : Type :=
  forall (n : nat) (s t : term),
    correct_a (equ s t) = true ->
      free_list A = [n] ->
        PA_cyclic_theorem (lor (neg (substitution A n s)) (substitution A n t))
                         0 (ord_succ (nat_ord ((num_conn A)+(num_conn A)))).

Definition Q2 (A : formula) (n : nat) : Type := num_conn A = n -> Q1 A.

Definition Q3 (m : nat) : Type := forall (A : formula), Q2 A m.

Lemma Q3_strongind_aux :
  Q3 0 ->
    (forall n, ((forall m, m <= n -> Q3 m) -> Q3 (S n))) ->
        (forall n m, m <= n -> Q3 m).
Proof.
intros Ind0 Ind.
induction n as [| n' IHn' ].

- intros m I. 
  assert (0 = m) as Z.
  { inversion I. reflexivity. }
  destruct Z.
  apply Ind0.

- intros m I.
  destruct (nat_ge_case_type _ _ I) as [I1 | I1].
  + apply IHn'.
    lia.
+ destruct I1.
  apply Ind.
  apply IHn'.
Qed.

Lemma Q3_strongind :
  Q3 0 ->
    (forall n, ((forall m, m <= n -> Q3 m) -> Q3 (S n))) ->
      (forall n, Q3 n).
Proof.
intros Ind0 Ind n.
apply (Q3_strongind_aux Ind0 Ind n n).
reflexivity.
Qed.

Lemma Q3_0 : Q3 0.
Proof.
unfold Q3, Q2. intros A NA.
destruct A as [a | | | ];
inversion NA.
unfold Q1.
intros n s t COR LIST.
apply (LEM_term_atomic _ _ _ _ COR LIST).
Qed.  

(*
Lemma Q3_inductive :
  forall n, (forall m, m <= n -> Q3 m) -> Q3 (S n).
Proof.
unfold Q3,Q2,Q1. intros n Ind A NA i s t COR LIST.
apply prune.
destruct A as [| B | B C | m B].

- inversion NA.

- inversion NA as [NB].
  apply negation2.
  fold substitution.
  apply exchange1.
  unfold num_conn. fold num_conn.
  apply (ord_incr (ord_succ (nat_ord ((num_conn B)+(num_conn B))))).
  + apply (true_theorem (Ind _ (nat_le_refl _) _ NB _ _ _ (correct_atom_symm _ _ COR) LIST)).
  + repeat rewrite ord_succ_nat.
    apply nat_ord_lt.
    lia.
  + apply nf_nat.

- destruct (num_conn_lor _ _ _ NA) as [NB NC].
  destruct (correct_closed_t _ _ COR) as [CS CT].
  pose proof (subst_remove (lor B C) i _ CT) as LISTSUB.
  rewrite LIST in LISTSUB.
  unfold remove in LISTSUB.
  case (nat_eq_dec i i) as [_ | FAL].
  apply free_list_closed, and_bool_prop in LISTSUB as [CB CC].
  case (ord_eqb (ord_succ (ord_max (ord_succ (ord_succ (nat_ord (num_conn B + num_conn B)))) (ord_succ (ord_succ (nat_ord (num_conn C + num_conn C)))))) (ord_succ (nat_ord (num_conn (lor B C) + num_conn (lor B C))))) eqn:X1.
  + apply ord_eqb_eq in X1.
    destruct X1.
    assert (0 = max 0 0) as EQ. reflexivity.
    rewrite EQ, <- app_nil_l.
    apply demorgan2.
    * rewrite  <- (closed_free_list _ CC), <- app_nil_l.
      apply passociativity1, exchange1, weakening.
      destruct (free_list_lor B C i LIST) as [[LISTB | LISTB] [LISTC | LISTC]].
      --  apply (true_theorem (Ind (num_conn B) NB B (eq_refl (num_conn B)) _ _ _ COR LISTB)).
      --  apply (true_theorem (Ind (num_conn B) NB B (eq_refl (num_conn B)) _ _ _ COR LISTB)).
      --  repeat rewrite (closed_subst_eq _ _ _ LISTB).
          (* apply (LEM B LISTB). *) admit.
      --  repeat rewrite (closed_subst_eq _ _ _ LISTB).
          (* apply (LEM B LISTB). *) admit.
    * rewrite  <- (closed_free_list _ CB), <- app_nil_l.
      apply passociativity1, exchange2, exchange1, weakening.
      destruct (free_list_lor B C i LIST) as [[LISTB | LISTB] [LISTC | LISTC]].
      --  apply (true_theorem (Ind (num_conn C) NC C (eq_refl (num_conn C)) _ _ _ COR LISTC)).
      --  repeat rewrite (closed_subst_eq _ _ _ LISTC).
          (* apply (LEM C LISTC). *) admit.
      --  apply (true_theorem (Ind (num_conn C) NC C (eq_refl (num_conn C)) _ _ _ COR LISTC)).
      --  repeat rewrite (closed_subst_eq _ _ _ LISTC).
          (* apply (LEM C LISTC). *) admit.

  + unfold substitution. fold substitution.
    rewrite <- app_nil_l.
    refine (ord_incr _ _ (@demorgan2 _ _ (lor (substitution B i t) (substitution C i t)) 0 0 _ _ _ _ _ _) _ _).
    * rewrite  <- (closed_free_list _ CC), <- app_nil_l.
      apply passociativity1, exchange1, weakening.
      destruct (free_list_lor B C i LIST) as [[LISTB | LISTB] [LISTC | LISTC]].
      --  apply (true_theorem (Ind (num_conn B) NB B (eq_refl (num_conn B)) _ _ _ COR LISTB)).
      --  apply (true_theorem (Ind (num_conn B) NB B (eq_refl (num_conn B)) _ _ _ COR LISTB)).
      --  repeat rewrite (closed_subst_eq _ _ _ LISTB).
          (* apply (LEM B LISTB). *) admit.
      --  repeat rewrite (closed_subst_eq _ _ _ LISTB).
          (* apply (LEM B LISTB). *) admit.
    * rewrite  <- (closed_free_list _ CB), <- app_nil_l.
      apply passociativity1, exchange2, exchange1, weakening.
      destruct (free_list_lor B C i LIST) as [[LISTB | LISTB] [LISTC | LISTC]].
      --  apply (true_theorem (Ind (num_conn C) NC C (eq_refl (num_conn C)) _ _ _ COR LISTC)).
      --  repeat rewrite (closed_subst_eq _ _ _ LISTC).
          (* apply (LEM C LISTC). *) admit.
      --  apply (true_theorem (Ind (num_conn C) NC C (eq_refl (num_conn C)) _ _ _ COR LISTC)).
      --  repeat rewrite (closed_subst_eq _ _ _ LISTC).
          (* apply (LEM C LISTC). *) admit.
    * rewrite <- ord_max_succ_succ in *.
      repeat rewrite ord_succ_nat in *.
      rewrite ord_max_nat in *.
      apply nat_ord_lt.
      unfold num_conn in *. fold num_conn in *.
      unfold max in *. fold max in *.
      rewrite <- plus_n_Sm in *.
      unfold nat_ord in X1.
      unfold ord_eqb in X1.
      destruct (num_conn B);
      destruct (num_conn C);
      unfold add in *; fold add in *;
      unfold max in *; fold max in *;
      try rewrite <- plus_n_O in *;
      try rewrite nat_eqb_refl in X1; inversion X1.
      lia.
    * rewrite ord_succ_nat.
      apply nf_nat.
  + contradict FAL.
    reflexivity.
  
- apply exchange1.
  inversion NA as [NB].
  unfold substitution. fold substitution.
  pose proof (univ_free_var _ _ _ LIST) as Heq.
  rewrite Heq.
  unfold num_conn. fold num_conn.
  rewrite <- plus_n_Sm.
  rewrite plus_comm.
  rewrite <- plus_n_Sm.
  repeat rewrite <- ord_succ_nat.s
  apply w_rule2.
  intros c.
  apply exchange1.
  apply (quantification2 _ _ _ c).
  destruct (correct_closed_t _ _ COR) as [CS CT].
  rewrite (substitution_order B m i s _ CS (projT2 c) Heq).
  rewrite (substitution_order B m i t _ CT (projT2 c) Heq).
  rewrite <- (num_conn_sub B m (projT1 c)).
  apply (Ind n (nat_le_refl n) (substitution B m (projT1 c))).
  + rewrite num_conn_sub.
    apply NB.
  + apply COR.
  + apply free_list_univ_sub.
    * destruct c as [c CC].
      unfold projT1.
      apply CC.
    * apply LIST.
Qed.

Lemma Q3_lemma : forall n, Q3 n.
Proof.
apply Q3_strongind.
apply Q3_0.
apply Q3_inductive.
Qed.

Lemma Q2_lemma : forall (n : nat) (A : formula), Q2 A n.
Proof.
apply Q3_lemma.
Qed.

Lemma Q1_lemma : forall (A : formula), Q1 A.
Proof.
intros.
pose proof (Q2_lemma) as LEMMA.
unfold Q2 in LEMMA.
apply (LEMMA (num_conn A) A).
reflexivity.
Qed.

Lemma LEM_term :
  forall (A : formula) (n : nat) (s t : term),
    correct_a (equ s t) = true ->
      free_list A = [n] ->
        PA_cyclic_theorem (lor (neg (substitution A n s)) (substitution A n t))
                         0 (ord_succ (nat_ord ((num_conn A)+(num_conn A)))).
Proof.
apply Q1_lemma.
Qed.
*)
