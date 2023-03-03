Require Import Lia.
Require Import Nat.
Require Import Wellfounded.
From Cyclic_PA.Casteran Require Import rpo.
From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import PA_cyclic.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
(*From Cyclic_PA.Logic Require Import cut_elim.
From Cyclic_PA.Logic Require Import Peano.*)

Fixpoint disjunction_of (A E : formula) : bool :=
match form_eqb A E with
| true => true
| false => match A with
  | lor B C =>
    (match form_eqb B E, form_eqb C E with
    | true, true => true
    | true, false => disjunction_of C E
    | false, true => disjunction_of B E
    | false, false => disjunction_of B E && disjunction_of C E
    end)
  | _ => false
  end
end.

Definition danger : formula := atom (equ zero (succ zero)).

Definition dangerous_disjunct (A : formula) : bool := disjunction_of A danger.

Lemma danger_swap :
    forall (A B : formula),
        dangerous_disjunct (lor A B) = dangerous_disjunct (lor B A).
Proof.
intros A B.
unfold dangerous_disjunct.
unfold disjunction_of; fold disjunction_of.
case (form_eqb A danger) eqn:X;
case (form_eqb B danger) eqn:X1;
case (disjunction_of A danger) eqn:X2;
case (disjunction_of B danger) eqn:X3;
unfold danger, "&&", form_eqb;
fold form_eqb;
reflexivity.
Qed.

Lemma danger_split :
    forall (A B : formula),
        dangerous_disjunct (lor A B) = dangerous_disjunct A && dangerous_disjunct B.
Proof.
intros A B.
unfold dangerous_disjunct.
unfold disjunction_of; fold disjunction_of.
unfold danger. 
unfold form_eqb; fold form_eqb.
fold danger.
case (form_eqb A danger) eqn:X;
case (form_eqb B danger) eqn:X1;
try apply form_eqb_eq in X;
try apply form_eqb_eq in X1;
try rewrite X;
try rewrite X1;
unfold danger;
unfold disjunction_of; fold disjunction_of;
try rewrite form_eqb_refl;
unfold "&&";
try reflexivity.
case (disjunction_of A (atom (equ zero (succ zero))));
reflexivity.
Qed.

Lemma danger_closed :
    forall A,
        dangerous_disjunct A = true ->
            closed A = true.
Proof.
intros A DA.
induction A.
2,4 : inversion DA.
- case (form_eqb (atom a) danger) eqn:X.
  + apply form_eqb_eq in X.
    rewrite X.
    unfold danger.
    unfold closed.
    unfold closed_a.
    unfold closed_t.
    unfold "&&".
    reflexivity.
  + unfold dangerous_disjunct in DA.
    unfold disjunction_of in DA.
    rewrite X in DA.
    inversion DA.
- rewrite danger_split in DA.
  destruct (and_bool_prop _ _ DA) as [DA1 DA2].
  unfold closed; fold closed.
  rewrite (IHA1 DA1).
  rewrite (IHA2 DA2).
  unfold "&&".
  reflexivity.
Qed.

Lemma not_closed_not_danger :
    forall A,
        closed A = false ->
            dangerous_disjunct A = false.
Proof.
intros A CA.
case (dangerous_disjunct A) eqn:DA.
2 : reflexivity. 
rewrite (danger_closed _ DA) in CA.
inversion CA.
Qed.

Lemma danger_not_deg_0 :
    forall P A d alpha,
        P_proves P A d alpha ->
            dangerous_disjunct A = true ->
                0 < d.
Proof.
intros P.
induction P.
3 : { intros A.
      induction A;
      intros d alpha [[[PF [PSV AX]] PD] PO] DA;
      unfold dangerous_disjunct in DA;
      unfold disjunction_of in DA;
      unfold ptree_formula,ptree_deg,ptree_ord in *;
      rewrite PF in *.
      - case (form_eqb (atom a) danger) eqn:EQB; inversion DA.
        unfold form_eqb, danger in EQB.
        apply atom_beq_eq in EQB.
        rewrite EQB in *.
        unfold node_extract, List.In in AX.
        contradict AX.
        intros FAL.
        pose proof (FAL (atom (equ zero (succ zero))) (or_introl eq_refl)) as NA.
        unfold PA_cyclic_axiom, correct_a, correctness, eval, nat_eqb in NA.
        inversion NA.
      - case (form_eqb (neg A) danger) eqn:Y.
        inversion Y.
        inversion DA.
      - unfold node_extract, List.In in AX.
        contradict AX.
        intros FAL.
        pose proof (FAL _ (or_introl eq_refl)) as NA.
        unfold PA_cyclic_axiom, correct_a, correctness, eval, nat_eqb in NA.
        inversion NA.
      - unfold node_extract, List.In in AX.
        contradict AX.
        intros FAL.
        pose proof (FAL _ (or_introl eq_refl)) as NA.
        unfold PA_cyclic_axiom, correct_a, correctness, eval, nat_eqb in NA.
        inversion NA. }

all : intros A d alpha [[[PF' [PSV AX]] PD'] PO'] DA;
      unfold ptree_formula,ptree_deg,ptree_ord,num_conn in *;
      fold ptree_formula ptree_deg ptree_ord num_conn in *.

18,19,20 : lia.

10-17 : rewrite <- PF' in DA.

11,13,15,17 : rewrite danger_split in DA;
              apply and_bool_prop in DA;
              destruct DA as [DA].

10-17 : unfold dangerous_disjunct in DA;
        unfold disjunction_of in DA;
        inversion DA.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3-8 : destruct PSV as [[[PF PSV] PD] PO].
9 : destruct PSV as [[[[PF FC] PSV] PD] PO].

all : apply (IHP (ptree_formula P) _ (ptree_ord P));
      repeat split;
      try apply PSV;
      try lia;
      rewrite <- PF' in DA;
      repeat rewrite danger_split in DA;
      try rewrite PF;
      try rewrite danger_swap;
      repeat rewrite danger_split;
      try apply AX.

8 : rewrite DA;
    unfold "&&";
    reflexivity.
  
1,3 : apply DA.

1 : apply PD'.

all : apply and_bool_prop in DA;
      destruct DA as [DA DA1].

- rewrite DA,DA1;
  unfold "&&";
  reflexivity.

- apply and_bool_prop in DA.
  destruct DA as [DA2 DA3].
  rewrite DA1,DA2,DA3.
  unfold "&&".
  reflexivity.

- apply and_bool_prop in DA.
  destruct DA as [DA2 DA3].
  rewrite DA1,DA2,DA3.
  unfold "&&".
  reflexivity.

- apply and_bool_prop in DA.
  destruct DA as [DA2 DA3].
  apply and_bool_prop in DA2. destruct DA2 as [DA2 DA4].
  rewrite DA1,DA2,DA3,DA4;
  unfold "&&";
  reflexivity.

- rewrite DA,DA1;
  unfold "&&";
  reflexivity.

- apply DA1.
Qed.

Lemma provable_not_danger :
    forall A d alpha,
        provable A d alpha ->
            dangerous_disjunct A = false.
Proof.
intros A d alpha X.
case (dangerous_disjunct A) eqn:Y.
- destruct (cut_elim _ _ _ X) as [beta [P HP]].
  pose proof (danger_not_deg_0 P A 0 beta HP Y) as Deg.
  inversion Deg.
- reflexivity.
Qed.

Lemma danger_not_provable' :
    forall A P,
        dangerous_disjunct A = true ->
            valid P ->
                form_eqb (ptree_formula P) A = false.
Proof.
intros A P DA PV.
case (form_eqb (ptree_formula P) A) eqn:Y.
- assert (provable (ptree_formula P) (ptree_deg P) (ptree_ord P)) as HP.
  { exists P. repeat split. apply PV. lia. }
  pose (provable_not_danger _ _ _ HP) as Danger.
  apply form_eqb_eq in Y.
  destruct Y.
  rewrite DA in Danger.
  inversion Danger.
- reflexivity.
Qed.

Lemma danger_not_provable :
    forall A,
        dangerous_disjunct A = true ->
            forall P d alpha, P_proves P A d alpha ->
                False.
Proof.
intros A DA P d alpha [[[PF PV] PD] PO].
pose proof (danger_not_provable' _ _ DA PV) as Danger.
destruct PF.
rewrite form_eqb_refl in Danger.
inversion Danger.
Qed.

Lemma danger_not_theorem :
    forall A,
        dangerous_disjunct A = true ->
            forall n alpha, PA_omega_theorem A n alpha ->
                False.
Proof.
intros A DA n alpha T.
apply (danger_not_provable _ DA _ _ _ (projT2(provable_theorem _ _ _ T))). 
Qed.

Lemma inconsistent_danger :
    forall A n1 n2 alpha1 alpha2,
        PA_omega_theorem A n1 alpha1 ->
            PA_omega_theorem (neg A) n2 alpha2 ->
                False.
Proof.
intros A n1 n2 alpha1 alpha2 T1 T2.
assert (closed danger = true) as CD.
{ unfold danger,closed, closed_a, closed_t, "&&".
  reflexivity. }
assert (dangerous_disjunct danger = true) as DD.
{ unfold dangerous_disjunct, disjunction_of, danger.
  rewrite form_eqb_refl.
  reflexivity. }
apply (danger_not_theorem _ DD _ _ (cut2 _ _ _ _ _ _ T1 (exchange1 _ _ _ _ (weakening (danger) _ _ _ CD T2)))).
Qed.

Lemma PA_Consistent :
    forall A,
        Peano_Theorems_Base A ->
            Peano_Theorems_Base (neg A) -> False.
Proof.
intros A T1 T2.
destruct (PA_Base_closed_PA_omega _  T1 czero) as [d1 [alpha1 T3]].
destruct (PA_Base_closed_PA_omega _  T2 czero) as [d2 [alpha2 T4]].
rewrite closure_neg in T4.
apply (inconsistent_danger _ _ _ _ _ T3 T4).
Qed.