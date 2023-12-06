From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import constraints.

Require Import Lia.
Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.EqdepFacts.

Open Scope bool_scope.
Open Scope list_scope.

Import ListNotations.

(*Language*)

Inductive predicate : Type :=
| Nullary : forall (i : nat), predicate
| Var : forall (i : nat), predicate.

Definition pure_predicate (pn : predicate) : bool :=
match pn with
| Nullary _ => true
| Var _ => false
end.

Inductive formula : Type :=
| fal : formula
| imp : formula -> formula -> formula
| bnd : ovar -> ovar -> formula -> formula
| prd : forall (pn : predicate), pure_predicate pn = true -> formula.
(*
| mu : forall n, (predicate n) -> formula -> formula
| muk : forall n, (predicate n) -> ordinal -> formula -> formula.
*)

Fixpoint num_conn (A : formula) : ordinal :=
match A with
| fal => cast Zero
| imp B C => oadd (oadd (num_conn B) (num_conn C)) (cast (nat_ord 1))
| bnd o1 o2 B => oadd (num_conn B) (cast (nat_ord 1))
| prd pn pure => cast Zero
end.

Fixpoint vars_in (a : formula) : list ovar :=
match a with
| fal => []
| imp B C => (vars_in B) ++ (vars_in C)
| bnd o1 o2 B => o2 :: remove nat_eq_dec o1 (vars_in B)
| prd pn pure => []
end.

Definition prd_eqb (pn1 pn2 : predicate) : bool :=
match pn1, pn2 with
| Nullary i1, Nullary i2 => nat_eqb i1 i2
| Var i1, Var i2 => nat_eqb i1 i2
| _, _ => false
end.

Fixpoint form_eqb (A1 A2 : formula) : bool :=
match A1, A2 with
| fal, fal => true
| imp B1 C1, imp B2 C2 => form_eqb B1 B2 && form_eqb C1 C2
| bnd o1 o2 B1, bnd o3 o4 B2 => nat_eqb o1 o3 && nat_eqb o2 o4 && form_eqb B1 B2
| prd pn1 _, prd pn2 _ => prd_eqb pn1 pn2
| _, _ => false
end.

Fixpoint form_depth (phi : formula) : nat :=
match phi with
| fal => 0
| imp B C => max (form_depth B) (form_depth C)
| bnd o1 o2 B => form_depth B
| prd pn pure => 0
end.

Lemma prd_eqb_sym :
    forall (pn1 pn2 : predicate),
        prd_eqb pn1 pn2 = prd_eqb pn2 pn1. 
Proof.
induction pn1;
destruct pn2;
unfold prd_eqb;
fold @prd_eqb;
subst;
try rewrite (nat_eqb_symm i i0);
reflexivity.
Qed.

Lemma prd_eqb_eq :
    forall (pn1 pn2 : predicate),
        prd_eqb pn1 pn2 = true ->
            pn1 = pn2.
Proof.
induction pn1;
destruct pn2;
intros EQ;
unfold prd_eqb in EQ;
try inversion EQ;
try apply nat_eqb_eq in EQ;
subst;
reflexivity.
Qed.

Lemma prd_eqb_refl :
    forall (pn : predicate),
        prd_eqb pn pn = true.
Proof.
destruct pn;
unfold prd_eqb;
fold @prd_eqb;
repeat rewrite nat_eqb_refl;
reflexivity.
Qed.

Definition prd_eq_dec : forall (a b : predicate), {a = b} + {a <> b}.
intros a b.
case (prd_eqb a b) eqn:EQ.
- left. apply prd_eqb_eq, EQ.
- right.
  intros FAL.
  subst.
  rewrite prd_eqb_refl in EQ.
  inversion EQ.
Qed.

Lemma form_eqb_eq :
    forall (A B : formula),
        form_eqb A B = true ->
            A = B.
Proof.
induction A;
intros B EQ;
destruct B;
inversion EQ as [EQ'];
repeat apply and_bool_prop in EQ as [EQ ?EQ];
try apply nat_eqb_eq in EQ as [];
try apply nat_eqb_eq in EQ0 as [];
try apply nat_eqb_eq in EQ1 as [].
- reflexivity.
- rewrite (IHA1 _ EQ),(IHA2 _ EQ0).
  reflexivity.
- rewrite (IHA _ EQ0).
  reflexivity.
- apply prd_eqb_eq in EQ'.
  subst.
  rewrite (UIP  _ _ _ e e0).
  reflexivity.
Qed.

Lemma form_eqb_refl : forall (a : formula), form_eqb a a = true.
Proof.
intros a.
induction a;
unfold form_eqb;
fold form_eqb;
repeat rewrite nat_eqb_refl;
try rewrite IHa;
try rewrite IHa1;
try rewrite IHa2;
try rewrite prd_eqb_refl;
reflexivity.
Qed.

Definition form_eq_dec : forall (a b : formula), {a = b} + {a <> b}.
intros a b.
case (form_eqb a b) eqn:EQ.
- left. apply form_eqb_eq, EQ.
- right.
  intros FAL.
  subst.
  rewrite form_eqb_refl in EQ.
  inversion EQ.
Qed.