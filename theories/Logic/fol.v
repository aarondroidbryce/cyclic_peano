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
Inductive nvec : nat -> Type :=
| Null : nvec 0
| New : forall {m : nat}, nat -> nvec m -> nvec (S m).

Inductive predicate : nat -> Type :=
| Nullary : forall (i : nat), predicate 0
| Succary : forall {m : nat} (i : nat) (prd : predicate m), @predicate (S m)
| Var : forall {n : nat} (i : nat), predicate n.

Fixpoint pure_predicate {n : nat} (pn : predicate n) : bool :=
match pn with
| Nullary _ => true
| Succary _ pn' => pure_predicate pn'
| Var _ => false
end.

Inductive formula : Type :=
| fal : formula
| equ : ivar -> ivar -> formula
| imp : formula -> formula -> formula
| univ : formula -> formula
| bnd : ovar -> ovar -> formula -> formula
| prd : forall {n : nat} (vec : nvec n) (pn : predicate n), pure_predicate pn = true -> formula.
(*
| mu : forall n, (predicate n) -> formula -> formula
| muk : forall n, (predicate n) -> ordinal -> formula -> formula.
*)

Fixpoint num_conn (A : formula) : ordinal :=
match A with
| fal => cast Zero
| equ v1 v2 => cast Zero
| imp B C => oadd (oadd (num_conn B) (num_conn C)) (cast (nat_ord 1))
| univ B => oadd (num_conn B) (cast (nat_ord 1))
| bnd o1 o2 B => oadd (num_conn B) (cast (nat_ord 1))
| prd vec pn pure => cast Zero
end.

Fixpoint vars_in (a : formula) : list ovar :=
match a with
| fal => []
| equ v1 v2 => []
| imp B C => (vars_in B) ++ (vars_in C)
| univ B => (vars_in B)
| bnd o1 o2 B => o2 :: remove nat_eq_dec o1 (vars_in B)
| prd vec pn pure => []
end.

Fixpoint nvec_eqb {n1 n2 : nat} (vec1 : nvec n1) (vec2 : nvec n2) : bool :=
match vec1, vec2 with
| Null, Null => true (*nat_eqb m1 m2*)
| New m1 vec1', New m2 vec2' => nat_eqb m1 m2 && nvec_eqb vec1' vec2'
| _, _ => false
end.

Fixpoint prd_eqb {n1 n2 : nat} (pn1 : predicate n1) (pn2 : predicate n2) : bool :=
match nat_eqb n1 n2 with
| true => match pn1, pn2 with
    | Nullary i1, Nullary i2 => nat_eqb i1 i2
    | Succary i1 pn1', Succary i2 pn2'  => nat_eqb i1 i2 && prd_eqb pn1' pn2'
    | Var i1, Var i2 => nat_eqb i1 i2
    | _ , _ => false
    end
| false => false
end.

Fixpoint form_eqb (A1 A2 : formula) : bool :=
match A1, A2 with
| fal, fal => true
| equ v1 v2, equ v3 v4 => nat_eqb v1 v3 && nat_eqb v2 v4
| imp B1 C1, imp B2 C2 => form_eqb B1 B2 && form_eqb C1 C2
| univ B1, univ B2 => form_eqb B1 B2
| bnd o1 o2 B1, bnd o3 o4 B2 => nat_eqb o1 o3 && nat_eqb o2 o4 && form_eqb B1 B2
| prd vec1 pn1 _, prd vec2 pn2 _ => nvec_eqb vec1 vec2 && prd_eqb pn1 pn2
| _, _ => false
end.

(*
Fixpoint in_vecb {n : nat} (vec : nvec n) (i : ivar) : bool :=
match vec with
| Null => false
| New v vec' => nat_eqb v i || in_vecb vec' i
end.

Fixpoint free_var (phi : formula) (i : ivar) : bool :=
match phi with
| fal => false
| equ v1 v2 => nat_eqb v1 i || nat_eqb v2 i
| imp B C => free_var B i || free_var C i
| univ B => match i with
    | 0 => false
    | S n => free_var B n
    end
| bnd o1 o2 B => free_var B i
| prd vec pn pure => in_vecb vec i
end.
*)

Fixpoint form_depth (phi : formula) : nat :=
match phi with
| fal => 0
| equ v1 v2 => 0
| imp B C => max (form_depth B) (form_depth C)
| univ B => S (form_depth B)
| bnd o1 o2 B => form_depth B
| prd vec pn pure => 0
end.

Fixpoint vec_map {n : nat} (F : nat -> nat) (vec : nvec n) : nvec n :=
match vec with
| Null => Null
| New v vec' => New (F v) (vec_map F vec')
end.

(*
Fixpoint shift_subst (A : formula) (i1 i2 : ivar) : formula :=
match A with
| fal => fal
| equ v1 v2 =>
    match nat_semiconnex_type v1 i1, nat_semiconnex_type v2 i1 with
    | inl (inl GT1), inl (inl GT2) => equ (pred v1) (pred v2)
    | inl (inl GT1), inl (inr EQ2) => equ (pred v1) (v2 + i2)
    | inl (inl GT1), inr LT2 => equ (pred v1) v2
    | inl (inr EQ1), inl (inl GT2) => equ (v1 + i2) (pred v2)
    | inl (inr EQ1), inl (inr EQ2) => equ (v1 + i2) (v2 + i2)
    | inl (inr EQ1), inr LT2 => equ (v1 + i2) v2
    | inr LT1, inl (inl GT2) => equ v1 (pred v2)
    | inr LT1, inl (inr EQ2) => equ v1 (v2 + i2)
    | inr LT1, inr LT2 => equ v1 v2
    end
| imp B C => imp (shift_subst B i1 i2) (shift_subst C i1 i2) 
| univ B => univ (shift_subst B (S i1) i2)
| bnd o1 o2 B => bnd o1 o2 (shift_subst B i1 i2)
| prd vec pn pure =>
    prd
    (vec_map (fun n => match nat_semiconnex_type n i1 with
              | inl (inl GT) => (pred n)
              | inl (inr EQ) => (n + i2)
              | inr LT => n
              end) vec)
    pn pure
end.

Lemma shift_subst_lemma :
    forall (phi : formula) (i1 j1 i2 i3 : ivar),
        shift_subst (shift_subst A i1 i2) (i1 + j1) i3 = shift_subst (shift_subst A (S (i1 + j1)) i3) i1 (i2)
*)

Fixpoint shift_substitution (A : formula) (i1 i2 : ivar) : formula :=
match A with
| fal => fal
| equ v1 v2 => match nat_eqb v1 i1, nat_eqb v2 i1 with
    | true, true => equ (v1 + i2) (v2 + i2)
    | true, false => equ (v1 + i2) v2
    | false, true => equ v1 (v2 + i2)
    | false, false => equ v1 v2
    end
| imp B C => imp (shift_substitution B i1 i2) (shift_substitution C i1 i2)
| univ B => univ (shift_substitution B (S i1) i2)
| bnd o1 o2 B => bnd o1 o2 (shift_substitution B i1 i2)
| prd vec pn pure => prd (vec_map (fun n => if nat_eqb n i1 then n + i2 else n) vec) pn pure
end.


Fixpoint substitution_depth (A : formula) (depth : nat) (i1 i2 : ivar) : formula :=
match A with
| fal => fal
| equ v1 v2 => match nat_eqb v1 i1, nat_eqb v2 i1 with
    | true, true => equ i2 i2
    | true, false => equ i2 v2
    | false, true => equ v1 i2
    | false, false => equ v1 v2
    end
| imp B C => imp (substitution_depth B depth i1 i2) (substitution_depth C depth i1 i2)
| univ B =>
    (match nat_ltb depth i1, nat_ltb depth i2 with
    | true, true => univ (substitution_depth B (S depth) i1 i2)
    | _, _ => A
    end)
| bnd o1 o2 B => bnd o1 o2 (substitution_depth B depth i1 i2)
| prd vec pn pure => prd (vec_map (fun n => if nat_eqb n i1 then i2 else n) vec) pn pure
end.

Fixpoint substitution (A : formula) (i1 i2 : ivar) : formula :=
match A with
| fal => fal
| equ v1 v2 => match nat_eqb v1 i1, nat_eqb v2 i1 with
    | true, true => equ i2 i2
    | true, false => equ i2 v2
    | false, true => equ v1 i2
    | false, false => A
    end
| imp B C => imp (substitution B i1 i2) (substitution C i1 i2)
| univ B => univ (substitution B i1 i2)
| bnd o1 o2 B => bnd o1 o2 (substitution B i1 i2)
| prd vec pn pure => prd (vec_map (fun n => if nat_eqb n i1 then i2 else n) vec) pn pure
end.

Lemma vec_map_ext {n : nat} :
    forall (F G : nat -> nat),
        F = G ->
          forall (vec : nvec n),
              vec_map F vec = vec_map G vec.
Proof.
intros F G FEQ vec.
rewrite FEQ.
reflexivity.
Qed.

Lemma vec_map_id {n : nat} :
    forall (vec : nvec n),
              vec_map (fun n => n) vec = vec.
Proof.
induction vec.
reflexivity.
unfold vec_map;
fold @vec_map.
rewrite IHvec.
reflexivity.
Qed.

Lemma vec_map_app {n : nat} :
    forall (F G : nat -> nat) (vec : nvec n),
        vec_map F (vec_map G vec) = vec_map (fun n => (F (G n))) vec.
Proof.
intros F G.
induction vec.
reflexivity.
unfold vec_map;
fold @vec_map.
rewrite IHvec.
reflexivity.
Qed.

Lemma subst_depth_eq_refl : forall (A : formula) (n : nat) (i : ivar), substitution_depth A n i i = A.
Proof.
induction A;
intros n' iv;
unfold substitution_depth;
fold substitution_depth;
try rewrite IHA;
try rewrite IHA1;
try rewrite IHA2;
try reflexivity.
1 : case (nat_eqb i iv) eqn:EQ1;
    case (nat_eqb i0 iv) eqn:EQ2;
    try apply nat_eqb_eq in EQ1;
    try apply nat_eqb_eq in EQ2;
    subst;
    reflexivity.
1 : case (nat_ltb n' iv) eqn:EQ;
    reflexivity.
1 : assert ((fun n0 => if nat_eqb n0 iv then iv else n0) = (fun n => n)) as EQ.
    { apply functional_extensionality.
      intros x.
      case (nat_eqb x iv) eqn:EQ.
      apply nat_eqb_eq in EQ.
      rewrite EQ.
      all : reflexivity. }
    rewrite (vec_map_ext _ _ EQ), vec_map_id.
    reflexivity.
Qed.

Lemma subst_eq_refl : forall (A : formula) (i : ivar), substitution A i i = A.
Proof.
induction A;
intros iv;
unfold substitution;
fold substitution;
try rewrite IHA;
try rewrite IHA1;
try rewrite IHA2;
try reflexivity.
1 : case (nat_eqb i iv) eqn:EQ1;
    case (nat_eqb i0 iv) eqn:EQ2;
    try apply nat_eqb_eq in EQ1;
    try apply nat_eqb_eq in EQ2;
    subst;
    reflexivity.
1 : assert ((fun n0 => if nat_eqb n0 iv then iv else n0) = (fun n => n)) as EQ.
    { apply functional_extensionality.
      intros x.
      case (nat_eqb x iv) eqn:EQ.
      apply nat_eqb_eq in EQ.
      rewrite EQ.
      all : reflexivity. }
    rewrite (vec_map_ext _ _ EQ), vec_map_id.
    reflexivity.
Qed.

Lemma subst_forms_equiv_for_free_var_aux :
    forall (phi : formula) (v1 v2 : ivar) (n : nat),
        nat_ltb (form_depth phi + n) v1 = true ->
            nat_ltb (form_depth phi + n) v2 = true ->
                substitution_depth phi n v1 v2 = substitution phi v1 v2.
Proof.
induction phi;
intros v1 v2 n' FV1 FV2;
unfold substitution_depth;
fold substitution_depth;
unfold substitution;
fold substitution;
try reflexivity;
unfold form_depth in *;
fold form_depth in *;
apply nat_ltb_lt in FV1, FV2.
3 : rewrite IHphi.
2 : assert (n' < v1 /\ n' < v2) as [LT1 LT2].
2 : split; lia.
2 : rewrite (nat_lt_ltb _ _ LT1), (nat_lt_ltb _ _ LT2), IHphi.  
1 : rewrite IHphi1, IHphi2.
all : try reflexivity;
      apply nat_lt_ltb;
      lia.
Qed.

Lemma subst_forms_equiv_for_free_var :
    forall (phi : formula) (v1 v2 : ivar),
        nat_ltb (form_depth phi) v1 = true ->
            nat_ltb (form_depth phi) v2 = true ->
                substitution_depth phi 0 v1 v2 = substitution phi v1 v2.
Proof.
intros phi v1 v2 LT1 LT2.
apply subst_forms_equiv_for_free_var_aux;
rewrite <- plus_n_O.
apply LT1.
apply LT2.
Qed.

Lemma nvec_case :
    forall (n : nat) (P : nvec n -> Type),
        (forall (pf : n = 0),
            P (eq_rect 0 nvec Null n (eq_sym pf))) ->
        (forall (m i : nat) (vec : nvec m) (pf : n = S m), P (eq_rect (S m) nvec (New i vec) n (eq_sym pf))) ->
            (forall (vec : nvec n), P vec).
Proof.
intros n P BC IND vec.
induction vec.
apply (BC eq_refl).
apply (IND _ _ _ eq_refl).
Defined.

Lemma nvec_0_null : forall (vec : nvec 0), vec = Null.
Proof.
apply nvec_case.
- intros pf.
  subst.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in * by apply nat_eq_dec.
  reflexivity.
- intros i m vec pf.
  inversion pf.
Qed.

Lemma nvec_Sn_new : forall {n : nat} (vec : nvec (S n)), {subvec : nvec n & {m : nat & vec = New m subvec}}.
Proof.
intros n.
apply nvec_case.
- intros pf.
  inversion pf.
- intros i m vec pf.
  inversion pf as [pf'].
  subst.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in * by apply nat_eq_dec.
  apply (existT _ vec (existT _ m eq_refl)).
Defined.

Lemma nvec_eqb_eq :
    forall {n : nat} (vec1 vec2 : nvec n),
        nvec_eqb vec1 vec2 = true ->
            vec1 = vec2.
Proof.
induction n;
intros vec1 vec2 EQB.
- pose proof (nvec_0_null vec1).
  pose proof (nvec_0_null vec2).
  subst.
  reflexivity.
- pose proof (nvec_Sn_new vec1) as [vec3 [m1 EQ1]].
  pose proof (nvec_Sn_new vec2) as [vec4 [m2 EQ2]].
  subst.
  apply and_bool_prop in EQB as [EQ1 EQ2].
  apply nat_eqb_eq in EQ1.
  subst.
  rewrite (IHn _ _ EQ2).
  reflexivity.
Qed.

Lemma nvec_eqb_sym :
    forall {n1 n2 : nat} (vec1 : nvec n1) (vec2 : nvec n2),
        nvec_eqb vec1 vec2 = nvec_eqb vec2 vec1.
Proof.
induction n1;
destruct n2;
intros vec1 vec2;
try pose proof (nvec_0_null vec1);
try pose proof (nvec_0_null vec2);
try pose proof (nvec_Sn_new vec1) as [vec3 [m1 EQ1]];
try pose proof (nvec_Sn_new vec2) as [vec4 [m2 EQ2]];
subst;
try reflexivity.
unfold nvec_eqb;
fold @nvec_eqb.
rewrite nat_eqb_symm, IHn1.
reflexivity.
Qed.

Lemma nvec_eqb_refl :
    forall {n : nat} (vec : nvec n),
        nvec_eqb vec vec = true.
Proof.
induction n;
intros vec.
- pose proof (nvec_0_null vec).
  subst.
  reflexivity.
- pose proof (nvec_Sn_new vec) as [vec' [m EQ]].
  subst.
  unfold nvec_eqb;
  fold @nvec_eqb.
  rewrite nat_eqb_refl.
  rewrite IHn.
  reflexivity.
Qed.

Definition nvec_eq_dec {n : nat}: forall (a b : nvec n), {a = b} + {a <> b}.
intros a b.
case (nvec_eqb a b) eqn:EQ.
- left. apply nvec_eqb_eq, EQ.
- right.
  intros FAL.
  subst.
  rewrite nvec_eqb_refl in EQ.
  inversion EQ.
Qed.

Lemma nvec_eqb_type : 
    forall {n1 n2 : nat} (vec1 : nvec n1) (vec2 : nvec n2),
        nvec_eqb vec1 vec2 = true -> nat_eqb n1 n2 = true .
Proof.
intros n1 n2 vec1.
revert n2.
induction vec1;
intros n2 vec2 EQB;
destruct vec2;
unfold nvec_eqb in EQB.
- reflexivity.
- inversion EQB.
- inversion EQB.
- unfold nvec_eqb in EQB;
  fold @nvec_eqb in EQB.
  apply and_bool_prop in EQB as [EQB1 EQB2].
  apply (IHvec1 _ _ EQB2).
Qed.

Lemma pred_case :
    forall (n : nat) (P : predicate n -> Type),
        (forall (i : nat) (pf : n = 0),
            P (eq_rect _ predicate (Nullary i) _ (eq_sym pf))) ->
        (forall (m : nat) (i : nat) (prd : predicate m) (pf : n = S m),
            P (eq_rect _ predicate (Succary i prd) _ (eq_sym pf))) ->
        (forall (i : nat), P (Var i)) ->
            (forall (pn : predicate n), P pn).
Proof.
intros n P BC IND VARS pn.
induction pn.
apply (BC _ eq_refl).
apply (IND _ _ _ eq_refl).
apply VARS.
Qed.

Lemma prd_eqb_sym :
    forall {n1 n2 : nat} (pn1 : predicate n1) (pn2 : predicate n2),
        prd_eqb pn1 pn2 = prd_eqb pn2 pn1. 
Proof.
intros n1 n2 pn1.
revert n2.
induction pn1;
intros n2;
destruct pn2;
unfold prd_eqb;
fold @prd_eqb;
subst;
try rewrite !nat_eqb_refl;
try rewrite nat_eqb_symm;
try rewrite (nat_eqb_symm v v0);
try rewrite (nat_eqb_symm i i0);
try rewrite IHpn1;
reflexivity.
Qed.

Lemma prd_eqb_eq :
    forall {n : nat} (pn1 pn2 : predicate n),
        prd_eqb pn1 pn2 = true ->
            pn1 = pn2.
Proof.
intros n.
induction pn1;
intros pn2.
- apply (pred_case 0 (fun (pn2 : predicate 0) => prd_eqb (Nullary i) pn2 = true -> (Nullary i) = pn2)).
  + intros i1 pf EQB.
    rewrite pf in EQB.
    unfold eq_rect, eq_sym, prd_eqb, nat_eqb in EQB.
    apply nat_eqb_eq in EQB.
    subst.
    pose proof (UIP_refl _ _ pf).
    subst.
    reflexivity.
  + intros m i1 pn1 pf EQB.
    inversion pf.
  + intros i1 EQB.
    inversion EQB.
- apply (pred_case (S m) (fun (pn2 : predicate (S m)) => prd_eqb (Succary i pn1) pn2 = true -> (Succary i pn1) = pn2)).
  + intros i1 pf EQB.
    inversion pf.
  + intros m2 i2 pn3 pf EQB.
    inversion pf as [pf'].
    subst.
    pose proof (UIP_refl _ _ pf).
    subst.
    unfold eq_rect, eq_sym, prd_eqb in EQB;
    fold @prd_eqb in EQB.
    rewrite nat_eqb_refl in EQB.
    apply and_bool_prop in EQB as [EQ1 EQ2].
    apply nat_eqb_eq in EQ1.
    specialize (IHpn1 _ EQ2) as EQ3.
    subst.
    reflexivity.
  + intros i1 EQB.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl in EQB.
    inversion EQB.
- apply (pred_case n (fun (pn2 : predicate n) => prd_eqb (Var i) pn2 = true -> (Var i) = pn2)).
  + intros i1 pf EQB.
    subst.
    inversion EQB.
  + intros m i1 pn1 pf EQB.
    subst.
    unfold eq_rect, eq_sym, prd_eqb in EQB.
    rewrite nat_eqb_refl in EQB.
    inversion EQB.
  + intros i2 EQB.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl in EQB.
    apply nat_eqb_eq in EQB.
    subst.
    reflexivity.
Qed.

Lemma prd_eqb_refl :
    forall {n : nat} (pn : predicate n),
        prd_eqb pn pn = true.
Proof.
intros n pn.
induction pn;
unfold prd_eqb;
fold @prd_eqb;
repeat rewrite nat_eqb_refl;
try rewrite IHpn;
try reflexivity.
Qed.

Lemma prd_eqb_type : 
    forall {n1 n2 : nat} (pn1 : predicate n1) (pn2 : predicate n2),
        prd_eqb pn1 pn2 = true -> nat_eqb n1 n2 = true .
Proof.
intros n1 n2 pn1 pn2 EQB.
destruct pn1, pn2;
subst;
unfold prd_eqb, eq_rect, eq_sym in EQB;
fold @prd_eqb in EQB.
- reflexivity.
- inversion EQB.
- case (nat_eqb 0 n) eqn:EQ1;
  inversion EQB.
- inversion EQB.
- case (nat_eqb (S m) (S m0)) eqn:EQ1.
  reflexivity.
  inversion EQB.
- case (nat_eqb (S m) n) eqn:EQ1;
  inversion EQB.
- case (nat_eqb n 0) eqn:EQ1;
  inversion EQB.
- case (nat_eqb n (S m)) eqn:EQ1;
  inversion EQB.
- case (nat_eqb n n0) eqn:EQ1;
  inversion EQB;
  reflexivity.
Qed.

Definition prd_eq_dec {n : nat} : forall (a b : predicate n), {a = b} + {a <> b}.
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
- reflexivity.
- rewrite (IHA1 _ EQ),(IHA2 _ EQ0).
  reflexivity.
- rewrite (IHA _ EQ').
  reflexivity.
- rewrite (IHA _ EQ0).
  reflexivity.
- apply and_bool_prop in EQ' as [EQ1 EQ2].
  pose proof (prd_eqb_type _ _ EQ2) as EQ3.
  apply nat_eqb_eq in EQ3.
  subst.
  apply nvec_eqb_eq in EQ1.
  apply prd_eqb_eq in EQ2.
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
try reflexivity.
rewrite nvec_eqb_refl.
apply prd_eqb_refl.
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

Lemma shift_subst_neb_form_neb :
    forall (phi1 phi2 : formula) (v1 v2 : ivar),
        form_eqb (shift_substitution phi1 v1 v2) (shift_substitution phi2 v1 v2) = false ->
            form_eqb phi1 phi2 = false.
Proof.
induction phi1;
destruct phi2;
intros v1 v2 EQ;
unfold shift_substitution in *;
fold shift_substitution in *;
unfold form_eqb in *;
fold form_eqb in *;
try apply andb_false_elim in EQ as [EQ1 | EQ2];
try rewrite (IHphi1 _ _ _ EQ);
try rewrite (IHphi1 _ _ _ EQ2);
try rewrite (IHphi1_1 _ _ _ EQ1);
try rewrite (IHphi1_2 _ _ _ EQ2);
try rewrite EQ1;
try rewrite EQ2;
try rewrite andb_false_r;
try apply EQ;
try reflexivity.
- case (nat_eqb i v1) eqn:EQ1;
  case (nat_eqb i0 v1) eqn:EQ2;
  case (nat_eqb i1 v1) eqn:EQ3;
  case (nat_eqb i2 v1) eqn:EQ4;
  try apply nat_eqb_eq in EQ1;
  try apply nat_eqb_eq in EQ2;
  try apply nat_eqb_eq in EQ3;
  try apply nat_eqb_eq in EQ4;
  subst;
  unfold form_eqb in EQ;
  try rewrite nat_eqb_refl in *;
  try rewrite andb_true_l in *;
  try rewrite andb_true_r in *;
  try rewrite EQ;
  try rewrite EQ1;
  try rewrite EQ2;
  try rewrite nat_eqb_symm;
  try rewrite EQ3;
  try reflexivity.
  apply EQ4.
  rewrite (nat_eqb_symm i2 v1), EQ4.
  all : apply andb_false_r.
- case (nvec_eqb vec vec0) eqn:EQV.
  pose proof (nvec_eqb_type _ _ EQV) as EQN.
  apply nat_eqb_eq in EQN.
  subst.
  apply nvec_eqb_eq in EQV.
  subst.
  rewrite nvec_eqb_refl in EQ1.
  inversion EQ1.
  reflexivity.
Qed.

Fixpoint nvec_equiv {n1 n2 : nat} (vec1 : nvec n1) (vec2 : nvec n2) (diff : ivar) : bool :=
match vec1, vec2 with
| Null, Null => true
| New v1 vec1', New v2 vec2' => (nat_eqb v1 v2 || nat_eqb (v1 + diff) v2) && nvec_equiv vec1' vec2' diff
| _, _ => false
end.

Lemma nvec_equiv_0_eq {n : nat} :
    forall (vec1 vec2 : nvec n),
        nvec_equiv vec1 vec2 0 = true ->
            vec1 = vec2.
Proof.
induction vec1.
- apply (nvec_case _ (fun (vec2 : nvec 0) => nvec_equiv Null vec2 0 = true -> Null = vec2)).
  + intros pf EQ.
    rewrite (UIP_refl _ _ pf) in *.
    reflexivity.
  + intros m i vec pf EQ.
    inversion pf.
- apply (nvec_case _ (fun vec2 => nvec_equiv (New n vec1) vec2 0 = true -> (New n vec1) = vec2)).
  + intros pf EQ'.
    inversion pf.
  + intros m' i vec2 pf EQ.
    inversion pf as [pf'].
    subst.
    rewrite (UIP_refl _ _ pf) in *.
    unfold eq_rect, eq_sym in *.
    apply and_bool_prop in EQ as [EQ1 EQ2].
    rewrite <- plus_n_O, orb_diag in EQ1.
    apply nat_eqb_eq in EQ1.
    subst.
    rewrite (IHvec1 _ EQ2).
    reflexivity.
Qed.


Lemma nvec_equiv_0_eqb {n1 n2 : nat} :
    forall (vec1 : nvec n1) (vec2 : nvec n2),
        nvec_equiv vec1 vec2 0 = nvec_eqb vec1 vec2.
Proof.
intros vec1.
revert n2.
induction vec1;
induction vec2;
unfold nvec_equiv;
fold @nvec_equiv;
unfold nvec_eqb;
fold @nvec_eqb;
try rewrite <- plus_n_O, orb_diag;
try rewrite IHvec1;
try reflexivity.
Qed.

Lemma nvec_vec_map_shift {n : nat} :
    forall (vec : nvec n) (v1 v2 : ivar),
        nvec_equiv vec (vec_map (fun m => if nat_eqb m v1 then m + v2 else m) vec) v2 = true.
Proof.
induction vec;
intros v1 v2;
unfold vec_map;
fold @vec_map;
unfold nvec_equiv;
fold @nvec_equiv.
reflexivity.
rewrite IHvec.
case (nat_eqb n v1) eqn:EQ;
rewrite nat_eqb_refl;
try rewrite orb_true_r;
reflexivity.
Qed.

Lemma nvec_equiv_refl {n : nat} :
    forall (vec : nvec n) (diff: ivar),
        nvec_equiv vec vec diff = true.
Proof.
induction vec;
intros diff;
unfold nvec_equiv;
fold @nvec_equiv;
try rewrite IHvec;
try rewrite nat_eqb_refl;
reflexivity.
Qed.

Fixpoint form_equiv (A1 A2 : formula) (diff : ivar) : bool :=
match A1, A2 with
| fal, fal => true
| equ v1 v2, equ v3 v4 => (nat_eqb v1 v3 || nat_eqb (v1 + diff) v3) && (nat_eqb v2 v4 || nat_eqb (v2 + diff) v4)
| imp B1 C1, imp B2 C2 => form_equiv B1 B2 diff && form_equiv C1 C2 diff
| univ B1, univ B2 => form_equiv B1 B2 diff
| bnd lambda1 kappa1 B1, bnd lambda2 kappa2 B2 => nat_eqb lambda1 lambda2 && nat_eqb kappa1 kappa2 && form_equiv B1 B2 diff
| prd vec1 pn1 _, prd vec2 pn2 _ => nvec_equiv vec1 vec2 diff && prd_eqb pn1 pn2
| _, _ => false
end.

Lemma form_equiv_preserves_depth :
    forall (A1 A2 : formula) (d : nat),
        form_equiv A1 A2 d = true ->
            form_depth A1 = form_depth A2.
Proof.
induction A1;
destruct A2;
intros d EQ;
inversion EQ as [EQ'];
unfold form_depth;
fold form_depth;
try apply and_bool_prop in EQ' as [EQ1 EQ2];
try rewrite (IHA1 _ _ EQ');
try rewrite (IHA1 _ _ EQ2);
try rewrite (IHA1_1 _ _ EQ1);
try rewrite (IHA1_2 _ _ EQ2);
try reflexivity.
Qed.

Lemma form_equiv_preserves_ovars :
    forall (A1 A2 : formula) (d : nat),
        form_equiv A1 A2 d = true ->
            vars_in A1 = vars_in A2.
Proof.
induction A1;
destruct A2;
intros d EQ;
inversion EQ as [EQ'];
unfold vars_in;
fold vars_in;
repeat apply and_bool_prop in EQ' as [EQ' ?EQ];
try apply nat_eqb_eq in EQ';
try apply nat_eqb_eq in EQ1;
subst;
try rewrite (IHA1 _ _ EQ');
try rewrite (IHA1 _ _ EQ0);
try rewrite (IHA1_1 _ _ EQ');
try rewrite (IHA1_2 _ _ EQ0);
try reflexivity.
Qed.

Lemma form_equiv_0_eq : 
    forall (phi1 phi2 : formula),
        form_equiv phi1 phi2 0 = form_eqb phi1 phi2.
Proof.
induction phi1;
destruct phi2;
unfold form_equiv;
fold form_equiv;
unfold form_eqb;
fold form_eqb;
try rewrite IHphi1;
try rewrite IHphi1_1, IHphi1_2;
try rewrite nat_eqb_refl;
try rewrite nvec_equiv_0_eqb;
try rewrite <- !plus_n_O, !orb_diag;
reflexivity.
Qed.

Lemma form_equiv_diff_shift_subst :
    forall (phi : formula) (v1 v2 : ivar),
        form_equiv phi (shift_substitution phi v1 v2) v2 = true.
Proof. 
induction phi;
intros v1 v2;
unfold shift_substitution;
fold shift_substitution;
unfold form_equiv;
fold form_equiv;
try rewrite !nat_eqb_refl;
try rewrite prd_eqb_refl;
try rewrite IHphi;
try rewrite IHphi1, IHphi2;
try rewrite nvec_vec_map_shift;
try reflexivity.
case (nat_eqb i v1) eqn:EQ1;
case (nat_eqb i0 v1) eqn:EQ2;
try apply nat_eqb_eq in EQ1;
try apply nat_eqb_eq in EQ2;
subst;
try rewrite !nat_eqb_refl;
try rewrite !orb_true_l;
try rewrite !orb_true_r;
reflexivity.
Qed.

Lemma shift_subst_idem :
    forall (phi : formula) (v1 v2 : ivar),
        shift_substitution (shift_substitution phi v1 v2) v1 v2 = shift_substitution phi v1 v2.
Proof.
induction phi;
intros v1 v2;
unfold shift_substitution;
fold shift_substitution;
try rewrite IHphi;
try rewrite IHphi1, IHphi2;
try reflexivity.
- case (nat_eqb i v1) eqn:EQ1;
  case (nat_eqb i0 v1) eqn:EQ2;
  try apply nat_eqb_eq in EQ1;
  try apply nat_eqb_eq in EQ2;
  subst;
  unfold shift_substitution;
  fold shift_substitution;
  try rewrite EQ1;
  try rewrite EQ2;
  case (nat_eqb (v1 + v2) v1) eqn:EQ3;
  try apply nat_eqb_eq in EQ3;
  try rewrite !EQ3;
  reflexivity.
- rewrite vec_map_app.
  rewrite <- (vec_map_ext (fun n0 => if nat_eqb n0 v1 then n0 + v2 else n0)).
  reflexivity.
  apply functional_extensionality.
  intros m.
  case (nat_eqb m v1) eqn:EQ.
  + apply nat_eqb_eq in EQ;
    subst.
    destruct v2.
    rewrite <- !plus_n_O, nat_eqb_refl.
    reflexivity.
    case (nat_eqb (v1 + S v2) v1) eqn:EQ.
    apply nat_eqb_eq in EQ.
    rewrite !EQ.
    reflexivity.
    reflexivity.
  + rewrite EQ.
    reflexivity.
Qed.

Lemma form_equiv_refl :
    forall (phi : formula) (d : nat),
        form_equiv phi phi d = true.
Proof.
induction phi;
intros d;
unfold form_equiv;
fold form_equiv;
try rewrite !nat_eqb_refl;
try rewrite prd_eqb_refl;
try rewrite !orb_true_l;
try rewrite IHphi;
try rewrite IHphi1, IHphi2;
try rewrite nvec_equiv_refl;
try reflexivity.
Qed.

(*
Fixpoint sig_subst (a : formula) (sig : ovar -> ovar) : formula :=
match a with
| fal => fal
| equ v1 v2 => equ v1 v2
| imp a1 a2 =>  imp (sig_subst a1 sig) (sig_subst a2 sig)
| univ v a => univ v (sig_subst a sig)
| bnd o1 o2 a => bnd o1 (sig o2) (sig_subst a (fun o => if nat_eq_dec o o1 then o else sig o))
| prd pn pure => prd pn pure
end.

Lemma sig_subst_id :
    forall (phi : formula),
        sig_subst phi (fun o => o) = phi.
Proof.
induction phi;
unfold sig_subst;
fold sig_subst;
try reflexivity.
rewrite IHphi1, IHphi2.
reflexivity.
rewrite IHphi.
reflexivity.
assert ((fun o1 : ovar => if nat_eq_dec o1 o then o1 else o1) = fun o2 => o2) as FEQ.
{ apply functional_extensionality.
  intros o1.
  case nat_eq_dec;
  reflexivity. }
rewrite FEQ, IHphi.
reflexivity.
Qed.

Lemma sig_subst_ext :
    forall (phi : formula) (f g : ovar -> ovar),
        f = g ->
            sig_subst phi f = sig_subst phi g.
Proof.
intros phi f g FEQ.
rewrite FEQ.
reflexivity.
Qed.

Lemma sig_subst_coherent_bi_is_inj {OC1 OC2 : constraint} :
    forall (phi1 phi2 : formula) (sig : constraint_type OC1 -> constraint_type OC2),
        coherent_bijection sig ->
            incl (vars_in phi1) (OC_list OC1) ->
                incl (vars_in phi2) (OC_list OC1) ->
                    phi1 = phi2 <-> sig_subst phi1 (sig_generalise sig) = sig_subst phi2 (sig_generalise sig).
Proof.
induction phi1;
destruct phi2;
intros sig COH SUB1 SUB2;
split;
intros EQ;
try inversion EQ;
subst;
try reflexivity.
- rewrite (proj2 (IHphi1_1 phi2_1 sig COH (fun o IN => (SUB1 _ (in_or_app _ _ _ (or_introl IN)))) (fun o IN => (SUB2 _ (in_or_app _ _ _ (or_introl IN))))) H0).
  rewrite (proj2 (IHphi1_2 phi2_2 sig COH (fun o IN => (SUB1 _ (in_or_app _ _ _ (or_intror IN)))) (fun o IN => (SUB2 _ (in_or_app _ _ _ (or_intror IN))))) H1).
  reflexivity.
- rewrite (proj2 (IHphi1 phi2 sig COH (fun o IN => (SUB1 _ IN)) (fun o IN => (SUB2 _ IN))) H1).
  reflexivity.
- unfold vars_in in *;
  fold vars_in in *.
  unfold sig_generalise in H1.
  case (in_dec nat_eq_dec o0 (OC_list OC1)) as [IN1 | FAL].
  case (in_dec nat_eq_dec o2 (OC_list OC1)) as [IN2 | FAL].
  + apply constraint_type_eq_proj in H1.
    apply (coherent_bijective_is_injective _ COH) in H1.
    inversion H1.
    subst.
    pose proof (proof_irrelevance _ IN1 IN2).
    subst.
    assert (incl (vars_in phi1) (OC_list OC1)) as SUB1'.
    admit.
    assert (incl (vars_in phi2) (OC_list OC1)) as SUB2'.
    admit.
    case (in_dec nat_eq_dec o1 (OC_list OC1)) as [IN1 | NIN1].
    assert ((fun o : ovar => if nat_eq_dec o o1 then o else (sig_generalise sig o)) = sig_generalise (fun o => if nat_eq_dec (projT1 o) o1 then (existT (OC_elt OC2) (projT1 o) ((fst (fst (fst COH))) _)) else sig o)) as EQF.
    rewrite (proj2 (IHphi1 _ _ _ SUB1' SUB2')).
    admit.
  + contradiction (FAL (SUB2 _ (or_introl eq_refl))).
  + contradiction (FAL (SUB1 _ (or_introl eq_refl))).
Qed.
(*
Lemma sig_applicable_sig_inverse {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) :
    forall (phi : formula),
        incl (vars_in phi) (OC_list OC2) ->
            coherent_bijection sig -> 
                sig_subst (sig_subst phi (sig_inverse sig)) (sig_generalise sig) = phi.
Proof.
intros phi.
revert sig.
induction phi;
intros sig SUB COH;
try reflexivity.
- unfold sig_subst;
  fold sig_subst.
  unfold vars_in in *;
  fold vars_in in *.
  rewrite IHphi1, IHphi2;
  try assumption.
  reflexivity.
  refine (fun o IN => SUB _ (in_or_app _ _ _ (or_intror IN))).
  refine (fun o IN => SUB _ (in_or_app _ _ _ (or_introl IN))).
- unfold sig_subst;
  fold sig_subst.
  unfold vars_in in *;
  fold vars_in in *.
  rewrite IHphi.
  reflexivity.
  apply SUB.
  apply COH.
- unfold sig_subst;
  fold sig_subst.
  unfold vars_in in *;
  fold vars_in in *.
  rewrite (coherent_bijection_sig_inverse _ COH _ (SUB _ (or_introl eq_refl))).
  assert ((sig_subst (sig_subst phi (fun o1 : ovar => if nat_eq_dec o1 o then o1 else sig_inverse sig o1)) (fun o1 : ovar => if nat_eq_dec o1 o then o1 else sig_generalise sig o1)) = sig_subst phi (fun o1 : ovar => o1)) as EQ.
  { case (in_dec nat_eq_dec o (OC_list OC2)) as [IN | NIN].
    + assert ((fun o1 : ovar => if nat_eq_dec o1 o then o1 else sig_inverse sig o1) = sig_inverse (fun o1 : constraint_type OC1 => if nat_eq_dec (projT1 o1) o then (existT _ o IN) else sig o1)) as EQ1.
      { admit. }
      assert ((fun o1 : ovar => if nat_eq_dec o1 o then o1 else sig_generalise sig o1) = sig_generalise (fun o1 : constraint_type OC1 => if nat_eq_dec (projT1 o1) o then (existT _ o IN) else sig o1)) as EQ2.
      { admit. }
      rewrite EQ1, EQ2, IHphi, sig_subst_id.
      reflexivity.
      admit.
      destruct COH as [[[INJ SUR] REL_iff] PREC].
      repeat split.
      * intros lambda.
        case (nat_eq_dec (projT1 lambda) o) as [EQ | NE].
        apply IN.
        apply INJ.
      * intros [lambda IN'].
        case (nat_eq_dec lambda o) as [EQ | NE].
        --  refine (existT _ (existT _ o _) _).
            unfold projT1.
            case (nat_eq_dec o o) as [_ | FAL].
            subst.
            rewrite (proof_irrelevance _ IN IN').
            reflexivity.
            contradiction (FAL eq_refl).
        --  destruct (SUR (existT _ lambda IN')) as [[kappa IN''] EQ].
            refine (existT _ (existT _ kappa _) _).
            unfold projT1.
            rewrite EQ.
            
    + assert ((fun o1 : ovar => if nat_eq_dec o1 o then o1 else sig_inverse sig o1) = sig_inverse sig) as EQ1.
      { admit. }
      assert ((fun o1 : ovar => if nat_eq_dec o1 o then o1 else sig_generalise sig o1) = sig_generalise sig) as EQ2.
      { admit. }
      rewrite EQ1, EQ2, IHphi, sig_subst_id.
      reflexivity.
      admit.
      apply COH.
      
    admit. }
  rewrite EQ, sig_subst_id.
  reflexivity.
Admitted.
*)
*)