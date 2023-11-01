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
| New : forall (i : nat), nat -> nvec i -> nvec (S i).

Inductive predicate {n : nat} : nvec n -> Type :=
| Nullary : forall (i : nat) (pf : n = 0), predicate (eq_rect _ _ Null _ (eq_sym pf))
| Succary : forall {m : nat} {vec : nvec m} (i : nat) (v : ivar) (prd : predicate vec) (pf : n = S m), predicate (eq_rect _ _ (New m v vec) _ (eq_sym pf))
| Var : forall {vec : nvec n} (i : nat), predicate vec.

Fixpoint pure_predicate {n : nat} {vec : nvec n} (pn : predicate vec) : bool :=
match pn with
| Nullary _ _ => true
| Succary _ _ pn' _ => pure_predicate pn'
| Var _ => false
end.

(*
Inductive predicate : nat -> Type :=
| Nullary : forall (n : nat), predicate 0
| Succary : forall {i : nat} (n : nat) (v : ivar) (prd : predicate i), predicate (S i).
*)

Inductive formula : Type :=
| fal : formula
| equ : ivar -> ivar -> formula
| imp : formula -> formula -> formula
| univ : ivar -> formula -> formula
| bnd : ovar -> ovar -> formula -> formula
| prd : forall {n : nat} {vec : nvec n} (pn : predicate vec), pure_predicate pn = true -> formula.
(*
| mu : forall n, (predicate n) -> formula -> formula
| muk : forall n, (predicate n) -> ordinal -> formula -> formula.
*)



Fixpoint num_conn (A : formula) : ordinal :=
match A with
| fal => cast Zero
| equ v1 v2 => cast Zero
| imp B C => oadd (oadd (num_conn B) (num_conn C)) (cast (nat_ord 1))
| univ v B => oadd (num_conn B) (cast (nat_ord 1))
| bnd o1 o2 B => oadd (num_conn B) (cast (nat_ord 1))
| prd pn pure => cast Zero
end.

Fixpoint vars_in (a : formula) : list ovar :=
match a with
| fal => []
| equ v1 v2 => []
| imp B C => (vars_in B) ++ (vars_in C)
| univ v B => (vars_in B)
| bnd o1 o2 B => o2 :: remove nat_eq_dec o1 (vars_in B)
| prd pn pure => []
end.

Fixpoint nvec_eqb {n1 n2 : nat} (vec1 : nvec n1) (vec2 : nvec n2) : bool :=
match vec1, vec2 with
| Null, Null => true (*nat_eqb m1 m2*)
| New _ m1 vec1', New _ m2 vec2' => nat_eqb m1 m2 && nvec_eqb vec1' vec2'
| _, _ => false
end.

Fixpoint prd_eqb {n1 n2 : nat} {vec1 : nvec n1} {vec2 : nvec n2} (pn1 : predicate vec1) (pn2 : predicate vec2) : bool :=
match nat_eqb n1 n2 with
| true => match nvec_eqb vec1 vec2 with
    | true => match pn1, pn2 with
        | Nullary i1 _, Nullary i2 _ => nat_eqb i1 i2
        | Succary i1 v1 pn1' _, Succary i2 v2 pn2' _  => nat_eqb i1 i2 && nat_eqb v1 v2 && prd_eqb pn1' pn2'
        | Var i1, Var i2 => nat_eqb i1 i2
        | _ , _ => false
        end
    | false => false
    end
| false => false
end.

Fixpoint form_eqb (A1 A2 : formula) : bool :=
match A1, A2 with
| fal, fal => true
| equ v1 v2, equ v3 v4 => nat_eqb v1 v3 && nat_eqb v2 v4
| imp B1 C1, imp B2 C2 => form_eqb B1 B2 && form_eqb C1 C2
| univ v1 B1, univ v2 B2 => nat_eqb v1 v2 && form_eqb B1 B2
| bnd o1 o2 B1, bnd o3 o4 B2 => nat_eqb o1 o3 && nat_eqb o2 o4 && form_eqb B1 B2
| prd pn1 _, prd pn2 _ => prd_eqb pn1 pn2
| _, _ => false
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
| univ v B => 
    (match nat_eqb v i1 with
    | true => A
    | false => univ v (substitution B i1 i2)
    end)
| bnd o1 o2 B => bnd o1 o2 (substitution B i1 i2)
| prd pn _ => A
end.

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
all : case (nat_eqb i iv) eqn:EQ1;
      try reflexivity.
all : case (nat_eqb i0 iv) eqn:EQ2;
      try apply nat_eqb_eq in EQ1;
      try apply nat_eqb_eq in EQ2;
      subst;
      reflexivity.
Qed.

Lemma nvec_case :
    forall (n : nat) (P : nvec n -> Type),
        (forall (pf : n = 0),
            P (eq_rect 0 nvec Null n (eq_sym pf))) ->
        (forall (i m : nat) (vec : nvec i) (pf : n = S i), P (eq_rect (S i) nvec (New i m vec) n (eq_sym pf))) ->
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

Lemma nvec_Sn_new : forall {n : nat} (vec : nvec (S n)), {subvec : nvec n & {m : nat & vec = New n m subvec}}.
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

Lemma pred_case :
    forall (n : nat) (vec : nvec n) (P : predicate vec -> Type),
        (forall (i : nat) (pf : n = 0) (pfv : vec = (eq_rect 0 nvec Null n (eq_sym pf))),
            P (eq_rect _ predicate (Nullary i pf) _ (eq_sym pfv))) ->
        (forall (m : nat) (vec' : nvec m) (i : nat) (v : ivar) (prd : predicate vec') (pf : n = S m) (pfv : vec = eq_rect (S m) nvec (New m v vec') n (eq_sym pf)),
            P (eq_rect _ predicate (Succary i v prd pf) _ (eq_sym pfv))) ->
        (forall (i : nat), P (Var i)) ->
            (forall (pn : predicate vec), P pn).
Proof.
intros n vec P BC IND VARS pn.
pose proof (Eqdep_dec.eq_rect_eq_dec nat_eq_dec nvec vec (eq_sym eq_refl)).
induction pn.
apply (BC _ pf eq_refl).
apply (IND _ _ _ _ _ pf eq_refl).
apply VARS.
Qed.

Lemma prd_eqb_sym :
    forall {n1 n2 : nat} {vec1 : nvec n1} {vec2 : nvec n2} (pn1 : predicate vec1) (pn2 : predicate vec2),
        prd_eqb pn1 pn2 = prd_eqb pn2 pn1. 
Proof.
intros n1 n2 vec1 vec2 pn1.
revert n2 vec2.
induction pn1;
intros n2 vec2;
destruct pn2;
unfold prd_eqb;
fold @prd_eqb;
subst;
try rewrite !nat_eqb_refl;
try rewrite nvec_eqb_refl;
try rewrite nat_eqb_symm;
try rewrite nvec_eqb_sym;
try rewrite (nat_eqb_symm v v0);
try rewrite (nat_eqb_symm i i0);
try rewrite IHpn1;
reflexivity.
Qed.

Lemma prd_eqb_eq :
    forall {n : nat} {vec : nvec n} (pn1 pn2 : predicate vec),
        prd_eqb pn1 pn2 = true ->
            pn1 = pn2.
Proof.
intros n vec.
induction pn1.
- intros pn2.
  subst.
  unfold eq_rect, eq_sym in *.
  apply (pred_case 0 Null (fun (pn2 : predicate Null) => prd_eqb (Nullary i eq_refl) pn2 = true -> (Nullary i eq_refl) = pn2)).
  + intros i1 pf pfv EQB.
    rewrite pfv in EQB.
    unfold eq_rect, eq_sym in EQB.
    rewrite (UIP _ _ _ pf eq_refl) in EQB.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl in EQB.
    apply nat_eqb_eq in EQB.
    subst.
    pose proof (UIP_refl _ _ pf).
    subst.
    unfold eq_rect, eq_sym in pfv.
    pose proof (UIP_refl _ _ pfv).
    subst.
    reflexivity.
  + intros m vec i1 v pn1 pf pfv EQB.
    inversion pf.
  + intros i1 EQB.
    inversion EQB.
- intros pn3.
  subst.
  unfold eq_rect, eq_sym in *.
  apply (pred_case (S m) (New m v vec) (fun (pn2 : predicate (New m v vec)) => prd_eqb (Succary i v pn1 eq_refl) pn2 = true -> (Succary i v pn1 eq_refl) = pn2)).
  + intros i1 pf pfv EQB.
    inversion pf.
  + intros m2 vec2 i2 v2 pn2 pf pfv EQB.
    inversion pf as [pf'].
    subst.
    pose proof (UIP_refl _ _ pf).
    subst.
    unfold eq_rect, eq_sym in pfv.
    inversion pfv as [[EQ1 EQ2]].
    apply inj_pair2 in EQ2.
    subst.
    pose proof (UIP_refl _ _ pfv).
    subst.
    unfold eq_rect, eq_sym in *.
    unfold prd_eqb in EQB;
    fold @prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl, nat_eqb_refl, andb_true_r in EQB.
    apply and_bool_prop in EQB as [EQ1 EQ2].
    apply nat_eqb_eq in EQ1.
    specialize (IHpn1 _ EQ2) as EQ3.
    subst.
    reflexivity.
  + intros i1 EQB.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl in EQB.
    inversion EQB.
- intros pn2.
  apply (pred_case n vec (fun (pn2 : predicate vec) => prd_eqb (Var i) pn2 = true -> (Var i) = pn2)).
  + intros i1 pf pfv EQB.
    subst.
    inversion EQB.
  + intros m vec2 i1 v pn1 pf pfv EQB.
    subst.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl in EQB.
    inversion EQB.
  + intros i2 EQB.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl in EQB.
    apply nat_eqb_eq in EQB.
    subst.
    reflexivity.
Qed.

Lemma prd_eqb_refl :
    forall {n : nat} {vec : nvec n} (pn : predicate vec),
        prd_eqb pn pn = true.
Proof.
intros n vec pn.
induction pn;
unfold prd_eqb;
fold @prd_eqb;
repeat rewrite nat_eqb_refl;
rewrite nvec_eqb_refl;
try rewrite IHpn;
try reflexivity.
Qed.

Lemma prd_eqb_type : 
    forall {n1 n2 : nat} {vec1 : nvec n1} {vec2 : nvec n2} (pn1 : predicate vec1) (pn2 : predicate vec2),
        prd_eqb pn1 pn2 = true -> nat_eqb n1 n2 = true /\ nvec_eqb vec1 vec2 = true.
Proof.
intros n1 n2 vec1 vec2 pn1 pn2 EQB.
destruct pn1, pn2;
subst;
unfold prd_eqb, eq_rect, eq_sym in EQB;
fold @prd_eqb in EQB.
- split; reflexivity.
- inversion EQB.
- case (nat_eqb 0 n2) eqn:EQ1;
  case (nvec_eqb Null vec) eqn:EQ2;
  inversion EQB.
- inversion EQB.
- unfold eq_rect, eq_sym.
  case (nat_eqb (S m) (S m0)) eqn:EQ1.
  case (nvec_eqb (New m v vec) (New m0 v0 vec0)) eqn:EQ2.
  split; reflexivity.
  inversion EQB.
  inversion EQB.
- case (nat_eqb (S m) n2) eqn:EQ1;
  case (nvec_eqb (New m v vec) vec0) eqn:EQ2;
  inversion EQB.
- case (nat_eqb n1 0) eqn:EQ1;
  case (nvec_eqb vec Null) eqn:EQ2;
  inversion EQB.
- case (nat_eqb n1 (S m)) eqn:EQ1;
  case (nvec_eqb vec (New m v vec0)) eqn:EQ2;
  inversion EQB.
- case (nat_eqb n1 n2) eqn:EQ1;
  case (nvec_eqb vec vec0) eqn:EQ2;
  inversion EQB.
  split; reflexivity.
Qed.

Definition prd_eq_dec {n : nat} {vec : nvec n} : forall (a b : predicate vec), {a = b} + {a <> b}.
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
- rewrite (IHA _ EQ0).
  reflexivity.
- rewrite (IHA _ EQ0).
  reflexivity.
- destruct (prd_eqb_type _ _ EQ') as [EQ1 EQ2].
  apply nat_eqb_eq in EQ1.
  subst.
  apply nvec_eqb_eq in EQ2.
  subst.
  apply prd_eqb_eq in EQ'.
  subst.
  pose proof (UIP  _ _ _ e e0).
  subst.
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

(*
Fixpoint vec_map {n : nat} (F : nat -> nat) (vec : nvec n) : nvec n :=
match n as n' return n' = n -> nvec n with
| 0 => fun pf => (eq_rect _ _ Null _ pf)
| S m => match vec with
    | Null => fun pf => Null
    | New _ v vec' => fun pf => New _ (F v) (vec_map F vec')
    end
end eq_refl.
*)

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