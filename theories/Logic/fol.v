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
(*
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
*)
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
| prd : forall (pn : predicate), formula
| nu : forall (i : nat), formula -> formula
| nuk : forall (i : nat), ovar -> formula -> formula.

Fixpoint num_conn (A : formula) : ordinal :=
match A with
| fal => cast Zero
| imp B C => oadd (oadd (num_conn B) (num_conn C)) (cast (nat_ord 1))
| bnd o1 o2 B => oadd (num_conn B) (cast (nat_ord 1))
| prd pn => cast Zero
| nu i phi => oadd olim (num_conn phi)
| nuk i kappa phi => oadd (assn kappa) (num_conn phi)
end.

Fixpoint vars_in (a : formula) : list ovar :=
match a with
| fal => []
| imp B C => (vars_in B) ++ (vars_in C)
| bnd o1 o2 B => o2 :: remove nat_eq_dec o1 (vars_in B)
| prd pn => []
| nu i phi => vars_in phi
| nuk i kappa phi => kappa :: vars_in phi
end.

Fixpoint vars_used (a : formula) : list ovar :=
match a with
| fal => []
| imp B C => (vars_used B) ++ (vars_used C)
| bnd o1 o2 B => o2 :: vars_used B
| prd pn => []
| nu i phi => vars_used phi
| nuk i kappa phi => kappa :: vars_used phi
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
| prd pn1, prd pn2 => prd_eqb pn1 pn2
| nu i1 phi1, nu i2 phi2 => nat_eqb i1 i2 && form_eqb phi1 phi2
| nuk i1 kappa1 phi1, nuk i2 kappa2 phi2 => nat_eqb i1 i2 && nat_eqb kappa1 kappa2 && form_eqb phi1 phi2
| _, _ => false
end.

Fixpoint ovar_sub (A : formula) (eta rho : ovar) : formula :=
match A with
| fal => fal
| imp B C => imp (ovar_sub B eta rho) (ovar_sub C eta rho)
| bnd lambda kappa B => match nat_eqb eta lambda, nat_eqb eta kappa with
    | true, true => bnd lambda rho B
    | true, false => bnd lambda kappa B
    | false, true => bnd lambda rho (ovar_sub B eta rho)
    | false, false => bnd lambda kappa (ovar_sub B eta rho)
    end
| prd pn => A
| nu x phi => nu x (ovar_sub phi eta rho)
| nuk x kappa phi => match nat_eqb eta kappa with
    | true => nuk x rho (ovar_sub phi eta rho)
    | false => nuk x kappa (ovar_sub phi eta rho)
    end
end.

Fixpoint pvar_sub (A : formula) (i : nat) (psi : formula) : formula :=
match A with
| fal => fal
| imp B C => imp (pvar_sub B i psi) (pvar_sub C i psi)
| bnd lambda kappa B => bnd lambda kappa (pvar_sub B i psi)
| prd (Nullary n) => prd (Nullary n)
| prd (Var n) => match nat_eqb n i with
    | true => psi
    | false => prd (Var n)
    end
| nu x phi => match nat_eqb x i with
    | true => nu x phi
    | false => nu x (pvar_sub phi i psi)
    end
| nuk x kappa phi => match nat_eqb x i with
    | true => nuk x kappa phi
    | false => nuk x kappa (pvar_sub phi i psi)
    end
end.

Fixpoint form_sub (A psi rho : formula) : formula :=
match form_eqb A psi with
| true => rho
| false => match A with
    | fal => fal
    | imp B C => imp (form_sub B psi rho) (form_sub C psi rho)
    | bnd lambda kappa B => bnd lambda kappa (form_sub B psi rho)
    | prd pn => prd pn
    | nu x phi => nu x (form_sub phi psi rho)
    | nuk x kappa phi => nuk x kappa (form_sub phi psi rho)
    end
end.

Lemma vars_in_is_used : 
    forall (phi : formula),
        incl (vars_in phi) (vars_used phi).
Proof.
induction phi;
unfold vars_in, vars_used;
fold vars_in vars_used.
1,4 : intros o IN; apply IN.
apply (incl_app_app IHphi1 IHphi2).
apply incl_head, (incl_tran (incl_remove _ _) IHphi).
apply IHphi.
apply incl_head, IHphi.
Qed.

Lemma vars_not_used_not_in : 
    forall (phi : formula) (o : ovar),
        ~ In o (vars_used phi) ->
            ~ In o (vars_in phi).
Proof.
intros phi o NIN FAL.
apply NIN.
apply vars_in_is_used, FAL.
Qed.

Lemma vars_in_list_is_used : 
    forall (gamma : list formula),
        incl (flat_map vars_in gamma) (flat_map vars_used gamma).
Proof.
induction gamma.
intros o IN; apply IN.
apply (incl_app_app (vars_in_is_used _) IHgamma).
Qed.

Lemma vars_not_used_list_not_in : 
    forall (gamma : list formula) (o : ovar),
        ~ In o (flat_map vars_used gamma) ->
            ~ In o (flat_map vars_in gamma).
Proof.
intros gamma o NIN FAL.
apply NIN.
apply vars_in_list_is_used, FAL.
Qed.

Lemma bnd_vars_in_type :
    forall {phi : formula} (lambda kappa : ovar) {o : ovar},
        In o (vars_in phi) ->
            o = lambda \/ (o <> lambda /\ In o (vars_in (bnd lambda kappa phi))).
Proof.
induction phi;
intros lambda' kappa' o' IN.
- inversion IN.
- apply in_app_or in IN as [IN1 | IN2].
  + destruct (IHphi1 lambda' kappa' _ IN1) as [EQ | [NE [EQ | IN]]].
    apply or_introl, EQ.
    apply or_intror, (conj NE), or_introl, EQ.
    apply or_intror, (conj NE), or_intror.
    rewrite remove_app.
    apply in_or_app, or_introl, IN.
  + destruct (IHphi2 lambda' kappa' _ IN2) as [EQ | [NE [EQ | IN]]].
    apply or_introl, EQ.
    apply or_intror, (conj NE), or_introl, EQ.
    apply or_intror, (conj NE), or_intror.
    rewrite remove_app.
    apply in_or_app, or_intror, IN.
- destruct IN as [EQ | IN].
  + subst.
    destruct (nat_eq_dec o' lambda') as [EQ | NE].
    * apply or_introl, EQ.
    * apply or_intror, (conj NE), or_intror, (in_in_remove _ _ NE), or_introl, eq_refl.
  + apply in_remove in IN as [IN NE].
    destruct (IHphi lambda' kappa' _ IN) as [EQ | [NE' [EQ | IN']]].
    * apply or_introl, EQ.
    * apply or_intror, (conj NE'), or_introl, EQ.
    * apply or_intror, (conj NE'), or_intror.
      fold vars_in (@In ovar).
      unfold remove at 1;
      fold (remove nat_eq_dec).
      case nat_eq_dec eqn:EQ';
      try apply or_intror;
      rewrite remove_remove_comm;
      apply (in_in_remove _ _ NE IN').
- inversion IN.
- apply IHphi, IN.
- destruct IN as [EQ | IN].
  + subst.
    destruct (nat_eq_dec o' lambda') as [EQ | NE].
    * apply or_introl, EQ.
    * apply or_intror, (conj NE), or_intror, (in_in_remove _ _ NE), or_introl, eq_refl.
  + destruct (IHphi lambda' kappa' _ IN) as [EQ | [NE' [EQ | IN']]].
    * apply or_introl, EQ.
    * apply or_intror, (conj NE'), or_introl, EQ.
    * apply or_intror, (conj NE'), or_intror.
      fold vars_in (@In ovar).
      unfold remove at 1;
      fold (remove nat_eq_dec).
      case nat_eq_dec eqn:EQ';
      try apply or_intror;
      apply IN'.
Qed.

Lemma vars_in_osub_conv :
    forall {phi : formula} {lambda kappa eta : ovar},
        In eta (vars_in phi) ->
            eta = lambda \/ In eta (vars_in (ovar_sub phi lambda kappa)).
Proof.
induction phi;
intros lambda' kappa' eta' IN.
- inversion IN.
- apply in_app_or in IN as [IN1 | IN2].
  + destruct (IHphi1 lambda' kappa' _ IN1) as [EQ | IN].
    apply or_introl, EQ.
    apply or_intror, in_or_app, or_introl, IN.
  + destruct (IHphi2 lambda' kappa' _ IN2) as [EQ | IN].
    apply or_introl, EQ.
    apply or_intror, in_or_app, or_intror, IN.
- unfold ovar_sub;
  fold ovar_sub.
  case (nat_eqb lambda' o) eqn:EQ1;
  case (nat_eqb lambda' o0) eqn:EQ2;
  try apply nat_eqb_eq in EQ1;
  try apply nat_eqb_eq in EQ2;
  subst;
  destruct IN as [EQ | IN];
  subst.
  1,5 : apply or_introl, eq_refl.
  1,3 : apply in_remove in IN as [IN NE];
        apply or_intror, or_intror, (in_in_remove nat_eq_dec _ NE IN).
  1,3 : apply or_intror, or_introl, eq_refl.
  1,2 : apply in_remove in IN as [IN NE].
  1 : destruct (IHphi o0 kappa' _ IN) as [EQ | IN'].
      apply or_introl, EQ.
      apply or_intror, or_intror, (in_in_remove _ _ NE), IN'.
      destruct (IHphi lambda' kappa' _ IN) as [EQ | IN'].
      apply or_introl, EQ.
      apply or_intror, or_intror, (in_in_remove _ _ NE), IN'.
- inversion IN.
- apply (IHphi _ _ _ IN).
- unfold ovar_sub;
  fold ovar_sub.
  case (nat_eqb lambda' o) eqn:EQ.
  + apply nat_eqb_eq in EQ.
    subst.
    destruct IN as [EQ | IN].
    apply or_introl, eq_sym, EQ.
    destruct (IHphi o kappa' _ IN) as [EQ | IN'].
    apply or_introl, EQ.
    apply or_intror, or_intror, IN'.
  + destruct IN as [EQ' | IN].
    apply or_intror, or_introl, EQ'.
    destruct (IHphi lambda' kappa' _ IN) as [EQ' | IN'].
    apply or_introl, EQ'.
    apply or_intror, or_intror, IN'. 
Qed.

Lemma vars_used_osub_conv :
    forall {phi : formula} {lambda kappa eta : ovar},
        In eta (vars_used phi) ->
            eta = lambda \/ In eta (vars_used (ovar_sub phi lambda kappa)).
Proof.
induction phi;
intros lambda' kappa' eta' IN.
- inversion IN.
- apply in_app_or in IN as [IN1 | IN2].
  + destruct (IHphi1 lambda' kappa' _ IN1) as [EQ | IN].
    apply or_introl, EQ.
    apply or_intror, in_or_app, or_introl, IN.
  + destruct (IHphi2 lambda' kappa' _ IN2) as [EQ | IN].
    apply or_introl, EQ.
    apply or_intror, in_or_app, or_intror, IN.
- unfold ovar_sub;
  fold ovar_sub.
  case (nat_eqb lambda' o) eqn:EQ1;
  case (nat_eqb lambda' o0) eqn:EQ2;
  try apply nat_eqb_eq in EQ1;
  try apply nat_eqb_eq in EQ2;
  subst;
  destruct IN as [EQ | IN];
  subst.
  1,5 : apply or_introl, eq_refl.
  1,3 : apply or_intror, or_intror, IN.
  1,3 : apply or_intror, or_introl, eq_refl.
  1 : destruct (IHphi o0 kappa' _ IN) as [EQ | IN'].
      apply or_introl, EQ.
      apply or_intror, or_intror, IN'.
      destruct (IHphi lambda' kappa' _ IN) as [EQ | IN'].
      apply or_introl, EQ.
      apply or_intror, or_intror, IN'.
- inversion IN.
- apply (IHphi _ _ _ IN).
- unfold ovar_sub;
  fold ovar_sub.
  case (nat_eqb lambda' o) eqn:EQ.
  + apply nat_eqb_eq in EQ.
    subst.
    destruct IN as [EQ | IN].
    apply or_introl, eq_sym, EQ.
    destruct (IHphi o kappa' _ IN) as [EQ | IN'].
    apply or_introl, EQ.
    apply or_intror, or_intror, IN'.
  + destruct IN as [EQ' | IN].
    apply or_intror, or_introl, EQ'.
    destruct (IHphi lambda' kappa' _ IN) as [EQ' | IN'].
    apply or_introl, EQ'.
    apply or_intror, or_intror, IN'. 
Qed.

Lemma vars_in_osub :
    forall {phi : formula} {lambda kappa eta : ovar},
        In eta (vars_in (ovar_sub phi lambda kappa)) ->
            eta = kappa \/ (eta <> lambda /\ In eta (vars_in phi)).
Proof.
induction phi;
intros lambda' kappa' eta' IN.
- inversion IN.
- apply in_app_or in IN as [IN1 | IN2].
  + destruct (IHphi1 _ _ _ IN1) as [EQ | [NE IN]].
    apply or_introl, EQ.
    apply or_intror, (conj NE), in_or_app, or_introl, IN.
  + destruct (IHphi2 _ _ _ IN2) as [EQ | [NE IN]].
    apply or_introl, EQ.
    apply or_intror, (conj NE), in_or_app, or_intror, IN.
- unfold ovar_sub in IN;
  fold ovar_sub in IN.
  case (nat_eqb lambda' o) eqn:EQ1;
  case (nat_eqb lambda' o0) eqn:EQ2;
  try apply nat_eqb_eq in EQ1;
  try apply nat_eqb_eq in EQ2;
  subst;
  destruct IN as [EQ | IN];
  subst.
  1,5 : apply or_introl, eq_refl.
  1,3 : apply in_remove in IN as [IN NE];
      apply or_intror, (conj NE), or_intror, (in_in_remove nat_eq_dec _ NE IN).
  1,3 : apply or_intror, conj, or_introl, eq_refl.
  1 : destruct (nat_eq_dec eta' o) as [EQ | NE].
  3 : destruct (nat_eq_dec eta' lambda') as [EQ | NE].
  1,3 : subst;
        rewrite nat_eqb_refl in EQ2;
        inversion EQ2.
  1,2 : apply NE.
  1,2 : apply in_remove in IN as [IN NE];
        destruct (IHphi _ _ _ IN) as [EQ' | [NE' IN']].
  1,3 : apply or_introl, EQ'.
  1,2 : apply or_intror, (conj NE'), or_intror, (in_in_remove nat_eq_dec _ NE IN'). 
- inversion IN.
- destruct (IHphi _ _ _ IN) as [EQ | [NE IN']].
  apply or_introl, EQ.
  apply or_intror, (conj NE), IN'.
- unfold ovar_sub in IN;
  fold ovar_sub in IN.
  case (nat_eqb lambda' o) eqn:EQ.
  + apply nat_eqb_eq in EQ.
    subst.
    destruct IN as [EQ | IN].
    apply or_introl, eq_sym, EQ.
    destruct (IHphi _ _ _ IN) as [EQ | [NE IN']].
    apply or_introl, EQ.
    apply or_intror, (conj NE), or_intror, IN'.
  + destruct IN as [EQ' | IN].
    * subst.
      apply or_intror, conj, or_introl, eq_refl.
      destruct (nat_eq_dec eta' lambda') as [EQ' | NE].
      subst.
      rewrite nat_eqb_refl in EQ.
      inversion EQ.
      apply NE.
    * destruct (IHphi _ _ _ IN) as [EQ' | [NE IN']].
      apply or_introl, EQ'.
      apply or_intror, (conj NE), or_intror, IN'. 
Qed.

Lemma vars_used_osub :
    forall {phi : formula} {lambda kappa eta : ovar},
        In eta (vars_used (ovar_sub phi lambda kappa)) ->
            eta = kappa \/ In eta (vars_used phi).
Proof.
induction phi;
intros lambda' kappa' eta' IN.

- inversion IN.
- apply in_app_or in IN as [IN1 | IN2].
  + destruct (IHphi1 _ _ _ IN1) as [EQ | IN].
    apply or_introl, EQ.
    apply or_intror, in_or_app, or_introl, IN.
  + destruct (IHphi2 _ _ _ IN2) as [EQ | IN].
    apply or_introl, EQ.
    apply or_intror, in_or_app, or_intror, IN.
- unfold ovar_sub in IN;
  fold ovar_sub in IN.
  case (nat_eqb lambda' o) eqn:EQ1;
  case (nat_eqb lambda' o0) eqn:EQ2;
  try apply nat_eqb_eq in EQ1;
  try apply nat_eqb_eq in EQ2;
  subst;
  destruct IN as [EQ | IN];
  subst.
  1,5 : apply or_introl, eq_refl.
  1,3 : apply or_intror, or_intror, IN.
  1,3 : apply or_intror, or_introl, eq_refl.
  1,2 : destruct (IHphi _ _ _ IN) as [EQ' | IN'].
  1,3 : apply or_introl, EQ'.
  1,2 : apply or_intror, or_intror, IN'.
- inversion IN.
- destruct (IHphi _ _ _ IN) as [EQ | IN'].
  apply or_introl, EQ.
  apply or_intror, IN'.
- unfold ovar_sub in IN;
  fold ovar_sub in IN.
  case (nat_eqb lambda' o) eqn:EQ.
  + apply nat_eqb_eq in EQ.
    subst.
    destruct IN as [EQ | IN].
    apply or_introl, eq_sym, EQ.
    destruct (IHphi _ _ _ IN) as [EQ | IN'].
    apply or_introl, EQ.
    apply or_intror, or_intror, IN'.
  + destruct IN as [EQ' | IN].
    * subst.
      apply or_intror, or_introl, eq_refl.
    * destruct (IHphi _ _ _ IN) as [EQ' | IN'].
      apply or_introl, EQ'.
      apply or_intror, or_intror, IN'. 
Qed.

Lemma not_in_osub :
    forall {phi : formula} {lambda kappa : ovar},
        lambda <> kappa ->
            ~ In lambda (vars_in (ovar_sub phi lambda kappa)).
Proof.
induction phi;
intros lambda' kappa' NE FAL.
- apply FAL.
- apply in_app_or in FAL as [FAL1 | FAL2].
  apply (IHphi1 _ _ NE FAL1).
  apply (IHphi2 _ _ NE FAL2).
- unfold ovar_sub in FAL;
  fold ovar_sub in FAL.
  case (nat_eqb lambda' o) eqn:EQ1;
  case (nat_eqb lambda' o0) eqn:EQ2;
  try apply nat_eqb_eq in EQ1;
  try apply nat_eqb_eq in EQ2;
  subst;
  destruct FAL as [EQ | FAL];
  subst;
  try contradiction (NE eq_refl);
  try contradiction (proj2 (in_remove nat_eq_dec _ _ _ FAL) eq_refl);
  try rewrite nat_eqb_refl in EQ2;
  try inversion EQ2;
  apply (IHphi _ _ NE (proj1 (in_remove nat_eq_dec _ _ _ FAL))).
- apply FAL.
- apply (IHphi _ _ NE FAL).
- unfold ovar_sub in FAL;
  fold ovar_sub in FAL.
  case (nat_eqb lambda' o) eqn:EQ.
  + apply nat_eqb_eq in EQ.
    subst.
    destruct FAL as [EQ | FAL].
    subst.
    contradiction (NE eq_refl).
    apply (IHphi _ _ NE FAL).
  + destruct FAL as [EQ' | FAL].
    subst.
    rewrite nat_eqb_refl in EQ.
    inversion EQ.
    apply (IHphi _ _ NE FAL).
Qed.

Lemma vars_in_psub_type :
    forall {phi psi : formula} {x : nat} {eta : ovar},
        In eta (vars_in (pvar_sub phi x psi)) ->
            In eta (vars_in phi) \/ In eta (vars_in psi).
Proof.
induction phi;
intros psi x eta IN.
- inversion IN.
- apply in_app_or in IN as [IN1 | IN2].
  destruct (IHphi1 _ _ _ IN1) as [IN1_1 | IN1_2].
  apply or_introl, in_or_app, or_introl, IN1_1.
  apply or_intror, IN1_2.
  destruct (IHphi2 _ _ _ IN2) as [IN2_1 | IN2_2].
  apply or_introl, in_or_app, or_intror, IN2_1.
  apply or_intror, IN2_2.
- destruct IN as [EQ | IN].
  apply or_introl, or_introl, EQ.
  apply in_remove in IN as [IN NE].
  destruct (IHphi _ _ _ IN) as [IN1 | IN2].
  apply or_introl, or_intror, in_in_remove, IN1.
  apply NE.
  apply or_intror, IN2.
- unfold pvar_sub in IN.
  destruct pn.
  2 : case (nat_eqb i x) eqn:EQ.
  1,3 : inversion IN.
  apply or_intror, IN.
- unfold pvar_sub in IN;
  fold pvar_sub in IN.
  case (nat_eqb i x) eqn:EQ.
  apply or_introl, IN.
  apply (IHphi _ _ _ IN).
- unfold pvar_sub in IN;
  fold pvar_sub in IN.
  case (nat_eqb i x) eqn:EQ.
  apply or_introl, IN.
  destruct IN as [EQ' | IN].
  apply or_introl, or_introl, EQ'.
  destruct (IHphi _ _ _ IN) as [IN1 | IN2].
  apply or_introl, or_intror, IN1.
  apply or_intror, IN2.
Qed.

Lemma vars_in_in_psub :
    forall {phi psi : formula} {x : nat} {eta : ovar},
        In eta (vars_in phi) ->
        In eta (vars_in (pvar_sub phi x psi)).
Proof.
induction phi;
intros psi x eta IN;
unfold pvar_sub;
fold pvar_sub.
- inversion IN.
- apply in_app_or in IN as [IN1 | IN2].
  apply in_or_app, or_introl, IHphi1, IN1.
  apply in_or_app, or_intror, IHphi2, IN2.
- destruct IN as [EQ | IN].
  apply or_introl, EQ.
  apply in_remove in IN as [IN NE].
  apply or_intror, in_in_remove, IHphi, IN.
  apply NE.
- inversion IN.
- case (nat_eqb i x) eqn:EQ.
  apply IN.
  apply (IHphi _ _ _ IN).
- case (nat_eqb i x) eqn:EQ.
  apply IN.
  destruct IN as [EQ' | IN].
  apply or_introl, EQ'.
  apply or_intror, IHphi, IN.
Qed.

Lemma sub_self_triv :
    forall {phi : formula} (lambda : ovar),
        ovar_sub phi lambda lambda = phi.
Proof.
induction phi;
intros lambda';
unfold ovar_sub;
fold ovar_sub;
try case nat_eqb eqn:EQ1;
try case (nat_eqb lambda' o0) eqn:EQ2;
try apply nat_eqb_eq in EQ1;
try apply nat_eqb_eq in EQ2;
subst;
try rewrite IHphi;
try rewrite IHphi1, IHphi2;
reflexivity.
Qed.

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
  reflexivity.
- rewrite (IHA _ EQ0).
  reflexivity.
- rewrite (IHA _ EQ0).
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