From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import constraints.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.

Require Import List.
Require Import Lia.
Import ListNotations.

Definition ug_left_inv_formula (phi A : formula) (b : bool) : formula := formula_sub phi (univ A) A 0 b.

Lemma ug_l_inv_form_depth_le :
    forall (phi A : formula) (b : bool),
        form_depth (formula_sub phi (univ A) A 0 b) <= form_depth phi.
Proof.
intros phi A b.
unfold formula_sub.
case form_equiv eqn:EQF.
destruct b.
rewrite (form_equiv_preserves_depth _ _ _ EQF).
unfold form_depth;
fold form_depth.
all : lia.
Qed.

Definition ug_left_inv_batch (gamma : list formula) (A : formula) (d : nat) (S : subst_ind) : list formula := batch_sub gamma (univ A) A d S.

Fixpoint ptree_ug_l_inv_fit
  (P : ptree) (A : formula) (S : subst_ind) : ptree :=
let REC := (fun PT SI => (ptree_ug_l_inv_fit PT A SI)) in
match P, S with
| bot, _ => P

| pred vec pn pure, _ => P

| equal v1 v2, _ => P

| loop_head OC gamma delta alpha P_Target, _ => loop_head OC (ug_left_inv_batch gamma A 0 S) delta alpha (REC P_Target S)

| @sub_l OC gamma delta phi v1 v2 alpha P', s1 :: s2 :: S' => @sub_l OC (ug_left_inv_batch gamma A 0 S') delta (formula_sub (shift_substitution phi v1 v2) (univ A) A v2 s2) v1 v2 alpha (REC P' (s1 :: s2 :: S'))

| @sub_r OC gamma delta phi v1 v2 alpha P', s :: S' => @sub_r OC (ug_left_inv_batch gamma A 0 S') delta phi v1 v2 alpha (REC P' (s :: S'))

| @con_l OC gamma delta phi alpha P', s :: S' => @con_l OC (ug_left_inv_batch gamma A 0 S') delta (ug_left_inv_formula phi A s) alpha (REC P' (s :: s :: S'))

| @con_r OC gamma delta phi alpha P', _ => @con_r OC (ptree_left (REC P' S)) delta phi alpha (REC P' S)

| @refl OC gamma delta v alpha P', _ => @refl OC (ug_left_inv_batch gamma A 0 S) delta v alpha (ptree_ug_l_inv_fit P' A (false :: S))


| @ex_l OC gamma delta n alpha P', _ => @ex_l OC (ptree_left (REC P' (unbury S n))) delta n alpha (REC P' (unbury S n))

| @ex_r OC gamma delta n alpha P', _ => @ex_r OC (ptree_left (REC P' S)) delta n alpha (REC P' S)


| @wkn_l OC gamma delta phi alpha P', s :: S' => @wkn_l OC (ug_left_inv_batch gamma A 0 S') delta (ug_left_inv_formula phi A s) alpha (REC P' S')

| @wkn_r OC gamma delta phi alpha P', _ => @wkn_r OC (ptree_left (REC P' S)) delta phi alpha (REC P' S)

| @rst OC gamma delta kappa alpha P', _ => @rst OC (ptree_left (REC P' S)) delta kappa alpha (REC P' S)

| @ug_l OC gamma delta phi alpha P', s :: S' => match form_eqb phi A, s with
    | true, true => REC P' (false :: S')
    | _, _ => let SI := (false :: S') in @ug_l OC (ug_left_inv_batch gamma A 0 S') delta phi alpha (REC P' SI)
    end

| @ug_r OC gamma delta phi alpha P', _ => @ug_r OC (ptree_left (REC P' S)) delta phi alpha (REC P' S)

| @bnd_l OC gamma delta phi lambda kappa alpha P', s :: S' => @bnd_l OC (ug_left_inv_batch gamma A 0 S') delta phi lambda kappa alpha (REC P' (false :: S'))

| @bnd_r OC gamma delta phi lambda kappa alpha P', _ => @bnd_r OC (ptree_left (REC P' S)) delta phi lambda kappa alpha (REC P' S)

| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2, s :: S' =>  @imp_l OC (ug_left_inv_batch gamma A 0 S') delta phi psi alpha1 alpha2 (REC P1 (false :: S')) (REC P2 S')

| @imp_r OC gamma delta phi psi alpha P', _ => @imp_r OC (ug_left_inv_batch gamma A 0 S) delta phi psi alpha (REC P' (false :: S))

| @cut OC gamma delta phi alpha1 alpha2 P1 P2, _ => @cut OC (ug_left_inv_batch gamma A 0 S) delta phi alpha1 alpha2 (REC P1 S) (REC P2 (false :: S))

| _ , _ => P
end.

Definition ptree_ug_l_inv (P : ptree) (A : formula) (S : subst_ind) : ptree :=
match nat_eqb (length (ptree_left P)) (length S) with
| true => ptree_ug_l_inv_fit P A S
| false => P
end.

Lemma ptree_ug_l_inv_fit_true :
    forall {P : ptree} {A : formula},
        forall {S : subst_ind},
            nat_eqb (length (ptree_left P)) (length S) = true ->
                (ptree_ug_l_inv_fit P A S) = (ptree_ug_l_inv P A S).
Proof. intros P A S EQ. unfold ptree_ug_l_inv. rewrite EQ. reflexivity. Qed.

Lemma ptree_ug_l_inv_left :
    forall (P : ptree) (A : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_left (ptree_ug_l_inv P A S) =
                    (ug_left_inv_batch (ptree_left P) A 0 S).
Proof.
intros P A.
induction P;
try intros PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub;
case nat_eqb eqn:EQ;
try reflexivity;
unfold ptree_ug_l_inv_fit;
fold ptree_ug_l_inv_fit;
unfold ptree_left in EQ;
fold ptree_left in EQ.

1-3 : destruct PSV.
4 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
6-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
16-17 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
19 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
20 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
21 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
22 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst;
      unfold ptree_left at 2;
      try unfold ptree_left at 2;
      unfold batch_sub_fit;
      fold @batch_sub_fit.

9,12,14,15,17,19 :  rewrite (batch_sub_fit_true EQ);
                    rewrite (ptree_ug_l_inv_fit_true EQ);
                    apply (IHP PSV).

1-3 : destruct S;
      reflexivity.

all : try rewrite (batch_sub_fit_true EQ);
      try reflexivity.

1 : { destruct S as [ | b1 [ | b2 S]].
      1,2 : inversion EQ.
      unfold ptree_left.
      unfold form_equiv, ug_left_inv_formula, ug_left_inv_batch.
      rewrite batch_sub_fit_true.
      2 : apply EQ.
      admit. }

3 : { unfold ptree_left at 1.
      fold (ptree_left (ptree_ug_l_inv_fit P A (unbury S n))).
      rewrite ptree_ug_l_inv_fit_true, <- batch_bury_comm, (IHP PSV).
      reflexivity.
      rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ.
      apply EQ. }

all : destruct S as [ | b S];
      inversion EQ.

4 : unfold formula_sub, form_equiv;
    fold form_equiv;
    try rewrite form_equiv_0_eq;
    case (form_eqb phi A) eqn:EQF.
4 : destruct b.

all : try unfold ptree_left at 1 2;
      try fold (ptree_left P);
      try fold (ptree_left P2);
      unfold batch_sub, batch_sub_fit;
      fold batch_sub_fit;
      try rewrite batch_sub_fit_true;
      try rewrite EQ;
      try apply EQ;
      try reflexivity.

1 : rewrite ptree_ug_l_inv_fit_true, (IHP PSV), PG.
    unfold ug_left_inv_batch, batch_sub, batch_sub_fit at 1;
    fold batch_sub_fit.
    unfold length in *;
    fold (@length formula) (@length bool) in *.
    rewrite EQ, formula_sub_false, H0.
    apply form_eqb_eq in EQF.
    subst.
    reflexivity.
    rewrite PG.
    apply EQ.
Admitted.

Lemma ptree_ug_l_inv_right :
    forall (P : ptree) (A : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_right (ptree_ug_l_inv P A S) =
                   (ptree_right P).
Proof.
intros P A.
induction P;
try intros PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub.

1-3 : destruct PSV.
4 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
6-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
16-17 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
19 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
20 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
21 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
22 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold ptree_ug_l_inv_fit;
      fold ptree_ug_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.

1 : destruct S as [ | b1 [ | b2 S]];
    reflexivity.

all : destruct S as [ | b S];
      inversion EQ;
      try case (form_eqb phi A) eqn:EQF;
      case b;
      try reflexivity.

1 : unfold ptree_right at 2.
    rewrite ptree_ug_l_inv_fit_true.
    apply (IHP PSV).
    rewrite PG.
    apply EQ.
Qed.

Lemma ptree_ug_l_inv_constraint :
    forall (P : ptree) (A : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_constraint (ptree_ug_l_inv P A S) =
                   (ptree_constraint P).
Proof.
intros P A.
induction P;
try intros PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub.

1-3 : destruct PSV.
4 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
6-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
16-17 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
19 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
20 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
21 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
22 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold ptree_ug_l_inv_fit;
      fold ptree_ug_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.


1 : destruct S as [ | b1 [ | b2 S]];
    reflexivity.
  
all : destruct S as [ | b S];
      inversion EQ;
      try case (form_eqb phi A) eqn:EQF;
      case b;
      try reflexivity.

1 : unfold ptree_constraint at 2.
    rewrite ptree_ug_l_inv_fit_true.
    apply (IHP PSV).
    rewrite PG.
    apply EQ.
Qed.

Lemma ptree_ug_l_inv_deg :
    forall (P : ptree) (A : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_deg (ptree_ug_l_inv P A S) =
                   (ptree_deg P).
Proof.
intros P A.
induction P;
try intros PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub.

1-3 : destruct PSV.
4 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
6-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
16-17 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
19 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
20 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
21 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
22 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold ptree_ug_l_inv_fit;
      fold ptree_ug_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.


1 : destruct S as [ | b1 [ | b2 S]];
    reflexivity.
  
all : destruct S as [ | b S];
      inversion EQ;
      try case (form_eqb phi A) eqn:EQF;
      case b;
      try reflexivity.

1 : unfold ptree_deg at 2.
    rewrite ptree_ug_l_inv_fit_true.
    apply (IHP PSV).
    rewrite PG.
    apply EQ.
Qed.

Lemma ug_l_formula_inv_vars :
    forall (phi : formula) (A : formula) (b : bool),
        vars_in (ug_left_inv_formula phi A b) =
            vars_in phi.
Proof.
intros phi A b.
unfold ug_left_inv_formula, formula_sub.
case form_equiv eqn:EQF.
destruct b.
rewrite (form_equiv_preserves_ovars _ _ _ EQF).
all : reflexivity.
Qed.

Lemma ptree_ug_l_inv_vars :
    forall (gamma : list formula) (A : formula) (S : subst_ind),
        flat_map vars_in (ug_left_inv_batch gamma A 0 S) =
            flat_map vars_in gamma.
Proof.
induction gamma;
intros A S;
unfold ug_left_inv_batch, batch_sub, batch_sub_fit;
fold batch_sub_fit;
destruct S;
unfold length, nat_eqb;
fold (@length formula) (@length bool) nat_eqb.
1-3 : reflexivity.
case nat_eqb eqn:EQN.
unfold flat_map;
fold (flat_map vars_in).
rewrite (batch_sub_fit_true EQN).
fold (ug_left_inv_batch gamma A 0 S).
rewrite IHgamma.
fold (ug_left_inv_formula a A b).
rewrite ug_l_formula_inv_vars.
reflexivity.
reflexivity.
Qed.

Lemma ptree_ug_l_inv_bot :
    forall (phi : formula) (S : subst_ind),
        ptree_ug_l_inv bot phi S = bot.
Proof.
intros phi S.
unfold ptree_ug_l_inv, ptree_ug_l_inv_fit.
case (nat_eqb);
reflexivity.
Qed.

(*
Lemma ptree_ug_l_inv_leaves :
    forall (P : ptree) (A : formula) (v : ivar),
        struct_valid P ->
            forall (S : subst_ind),
                (length (ptree_left P) = length S) ->
                    In ((loop_head (ptree_constraint P) (ptree_left P) (ptree_right P) (ptree_deg P) bot), bot) (leaves P) ->
                        In ((loop_head (ptree_constraint P) (batch_sub (ptree_left P) (univ v A) A S) (ptree_right P) (ptree_deg P) bot), bot) (leaves (ptree_ug_l_inv P A v S)).
Proof.
intros P A v.
induction P;
try intros PSV S EQ INPL;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub.

1-3 : destruct PSV.
5-11 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
12 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
13-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
16 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
17 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
18 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
19 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
4 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[[PRec PG] PD] POC] PDeg] PLoop]]].

1-3 : inversion INPL as [].

1 : { subst.
      unfold ptree_constraint, ptree_left, ptree_right, ptree_deg in *.
      rewrite EQ, nat_eqb_refl.
      unfold ptree_ug_l_inv_fit, leaves.
      rewrite batch_sub_fit_true.
      apply (or_introl eq_refl).
      rewrite EQ.
      apply nat_eqb_refl. }

1 : { inversion INPL as [INPL' | FAL];
      try inversion FAL.
      unfold ptree_constraint, ptree_left, ptree_right, ptree_deg in INPL';
      fold ptree_constraint ptree_left ptree_right ptree_deg in *.
      inversion INPL' as [[EQ1 EQ2]].
      subst.
      contradiction PRec. }



all : subst;
      try rewrite EQ, nat_eqb_refl.

      case nat_eqb eqn:EQ;
      try apply INPL.
      unfold ptree_ug_l_inv_fit;
      fold ptree_ug_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.

2,4,5 : destruct S as [ | b S];
        inversion EQ;
        reflexivity.

- destruct S as [ | b1 [ | b2 S]].
  inversion EQ.
  inversion EQ.
  reflexivity.

- destruct S as [ | b S].
  inversion EQ.
  case (nat_eqb v0 v && form_eqb phi A).
  case b.
  2,3 : reflexivity.
  unfold ptree_deg at 2.
  rewrite ptree_ug_l_inv_fit_true.
  apply (IHP PSV).
  rewrite PG.
  apply EQ.
Qed.
*)

Lemma ptree_ug_l_inv_struct :
    forall (P : ptree) (A : formula),
        struct_valid P ->
            forall (S : subst_ind),
                struct_valid (ptree_ug_l_inv P A S).
Proof.
intros P.
induction P;
try intros AF PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub;
case nat_eqb eqn:EQ;
try apply PSV;
unfold ptree_ug_l_inv_fit;
fold ptree_ug_l_inv_fit.

16 :  destruct S as [ | b S];
      try apply PSV.

14 :  destruct S as [ | b S];
      try apply PSV.

12 :  destruct S as [ | b S];
      try apply PSV.

9 : destruct S as [ | b S];
    try apply PSV.

4 : destruct S as [ | b S];
    try apply PSV.

3 : destruct S as [ | b S];
    try apply PSV.

2 : destruct S as [ | b1 [ | b2 S]];
    try apply PSV.

1 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
3-11 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
12 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
13-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
16 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] [NING NIND]] PDeg].
17 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
18 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
19 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst.

13 :  case (form_eqb phi AF) eqn:EQfn;
      case b.

2 : { rewrite ptree_ug_l_inv_fit_true.
      2 : apply EQ.
      enough (struct_valid (loop_head (ptree_constraint P) (ug_left_inv_batch (ptree_left P) AF 0 S) (ptree_right P) (ptree_deg P) (ptree_ug_l_inv P AF S))) as PSV'.
      destruct P;
      try apply PSV';
      contradiction (PRec eq_refl).
      repeat split.
      - apply (IHP _ PSV).
      - rewrite ptree_ug_l_inv_vars.
        apply PG_app.
      - apply PD_app.
      - destruct (ptree_eq_dec (ptree_ug_l_inv P AF S) bot) as [EQ' | NE].
        apply (inl EQ').
        right.
        repeat split;
        try rewrite P1G;
        try rewrite P2G;
        try apply EQ;
        try unfold ptree_left at 1 in EQ;
        try rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ;
        try apply EQ;
        repeat split;
        try rewrite ptree_ug_l_inv_constraint;
        try apply ptree_ug_l_inv_deg;
        try rewrite ptree_ug_l_inv_left;
        try rewrite PG;
        try rewrite P1G;
        try rewrite P2G;
        unfold flat_map;
        fold (flat_map vars_in);
        try rewrite ptree_ug_l_inv_vars;
        try rewrite ug_l_formula_inv_vars;
        unfold ug_left_inv_batch;
        try rewrite batch_sub_false_head;
        try rewrite ptree_ug_l_inv_right;
        try apply Order;
        try assumption;
        try apply (IHP _ _ PSV);
        try apply (IHP1 _ _ P1SV);
        try apply (IHP2 _ _ P2SV);
        try reflexivity. }

1 : { repeat split.
      rewrite ptree_ug_l_inv_vars.
      apply PG_app.
      apply PD_app.
      apply (inl eq_refl). }

all : repeat rewrite ptree_ug_l_inv_fit_true;
      try rewrite PG;
      try rewrite P1G;
      try rewrite P2G;
      try apply EQ;
      unfold ptree_left at 1 in EQ;
      try rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ;
      try apply EQ;
      repeat split;
      try rewrite ptree_ug_l_inv_constraint;
      try apply ptree_ug_l_inv_deg;
      try rewrite ptree_ug_l_inv_left;
      try rewrite PG;
      try rewrite P1G;
      try rewrite P2G;
      unfold flat_map;
      fold (flat_map vars_in);
      try rewrite ptree_ug_l_inv_vars;
      try rewrite ug_l_formula_inv_vars;
      unfold ug_left_inv_batch;
      try rewrite batch_sub_false_head;
      try rewrite ptree_ug_l_inv_right;
      try assumption;
      try apply (IHP _ PSV);
      try apply (IHP1 _ P1SV);
      try apply (IHP2 _ P2SV);
      try reflexivity.

all : try rewrite <- batch_sub_fit_true;
      unfold batch_sub_fit;
      fold batch_sub_fit;
      try rewrite batch_sub_fit_true;
      try reflexivity;
      try apply EQ.

- unfold formula_sub, form_equiv;
  fold form_equiv.
  case (form_equiv phi (univ AF) 0) eqn:EQF.
  destruct b2.
  rewrite form_equiv_0_eq in EQF.
  apply form_eqb_eq in EQF.
  subst.
  rewrite form_equiv_diff_shift_subst.

all : pose proof (ug_l_inv_form_depth_le phi AF b2) as LE;
      unfold ug_left_inv_formula;
      lia.
Qed.