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

Definition ug_left_inv_formula (phi A : formula) (b : bool) : formula := formula_sub phi (univ A) A b.

Lemma ug_l_inv_form_depth_le :
    forall (phi A : formula) (b : bool),
        form_depth (formula_sub phi (univ A) A b) <= form_depth phi.
Proof.
intros phi A b.
unfold formula_sub.
case form_eqb eqn:EQF.
destruct b.
apply form_eqb_eq in EQF.
subst.
unfold form_depth;
fold form_depth.
all : lia.
Qed.

Definition ug_left_inv_batch (gamma : list formula) (A : formula) (S : subst_ind) : list formula := batch_sub gamma (univ A) A S.

Fixpoint ptree_ug_l_inv_fit
  (P : ptree) (A : formula) (S : subst_ind) (depth : nat) : ptree :=
match depth with
| 0 => P
| S d =>
let REC := (fun PT SI DEP => (ptree_ug_l_inv_fit PT A SI DEP)) in
match P, S with
| bot, _ => P

| pred vec pn pure, _ => P

| equal v1 v2, _ => P

| loop_head OC gamma delta alpha P_Target, _ => loop_head OC (ug_left_inv_batch gamma A S) delta alpha (REC P_Target S d)

| @sub_l OC gamma delta phi v1 v2 alpha P', s1 :: s2 :: S' => match (form_eqb phi A) with
    | true => P
    | false => @sub_l OC (ug_left_inv_batch gamma A S') delta (ug_left_inv_formula phi A s2) v1 v2 alpha (REC (ptree_ug_l_inv_fit P' (shift_substitution A (Datatypes.S v1) v2) (false :: s2 :: repeat false (length S')) d) (s1 :: false :: S') d)
    end
| @sub_r OC gamma delta phi v1 v2 alpha P', s :: S' => @sub_r OC (ug_left_inv_batch gamma A S') delta phi v1 v2 alpha (REC P' (s :: S') d)

| @con_l OC gamma delta phi alpha P', s :: S' => @con_l OC (ug_left_inv_batch gamma A S') delta (ug_left_inv_formula phi A s) alpha (REC P' (s :: s :: S') d)

| @con_r OC gamma delta phi alpha P', _ => @con_r OC (ptree_left (REC P' S d)) delta phi alpha (REC P' S d)

| @refl OC gamma delta v alpha P', _ => @refl OC (ug_left_inv_batch gamma A S) delta v alpha (ptree_ug_l_inv_fit P' A (false :: S) d)


| @ex_l OC gamma delta n alpha P', _ => @ex_l OC (ptree_left (REC P' (unbury S n) d)) delta n alpha (REC P' (unbury S n) d)

| @ex_r OC gamma delta n alpha P', _ => @ex_r OC (ptree_left (REC P' S d)) delta n alpha (REC P' S d)


| @wkn_l OC gamma delta phi alpha P', s :: S' => @wkn_l OC (ug_left_inv_batch gamma A S') delta (ug_left_inv_formula phi A s) alpha (REC P' S' d)

| @wkn_r OC gamma delta phi alpha P', _ => @wkn_r OC (ptree_left (REC P' S d)) delta phi alpha (REC P' S d)

| @rst OC gamma delta kappa alpha P', _ => @rst OC (ptree_left (REC P' S d)) delta kappa alpha (REC P' S d)

| @ug_l OC gamma delta phi alpha P', s :: S' => match s, form_eqb phi A with
    | true, true => REC P' (false :: S') d
    | _, _ => let SI := (false :: S') in @ug_l OC (ug_left_inv_batch gamma A S') delta phi alpha (REC P' SI d)
    end

| @ug_r OC gamma delta phi alpha P', _ => @ug_r OC (ptree_left (REC P' S d)) delta phi alpha (REC P' S d)

| @bnd_l OC gamma delta phi lambda kappa alpha P', s :: S' => @bnd_l OC (ug_left_inv_batch gamma A S') delta phi lambda kappa alpha (REC P' (false :: S') d)

| @bnd_r OC gamma delta phi lambda kappa alpha P', _ => @bnd_r OC (ptree_left (REC P' S d)) delta phi lambda kappa alpha (REC P' S d)

| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2, s :: S' =>  @imp_l OC (ug_left_inv_batch gamma A S') delta phi psi alpha1 alpha2 (REC P1 (false :: S') d) (REC P2 S' d)

| @imp_r OC gamma delta phi psi alpha P', _ => @imp_r OC (ug_left_inv_batch gamma A S) delta phi psi alpha (REC P' (false :: S) d)

| @cut OC gamma delta phi alpha1 alpha2 P1 P2, _ => @cut OC (ug_left_inv_batch gamma A S) delta phi alpha1 alpha2 (REC P1 S d) (REC P2 (false :: S) d)

| _ , _ => P
end
end.

Definition ptree_ug_l_inv (P : ptree) (A : formula) (S : subst_ind) : ptree :=
match nat_eqb (length (ptree_left P)) (length S) with
| true => ptree_ug_l_inv_fit P A S (ptree_height P)
| false => P
end.

Lemma ptree_ug_l_inv_fit_true :
    forall {P : ptree} {A : formula},
        forall {S : subst_ind},
            nat_eqb (length (ptree_left P)) (length S) = true ->
                (ptree_ug_l_inv_fit P A S (ptree_height P)) = (ptree_ug_l_inv P A S).
Proof. intros P A S EQ. unfold ptree_ug_l_inv. rewrite EQ. reflexivity. Qed.

Lemma ptree_ug_l_inv_left :
    forall (P : ptree) (A : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_left (ptree_ug_l_inv P A S) =
                    (ug_left_inv_batch (ptree_left P) A S).
Proof.
intros P A.
induction P;
try intros PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub;
case nat_eqb eqn:EQ;
try reflexivity;
unfold ptree_height;
fold ptree_height;
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
      reflexivity. }

3 : { unfold ptree_left at 1.
      fold (ptree_left (ptree_ug_l_inv_fit P A (unbury S n) (ptree_height P))).
      rewrite ptree_ug_l_inv_fit_true, <- batch_bury_comm, (IHP PSV).
      reflexivity.
      rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ.
      apply EQ. }

all : destruct S as [ | b S];
      inversion EQ.

4 : destruct b.
4,5 : unfold formula_sub, form_eqb;
      fold form_eqb;
      case (form_eqb phi A) eqn:EQF.

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
Qed.

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
      unfold ptree_height;
      fold ptree_height;
      unfold ptree_ug_l_inv_fit;
      fold ptree_ug_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.

1 : destruct S as [ | b1 [ | b2 S]];
    reflexivity.

all : destruct S as [ | b S];
      inversion EQ;
      destruct b;
      try case (form_eqb phi A) eqn:EQF;
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
      unfold ptree_height;
      fold ptree_height;
      unfold ptree_ug_l_inv_fit;
      fold ptree_ug_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.


1 : destruct S as [ | b1 [ | b2 S]];
    reflexivity.
  
all : destruct S as [ | b S];
      inversion EQ;
      destruct b;
      try case (form_eqb phi A) eqn:EQF;
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
      unfold ptree_height;
      fold ptree_height;
      unfold ptree_ug_l_inv_fit;
      fold ptree_ug_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.


1 : destruct S as [ | b1 [ | b2 S]];
    reflexivity.
  
all : destruct S as [ | b S];
      inversion EQ;
      destruct b;
      try case (form_eqb phi A) eqn:EQF;
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
case form_eqb eqn:EQF.
destruct b.
apply form_eqb_eq in EQF.
subst.
all : reflexivity.
Qed.

Lemma ptree_ug_l_inv_vars :
    forall (gamma : list formula) (A : formula) (S : subst_ind),
        flat_map vars_in (ug_left_inv_batch gamma A S) =
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
fold (ug_left_inv_batch gamma A S).
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


Lemma ptree_ug_l_inv_height_aux :
    forall (n : nat) (P : ptree) (A : formula),
        ptree_height P <= n ->
            forall (S : subst_ind),
                ptree_height (ptree_ug_l_inv_fit P A S n) <= n.
Proof.
induction n;
intros P A LT S.
destruct P;
inversion LT.
destruct P;
apply le_S_n in LT;
unfold ptree_ug_l_inv_fit;
fold ptree_ug_l_inv_fit;
unfold ptree_height;
fold ptree_height.

5,6,7,12,15,17,19 : destruct S as [ | b S].

6 : destruct S as [ | b1 [ | B2 S]].

16 : destruct b.
16 : case (form_eqb phi A) eqn:EQF.

all : unfold ptree_height in *;
      fold ptree_height in *;
      try apply le_n_S;
      try rewrite EQL';
      try apply (IHn _ _ LT);
      try lia.

- apply (IHn _ _ (IHn _ _ LT _) _).

- apply (IHn _ _ (IHn _ _ LT _) _).

- apply le_S, IHn, LT.

- assert ((ptree_height P1) <= n /\ (ptree_height P2) <= n) as [LT1 LT2]. split; lia.
  pose proof (IHn _ A LT1 (false :: S)) as LT3.
  pose proof (IHn _ A LT2 S) as LT4.
  lia.

- assert ((ptree_height P1) <= n /\ (ptree_height P2) <= n) as [LT1 LT2]. split; lia.
  pose proof (IHn _ A LT1 S) as LT3.
  pose proof (IHn _ A LT2 (false :: S)) as LT4.
  lia.
Qed.

Lemma ptree_ug_l_inv_height :
    forall (P : ptree) (A : formula) (S : subst_ind),
        ptree_height (ptree_ug_l_inv_fit P A S (ptree_height P)) <= (ptree_height P).
Proof. intros P A S. apply (ptree_ug_l_inv_height_aux _ _ _ (le_n _)). Qed.


Lemma ptree_ug_l_inv_fit_extra :
    forall (d1 d2 : nat) (P : ptree) (A : formula) (S : subst_ind),
        (ptree_height P) <= d1 ->
            (ptree_height P) <= d2 ->
                ptree_ug_l_inv_fit P A S d1 = ptree_ug_l_inv_fit P A S d2.
Proof.
induction d1;
intros d2 P A S LT1 LT2.
destruct P;
inversion LT1.
destruct d2.
destruct P;
inversion LT2.
destruct P;
apply le_S_n in LT1;
apply le_S_n in LT2;
unfold ptree_height in *;
fold ptree_height in *;
unfold ptree_ug_l_inv_fit;
fold ptree_ug_l_inv_fit.

6,7,12,15,17,19 : destruct S as [ | b S].

5 : destruct S as [ | b1 [ | b2 S]].

15 : destruct b.
15 : case (form_eqb phi A) eqn:EQF.

21,31 : assert (ptree_height P1 <= d1 /\ ptree_height P2 <= d1 /\ (ptree_height P1) <= d2 /\ (ptree_height P2) <= d2) as [LT3 [LT4 [LT5 LT6]]]; repeat split; try lia.

all : try rewrite (IHd1 _ _ _ _ LT1 LT2);
      try rewrite (IHd1 _ _ _ _ LT3 LT5);
      try rewrite (IHd1 _ _ _ _ LT4 LT6);
      try rewrite (IHd1 _ _ _ _ LT3);
      try rewrite (IHd1 _ _ _ _ LT4);
      try reflexivity.

1 : pose proof (ptree_ug_l_inv_height P (shift_substitution A (Datatypes.S v1) v2) (false :: b2 :: (repeat false (@length bool S)))) as LT3.
    rewrite <- (IHd1 _ _ _ _ LT1 (le_n _)) in LT3.
    rewrite (IHd1 _ _ _ _ LT1 LT2) in LT3.
    rewrite (IHd1 _ _ _ _ (PeanoNat.Nat.le_trans _ _ _ LT3 LT1) (PeanoNat.Nat.le_trans _ _ _ LT3 LT2)).
    reflexivity.
Qed.

Lemma ptree_ug_l_inv_struct_aux :
    forall (d : nat) (P : ptree) (A : formula),
        ptree_height P <= d ->
            struct_valid P ->
                forall (S : subst_ind),
                    struct_valid (ptree_ug_l_inv P A S).
Proof.
induction d;
intros P A LT PSV S.
exfalso.
destruct P;
inversion LT.
destruct P;
unfold ptree_ug_l_inv;
case nat_eqb eqn:EQ;
try apply PSV;
unfold ptree_height in *;
fold ptree_height in *;
apply le_S_n in LT;
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

13 : destruct b.
13 : case (form_eqb phi A) eqn:EQF.

2 : { rewrite ptree_ug_l_inv_fit_true.
      2 : apply EQ.
      enough (struct_valid (loop_head (ptree_constraint P) (ug_left_inv_batch (ptree_left P) A S) (ptree_right P) (ptree_deg P) (ptree_ug_l_inv P A S))) as PSV'.
      destruct P;
      try apply PSV';
      contradiction (PRec eq_refl).
      repeat split.
      - apply (IHd _ _ LT PSV).
      - rewrite ptree_ug_l_inv_vars.
        apply PG_app.
      - apply PD_app.
      - destruct (ptree_eq_dec (ptree_ug_l_inv P A S) bot) as [EQ' | NE].
        apply (inl EQ').
        right.
        repeat split;
        try apply EQ;
        try rewrite ptree_ug_l_inv_constraint;
        try apply ptree_ug_l_inv_deg;
        try rewrite ptree_ug_l_inv_left;
        try rewrite ptree_ug_l_inv_right;
        try assumption;
        try reflexivity. }

1 : { repeat split.
      rewrite ptree_ug_l_inv_vars.
      apply PG_app.
      apply PD_app.
      apply (inl eq_refl). }

19 : rewrite (ptree_ug_l_inv_fit_extra _ _ _ _ _ (PeanoNat.Nat.le_max_l _ _) (le_n _)), (ptree_ug_l_inv_fit_extra _ _ _ _ _ (PeanoNat.Nat.le_max_r _ _) (le_n _)).

17 : rewrite (ptree_ug_l_inv_fit_extra _ _ _ _ _ (PeanoNat.Nat.le_max_l _ _) (le_n _)), (ptree_ug_l_inv_fit_extra _ _ _ _ _ (PeanoNat.Nat.le_max_r _ _) (le_n _)).

1 : { rewrite (ptree_ug_l_inv_fit_extra _ _ _ _ _ (ptree_ug_l_inv_height _ _ _) (le_n _)).
      rewrite !ptree_ug_l_inv_fit_true.
      3 : rewrite !ptree_ug_l_inv_fit_true;
          try rewrite (ptree_ug_l_inv_left _ _ PSV);
          unfold ug_left_inv_batch;
          try rewrite <- batch_sub_length;
          try apply nat_eqb_eq.
      all : try rewrite PG;
            unfold length;
            fold (@length formula) (@length bool);
            try rewrite repeat_length;
            try apply EQ.
      repeat split.
      1 : { refine (IHd _ _ (PeanoNat.Nat.le_trans _ _ _ _ LT) (IHd _ _ LT PSV _) _).
            pose proof (ptree_ug_l_inv_height P (shift_substitution A (Datatypes.S v1) v2) (false :: b2 :: (repeat false (length S)))) as LT'.
            rewrite !ptree_ug_l_inv_fit_true in LT'.
            apply LT'.
            rewrite PG.
            unfold length in *;
            fold (@length formula) (@length bool) in *.
            rewrite repeat_length.
            apply EQ. }
      1 : rewrite ptree_ug_l_inv_vars;
          unfold ug_left_inv_batch;
          apply PG_app.
      1 : apply PD_app.
      all : try rewrite !ptree_ug_l_inv_left;
            try rewrite !ptree_ug_l_inv_right;
            try rewrite !ptree_ug_l_inv_constraint;
            try rewrite !ptree_ug_l_inv_deg;
            try reflexivity;
            try apply PSV;
            try apply (IHd _ _ LT PSV).
      unfold ug_left_inv_batch.
      unfold batch_sub at 1.
      unfold ptree_left in EQ.
      rewrite PG, <- batch_sub_length.
      unfold batch_sub.
      all : unfold length in *;
            fold (@length bool) (@length formula) in *;
            try rewrite repeat_length.
      2 : apply (nat_eqb_eq _ _ EQ).
      rewrite EQ.
      unfold nat_eqb in EQ;
      fold nat_eqb in EQ.
      rewrite EQ.
      unfold batch_sub_fit;
      fold batch_sub_fit.
      rewrite batch_sub_false.
      unfold formula_sub, form_eqb;
      fold form_eqb.
      case (form_eqb (shift_substitution phi v1 v2) (univ (shift_substitution A (Datatypes.S v1) v2))) eqn:EQF.
      destruct b2.
      - assert (form_eqb (shift_substitution phi v1 v2) (shift_substitution (univ A) v1 v2) = true) as EQF'. apply EQF.
        case form_eqb.
        unfold ug_left_inv_formula, formula_sub.
        admit.
        admit.
      - case form_eqb;
        unfold ug_left_inv_formula;
        rewrite formula_sub_false;
        reflexivity.
      - assert (form_eqb (shift_substitution phi v1 v2) (shift_substitution (univ A) v1 v2) = false) as EQF'. apply EQF.
        case form_eqb;
        unfold ug_left_inv_formula, formula_sub;
        rewrite (shift_subst_neb_form_neb _ _ _ _ EQF');
        reflexivity. }

18 : assert ((ptree_height P1) <= d /\ (ptree_height P2) <= d) as [LT1 LT2].
18 : split; lia.

16 : assert ((ptree_height P1) <= d /\ (ptree_height P2) <= d) as [LT1 LT2].
16 : split; lia.

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
      try apply (IHd _ _ LT PSV);
      try apply (IHd _ _ LT1 P1SV);
      try apply (IHd _ _ LT2 P2SV);
      try reflexivity.

all : try rewrite <- batch_sub_fit_true;
      unfold batch_sub_fit;
      fold batch_sub_fit;
      try rewrite batch_sub_fit_true;
      try reflexivity;
      try apply EQ.
Admitted.