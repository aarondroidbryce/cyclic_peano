From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import constraints.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.

Require Import List.
Import ListNotations.

Definition ug_left_inv_formula (phi A : formula) (v : ivar) (b : bool) : formula := formula_sub phi (univ v A) A b.

Definition ug_left_inv_batch (gamma : list formula) (A : formula) (v : ivar) (S : subst_ind) : list formula := batch_sub gamma (univ v A) A S.

Fixpoint ptree_ug_l_inv_fit
  (P : ptree) (A : formula) (i : ivar) (S : subst_ind) : ptree :=
let REC := (fun PT SI => (ptree_ug_l_inv_fit PT A i SI)) in
match P, S with
| bot, _ => P

| pred vec pn pure, _ => P

| equal v1 v2, _ => P

| loop_head OC gamma delta alpha P_Target, _ => loop_head OC (ug_left_inv_batch gamma A i S) delta alpha (REC P_Target S)

| @con_l OC gamma delta phi alpha P', s :: S' => @con_l OC (ug_left_inv_batch gamma A i S') delta (ug_left_inv_formula phi A i s) alpha (REC P' (s :: s :: S'))

| @con_r OC gamma delta phi alpha P', _ => @con_r OC (ptree_left (REC P' S)) delta phi alpha (REC P' S)

| @sub_l OC gamma delta phi v1 v2 alpha P', s1 :: s2 :: S' => @sub_l OC (ug_left_inv_batch gamma A i S') delta (ug_left_inv_formula phi A i s2) v1 v2 alpha (REC P' (s1 :: s2 :: S'))

| @sub_r OC gamma delta phi v1 v2 alpha P', s :: S' => @sub_r OC (ug_left_inv_batch gamma A i S') delta phi v1 v2 alpha (REC P' (s :: S'))

| @refl OC gamma delta v alpha P', _ => @refl OC (ug_left_inv_batch gamma A i S) delta v alpha (ptree_ug_l_inv_fit P' A i (false :: S))


| @ex_l OC gamma delta n alpha P', _ => @ex_l OC (ptree_left (REC P' (unbury S n))) delta n alpha (REC P' (unbury S n))

| @ex_r OC gamma delta n alpha P', _ => @ex_r OC (ptree_left (REC P' S)) delta n alpha (REC P' S)


| @wkn_l OC gamma delta phi alpha P', s :: S' => @wkn_l OC (ug_left_inv_batch gamma A i S') delta (ug_left_inv_formula phi A i s) alpha (REC P' S')

| @wkn_r OC gamma delta phi alpha P', _ => @wkn_r OC (ptree_left (REC P' S)) delta phi alpha (REC P' S)

| @rst OC gamma delta kappa alpha P', _ => @rst OC (ptree_left (REC P' S)) delta kappa alpha (REC P' S)

| @ug_l OC gamma delta phi v alpha P', s :: S' => match nat_eqb v i && form_eqb phi A, s with
    | true, true => REC P' (false :: S')
    | _, _ => let SI := (false :: S') in @ug_l OC (ug_left_inv_batch gamma A i S') delta phi v alpha (REC P' SI)
    end

| @ug_r OC gamma delta phi v alpha P', _ => @ug_r OC (ptree_left (REC P' S)) delta phi v alpha (REC P' S)

| @bnd_l OC gamma delta phi lambda kappa alpha P', s :: S' => @bnd_l OC (ug_left_inv_batch gamma A i S') delta phi lambda kappa alpha (REC P' (false :: S'))

| @bnd_r OC gamma delta phi lambda kappa alpha P', _ => @bnd_r OC (ptree_left (REC P' S)) delta phi lambda kappa alpha (REC P' S)

| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2, s :: S' =>  @imp_l OC (ug_left_inv_batch gamma A i S') delta phi psi alpha1 alpha2 (REC P1 (false :: S')) (REC P2 S')

| @imp_r OC gamma delta phi psi alpha P', _ => @imp_r OC (ug_left_inv_batch gamma A i S) delta phi psi alpha (REC P' (false :: S))

| @cut OC gamma delta phi alpha1 alpha2 P1 P2, _ => @cut OC (ug_left_inv_batch gamma A i S) delta phi alpha1 alpha2 (REC P1 S) (REC P2 (false :: S))

| _ , _ => P
end.

Definition ptree_ug_l_inv (P : ptree) (A : formula) (i : ivar) (S : subst_ind) : ptree :=
match nat_eqb (length (ptree_left P)) (length S) with
| true => ptree_ug_l_inv_fit P A i S
| false => P
end.

Lemma ptree_ug_l_inv_fit_true :
    forall {P : ptree} {A : formula} {v : ivar},
        forall {S : subst_ind},
            nat_eqb (length (ptree_left P)) (length S) = true ->
                (ptree_ug_l_inv_fit P A v S) = (ptree_ug_l_inv P A v S).
Proof. intros P A v S EQ. unfold ptree_ug_l_inv. rewrite EQ. reflexivity. Qed.

Lemma ptree_ug_l_inv_left :
    forall (P : ptree) (A : formula) (v : ivar),
        struct_valid P ->
            weak_formula A = false ->
                forall (S : subst_ind),
                    ptree_left (ptree_ug_l_inv P A v S) =
                        (ug_left_inv_batch (ptree_left P) A v S).
Proof.
intros P A v.
induction P;
try intros PSV WF S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub;
case nat_eqb eqn:EQ;
try reflexivity;
unfold ptree_ug_l_inv_fit;
fold ptree_ug_l_inv_fit;
unfold ptree_left in EQ;
fold ptree_left in EQ.

1-3 : destruct PSV.
4 : destruct PSV as [[[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]] PWF].
6-12 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
13-14 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg] PWF].
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

7,12,14,15,17,19 :  rewrite (batch_sub_fit_true EQ);
                    rewrite (ptree_ug_l_inv_fit_true EQ);
                    apply (IHP PSV WF).

1-3 : destruct S;
      reflexivity.

all : try rewrite (batch_sub_fit_true EQ);
      try reflexivity.

- destruct S as [ | b S];
  inversion EQ.
  rewrite batch_sub_fit_true, ptree_ug_l_inv_fit_true.
  reflexivity.
  rewrite PG.
  apply EQ.
  apply EQ.

- destruct S as [ | b1 [ | b2 S]].
  1,2 : inversion EQ.
  unfold ptree_left.
  unfold formula_sub at 1.
  unfold form_eqb, ug_left_inv_formula, ug_left_inv_batch.
  rewrite batch_sub_fit_true.
  2 : apply EQ.
  unfold form_equiv at 1.
  rewrite (form_sub_sub0_comm _ _ _ _ _ WF).
  reflexivity.

- destruct S as [ | b S].
  inversion EQ.
  rewrite batch_sub_fit_true.
  reflexivity.
  apply EQ.

- unfold ptree_left at 1.
  fold (ptree_left (ptree_ug_l_inv_fit P A v (unbury S n))).
  rewrite ptree_ug_l_inv_fit_true, <- batch_bury_comm, (IHP PSV WF).
  reflexivity.
  rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ.
  apply EQ.

- destruct S as [ | b S].
  inversion EQ.
  unfold ptree_left at 1 2.
  fold (ptree_left P).
  unfold batch_sub, batch_sub_fit;
  fold batch_sub_fit.
  rewrite batch_sub_fit_true, EQ.
  reflexivity.
  apply EQ.

- destruct S as [ | b S].
  inversion EQ.
  unfold formula_sub, form_eqb;
  fold form_eqb.
  case (nat_eqb v0 v && form_eqb phi A) eqn:EQ'.
  case b.
  + apply and_bool_prop in EQ' as [EQ1 EQ2].
    apply form_eqb_eq in EQ2.
    subst.
    rewrite ptree_ug_l_inv_fit_true, (IHP PSV WF), PG.
    unfold ug_left_inv_batch, batch_sub, batch_sub_fit at 1;
    fold batch_sub_fit.
    unfold length in *;
    fold (@length formula) (@length bool) in *.
    rewrite EQ, formula_sub_false.
    apply nat_eqb_eq in EQ1.
    subst.
    rewrite form_equiv_refl.
    reflexivity.
    rewrite PG.
    apply EQ.
  + unfold ptree_left.
    rewrite batch_sub_fit_true.
    apply and_bool_prop in EQ' as [EQ1 EQ2].
    apply nat_eqb_eq in EQ1.
    apply form_eqb_eq in EQ2.
    subst.
    rewrite form_equiv_refl.
    reflexivity.
    apply EQ.
  + unfold ptree_left.
    rewrite batch_sub_fit_true.
    unfold form_equiv;
    fold form_equiv.
    case (nat_eqb v0 v) eqn:EQN;
    try apply nat_eqb_eq in EQN;
    subst;
    rewrite (not_weak_equiv_eqb _ _ WF), EQ';
    reflexivity.
    apply EQ.

- destruct S as [ | b S].
  inversion EQ.
  unfold ptree_left at 1, formula_sub, form_eqb.
  rewrite batch_sub_fit_true.
  reflexivity.
  apply EQ.

- destruct S as [ | b S].
  inversion EQ.
  unfold ptree_left at 1 2;
  fold (ptree_left P2).
  unfold batch_sub, batch_sub_fit;
  fold batch_sub_fit.
  rewrite batch_sub_fit_true, EQ.
  reflexivity.
  apply EQ.
Qed.

Lemma ptree_ug_l_inv_right :
    forall (P : ptree) (A : formula) (v : ivar),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_right (ptree_ug_l_inv P A v S) =
                   (ptree_right P).
Proof.
intros P A v.
induction P;
try intros PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub.

1-3 : destruct PSV.
4 : destruct PSV as [[[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]] PWF].
6-12 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
13-14 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg] PWF].
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

1,3,4,6,7 : destruct S as [ | b S];
        inversion EQ;
        reflexivity.

- destruct S as [ | b1 [ | b2 S]];
  reflexivity.

- destruct S as [ | b S].
  inversion EQ.
  case (nat_eqb v0 v && form_eqb phi A).
  case b.
  2,3 : reflexivity.
  unfold ptree_right at 2.
  rewrite ptree_ug_l_inv_fit_true.
  apply (IHP PSV).
  rewrite PG.
  apply EQ.
Qed.

Lemma ptree_ug_l_inv_constraint :
    forall (P : ptree) (A : formula) (v : ivar),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_constraint (ptree_ug_l_inv P A v S) =
                   (ptree_constraint P).
Proof.
intros P A v.
induction P;
try intros PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub.

1-3 : destruct PSV.
4 : destruct PSV as [[[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]] PWF].
6-12 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
13-14 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg] PWF].
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

1,3,4,6,7 : destruct S as [ | b S];
            inversion EQ;
            reflexivity.

- destruct S as [ | b1 [ | b2 S]];
  reflexivity.

- destruct S as [ | b S].
  inversion EQ.
  case (nat_eqb v0 v && form_eqb phi A).
  case b.
  2,3 : reflexivity.
  unfold ptree_constraint at 2.
  rewrite ptree_ug_l_inv_fit_true.
  apply (IHP PSV).
  rewrite PG.
  apply EQ.
Qed.

Lemma ptree_ug_l_inv_deg :
    forall (P : ptree) (A : formula) (v : ivar),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_deg (ptree_ug_l_inv P A v S) =
                   (ptree_deg P).
Proof.
intros P A v.
induction P;
try intros PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub.

1-3 : destruct PSV.
4 : destruct PSV as [[[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]] PWF].
6-12 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
13-14 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg] PWF].
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

1,3,4,6,7 : destruct S as [ | b S];
            inversion EQ;
            reflexivity.

- destruct S as [ | b1 [ | b2 S]];
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

Lemma ug_l_formula_inv_vars :
    forall (phi : formula) (A : formula) (v : ivar) (b : bool),
        weak_formula A = false ->
            vars_in (ug_left_inv_formula phi A v b) =
                vars_in phi.
Proof.
intros phi A v b WF.
unfold ug_left_inv_formula, formula_sub.
case form_equiv eqn:EQF.
destruct b.
rewrite not_weak_equiv_eqb in EQF.
apply form_eqb_eq in EQF.
subst.
all : try reflexivity.
apply WF.
Qed.

Lemma ptree_ug_l_inv_vars :
    forall (gamma : list formula) (A : formula) (v : ivar) (S : subst_ind),
        weak_formula A = false ->
            flat_map vars_in (ug_left_inv_batch gamma A v S) =
                flat_map vars_in gamma.
Proof.
induction gamma;
intros A v S WF;
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
fold (ug_left_inv_batch gamma A v S).
rewrite (IHgamma _ _ _ WF).
fold (ug_left_inv_formula a A v b).
rewrite (ug_l_formula_inv_vars _ _ _ _ WF).
reflexivity.
reflexivity.
Qed.

Lemma ptree_ug_l_inv_bot :
    forall (phi : formula) (v : ivar) (S : subst_ind),
        ptree_ug_l_inv bot phi v S = bot.
Proof.
intros phi v S.
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
    forall (P : ptree) (A : formula) (v : ivar),
        struct_valid P ->
            weak_formula A = false ->
                forall (S : subst_ind),
                    struct_valid (ptree_ug_l_inv P A v S).
Proof.
intros P.
induction P;
try intros AF vf PSV WF S;
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

5 : destruct S as [ | b S];
    try apply PSV.

4 : destruct S as [ | b1 [ | b2 S]];
    try apply PSV.

2 : destruct S as [ | b S];
    try apply PSV.

1 : destruct PSV as [[[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]] PWF].
3-9 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
10-11 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg] PWF].
12 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
13-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
16 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] [NING NIND]] PDeg].
17 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
18 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
19 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst.

13 :  case (nat_eqb v vf && form_eqb phi AF) eqn:EQfn;
      case b.

2 : { rewrite ptree_ug_l_inv_fit_true.
      2 : apply EQ.
      enough (struct_valid (loop_head (ptree_constraint P) (ug_left_inv_batch (ptree_left P) AF vf S) (ptree_right P) (ptree_deg P) (ptree_ug_l_inv P AF vf S))) as PSV'.
      destruct P;
      try apply PSV';
      contradiction (PRec eq_refl).
      repeat split.
      - apply (IHP _ _ PSV WF).
      - rewrite ptree_ug_l_inv_vars.
        apply PG_app.
        apply WF.
      - apply PD_app.
      - destruct (ptree_eq_dec (ptree_ug_l_inv P AF vf S) bot) as [EQ' | NE].
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
        try reflexivity.
      - intros phi [INL | INR].
        + unfold ug_left_inv_batch in INL.
          rewrite batch_sub_is_map_combine in INL.
          apply in_map_iff in INL as [[psi b] [EQF IN]].
          apply in_combine_l in IN.
          rewrite <- EQF.
          unfold fst, snd.
          refine (not_weak_sub_not_weak _ _ _ (PWF _ (or_introl IN)) WF _).
          apply nat_eqb_eq, EQ.
        + apply (PWF _ (or_intror INR)). }

1 : { repeat split.
      rewrite ptree_ug_l_inv_vars.
      apply PG_app.
      apply WF.
      apply PD_app.
      apply (inl eq_refl).
      intros phi [INL | INR].
      - unfold ug_left_inv_batch in INL.
        rewrite batch_sub_is_map_combine in INL.
        apply in_map_iff in INL as [[psi b] [EQF IN]].
        apply in_combine_l in IN.
        rewrite <- EQF.
        unfold fst, snd.
        refine (not_weak_sub_not_weak _ _ _ (PWF _ (or_introl IN)) WF _).
        apply nat_eqb_eq, EQ.        
      - apply (PWF _ (or_intror INR)). }

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
      try apply (IHP _ _ PSV WF);
      try apply (IHP1 _ _ P1SV WF);
      try apply (IHP2 _ _ P2SV WF);
      try reflexivity.

all : try rewrite <- batch_sub_fit_true;
      unfold batch_sub_fit;
      fold batch_sub_fit;
      try rewrite batch_sub_fit_true;
      try reflexivity;
      try apply EQ.

1 : rewrite <- (form_sub_sub0_comm _ _ _ _ _ WF).
    reflexivity.

1 : apply (not_weak_sub_not_weak _ _ _ PWF WF).
Qed.