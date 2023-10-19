From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
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

| loop_head OC1 OC2 gamma delta sig P_Target, _ => loop_head OC1 OC2 (ug_left_inv_batch gamma A i S) delta sig (ptree_ug_l_inv_fit P_Target A i (list_filter S (sublist_filter form_eq_dec (map (fun lambda => sig_subst lambda (sig_generalise sig)) (ptree_left P_Target)) gamma)))

| @con_l OC gamma delta phi v1 v2 alpha P', s1 :: s2 :: S' => @con_l OC (ug_left_inv_batch gamma A i S') delta (ug_left_inv_formula phi A i s2) v1 v2 alpha (REC P' (s1 :: s2 :: s2 :: S'))

| @con_r OC gamma delta phi alpha P', _ => @con_r OC (ptree_left (REC P' S)) delta phi alpha (REC P' S)

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
            forall (S : subst_ind),
                ptree_left (ptree_ug_l_inv P A v S) =
                    (ug_left_inv_batch (ptree_left P) A v S).
Proof.
intros P A v.
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
4 : destruct PSV as [[[[PSV [PG_app PD_app]] PL_app] Psig] PLoop].
5-11 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
12 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
13-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
16 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
17 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
18 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
19 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst;
      unfold ptree_left at 2;
      try unfold ptree_left at 2;
      unfold batch_sub_fit;
      fold @batch_sub_fit.

6,9,11,12,14,16 : rewrite (batch_sub_fit_true EQ);
                  rewrite (ptree_ug_l_inv_fit_true EQ);
                  apply (IHP PSV).

1-3 : destruct S;
      reflexivity.

- rewrite (batch_sub_fit_true EQ).
  reflexivity.

- destruct S as [ | b1 [ | b2 S]].
  inversion EQ.
  inversion EQ.
  rewrite batch_sub_fit_true, ptree_ug_l_inv_fit_true.
  reflexivity.
  rewrite PG.
  apply EQ.
  apply EQ.

- rewrite (batch_sub_fit_true EQ).
  reflexivity.

- unfold ptree_left at 1.
  fold (ptree_left (ptree_ug_l_inv_fit P A v (unbury S n))).
  rewrite batch_sub_fit_true, ptree_ug_l_inv_fit_true, <- batch_bury_comm, (IHP PSV).
  reflexivity.
  rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ.
  apply EQ.
  apply EQ.

- destruct S as [ | b S].
  inversion EQ.
  unfold ptree_left at 1 2.
  fold (ptree_left P).
  unfold batch_sub_fit;
  fold batch_sub_fit.  
  rewrite batch_sub_fit_true.
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
    rewrite ptree_ug_l_inv_fit_true, (IHP PSV), PG.
    unfold ug_left_inv_batch, batch_sub, batch_sub_fit at 1;
    fold batch_sub_fit.
    unfold length in *;
    fold (@length formula) (@length bool) in *.
    rewrite EQ, formula_sub_false.
    reflexivity.
    rewrite PG.
    apply EQ.
  + unfold ptree_left.
    rewrite batch_sub_fit_true.
    reflexivity.
    apply EQ.
  + unfold ptree_left.
    rewrite batch_sub_fit_true.
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
  unfold batch_sub_fit;
  fold batch_sub_fit.
  rewrite batch_sub_fit_true.
  reflexivity.
  apply EQ.

- rewrite (batch_sub_fit_true EQ).
  reflexivity.

- unfold ptree_left at 1.
  fold (ptree_left P1).
  rewrite batch_sub_fit_true.
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
4 : destruct PSV as [[[[PSV [PG_app PD_app]] PL_app] Psig] PLoop].
5-11 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
12 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
13-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
16 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
17 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
18 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
19 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
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
4 : destruct PSV as [[[[PSV [PG_app PD_app]] PL_app] Psig] PLoop].
5-11 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
12 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
13-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
16 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
17 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
18 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
19 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
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
4 : destruct PSV as [[[[PSV [PG_app PD_app]] PL_app] Psig] PLoop].
5-11 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
12 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
13-14 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
16 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
17 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
18 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
19 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
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

Lemma ug_l_formula_inv_vars :
    forall (phi : formula) (A : formula) (v : ivar),
        forall (b : bool),
            vars_in (ug_left_inv_formula phi A v b) =
                vars_in phi.
Proof.
intros phi A v b.
unfold ug_left_inv_formula, formula_sub.
case form_eqb eqn:EQf.
case b.
apply form_eqb_eq in EQf.
subst.
all : reflexivity.
Qed.

Lemma ptree_ug_l_inv_vars :
    forall (gamma : list formula) (A : formula) (v : ivar),
        forall (S : subst_ind),
            flat_map vars_in (ug_left_inv_batch gamma A v S) =
                flat_map vars_in gamma.
Proof.
induction gamma;
intros A v S;
unfold ug_left_inv_batch, batch_sub, batch_sub_fit;
fold batch_sub_fit;
destruct S;
unfold length, nat_eqb;
fold (@length formula) (@length bool) nat_eqb.
1-3 : reflexivity.
case nat_eqb eqn:EQn.
unfold flat_map;
fold (flat_map vars_in).
rewrite (batch_sub_fit_true EQn).
fold (ug_left_inv_batch gamma A v S).
rewrite IHgamma.
unfold formula_sub.
case form_eqb eqn:EQf.
case b.
apply form_eqb_eq in EQf.
subst.
all : reflexivity.
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

Lemma ptree_ug_l_inv_struct :
    forall (P : ptree) (A : formula) (v : ivar),
        struct_valid P ->
            forall (S : subst_ind),
                struct_valid (ptree_ug_l_inv P A v S).
Proof.
intros P.
induction P;
try intros AF vf PSV S;
unfold ptree_ug_l_inv;
unfold ug_left_inv_batch, batch_sub;
case nat_eqb eqn:EQ;
try apply PSV.

all : unfold ptree_ug_l_inv_fit;
      fold ptree_ug_l_inv_fit.

14 :  destruct S as [ | b S];
      try apply PSV.

12 :  destruct S as [ | b S];
      try apply PSV.

10 :  destruct S as [ | b S];
      try apply PSV.

7 : destruct S as [ | b S];
    try apply PSV.

2 : destruct S as [ | b1 [ | b2 S]];
    try apply PSV.

1 : destruct PSV as [[[[[PSV [PG_app PD_app]] PL_app] PL_OC] Psig] PLoop].
2-8 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
9 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
10-11 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
12 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
13 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] FRESH] [NING NIND]] PDeg].
14 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
15 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst.

10 :  case (nat_eqb v vf && form_eqb phi AF) eqn:EQfn;
      case b.

1 : { destruct Psig as [[OC_Sub [Order Coherent]] [SUBG SUBD]].
      rewrite ptree_ug_l_inv_fit_true.
      2 : { rewrite sublist_count_length, sublist_filter_true, map_length.
            apply nat_eqb_refl.
            apply SUBG.
            rewrite sublist_filter_length.
            apply (eq_sym (nat_eqb_eq _ _ EQ)).
            apply SUBG. }
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
      - destruct PL_OC as [EQ' | PL_OC].
        subst.
        left.
        apply ptree_ug_l_inv_bot.
        right.
        apply PL_OC.
      - pose proof (batch_sub_sublist _ _ (univ vf AF) AF S SUBG (nat_eqb_eq _ _ EQ)).
        rewrite map_batch_sub.
        + admit.
        + intros phi1 phi2.
          split;
          intros EQ'.
          subst.
          reflexivity.
          

        apply coherent_is_injective.
        apply batch_sub_sublist. _ _ _ _ _ SUBG (nat_eqb_eq _ _ EQ)). *)
        admit.
      - admit.
}

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
      try apply (IHP _ _ PSV);
      try apply (IHP1 _ _ P1SV);
      try apply (IHP2 _ _ P2SV);
      try reflexivity.

1 : unfold batch_sub, batch_sub_fit;
    fold batch_sub_fit.
    unfold length in *;
    fold (@length formula) (@length bool) in *;
    unfold nat_eqb in *;
    fold nat_eqb in *.
    rewrite EQ.
    unfold formula_sub at 1, form_eqb, ug_left_inv_formula.
    admit.
Qed.

Lemma demorgan1_valid :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (demorgan1_sub_ptree P E F S).
Proof.
intros P E F [PSV PAX].
induction P; try intros S FS;
unfold demorgan1_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold demorgan1_sub_ptree_fit; fold demorgan1_sub_ptree_fit.

all : try apply (PSV,PAX).

1 : { repeat split.
      rewrite dem1_axiom_id;
      apply PAX.
      apply or_introl, eq_refl. }

  1 : destruct PSV as [PSV DU].
  2 : destruct PSV as [[PSV OU] NO].
  3-10 : destruct PSV as [[[PF PSV] PD] PO].
  11 : destruct PSV as [[[[PF PSV] PD] PO] FC].
  12-16: destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O].
  17: destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA].

  3-6,8-13,16,17 : 
      destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

  4-6,13 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

  6 : destruct S1_1; inversion FS'' as [FS'''];
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

  7,8,13,14 :
      case (form_eqb a E) eqn:EQ1;
      case (form_eqb b F) eqn:EQ2;
      unfold ptree_deg; fold ptree_deg;
      try apply (PSV,PAX).

11,19 : case (nat_eqb d1 (Nat.max d1 d2)) eqn:EQ.


all : unfold node_extract in *;
      fold node_extract in *;
      try apply form_eqb_eq in EQ1;
      try destruct EQ1;
      try apply form_eqb_eq in EQ2;
      try destruct EQ2;
      repeat rewrite demorgan1_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply (IHP1 P1SV);
      try apply (IHP2 P2SV);
      unfold ptree_deg; fold ptree_deg;
      try rewrite demorgan1_ptree_deg;
      try rewrite demorgan1_ptree_ord;
      try apply ptree_ord_nf_struct;
      unfold ptree_ord; fold ptree_ord;
      try rewrite demorgan1_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      repeat split;
      unfold demorgan1_sub_formula;
      repeat rewrite formula_sub_ind_lor;
      try rewrite formula_sub_ind_0;
      try rewrite non_target_sub;
      try rewrite non_target_sub_term;
      try apply PSV;
      try apply PAX;
      try apply PD;
      try rewrite PO;
      try apply P1SV;
      try rewrite P1D in *;
      try rewrite P1O;
      try apply P2SV;
      try rewrite P2D in *;
      try rewrite P2O;
      try apply FS;
      try apply DU;
      try apply OU;
      try apply NO;
      try apply INA;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit, non_target;
      fold subst_ind_fit non_target;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      unfold "&&";
      try reflexivity;
      try apply (fun B INB => PAX B (in_or_app _ _ _ (or_introl INB)));
      try apply (fun B INB => PAX B (in_or_app _ _ _ (or_intror INB)));
      try apply max_lem1;
      try apply EQ;
      try apply ord_lt_max_succ_l;
      try reflexivity.

  8 : { intros B INB.
        rewrite closed_free_list in INB.
        inversion INB.
        apply formula_sub_ind_closed.
        apply (valid_closed_formula PAX FC).
        intros CEF.
        apply and_bool_prop in CEF as [CE CF].
        apply CE. }

  all : unfold node_extract in *;
        fold node_extract in *;
        intros A IN;
        try apply in_app_or in IN as [IN1 | IN2];
        try apply (fun FSUB => dem1_all_ax_trans _ _ _ _ P1SV FSUB (fun B INB1 => PAX B (in_or_app _ _ _ (or_introl INB1))) _ IN1);
        try apply (fun FSUB => dem1_all_ax_trans _ _ _ _ P2SV FSUB (fun B INB2 => PAX B (in_or_app _ _ _ (or_intror INB2))) _ IN2);
        try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
        try apply (PAX _ (in_or_app _ _ _ (or_intror IN2)));
        try rewrite P1F;
        try rewrite P2F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS1;
        try rewrite FS2;
        try rewrite non_target_fit;
        try reflexivity.

  all : try apply (PAX _ (in_or_app _ _ _ (or_intror IN)));
        try apply in_app_or in IN as [IN1 | IN2];
        try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
        try apply (fun FSUB => dem1_all_ax_trans _ _ _ _ P1SV FSUB (fun B INB => PAX B (in_or_app _ _ _ (or_intror INB))) _ IN2);
        try rewrite P1F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS1, non_target_sub_fit;
        try reflexivity.
Qed.