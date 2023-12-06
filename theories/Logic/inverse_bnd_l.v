From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import constraints.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.

Require Import List.
Require Import Bool.
Require Import Lia.
Import ListNotations.

Definition bnd_left_inv_formula (phi A : formula) (lambda kappa : ovar) (b : bool) : formula := formula_sub phi (bnd lambda kappa A) A b.

Definition bnd_left_inv_batch (gamma : list formula) (A : formula) (lambda kappa : ovar) (S : subst_ind) : list formula := batch_sub gamma (bnd lambda kappa A) A S.

Fixpoint ptree_bnd_l_inv_fit
  (P : ptree) (A : formula) (lambda kappa : ovar) (S : subst_ind) : ptree :=
let REC := (fun PT SI => (ptree_bnd_l_inv_fit PT A lambda kappa SI)) in
match P, S with
| bot, _ => P

| pred pn pure, _ => P

| loop_head OC gamma delta alpha P_Target, _ => loop_head OC (bnd_left_inv_batch gamma A lambda kappa S) delta alpha (REC P_Target S)

| @con_l OC gamma delta phi alpha P', s :: S' => @con_l OC (bnd_left_inv_batch gamma A lambda kappa S') delta (bnd_left_inv_formula phi A lambda kappa s) alpha (REC P' (s :: s :: S'))

| @con_r OC gamma delta phi alpha P', _ => @con_r OC (ptree_left (REC P' S)) delta phi alpha (REC P' S)

| @ex_l OC gamma delta n alpha P', _ => @ex_l OC (ptree_left (REC P' (unbury S n))) delta n alpha (REC P'(unbury S n))

| @ex_r OC gamma delta n alpha P', _ => @ex_r OC (ptree_left (REC P' S)) delta n alpha (REC P' S)


| @wkn_l OC gamma delta phi alpha P', s :: S' => @wkn_l OC (bnd_left_inv_batch gamma A lambda kappa S') delta (bnd_left_inv_formula phi A lambda kappa s) alpha (REC P' S')

| @wkn_r OC gamma delta phi alpha P', _ => @wkn_r OC (ptree_left (REC P' S)) delta phi alpha (REC P' S)

| @rst OC gamma delta kappa alpha P', _ => @rst OC (ptree_left (REC P' S)) delta kappa alpha (REC P' S)

| @bnd_l OC gamma delta phi eta iota alpha P', s :: S' => match nat_eqb eta lambda, nat_eqb iota kappa, form_eqb phi A, s with
    | true, true, true, true => REC P' (false :: S')
    | _, _, _, _ => @bnd_l OC (bnd_left_inv_batch gamma A lambda kappa S') delta phi eta iota alpha (REC P' (false :: S'))
    end

| @bnd_r OC gamma delta phi eta iota alpha P', _ => @bnd_r OC (ptree_left (REC P' S)) delta phi eta iota alpha (REC P' S)

| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2, s :: S' =>  @imp_l OC (bnd_left_inv_batch gamma A lambda kappa S') delta phi psi alpha1 alpha2 (REC P1 (false :: S')) (REC P2 S')

| @imp_r OC gamma delta phi psi alpha P', _ => @imp_r OC (bnd_left_inv_batch gamma A lambda kappa S) delta phi psi alpha (REC P' (false :: S))

| @cut OC gamma delta phi alpha1 alpha2 P1 P2, _ => @cut OC (bnd_left_inv_batch gamma A lambda kappa S) delta phi alpha1 alpha2 (REC P1 S) (REC P2 (false :: S))

| _ , _ => P
end.

Definition ptree_bnd_l_inv (P : ptree) (A : formula) (lambda kappa : ovar) (S : subst_ind) : ptree :=
match nat_eqb (length (ptree_left P)) (length S) with
| true => ptree_bnd_l_inv_fit P A lambda kappa S
| false => P
end.

Lemma ptree_bnd_l_inv_fit_true :
    forall {P : ptree} {A : formula} {lambda kappa : ovar},
        forall {S : subst_ind},
            nat_eqb (length (ptree_left P)) (length S) = true ->
                (ptree_bnd_l_inv_fit P A lambda kappa S) = (ptree_bnd_l_inv P A lambda kappa S).
Proof. intros P A lambda kappa S EQ. unfold ptree_bnd_l_inv. rewrite EQ. reflexivity. Qed.

Lemma ptree_bnd_l_inv_left :
    forall (P : ptree) (A : formula) (lambda kappa : ovar),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_left (ptree_bnd_l_inv P A lambda kappa S) =
                    (bnd_left_inv_batch (ptree_left P) A lambda kappa S).
Proof.
intros P A lambda kappa.
induction P;
try intros PSV S;
unfold ptree_bnd_l_inv;
unfold bnd_left_inv_batch, batch_sub;
case nat_eqb eqn:EQ;
try reflexivity;
unfold ptree_height;
fold ptree_height;
unfold ptree_bnd_l_inv_fit;
fold ptree_bnd_l_inv_fit;
unfold ptree_left in EQ;
fold ptree_left in EQ.

1-2 : destruct PSV.
3 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
5-10 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
13 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
14 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
15 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst;
      unfold ptree_left;
      unfold batch_sub_fit;
      fold @batch_sub_fit.

all : try rewrite (batch_sub_fit_true EQ);
      try rewrite (ptree_bnd_l_inv_fit_true EQ);
      unfold bnd_left_inv_batch;
      try apply (IHP PSV);
      try reflexivity.

1-2 : destruct S;
      reflexivity.

2 : { fold (ptree_left (ptree_bnd_l_inv_fit P A lambda kappa (unbury S n))).
      rewrite ptree_bnd_l_inv_fit_true, <- batch_bury_comm, (IHP PSV).
      reflexivity.
      rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ.
      apply EQ. }

all : destruct S as [ | b S];
      inversion EQ as [EQ'];
      unfold length in *;
      fold (@length bool) (@length formula) in *.

3 : case (nat_eqb lambda0 lambda) eqn:EQL;
    try apply nat_eqb_eq in EQL.
3 : case (nat_eqb kappa0 kappa) eqn:EQK;
    try apply nat_eqb_eq in EQK.
3 : case (form_eqb phi A) eqn:EQF;
    try apply form_eqb_eq in EQF.
3 : destruct b.


all : subst;
      unfold ptree_left;
      try fold (ptree_left P);
      try fold (ptree_left P2);
      unfold batch_sub, batch_sub_fit;
      fold batch_sub_fit;
      try rewrite batch_sub_fit_true;
      try rewrite PG;
      try rewrite EQ';
      try rewrite EQ;
      try apply EQ;
      try reflexivity.

1 : fold (ptree_left (ptree_bnd_l_inv_fit P A lambda kappa (false :: S))).
    rewrite ptree_bnd_l_inv_fit_true, (IHP PSV).
    rewrite PG.
    unfold formula_sub, bnd_left_inv_batch, batch_sub, batch_sub_fit.
    fold batch_sub_fit.
    unfold length;
    fold (@length bool) (@length formula).
    rewrite EQ, EQ', form_eqb_refl.
    unfold formula_sub.
    case (form_eqb);
    reflexivity.
    rewrite PG.
    apply EQ.

1 : unfold bnd_left_inv_batch, batch_sub, batch_sub_fit at 1;
    fold batch_sub_fit.
    rewrite EQ', formula_sub_false.
    reflexivity.

all  : unfold formula_sub, form_eqb, bnd_left_inv_batch, batch_sub, batch_sub_fit at 1;
    fold batch_sub_fit form_eqb;
    try rewrite EQ';
    try rewrite !nat_eqb_refl;
    try rewrite EQL;
    try rewrite EQK;
    try rewrite EQF;
    try rewrite !andb_false_r;
    try rewrite !andb_false_l;
    try reflexivity.
Qed.

Lemma ptree_bnd_l_inv_right :
    forall (P : ptree) (A : formula) (lambda kappa : ovar),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_right (ptree_bnd_l_inv P A lambda kappa S) =
                   (ptree_right P).
Proof.
intros P A lambda kappa.
induction P;
try intros PSV S;
unfold ptree_bnd_l_inv;
unfold bnd_left_inv_batch, batch_sub.

1-2 : destruct PSV.
3 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
5-10 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
13 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
14 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
15 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold ptree_bnd_l_inv_fit;
      fold ptree_bnd_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.

all : destruct S as [ | b S];
      inversion EQ;
      try case (nat_eqb lambda0 lambda) eqn:EQL;
      try case (nat_eqb kappa0 kappa) eqn:EQK;
      try case (form_eqb phi A) eqn:EQF;
      destruct b;
      try reflexivity.

1 : rewrite ptree_bnd_l_inv_fit_true.
    apply (IHP PSV).
    rewrite PG.
    apply EQ.
Qed.

Lemma ptree_bnd_l_inv_constraint :
    forall (P : ptree) (A : formula) (lambda kappa : ovar),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_constraint (ptree_bnd_l_inv P A lambda kappa S) =
                   (ptree_constraint P).
Proof.
intros P A lambda kappa.
induction P;
try intros PSV S;
unfold ptree_bnd_l_inv;
unfold bnd_left_inv_batch, batch_sub.

1-2 : destruct PSV.
3 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
5-10 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
13 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
14 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
15 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold ptree_bnd_l_inv_fit;
      fold ptree_bnd_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.

all : destruct S as [ | b S];
      inversion EQ;
      try case (nat_eqb lambda0 lambda) eqn:EQL;
      try case (nat_eqb kappa0 kappa) eqn:EQK;
      try case (form_eqb phi A) eqn:EQF;
      destruct b;
      try reflexivity.

1 : rewrite ptree_bnd_l_inv_fit_true.
    apply (IHP PSV).
    rewrite PG.
    apply EQ.
Qed.

Lemma ptree_bnd_l_inv_deg :
    forall (P : ptree) (A : formula) (lambda kappa : ovar),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_deg (ptree_bnd_l_inv P A lambda kappa S) =
                   (ptree_deg P).
Proof.
intros P A lambda kappa.
induction P;
try intros PSV S;
unfold ptree_bnd_l_inv;
unfold bnd_left_inv_batch, batch_sub.

1-2 : destruct PSV.
3 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
5-10 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
13 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
14 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
15 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold ptree_bnd_l_inv_fit;
      fold ptree_bnd_l_inv_fit;
      unfold ptree_left in EQ;
      fold ptree_left in EQ.

all : destruct S as [ | b S];
      inversion EQ;
      try case (nat_eqb lambda0 lambda) eqn:EQL;
      try case (nat_eqb kappa0 kappa) eqn:EQK;
      try case (form_eqb phi A) eqn:EQF;
      destruct b;
      try reflexivity.

1 : rewrite ptree_bnd_l_inv_fit_true.
    apply (IHP PSV).
    rewrite PG.
    apply EQ.
Qed.

Lemma bnd_l_formula_inv_vars :
    forall (phi : formula) (A : formula) (lambda kappa : ovar) (b : bool) (OC : constraint),
        OC_rel OC lambda kappa = true ->
            incl (vars_in phi) (OC_list OC) ->
                incl (vars_in (bnd_left_inv_formula phi A lambda kappa b)) (OC_list OC).
Proof.
intros phi A lambda kappa b OC REL SUB o IN.
unfold bnd_left_inv_formula, formula_sub in IN.
case form_eqb eqn:EQF.
destruct b.
apply form_eqb_eq in EQF.
subst.
case (nat_eq_dec o lambda) as [EQ | NE].
subst.
apply (OC_null _ _ _ REL).
apply SUB.
apply (or_intror (in_in_remove _ _ NE IN)).
all : apply SUB, IN.
Qed.

Lemma ptree_bnd_l_inv_vars :
    forall (gamma : list formula) (A : formula) (lambda kappa : ovar) (S : subst_ind) (OC : constraint),
        OC_rel OC lambda kappa = true ->
            incl (flat_map vars_in gamma) (OC_list OC) ->
                incl (flat_map vars_in (bnd_left_inv_batch gamma A lambda kappa S)) (OC_list OC).
Proof.
induction gamma;
intros A lambda kappa S OC REL SUB;
unfold bnd_left_inv_batch, batch_sub, batch_sub_fit;
fold batch_sub_fit;
destruct S;
unfold length, nat_eqb;
fold (@length formula) (@length bool) nat_eqb.
4 : case nat_eqb eqn:EQN.
1,2,3,5 : apply SUB.
unfold flat_map;
fold (flat_map vars_in).
rewrite (batch_sub_fit_true EQN).
fold (bnd_left_inv_batch gamma A lambda kappa S).
apply incl_app_inv in SUB as [SUB1 SUB2].
apply (incl_app (bnd_l_formula_inv_vars _ _ _ _ _ _ REL SUB1) (IHgamma _ _ _ _ _ REL SUB2)).
Qed.


Lemma bnd_l_formula_inv_vars_sub :
    forall (phi : formula) (A : formula) (lambda kappa : ovar) (b : bool),
        incl (vars_in (bnd_left_inv_formula phi A lambda kappa b)) (lambda :: (vars_in phi)).
Proof.
intros phi A lambda kappa b o IN.
unfold bnd_left_inv_formula, formula_sub in IN.
case form_eqb eqn:EQF.
destruct b.
apply form_eqb_eq in EQF.
subst.
case (nat_eq_dec o lambda) as [EQ | NE].
subst.
apply (or_introl eq_refl).
apply (or_intror (or_intror (in_in_remove _ _ NE IN))).
all : apply (or_intror IN).
Qed.

Lemma ptree_bnd_l_inv_vars_sub :
    forall (gamma : list formula) (A : formula) (lambda kappa : ovar) (S : subst_ind),
        incl (flat_map vars_in (bnd_left_inv_batch gamma A lambda kappa S)) (lambda :: (flat_map vars_in gamma)).
Proof.
induction gamma;
intros A lambda kappa S;
unfold bnd_left_inv_batch, batch_sub, batch_sub_fit;
fold batch_sub_fit;
destruct S;
unfold length, nat_eqb;
fold (@length formula) (@length bool) nat_eqb.
4 : case nat_eqb eqn:EQN.
1,2,3,5 : intros o IN;
          apply or_intror, IN.
unfold flat_map;
fold (flat_map vars_in).
rewrite (batch_sub_fit_true EQN).
fold (bnd_left_inv_batch gamma A lambda kappa S).
refine (incl_tran (incl_app_app (bnd_l_formula_inv_vars_sub _ _ _ _ _) (IHgamma _ _ _ _)) (incl_tran (perm_in nat_eq_dec perm_head) (fun o IN => _))).
destruct IN as [EQ | IN].
subst.
apply (or_introl eq_refl).
apply IN.
Qed.

Lemma ptree_bnd_l_inv_bot :
    forall (phi : formula) (lambda kappa : ovar) (S : subst_ind),
        ptree_bnd_l_inv bot phi lambda kappa S = bot.
Proof.
intros phi lambda kappa S.
unfold ptree_bnd_l_inv, ptree_bnd_l_inv_fit.
case (nat_eqb);
reflexivity.
Qed.

(*
Lemma ptree_bnd_l_inv_leaves :
    forall (P : ptree) (A : formula) (v : ivar),
        struct_valid P ->
            forall (S : subst_ind),
                (length (ptree_left P) = length S) ->
                    In ((loop_head (ptree_constraint P) (ptree_left P) (ptree_right P) (ptree_deg P) bot), bot) (leaves P) ->
                        In ((loop_head (ptree_constraint P) (batch_sub (ptree_left P) (univ v A) A S) (ptree_right P) (ptree_deg P) bot), bot) (leaves (ptree_bnd_l_inv P A v S)).
Proof.
intros P A v.
induction P;
try intros PSV S EQ INPL;
unfold ptree_bnd_l_inv;
unfold bnd_left_inv_batch, batch_sub.

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
      unfold ptree_bnd_l_inv_fit, leaves.
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
      unfold ptree_bnd_l_inv_fit;
      fold ptree_bnd_l_inv_fit;
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
  rewrite ptree_bnd_l_inv_fit_true.
  apply (IHP PSV).
  rewrite PG.
  apply EQ.
Qed.
*)


Lemma ptree_bnd_l_inv_height_aux :
    forall (n : nat) (P : ptree) (A : formula) (lambda kappa : ovar),
        ptree_height P <= n ->
            forall (S : subst_ind),
                ptree_height (ptree_bnd_l_inv_fit P A lambda kappa S) <= n.
Proof.
induction n;
intros P A lambda kappa LT S.
destruct P;
inversion LT.
destruct P;
apply le_S_n in LT;
unfold ptree_bnd_l_inv_fit;
fold ptree_bnd_l_inv_fit;
unfold ptree_height;
fold ptree_height.

4,8,11,13 : destruct S as [ | b S].

9 : case (nat_eqb lambda0 lambda) eqn:EQL.
9 : case (nat_eqb kappa0 kappa) eqn:EQK.
9 : case (form_eqb phi A) eqn:EQF.
9 : destruct b.

all : unfold ptree_height in *;
      fold ptree_height in *;
      try apply le_n_S;
      try rewrite EQL';
      try apply (IHn _ _ _ _ LT);
      try lia.

- apply le_S, IHn, LT.

- assert ((ptree_height P1) <= n /\ (ptree_height P2) <= n) as [LT1 LT2]. split; lia.
  pose proof (IHn _ A lambda kappa LT1 (false :: S)) as LT3.
  pose proof (IHn _ A lambda kappa LT2 S) as LT4.
  lia.

- assert ((ptree_height P1) <= n /\ (ptree_height P2) <= n) as [LT1 LT2]. split; lia.
  pose proof (IHn _ A lambda kappa LT1 S) as LT3.
  pose proof (IHn _ A lambda kappa LT2 (false :: S)) as LT4.
  lia.
Qed.

(*
Lemma ptree_bnd_l_inv_height :
    forall (P : ptree) (A : formula) (S : subst_ind),
        ptree_height (ptree_bnd_l_inv_fit P A S (ptree_height P)) <= (ptree_height P).
Proof. intros P A S. apply (ptree_bnd_l_inv_height_aux _ _ _ (le_n _)). Qed.
*)

(*
Lemma ptree_bnd_l_inv_fit_extra :
    forall (d1 d2 : nat) (P : ptree) (A : formula) (S : subst_ind),
        (ptree_height P) <= d1 ->
            (ptree_height P) <= d2 ->
                ptree_bnd_l_inv_fit P A S d1 = ptree_bnd_l_inv_fit P A S d2.
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
unfold ptree_bnd_l_inv_fit;
fold ptree_bnd_l_inv_fit.

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

1 : pose proof (ptree_bnd_l_inv_height P (shift_substitution A (Datatypes.S v1) v2) (false :: b2 :: (repeat false (@length bool S)))) as LT3.
    rewrite <- (IHd1 _ _ _ _ LT1 (le_n _)) in LT3.
    rewrite (IHd1 _ _ _ _ LT1 LT2) in LT3.
    rewrite (IHd1 _ _ _ _ (PeanoNat.Nat.le_trans _ _ _ LT3 LT1) (PeanoNat.Nat.le_trans _ _ _ LT3 LT2)).
    reflexivity.
Qed.
*)

Lemma ptree_bnd_l_inv_struct_aux :
    forall (P : ptree) (A : formula) (lambda kappa : ovar),
        struct_valid P ->
            (OC_rel (ptree_constraint P) lambda kappa = true) ->
                forall (S : subst_ind),
                    struct_valid (ptree_bnd_l_inv P A lambda kappa S).
Proof.
intros P A lambda kappa.
induction P;
intros PSV REL S;
unfold ptree_bnd_l_inv;
case nat_eqb eqn:EQ;
try apply PSV;
unfold ptree_bnd_l_inv_fit;
fold ptree_bnd_l_inv_fit.

11 :  destruct S as [ | b S];
      try apply PSV.

6 :  destruct S as [ | b S];
      try apply PSV.

2 :  destruct S as [ | b S];
      try apply PSV.

9 : destruct S as [ | b S];
    try apply PSV.

1 : destruct PSV as [[PSV [PG_app PD_app]] [PBot | [[[[PRec PG] PD] POC] PDeg]]].
3-8 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
9 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
10 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
11 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] [NING NIND]] PDeg].
12 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
13 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
14 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst.

10 :  case (nat_eqb lambda0 lambda) eqn:EQL;
      try apply nat_eqb_eq in EQL;
      subst.
10 :  case (nat_eqb kappa0 kappa) eqn:EQK;
      try apply nat_eqb_eq in EQK;
      subst.
10 :  case (form_eqb phi A) eqn:EQF;
      try apply form_eqb_eq in EQF;
      subst.
10 : destruct b.

2 : { rewrite ptree_bnd_l_inv_fit_true.
      2 : apply EQ.
      enough (struct_valid (loop_head (ptree_constraint P) (bnd_left_inv_batch (ptree_left P) A lambda kappa S) (ptree_right P) (ptree_deg P) (ptree_bnd_l_inv P A lambda kappa S))) as PSV'.
      destruct P;
      try apply PSV';
      contradiction (PRec eq_refl).
      repeat split.
      - apply (IHP PSV REL).
      - unfold ptree_left at 1.
        unfold ptree_left at 1 in PG_app.
        unfold ptree_constraint at 1 in REL.
        apply (ptree_bnd_l_inv_vars _ _ _ _ _ _ REL PG_app).
      - apply PD_app.
      - destruct (ptree_eq_dec (ptree_bnd_l_inv P A lambda kappa S) bot) as [EQ' | NE].
        apply (inl EQ').
        right.
        repeat split;
        try apply EQ;
        try rewrite ptree_bnd_l_inv_constraint;
        try apply ptree_bnd_l_inv_deg;
        try rewrite ptree_bnd_l_inv_left;
        try rewrite ptree_bnd_l_inv_right;
        try assumption;
        try reflexivity. }

1 : { repeat split.
      - apply (ptree_bnd_l_inv_vars _ _ _ _ _ _ REL PG_app).
      - apply PD_app.
      - apply (inl eq_refl). }

(*
19 : rewrite (ptree_bnd_l_inv_fit_extra _ _ _ _ _ (PeanoNat.Nat.le_max_l _ _) (le_n _)), (ptree_bnd_l_inv_fit_extra _ _ _ _ _ (PeanoNat.Nat.le_max_r _ _) (le_n _)).

17 : rewrite (ptree_bnd_l_inv_fit_extra _ _ _ _ _ (PeanoNat.Nat.le_max_l _ _) (le_n _)), (ptree_bnd_l_inv_fit_extra _ _ _ _ _ (PeanoNat.Nat.le_max_r _ _) (le_n _)).
*)

(*
1 : { rewrite (ptree_bnd_l_inv_fit_extra _ _ _ _ _ (ptree_bnd_l_inv_height _ _ _) (le_n _)).
      rewrite !ptree_bnd_l_inv_fit_true.
      3 : rewrite !ptree_bnd_l_inv_fit_true;
          try rewrite (ptree_bnd_l_inv_left _ _ PSV);
          unfold bnd_left_inv_batch;
          try rewrite <- batch_sub_length;
          try apply nat_eqb_eq.
      all : try rewrite PG;
            unfold length;
            fold (@length formula) (@length bool);
            try rewrite repeat_length;
            try apply EQ.
      repeat split.
      1 : { refine (IHd _ _ (PeanoNat.Nat.le_trans _ _ _ _ LT) (IHd _ _ LT PSV _) _).
            pose proof (ptree_bnd_l_inv_height P (shift_substitution A (Datatypes.S v1) v2) (false :: b2 :: (repeat false (length S)))) as LT'.
            rewrite !ptree_bnd_l_inv_fit_true in LT'.
            apply LT'.
            rewrite PG.
            unfold length in *;
            fold (@length formula) (@length bool) in *.
            rewrite repeat_length.
            apply EQ. }
      1 : rewrite ptree_bnd_l_inv_vars;
          unfold bnd_left_inv_batch;
          apply PG_app.
      1 : apply PD_app.
      all : try rewrite !ptree_bnd_l_inv_left;
            try rewrite !ptree_bnd_l_inv_right;
            try rewrite !ptree_bnd_l_inv_constraint;
            try rewrite !ptree_bnd_l_inv_deg;
            try reflexivity;
            try apply PSV;
            try apply (IHd _ _ LT PSV).
      unfold bnd_left_inv_batch.
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
        unfold bnd_left_inv_formula, formula_sub.
        admit.
        admit.
      - case form_eqb;
        unfold bnd_left_inv_formula;
        rewrite formula_sub_false;
        reflexivity.
      - assert (form_eqb (shift_substitution phi v1 v2) (shift_substitution (univ A) v1 v2) = false) as EQF'. apply EQF.
        case form_eqb;
        unfold bnd_left_inv_formula, formula_sub;
        rewrite (shift_subst_neb_form_neb _ _ _ _ EQF');
        reflexivity. }

18 : assert ((ptree_height P1) <= d /\ (ptree_height P2) <= d) as [LT1 LT2].
18 : split; lia.

16 : assert ((ptree_height P1) <= d /\ (ptree_height P2) <= d) as [LT1 LT2].
16 : split; lia.
*)

7 : { rewrite ptree_bnd_l_inv_fit_true;
      try rewrite PG;
      try rewrite P1G;
      try rewrite P2G;
      try apply EQ;
      unfold ptree_left at 1 in EQ;
      try rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ;
      try apply EQ;
      repeat split;
      try rewrite ptree_bnd_l_inv_constraint;
      try apply ptree_bnd_l_inv_deg;
      try rewrite ptree_bnd_l_inv_left;
      try rewrite PG;
      try rewrite P1G;
      try rewrite P2G;
      unfold flat_map;
      fold (flat_map vars_in);
      unfold bnd_left_inv_batch;
      try rewrite batch_sub_false_head;
      try rewrite ptree_bnd_l_inv_right;
      try assumption;
      try apply (IHP PSV REL);
      try apply (IHP1 P1SV REL);
      try rewrite <- P2OC in REL;
      try apply (IHP2 P2SV REL);
      try reflexivity.
      2 : unfold ptree_left at 1;
          apply (ptree_bnd_l_inv_vars _ _ _ _ _ _ REL PG_app).
      apply IHP.
      apply PSV.
      rewrite POC.
      unfold restriction, OC_rel at 1, projT2, projT1.
      unfold ptree_constraint in REL.
      rewrite REL, andb_true_l.
       }

all : repeat rewrite ptree_bnd_l_inv_fit_true;
      try rewrite PG;
      try rewrite P1G;
      try rewrite P2G;
      try apply EQ;
      unfold ptree_left at 1 in EQ;
      try rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ;
      try apply EQ;
      repeat split;
      try rewrite ptree_bnd_l_inv_constraint;
      try apply ptree_bnd_l_inv_deg;
      try rewrite ptree_bnd_l_inv_left;
      try rewrite PG;
      try rewrite P1G;
      try rewrite P2G;
      unfold flat_map;
      fold (flat_map vars_in);
      unfold bnd_left_inv_batch;
      try rewrite batch_sub_false_head;
      try rewrite ptree_bnd_l_inv_right;
      try assumption;
      try apply (IHP PSV REL);
      try apply (IHP1 P1SV REL);
      try rewrite <- P2OC in REL;
      try apply (IHP2 P2SV REL);
      try reflexivity.

14 :  { intros FAL.
        apply NING.
        unfold ptree_constraint at 1 in REL.
        unfold ptree_left at 1 in PG_app.
        pose proof (ptree_bnd_l_inv_vars_sub _ _ _ _ _ _ FAL) as [FAL1 | FAL2].
        subst.
        destruct POC as [NEW].
        contradict (NEW (proj1 (OC_null _ _ _ REL))).
        apply FAL2. }

12 :  { apply (IHP PSV).
        destruct POC as [NEW [KIN POC]].
        rewrite POC.
        unfold OC_rel, add_fresh_child, projT2, projT1.
        unfold ptree_constraint at 1 in REL.
        rewrite REL.
        reflexivity. }

(*
10 :  { intros FAL.
        apply KNING.
        unfold ptree_constraint at 1 in REL.
        unfold ptree_left at 1 in PG_app.
        pose proof (struct_OC_app _ PSV) as [P'G_app P'D_app].
        rewrite POC in *.
        pose proof (ptree_bnd_l_inv_vars_sub _ _ _ _ _ _ FAL) as [FAL1 | FAL2].
        subst.

        admit.
        apply FAL2. }

8 : { apply (IHP PSV).
      rewrite POC.
      unfold OC_rel, restriction, projT2, projT1.
      unfold ptree_constraint at 1 in REL.
      rewrite REL.
      case (in_dec nat_eq_dec lambda (children OC kappa0)) as [FAL | _].
      unfold children in FAL.
      apply filter_In in FAL as [FAL1 FAL2].
      admit.
      case (in_dec nat_eq_dec kappa (children OC kappa0)) as [FAL | _].
      admit.
      reflexivity. }*)

2 : try rewrite <- batch_sub_fit_true;
    unfold batch_sub_fit;
    fold batch_sub_fit;
    try rewrite batch_sub_fit_true;
    try reflexivity;
    try apply EQ.

all : unfold ptree_left at 1;
      try apply (ptree_bnd_l_inv_vars _ _ _ _ _ _ REL PG_app).

2 : { intros o IN.
      rewrite flat_map_bury_incl in IN.
      pose proof (ptree_bnd_l_inv_vars (ptree_left P) A lambda kappa (unbury S n) (ptree_constraint P) REL (fun o' IN' => PG_app o' (proj2 (flat_map_bury_incl o') IN'))) as SUB.
      apply SUB, IN. }

1 : pose proof (ptree_bnd_l_inv_vars (phi :: gamma) A lambda kappa (b :: S) (ptree_constraint P) REL PG_app) as SUB.
2 : pose proof (ptree_bnd_l_inv_vars (phi :: (ptree_left P)) A lambda kappa (b :: S) (ptree_constraint P) REL PG_app) as SUB.
3-6 : pose proof (ptree_bnd_l_inv_vars _ A _ _ (false :: S) _ REL PG_app) as SUB.
7 : fold (ptree_constraint (@imp_l (ptree_constraint P1) (ptree_left P2) (ptree_right P1) phi psi (ptree_deg P1) (ptree_deg P2) P1 P2)) in PG_app;
    rewrite <- P2OC in PG_app;
    pose proof (ptree_bnd_l_inv_vars _ A _ _ (false :: S) _ REL PG_app) as SUB;
    unfold ptree_constraint at 1 in SUB;
    rewrite P2OC in SUB.
8 : fold (ptree_constraint (@cut (ptree_constraint P1) (ptree_left P1) (ptree_right P2) phi (ptree_deg P1) (ptree_deg P2) P1 P2)) in PG_app;
    rewrite <- P2OC in PG_app;
    pose proof (ptree_bnd_l_inv_vars _ A _ _ S _ REL PG_app) as SUB;
    unfold ptree_constraint at 1 in SUB;
    rewrite P2OC in SUB.


1-6 : unfold ptree_left, bnd_left_inv_batch, batch_sub, batch_sub_fit, length, nat_eqb in SUB;
      fold (ptree_left P) batch_sub_fit (@length bool) (@length formula) nat_eqb in SUB;
      unfold length, nat_eqb in EQ;
      fold (@length bool) (@length formula) nat_eqb in EQ;
      try rewrite EQ in SUB;
      rewrite batch_sub_fit_true in SUB;
      try rewrite formula_sub_false in SUB;
      try apply SUB;
      try apply EQ.

1,2 : unfold ptree_left, bnd_left_inv_batch, batch_sub, batch_sub_fit, length, nat_eqb in SUB;
    fold (ptree_left P1) (ptree_left P2) batch_sub_fit (@length bool) (@length formula) nat_eqb in SUB;
    unfold length, nat_eqb in EQ;
    fold (@length bool) (@length formula) nat_eqb in EQ;
    try rewrite EQ in SUB;
    rewrite batch_sub_fit_true in SUB;
    try rewrite formula_sub_false in SUB;
    try apply SUB;
    try apply EQ.
Admitted.