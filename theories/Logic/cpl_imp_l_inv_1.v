From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import constraints.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import cpl_trees.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.

Definition imp_left_inv_1_formula (phi A B : formula) (b : bool) : formula := formula_sub phi (imp A B) B b.

Definition imp_left_inv_1_batch (gamma : list formula) (A B : formula) (S : subst_ind) : list formula := batch_sub gamma (imp A B) B S.

Fixpoint cpl_tree_imp_l_inv_1_fit
  (T : cpl_tree) (A B : formula) (S : subst_ind) : cpl_tree :=
let REC := (fun PT SI => (cpl_tree_imp_l_inv_1_fit PT A B SI)) in
match T, S with
| leaf OC gamma delta l, _ => leaf OC (imp_left_inv_1_batch gamma A B S) delta l

| @deg_up OC gamma delta alpha beta b T', _ => @deg_up OC (cpl_tree_left (REC T' S)) delta alpha beta b (REC T' S)

| @con_l OC gamma delta phi alpha T', s :: S' => @con_l OC (imp_left_inv_1_batch gamma A B S') delta (imp_left_inv_1_formula phi A B s) alpha (REC T' (s :: s :: S'))

| @con_r OC gamma delta phi alpha T', _ => @con_r OC (cpl_tree_left (REC T' S)) delta phi alpha (REC T' S)

| @ex_l OC gamma delta n alpha T', _ => @ex_l OC (cpl_tree_left (REC T' (unbury S n))) delta n alpha (REC T'(unbury S n))

| @ex_r OC gamma delta n alpha T', _ => @ex_r OC (cpl_tree_left (REC T' S)) delta n alpha (REC T' S)

| @wkn_l OC gamma delta phi alpha T', s :: S' => @wkn_l OC (imp_left_inv_1_batch gamma A B S') delta (imp_left_inv_1_formula phi A B s) alpha (REC T' S')

| @wkn_r OC gamma delta phi alpha T', _ => @wkn_r OC (cpl_tree_left (REC T' S)) delta phi alpha (REC T' S)

| @rst OC gamma delta eta alpha T', _ => @rst OC (cpl_tree_left (REC T' S)) delta eta alpha (REC T' S)

| @bnd_l OC gamma delta phi eta iota alpha T', s :: S' => @bnd_l OC (imp_left_inv_1_batch gamma A B S') delta phi eta iota alpha (REC T' (false :: S'))

| @bnd_r OC gamma delta phi eta iota alpha T', _ => @bnd_r OC (cpl_tree_left (REC T' S)) delta phi eta iota alpha (REC T' S)

| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2, s :: S' => match (form_eqb phi A), (form_eqb psi B), s with
    | true, true, true => @deg_up OC (cpl_tree_left (REC T1 (false :: S'))) delta alpha1 alpha2 true (REC T1 (false :: S'))
    | _, _ , _ => @imp_l OC (imp_left_inv_1_batch gamma A B S') delta phi psi alpha1 alpha2 (REC T1 (false :: S')) (REC T2 S')
    end

| @imp_r OC gamma delta phi psi alpha T', _ => @imp_r OC (imp_left_inv_1_batch gamma A B S) delta phi psi alpha (REC T' (false :: S))

| @cut OC gamma delta phi alpha1 alpha2 T1 T2, _ => @cut OC (imp_left_inv_1_batch gamma A B S) delta phi alpha1 alpha2 (REC T1 S) (REC T2 (false :: S))

| _ , _ => T
end.

Definition cpl_tree_imp_l_inv_1 (T : cpl_tree) (A B : formula) (S : subst_ind) : cpl_tree :=
match nat_eqb (length (cpl_tree_left T)) (length S) with
| true => cpl_tree_imp_l_inv_1_fit T A B S
| false => T
end.


Lemma cpl_tree_imp_l_inv_1_fit_true :
    forall {T : cpl_tree} {A B : formula},
        forall {S : subst_ind},
            nat_eqb (length (cpl_tree_left T)) (length S) = true ->
                (cpl_tree_imp_l_inv_1_fit T A B S) = (cpl_tree_imp_l_inv_1 T A B S).
Proof. intros T A B S EQ. unfold cpl_tree_imp_l_inv_1. rewrite EQ. reflexivity. Qed.

Lemma cpl_tree_imp_l_inv_1_left :
    forall (T : cpl_tree) (A B : formula),
        structured T ->
            forall (S : subst_ind),
                cpl_tree_left (cpl_tree_imp_l_inv_1 T A B S) =
                    (imp_left_inv_1_batch (cpl_tree_left T) A B S).
Proof.
intros T A B.
induction T;
try intros Tstr S;
unfold cpl_tree_imp_l_inv_1;
unfold imp_left_inv_1_batch, batch_sub;
case nat_eqb eqn:EQ;
try reflexivity;
unfold cpl_tree_imp_l_inv_1_fit;
fold cpl_tree_imp_l_inv_1_fit;
unfold cpl_tree_left in EQ;
fold cpl_tree_left in EQ.

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : subst;
      unfold cpl_tree_left;
      unfold batch_sub_fit;
      fold @batch_sub_fit.

all : try rewrite (batch_sub_fit_true EQ);
      try rewrite (cpl_tree_imp_l_inv_1_fit_true EQ);
      unfold imp_left_inv_1_batch;
      try apply (IHT Tstr);
      try reflexivity.

2 : { fold (cpl_tree_left (cpl_tree_imp_l_inv_1_fit T A B (unbury S n))).
      rewrite cpl_tree_imp_l_inv_1_fit_true, <- batch_bury_comm, (IHT Tstr).
      reflexivity.
      rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ.
      apply EQ. }

all : destruct S as [ | b S];
      inversion EQ as [EQ'];
      unfold length in *;
      fold (@length bool) (@length formula) in *.

4 : case (form_eqb phi A) eqn:EQF1;
    try apply form_eqb_eq in EQF1.
4 : case (form_eqb psi B) eqn:EQF2;
    try apply form_eqb_eq in EQF2.
4 : destruct b.

all : subst;
      unfold cpl_tree_left;
      try fold (cpl_tree_left T);
      try fold (cpl_tree_left T2);
      unfold batch_sub, batch_sub_fit;
      fold batch_sub_fit;
      try rewrite batch_sub_fit_true;
      try rewrite TG;
      try rewrite EQ';
      try rewrite EQ;
      try apply EQ;
      try reflexivity.

1 : fold (cpl_tree_left (cpl_tree_imp_l_inv_1_fit T1 A B (false :: S))).
    rewrite cpl_tree_imp_l_inv_1_fit_true, (IHT1 T1str).
    unfold formula_sub.
    rewrite form_eqb_refl, T1G.
    unfold imp_left_inv_1_batch.
    apply batch_sub_false_head.
    rewrite T1G.
    apply EQ'.

all : unfold formula_sub, form_eqb, imp_left_inv_1_batch, batch_sub, batch_sub_fit at 1;
      fold batch_sub_fit form_eqb;
      try rewrite EQ';
      try rewrite !form_eqb_refl;
      try rewrite EQF1;
      try rewrite EQF2;
      try rewrite !andb_false_r;
      try rewrite !andb_false_l;
      try reflexivity.
Qed.

Lemma cpl_tree_imp_l_inv_1_right :
    forall (T : cpl_tree) (A B : formula),
        structured T ->
            forall (S : subst_ind),
                cpl_tree_right (cpl_tree_imp_l_inv_1 T A B S) =
                   (cpl_tree_right T).
Proof.
intros T A B.
induction T;
try intros Tstr S;
unfold cpl_tree_imp_l_inv_1;
unfold imp_left_inv_1_batch, batch_sub.

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold cpl_tree_imp_l_inv_1_fit;
      fold cpl_tree_imp_l_inv_1_fit;
      unfold cpl_tree_left in EQ;
      fold cpl_tree_left in EQ.

all : destruct S as [ | b S];
      inversion EQ;
      try case (form_eqb phi A) eqn:EQF1;
      try case (form_eqb psi B) eqn:EQF2;
      destruct b;
      try reflexivity.
Qed.

Lemma cpl_tree_imp_l_inv_1_constraint :
    forall (T : cpl_tree) (A B : formula),
        structured T ->
            forall (S : subst_ind),
                cpl_tree_constraint (cpl_tree_imp_l_inv_1 T A B S) =
                   (cpl_tree_constraint T).
Proof.
intros T A B.
induction T;
try intros Tstr S;
unfold cpl_tree_imp_l_inv_1;
unfold imp_left_inv_1_batch, batch_sub.

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold cpl_tree_imp_l_inv_1_fit;
      fold cpl_tree_imp_l_inv_1_fit;
      unfold cpl_tree_left in EQ;
      fold cpl_tree_left in EQ.

all : destruct S as [ | b S];
      inversion EQ;
      try case (form_eqb phi A) eqn:EQF1;
      try case (form_eqb psi B) eqn:EQF2;
      destruct b;
      try reflexivity.
Qed.

Lemma cpl_tree_imp_l_inv_1_deg :
    forall (T : cpl_tree) (A B : formula),
        structured T ->
            forall (S : subst_ind),
                cpl_tree_deg (cpl_tree_imp_l_inv_1 T A B S) =
                   (cpl_tree_deg T).
Proof.
intros T A B.
induction T;
try intros Tstr S;
unfold cpl_tree_imp_l_inv_1;
unfold imp_left_inv_1_batch, batch_sub.

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : subst; 
      case nat_eqb eqn:EQ;
      try reflexivity;
      unfold cpl_tree_imp_l_inv_1_fit;
      fold cpl_tree_imp_l_inv_1_fit;
      unfold cpl_tree_left in EQ;
      fold cpl_tree_left in EQ.

all : destruct S as [ | b S];
      inversion EQ;
      try rewrite H0;
      try case (form_eqb phi A) eqn:EQF1;
      try case (form_eqb psi B) eqn:EQF2;
      destruct b;
      try reflexivity.
Qed.

Lemma imp_l_formula_inv_1_vars_in :
    forall (phi : formula) (A B : formula) (b : bool) (OC : constraint),
        incl (vars_in phi) (OC_list OC) ->
            incl (vars_in (imp_left_inv_1_formula phi A B b)) (OC_list OC).
Proof.
intros phi A B b OC SUB o IN.
unfold imp_left_inv_1_formula, formula_sub in IN.
apply SUB.
case form_eqb eqn:EQF.
destruct b.
apply form_eqb_eq in EQF.
subst.
apply in_or_app,or_intror.
all : apply IN.
Qed.

Lemma cpl_tree_imp_l_inv_1_vars_in :
    forall {gamma : list formula} {A B : formula} (S : subst_ind) {OC : constraint},
        incl (flat_map vars_in gamma) (OC_list OC) ->
            incl (flat_map vars_in (imp_left_inv_1_batch gamma A B S)) (OC_list OC).
Proof.
induction gamma;
intros A B S OC SUB;
unfold imp_left_inv_1_batch, batch_sub, batch_sub_fit;
fold batch_sub_fit;
destruct S;
unfold length, nat_eqb;
fold (@length formula) (@length bool) nat_eqb.
4 : case nat_eqb eqn:EQN.
1,2,3,5 : apply SUB.
unfold flat_map;
fold (flat_map vars_in).
rewrite (batch_sub_fit_true EQN).
fold (imp_left_inv_1_batch gamma A B S).
apply incl_app_inv in SUB as [SUB1 SUB2].
apply (incl_app (imp_l_formula_inv_1_vars_in _ _ _ _ _ SUB1) (IHgamma _ _ _ _ SUB2)).
Qed.


Lemma imp_l_formula_inv_1_vars_used_sub :
    forall {phi : formula} {A B : formula} {b : bool},
        incl (vars_used (imp_left_inv_1_formula phi A B b)) (vars_used phi).
Proof.
intros phi A B b o IN.
unfold imp_left_inv_1_formula, formula_sub in IN.
case form_eqb eqn:EQF.
destruct b.
apply form_eqb_eq in EQF.
subst.
apply in_or_app,or_intror.
all : apply IN.
Qed.

Lemma imp_l_formula_inv_1_vars_used_sub_batch :
    forall {gamma : list formula} {A B : formula} {S : subst_ind},
        incl (flat_map vars_used (imp_left_inv_1_batch gamma A B S)) (flat_map vars_used gamma).
Proof.
induction gamma;
intros A B S o IN;
destruct S;
try contradiction IN;
unfold imp_left_inv_1_batch, batch_sub, batch_sub_fit, length, nat_eqb in IN.
apply IN.
fold (@length formula) (@length bool) nat_eqb batch_sub_fit in IN.
case nat_eqb eqn:EQL.
2 : apply IN.
rewrite (batch_sub_fit_true EQL) in IN.
apply in_app_or in IN as [IN1 | IN2].
apply in_or_app, or_introl, (imp_l_formula_inv_1_vars_used_sub _ IN1).
apply in_or_app, or_intror, (IHgamma _ _ _ _ IN2).
Qed.

Lemma cpl_tree_imp_l_inv_1_struct_aux :
    forall (T : cpl_tree) (A B : formula),
        structured T ->
            forall (S : subst_ind),
                structured (cpl_tree_imp_l_inv_1 T A B S).
Proof.
intros T A B.
induction T;
try intros Tstr S;
unfold cpl_tree_imp_l_inv_1;
unfold imp_left_inv_1_batch, batch_sub.

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : subst; 
      case nat_eqb eqn:EQ;
      unfold cpl_tree_imp_l_inv_1_fit;
      fold cpl_tree_imp_l_inv_1_fit;
      unfold cpl_tree_left in EQ;
      fold cpl_tree_left in EQ;
      try fold (cpl_tree_left T) in EQ;
      try fold (cpl_tree_left T1) in EQ;
      try fold (cpl_tree_left T2) in EQ.

5,13,19,23 : destruct S.

12 : case (form_eqb phi A) eqn:FEQ1.
12 : case (form_eqb psi B) eqn:FEQ2.
12 : destruct b.

2,4,5,7,9,11,16,18,20,22,23,25,27,28,30,31,33,35 : repeat split; try assumption; try apply (existT _ NEW (existT _ KIN TOC)).

14 :  { rewrite cpl_tree_imp_l_inv_1_fit_true.
        repeat split;
        try assumption.
        - apply (IHT Tstr).
        - unfold cpl_tree_left at 1.
          rewrite cpl_tree_imp_l_inv_1_left.
          apply (cpl_tree_imp_l_inv_1_vars_in S TG_app).
          apply Tstr.
        - apply cpl_tree_imp_l_inv_1_right, Tstr.
        - rewrite cpl_tree_imp_l_inv_1_left.
          intros FAL.
          apply KNING.
          apply (imp_l_formula_inv_1_vars_used_sub_batch _ FAL).
          apply Tstr.
        - rewrite <- TOC.
          apply cpl_tree_imp_l_inv_1_constraint, Tstr.
        - apply cpl_tree_imp_l_inv_1_deg, Tstr.
        - apply EQ. }

all : try rewrite !cpl_tree_imp_l_inv_1_fit_true;
      try rewrite TG;
      try rewrite T1G;
      try rewrite T2G;
      try rewrite bury_length, <- (@bury_unbury _ S n), bury_length in EQ;
      try apply EQ;
      repeat split;
      try apply (IHT Tstr);
      try apply (IHT1 T1str);
      try apply (IHT2 T2str);
      try apply (cpl_tree_imp_l_inv_1_vars_in _ TG_app);
      try apply (cpl_tree_imp_l_inv_1_vars_in _ TD_app);
      try rewrite cpl_tree_imp_l_inv_1_left;
      try rewrite cpl_tree_imp_l_inv_1_right;
      try rewrite cpl_tree_imp_l_inv_1_constraint;
      try rewrite cpl_tree_imp_l_inv_1_deg;
      try refine (existT _ NEW (existT _ KIN TOC));
      try apply Tstr;
      try apply T1str;
      try apply T2str;
      try rewrite TG;
      try rewrite T1G;
      try rewrite T2G;
      try rewrite TD;
      try rewrite T1D;
      try rewrite T2D;
      try rewrite T1OC;
      try rewrite T2OC;
      try apply EQ;
      try reflexivity;
      unfold imp_left_inv_1_batch, batch_sub, batch_sub_fit;
      fold batch_sub_fit;
      unfold length, nat_eqb in *;
      fold (@length formula) (@length bool) nat_eqb in *;
      try rewrite EQ;
      try rewrite formula_sub_false;
      try reflexivity;
      try apply TD_app;
      try assumption.

all : unfold cpl_tree_left in *;
      unfold imp_left_inv_1_formula;
      try fold (cpl_tree_left T) in *;
      try fold (cpl_tree_left T2) in *;
      try rewrite batch_sub_fold_head;
      try rewrite batch_sub_fit_true;
      try apply EQ;
      try rewrite batch_bury_comm;
      try apply (cpl_tree_imp_l_inv_1_vars_in S TG_app);
      try apply (cpl_tree_imp_l_inv_1_vars_in (b :: S) TG_app);
      unfold flat_map in *;
      fold (flat_map vars_in) in *;
      fold (flat_map vars_used) in *;
      try apply (incl_app (proj1 (incl_app_inv _ _ TG_app)) (cpl_tree_imp_l_inv_1_vars_in _ (proj2 (incl_app_inv _ _ TG_app))));
      try apply (incl_app (proj2 (incl_app_inv _ _ (proj1 (incl_app_inv _ _ TG_app)))) (cpl_tree_imp_l_inv_1_vars_in _ (proj2 (incl_app_inv _ _ TG_app)))).

1 : intros FAL.
    apply NING.
    apply (imp_l_formula_inv_1_vars_used_sub_batch _ FAL).
Qed.