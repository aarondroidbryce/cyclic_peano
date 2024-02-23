From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import constraints.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import proof_trees.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep_dec.


Inductive cpl_tree : Type :=
| leaf : forall (OC : constraint) (gamma delta : list formula) (alpha : ordinal), cpl_tree

| con_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| con_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| ex_l : forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| ex_r : forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| wkn_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| wkn_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| rst : forall {OC : constraint} {gamma delta : list formula} (kappa : ovar) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| bnd_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (lambda kappa : ovar) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| bnd_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (lambda kappa : ovar) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| imp_l : forall {OC : constraint} {gamma delta : list formula} (phi psi : formula) {alpha1 alpha2 : ordinal} (T1 T2 : cpl_tree), cpl_tree

| imp_r : forall {OC : constraint} {gamma delta : list formula} (phi psi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| cut : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha1 alpha2 : ordinal} (T1 T2 : cpl_tree), cpl_tree.

Definition cpl_tree_left (T : cpl_tree) : list formula :=
match T with
| leaf OC gamma delta alpha => gamma


| @con_l OC gamma delta phi alpha T' => phi :: gamma

| @con_r OC gamma delta phi alpha T' => gamma


| @ex_l OC gamma delta n alpha T' => bury gamma n

| @ex_r OC gamma delta n alpha T' => gamma


| @wkn_l OC gamma delta phi alpha T' => phi :: gamma

| @wkn_r OC gamma delta phi alpha T' => gamma

| @rst OC gamma delta kappa alpha T' => gamma


| @bnd_l OC gamma delta phi lambda kappa alpha T' => (bnd lambda kappa phi) :: gamma

| @bnd_r OC gamma delta phi lambda kappa alpha T' => gamma


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => (imp phi psi) :: gamma

| @imp_r OC gamma delta phi psi alpha T' => gamma


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => gamma
end.

Definition cpl_tree_right (T : cpl_tree) : list formula :=
match T with
| leaf OC gamma delta alpha => delta

| @con_l OC gamma delta phi alpha T' => delta

| @con_r OC gamma delta phi alpha T' => phi :: delta


| @ex_l OC gamma delta n alpha T' => delta

| @ex_r OC gamma delta n alpha T' => bury delta n


| @wkn_l OC gamma delta phi alpha T' => delta

| @wkn_r OC gamma delta phi alpha T' => phi :: delta

| @rst OC gamma delta kappa alpha T' => delta


| @bnd_l OC gamma delta phi lambda kappa alpha T' => delta

| @bnd_r OC gamma delta phi lambda kappa alpha T' => (bnd lambda kappa phi) :: delta


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => delta

| @imp_r OC gamma delta phi psi alpha T' => (imp phi psi) :: delta


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => delta
end.

Definition cpl_tree_constraint (T : cpl_tree) : constraint :=
match T with
| leaf OC gamma delta alpha => OC

| @con_l OC gamma delta phi alpha T' => OC

| @con_r OC gamma delta phi alpha T' => OC


| @ex_l OC gamma delta n alpha T' => OC

| @ex_r OC gamma delta n alpha T' => OC


| @wkn_l OC gamma delta phi alpha T' => OC

| @wkn_r OC gamma delta phi alpha T' => OC

| @rst OC gamma delta kappa alpha T' => OC


| @bnd_l OC gamma delta phi lambda kappa alpha T' => OC

| @bnd_r OC gamma delta phi lambda kappa alpha T' => OC


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => OC

| @imp_r OC gamma delta phi psi alpha T' => OC


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => OC
end.

Definition cpl_tree_deg (T : cpl_tree) : ordinal :=
match T with
| leaf OC gamma delta alpha => alpha

| @con_l OC gamma delta phi alpha T' => alpha

| @con_r OC gamma delta phi alpha T' => alpha


| @ex_l OC gamma delta n alpha T' => alpha

| @ex_r OC gamma delta n alpha T' => alpha


| @wkn_l OC gamma delta phi alpha T' => alpha

| @wkn_r OC gamma delta phi alpha T' => alpha

| @rst OC gamma delta L alpha T' => alpha

| @bnd_l OC gamma delta phi lambda kappa alpha T' => alpha

| @bnd_r OC gamma delta phi lambda kappa alpha T' => alpha


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => omax alpha1 alpha2

| @imp_r OC gamma delta phi psi alpha T' => alpha


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))
end.

Fixpoint cpl_leaves (T : cpl_tree) : (list (constraint * list formula * list formula * ordinal)) :=
match T with
| leaf OC gamma delta alpha => [(OC, gamma, delta, alpha)]

| @con_l OC gamma delta phi alpha T' => (cpl_leaves T')

| @con_r OC gamma delta phi alpha T' => (cpl_leaves T')


| @ex_l OC gamma delta n alpha T' => (cpl_leaves T')

| @ex_r OC gamma delta n alpha T' => (cpl_leaves T')


| @wkn_l OC gamma delta phi alpha T' => (cpl_leaves T')

| @wkn_r OC gamma delta phi alpha T' => (cpl_leaves T')

| @rst OC gamma delta kappa alpha T' => (cpl_leaves T')


| @bnd_l OC gamma delta phi lambda kappa alpha T' => (cpl_leaves T')

| @bnd_r OC gamma delta phi lambda kappa alpha T' => (cpl_leaves T')


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => (cpl_leaves T1) ++ (cpl_leaves T2)

| @imp_r OC gamma delta phi psi alpha T' => (cpl_leaves T')


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => (cpl_leaves T1) ++ (cpl_leaves T2)
end.

Lemma cpl_tree_eq_dec : forall (T1 T2 : cpl_tree), {T1 = T2} + {T1 <> T2}.
Proof.
induction T1;
destruct T2.

2-14 : right; discriminate.
3-15 : right; discriminate.
4-16 : right; discriminate.
5-17 : right; discriminate.
6-18 : right; discriminate.
7-19 : right; discriminate.
8-20 : right; discriminate.
9-21 : right; discriminate.
10-22 : right; discriminate.
11-23 : right; discriminate.
12-24 : right; discriminate.
13-25 : right; discriminate.

all : try destruct (nat_eq_dec n n0) as [EQN | NE];
      try destruct (IHT1 T2) as [EQ | NE];
			try destruct (IHT1_1 T2_1) as [EQ1 | NE];
      try destruct (IHT1_2 T2_2) as [EQ2 | NE];
      try destruct (prd_eq_dec pn pn0) as [EQT | NE];
      try destruct (constraint_eq_dec OC OC0) as [EQO | NE];
      try destruct (nat_eq_dec l l0) as [EQLEN | NE];
			try destruct (nat_eq_dec v v0) as [EQV | NE];
			try destruct (nat_eq_dec v1 v0) as [EQV1 | NE];
			try destruct (nat_eq_dec v2 v3) as [EQV2 | NE];
      try destruct (list_eq_dec form_eq_dec gamma gamma0) as [EQG | NE];
      try destruct (list_eq_dec form_eq_dec delta delta0) as [EQD | NE];
      try destruct (list_eq_dec form_eq_dec pi pi0) as [EQTI | NE];
			try destruct (list_eq_dec form_eq_dec sigma sigma0) as [EQS | NE];
      try destruct (form_eq_dec phi phi0) as [EQT1 | NE];
			try destruct (form_eq_dec psi psi0) as [EQT2 | NE];
			try destruct (ordinal_eq_dec alpha alpha0) as [EQA | NE];
      try destruct (ordinal_eq_dec alpha1 alpha0) as [EQA1 | NE];
      try destruct (ordinal_eq_dec alpha2 alpha3) as [EQA2 | NE];
			try destruct (nat_eq_dec kappa kappa0) as [EQK | NE];
      try destruct (nat_eq_dec lambda lambda0) as [EQL | NE];
      subst;
      try rewrite (proof_irrelevance _ e e0);
			try apply (left (eq_refl));
      right;
      intros FAL;
      inversion FAL as [FAL'];
      repeat apply inj_pair2 in FAL';
      try contradiction NE.
Qed.

Definition semi_applicable (OC : constraint) (T : cpl_tree) : Prop := (incl (flat_map vars_in (cpl_tree_left T)) (OC_list OC)) * (incl (flat_map vars_in (cpl_tree_right T)) (OC_list OC)).


Fixpoint structured (T : cpl_tree) : Type :=
match T with
| leaf OC gamma delta alpha => semi_applicable OC T

| @con_l OC gamma delta phi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = phi :: phi :: gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @con_r OC gamma delta phi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = phi :: phi :: delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))


| @ex_l OC gamma delta n alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @ex_r OC gamma delta n alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))


| @wkn_l OC gamma delta phi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @wkn_r OC gamma delta phi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @rst OC gamma delta kappa alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (~ In kappa (flat_map vars_used gamma)) * (~ In kappa (flat_map vars_used delta)) * {SUB : (OC_elt OC kappa) & cpl_tree_constraint T' = restriction OC (children OC kappa) (children_subset OC kappa)} * (cpl_tree_deg T' = alpha))

| @bnd_l OC gamma delta phi lambda kappa alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = phi :: gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (OC_rel OC lambda kappa = true) * (cpl_tree_deg T' = alpha))

| @bnd_r OC gamma delta phi lambda kappa alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = phi :: delta) * {NEW : ~ OC_elt OC lambda & {KIN : OC_elt OC kappa & cpl_tree_constraint T' = add_fresh_child OC lambda kappa NEW KIN}} * (~ In lambda (flat_map vars_used gamma) /\ ~ In lambda (flat_map vars_used (phi :: delta))) * (cpl_tree_deg T' = alpha))


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => (structured T1 * structured T2) * (semi_applicable OC T * (cpl_tree_left T1 = psi :: gamma) * (cpl_tree_right T1 = delta) * (cpl_tree_constraint T1 = OC) * (cpl_tree_left T2 = gamma) * (cpl_tree_right T2 = phi :: delta) * (cpl_tree_constraint T2 = OC) * (cpl_tree_deg T1 = alpha1) * (cpl_tree_deg T2 = alpha2))

| @imp_r OC gamma delta phi psi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = phi :: gamma) * (cpl_tree_right T' = psi :: delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => (structured T1 * structured T2) * (semi_applicable OC T * (cpl_tree_left T1 = gamma) * (cpl_tree_right T1 = phi :: delta) * (cpl_tree_constraint T1 = OC) * (cpl_tree_left T2 = phi :: gamma) * (cpl_tree_right T2 = delta) * (cpl_tree_constraint T2 = OC) * (cpl_tree_deg T1 = alpha1) * (cpl_tree_deg T2 = alpha2))
end.

Lemma test :
    forall (T : cpl_tree),
        structured T ->
            (forall L,
                In L (cpl_leaves T) ->
                    (uncurry (uncurry (uncurry provable))) L) ->
            provable (cpl_tree_constraint T) (cpl_tree_left T) (cpl_tree_right T) (cpl_tree_deg T).
Proof.
induction T;
intros Tstr LEAF.

1 : destruct Tstr as [TG_app TD_app].
2-7 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
8 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
11 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
12 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
13 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold provable in *;
      unfold cpl_tree_constraint, cpl_tree_left, cpl_tree_right, cpl_tree_deg.

1 : specialize (LEAF (OC, gamma, delta, alpha) (or_introl eq_refl)).
    apply LEAF.

1 : apply ptree_con_l.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply ptree_con_r.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply ptree_ex_l.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply ptree_ex_r.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply ptree_wkn_l.
    refine (incl_tran (fun f IN => in_or_app _ _ _ (or_introl IN)) TG_app).
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply ptree_wkn_r.
    refine (incl_tran (fun f IN => in_or_app _ _ _ (or_introl IN)) TD_app).
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply (ptree_reset _ _ _ kappa _ KNING KNIND KIN).
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply ptree_bnd_l.
    apply TOC_rel.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply (ptree_bnd_r _ _ _ _ _ _ _ NEW KIN NING NIND).
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply ptree_imp_l.
    rewrite <- T1G, <- T1D, <- T1OC, <- T1Deg.
    apply (IHT1 T1str (fun L IN => LEAF L (in_or_app _ _ _ (or_introl IN)))).
    rewrite <- T2G, <- T2D, <- T2OC, <- T2Deg.
    apply (IHT2 T2str (fun L IN => LEAF L (in_or_app _ _ _ (or_intror IN)))).

1 : apply ptree_imp_r.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply ptree_cut.
    rewrite <- T1G, <- T1D, <- T1OC, <- T1Deg.
    apply (IHT1 T1str (fun L IN => LEAF L (in_or_app _ _ _ (or_introl IN)))).
    rewrite <- T2G, <- T2D, <- T2OC, <- T2Deg.
    apply (IHT2 T2str (fun L IN => LEAF L (in_or_app _ _ _ (or_intror IN)))).
Qed.

(*
Master destruct tactic.

1 : destruct Tstr as [TG_app TD_app].
2-7 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
8 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
11 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
12 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
13 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

*)