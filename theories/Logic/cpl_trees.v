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
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.


Inductive cpl_tree : Type :=
| leaf : forall (OC : constraint) (gamma delta : list formula) (alpha : ordinal), cpl_tree

| deg_up : forall {OC : constraint} {gamma delta : list formula} {alpha : ordinal} (beta : ordinal) (b : bool) (T' : cpl_tree), cpl_tree 

| con_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| con_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| ex_l : forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| ex_r : forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| wkn_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| wkn_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| rst : forall {OC : constraint} {gamma delta : list formula} (kappa : ovar) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| nu_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (x : nat) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| nu_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (x : nat) (lambda : ovar) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| nuk_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (x : nat) (lambda kappa : ovar) {alpha : ordinal} (T' : cpl_tree), cpl_tree

| nuk_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (x : nat) (lambda kappa : ovar) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| imp_l : forall {OC : constraint} {gamma delta : list formula} (phi psi : formula) {alpha1 alpha2 : ordinal} (T1 T2 : cpl_tree), cpl_tree

| imp_r : forall {OC : constraint} {gamma delta : list formula} (phi psi : formula) {alpha : ordinal} (T' : cpl_tree), cpl_tree


| cut : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha1 alpha2 : ordinal} (T1 T2 : cpl_tree), cpl_tree.

Definition cpl_tree_left (T : cpl_tree) : list formula :=
match T with
| leaf OC gamma delta alpha => gamma

| @deg_up OC gamma delta alpha beta b T' => gamma 

| @con_l OC gamma delta phi alpha T' => phi :: gamma

| @con_r OC gamma delta phi alpha T' => gamma


| @ex_l OC gamma delta n alpha T' => bury gamma n

| @ex_r OC gamma delta n alpha T' => gamma


| @wkn_l OC gamma delta phi alpha T' => phi :: gamma

| @wkn_r OC gamma delta phi alpha T' => gamma

| @rst OC gamma delta kappa alpha T' => gamma


| @nu_l OC gamma delta phi x alpha T' => (nu x phi) :: gamma

| @nu_r OC gamma delta phi x lambda alpha T' => gamma

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => (nuk x kappa phi) :: gamma

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => gamma


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => (imp phi psi) :: gamma

| @imp_r OC gamma delta phi psi alpha T' => gamma


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => gamma
end.

Definition cpl_tree_right (T : cpl_tree) : list formula :=
match T with
| leaf OC gamma delta alpha => delta

| @deg_up OC gamma delta alpha beta b T' => delta

| @con_l OC gamma delta phi alpha T' => delta

| @con_r OC gamma delta phi alpha T' => phi :: delta


| @ex_l OC gamma delta n alpha T' => delta

| @ex_r OC gamma delta n alpha T' => bury delta n


| @wkn_l OC gamma delta phi alpha T' => delta

| @wkn_r OC gamma delta phi alpha T' => phi :: delta

| @rst OC gamma delta kappa alpha T' => delta


| @nu_l OC gamma delta phi x alpha T' => delta

| @nu_r OC gamma delta phi x lambda alpha T' => (nu x phi) :: delta

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => delta

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => (nuk x kappa phi) :: delta


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => delta

| @imp_r OC gamma delta phi psi alpha T' => (imp phi psi) :: delta


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => delta
end.

Definition cpl_tree_constraint (T : cpl_tree) : constraint :=
match T with
| leaf OC gamma delta alpha => OC

| @deg_up OC gamma delta alpha beta b T' => OC

| @con_l OC gamma delta phi alpha T' => OC

| @con_r OC gamma delta phi alpha T' => OC


| @ex_l OC gamma delta n alpha T' => OC

| @ex_r OC gamma delta n alpha T' => OC


| @wkn_l OC gamma delta phi alpha T' => OC

| @wkn_r OC gamma delta phi alpha T' => OC

| @rst OC gamma delta kappa alpha T' => OC


| @nu_l OC gamma delta phi x alpha T' => OC

| @nu_r OC gamma delta phi x lambda alpha T' => OC

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => OC

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => OC


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => OC

| @imp_r OC gamma delta phi psi alpha T' => OC


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => OC
end.

Definition cpl_tree_deg (T : cpl_tree) : ordinal :=
match T with
| leaf OC gamma delta alpha => alpha

| @deg_up OC gamma delta alpha beta true T' => omax alpha beta

| @deg_up OC gamma delta alpha beta false T' => omax beta alpha

| @con_l OC gamma delta phi alpha T' => alpha

| @con_r OC gamma delta phi alpha T' => alpha


| @ex_l OC gamma delta n alpha T' => alpha

| @ex_r OC gamma delta n alpha T' => alpha


| @wkn_l OC gamma delta phi alpha T' => alpha

| @wkn_r OC gamma delta phi alpha T' => alpha

| @rst OC gamma delta L alpha T' => alpha

| @nu_l OC gamma delta phi x alpha T' => alpha

| @nu_r OC gamma delta phi x lambda alpha T' => alpha

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => alpha

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => alpha


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => omax alpha1 alpha2

| @imp_r OC gamma delta phi psi alpha T' => alpha


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))
end.

Fixpoint cpl_leaves (T : cpl_tree) : (list (constraint * list formula * list formula * ordinal)) :=
match T with
| leaf OC gamma delta alpha => [(OC, gamma, delta, alpha)]

| @deg_up OC gamma delta alpha beta b T' => (cpl_leaves T')

| @con_l OC gamma delta phi alpha T' => (cpl_leaves T')

| @con_r OC gamma delta phi alpha T' => (cpl_leaves T')


| @ex_l OC gamma delta n alpha T' => (cpl_leaves T')

| @ex_r OC gamma delta n alpha T' => (cpl_leaves T')


| @wkn_l OC gamma delta phi alpha T' => (cpl_leaves T')

| @wkn_r OC gamma delta phi alpha T' => (cpl_leaves T')

| @rst OC gamma delta kappa alpha T' => (cpl_leaves T')


| @nu_l OC gamma delta phi x alpha T' => (cpl_leaves T')

| @nu_r OC gamma delta phi x lambda alpha T' => (cpl_leaves T')

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => (cpl_leaves T')

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => (cpl_leaves T')


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => (cpl_leaves T1) ++ (cpl_leaves T2)

| @imp_r OC gamma delta phi psi alpha T' => (cpl_leaves T')


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => (cpl_leaves T1) ++ (cpl_leaves T2)
end.


Fixpoint cpl_tree_depth (T : cpl_tree) : nat :=
match T with
| leaf OC gamma delta alpha => 0

| @deg_up OC gamma delta alpha beta b T' => cpl_tree_depth T'

| @con_l OC gamma delta phi alpha T' => cpl_tree_depth T'

| @con_r OC gamma delta phi alpha T' => cpl_tree_depth T'


| @ex_l OC gamma delta n alpha T' => cpl_tree_depth T'

| @ex_r OC gamma delta n alpha T' => cpl_tree_depth T'


| @wkn_l OC gamma delta phi alpha T' => cpl_tree_depth T'

| @wkn_r OC gamma delta phi alpha T' => cpl_tree_depth T'

| @rst OC gamma delta kappa alpha T' => cpl_tree_depth T'


| @nu_l OC gamma delta phi x alpha T' => S (cpl_tree_depth T')

| @nu_r OC gamma delta phi x lambda alpha T' => S (cpl_tree_depth T')

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => S (cpl_tree_depth T')

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => S (cpl_tree_depth T')


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => S (max (cpl_tree_depth T1) (cpl_tree_depth T2))

| @imp_r OC gamma delta phi psi alpha T' => S (cpl_tree_depth T')


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => S (max (cpl_tree_depth T1) (cpl_tree_depth T2))
end.

Lemma cpl_tree_eq_dec : forall (T1 T2 : cpl_tree), {T1 = T2} + {T1 <> T2}.
Proof.
induction T1;
destruct T2.

2-17 : right; discriminate.
3-18 : right; discriminate.
4-19 : right; discriminate.
5-20 : right; discriminate.
6-21 : right; discriminate.
7-22 : right; discriminate.
8-23 : right; discriminate.
9-24 : right; discriminate.
10-25 : right; discriminate.
11-26 : right; discriminate.
12-27 : right; discriminate.
13-28 : right; discriminate.
14-29 : right; discriminate.

all : try destruct (nat_eq_dec n n0) as [EQN | NE];
      try destruct (nat_eq_dec x x0) as [EQX | NE];
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
      try destruct (ordinal_eq_dec beta beta0) as [EQB | NE];
      try destruct (ordinal_eq_dec alpha1 alpha0) as [EQA1 | NE];
      try destruct (ordinal_eq_dec alpha2 alpha3) as [EQA2 | NE];
			try destruct (nat_eq_dec kappa kappa0) as [EQK | NE];
      try destruct (nat_eq_dec lambda lambda0) as [EQL | NE];
      try destruct (Bool.bool_dec b b0) as [EQBL | NE];
      subst;
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

| @deg_up OC gamma delta alpha beta b T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @con_l OC gamma delta phi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = phi :: phi :: gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @con_r OC gamma delta phi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = phi :: phi :: delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))


| @ex_l OC gamma delta n alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @ex_r OC gamma delta n alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))


| @wkn_l OC gamma delta phi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @wkn_r OC gamma delta phi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @rst OC gamma delta kappa alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (~ In kappa (flat_map vars_used gamma)) * (~ In kappa (flat_map vars_used delta)) * {SUB : (OC_elt OC kappa) & cpl_tree_constraint T' = restriction OC (children OC kappa) (children_subset OC kappa)} * (cpl_tree_deg T' = alpha))


| @nu_l OC gamma delta phi x alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = (pvar_sub phi x (nu x phi)) :: gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

| @nu_r OC gamma delta phi x lambda alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = (nuk x lambda phi) :: delta) * {NEW : ~ OC_elt OC lambda & cpl_tree_constraint T' = (add_fresh OC lambda NEW)} * (~ In lambda (flat_map vars_used gamma) /\ ~ In lambda (flat_map vars_used (phi :: delta))) * (cpl_tree_deg T' = alpha))

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = (pvar_sub phi x (nuk x lambda phi)) :: gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (OC_rel OC lambda kappa = true) * (cpl_tree_deg T' = alpha))

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = (pvar_sub phi x (nuk x lambda phi)) :: delta) * {NEW : ~ OC_elt OC lambda & {KIN : OC_elt OC kappa & cpl_tree_constraint T' = add_fresh_child OC lambda kappa NEW KIN}} * (~ In lambda (flat_map vars_used gamma) /\ ~ In lambda (flat_map vars_used (phi :: delta))) * (cpl_tree_deg T' = alpha))


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => (structured T1 * structured T2) * (semi_applicable OC T * (cpl_tree_left T1 = psi :: gamma) * (cpl_tree_right T1 = delta) * (cpl_tree_constraint T1 = OC) * (cpl_tree_left T2 = gamma) * (cpl_tree_right T2 = phi :: delta) * (cpl_tree_constraint T2 = OC) * (cpl_tree_deg T1 = alpha1) * (cpl_tree_deg T2 = alpha2))

| @imp_r OC gamma delta phi psi alpha T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = phi :: gamma) * (cpl_tree_right T' = psi :: delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => (structured T1 * structured T2) * (semi_applicable OC T * (cpl_tree_left T1 = gamma) * (cpl_tree_right T1 = phi :: delta) * (cpl_tree_constraint T1 = OC) * (cpl_tree_left T2 = phi :: gamma) * (cpl_tree_right T2 = delta) * (cpl_tree_constraint T2 = OC) * (cpl_tree_deg T1 = alpha1) * (cpl_tree_deg T2 = alpha2))
end.

Lemma cpl_last_is_showable :
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
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW TOC]] [NING NIND]] TDeg]].
12 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
13 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
15 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
16 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold provable in *;
      unfold cpl_tree_constraint, cpl_tree_left, cpl_tree_right, cpl_tree_deg.

1 : specialize (LEAF (OC, gamma, delta, alpha) (or_introl eq_refl)).
    apply LEAF.

1 : destruct b.
    apply ptree_deg_up_1.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).
    apply ptree_deg_up_2.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

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

1 : apply ptree_nu_l.
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply (ptree_nu_r _ _ _ _ _ _ _ NEW NING NIND).
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply (ptree_nuk_l _ _ _ _ _ _ _ _ TOC_rel).
    rewrite <- TG, <- TD, <- TOC, <- TDeg.
    apply (IHT Tstr LEAF).

1 : apply (ptree_nuk_r _ _ _ _ _ _ _ _ NEW KIN NING NIND).
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

Fixpoint left_ops (T : cpl_tree) : nat :=
match T with
| leaf OC gamma delta alpha => 0

| @deg_up OC gamma delta alpha beta b T' => left_ops T'

| @con_l OC gamma delta phi alpha T' => S (left_ops T')

| @con_r OC gamma delta phi alpha T' => left_ops T'


| @ex_l OC gamma delta n alpha T' => left_ops T'

| @ex_r OC gamma delta n alpha T' => left_ops T'


| @wkn_l OC gamma delta phi alpha T' => left_ops T'

| @wkn_r OC gamma delta phi alpha T' => left_ops T'

| @rst OC gamma delta kappa alpha T' => left_ops T'


| @nu_l OC gamma delta phi x alpha T' => left_ops T'

| @nu_r OC gamma delta phi x lambda alpha T' => left_ops T'

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => left_ops T'

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => left_ops T'


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => max (left_ops T1) (left_ops T2)

| @imp_r OC gamma delta phi psi alpha T' => left_ops T'


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => max (left_ops T1) (left_ops T2)
end.

Fixpoint right_ops (T : cpl_tree) : nat :=
match T with
| leaf OC gamma delta alpha => 0

| @deg_up OC gamma delta alpha beta b T' => right_ops T'

| @con_l OC gamma delta phi alpha T' => right_ops T'

| @con_r OC gamma delta phi alpha T' => S (right_ops T')


| @ex_l OC gamma delta n alpha T' => right_ops T'

| @ex_r OC gamma delta n alpha T' => right_ops T'


| @wkn_l OC gamma delta phi alpha T' => right_ops T'

| @wkn_r OC gamma delta phi alpha T' => right_ops T'

| @rst OC gamma delta kappa alpha T' => right_ops T'


| @nu_l OC gamma delta phi x alpha T' => right_ops T'

| @nu_r OC gamma delta phi x lambda alpha T' => right_ops T'

| @nuk_l OC gamma delta phi x lambda kappa alpha T' => right_ops T'

| @nuk_r OC gamma delta phi x lambda kappa alpha T' => right_ops T'


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => max (right_ops T1) (right_ops T2)

| @imp_r OC gamma delta phi psi alpha T' => right_ops T'


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => max (right_ops T1) (right_ops T2)
end.

Definition T_shows (T : cpl_tree) (OC : constraint) (gamma delta : list formula) (alpha : ordinal) (d l r : nat) : Type :=
  (structured T) * (cpl_tree_left T = gamma) * (cpl_tree_right T = delta) * (cpl_tree_constraint T = OC) * (cpl_tree_deg T = alpha) * (cpl_tree_depth T = d) * (left_ops T = l) * (right_ops T = r).

Definition showable (OC : constraint) (gamma delta : list formula) (alpha : ordinal) (d l r: nat) : Type :=
  {T : cpl_tree & (T_shows T OC gamma delta alpha d l r)}.

Lemma structured_OC_semiapp :
  forall (T : cpl_tree),
      structured T ->
          semi_applicable (cpl_tree_constraint T) T.
Proof.
induction T;
intros Tstr.

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW TOC]] [NING NIND]] TDeg]].
12 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
13 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
15 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
16 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : repeat split;
      unfold cpl_tree_left, cpl_tree_right, flat_map, vars_in;
      fold vars_in (flat_map vars_in);
      try apply TG_app;
      try apply TD_app.
Qed.


Lemma cpl_tree_deg_up_1 :
  forall {OC : constraint} {gamma delta : list formula} {alpha : ordinal} (beta : ordinal) {d l r: nat},
      showable OC gamma delta alpha d l r ->
          showable OC gamma delta (omax alpha beta) d l r.
Proof.
intros OC gamma delta alpha beta d l r [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (deg_up beta true T) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ Tstr)).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_deg_up_2 :
  forall {OC : constraint} {gamma delta : list formula} {alpha : ordinal} (beta : ordinal) {d l r: nat},
      showable OC gamma delta alpha d l r ->
          showable OC gamma delta (omax beta alpha) d l r.
Proof.
intros OC gamma delta alpha beta d l r [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (deg_up beta false T) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ Tstr)).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_con_l :
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha : ordinal} {d l r: nat},
      showable OC (phi :: phi :: gamma) delta alpha d l r ->
          showable OC (phi :: gamma) delta alpha d (S l) r.
Proof.
intros OC gamma delta phi alpha d l r [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (con_l phi T) _).
repeat split;
try assumption.
1 : refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ (phi :: phi :: gamma) (fun (A : formula) (IN : In A (phi :: gamma)) => (or_intror IN))) _).
  rewrite <- Tgam.
  apply (fst (structured_OC_semiapp _ Tstr)).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_con_r :
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha : ordinal} {d l r: nat},
      showable OC gamma (phi :: phi :: delta) alpha d l r ->
          showable OC gamma (phi :: delta) alpha d l (S r).
Proof.
intros OC gamma delta phi alpha d l r [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (con_r phi T) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ Tstr)).
1 : refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ (phi :: phi :: delta) (fun (A : formula) (IN : In A (phi :: delta)) => (or_intror IN))) _).
    rewrite <- Tdelt.
    apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_ex_l : 
  forall {OC : constraint} {gamma delta : list formula} {n : nat} {alpha : ordinal} {d l r: nat},
      showable OC gamma delta alpha d l r->
          showable OC (bury gamma n) delta alpha d l r.
Proof.
intros OC gamma delta n alpha d l r [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (ex_l n T) _).
repeat split;
try assumption.
1 : refine (incl_tran (fun A => proj1 (flat_map_bury_incl A)) (fst (structured_OC_semiapp _ Tstr))).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_ex_r : 
  forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} {d l r: nat},
      showable OC gamma delta alpha d l r->
          showable OC gamma (bury delta n) alpha d l r.
Proof.
intros OC gamma delta n alpha d l r [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (ex_r n T) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ Tstr)).
1 : refine (incl_tran (fun A => proj1 (flat_map_bury_incl A)) (snd (structured_OC_semiapp _ Tstr))).
Qed.

Lemma cpl_tree_wkn_l : 
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha: ordinal} {d l r : nat},
      incl (vars_in phi) (OC_list OC) ->
          showable OC gamma delta alpha d l r->
              showable OC (phi :: gamma) delta alpha d l r.
Proof.
intros OC gamma delta phi alpha d l r SUB [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (wkn_l phi T) _).
repeat split;
try assumption.
1 : apply (incl_app SUB (fst (structured_OC_semiapp _ Tstr))).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_wkn_r : 
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha: ordinal} {d l r : nat},
      incl (vars_in phi) (OC_list OC) ->
          showable OC gamma delta alpha d l r->
              showable OC gamma (phi :: delta) alpha d l r.
Proof.
intros OC gamma delta phi alpha d l r SUB [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (wkn_r phi T) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ Tstr)).
1 : apply (incl_app SUB (snd (structured_OC_semiapp _ Tstr))).
Qed.

Lemma cpl_tree_weaken_left : 
  forall {gamma delta sigma : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      incl (flat_map vars_in sigma) (OC_list OC) ->
          showable OC gamma delta alpha d l r ->
              showable OC (gamma ++ sigma) delta alpha d l r.
Proof.
intros gamma delta sigma.
revert gamma delta.
apply (rev_ind_type (fun sigma => forall (gamma delta : list formula) (OC : constraint) (alpha : ordinal) (d l r : nat), incl (flat_map vars_in sigma) (OC_list OC) -> showable OC gamma delta alpha d l r-> showable OC (gamma ++ sigma) delta alpha d l r)).
- intros gamma delta OC alpha d l r SUB Tshow.
  rewrite app_nil_r.
  apply Tshow.
- intros phi sigma' IND gamma delta OC alpha d l r SUB Tshow.
  rewrite app_assoc.
  rewrite <- (app_nil_l ((gamma ++ sigma') ++ [phi])), <- (@bury_type _ phi [] (gamma ++ sigma')), app_nil_l.
  apply cpl_tree_ex_l, cpl_tree_wkn_l, IND, Tshow;
  rewrite flat_map_app in SUB.
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_intror (in_or_app _ _ _ (or_introl IN))))).
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_introl IN))).
Qed.

Lemma cpl_tree_weaken_right : 
  forall {gamma delta pi : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      incl (flat_map vars_in pi) (OC_list OC) ->
          showable OC gamma delta alpha d l r ->
              showable OC gamma (delta ++ pi) alpha d l r.
Proof.
intros gamma delta pi.
revert gamma delta.
apply (rev_ind_type (fun pi => forall (gamma delta : list formula) (OC : constraint) (alpha : ordinal) (d l r : nat), incl (flat_map vars_in pi) (OC_list OC) -> showable OC gamma delta alpha d l r -> showable OC gamma (delta ++ pi) alpha d l r)).
- intros gamma delta OC alpha d l r SUB Tshow.
  rewrite app_nil_r.
  apply Tshow.
- intros phi pi' IND gamma delta OC alpha d l r SUB Tshow.
  rewrite app_assoc.
  rewrite <- (app_nil_l ((delta ++ pi') ++ [phi])), <- (@bury_type _ phi [] (delta ++ pi')), app_nil_l.
  apply cpl_tree_ex_r, cpl_tree_wkn_r, IND, Tshow;
  rewrite flat_map_app in SUB.
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_intror (in_or_app _ _ _ (or_introl IN))))).
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_introl IN))).
Qed.

Lemma cpl_tree_reset : 
  forall {gamma delta : list formula} {OC : constraint} {kappa : ovar} {alpha: ordinal} {d l r : nat},
      ~ In kappa (flat_map vars_used gamma) ->
          ~ In kappa (flat_map vars_used delta) ->
              OC_elt OC kappa ->
                  showable (restriction OC (children OC kappa) (children_subset OC kappa)) gamma delta alpha d l r ->
                      showable OC gamma delta alpha d l r.
Proof.
intros gamma delta OC kappa alpha d l r NING NIND ELT [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (rst kappa T) _).
repeat split;
try assumption.
1 : apply (incl_tran (fst (structured_OC_semiapp _ Tstr))).
2 : apply (incl_tran (snd (structured_OC_semiapp _ Tstr))).
1,2 : rewrite Tcon;
      apply incl_filter.
Qed.

Lemma cpl_tree_nu_l : 
    forall {OC : constraint} {gamma delta : list formula} {phi : formula} {x : nat} {alpha : ordinal} {d l r : nat},
        showable OC ((pvar_sub phi x (nu x phi)) :: gamma) delta alpha d l r ->
                showable OC ((nu x phi) :: gamma) delta alpha (S d) l r.
Proof.
intros OC gamma delta phi x alpha d l r [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (nu_l phi x T) _).
repeat split;
try assumption.
1 : intros o IN.
    apply (fst (structured_OC_semiapp _ Tstr)).
    rewrite Tgam.
    apply in_app_or in IN as [IN1 | IN2].
    apply in_or_app, or_introl, vars_in_in_psub, IN1.
    apply in_or_app, or_intror, IN2.
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_nu_r :
    forall {OC : constraint} {gamma delta : list formula} {phi : formula} {x : nat} {lambda : ovar} {alpha : ordinal} {d l r : nat} (NEW : ~ OC_elt OC lambda),
        ~ In lambda (flat_map vars_used gamma) ->
            ~ In lambda (flat_map vars_used (phi :: delta)) ->
                showable (add_fresh OC lambda NEW) gamma ((nuk x lambda phi) :: delta) alpha d l r ->
                    showable OC gamma ((nu x phi) :: delta) alpha (S d) l r.
Proof.
intros OC gamma delta phi x lambda alpha d l r NEW NING NIND [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (nu_r phi x lambda T) _).
repeat split;
try assumption.
3 : refine (existT _ NEW Tcon).
1 : intros o IN.
    pose proof ((fst (structured_OC_semiapp _ Tstr)) o IN) as TG_app.
    rewrite Tcon in TG_app.
    unfold OC_list, add_fresh_child, projT1 in TG_app.
    destruct TG_app as [EQ | TG_app].
    subst.
    contradiction (NING (vars_in_list_is_used _ _ IN)).
    apply TG_app.    
1 : intros o IN.
    pose proof ((snd (structured_OC_semiapp _ Tstr)) o) as TD_app;
    rewrite Tdelt, Tcon in TD_app.
    specialize (TD_app (or_intror IN)).
    unfold OC_list, add_fresh, projT1 in TD_app.
    destruct TD_app as [EQ | TD_app];
    subst.
    apply in_app_or in IN as [IN1 | IN2].
    contradiction (NIND (in_or_app _ _ _ (or_introl (vars_in_is_used _ _ IN1)))).
    contradiction (NIND (in_or_app _ _ _ (or_intror (vars_in_list_is_used _ _  IN2)))).
    apply TD_app.
Qed.

Lemma cpl_tree_nuk_l : 
    forall {OC : constraint} {gamma delta : list formula} {phi : formula} {x : nat} {lambda kappa : ovar} {alpha : ordinal} {d l r : nat},
        OC_rel OC lambda kappa = true ->
            showable OC ((pvar_sub phi x (nuk x lambda phi)) :: gamma) delta alpha d l r ->
                showable OC ((nuk x kappa phi) :: gamma) delta alpha (S d) l r.
Proof.
intros OC gamma delta phi x lambda kappa alpha d l r rel [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (nuk_l phi x lambda kappa T) _).
repeat split;
try assumption.
1 : intros o IN.
    apply in_app_or in IN as [[EQ | IN1] | IN2].
    subst.
    apply (OC_null _ _ _ rel).
    1,2 : apply (fst (structured_OC_semiapp _ Tstr));
          rewrite Tgam.
    apply in_or_app, or_introl, vars_in_in_psub, IN1.
    apply in_or_app, or_intror, IN2.
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_nuk_r : 
    forall {OC : constraint} {gamma delta : list formula} {phi : formula} {x : nat} {lambda kappa : ovar} {alpha : ordinal} {d l r : nat} (NEW : ~ OC_elt OC lambda) (KIN : OC_elt OC kappa),
        ~ In lambda (flat_map vars_used gamma) ->
            ~ In lambda (flat_map vars_used (phi :: delta)) ->
                showable (add_fresh_child OC lambda kappa NEW KIN) gamma ((pvar_sub phi x (nuk x lambda phi)) :: delta) alpha d l r ->
                    showable OC gamma ((nuk x kappa phi) :: delta) alpha (S d) l r.
Proof.
intros OC gamma delta phi x lambda kappa alpha d l r NEW KIN NING NIND [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (nuk_r phi x lambda kappa T) _).
repeat split;
try assumption.
3 : refine (existT _ NEW (existT _ KIN Tcon)).
1 : intros o IN.
    pose proof ((fst (structured_OC_semiapp _ Tstr)) o IN) as TG_app.
    rewrite Tcon in TG_app.
    unfold OC_list, add_fresh_child, projT1 in TG_app.
    destruct TG_app as [EQ | TG_app].
    subst.
    contradiction (NING (vars_in_list_is_used _ _ IN)).
    apply TG_app.    
1 : intros o [EQ | IN].
    subst.
    apply KIN.
    pose proof ((snd (structured_OC_semiapp _ Tstr)) o) as TD_app.
    rewrite Tdelt, Tcon in TD_app.
    apply in_app_or in IN as [IN1 | IN2];
    try specialize (TD_app (in_or_app _ _ _ (or_introl (vars_in_in_psub IN1))));
    try specialize (TD_app (in_or_app _ _ _ (or_intror IN2)));
    unfold OC_list, add_fresh_child, projT1 in TD_app;
    destruct TD_app as [EQ | TD_app];
    subst.
    2,4 : apply TD_app.
    1 : contradiction (NIND (in_or_app _ _ _ (or_introl (vars_in_is_used _ _ IN1)))).
    1 : contradiction (NIND (in_or_app _ _ _ (or_intror (vars_in_list_is_used _ _  IN2)))).
Qed.

(*
Lemma cpl_tree_bnd_l : 
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {lambda kappa : ovar} {alpha : ordinal} {d l r : nat},
      OC_rel OC lambda kappa = true ->
          showable OC (phi :: gamma) delta alpha d l r ->
              showable OC ((bnd lambda kappa phi) :: gamma) delta alpha (S d) l r.
Proof.
intros OC gamma delta phi lambda kappa alpha d l r rel [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (bnd_l phi lambda kappa T) _).
repeat split;
try assumption.
1 : { intros o IN.
    apply in_app_or in IN as [[IN1 | IN2] | IN3].
    - subst.
      apply (OC_null _ _ _ rel).
    - apply in_remove in IN2 as [IN2 _].
      apply (fst (structured_OC_semiapp _ Tstr)).
      rewrite Tgam.
      apply in_or_app, or_introl, IN2.
    - apply (fst (structured_OC_semiapp _ Tstr)).
      rewrite Tgam.
      apply in_or_app, or_intror, IN3. }
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_bnd_r : 
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {lambda kappa : ovar} {alpha : ordinal} {d l r : nat} (NEW : ~ OC_elt OC lambda) (KIN : OC_elt OC kappa),
      ~ In lambda (flat_map vars_used gamma) ->
          ~ In lambda (flat_map vars_used (phi :: delta)) ->
              showable (add_fresh_child OC lambda kappa NEW KIN) gamma (phi :: delta) alpha d l r ->
                  showable OC gamma ((bnd lambda kappa phi) :: delta) alpha (S d) l r.
Proof.
intros OC gamma delta phi lambda kappa alpha d l r NEW KIN NING NIND [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (bnd_r phi lambda kappa T) _).
repeat split;
try assumption.
3 : refine (existT _ NEW (existT _ KIN Tcon)).
1 : intros o IN.
  pose proof ((fst (structured_OC_semiapp _ Tstr)) o IN) as PG_app.
  rewrite Tcon in PG_app.
  unfold OC_list, add_fresh_child, projT1 in PG_app.
  destruct PG_app as [EQ | PG_app].
  subst.
  contradiction (NING (vars_in_list_is_used _ _ IN)).
  apply PG_app.    
1 : { intros o [EQ | IN].
    1 : subst.
        apply KIN.
    1 : apply in_app_or in IN as [IN1 | IN2].
        apply  in_remove in IN1 as [IN1 _].
    all : pose proof ((snd (structured_OC_semiapp _ Tstr)) o) as PD_app;
          rewrite Tdelt, Tcon in PD_app;
          try specialize (PD_app (in_or_app _ _ _ (or_introl IN1)));
          try specialize (PD_app (in_or_app _ _ _ (or_intror IN2)));
          unfold OC_list, add_fresh_child, projT1 in PD_app;
          destruct PD_app as [EQ | PD_app];
          subst.
    1 : contradiction (NIND (in_or_app _ _ _ (or_introl (vars_in_is_used _ _ IN1)))).
    1 : apply PD_app.
    1 : contradiction (NIND (in_or_app _ _ _ (or_intror (vars_in_list_is_used _ _  IN2)))).
    1 : apply PD_app. }
Qed.
*)

Lemma cpl_tree_imp_l : 
  forall {OC : constraint} {gamma delta : list formula} {phi psi : formula} {alpha1 alpha2 : ordinal} {d1 d2 l1 l2 r1 r2 : nat},
      showable OC (psi :: gamma) delta alpha1 d1 l1 r1 ->
          showable OC gamma (phi :: delta) alpha2 d2 l2 r2 ->
              showable OC ((imp phi psi) :: gamma) delta (omax alpha1 alpha2) (S (max d1 d2)) (max l1 l2) (max r1 r2).
Proof.
intros OC gamma delta phi psi alpha1 alpha2 d1 d2 l1 l2 r1 r2 [T1 [[[[[[[T1str T1gam] T1delt] T1con] T1deg] T1dep] T1left] T1right]] [T2 [[[[[[[T2str T2gam] T2delt] T2con] T2deg] T2dep] T2left] T2right]].
subst.
refine (existT _ (imp_l phi psi T1 T2) _).
repeat split;
try assumption.
1 : intros o IN.
  repeat apply in_app_or in IN as [IN | IN].
1 : rewrite <- T2con.
    apply (snd (structured_OC_semiapp _ T2str)).
    rewrite T2delt.
    apply (in_or_app _ _ _ (or_introl IN)).
1 : apply (fst (structured_OC_semiapp _ T1str)).
    rewrite T1gam.
    apply (in_or_app _ _ _ (or_introl IN)).
1 : rewrite <- T2con.
    apply (fst (structured_OC_semiapp _ T2str)), IN.
1 : apply (snd (structured_OC_semiapp _ T1str)).
Qed.

Lemma cpl_tree_imp_r : 
  forall {OC : constraint} {gamma delta : list formula} {phi psi : formula} {alpha : ordinal} {d l r : nat},
      showable OC (phi :: gamma) (psi :: delta) alpha d l r ->
          showable OC gamma ((imp phi psi) :: delta) alpha (S d) l r.
Proof.
intros OC gamma delta phi psi alpha d l r [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
subst.
refine (existT _ (imp_r phi psi T) _).
repeat split;
try assumption.
1 : refine (incl_tran _ (fst (structured_OC_semiapp _ Tstr))).
    rewrite Tgam.
    apply (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ (phi :: gamma) (fun (A : formula) (IN : In A gamma) => (or_intror IN))).
1 : intros o IN.
    repeat apply in_app_or in IN as [IN | IN].
1 : apply (fst (structured_OC_semiapp _ Tstr)).
    rewrite Tgam.
    apply (in_or_app _ _ _ (or_introl IN)).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
    rewrite Tdelt.
    apply (in_or_app _ _ _ (or_introl IN)).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
    rewrite Tdelt.
    apply (in_or_app _ _ _ (or_intror IN)).
Qed.

Lemma cpl_tree_cut : 
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha1 alpha2 : ordinal} {d1 d2 l1 l2 r1 r2 : nat},
      showable OC gamma (phi :: delta) alpha1 d1 l1 r1 ->
          showable OC (phi :: gamma) delta alpha2 d2 l2 r2 ->
              showable OC gamma delta (omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))) (S (max d1 d2)) (max l1 l2) (max r1 r2).
Proof.
intros OC gamma delta phi alpha1 alpha2 d1 d2 l1 l2 r1 r2 [T1 [[[[[[[T1str T1gam] T1delt] T1con] T1deg] T1dep] T1left] T1right]] [T2 [[[[[[[T2str T2gam] T2delt] T2con] T2deg] T2dep] T2left] T2right]].
subst.
refine (existT _ (cut phi T1 T2) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ T1str)).
1 : rewrite <- T2con.
    apply (snd (structured_OC_semiapp _ T2str)).
Qed.

Lemma commutative_left_aux :
  forall {LN : list nat} {gamma1 gamma2 delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      (set_bury gamma1 LN = gamma2) ->
          showable OC gamma1 delta alpha d l r ->
              showable OC gamma2 delta alpha d l r.
Proof.
induction LN;
intros gamma1 gamma2 delta OC alpha d l r EQ Tshow.
- unfold set_bury in EQ.
  subst.
  apply Tshow.
- unfold set_bury in EQ;
  fold @set_bury in EQ.
  apply (IHLN _ _ _ _ _ _ _ _ EQ), cpl_tree_ex_l, Tshow.
Qed.

Lemma cpl_tree_comm_left :
  forall {gamma1 gamma2 delta : list formula} {OC : constraint} {alpha : ordinal} {d l r : nat},
      (perm gamma1 gamma2) ->
          showable OC gamma1 delta alpha d l r ->
              showable OC gamma2 delta alpha d l r.
Proof.
intros gamma1 gamma2 delta OC alpha d l r perm SHOW.
pose proof (set_bury_eq_perm perm) as [LN EQ].
apply (commutative_left_aux EQ SHOW).
Defined.

Lemma prove_dups_left_aux :
  forall {n : nat} {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      length gamma = n ->
          showable OC gamma delta alpha d l r ->
              {l' : nat & showable OC (nodup form_eq_dec gamma) delta alpha d l' r}.
Proof.
induction n;
intros gamma delta OC alpha d l r EQ Tshow.
- destruct gamma.
  + refine (existT _ l Tshow).
  + inversion EQ.
- case (no_dup_dec_cases form_eq_dec gamma) as [NDG | DG].
  + rewrite (nodup_fixed_point _ NDG).
    refine (existT _ l Tshow).
  + destruct (has_dups_split form_eq_dec DG) as [A [gamma1 [gamma2 [gamma3 EQL]]]].
    rewrite EQL in *.
    assert (length (A :: gamma1 ++ gamma2 ++ gamma3) = n) as LEN.
    { rewrite app_length in EQ.
      unfold length in *;
      fold (@length formula) in *.
      repeat rewrite app_length in *.
      unfold length in EQ;
      fold (@length formula) in EQ.
      repeat rewrite <- plus_n_Sm in EQ.
      lia. }
    pose proof (IHn _ _ _ _ _ _ _ LEN (cpl_tree_con_l (cpl_tree_comm_left (double_perm_head) Tshow))) as [l' Tshow'].
    rewrite <- nodup_double_cons in Tshow'.
    refine (existT _ l' (cpl_tree_comm_left (perm_sym (perm_nodup form_eq_dec double_perm_head)) Tshow')).
Qed.

Lemma cpl_tree_nodups_left :
  forall {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      showable OC gamma delta alpha d l r ->
          {l' : nat & showable OC (nodup form_eq_dec gamma) delta alpha d l' r}.
Proof.
intros gamma delta OC alpha d l r Tshow.
apply (prove_dups_left_aux eq_refl Tshow).
Qed.

Lemma prove_extras_left_aux :
  forall {n : nat} {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      length gamma = n ->
          showable OC (nodup form_eq_dec gamma) delta alpha d l r ->
              showable OC gamma delta alpha d l r.
Proof.
induction n;
intros gamma delta OC alpha d l r EQ Tshow.
- destruct gamma.
  + apply Tshow.
  + inversion EQ.
- case (no_dup_dec_cases form_eq_dec gamma) as [NDG | DG].
  + rewrite <- (nodup_fixed_point form_eq_dec NDG).
    apply Tshow.
  + destruct (has_dups_split form_eq_dec DG) as [A [gamma1 [gamma2 [gamma3 EQL]]]].
    subst.
    destruct (@nodup_split_perm _ form_eq_dec (A :: A :: gamma1 ++ gamma2 ++ gamma3)) as [sigma [PERM SUB]].
    assert (incl (flat_map vars_in sigma) (OC_list OC)) as SUB'.
    { destruct Tshow as [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
      refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (incl_tran SUB (incl_tran (fun B IN => perm_in form_eq_dec (perm_sym double_perm_head) _ IN) (fun B IN => proj2 (nodup_In _ _ _) IN)))) _).
      rewrite <- Tgam, <- Tcon.
      apply (fst (structured_OC_semiapp _ Tstr)). }
    apply (cpl_tree_comm_left (perm_trans _ _ _ (perm_sym PERM) (perm_sym double_perm_head)) (cpl_tree_weaken_left SUB' ((cpl_tree_comm_left (perm_nodup form_eq_dec double_perm_head)) Tshow))).
Qed.

Lemma cpl_tree_redups_left :
  forall {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      showable OC (nodup form_eq_dec gamma) delta alpha d l r ->
          showable OC gamma delta alpha d l r.
Proof.
intros gamma delta OC alpha d l r Tshow.
apply (prove_extras_left_aux eq_refl Tshow).
Qed.

Lemma cpl_tree_equiv_left :
  forall {gamma1 gamma2 delta : list formula} {OC : constraint} {alpha : ordinal} {d l r : nat},
      (forall A : formula, In A gamma1 <-> In A gamma2) ->
          showable OC gamma1 delta alpha d l r ->
              {l' : nat & showable OC gamma2 delta alpha d l' r}.
Proof.
intros gamma1 gamma2 delta OC alpha d l r EQUIV Tshow.
apply (existT _ (projT1 (cpl_tree_nodups_left Tshow)) (cpl_tree_redups_left ((cpl_tree_comm_left (equiv_nodup_perm form_eq_dec EQUIV)) (projT2 (cpl_tree_nodups_left Tshow))))).
Qed.

Lemma commutative_right_aux :
  forall {LN : list nat} {gamma delta1 delta2 : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      (set_bury delta1 LN = delta2) ->
          showable OC gamma delta1 alpha d l r->
              showable OC gamma delta2 alpha d l r.
Proof.
induction LN;
intros gamma1 gamma2 delta OC alpha d l r EQ Tshow.
- unfold set_bury in EQ.
  subst.
  apply Tshow.
- unfold set_bury in EQ;
  fold @set_bury in EQ.
  apply (IHLN _ _ _ _ _ _ _ _ EQ), cpl_tree_ex_r, Tshow.
Qed.

Lemma cpl_tree_comm_right :
  forall {gamma delta1 delta2 : list formula} {OC : constraint} {alpha : ordinal} {d l r : nat},
      (perm delta1 delta2) ->
          showable OC gamma delta1 alpha d l r ->
              showable OC gamma delta2 alpha d l r.
Proof.
intros gamma delta1 delta2 OC alpha d l r perm.
pose proof (set_bury_eq_perm perm) as [LN EQ].
apply (commutative_right_aux EQ).
Defined.

Lemma prove_dups_right_aux :
  forall {n : nat} {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      length delta = n ->
          showable OC gamma delta alpha d l r ->
              {r' : nat & showable OC gamma (nodup form_eq_dec delta) alpha d l r'}.
Proof.
induction n;
intros gamma delta OC alpha d l r EQ Tshow.
- destruct delta.
  refine (existT _ r Tshow).
  inversion EQ.
- case (no_dup_dec_cases form_eq_dec delta) as [NDD | DD].
  + rewrite (nodup_fixed_point _ NDD).
    refine (existT _ r Tshow).
  + destruct (has_dups_split form_eq_dec DD) as [A [delta1 [delta2 [delta3 EQL]]]].
    subst.
    assert (length (A :: delta1 ++ delta2 ++ delta3) = n) as LEN.
    { rewrite app_length in EQ.
      unfold length in *;
      fold (@length formula) in *.
      repeat rewrite app_length in *.
      unfold length in EQ;
      fold (@length formula) in EQ.
      repeat rewrite <- plus_n_Sm in EQ.
      lia. }
    pose proof (IHn _ _ _ _ _ _ _ LEN (cpl_tree_con_r (cpl_tree_comm_right (double_perm_head) Tshow))) as [r' Tshow'].
    rewrite <- nodup_double_cons in Tshow'.
    refine (existT _ r' (cpl_tree_comm_right (perm_sym (perm_nodup form_eq_dec double_perm_head)) Tshow')).
Qed.

Lemma cpl_tree_nodups_right :
  forall {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      showable OC gamma delta alpha d l r ->
          {r' : nat & showable OC gamma (nodup form_eq_dec delta) alpha d l r'}.
Proof.
intros gamma delta OC alpha d l r Tshow.
apply (prove_dups_right_aux eq_refl Tshow).
Qed.

Lemma prove_extras_right_aux :
  forall {n : nat} {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      length delta = n ->
          showable OC gamma (nodup form_eq_dec delta) alpha d l r ->
              showable OC gamma delta alpha d l r.
Proof.
induction n;
intros gamma delta OC alpha d l r EQ Tshow.
- destruct delta.
  + apply Tshow.
  + inversion EQ.
- case (no_dup_dec_cases form_eq_dec delta) as [NDD | DD].
  + rewrite <- (nodup_fixed_point form_eq_dec NDD).
    apply Tshow.
  + destruct (has_dups_split form_eq_dec DD) as [A [delta1 [delta2 [delta3 EQL]]]].
    subst.
    destruct (@nodup_split_perm _ form_eq_dec (A :: A :: delta1 ++ delta2 ++ delta3)) as [pi [PERM SUB]].
    assert (incl (flat_map vars_in pi) (OC_list OC)) as SUB'.
    { destruct Tshow as [T [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep] Tleft] Tright]].
      refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (incl_tran SUB (incl_tran (fun B IN => perm_in form_eq_dec (perm_sym double_perm_head) _ IN) (fun B IN => proj2 (nodup_In _ _ _) IN)))) _).
      rewrite <- Tdelt, <- Tcon.
      apply (snd (structured_OC_semiapp _ Tstr)). }
    apply (cpl_tree_comm_right (perm_trans _ _ _ (perm_sym PERM) (perm_sym double_perm_head)) (cpl_tree_weaken_right SUB' ((cpl_tree_comm_right (perm_nodup form_eq_dec double_perm_head)) Tshow))).
Qed.

Lemma cpl_tree_redups_right :
  forall {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d l r : nat},
      showable OC gamma (nodup form_eq_dec delta) alpha d l r ->
          showable OC gamma delta alpha d l r.
Proof.
intros gamma delta OC alpha d l r Tshow.
apply (prove_extras_right_aux eq_refl Tshow).
Qed.

Lemma cpl_tree_equiv_right :
  forall {gamma delta1 delta2 : list formula} {OC : constraint} {alpha : ordinal} {d l r : nat},
      (forall A : formula, In A delta1 <-> In A delta2) ->
          showable OC gamma delta1 alpha d l r ->
              {r' : nat & showable OC gamma delta2 alpha d l r'}.
Proof.
intros gamma delta1 delta2 OC alpha d l r EQUIV Tshow.
apply (existT _ (projT1 (cpl_tree_nodups_right Tshow)) (cpl_tree_redups_right ((cpl_tree_comm_right (equiv_nodup_perm form_eq_dec EQUIV)) (projT2 (cpl_tree_nodups_right Tshow))))).
Qed.

Lemma strong_ind_type :
  forall n (P : nat -> Type), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  exact (fun p P F => induction_ltof1 nat (fun m => m) P F p).
Defined.

Lemma struct_show_self :
    forall {T : cpl_tree},
        structured T ->
            T_shows T (cpl_tree_constraint T) (cpl_tree_left T) (cpl_tree_right T) (cpl_tree_deg T) (cpl_tree_depth T) (left_ops T) (right_ops T).
Proof.
intros T Tstr.
repeat split.
apply Tstr.
Qed.


Lemma cpl_tree_imp_l_inv_1 :
forall {l : nat} {T : cpl_tree} {gamma1 gamma2 delta : list formula} {phi psi : formula} {OC : constraint} {d r : nat} {alpha : ordinal},
    left_ops T <= l ->
        T_shows T OC (gamma1 ++ imp phi psi :: gamma2) delta alpha d (left_ops T) r ->
            {d' : nat & {l' : nat & {r' : nat & ((showable OC (gamma1 ++ psi :: gamma2) delta alpha d' l' r') * (d' <= cpl_tree_depth T) * (l' <= left_ops T))%type}}}.
Proof.
induction l as [l IND] using strong_ind_type.
induction T;
intros gamma1' gamma2' delta' phi' psi' OC' d r alpha' LT Tshow;
inversion Tshow as [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth] Tleft] Tright].

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW TOC]] [NING NIND]] TDeg]].
12 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
13 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
15 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
16 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold cpl_tree_left in Tgam;
      subst.

1 : refine (existT _ 0 (existT _ 0 (existT _ 0 (pair (pair (existT _ (leaf OC (gamma1' ++ psi' :: gamma2') delta alpha) _) (Nat.le_refl _)) (Nat.le_refl _))))).
    repeat split;
    intros o IN;
    unfold cpl_tree_left in *;
    unfold cpl_tree_right in *;
    rewrite flat_map_app in *.
    apply in_app_or in IN as [IN1 | IN2].
    refine (TG_app o (in_or_app _ _ _ (or_introl IN1))).
    apply in_app_or in IN2 as [IN2 | IN3].
    refine (TG_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_intror IN2))))))).
    refine (TG_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror IN3))))).
    refine (TD_app o IN).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    subst.
    destruct b.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_1 _ Tshow'') LTD) LT')))).
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_2 _ Tshow'') LTD) LT')))).

1 : { destruct gamma1' as [ | f gamma1'].
      - rewrite app_nil_l in Tgam.
        pose proof (struct_show_self Tstr) as Tshow'.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        rewrite TG in Tshow'.
        rewrite <- (app_nil_l (_ :: gamma2')), app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow') as [d' [l' [r' [[[T' Tshow''] LTD] LT']]]].
        inversion Tshow'' as [[[[[[[Tstr' Tgam'] Tdelt'] Tcon'] Tdeg'] Tdepth'] Tleft'] Tright'].
        subst.
        rewrite <- app_comm_cons, app_nil_l, <- (app_nil_l (_ :: _)) in Tshow''.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ LT' Tshow'') as [d'' [l'' [r'' [[Tshow''' LTD'] LT'']]]].
        rewrite app_nil_l in *.
        refine (existT _ d'' (existT _ (S l'') (existT _ r'' (pair (pair (cpl_tree_con_l Tshow''') (Nat.le_trans _ _ _ LTD' LTD)) (le_n_S _ _ (Nat.le_trans _ _ _ LT'' LT')))))).
      - rewrite <- app_comm_cons in Tgam.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TG in Tshow'.
        rewrite !app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        rewrite <- app_comm_cons.
        refine (existT _ d' (existT _ (S l') (existT _ r' (pair (pair (cpl_tree_con_l Tshow'') LTD) (le_n_S _ _ LT'))))). }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TD in Tshow''.
    refine (existT _ d' (existT _ l' (existT _ (S r') (pair (pair (cpl_tree_con_r Tshow'') LTD) LT')))).

1 : destruct (perm_split (perm_sym bury_is_perm) Tgam) as [gamma1 [gamma2 [EQ perm]]].
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite EQ in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, cpl_tree_deg.
    fold cpl_tree_depth (cpl_tree_deg T).
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_left _ Tshow'') LTD) LT')))).
    apply perm_trans with (psi' :: gamma1 ++ gamma2).
    apply perm_head.
    apply perm_trans with (psi' :: gamma1' ++ gamma2').
    apply perm_skip, perm_sym, perm.
    apply perm_sym, perm_head.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_right bury_is_perm Tshow'') LTD) LT')))).

1 : { destruct gamma1'.
      - rewrite app_nil_l in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        refine (existT _ (cpl_tree_depth T) (existT _ (left_ops T) (existT _ (right_ops T) (pair (pair (cpl_tree_wkn_l _ (existT _ T _)) (Nat.le_refl _)) (Nat.le_refl _))))).
        intros o IN.
        apply TG_app, in_or_app, or_introl, in_or_app, or_intror, IN.
        repeat split.
        apply Tstr.
      - rewrite <- app_comm_cons in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite EQ2 in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_l _ Tshow'') LTD) LT')))).
        intros o IN.
        apply TG_app, in_or_app, or_introl, IN. }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_r _ Tshow'') LTD) LT')))).
    intros o IN.
    apply TD_app, in_or_app, or_introl, IN.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC in Tshow''.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_reset _ _ KIN Tshow'') LTD) LT')))).
    intros FAL.
    apply KNING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.
    intros FAL.
    apply KNIND, FAL.

1 : destruct gamma1'.
    rewrite app_nil_l in *.
    inversion Tgam.
    rewrite <- app_comm_cons in *.
    inversion Tgam as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nu_l Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC, TD in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nu_r _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    apply NING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.
    intros FAL.
    apply NIND, FAL.

1 : destruct gamma1'.
    rewrite app_nil_l in *.
    inversion Tgam.
    rewrite <- app_comm_cons in *.
    inversion Tgam as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nuk_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC, TD in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nuk_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    apply NING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.
    intros FAL.
    apply NIND, FAL.

(*
1 : destruct gamma1'.
    rewrite app_nil_l in *.
    inversion Tgam.
    rewrite <- app_comm_cons in *.
    inversion Tgam as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC, TD in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    apply NING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.
    intros FAL.
    apply NIND, FAL.
*)

1 : { destruct gamma1'.
      - rewrite app_nil_l in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self T1str) as T1show.
        rewrite <- T1G.
        unfold cpl_tree_deg at 5.
        refine (existT _ (cpl_tree_depth T1) (existT _ (left_ops T1) (existT _ (right_ops T1) (pair (pair (cpl_tree_deg_up_1 _ (existT _ T1 T1show)) (le_S _ _ (Nat.le_max_l _ _))) (Nat.le_max_l _ _))))).
      - rewrite <- app_comm_cons in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self T1str) as T1show.
        rewrite T1G, EQ2, app_comm_cons in T1show.
        pose proof (struct_show_self T2str) as T2show.
        rewrite T2D, EQ2, T2OC in T2show.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth, left_ops;
        fold cpl_tree_depth left_ops.
        pose proof (IHT1 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _) LT) T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
        pose proof (IHT2 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _) LT) T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
        refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_imp_l T1show' T2show') _) _)))).
        lia.
        lia. }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, TD, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_imp_r Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite Tgam, T1D in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2G, Tgam, T2OC, app_comm_cons in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, left_ops;
    fold cpl_tree_depth left_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_cut T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.
Qed.

Lemma cpl_tree_imp_l_inv_2 :
forall {l : nat} {T : cpl_tree} {gamma1 gamma2 delta : list formula} {phi psi : formula} {OC : constraint} {d r : nat} {alpha : ordinal},
    left_ops T <= l ->
        T_shows T OC (gamma1 ++ imp phi psi :: gamma2) delta alpha d (left_ops T) r ->
            {d' : nat & {l' : nat & {r' : nat & ((showable OC (gamma1 ++ gamma2) (delta ++ [phi]) alpha d' l' r') * (d' <= cpl_tree_depth T) * (l' <= left_ops T))%type}}}.
Proof.
induction l as [l IND] using strong_ind_type.
induction T;
intros gamma1' gamma2' delta' phi' psi' OC' d r alpha' LT Tshow;
inversion Tshow as [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth] Tleft] Tright].

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW TOC]] [NING NIND]] TDeg]].
12 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
13 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
15 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
16 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold cpl_tree_left in Tgam;
      subst.

1 : refine (existT _ 0 (existT _ 0 (existT _ 0 (pair (pair (existT _ (leaf OC (gamma1' ++ gamma2') (delta ++ [phi']) alpha) _) (Nat.le_refl _)) (Nat.le_refl _))))).
    repeat split;
    intros o IN;
    unfold cpl_tree_left in *;
    unfold cpl_tree_right in *;
    rewrite flat_map_app in *;
    apply in_app_or in IN as [IN1 | IN2].
    refine (TG_app o (in_or_app _ _ _ (or_introl IN1))).
    refine (TG_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror IN2))))).
    refine (TD_app o IN1).
    unfold flat_map in IN2.
    rewrite app_nil_r in IN2.
    refine (TG_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl IN2))))))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    subst.
    destruct b.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_1 _ Tshow'') LTD) LT')))).
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_2 _ Tshow'') LTD) LT')))).

1 : { destruct gamma1' as [ | f gamma1'].
      - rewrite app_nil_l in Tgam.
        pose proof (struct_show_self Tstr) as Tshow'.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        rewrite TG in Tshow'.
        rewrite <- (app_nil_l (_ :: _)) in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow') as [d' [l' [r' [[[T' Tshow''] LTD] LT']]]].
        inversion Tshow'' as [[[[[[[Tstr' Tgam'] Tdelt'] Tcon'] Tdeg'] Tdepth'] Tleft'] Tright'].
        subst.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ LT' Tshow'') as [d'' [l'' [r'' [[Tshow''' LTD'] LT'']]]].
        rewrite <- app_assoc in Tshow'''.
        unfold app at 3 in Tshow'''.
        refine (existT _ d'' (existT _ l'' (existT _ (S r'') (pair (pair _ (Nat.le_trans _ _ _ LTD' LTD)) (le_S _ _ (Nat.le_trans _ _ _ LT'' LT')))))).
        pose proof (@perm_head _ (cpl_tree_right T) [] phi') as PERM.
        rewrite app_nil_r in PERM.
        pose proof (@perm_head _ (phi' :: (cpl_tree_right T)) [] phi') as PERM1.
        rewrite app_nil_r in PERM1.
        pose proof (@perm_head _ (cpl_tree_right T) [phi'] phi') as PERM2.
        apply (cpl_tree_comm_right (perm_sym PERM)), cpl_tree_con_r, (cpl_tree_comm_right PERM1), (cpl_tree_comm_right PERM2), Tshow'''.
      - rewrite <- app_comm_cons in Tgam.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TG in Tshow'.
        rewrite !app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        rewrite <- app_comm_cons.
        refine (existT _ d' (existT _ (S l') (existT _ r' (pair (pair (cpl_tree_con_l Tshow'') LTD) (le_n_S _ _ LT'))))). }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ (S r') (pair (pair (cpl_tree_con_r _) LTD) LT')))).
    rewrite !app_comm_cons, <- TD.
    apply Tshow''.

1 : destruct (perm_split (perm_sym bury_is_perm) Tgam) as [gamma1 [gamma2 [EQ perm]]].
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite EQ in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, cpl_tree_deg.
    fold cpl_tree_depth (cpl_tree_deg T).
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_left (perm_sym perm) Tshow'') LTD) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_right (perm_app (bury_is_perm) perm_refl) Tshow'') LTD) LT')))).

1 : { destruct gamma1'.
      - rewrite app_nil_l in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        refine (existT _ (cpl_tree_depth T) (existT _ (left_ops T) (existT _ (right_ops T) (pair (pair (cpl_tree_weaken_right _ (existT _ T _)) (Nat.le_refl _)) (Nat.le_refl _))))).
        intros o IN.
        unfold flat_map in IN.
        rewrite app_nil_r in IN.
        apply TG_app, in_or_app, or_introl, in_or_app, or_introl, IN.
        repeat split.
        apply Tstr.
      - rewrite <- app_comm_cons in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite EQ2 in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_l _ Tshow'') LTD) LT')))).
        intros o IN.
        apply TG_app, in_or_app, or_introl, IN. }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_r _ Tshow'') LTD) LT')))).
    intros o IN.
    apply TD_app, in_or_app, or_introl, IN.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC in Tshow''.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_reset _ _ KIN Tshow'') LTD) LT')))).
    intros FAL.
    apply KNING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL2.
    intros FAL.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply KNIND, FAL1.
    apply KNING.
    rewrite Tgam, flat_map_app.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.

1 : destruct gamma1'.
    rewrite app_nil_l in *.
    inversion Tgam.
    rewrite <- app_comm_cons in *.
    inversion Tgam as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nu_l Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC, TD in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nu_r _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    apply NING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL2.
    intros FAL.
    fold (@app formula) (flat_map vars_used) in FAL.
    rewrite app_comm_cons, flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NIND, FAL1.
    apply NING.
    rewrite Tgam, flat_map_app.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.

1 : destruct gamma1'.
    rewrite app_nil_l in *.
    inversion Tgam.
    rewrite <- app_comm_cons in *.
    inversion Tgam as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nuk_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC, TD in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nuk_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    apply NING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL2.
    intros FAL.
    fold (@app formula) (flat_map vars_used) in FAL.
    rewrite app_comm_cons, flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NIND, FAL1.
    apply NING.
    rewrite Tgam, flat_map_app.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.

(*
1 : destruct gamma1'.
    rewrite app_nil_l in *.
    inversion Tgam.
    rewrite <- app_comm_cons in *.
    inversion Tgam as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC, TD in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    apply NING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL2.
    intros FAL.
    fold (@app formula) (flat_map vars_used) in FAL.
    rewrite app_comm_cons, flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NIND, FAL1.
    apply NING.
    rewrite Tgam, flat_map_app.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
*)

1 : { destruct gamma1'.
      - rewrite app_nil_l in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self T2str) as T2show.
        rewrite <- T2OC.
        unfold cpl_tree_deg at 5.
        refine (existT _ (cpl_tree_depth T2) (existT _ (left_ops T2) (existT _ (right_ops T2) (pair (pair (cpl_tree_deg_up_2 _ (cpl_tree_comm_right _ (existT _ T2 T2show))) (le_S _ _ (Nat.le_max_r _ _))) (Nat.le_max_r _ _))))).
        rewrite T2D, <- (app_nil_r (cpl_tree_right T1)) at 1.
        apply perm_sym, perm_head.
      - rewrite <- app_comm_cons in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self T1str) as T1show.
        rewrite T1G, EQ2, app_comm_cons in T1show.
        pose proof (struct_show_self T2str) as T2show.
        rewrite T2D, EQ2, T2OC in T2show.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth, left_ops;
        fold cpl_tree_depth left_ops.
        pose proof (IHT1 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _) LT) T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
        pose proof (IHT2 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _) LT) T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
        refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_imp_l T1show' T2show') _) _)))).
        lia.
        lia. }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, TD, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_imp_r Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite Tgam, T1D in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2G, Tgam, T2OC, app_comm_cons in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, left_ops;
    fold cpl_tree_depth left_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_cut T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.
Qed.


Lemma cpl_tree_imp_r_inv :
forall {r : nat} {T : cpl_tree} {gamma delta1 delta2 : list formula} {phi psi : formula} {OC : constraint} {d l : nat} {alpha : ordinal},
    right_ops T <= r ->
        T_shows T OC gamma (delta1 ++ imp phi psi :: delta2) alpha d l (right_ops T) ->
            {d' : nat & {l' : nat & {r' : nat & ((showable OC (gamma ++ [phi]) (delta1 ++ psi :: delta2) alpha d' l' r') * (d' <= cpl_tree_depth T) * (r' <= right_ops T))%type}}}.
Proof.
induction r as [r IND] using strong_ind_type.
induction T;
intros gamma' delta1' delta2' phi' psi' OC' d l alpha' LT Tshow;
inversion Tshow as [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth] Tleft] Tright].

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW TOC]] [NING NIND]] TDeg]].
12 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
13 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
15 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
16 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold cpl_tree_right in Tdelt;
      subst.

1 : refine (existT _ 0 (existT _ 0 (existT _ 0 (pair (pair (existT _ (leaf OC (gamma ++ [phi']) (delta1' ++ psi' :: delta2') alpha) _) (Nat.le_refl _)) (Nat.le_refl _))))).
    repeat split;
    intros o IN;
    unfold cpl_tree_left in *;
    unfold cpl_tree_right in *;
    rewrite flat_map_app in *;
    apply in_app_or in IN as [IN1 | IN2].
    refine (TG_app o IN1).
    unfold flat_map in IN2.
    rewrite app_nil_r in IN2.
    refine (TD_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl IN2))))))).
    refine (TD_app o (in_or_app _ _ _ (or_introl IN1))).
    apply in_app_or in IN2 as [IN2 | IN3].
    refine (TD_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_intror IN2))))))).
    refine (TD_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror IN3))))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    subst.
    destruct b.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_1 _ Tshow'') LTD) LT')))).
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_2 _ Tshow'') LTD) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt,TG in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ (S l') (existT _ r' (pair (pair (cpl_tree_con_l Tshow'') LTD) LT')))).

1 : { destruct delta1' as [ | f delta1'].
      - rewrite app_nil_l in *.
        pose proof (struct_show_self Tstr) as Tshow'.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        rewrite TD in Tshow'.
        rewrite <- (app_nil_l (imp phi' psi' :: delta2')), app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow') as [d' [l' [r' [[[T' Tshow''] LTD] LT']]]].
        rewrite <- app_comm_cons, app_nil_l, <- (app_nil_l (imp _ _ :: _)) in Tshow''.
        inversion Tshow'' as [[[[[[[Tstr' Tgam'] Tdelt'] Tcon'] Tdeg'] Tdepth'] Tleft'] Tright'].
        subst.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ LT' Tshow'') as [d'' [l'' [r'' [[Tshow''' LTD'] LT'']]]].
        rewrite <- app_assoc in Tshow'''.
        unfold app at 2 3 in Tshow'''.
        refine (existT _ d'' (existT _ (S l'') (existT _ (S r'') (pair (pair _ (Nat.le_trans _ _ _ LTD' LTD)) (le_n_S _ _ (Nat.le_trans _ _ _ LT'' LT')))))).
        pose proof (@perm_head _ (cpl_tree_left T) [] phi') as PERM.
        rewrite app_nil_r in PERM.
        pose proof (@perm_head _ (phi' :: (cpl_tree_left T)) [] phi') as PERM1.
        rewrite app_nil_r in PERM1.
        pose proof (@perm_head _ (cpl_tree_left T) [phi'] phi') as PERM2.
        apply (cpl_tree_comm_left (perm_sym PERM)), cpl_tree_con_l, (cpl_tree_comm_left PERM1), (cpl_tree_comm_left PERM2), cpl_tree_con_r, Tshow'''.
      - rewrite <- app_comm_cons in Tdelt.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TD in Tshow'.
        rewrite !app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        rewrite <- app_comm_cons.
        refine (existT _ d' (existT _ l' (existT _ (S r') (pair (pair (cpl_tree_con_r Tshow'') LTD) (le_n_S _ _ LT'))))). }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_left (perm_app (bury_is_perm) perm_refl) Tshow'') LTD) LT')))).

1 : destruct (perm_split (perm_sym bury_is_perm) Tdelt) as [delta1 [delta2 [EQ perm]]].
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite EQ in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth, cpl_tree_deg.
    fold cpl_tree_depth (cpl_tree_deg T).
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_right _ Tshow'') LTD) LT')))).
    apply perm_trans with (psi' :: delta1 ++ delta2).
    apply perm_head.
    apply perm_trans with (psi' :: delta1' ++ delta2').
    apply perm_skip, perm_sym, perm.
    apply perm_sym, perm_head.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_l _ Tshow'') LTD) LT')))).
    intros o IN.
    apply TG_app, in_or_app, or_introl, IN.

1 : { destruct delta1'.
      - rewrite app_nil_l in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        refine (existT _ (cpl_tree_depth T) (existT _ (left_ops T) (existT _ (right_ops T) (pair (pair (cpl_tree_weaken_left _ (cpl_tree_wkn_r _ (existT _ T _))) (Nat.le_refl _)) (Nat.le_refl _))))).
        intros o IN.
        unfold flat_map in IN.
        rewrite app_nil_r in IN.
        apply TD_app, in_or_app, or_introl, in_or_app, or_introl, IN.
        intros o IN.
        unfold flat_map in IN.
        apply TD_app, in_or_app, or_introl, in_or_app, or_intror, IN.
        repeat split.
        apply Tstr.
      - rewrite <- app_comm_cons in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite EQ2 in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_r _ Tshow'') LTD) LT')))).
        intros o IN.
        apply TD_app, in_or_app, or_introl, IN. }    

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC in Tshow''.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_reset _ _ KIN Tshow'') LTD) LT')))).
    intros FAL.
    rewrite flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply KNING, FAL1.
    apply KNIND.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    rewrite Tdelt.
    rewrite flat_map_app.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
    intros FAL.
    apply KNIND.
    rewrite Tdelt, flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TG in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nu_l Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : destruct delta1'.
    rewrite app_nil_l in *.
    inversion Tdelt.
    rewrite <- app_comm_cons in *.
    inversion Tdelt as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TD, app_comm_cons, TOC in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nu_r _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    rewrite flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NING, FAL1.
    apply NIND.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
    intros FAL.
    apply NIND.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    fold (flat_map vars_used) (@app formula) in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app in *.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_introl, FAL2.
    apply in_app_or in FAL3 as [FAL3 | FAL4].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL3.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL4.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TG in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nuk_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : destruct delta1'.
    rewrite app_nil_l in *.
    inversion Tdelt.
    rewrite <- app_comm_cons in *.
    inversion Tdelt as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TD, app_comm_cons, TOC in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nuk_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    rewrite flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NING, FAL1.
    apply NIND.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
    intros FAL.
    apply NIND.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    fold (flat_map vars_used) (@app formula) in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app in *.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_introl, FAL2.
    apply in_app_or in FAL3 as [FAL3 | FAL4].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL3.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL4.

(*
1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TG in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : destruct delta1'.
    rewrite app_nil_l in *.
    inversion Tdelt.
    rewrite <- app_comm_cons in *.
    inversion Tdelt as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TD, app_comm_cons, TOC in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    rewrite flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NING, FAL1.
    apply NIND.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
    intros FAL.
    apply NIND.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    fold (flat_map vars_used) (@app formula) in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app in *.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_introl, FAL2.
    apply in_app_or in FAL3 as [FAL3 | FAL4].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL3.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL4.
*)

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite Tdelt, T1G in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2D, Tdelt, T2OC, app_comm_cons in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, right_ops;
    fold cpl_tree_depth right_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_imp_l T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.

1 : { destruct delta1'.
      - rewrite app_nil_l in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TG, TD in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        refine (existT _ (cpl_tree_depth T) (existT _ (left_ops T) (existT _ (right_ops T) (pair (pair (cpl_tree_comm_left _ (existT _ T Tshow')) (le_S _ _ (Nat.le_refl _))) (Nat.le_refl _))))).
        apply perm_sym.
        rewrite <- app_nil_r.
        apply perm_head.
      - rewrite <- app_comm_cons in Tdelt.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TG, TD, app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_imp_r Tshow'') (le_n_S _ _ LTD)) LT')))). }

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite T1D, Tdelt, app_comm_cons in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2G, Tdelt, T2OC in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, right_ops;
    fold cpl_tree_depth right_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_cut T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.
Qed.


Lemma cpl_tree_nu_r_inv :
forall {r : nat} {T : cpl_tree} {gamma delta1 delta2 : list formula} {phi : formula} {x : nat} {OC : constraint} {d l : nat} {alpha : ordinal},
    right_ops T <= r ->
        T_shows T OC gamma (delta1 ++ nu x phi :: delta2) alpha d l (right_ops T) ->
            forall (lambda : ovar) (NEW : ~ OC_elt OC lambda),
                {d' : nat & {l' : nat & {r' : nat & ((showable (add_fresh OC lambda NEW) gamma (delta1 ++ (nuk x lambda phi) :: delta2) alpha d' l' r') * (d' <= cpl_tree_depth T) * (r' <= right_ops T))%type}}}.
Proof.
induction r as [r IND] using strong_ind_type.
induction T;
intros gamma' delta1' delta2' phi' x' OC' d l alpha' LT Tshow lambda' NEW';
inversion Tshow as [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth] Tleft] Tright].

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW TOC]] [NING NIND]] TDeg]].
12 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
13 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
15 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
16 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold cpl_tree_right in Tdelt;
      subst.

1 : refine (existT _ 0 (existT _ 0 (existT _ 0 (pair (pair (existT _ (leaf (add_fresh OC _ NEW') gamma (delta1' ++ (nuk x' lambda' phi') :: delta2') alpha) _) (Nat.le_refl _)) (Nat.le_refl _))))).
    repeat split;
    intros o IN.
    apply or_intror, TG_app, IN.
    unfold cpl_tree_left in *;
    unfold cpl_tree_right in *;
    rewrite flat_map_app in *.
    apply in_app_or in IN as [IN1 | IN2].
    refine (or_intror (TD_app o (in_or_app _ _ _ (or_introl IN1)))).
    apply in_app_or in IN2 as [[EQ | IN2] | IN3].
    refine (or_introl EQ).
    refine (or_intror (TD_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl IN2)))))).
    refine (or_intror (TD_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror IN3)))))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    subst.
    destruct b.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_1 _ Tshow'') LTD) LT')))).
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_2 _ Tshow'') LTD) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt,TG in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ (S l') (existT _ r' (pair (pair (cpl_tree_con_l Tshow'') LTD) LT')))).

1 : { destruct delta1' as [ | f delta1'].
      - rewrite app_nil_l in *.
        pose proof (struct_show_self Tstr) as Tshow'.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        rewrite TD in Tshow'.
        rewrite <- (app_nil_l (_ :: delta2')), app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow') as [d' [l' [r' [[[T' Tshow''] LTD] LT']]]].
        rewrite <- app_comm_cons, app_nil_l, <- (app_nil_l (nu _ _ :: _)) in Tshow''.
        inversion Tshow'' as [[[[[[[Tstr' Tgam'] Tdelt'] Tcon'] Tdeg'] Tdepth'] Tleft'] Tright'].
        subst.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ LT' Tshow'' _ NEW') as [d'' [l'' [r'' [[Tshow''' LTD'] LT'']]]].
        rewrite <- app_assoc in Tshow'''.
        unfold app at 2 3 in Tshow'''.
        refine (existT _ d'' (existT _ (S l'') (existT _ (S r'') (pair (pair _ (Nat.le_trans _ _ _ LTD' LTD)) (le_n_S _ _ (Nat.le_trans _ _ _ LT'' LT')))))).
        pose proof (@perm_head _ (cpl_tree_left T) [] phi') as PERM.
        rewrite app_nil_r in PERM.
        pose proof (@perm_head _ (phi' :: (cpl_tree_left T)) [] phi') as PERM1.
        rewrite app_nil_r in PERM1.
        pose proof (@perm_head _ (cpl_tree_left T) [phi'] phi') as PERM2.
        apply (cpl_tree_comm_left (perm_sym PERM)), cpl_tree_con_l, (cpl_tree_comm_left PERM1), (cpl_tree_comm_left PERM2), cpl_tree_con_r, Tshow'''.
      - rewrite <- app_comm_cons in Tdelt.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TD in Tshow'.
        rewrite !app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        rewrite <- app_comm_cons.
        refine (existT _ d' (existT _ l' (existT _ (S r') (pair (pair (cpl_tree_con_r Tshow'') LTD) (le_n_S _ _ LT'))))). }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_left (perm_app (bury_is_perm) perm_refl) Tshow'') LTD) LT')))).

1 : destruct (perm_split (perm_sym bury_is_perm) Tdelt) as [delta1 [delta2 [EQ perm]]].
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite EQ in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth, cpl_tree_deg.
    fold cpl_tree_depth (cpl_tree_deg T).
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_right _ Tshow'') LTD) LT')))).
    apply perm_trans with (psi' :: delta1 ++ delta2).
    apply perm_head.
    apply perm_trans with (psi' :: delta1' ++ delta2').
    apply perm_skip, perm_sym, perm.
    apply perm_sym, perm_head.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_l _ Tshow'') LTD) LT')))).
    intros o IN.
    apply TG_app, in_or_app, or_introl, IN.

1 : { destruct delta1'.
      - rewrite app_nil_l in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        refine (existT _ (cpl_tree_depth T) (existT _ (left_ops T) (existT _ (right_ops T) (pair (pair (cpl_tree_weaken_left _ (cpl_tree_wkn_r _ (existT _ T _))) (Nat.le_refl _)) (Nat.le_refl _))))).
        intros o IN.
        unfold flat_map in IN.
        rewrite app_nil_r in IN.
        apply TD_app, in_or_app, or_introl, in_or_app, or_introl, IN.
        intros o IN.
        unfold flat_map in IN.
        apply TD_app, in_or_app, or_introl, in_or_app, or_intror, IN.
        repeat split.
        apply Tstr.
      - rewrite <- app_comm_cons in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite EQ2 in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_r _ Tshow'') LTD) LT')))).
        intros o IN.
        apply TD_app, in_or_app, or_introl, IN. }    

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC in Tshow''.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_reset _ _ KIN Tshow'') LTD) LT')))).
    intros FAL.
    rewrite flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply KNING, FAL1.
    apply KNIND.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    rewrite Tdelt.
    rewrite flat_map_app.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
    intros FAL.
    apply KNIND.
    rewrite Tdelt, flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TG in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nu_l Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : destruct delta1'.
    rewrite app_nil_l in *.
    inversion Tdelt.
    rewrite <- app_comm_cons in *.
    inversion Tdelt as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TD, app_comm_cons, TOC in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nu_r _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    rewrite flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NING, FAL1.
    apply NIND.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
    intros FAL.
    apply NIND.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    fold (flat_map vars_used) (@app formula) in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app in *.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_introl, FAL2.
    apply in_app_or in FAL3 as [FAL3 | FAL4].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL3.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL4.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TG in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nuk_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : destruct delta1'.
    rewrite app_nil_l in *.
    inversion Tdelt.
    rewrite <- app_comm_cons in *.
    inversion Tdelt as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TD, app_comm_cons, TOC in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_nuk_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    rewrite flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NING, FAL1.
    apply NIND.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
    intros FAL.
    apply NIND.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    fold (flat_map vars_used) (@app formula) in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app in *.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_introl, FAL2.
    apply in_app_or in FAL3 as [FAL3 | FAL4].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL3.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL4.

(*
1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TG in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : destruct delta1'.
    rewrite app_nil_l in *.
    inversion Tdelt.
    rewrite <- app_comm_cons in *.
    inversion Tdelt as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TD, app_comm_cons, TOC in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    rewrite flat_map_app in FAL.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply NING, FAL1.
    apply NIND.
    unfold flat_map in FAL2.
    rewrite app_nil_r in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app.
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_introl, FAL2.
    intros FAL.
    apply NIND.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    fold (flat_map vars_used) (@app formula) in FAL2.
    apply in_or_app, or_intror.
    fold (flat_map vars_used).
    rewrite flat_map_app in *.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_introl, FAL2.
    apply in_app_or in FAL3 as [FAL3 | FAL4].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL3.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL4.
*)

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite Tdelt, T1G in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2D, Tdelt, T2OC, app_comm_cons in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, right_ops;
    fold cpl_tree_depth right_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_imp_l T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.

1 : { destruct delta1'.
      - rewrite app_nil_l in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TG, TD in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        refine (existT _ (cpl_tree_depth T) (existT _ (left_ops T) (existT _ (right_ops T) (pair (pair (cpl_tree_comm_left _ (existT _ T Tshow')) (le_S _ _ (Nat.le_refl _))) (Nat.le_refl _))))).
        apply perm_sym.
        rewrite <- app_nil_r.
        apply perm_head.
      - rewrite <- app_comm_cons in Tdelt.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TG, TD, app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ LT Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_imp_r Tshow'') (le_n_S _ _ LTD)) LT')))). }

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite T1D, Tdelt, app_comm_cons in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2G, Tdelt, T2OC in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, right_ops;
    fold cpl_tree_depth right_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_cut T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.
Qed.



(*
Lemma cpl_tree_bnd_r_inv :
    forall {r : nat} {T : cpl_tree} {gamma delta1 delta2 : list formula} {phi : formula} {lambda kappa} {OC : constraint} {d l : nat} {alpha : ordinal},
        right_ops T <= r ->
            T_shows T OC gamma (delta1 ++ bnd lambda kappa phi :: delta2) alpha d l (right_ops T) ->
                forall (eta : ovar),
                    OC_elt OC eta ->
                        OC_rel OC eta kappa = false ->
                            {d' : nat & {l' : nat & {r' : nat & ((showable OC gamma (delta1 ++ (ovar_sub phi lambda eta) :: delta2) alpha d' l' r') * (d' <= cpl_tree_depth T) * (r' <= right_ops T))%type}}}.
Proof.
induction r as [r IND] using strong_ind_type.
induction T;
intros gamma' delta1' delta2' phi' lambda' kappa' OC' d l alpha' LT Tshow eta IN' GT;
inversion Tshow as [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth] Tleft] Tright].

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold cpl_tree_right in Tdelt;
      subst.

1 : refine (existT _ 0 (existT _ 0 (existT _ 0 (pair (pair (existT _ (leaf OC gamma (delta1' ++ (ovar_sub phi' lambda' eta) :: delta2') alpha) _) (Nat.le_refl _)) (Nat.le_refl _))))).
    repeat split.
    apply TG_app.
    intros o IN;
    unfold cpl_tree_left in *;
    unfold cpl_tree_right in *;
    rewrite flat_map_app in *;
    apply in_app_or in IN as [IN1 | IN2].
    refine (TD_app o (in_or_app _ _ _ (or_introl IN1))).
    apply in_app_or in IN2 as [IN2 | IN3].
    apply vars_in_sub in IN2 as [EQ | [NE IN2]].
    subst.
    apply IN'.
    apply TD_app, in_or_app, or_intror, in_or_app, or_introl, or_intror, (in_in_remove _ _ NE IN2).
    refine (TD_app o (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror IN3))))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    subst.
    destruct b.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_1 _ Tshow'') LTD) LT')))).
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_2 _ Tshow'') LTD) LT')))).

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt,TG in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ (S l') (existT _ r' (pair (pair (cpl_tree_con_l Tshow'') LTD) LT')))).

1 : { destruct delta1' as [ | f delta1'].
      - rewrite app_nil_l in *.
        pose proof (struct_show_self Tstr) as Tshow'.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        rewrite TD in Tshow'.
        rewrite <- (app_nil_l (_ :: delta2')), app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow' _ IN' GT) as [d' [l' [r' [[[T' Tshow''] LTD] LT']]]].
        rewrite <- app_comm_cons, app_nil_l, <- (app_nil_l (bnd _ _ _ :: _)) in Tshow''.
        inversion Tshow'' as [[[[[[[Tstr' Tgam'] Tdelt'] Tcon'] Tdeg'] Tdepth'] Tleft'] Tright'].
        subst.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ _ LT' Tshow'' _ IN' GT) as [d'' [l'' [r'' [[Tshow''' LTD'] LT'']]]].
        rewrite app_nil_l in Tshow'''.
        refine (existT _ d'' (existT _ l'' (existT _ (S r'') (pair (pair (cpl_tree_con_r Tshow''') (Nat.le_trans _ _ _ LTD' LTD)) (le_n_S _ _ (Nat.le_trans _ _ _ LT'' LT')))))).
      - rewrite <- app_comm_cons in Tdelt.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TD in Tshow'.
        rewrite !app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ d' (existT _ l' (existT _ (S r') (pair (pair (cpl_tree_con_r Tshow'') LTD) (le_n_S _ _ LT'))))). }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_ex_l Tshow'') LTD) LT')))).

1 : destruct (perm_split (perm_sym bury_is_perm) Tdelt) as [delta1 [delta2 [EQ perm]]].
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite EQ in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth, cpl_tree_deg.
    fold cpl_tree_depth (cpl_tree_deg T).
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_right _ Tshow'') LTD) LT')))).
    apply perm_trans with ((ovar_sub phi' lambda' eta) :: delta1 ++ delta2).
    apply perm_head.
    apply perm_trans with ((ovar_sub phi' lambda' eta) :: delta1' ++ delta2').
    apply perm_skip, perm_sym, perm.
    apply perm_sym, perm_head.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_l _ Tshow'') LTD) LT')))).
    intros o IN.
    apply TG_app, in_or_app, or_introl, IN.

1 : { destruct delta1'.
      - rewrite app_nil_l in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        refine (existT _ (cpl_tree_depth T) (existT _ (left_ops T) (existT _ (right_ops T) (pair (pair (cpl_tree_wkn_r _ (existT _ T _)) (Nat.le_refl _)) (Nat.le_refl _))))).
        intros o IN.
        unfold flat_map in IN.
        apply vars_in_sub in IN as [EQ | [NE IN]].
        subst.
        apply IN'.
        apply TD_app, in_or_app, or_introl, or_intror, (in_in_remove _ _ NE IN).
        repeat split.
        apply Tstr.
      - rewrite <- app_comm_cons in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite EQ2 in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_r _ Tshow'') LTD) LT')))).
        intros o IN.
        apply TD_app, in_or_app, or_introl, IN. }    

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    assert (OC_elt (cpl_tree_constraint T) eta) as IN''.
    { rewrite TOC.
      unfold OC_elt, OC_list, restriction, projT1.
      unfold cpl_tree_constraint in *;
      fold (cpl_tree_constraint T) in *.
      apply filter_In, (conj IN').
      case in_dec as [IN | NIN].
      apply filter_In in IN as [IN _].
      apply filter_In in IN as [_ FAL].
      rewrite <- GT in FAL.
      admit.
      reflexivity. }
    assert (OC_rel (cpl_tree_constraint T) eta kappa' = false) as GT'.
    { admit. }
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN'' GT') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC in Tshow''.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_reset _ _ KIN Tshow'') LTD) LT')))).
    apply KNING.
    intros FAL.
    apply KNIND.
    rewrite flat_map_app in FAL.
    rewrite Tdelt, flat_map_app.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply vars_used_sub in FAL2 as [EQ | FAL2].
    subst.
    admit.
    apply in_or_app, or_intror, in_or_app, or_introl, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tdelt in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TG in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : { destruct delta1'.
      - rewrite app_nil_l in *.
        inversion Tdelt as [[EQ1 EQ2 EQ3 EQ4]].
        subst.
        admit.
      - rewrite <- app_comm_cons in *.
        inversion Tdelt as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TD, app_comm_cons, TOC in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        assert (OC_elt (cpl_tree_constraint T) eta) as IN''.
        { admit. }
        assert (OC_rel (cpl_tree_constraint T) eta kappa' = false) as GT'.
        { admit. }
        rewrite TOC in IN'', GT'.
        pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN'' GT') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
        apply NING.
        intros FAL.
        apply NIND.
        apply in_app_or in FAL as [FAL1 | FAL2].
        apply in_or_app, or_introl, FAL1.
        fold (flat_map vars_used) (@app formula) in FAL2.
        apply in_or_app, or_intror.
        fold (flat_map vars_used).
        rewrite flat_map_app in *.
        apply in_app_or in FAL2 as [FAL2 | FAL3].
        apply in_or_app, or_introl, FAL2.
        apply in_app_or in FAL3 as [FAL3 | FAL4].
        admit.
        (* apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL3. *)
        apply in_or_app, or_intror, in_or_app, or_intror, FAL4. }

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite Tdelt, T1G in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2D, Tdelt, T2OC, app_comm_cons in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, right_ops;
    fold cpl_tree_depth right_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) T1show _ IN' GT) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) T2show _ IN' GT) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_imp_l T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.

1 : destruct delta1'.
    inversion Tdelt.
    rewrite <- app_comm_cons in Tdelt.
    inversion Tdelt as [[EQ1 EQ2]].
    subst.
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, TD, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_left at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT Tshow' _ IN' GT) as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_imp_r Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite T1D, Tdelt, app_comm_cons in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2G, Tdelt, T2OC in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, right_ops;
    fold cpl_tree_depth right_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) T1show _ IN' GT) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) T2show _ IN' GT) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_cut T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.
Qed.

(*
Lemma cpl_tree_bnd_l_inv :
forall {l : nat} {T : cpl_tree} {gamma1 gamma2 delta : list formula} {phi : formula} {lambda kappa} {OC : constraint} {d r : nat} {alpha : ordinal},
    left_ops T <= l ->
        (OC_rel (cpl_tree_constraint T) lambda kappa = true) ->
            T_shows T OC (gamma1 ++ bnd lambda kappa phi :: gamma2) delta alpha d (left_ops T) r ->
                {d' : nat & {l' : nat & {r' : nat & ((showable OC (gamma1 ++ phi :: gamma2) delta alpha d' l' r') * (d' <= cpl_tree_depth T) * (l' <= left_ops T))%type}}}.*)

Lemma cpl_tree_bnd_l_inv :
    forall {l : nat} {T : cpl_tree} {gamma1 gamma2 delta : list formula} {phi : formula} {lambda kappa} {OC : constraint} {d r : nat} {alpha : ordinal},
        left_ops T <= l ->
            T_shows T OC (gamma1 ++ bnd lambda kappa phi :: gamma2) delta alpha d (left_ops T) r ->
                {eta : ovar & {d' : nat & {l' : nat & {r' : nat & ((showable OC (gamma1 ++ (ovar_sub phi lambda eta) :: gamma2) delta alpha d' l' r') * (d' <= cpl_tree_depth T) * (l' <= left_ops T))%type}}}}.
Proof.
induction l as [l IND] using strong_ind_type.
induction T;
intros gamma1' gamma2' delta' phi' lambda' kappa' OC' d r alpha' LT REL Tshow;
inversion Tshow as [[[[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth] Tleft] Tright].

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold cpl_tree_left in Tgam;
      subst.

1 : refine (existT _ 0 (existT _ 0 (existT _ 0 (pair (pair (existT _ (leaf OC (gamma1' ++ phi' :: gamma2') delta alpha) _) (Nat.le_refl _)) (Nat.le_refl _))))).
    repeat split;
    intros o IN;
    unfold cpl_tree_left in *;
    unfold cpl_tree_right in *;
    rewrite flat_map_app in *.
    apply in_app_or in IN as [IN1 | IN2].
    refine (TG_app o (in_or_app _ _ _ (or_introl IN1))).
    apply in_app_or in IN2 as [IN2 | IN3].
    apply (bnd_vars_in_type lambda' kappa') in IN2 as [EQ | [NE IN2]].
    subst.
    apply (OC_null OC _ _ REL).
    apply TG_app, in_or_app, or_intror, in_or_app, or_introl, IN2.
    apply TG_app, in_or_app, or_intror, in_or_app, or_intror, IN3.
    apply TD_app, IN.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    subst.
    destruct b.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_1 _ Tshow'') LTD) LT')))).
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_deg_up_2 _ Tshow'') LTD) LT')))).

1 : { destruct gamma1' as [ | f gamma1'].
      - rewrite app_nil_l in Tgam.
        pose proof (struct_show_self Tstr) as Tshow'.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        rewrite TG in Tshow'.
        rewrite <- (app_nil_l (_ :: gamma2')), app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) REL Tshow') as [d' [l' [r' [[[T' Tshow''] LTD] LT']]]].
        inversion Tshow'' as [[[[[[[Tstr' Tgam'] Tdelt'] Tcon'] Tdeg'] Tdepth'] Tleft'] Tright'].
        subst.
        rewrite <- app_comm_cons, app_nil_l, <- (app_nil_l (_ :: _)) in Tshow''.
        unfold cpl_tree_constraint at 1 in REL.
        rewrite <- Tcon' in REL.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ _ LT' REL Tshow'') as [d'' [l'' [r'' [[Tshow''' LTD'] LT'']]]].
        rewrite app_nil_l in *.
        refine (existT _ d'' (existT _ (S l'') (existT _ r'' (pair (pair (cpl_tree_con_l Tshow''') (Nat.le_trans _ _ _ LTD' LTD)) (le_n_S _ _ (Nat.le_trans _ _ _ LT'' LT')))))).
      - rewrite <- app_comm_cons in Tgam.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TG in Tshow'.
        rewrite !app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1, cpl_tree_deg at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IND _ LT _ _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        rewrite <- app_comm_cons.
        refine (existT _ d' (existT _ (S l') (existT _ r' (pair (pair (cpl_tree_con_l Tshow'') LTD) (le_n_S _ _ LT'))))). }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TD in Tshow''.
    refine (existT _ d' (existT _ l' (existT _ (S r') (pair (pair (cpl_tree_con_r Tshow'') LTD) LT')))).

1 : destruct (perm_split (perm_sym bury_is_perm) Tgam) as [gamma1 [gamma2 [EQ perm]]].
    pose proof (struct_show_self Tstr) as Tshow'.
    rewrite EQ in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, cpl_tree_deg.
    fold cpl_tree_depth (cpl_tree_deg T).
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_left _ Tshow'') LTD) LT')))).
    apply perm_trans with (phi' :: gamma1 ++ gamma2).
    apply perm_head.
    apply perm_trans with (phi' :: gamma1' ++ gamma2').
    apply perm_skip, perm_sym, perm.
    apply perm_sym, perm_head.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_comm_right bury_is_perm Tshow'') LTD) LT')))).

1 : { destruct gamma1'.
      - rewrite app_nil_l in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        refine (existT _ (cpl_tree_depth T) (existT _ (left_ops T) (existT _ (right_ops T) (pair (pair (cpl_tree_wkn_l _ (existT _ T _)) (Nat.le_refl _)) (Nat.le_refl _))))).
        intros o IN.
        apply (bnd_vars_in_type lambda' kappa') in IN as [EQ | [NE IN]].
        subst.
        apply (OC_null (cpl_tree_constraint T) _ _ REL).
        apply TG_app, in_or_app, or_introl, IN.
        repeat split.
        apply Tstr.
      - rewrite <- app_comm_cons in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite EQ2 in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_l _ Tshow'') LTD) LT')))).
        intros o IN.
        apply TG_app, in_or_app, or_introl, IN. }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_wkn_r _ Tshow'') LTD) LT')))).
    intros o IN.
    apply TD_app, in_or_app, or_introl, IN.

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    admit.
    (* pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC in Tshow''.
    refine (existT _ d' (existT _ l' (existT _ r' (pair (pair (cpl_tree_reset _ _ KIN Tshow'') LTD) LT')))).
    intros FAL.
    apply KNING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_intror, in_or_app, or_introl, in_or_app, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.
    intros FAL.
    apply KNIND, FAL. *)

1 : { destruct gamma1'.
      - rewrite app_nil_l in *.
        inversion Tgam.
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite <- TG.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1, cpl_tree_deg at 1, cpl_tree_depth at 1, left_ops at 1.
        fold cpl_tree_depth left_ops.
        refine (existT _ _ (existT _ _ (existT _ _ (pair (pair (existT _ T Tshow') (le_S _ _ (Nat.le_refl _))) (Nat.le_refl _))))).
      - rewrite <- app_comm_cons in *.
        inversion Tgam as [[EQ1 EQ2]].
        subst.
        pose proof (struct_show_self Tstr) as Tshow'.
        rewrite TG, app_comm_cons in Tshow'.
        unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
        unfold cpl_tree_depth.
        fold cpl_tree_depth.
        pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
        refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_l TOC_rel Tshow'') (le_n_S _ _ LTD)) LT')))). }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite Tgam in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    assert (OC_rel (cpl_tree_constraint T) lambda' kappa' = true) as REL'.
    { rewrite TOC.
      unfold OC_rel, add_fresh_child.
      unfold projT2.
      unfold projT1.
      unfold cpl_tree_constraint at 1 in REL.
      rewrite REL.
      reflexivity. }
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL' Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    rewrite TOC, TD in Tshow''.
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_bnd_r _ _ _ _ Tshow'') (le_n_S _ _ LTD)) LT')))).
    intros FAL.
    apply NING.
    rewrite Tgam.
    rewrite flat_map_app in *.
    apply in_app_or in FAL as [FAL1 | FAL2].
    apply in_or_app, or_introl, FAL1.
    apply in_app_or in FAL2 as [FAL2 | FAL3].
    apply in_or_app, or_intror, in_or_app, or_introl, or_intror, FAL2.
    apply in_or_app, or_intror, in_or_app, or_intror, FAL3.
    intros FAL.
    apply NIND, FAL.

1 : { destruct gamma1'.
      rewrite app_nil_l in *.
      inversion Tgam as [[EQ1 EQ2]].
      rewrite <- app_comm_cons in *.
      inversion Tgam as [[EQ1 EQ2]].
      subst.
      pose proof (struct_show_self T1str) as T1show.
      rewrite T1G, EQ2, app_comm_cons in T1show.
      pose proof (struct_show_self T2str) as T2show.
      rewrite T2D, EQ2, T2OC in T2show.
      unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
      unfold cpl_tree_depth, left_ops;
      fold cpl_tree_depth left_ops.
      pose proof (IHT1 _ _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _) LT) REL T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
      rewrite <- T2OC in REL.
      pose proof (IHT2 _ _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _) LT) REL T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
      refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_imp_l T1show' T2show') _) _)))).
      lia.
      lia. }

1 : pose proof (struct_show_self Tstr) as Tshow'.
    rewrite TG, TD, app_comm_cons in Tshow'.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ _ _ LT REL Tshow') as [d' [l' [r' [[Tshow'' LTD] LT']]]].
    refine (existT _ (S d') (existT _ l' (existT _ r' (pair (pair (cpl_tree_imp_r Tshow'') (le_n_S _ _ LTD)) LT')))).

1 : pose proof (struct_show_self T1str) as T1show.
    rewrite Tgam, T1D in T1show.
    pose proof (struct_show_self T2str) as T2show.
    rewrite T2G, Tgam, T2OC, app_comm_cons in T2show.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth, left_ops;
    fold cpl_tree_depth left_ops.
    pose proof (IHT1 _ _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l _ _)  LT) REL T1show) as [d1 [l1 [r1 [[T1show' LT1D] LT1]]]].
    rewrite <- T2OC in REL.
    pose proof (IHT2 _ _ _ _ _ _ _ _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r _ _)  LT) REL T2show) as [d2 [l2 [r2 [[T2show' LT2D] LT2]]]].
    refine (existT _ (S (Init.Nat.max d1 d2)) (existT _ (Init.Nat.max l1 l2) (existT _ (Init.Nat.max r1 r2) (pair (pair (cpl_tree_cut T1show' T2show') (le_n_S _ _ _)) _)))).
    lia.
    lia.
Qed.
*)

(*
Master destruct tactic.

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW TOC]] [NING NIND]] TDeg]].
12 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
13 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
15 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
16 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

*)