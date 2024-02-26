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
Require Import Arith.


Inductive cpl_tree : Type :=
| leaf : forall (OC : constraint) (gamma delta : list formula) (alpha : ordinal), cpl_tree

| deg_up : forall {OC : constraint} {gamma delta : list formula} (alpha beta : ordinal) (T' : cpl_tree), cpl_tree 

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

| @deg_up OC gamma delta alpha beta T' => gamma 

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

| @deg_up OC gamma delta alpha beta T' => delta

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

| @deg_up OC gamma delta alpha beta T' => OC

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

| @deg_up OC gamma delta alpha beta T' => omax alpha beta

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

| @deg_up OC gamma delta alpha beta T' => (cpl_leaves T')

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


Fixpoint cpl_tree_depth (T : cpl_tree) : nat :=
match T with
| leaf OC gamma delta alpha => 0

| @deg_up OC gamma delta alpha beta T' => cpl_tree_depth T'

| @con_l OC gamma delta phi alpha T' => cpl_tree_depth T'

| @con_r OC gamma delta phi alpha T' => cpl_tree_depth T'


| @ex_l OC gamma delta n alpha T' => cpl_tree_depth T'

| @ex_r OC gamma delta n alpha T' => cpl_tree_depth T'


| @wkn_l OC gamma delta phi alpha T' => S (cpl_tree_depth T')

| @wkn_r OC gamma delta phi alpha T' => S (cpl_tree_depth T')

| @rst OC gamma delta kappa alpha T' => S (cpl_tree_depth T')


| @bnd_l OC gamma delta phi lambda kappa alpha T' => S (cpl_tree_depth T')

| @bnd_r OC gamma delta phi lambda kappa alpha T' => S (cpl_tree_depth T')


| @imp_l OC gamma delta phi psi alpha1 alpha2 T1 T2 => S (max (cpl_tree_depth T1) (cpl_tree_depth T2))

| @imp_r OC gamma delta phi psi alpha T' => S (cpl_tree_depth T')


| @cut OC gamma delta phi alpha1 alpha2 T1 T2 => S (max (cpl_tree_depth T1) (cpl_tree_depth T2))
end.

Lemma cpl_tree_eq_dec : forall (T1 T2 : cpl_tree), {T1 = T2} + {T1 <> T2}.
Proof.
induction T1;
destruct T2.

2-15 : right; discriminate.
3-16 : right; discriminate.
4-17 : right; discriminate.
5-18 : right; discriminate.
6-19 : right; discriminate.
7-20 : right; discriminate.
8-21 : right; discriminate.
9-22 : right; discriminate.
10-23 : right; discriminate.
11-24 : right; discriminate.
12-25 : right; discriminate.
13-26 : right; discriminate.
14-27 : right; discriminate.

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
      try destruct (ordinal_eq_dec beta beta0) as [EQB | NE];
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

| @deg_up OC gamma delta alpha beta T' => structured T' * (semi_applicable OC T * (cpl_tree_left T' = gamma) * (cpl_tree_right T' = delta) * (cpl_tree_constraint T' = OC) * (cpl_tree_deg T' = alpha))

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
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold provable in *;
      unfold cpl_tree_constraint, cpl_tree_left, cpl_tree_right, cpl_tree_deg.

1 : specialize (LEAF (OC, gamma, delta, alpha) (or_introl eq_refl)).
    apply LEAF.

1 : apply ptree_deg_up.
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

Definition T_shows (T : cpl_tree) (OC : constraint) (gamma delta : list formula) (alpha : ordinal) (d : nat) : Type :=
  (structured T) * (cpl_tree_left T = gamma) * (cpl_tree_right T = delta) * (cpl_tree_constraint T = OC) * (cpl_tree_deg T = alpha) * (cpl_tree_depth T = d).

Definition showable (OC : constraint) (gamma delta : list formula) (alpha : ordinal) (d : nat) : Type :=
  {T : cpl_tree & (T_shows T OC gamma delta alpha d)}.

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
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : repeat split;
      unfold cpl_tree_left, cpl_tree_right, flat_map, vars_in;
      fold vars_in (flat_map vars_in);
      try apply TG_app;
      try apply TD_app.
Qed.


Lemma cpl_tree_deg_up :
  forall {OC : constraint} {gamma delta : list formula} {alpha beta : ordinal} {d : nat},
      showable OC gamma delta alpha d ->
          showable OC gamma delta (omax alpha beta) d.
Proof.
intros OC gamma delta alpha beta d [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
subst.
refine (existT _ (deg_up (cpl_tree_deg T) beta T) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ Tstr)).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_con_l :
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha : ordinal} {d : nat},
      showable OC (phi :: phi :: gamma) delta alpha d ->
          showable OC (phi :: gamma) delta alpha d.
Proof.
intros OC gamma delta phi alpha d [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
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
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha : ordinal} {d : nat},
      showable OC gamma (phi :: phi :: delta) alpha d ->
          showable OC gamma (phi :: delta) alpha d.
Proof.
intros OC gamma delta phi alpha d [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
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
  forall {OC : constraint} {gamma delta : list formula} {n : nat} {alpha : ordinal} {d : nat},
      showable OC gamma delta alpha d ->
          showable OC (bury gamma n) delta alpha d.
Proof.
intros OC gamma delta n alpha d [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
subst.
refine (existT _ (ex_l n T) _).
repeat split;
try assumption.
1 : refine (incl_tran (fun A => proj1 (flat_map_bury_incl A)) (fst (structured_OC_semiapp _ Tstr))).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_ex_r : 
  forall {OC : constraint} {gamma delta : list formula} {n : nat} {alpha : ordinal} {d : nat},
      showable OC gamma delta alpha d ->
          showable OC gamma (bury delta n) alpha d.
Proof.
intros OC gamma delta n alpha d [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
subst.
refine (existT _ (ex_r n T) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ Tstr)).
1 : refine (incl_tran (fun A => proj1 (flat_map_bury_incl A)) (snd (structured_OC_semiapp _ Tstr))).
Qed.

Lemma cpl_tree_wkn_l : 
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha: ordinal} {d : nat},
      incl (vars_in phi) (OC_list OC) ->
          showable OC gamma delta alpha d ->
              showable OC (phi :: gamma) delta alpha (S d).
Proof.
intros OC gamma delta phi alpha d SUB [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
subst.
refine (existT _ (wkn_l phi T) _).
repeat split;
try assumption.
1 : apply (incl_app SUB (fst (structured_OC_semiapp _ Tstr))).
1 : apply (snd (structured_OC_semiapp _ Tstr)).
Qed.

Lemma cpl_tree_wkn_r : 
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha: ordinal} {d : nat},
      incl (vars_in phi) (OC_list OC) ->
          showable OC gamma delta alpha d ->
              showable OC gamma (phi :: delta) alpha (S d).
Proof.
intros OC gamma delta phi alpha d SUB [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
subst.
refine (existT _ (wkn_r phi T) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ Tstr)).
1 : apply (incl_app SUB (snd (structured_OC_semiapp _ Tstr))).
Qed.

Lemma cpl_tree_weaken_left : 
  forall {gamma delta sigma : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      incl (flat_map vars_in sigma) (OC_list OC) ->
          showable OC gamma delta alpha d ->
              showable OC (gamma ++ sigma) delta alpha (length sigma + d).
Proof.
intros gamma delta sigma.
revert gamma delta.
apply (rev_ind_type (fun sigma => forall (gamma delta : list formula) (OC : constraint) (alpha : ordinal) (d : nat), incl (flat_map vars_in sigma) (OC_list OC) -> showable OC gamma delta alpha d -> showable OC (gamma ++ sigma) delta alpha (length sigma + d))).
- intros gamma delta OC alpha d SUB Tshow.
  rewrite app_nil_r.
  apply Tshow.
- intros phi sigma' IND gamma delta OC alpha d SUB Tshow.
  rewrite app_assoc.
  rewrite <- (app_nil_l ((gamma ++ sigma') ++ [phi])), <- (@bury_type _ phi [] (gamma ++ sigma')), app_nil_l, app_length.
  unfold length at 3.
  rewrite <- plus_n_Sm, <- plus_n_O, plus_Sn_m.
  apply cpl_tree_ex_l, cpl_tree_wkn_l, IND, Tshow;
  rewrite flat_map_app in SUB.
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_intror (in_or_app _ _ _ (or_introl IN))))).
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_introl IN))).
Qed.

Lemma cpl_tree_weaken_right : 
  forall {gamma delta pi : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      incl (flat_map vars_in pi) (OC_list OC) ->
          showable OC gamma delta alpha d ->
              showable OC gamma (delta ++ pi) alpha (length pi + d).
Proof.
intros gamma delta pi.
revert gamma delta.
apply (rev_ind_type (fun pi => forall (gamma delta : list formula) (OC : constraint) (alpha : ordinal) (d : nat), incl (flat_map vars_in pi) (OC_list OC) -> showable OC gamma delta alpha d -> showable OC gamma (delta ++ pi) alpha (length pi + d))).
- intros gamma delta OC alpha d SUB Tshow.
  rewrite app_nil_r.
  apply Tshow.
- intros phi pi' IND gamma delta OC alpha d SUB Tshow.
  rewrite app_assoc.
  rewrite <- (app_nil_l ((delta ++ pi') ++ [phi])), <- (@bury_type _ phi [] (delta ++ pi')), app_nil_l, app_length.
  unfold length at 3.
  rewrite <- plus_n_Sm, <- plus_n_O, plus_Sn_m.
  apply cpl_tree_ex_r, cpl_tree_wkn_r, IND, Tshow;
  rewrite flat_map_app in SUB.
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_intror (in_or_app _ _ _ (or_introl IN))))).
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_introl IN))).
Qed.

Lemma cpl_tree_reset : 
  forall {gamma delta : list formula} {OC : constraint} {kappa : ovar} {alpha: ordinal} {d : nat},
      ~ In kappa (flat_map vars_used gamma) ->
          ~ In kappa (flat_map vars_used delta) ->
              OC_elt OC kappa ->
                  showable (restriction OC (children OC kappa) (children_subset OC kappa)) gamma delta alpha d ->
                      showable OC gamma delta alpha (S d).
Proof.
intros gamma delta OC kappa alpha d NING NIND ELT [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
subst.
refine (existT _ (rst kappa T) _).
repeat split;
try assumption.
1 : apply (incl_tran (fst (structured_OC_semiapp _ Tstr))).
2 : apply (incl_tran (snd (structured_OC_semiapp _ Tstr))).
1,2 : rewrite Tcon;
      apply incl_filter.
Qed.

Lemma cpl_tree_bnd_l : 
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {lambda kappa : ovar} {alpha : ordinal} {d : nat},
      OC_rel OC lambda kappa = true ->
          showable OC (phi :: gamma) delta alpha d ->
              showable OC ((bnd lambda kappa phi) :: gamma) delta alpha (S d).
Proof.
intros OC gamma delta phi lambda kappa alpha d rel [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
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
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {lambda kappa : ovar} {alpha : ordinal} {d : nat} (NEW : ~ OC_elt OC lambda) (KIN : OC_elt OC kappa),
      ~ In lambda (flat_map vars_used gamma) ->
          ~ In lambda (flat_map vars_used (phi :: delta)) ->
              showable (add_fresh_child OC lambda kappa NEW KIN) gamma (phi :: delta) alpha d ->
                  showable OC gamma ((bnd lambda kappa phi) :: delta) alpha (S d).
Proof.
intros OC gamma delta phi lambda kappa alpha d NEW KIN NING NIND [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
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

Lemma cpl_tree_imp_l : 
  forall {OC : constraint} {gamma delta : list formula} {phi psi : formula} {alpha1 alpha2 : ordinal} {d1 d2 : nat},
      showable OC (psi :: gamma) delta alpha1 d1 ->
          showable OC gamma (phi :: delta) alpha2 d2 ->
              showable OC ((imp phi psi) :: gamma) delta (omax alpha1 alpha2) (S (max d1 d2)).
Proof.
intros OC gamma delta phi psi alpha1 alpha2 d1 d2 [T1 [[[[[T1str T1gam] T1delt] T1con] T1deg] T1dep]] [T2 [[[[[T2str T2gam] T2delt] T2con] T2deg] T2dep]].
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
  forall {OC : constraint} {gamma delta : list formula} {phi psi : formula} {alpha : ordinal} {d : nat},
      showable OC (phi :: gamma) (psi :: delta) alpha d ->
          showable OC gamma ((imp phi psi) :: delta) alpha (S d).
Proof.
intros OC gamma delta phi psi alpha d [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
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
  forall {OC : constraint} {gamma delta : list formula} {phi : formula} {alpha1 alpha2 : ordinal} {d1 d2 : nat},
      showable OC gamma (phi :: delta) alpha1 d1 ->
          showable OC (phi :: gamma) delta alpha2 d2 ->
              showable OC gamma delta (omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))) (S (max d1 d2)).
Proof.
intros OC gamma delta phi alpha1 alpha2 d1 d2 [T1 [[[[[T1str T1gam] T1delt] T1con] T1deg] T1dep]] [T2 [[[[[T2str T2gam] T2delt] T2con] T2deg] T2dep]].
subst.
refine (existT _ (cut phi T1 T2) _).
repeat split;
try assumption.
1 : apply (fst (structured_OC_semiapp _ T1str)).
1 : rewrite <- T2con.
    apply (snd (structured_OC_semiapp _ T2str)).
Qed.

Lemma commutative_left_aux :
  forall {LN : list nat} {gamma1 gamma2 delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      (set_bury gamma1 LN = gamma2) ->
          showable OC gamma1 delta alpha d ->
              showable OC gamma2 delta alpha d.
Proof.
induction LN;
intros gamma1 gamma2 delta OC alpha d EQ Tshow.
- unfold set_bury in EQ.
  subst.
  apply Tshow.
- unfold set_bury in EQ;
  fold @set_bury in EQ.
  apply (IHLN _ _ _ _ _ _ EQ), cpl_tree_ex_l, Tshow.
Qed.

Lemma cpl_tree_comm_left :
  forall {gamma1 gamma2 delta : list formula} {OC : constraint} {alpha : ordinal} {d : nat},
      (perm gamma1 gamma2) ->
          showable OC gamma1 delta alpha d ->
              showable OC gamma2 delta alpha d.
Proof.
intros gamma1 gamma2 delta OC alpha d perm SHOW.
pose proof (set_bury_eq_perm perm) as [LN EQ].
apply (commutative_left_aux EQ SHOW).
Defined.

Lemma prove_dups_left_aux :
  forall {n : nat} {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      length gamma = n ->
          showable OC gamma delta alpha d ->
              showable OC (nodup form_eq_dec gamma) delta alpha d.
Proof.
induction n;
intros gamma delta OC alpha d EQ Tshow.
- destruct gamma.
  + apply Tshow.
  + inversion EQ.
- case (no_dup_dec_cases form_eq_dec gamma) as [NDG | DG].
  + rewrite (nodup_fixed_point _ NDG).
    apply Tshow.
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
    apply (cpl_tree_comm_left (perm_sym (perm_nodup form_eq_dec double_perm_head))).
    rewrite nodup_double_cons.
    apply (IHn _ _ _ _ _ LEN (cpl_tree_con_l (cpl_tree_comm_left (double_perm_head) Tshow))).
Qed.

Lemma cpl_tree_nodups_left :
  forall {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      showable OC gamma delta alpha d ->
          showable OC (nodup form_eq_dec gamma) delta alpha d.
Proof.
intros gamma delta OC alpha d Tshow.
apply (prove_dups_left_aux eq_refl Tshow).
Qed.

Lemma prove_extras_left_aux :
  forall {n : nat} {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      length gamma = n ->
          showable OC (nodup form_eq_dec gamma) delta alpha d ->
              {d' : nat & showable OC gamma delta alpha d'}.
Proof.
induction n;
intros gamma delta OC alpha d EQ Tshow.
- destruct gamma.
  apply (existT _ d Tshow).
  inversion EQ.
- case (no_dup_dec_cases form_eq_dec gamma) as [NDG | DG].
+ rewrite <- (nodup_fixed_point form_eq_dec NDG).
  apply (existT _ d Tshow).
+ destruct (has_dups_split form_eq_dec DG) as [A [gamma1 [gamma2 [gamma3 EQL]]]].
  subst.
  destruct (@nodup_split_perm _ form_eq_dec (A :: A :: gamma1 ++ gamma2 ++ gamma3)) as [sigma [PERM SUB]].
  assert (incl (flat_map vars_in sigma) (OC_list OC)) as SUB'.
  { destruct Tshow as [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
    refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (incl_tran SUB (incl_tran (fun B IN => perm_in form_eq_dec (perm_sym double_perm_head) _ IN) (fun B IN => proj2 (nodup_In _ _ _) IN)))) _).
    rewrite <- Tgam, <- Tcon.
    apply (fst (structured_OC_semiapp _ Tstr)). }
  apply (existT _ (length sigma + d) (cpl_tree_comm_left (perm_trans _ _ _ (perm_sym PERM) (perm_sym double_perm_head)) (cpl_tree_weaken_left SUB' ((cpl_tree_comm_left (perm_nodup form_eq_dec double_perm_head)) Tshow)))).
Qed.

Lemma cpl_tree_redups_left :
  forall {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      showable OC (nodup form_eq_dec gamma) delta alpha d ->
          {d' : nat & showable OC gamma delta alpha d'}.
Proof.
intros gamma delta OC alpha d Tshow.
apply (prove_extras_left_aux eq_refl Tshow).
Qed.

Lemma cpl_tree_equiv_left :
  forall {gamma1 gamma2 delta : list formula} {OC : constraint} {alpha : ordinal} {d : nat},
      (forall A : formula, In A gamma1 <-> In A gamma2) ->
          showable OC gamma1 delta alpha d ->
              {d' : nat & showable OC gamma2 delta alpha d'}.
Proof.
intros gamma1 gamma2 delta OC alpha d EQUIV Tshow.
apply (cpl_tree_redups_left ((cpl_tree_comm_left (equiv_nodup_perm form_eq_dec EQUIV)) (cpl_tree_nodups_left Tshow))).
Qed.

Lemma commutative_right_aux :
  forall {LN : list nat} {gamma delta1 delta2 : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      (set_bury delta1 LN = delta2) ->
          showable OC gamma delta1 alpha d ->
              showable OC gamma delta2 alpha d.
Proof.
induction LN;
intros gamma1 gamma2 delta OC alpha d EQ Tshow.
- unfold set_bury in EQ.
  subst.
  apply Tshow.
- unfold set_bury in EQ;
  fold @set_bury in EQ.
  apply (IHLN _ _ _ _ _ _ EQ), cpl_tree_ex_r, Tshow.
Qed.

Lemma cpl_tree_comm_right :
  forall {gamma delta1 delta2 : list formula} {OC : constraint} {alpha : ordinal} {d : nat},
      (perm delta1 delta2) ->
          showable OC gamma delta1 alpha d ->
              showable OC gamma delta2 alpha d.
Proof.
intros gamma delta1 delta2 OC alpha d perm.
pose proof (set_bury_eq_perm perm) as [LN EQ].
apply (commutative_right_aux EQ).
Defined.

Lemma prove_dups_right_aux :
  forall {n : nat} {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      length delta = n ->
          showable OC gamma delta alpha d ->
              showable OC gamma (nodup form_eq_dec delta) alpha d.
Proof.
induction n;
intros gamma delta OC alpha d EQ Tshow.
- destruct delta.
  apply Tshow.
  inversion EQ.
- case (no_dup_dec_cases form_eq_dec delta) as [NDD | DD].
  + rewrite (nodup_fixed_point _ NDD).
    apply Tshow.
  + destruct (has_dups_split form_eq_dec DD) as [A [delta1 [delta2 [delta3 EQL]]]].
    subst.
    apply (cpl_tree_comm_right (perm_sym (perm_nodup form_eq_dec double_perm_head))).
    rewrite nodup_double_cons.
    apply IHn, cpl_tree_con_r, (cpl_tree_comm_right (double_perm_head)), Tshow.
    rewrite app_length in EQ.
    unfold length in *;
    fold (@length formula) in *.
    repeat rewrite app_length in *.
    unfold length in EQ;
    fold (@length formula) in EQ.
    repeat rewrite <- plus_n_Sm in EQ.
    lia.
Qed.

Lemma cpl_tree_nodups_right :
  forall {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      showable OC gamma delta alpha d ->
          showable OC gamma (nodup form_eq_dec delta) alpha d.
Proof.
intros gamma delta OC alpha d Tshow.
apply (prove_dups_right_aux eq_refl Tshow).
Qed.

Lemma prove_extras_right_aux :
  forall {n : nat} {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      length delta = n ->
          showable OC gamma (nodup form_eq_dec delta) alpha d ->
              {d' : nat & showable OC gamma delta alpha d'}.
Proof.
induction n;
intros gamma delta OC alpha d EQ Tshow.
- destruct delta.
  refine (existT _ d Tshow).
  inversion EQ.
- case (no_dup_dec_cases form_eq_dec delta) as [NDD | DD].
  + rewrite <- (nodup_fixed_point form_eq_dec NDD).
    refine (existT _ d Tshow).
  + destruct (has_dups_split form_eq_dec DD) as [A [delta1 [delta2 [delta3 EQL]]]].
    subst.
    destruct (@nodup_split_perm _ form_eq_dec (A :: A :: delta1 ++ delta2 ++ delta3)) as [pi [PERM SUB]].
    assert (incl (flat_map vars_in pi) (OC_list OC)) as SUB'.
    { destruct Tshow as [T [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdep]].
      refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (incl_tran SUB (incl_tran (fun B IN => perm_in form_eq_dec (perm_sym double_perm_head) _ IN) (fun B IN => proj2 (nodup_In _ _ _) IN)))) _).
      rewrite <- Tdelt, <- Tcon.
      apply (snd (structured_OC_semiapp _ Tstr)). }
    apply (existT _ (length pi + d) (cpl_tree_comm_right (perm_trans _ _ _ (perm_sym PERM) (perm_sym double_perm_head)) (cpl_tree_weaken_right SUB' ((cpl_tree_comm_right (perm_nodup form_eq_dec double_perm_head)) Tshow)))).
Qed.

Lemma cpl_tree_redups_right :
  forall {gamma delta : list formula} {OC : constraint} {alpha: ordinal} {d : nat},
      showable OC gamma (nodup form_eq_dec delta) alpha d ->
          {d' : nat & showable OC gamma delta alpha d'}.
Proof.
intros gamma delta OC alpha d Tshow.
apply (prove_extras_right_aux eq_refl Tshow).
Qed.

Lemma cpl_tree_equiv_right :
  forall {gamma delta1 delta2 : list formula} {OC : constraint} {alpha : ordinal} {d : nat},
      (forall A : formula, In A delta1 <-> In A delta2) ->
          showable OC gamma delta1 alpha d ->
              {d' : nat & showable OC gamma delta2 alpha d'}.
Proof.
intros gamma delta1 delta2 OC alpha d EQUIV Tshow.
apply (cpl_tree_redups_right ((cpl_tree_comm_right (equiv_nodup_perm form_eq_dec EQUIV)) (cpl_tree_nodups_right Tshow))).
Qed.


Lemma strong_ind_type :
  forall n (P : nat -> Type), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  exact (fun p P F => induction_ltof1 nat (fun m => m) P F p).
Defined.

Lemma cpl_tree_imp_l_inv_2 :
forall {n : nat} {T : cpl_tree} {gamma delta : list formula} {phi psi : formula} {OC : constraint} {alpha : ordinal} {d : nat},
    n = length gamma ->
        T_shows T OC (imp phi psi :: gamma) delta alpha d ->
            showable OC gamma (phi :: delta) alpha d.
Proof.
induction n as [n IND] using strong_ind_type.
induction T;
intros gamma' delta' phi' psi' OC' alpha' d' EQL Tshow;
inversion Tshow as [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth].

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

1 : refine (existT _ (leaf OC gamma' (phi' :: delta) alpha) _).
    repeat split.
    refine (fun o IN => TG_app o (in_or_app _ _ _ (or_intror IN))).
    intros o IN.
    apply in_app_or in IN as [IN1 | IN2].
    refine (TG_app o (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl IN1))))).
    refine (TD_app o IN2).

1 : assert (T_shows T (cpl_tree_constraint T) (imp phi' psi' :: gamma') (cpl_tree_right T) (cpl_tree_deg T) (cpl_tree_depth T)) as Tshow'.
    { repeat split.
      apply Tstr.
      apply Tgam. }
    apply cpl_tree_deg_up.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    apply (IHT _ _ _ _ _ _ _ eq_refl Tshow').

1 : assert (T_shows T (cpl_tree_constraint T) (imp phi' psi' :: imp phi' psi' :: gamma') (cpl_tree_right T) (cpl_tree_deg T) (cpl_tree_depth T)) as Tshow'.
    { repeat split.
      apply Tstr.
      inversion Tgam as [[EQ1 EQ2]].
      subst.
      apply TG. }
    apply cpl_tree_con_r.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1, cpl_tree_deg at 1.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    pose proof (IHT _ _ _ _ _ _ _ _ Tshow').

Lemma cpl_tree_imp_l_inv_2 :
forall {gamma delta : list formula} {phi psi : formula} {OC : constraint} {alpha : ordinal} {d : nat},
    showable OC (imp phi psi :: gamma) delta alpha d ->
        showable OC gamma (phi :: delta) alpha d.
Proof.
induction gamma;
intros delta' phi' psi' OC' alpha' d' [T Tshow];
inversion Tshow as [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth].

induction T.

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

1 : refine (existT _ (leaf OC [] (phi' :: delta) alpha) _).
    repeat split.
    intros o IN.
    inversion IN.
    intros o IN.
    apply in_app_or in IN as [IN1 | IN2].
    refine (TG_app o (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl IN1))))).
    refine (TD_app o IN2).

1 : assert (T_shows T (cpl_tree_constraint T) (imp phi' psi' :: []) (cpl_tree_right T) (cpl_tree_deg T) (cpl_tree_depth T)) as Tshow'.
    { repeat split.
      apply Tstr.
      apply Tgam. }
    apply cpl_tree_deg_up.
    unfold cpl_tree_constraint at 1, cpl_tree_right at 1.
    simpl in IHT.
    unfold cpl_tree_depth.
    fold cpl_tree_depth.
    apply (IHT _ _ _ _ _ _ _).


1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold cpl_tree_left in TG_app, Tgam;
    unfold cpl_tree_right in TD_app, Tdelt;
    unfold cpl_tree_constraint in Tcon;
    unfold cpl_tree_deg in Tdeg;
    unfold cpl_tree_depth in Tdepth;
    fold cpl_tree_depth in Tdepth;
    subst.

1 : refine (existT _ (leaf OC' gamma' (phi' :: delta') alpha') _).
  repeat split.
  refine (fun o IN => TG_app o (in_or_app _ _ _ (or_intror IN))).
  intros o IN.
  apply in_app_or in IN as [IN1 | IN2].
  refine (TG_app o (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl IN1))))).
  refine (TD_app o IN2).

1 : assert (T_shows T (cpl_tree_constraint T) (imp phi' psi' :: gamma') (cpl_tree_right T) (cpl_tree_deg T) (cpl_tree_depth T)) as Tshow'.
  { repeat split.
    apply Tstr.
    apply Tgam. }
  apply cpl_tree_deg_up.
  apply (IHT _ _ _ _ _ _ _ Tshow').



Qed.


Lemma cpl_tree_imp_l_inv_2 :
  forall {T : cpl_tree} {gamma delta : list formula} {phi psi : formula} {OC : constraint} {alpha : ordinal} {d : nat},
      T_shows T OC (imp phi psi :: gamma) delta alpha d ->
          showable OC gamma (phi :: delta) alpha d.
Proof.
induction T;
intros gamma' delta' phi' psi' OC' alpha' d' Tshow;
inversion Tshow as [[[[[Tstr Tgam] Tdelt] Tcon] Tdeg] Tdepth].

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

all : unfold cpl_tree_left in TG_app, Tgam;
      unfold cpl_tree_right in TD_app, Tdelt;
      unfold cpl_tree_constraint in Tcon;
      unfold cpl_tree_deg in Tdeg;
      unfold cpl_tree_depth in Tdepth;
      fold cpl_tree_depth in Tdepth;
      subst.

1 : refine (existT _ (leaf OC' gamma' (phi' :: delta') alpha') _).
    repeat split.
    refine (fun o IN => TG_app o (in_or_app _ _ _ (or_intror IN))).
    intros o IN.
    apply in_app_or in IN as [IN1 | IN2].
    refine (TG_app o (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl IN1))))).
    refine (TD_app o IN2).

1 : assert (T_shows T (cpl_tree_constraint T) (imp phi' psi' :: gamma') (cpl_tree_right T) (cpl_tree_deg T) (cpl_tree_depth T)) as Tshow'.
    { repeat split.
      apply Tstr.
      apply Tgam. }
    apply cpl_tree_deg_up.
    apply (IHT _ _ _ _ _ _ _ Tshow').



Qed.


Lemma cpl_tree_imp_l_inv_2 :
  forall {gamma delta : list formula} {phi psi : formula} {OC : constraint} {alpha : ordinal} {d : nat},
      showable OC (imp phi psi :: gamma) delta alpha d ->
          showable OC gamma (phi :: delta) alpha d.
Proof.
intros gamma delta phi psi OC alpha d Tshow.
apply (cpl_tree_redups_right ((cpl_tree_comm_right (equiv_nodup_perm form_eq_dec EQUIV)) (cpl_tree_nodups_right Tshow))).
Qed.

(*
Master destruct tactic.

1 : destruct Tstr as [TG_app TD_app].
2-8 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
9 : destruct Tstr as [Tstr [[[[[[[TG_app TD_app] TG] TD] KNING] KNIND] [KIN TOC]] TDeg]].
10 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] TOC] TOC_rel] TDeg]].
11 : destruct Tstr as [Tstr [[[[[[TG_app TD_app] TG] TD] [NEW [KIN TOC]]] [NING NIND]] TDeg]].
12 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].
13 : destruct Tstr as [Tstr [[[[[TG_app TD_app] TG] TD] TOC] TDeg]].
14 : destruct Tstr as [[T1str T2str] [[[[[[[[[TG_app TD_app] T1G] T1D] T1OC] T2G] T2D] T2OC] T1Deg] T2Deg]].

*)