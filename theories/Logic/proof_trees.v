From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
(*From Cyclic_PA.Logic Require Import substitute.*)
Require Import Lia.
Require Import List.
Import ListNotations.

Inductive ptree : Type :=
| bot : ptree

| pred : forall (n : nat), forall (pn : predicate n), ptree

| equal : forall (v1 v2 : ivar), ptree


| loop_head : forall (OC : constraint) (gamma delta : list formula) (P_Target : ptree), ptree

(*| deg_up : forall (OC : constraint) (gamma delta : list formula) (alpha beta : ordinal) (LT : ord_lt alpha beta) (P' : ptree), ptree *)

| con_l : forall (OC : constraint) (gamma delta : list formula) (phi : formula) (v1 v2 : ivar) (alpha : ordinal) (P' : ptree), ptree

| con_r : forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha : ordinal) (P' : ptree), ptree

| refl : forall (OC : constraint) (gamma delta : list formula) (v : ivar) (alpha : ordinal) (P' : ptree), ptree


| ex_l : forall (OC : constraint) (gamma delta : list formula) (n : nat) (alpha : ordinal) (P' : ptree), ptree

| ex_r : forall (OC : constraint) (gamma delta : list formula) (n : nat) (alpha : ordinal) (P' : ptree), ptree


| wkn : forall (OC : constraint) (gamma delta sigma pi : list formula) (alpha : ordinal) (P' : ptree), ptree

| rst : forall (OC : constraint) (gamma delta : list formula) (kappa : ovar) (alpha : ordinal) (P' : ptree), ptree


| ug_l : forall (OC : constraint) (gamma delta : list formula) (phi : formula) (v : ivar) (alpha : ordinal) (P' : ptree), ptree

| ug_r : forall (OC : constraint) (gamma delta : list formula) (phi : formula) (v : ivar) (alpha : ordinal) (P' : ptree), ptree

| bnd_l : forall (OC : constraint) (gamma delta : list formula) (phi : formula) (lambda kappa : ovar) (alpha : ordinal) (P' : ptree), ptree

| bnd_r : forall (OC : constraint) (gamma delta : list formula) (phi : formula) (lambda kappa : ovar) (alpha : ordinal) (P' : ptree), ptree


| imp_l : forall (OC : constraint) (gamma delta : list formula) (phi psi : formula) (alpha1 alpha2 : ordinal) (P1 P2 : ptree), ptree

| imp_r : forall (OC : constraint) (gamma delta : list formula) (phi psi : formula) (alpha : ordinal) (P' : ptree), ptree


| cut : forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha1 alpha2 : ordinal) (P1 P2 : ptree), ptree.

Lemma ptree_dec : forall (P1 P2 : ptree), {P1 = P2} + {P1 <> P2}.
Proof.
induction P1;
destruct P2.

324 : { destruct (IHP1_1 P2_1) as [EQ1 | NE1];
        destruct (IHP1_2 P2_2) as [EQ2 | NE2];
        destruct (constraint_eq_dec P2_2) as [EQ2 | NE2];
        try destruct EQ1;
        try destruct EQ2.
        left; reflexivity. }

all : right; try discriminate.

2-19 : right; discriminate.
3-20 : right; discriminate.
4-21 : right; discriminate.
5-22 : right; discriminate.
6-23 : right; discriminate.
7-24 : right; discriminate.
8-25 : right; discriminate.
9-26 : right; discriminate.
10-27 : right; discriminate.
11-28 : right; discriminate.
12-29 : right; discriminate.
13-30 : right; discriminate.
14-31 : right; discriminate.
15-32 : right; discriminate.
16-33 : right; discriminate.
17-34 : right; discriminate.
18-35 : right; discriminate.

1 : apply left, eq_refl.

1 : destruct (nat_eq_dec n n0) as [EQ | NE].

1 : destruct EQ.
    destruct pn;
    destruct pn0.

apply pred

auto.
discriminate.

Definition ptree_left (P : ptree) : list formula :=
match P with
| bot => [fal]

| pred n pn => [prd n pn]

| equal v1 v2 => [equ v1 v2]

| loop_head OC gamma delta P_Target => gamma

| con_l OC gamma delta phi v1 v2 alpha P' => (equ v1 v2) :: phi :: gamma

| con_r OC gamma delta phi alpha P' => gamma

| refl OC gamma delta v alpha P' => gamma


| ex_l OC gamma delta n alpha P' => bury gamma n

| ex_r OC gamma delta n alpha P' => gamma


| wkn OC gamma delta sigma pi alpha P' => gamma ++ sigma

| rst OC gamma delta kappa alpha P' => gamma

| ug_l OC gamma delta phi v alpha P' => (univ v phi) :: gamma

| ug_r OC gamma delta phi v alpha P' => gamma

| bnd_l OC gamma delta phi lambda kappa alpha P' => (bnd lambda kappa phi) :: gamma

| bnd_r OC gamma delta phi lambda kappa alpha P' => gamma


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => (imp phi psi) :: gamma

| imp_r OC gamma delta phi psi alpha P' => gamma


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => gamma
end.

Definition ptree_right (P : ptree) : list formula :=
match P with
| bot => []

| pred n pn => [prd n pn]

| equal v1 v2 => [equ v1 v2]

| loop_head OC gamma delta P_Target => delta

| con_l OC gamma delta phi v1 v2 alpha P' => delta

| con_r OC gamma delta phi alpha P' => phi :: delta

| refl OC gamma delta v alpha P' => delta


| ex_l OC gamma delta n alpha P' => delta

| ex_r OC gamma delta n alpha P' => bury delta n


| wkn OC gamma delta sigma pi alpha P' => delta ++ pi

| rst OC gamma delta kappa alpha P' => delta

| ug_l OC gamma delta phi v alpha P' => delta

| ug_r OC gamma delta phi v alpha P' => (univ v phi) :: delta

| bnd_l OC gamma delta phi lambda kappa alpha P' => delta

| bnd_r OC gamma delta phi lambda kappa alpha P' => (bnd lambda kappa phi) :: delta


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => delta

| imp_r OC gamma delta phi psi alpha P' => (imp phi psi) :: delta


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => delta
end.

(*
Fixpoint ptree_deg (P : ptree) : ordinal :=
match P with
| bot => cast Zero

| pred n P => cast Zero

| equal v1 v2 => cast Zero

| loop_head OC1 OC2 gamma delta => cast Zero

| con_l OC gamma delta phi v1 v2 alpha P' => alpha

| con_r OC gamma delta phi alpha P' => alpha

| refl OC gamma delta v alpha P' => alpha


| ex_l OC gamma delta n alpha P' => alpha

| ex_r OC gamma delta n alpha P' => alpha


| wkn OC gamma delta sigma pi alpha P' => alpha

| rst OC gamma delta L alpha P' => alpha

| ug_l OC gamma delta phi v alpha P' => alpha

| ug_r OC gamma delta phi v alpha P' => alpha

| bnd_l OC gamma delta phi lambda kappa Des alpha P' => alpha

| bnd_r OC gamma delta phi lambda kappa alpha P' => alpha


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => ord_max alpha1 alpha2

| imp_r OC gamma delta phi psi alpha1 alpha2 P1 P2 => ord_max alpha1 alpha2


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => ord_max (ord_max alpha1 alpha2) (num_conn phi)
end.
*)

Definition ptree_constraint (P : ptree) : constraint :=
match P with
| bot => empty

| pred n pn => empty

| equal v1 v2 => empty

| loop_head OC gamma delta P_Target => OC

| con_l OC gamma delta phi v1 v2 alpha P' => OC

| con_r OC gamma delta phi alpha P' => OC

| refl OC gamma delta v alpha P' => OC


| ex_l OC gamma delta n alpha P' => OC

| ex_r OC gamma delta n alpha P' => OC


| wkn OC gamma delta sigma pi alpha P' => OC

| rst OC gamma delta kappa alpha P' => OC

| ug_l OC gamma delta phi v alpha P' => OC

| ug_r OC gamma delta phi v alpha P' => OC

| bnd_l OC gamma delta phi lambda kappa alpha P' => OC

| bnd_r OC gamma delta phi lambda kappa alpha P' => OC


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => OC

| imp_r OC gamma delta phi psi alpha P' => OC


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => OC
end.

Definition states : Type := constraint * ((list formula) * (list formula)).

Definition ptree_state (P : ptree) : states := pair (ptree_constraint P) (pair (ptree_left P) (ptree_right P)).

(*
Definition ptree_premises (P : ptree) : list ptree :=
match P with
| bot => []

| pred n pn => []

| equal v1 v2 => []

| loop_head OC gamma delta P_Target => [P_Target]

| con_l OC gamma delta phi v1 v2 alpha P' => [P']

| con_r OC gamma delta phi alpha P' => [P']

| refl OC gamma delta v alpha P' => [P']


| ex_l OC gamma delta n alpha P' => [P']

| ex_r OC gamma delta n alpha P' => [P']


| wkn OC gamma delta sigma pi alpha P' => [P']

| rst OC gamma delta kappa alpha P' => [P']

| ug_l OC gamma delta phi v alpha P' => [P']

| ug_r OC gamma delta phi v alpha P' => [P']

| bnd_l OC gamma delta phi lambda kappa alpha P' => [P']

| bnd_r OC gamma delta phi lambda kappa alpha P' => [P']


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => [P1; P2]

| imp_r OC gamma delta phi psi alpha P' => [P']


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => [P1; P2]
end.
*)

Fixpoint leaves (P : ptree) : list ptree :=
match P with
| bot => []

| pred n pn => []

| equal v1 v2 => []

| loop_head OC gamma delta P_Target => [P]

| con_l OC gamma delta phi v1 v2 alpha P' => leaves P'

| con_r OC gamma delta phi alpha P' => leaves P'

| refl OC gamma delta v alpha P' => leaves P'


| ex_l OC gamma delta n alpha P' => leaves P'

| ex_r OC gamma delta n alpha P' => leaves P'


| wkn OC gamma delta sigma pi alpha P' => leaves P'

| rst OC gamma delta kappa alpha P' => leaves P'

| ug_l OC gamma delta phi v alpha P' => leaves P'

| ug_r OC gamma delta phi v alpha P' => leaves P'

| bnd_l OC gamma delta phi lambda kappa alpha P' => leaves P'

| bnd_r OC gamma delta phi lambda kappa alpha P' => leaves P'


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => leaves P1 ++ leaves P2

| imp_r OC gamma delta phi psi alpha P' => leaves P'


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => leaves P1 ++ leaves P2
end.

Definition path_marker := list bool.

Fixpoint path_fit (P : ptree) (M : path_marker) : list states :=
match P, M with
| bot, [true] => [ptree_state P]

| pred n pn, [true] => [ptree_state P]

| equal v1 v2, [true] => [ptree_state P]

| loop_head OC gamma delta P_Target, true :: M' => (ptree_state P) :: path_fit P_Target M'

| con_l OC gamma delta phi v1 v2 alpha P', true :: M' => (ptree_state P) :: path_fit P' M'

| con_r OC gamma delta phi alpha P', true :: M' => (ptree_state P) :: path_fit P' M'

| refl OC gamma delta v alpha P', true :: M' => (ptree_state P) :: path_fit P' M'


| ex_l OC gamma delta n alpha P', true :: M' => (ptree_state P) :: path_fit P' M'

| ex_r OC gamma delta n alpha P', true :: M' => (ptree_state P) :: path_fit P' M'


| wkn OC gamma delta sigma pi alpha P', true :: M' => (ptree_state P) :: path_fit P' M'

| rst OC gamma delta kappa alpha P', true :: M' => (ptree_state P) :: path_fit P' M'

| ug_l OC gamma delta phi v alpha P', true :: M' => (ptree_state P) :: path_fit P' M'

| ug_r OC gamma delta phi v alpha P', true :: M' => (ptree_state P) :: path_fit P' M'

| bnd_l OC gamma delta phi lambda kappa alpha P', true :: M' => (ptree_state P) :: path_fit P' M'

| bnd_r OC gamma delta phi lambda kappa alpha P', true :: M' => (ptree_state P) :: path_fit P' M'


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2, false :: M' => (ptree_state P) :: path_fit P1 M'

| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2, true :: M' => (ptree_state P) :: path_fit P2 M'

| imp_r OC gamma delta phi psi alpha P', true :: M' => (ptree_state P) :: path_fit P' M'


| cut OC gamma delta phi alpha1 alpha2 P1 P2, false :: M' => (ptree_state P) :: path_fit P1 M'

| cut OC gamma delta phi alpha1 alpha2 P1 P2, true :: M' => (ptree_state P) :: path_fit P2 M'

| _ , _ => []
end.

Definition applicable (OC : constraint) (gamma delta : list formula) : Type := (incl (flat_map vars_in gamma) (OC_list OC)) * (incl (flat_map vars_in delta) (OC_list OC)).

Fixpoint struct_valid (P : ptree) : Type :=
match P with
| bot => true = true

| pred n P => true = true

| equal v1 v2 => true = true

| loop_head OC gamma delta P_Target => applicable OC gamma delta * applicable (ptree_constraint P_Target) gamma delta * {sig : ovar -> ovar & coherent sig OC (ptree_constraint P_Target)} * (In (loop_head OC gamma delta bot) (leaves P_Target))

| con_l OC gamma delta phi v1 v2 alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = (equ v1 v2) :: phi :: (substitution phi v1 v2) :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC)

| con_r OC gamma delta phi alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = phi :: phi :: delta) * (ptree_constraint P' = OC)

| refl OC gamma delta v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = equ v v :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC)


| ex_l OC gamma delta n alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC)

| ex_r OC gamma delta n alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC)


| wkn OC gamma delta sigma pi alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC)

| rst OC gamma delta kappa alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (~ In kappa (flat_map vars_in gamma)) * (~ In kappa (flat_map vars_in delta)) * {SUB : (OC_elt OC kappa) & ptree_constraint P' = restriction OC (children OC kappa) (children_subset OC kappa)}

| ug_l OC gamma delta phi v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC)

| ug_r OC gamma delta phi v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = phi :: delta) * (ptree_constraint P' = OC)

| bnd_l OC gamma delta phi lambda kappa alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (OC_rel OC lambda kappa = true)

| bnd_r OC gamma delta phi lambda kappa alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = phi :: delta) * {NEW : ~ OC_elt OC lambda & {KIN : OC_elt OC kappa & ptree_constraint P' = add_fresh_child OC lambda kappa NEW KIN}}


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => struct_valid P1 * struct_valid P2 * applicable OC gamma delta * (ptree_left P1 = psi :: gamma) * (ptree_right P1 = delta) * (ptree_constraint P1 = OC) * (ptree_left P2 = gamma) * (ptree_right P2 = phi :: delta) * (ptree_constraint P2 = OC)

| imp_r OC gamma delta phi psi alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = psi :: delta) * (ptree_constraint P' = OC)


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => struct_valid P1 * struct_valid P2 * applicable OC gamma delta * (ptree_left P1 = gamma) * (ptree_right P1 = phi :: delta) * (ptree_constraint P1 = OC) * (ptree_left P2 = phi :: gamma) * (ptree_right P2 = delta) * (ptree_constraint P2 = OC)
end.

Lemma in_leaves_path : forall (P1 P2 : ptree), In P2 (leaves P1) -> {M : path_marker & {L : list states & path_fit P1 M = L ++ [ptree_state P2]}}.
Proof.
intros P1.
pose (ptree_state P1) as PS.
induction P1;
intros P2 IN.

1-3 : inversion IN.

1 : admit.

12 : { apply in_app_bor in IN as [IN1 | IN2]. }

12,14: admit.

all : destruct (IHP1 P2 IN) as [M [L EQ]];
      exists (true :: M);
      exists (PS :: L);
      unfold path_fit;
      fold path_fit PS;
      rewrite EQ;
      reflexivity.
Qed.

Lemma loop_struct_gives_path : forall (OC : constraint) (gamma delta : list formula) (P_Target : ptree), struct_valid (loop_head OC gamma delta P_Target) -> {M : path_marker & {L : list states & path_fit P_Target M = (ptree_state P_Target) :: L ++ [pair OC (pair gamma delta)]}}.

Definition valid (P : ptree) : Type := (struct_valid P) * (forall (A : formula), In A (leaves P) -> PA_cyclic_axiom A = true).

Definition P_proves (P : ptree) (A : formula) (d : nat) (alpha : ord) : Type :=
  (ptree_formula P = A) * (valid P) *
  (d = ptree_deg P) * (alpha = ptree_ord P).

Definition provable (A : formula) (d : nat) (alpha : ord) : Type :=
  {P : ptree & P_proves P A d alpha}.

Lemma structural_pre_theorem :
    forall {A : formula} {d : nat} {alpha : ord} {L : list formula} (ST : PA_cyclic_pre A d alpha L),
        {P : ptree & prod (prod( prod (prod (ptree_formula P = A) (struct_valid P)) (d = ptree_deg P)) (alpha = ptree_ord P)) (leaves P = L)}.
intros A d alpha L TS.
induction TS;
try destruct IHTS as [P [[[[PF PSV] PD] PO] PN]];
try destruct IHTS1 as [P1 [[[[P1F P1SV] P1D] P1H] P1N]];
try destruct IHTS2 as [P2 [[[[P2F P2SV] P2D] P2H] P2N]].
- exists (deg_up d' P). repeat split; auto. lia.
- exists (ord_up beta P). repeat split; auto. rewrite <- PO. auto.
- exists (leaf_ex n P). repeat split; auto. rewrite PN. apply l. unfold leaves; fold leaves. rewrite PN. reflexivity.
- exists (node A). repeat split.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (weakening_ad A D (ptree_deg P) alpha P). repeat split; auto. rewrite PN. apply FLSub.
- exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto.  rewrite P1N,P2N. reflexivity.
- exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
- exists (negation_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (negation_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_a A n c (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n c (ptree_deg P) alpha P). repeat split; auto.
- exists (loop_a A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  apply (existT _ L2 (eq_sym P2N)).
  rewrite P1N, P2N.
  reflexivity.
- exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  apply (existT _ L2 (eq_sym P2N)).
  admit.
  rewrite P1N, P2N.
  reflexivity.
- exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
- exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
- exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
Qed.

Lemma in_swap {A : Type} :
    forall (a b c : A) (L1 L2 : list A),
        In a (L1 ++ b :: c :: L2) <-> In a (L1 ++ c :: b :: L2).
Proof.
intros a b c L1 L2.
split;
intros IN;
apply in_app_iff;
apply in_app_iff in IN as [INL1 | [[] | [[] | INL2]]];
firstorder.
Qed.

Lemma in_cont {A : Type} :
    forall (a b : A) (L1 L2 : list A),
        In a (L1 ++ b :: b :: L2) <-> In a (L1 ++ b :: L2).
Proof.
intros a b L1 L2.
split;
intros IN;
apply in_app_iff;
try apply in_app_iff in IN as [INL1 | [[] | [[] | INL2]]];
try apply in_app_iff in IN as [INL1 | [[] | INL2]];
firstorder.
Qed.

Lemma provable_theorem :
    forall (A : formula) (d : nat) (alpha : ord),
        PA_cyclic_theorem A d alpha -> provable A d alpha.
Proof.
intros A d alpha T.
apply true_theorem in T. 
destruct T as [L [TS TAX]].
unfold provable.
induction TS;
try destruct (IHTS TAX) as [P [[[PF [PSV PAX]] PD] PO]];
try destruct (IHTS1 (fun B INB => TAX B (proj2 (in_app_iff _ _ _) (or_introl INB)))) as [P1 [[[P1F [P1SV P1AX]] P1D] P1H]];
try destruct (IHTS2 (fun B INB => TAX B (proj2 (in_app_iff _ _ _) (or_intror INB)))) as [P2 [[[P2F [P2SV P2AX]] P2D] P2H]];
try rewrite PF in PFC;
try rewrite P1F in P1FC;
try rewrite P2F in P2FC;
repeat apply and_bool_prop in PFC as [PFC ?];
repeat apply and_bool_prop in P1FC as [P1FC ?];
repeat apply and_bool_prop in P2FC as [P2FC ?].
- exists (deg_up d' P).
  repeat split; auto. lia.
- exists (ord_up beta P).
  repeat split; auto.
  rewrite <- PO. auto.
- destruct (structural_pre_theorem TS) as [P [[[[PF PSV] PD] PO] PN]].
  exists (leaf_ex n P). repeat split; auto. rewrite PN. apply l. unfold leaves; fold leaves. rewrite PN. apply TAX.
- exists (node A).
  repeat split.
  + intros A' IN. inversion IN.
    * destruct H. apply TAX, or_introl, eq_refl.
    * inversion H.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- pose proof (structural_pre_theorem TS) as [P' [[[[P'F P'SV] P'D] P'O] P'L]].
  exists (weakening_ad A D (ptree_deg P') alpha P'). repeat split; simpl; auto;
  try rewrite P'L.
  + apply FLSub.
  + apply TAX.
- exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
- exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
- exists (negation_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (negation_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_a A n c (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n c (ptree_deg P) alpha P). repeat split; auto.
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_a A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  apply (existT _ L2 (eq_sym P2L)).
  rewrite P1L,P2L.
  apply TAX.
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  apply (existT _ L2 (eq_sym P2L)).
  rewrite P1L,P2L.
  apply TAX.
- exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
- exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
- exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
Qed.

Lemma pre_theorem_structural :
    forall (P : ptree) (PSV : struct_valid P),
        PA_cyclic_pre (ptree_formula P) (ptree_deg P) (ptree_ord P) (leaves P).
Proof.
intros P PSV. induction P.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

2-15 :  try rewrite PF,<-PD,<-PO in IHP;
        pose proof (IHP PSV) as P';
        try rewrite PN in P'.

16-22 : rewrite P1F,<-P1D,<-P1O in IHP1;
        rewrite P2F,<-P2D,<-P2O in IHP2;
        pose proof (IHP1 P1SV) as P1';
        pose proof (IHP2 P2SV) as P2';
        try rewrite <- P2N in P2'.

apply (axiom _).
apply (pre_ex _ PL P').
apply (deg_incr _ _ P' DU).
apply (ord_incr _ _ P' OU NO).
apply (exchange1 P').
apply (exchange2 P').
apply (exchange3 P').
apply (exchange4 P').
apply (contraction1 P').
apply (contraction2 _ P').
apply (negation1 P').
apply (negation2 P').
apply (quantification1 P').
apply (quantification2 P').
apply (weakening _ CPF P').
apply (demorgan1 P1' P2').
apply (demorgan2 P1' P2').
apply (cut1 _ _ P1' P2').
apply (cut2 _ _ P1' P2').
apply (cut3 _ _ _ P1' P2').
apply (loop1 _ _ FREEA P1'). fold leaves. rewrite <- P2N. apply P2'.
apply (loop2 _ _ FREEA P1'). fold leaves. rewrite <- P2N. apply P2'.
Qed.

Lemma theorem_provable' :
    forall (P : ptree),
        valid P ->
            PA_cyclic_theorem (ptree_formula P) (ptree_deg P) (ptree_ord P).
Proof.
intros P [PSV PAX].
induction P.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

2 : unfold leaves in PAX;
    fold leaves in PAX.

3-14 :  try rewrite PF,<-PD,<-PO in IHP;
        pose proof (projT1 (projT2 (true_theorem (IHP PSV PAX)))) as P';
        pose proof (projT2 (projT2 (true_theorem (IHP PSV PAX)))) as PAX'.

16-22 : rewrite P1F, <- P1D, <- P1O in IHP1;
        rewrite P2F, <- P2D, <- P2O in IHP2;
        try pose proof (projT1 (projT2 (true_theorem (IHP1 P1SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB))))))) as P1';
        try pose proof (projT1 (projT2 (true_theorem (IHP2 P2SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB))))))) as P2';
        try pose proof (projT2 (projT2 (true_theorem (IHP1 P1SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB))))))) as AX1';
        try pose proof (projT2 (projT2 (true_theorem (IHP2 P2SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB))))))) as AX2';
        try fold leaves in *.

1 : apply (prune (axiom _) PAX).
1 : apply (IHP PSV (fun A INA => PAX A (proj1 (in_bury A) INA))).
1 : apply (prune (deg_incr _ _ P' DU) PAX').
1 : apply (prune (ord_incr _ _ P' OU NO) PAX').
1 : apply (prune (exchange1 P') PAX').
1 : apply (prune (exchange2 P') PAX').
1 : apply (prune (exchange3 P') PAX').
1 : apply (prune (exchange4 P') PAX').
1 : apply (prune (contraction1 P') PAX').
1 : apply (prune (contraction2 _ P') PAX').
1 : apply (prune (negation1 P') PAX').
1 : apply (prune (negation2 P') PAX').
1 : apply (prune (quantification1 P') PAX').
1 : apply (prune (quantification2 P') PAX').
1 : rewrite <-PF, PD, PO.
    apply (prune (weakening _ CPF (pre_theorem_structural _ PSV)) PAX).
1 : refine (prune (demorgan1 P1' P2') _).
2 : refine (prune (demorgan2 P1' P2') _).
3 : refine (prune (cut1 _ _ P1' P2') _).
4 : refine (prune (cut2 _ _ P1' P2') _).
5 : refine (prune (cut3 _ _ _ P1' P2') _).

1-5 : intros B INB;
      apply in_app_iff in INB as [INB1 | INB2];
      try apply (AX1' _ INB1);
      apply (AX2' _ INB2).

1,2 : pose proof (pre_theorem_structural P1 P1SV) as P1';
      pose proof (pre_theorem_structural P2 P2SV) as P2';
      rewrite P1F, <-P1D, <-P1O in P1';
      rewrite P2F, <-P2D, <-P2O, <- P2N in P2'.

1,2 : unfold leaves in PAX;
      fold leaves in PAX;
      rewrite <- P2N in PAX.

2 : apply (prune (loop2 _ _ FREEA P1' P2') PAX).

1 : apply (prune (loop1 _ _ FREEA P1' P2') PAX).
Qed.

Lemma theorem_provable :
    forall (A : formula) (d : nat) (alpha : ord),
        provable A d alpha ->
            PA_cyclic_theorem A d alpha.
Proof.
intros A d alpha [P [[[PF [PSV PAX]] PD] PO]].
rewrite <- PF, PD, PO.
apply (theorem_provable' _ (PSV, PAX)).
Qed.

Lemma ptree_ord_nf :
    forall (P : ptree),
        valid P ->
            nf (ptree_ord P).
Proof.
intros P PV.
pose proof (theorem_provable' _ PV) as PT.
apply (ord_nf _ PT).
Qed.

Lemma ptree_ord_nf_struct :
    forall (P : ptree),
        struct_valid P ->
            nf (ptree_ord P).
Proof.
intros P PV.
pose proof (pre_theorem_structural _ PV) as PT.
apply (ord_nf_pre _ PT).
Qed.

Lemma ptree_ord_nf_hyp :
    forall (alpha : ord) (P : ptree),
        alpha = ptree_ord P ->
            valid P ->
                nf alpha.
Proof.
intros alpha P EQ PV.
rewrite EQ.
apply ptree_ord_nf, PV.
Qed.

Lemma ptree_ord_nf_struct_hyp :
    forall (alpha : ord) (P : ptree),
        alpha = ptree_ord P ->
            struct_valid P ->
                nf alpha.
Proof.
intros alpha P EQ PV.
rewrite EQ.
apply ptree_ord_nf_struct, PV.
Qed.

Lemma associativity_1 :
    forall (C A B : formula) (d : nat) (alpha : ord),
        provable (lor (lor C A) B) d alpha ->
            provable (lor C (lor A B)) d alpha.
Proof.
intros C A B d alpha [P [[[PF [PSV PA]] PD] PO]].
exists (exchange_ab
          (lor A B) C (ptree_deg P) alpha
          (exchange_cab
              A C B (ptree_deg P) alpha
              (exchange_abd C A B (ptree_deg P) alpha P))).
repeat split; auto.
Qed.

Lemma associativity_2 :
    forall (C A B : formula) (d : nat) (alpha : ord),
        provable (lor C (lor A B)) d alpha ->
            provable (lor (lor C A) B) d alpha.
Proof.
intros C A B d alpha [P [[[PF [PSV PA]] PD] PO]].
exists (exchange_abd
            A C B (ptree_deg P) alpha
            (exchange_cab
                A B C (ptree_deg P) alpha
                (exchange_ab C (lor A B) (ptree_deg P) alpha P))).
repeat split; auto.
Qed.

Lemma provable_closed :
    forall (A : formula) (d : nat) (alpha : ord),
        provable A d alpha ->
            closed A = true.
Proof.
intros A d alpha PA.
apply (theorem_closed _ d alpha), theorem_provable, PA.
Qed.

Lemma provable_closed' :
    forall (P : ptree) (A : formula),
        valid P ->
            ptree_formula P = A ->
                closed A = true.
Proof.
intros P A [PSV PAX] PF.
pose (ptree_deg P) as d.
pose (ptree_ord P) as alpha.
apply (provable_closed _ d alpha).
exists P.
repeat split; auto.
Qed.

Lemma struct_non_empty_nodes : 
    forall (P : ptree),
        struct_valid P ->
            leaves P <> [].
Proof.
induction P;
intros PSV;
unfold leaves;
fold leaves.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

all : try apply (IHP PSV).

1 : discriminate.

all : intros FAL;
      try case (closed c) eqn:CC;
      try case (closed (univ n a)) eqn:CuA;
      try apply app_eq_nil in FAL as [FAL1 FAL2];
      try inversion FAL2;
      try apply (IHP1 P1SV FAL1);
      try apply (IHP1 P1SV FAL2);
      try apply (IHP2 P1SV FAL2);
      try apply (IHP PSV ((proj1 bury_nil) FAL)).
Qed.

Lemma struct_node_sum_less_l {L : list formula} {P : ptree} :
    struct_valid P ->
        length L < length (L ++ (leaves P)).
Proof.
intros PSV.
rewrite app_length.
case (leaves P) eqn:L2.
- destruct (struct_non_empty_nodes _ PSV L2).
- unfold length;
  fold (@length formula).
  lia.
Qed.

Lemma struct_node_sum_less_r {L : list formula} {P : ptree} :
    struct_valid P ->
        length L < length ((leaves P) ++ L).
Proof.
intros PSV.
rewrite app_length.
case (leaves P) eqn:L1.
- destruct (struct_non_empty_nodes _ PSV L1).
- unfold length;
  fold (@length formula).
  lia.
Qed.

(*Could keep track of height, as exact increase of 1 if required*)

(*
Theorem macro_weakening :
    forall (P : ptree) (B C : formula),
        closed C = true ->
            struct_valid P ->
                In B (leaves P) ->
                    {Q : ptree & (In (lor C B) (leaves Q) * (ptree_formula Q = lor C (ptree_formula P)) * (ptree_deg Q = ptree_deg P) * struct_valid Q)%type}.
Proof.
intros P.
induction P;
intros B C CB PSV INB.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

2-14 : destruct (IHP B C CB PSV INB) as [Q [[[INQ QF] QD] QSV]].

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

15-21 : unfold leaves in INB; fold leaves in INB;
        apply (@in_app_bor _ form_eq_dec) in INB as [INB1 | INB2];
        try destruct (IHP1 B C CB P1SV INB1) as [Q1 [[[INQ1 Q1F] Q1D] Q1SV]];
        try destruct (IHP1 B C CB P1SV INB2) as [Q1 [[[INQ1 Q1F] Q1D] Q1SV]];
        try destruct (IHP2 B C CB P2SV INB1) as [Q2 [[[INQ2 Q2F] Q2D] Q2SV]];
        try destruct (IHP2 B C CB P2SV INB2) as [Q2 [[[INQ2 Q2F] Q2D] Q2SV]].

1 : exists (node (lor C a)).
    repeat split.
    unfold leaves in *.
    inversion INB as [EQ | FAL].
    destruct EQ.
    apply or_introl, eq_refl.
    inversion FAL.

1 : exists (deg_up d' Q).

2 : exists Q.

3 : exists (exchange_ab (lor b a) C d (ptree_ord Q)
            (exchange_abd a b C d (ptree_ord Q)
            (exchange_ab C (lor a b) d (ptree_ord Q) Q))).

4 : exists (exchange_ab (lor (lor c b) a) C d (ptree_ord Q)
            (exchange_cabd c a b C d (ptree_ord Q)
            (exchange_ab C (lor (lor c a) b) d (ptree_ord Q) Q))).

5 : exists (exchange_ab (lor (lor b a) d) C d0 (ptree_ord Q)
            (exchange_abd d (lor b a) C d0 (ptree_ord Q)
            (exchange_cab d C (lor b a) d0 (ptree_ord Q)
            (exchange_ab (lor b a) (lor d C) d0 (ptree_ord Q)
            (exchange_abd a b (lor d C) d0 (ptree_ord Q)
            (exchange_ab (lor d C) (lor a b) d0 (ptree_ord Q)
            (exchange_cab d (lor a b) C d0 (ptree_ord Q)
            (exchange_abd (lor a b) d C d0 (ptree_ord Q)
            (exchange_ab C (lor (lor a b) d) d0 (ptree_ord Q) Q))))))))).

6 : exists (exchange_ab (lor (lor (lor c b) a) d) C d0 (ptree_ord Q)
            (exchange_abd d (lor (lor c b) a) C d0 (ptree_ord Q)
            (exchange_cab d C (lor (lor c b) a) d0 (ptree_ord Q)
            (exchange_ab (lor (lor c b) a) (lor d C) d0 (ptree_ord Q)
                (exchange_cabd c a b (lor d C) d0 (ptree_ord Q)
            (exchange_ab (lor d C) (lor (lor c a) b) d0 (ptree_ord Q)
            (exchange_cab d (lor (lor c a) b) C d0 (ptree_ord Q)
            (exchange_abd (lor (lor c a) b) d C d0 (ptree_ord Q)
            (exchange_ab C (lor (lor (lor c a) b) d) d0 (ptree_ord Q) Q))))))))).

7 : exists (exchange_ab a C d (ptree_ord Q)
            (contraction_ad a C d (ptree_ord Q)
            (exchange_ab C (lor a a) d (ptree_ord Q) Q))).

8 : exists (exchange_ab (lor a d) C d0 (ptree_ord Q)
            (exchange_abd d a C d0 (ptree_ord Q)
            (exchange_cab d C a d0 (ptree_ord Q)
            (exchange_ab a (lor d C) d0 (ptree_ord Q)
                (contraction_ad a (lor d C) d0 (ptree_ord Q)
            (exchange_ab (lor d C) (lor a a ) d0 (ptree_ord Q)
            (exchange_cab d (lor a a) C d0 (ptree_ord Q)
            (exchange_abd (lor a a) d C d0 (ptree_ord Q)
            (exchange_ab C (lor (lor a a) d) d0 (ptree_ord Q) Q))))))))).

9 : exists (exchange_ab (neg (neg a)) C d (ord_succ (ptree_ord Q))
            (negation_ad a C d (ptree_ord Q)
            (exchange_ab C a d (ptree_ord Q) Q))).

10 : exists (exchange_ab (lor (neg (neg a)) d) C d0 (ord_succ (ptree_ord Q))
            (exchange_abd d (neg (neg a)) C d0 (ord_succ (ptree_ord Q))
            (exchange_cab d C (neg (neg a)) d0 (ord_succ (ptree_ord Q))
            (exchange_ab (neg (neg a)) (lor d C) d0 (ord_succ (ptree_ord Q))
                (negation_ad a (lor d C) d0 (ptree_ord Q)
            (exchange_ab (lor d C) a d0 (ptree_ord Q)
            (exchange_cab d a C d0 (ptree_ord Q)
            (exchange_abd a d C d0 (ptree_ord Q)
            (exchange_ab C (lor a d) d0 (ptree_ord Q) Q))))))))).

11 : exists (exchange_ab (neg (univ m a)) C d (ord_succ (ptree_ord Q))
            (quantification_ad a C m t d (ptree_ord Q)
            (exchange_ab C (neg (substitution a m (projT1 t))) d (ptree_ord Q) Q))).

12 : exists (exchange_ab (lor (neg (univ m a)) d) C d0 (ord_succ (ptree_ord Q))
            (exchange_abd d (neg (univ m a)) C d0 (ord_succ (ptree_ord Q))
            (exchange_cab d C (neg (univ m a)) d0 (ord_succ (ptree_ord Q))
            (exchange_ab (neg (univ m a)) (lor d C) d0 (ord_succ (ptree_ord Q))
                (quantification_ad a (lor d C) m t d0 (ptree_ord Q)
            (exchange_ab (lor d C) (neg (substitution a m (projT1 t))) d0 (ptree_ord Q)
            (exchange_cab d (neg (substitution a m (projT1 t))) C d0 (ptree_ord Q)
            (exchange_abd (neg (substitution a m (projT1 t))) d C d0 (ptree_ord Q)
            (exchange_ab C (lor (neg (substitution a m (projT1 t))) d) d0 (ptree_ord Q) Q))))))))).

13 : exists (exchange_ab (lor a d) C d0 (ord_succ (ptree_ord Q))
            (exchange_abd d a C d0 (ord_succ (ptree_ord Q))
            (exchange_cab d C a d0 (ord_succ (ptree_ord Q))
            (exchange_ab a (lor d C) d0 (ord_succ (ptree_ord Q))
                (weakening_ad a (lor d C) d0 (ptree_ord Q)
            (exchange_ab C d d0 (ptree_ord Q) Q)))))).

14 : exists (exchange_ab (neg (lor a b)) C (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
            (demorgan_abd a b C d1 d2 (ptree_ord Q1) (ord_succ alpha2)
                (exchange_ab C (neg a) d1 (ptree_ord Q1) Q1)
                (exchange_ab C (neg b) d2 (ord_succ alpha2)
                    (weakening_ad C (neg b) d2 alpha2 P2)))).

15 : exists (exchange_ab (neg (lor a b)) C (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
            (demorgan_abd a b C d1 d2 (ord_succ alpha1) (ptree_ord Q2)
                (exchange_ab C (neg a) d1 (ord_succ alpha1)
                    (weakening_ad C (neg a) d1 alpha1 P1))
                (exchange_ab C (neg b) d2 (ptree_ord Q2) Q2))).

16 : exists (exchange_ab (lor (neg (lor a b)) d) C (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
            (exchange_abd d (neg (lor a b)) C (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
            (exchange_cab d C (neg (lor a b)) (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
            (exchange_ab (neg (lor a b)) (lor d C) (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
                (demorgan_abd a b (lor d C) d1 d2 (ptree_ord Q1) (ord_succ alpha2)
                    (exchange_ab (lor d C) (neg a) d1 (ptree_ord Q1)
                        (exchange_cab d (neg a) C d1 (ptree_ord Q1)
                        (exchange_abd (neg a) d C d1 (ptree_ord Q1)
                        (exchange_ab C (lor (neg a) d) d1 (ptree_ord Q1) Q1))))
                    (exchange_ab (lor d C) (neg b) d2 (ord_succ alpha2)
                        (exchange_cab d (neg b) C d2 (ord_succ alpha2)
                        (exchange_abd (neg b) d C d2 (ord_succ alpha2)
                        (exchange_ab C (lor (neg b) d) d2 (ord_succ alpha2)
                        (weakening_ad C (lor (neg b) d) d2 alpha2 P2)))))))))).

17 : exists (exchange_ab (lor (neg (lor a b)) d) C (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
            (exchange_abd d (neg (lor a b)) C (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
            (exchange_cab d C (neg (lor a b)) (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
            (exchange_ab (neg (lor a b)) (lor d C) (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
                (demorgan_abd a b (lor d C) d1 d2 (ord_succ alpha1) (ptree_ord Q2)
                    (exchange_ab (lor d C) (neg a) d1 (ord_succ alpha1)
                        (exchange_cab d (neg a) C d1 (ord_succ alpha1)
                        (exchange_abd (neg a) d C d1 (ord_succ alpha1)
                        (exchange_ab C (lor (neg a) d) d1 (ord_succ alpha1)
                        (weakening_ad C (lor (neg a) d) d1 alpha1 P1)))))
                    (exchange_ab (lor d C) (neg b) d2 (ptree_ord Q2)
                        (exchange_cab d (neg b) C d2 (ptree_ord Q2)
                        ((exchange_abd (neg b) d C d2 (ptree_ord Q2)
                        (exchange_ab C (lor (neg b) d) d2 (ptree_ord Q2) Q2)))))))))).

18 : exists (cut_ca (lor C c) a d1 d2 (ptree_ord Q1) alpha2
                (exchange_abd c C a d1 (ptree_ord Q1)
                    (exchange_cab c a C d1 (ptree_ord Q1)
                    (exchange_ab C (lor c a) d1 (ptree_ord Q1) Q1)))
                P2).

19 : exists (exchange_ab c C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
                (cut_cad c a C d1 d2 alpha1 (ptree_ord Q2)
                    P1
                    (exchange_ab C (neg a) d2 (ptree_ord Q2) Q2))).

20 : exists (cut_cad C a d d1 d2 (ptree_ord Q1) alpha2 Q1 P2).

21 : exists (exchange_ab d C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_succ (ord_max alpha1 (ptree_ord Q2))))
                (cut_ad a (lor d C) d1 d2 alpha1 (ptree_ord Q2)
                    P1
                    (exchange_ab (lor d C) (neg a) d2 (ptree_ord Q2)
                        (exchange_cab d (neg a) C d2 (ptree_ord Q2)
                        (exchange_abd (neg a) d C d2 (ptree_ord Q2)
                        (exchange_ab C (lor (neg a) d) d2 (ptree_ord Q2) Q2)))))).

22 : exists (exchange_ab (lor c d) C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max (ptree_ord Q1) alpha2))
            (exchange_cab c C d (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max (ptree_ord Q1) alpha2))
            (exchange_abd C c d (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max (ptree_ord Q1) alpha2))
                (cut_cad (lor C c) a d d1 d2 (ptree_ord Q1) alpha2
                    (exchange_abd c C a d1 (ptree_ord Q1)
                        (exchange_cab c a C d1 (ptree_ord Q1)
                        (exchange_ab C (lor c a) d1 (ptree_ord Q1) Q1)))
                    P2)))).

23 : exists (exchange_ab (lor c d) C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
            (exchange_abd d c C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
            (exchange_cab d C c (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
            (exchange_ab c (lor d C) (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
                (cut_cad c a (lor d C) d1 d2 alpha1 (ptree_ord Q2)
                    P1
                    (exchange_ab (lor d C) (neg a) d2 (ptree_ord Q2)
                        (exchange_cab d (neg a) C d2 (ptree_ord Q2)
                        (exchange_abd (neg a) d C d2 (ptree_ord Q2)
                        (exchange_ab C (lor (neg a) d) d2 (ptree_ord Q2) Q2))))))))).

24 : exists P1.

25 : exists (loop_ca C a n d1 d2 (ptree_ord Q1) alpha2 Q1 P2).

26 : exists P1.

27 : exists (exchange_ab (lor c (univ n a)) C (max d1 d2) (ord_succ (ord_add (ptree_ord Q1) (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero))))
            (exchange_cab c C (univ n a) (max d1 d2) (ord_succ (ord_add (ptree_ord Q1) (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero))))
                (loop_ca (lor c C) a n d1 d2 (ptree_ord Q1) alpha2
                    (exchange_cab c (substitution a n zero) C d1 (ptree_ord Q1)
                        (exchange_ab C (lor c (substitution a n zero)) d1 (ptree_ord Q1) Q1))
                    P2))).
(*
(exchange_ab (lor d C) (neg a) d1 (ptree_ord Q1) (exchange_cab d (neg a) C d1 (ptree_ord Q1) ((exchange_abd (neg a) d C d1 (ptree_ord Q1) (exchange_ab C (lor (neg a)) d) d1 (ptree_ord Q1) Q1))))
*)

26 : admit.

24 : admit.


all : repeat split;
      try apply INQ;
      try apply QF;
      try apply Q1F;
      try apply Q2F;
      try apply QD;
      try apply Q1D;
      try apply Q2D;
      try apply QO;
      try apply Q1O;
      try apply Q2O;
      try apply QSV;
      try apply Q1SV;
      try apply Q2SV;
      try rewrite QO;
      try rewrite Q1O;
      try rewrite Q2O;
      try apply OU;
      try apply NO;
      try rewrite QD;
      try rewrite Q1D;
      try rewrite Q2D;
      try apply DU;
      try apply PF;
      try apply P1F;
      try apply P2F;
      try rewrite <- PF;
      try rewrite <- P1F;
      try rewrite <- P2F;
      try apply QF;
      try apply Q1F;
      try apply Q2F;
      try apply PD;
      try apply P1D;
      try apply P2D;
      try apply PO;
      try apply P1O;
      try apply P2O;
      try apply PSV;
      try apply P1SV;
      try apply P2SV;
      try reflexivity;
      unfold leaves;
      fold leaves;
      try apply in_or_app;
      try apply (or_introl INQ1);
      try apply (or_intror INQ1);
      try apply (or_intror INQ2);
      try rewrite (closed_free_list _ CB);
      try apply INA;
      try apply incl_nil_l.

      rewrite Q2F.
      rewrite P1F.
      rewrite P2F.
      reflexivity.

all :      simpl.

Qed.

*)

(*
Master destruct tactic.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)
*)