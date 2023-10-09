From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
(*From Cyclic_PA.Logic Require Import substitute.*)
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep_dec.


Inductive ptree : Type :=
| bot : ptree

| pred : forall {n : nat} (vec : nvec n) (pn : predicate vec), pure_predicate pn = true -> ptree

| equal : forall (v1 v2 : ivar), ptree


| loop_head : forall (OC : constraint) (gamma delta : list formula) (P_Target : ptree), ptree

(*| deg_up : forall (OC : constraint) (gamma delta : list formula) (alpha beta : ordinal) (LT : ord_lt alpha beta) (P' : ptree), ptree *)

| con_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (v1 v2 : ivar) {alpha : ordinal} (P' : ptree), ptree

| con_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (P' : ptree), ptree

| refl : forall {OC : constraint} {gamma delta : list formula} (v : ivar) {alpha : ordinal} (P' : ptree), ptree


| ex_l : forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} (P' : ptree), ptree

| ex_r : forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} (P' : ptree), ptree


| wkn : forall {OC : constraint} (gamma delta sigma pi : list formula) {alpha : ordinal} (P' : ptree), ptree

| rst : forall {OC : constraint} {gamma delta : list formula} (kappa : ovar) {alpha : ordinal} (P' : ptree), ptree


| ug_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (v : ivar) {alpha : ordinal} (P' : ptree), ptree

| ug_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (v : ivar) {alpha : ordinal} (P' : ptree), ptree

| bnd_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (lambda kappa : ovar) {alpha : ordinal} (P' : ptree), ptree

| bnd_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (lambda kappa : ovar) {alpha : ordinal} (P' : ptree), ptree


| imp_l : forall {OC : constraint} {gamma delta : list formula} (phi psi : formula) {alpha1 alpha2 : ordinal} (P1 P2 : ptree), ptree

| imp_r : forall {OC : constraint} {gamma delta : list formula} (phi psi : formula) {alpha : ordinal} (P' : ptree), ptree


| cut : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha1 alpha2 : ordinal} (P1 P2 : ptree), ptree.

Definition ptree_left (P : ptree) : list formula :=
match P with
| bot => [fal]

| pred vec pn pure => [prd pn pure]

| equal v1 v2 => [equ v1 v2]

| loop_head OC gamma delta P_Target => gamma

| @con_l OC gamma delta phi v1 v2 alpha P' => (equ v1 v2) :: phi :: gamma

| @con_r OC gamma delta phi alpha P' => gamma

| @refl OC gamma delta v alpha P' => gamma


| @ex_l OC gamma delta n alpha P' => bury gamma n

| @ex_r OC gamma delta n alpha P' => gamma


| @wkn OC gamma delta sigma pi alpha P' => gamma ++ sigma

| @rst OC gamma delta kappa alpha P' => gamma

| @ug_l OC gamma delta phi v alpha P' => (univ v phi) :: gamma

| @ug_r OC gamma delta phi v alpha P' => gamma

| @bnd_l OC gamma delta phi lambda kappa alpha P' => (bnd lambda kappa phi) :: gamma

| @bnd_r OC gamma delta phi lambda kappa alpha P' => gamma


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => (imp phi psi) :: gamma

| @imp_r OC gamma delta phi psi alpha P' => gamma


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => gamma
end.

Definition ptree_right (P : ptree) : list formula :=
match P with
| bot => []

| pred vec pn pure => [prd pn pure]

| equal v1 v2 => [equ v1 v2]

| loop_head OC gamma delta P_Target => delta

| @con_l OC gamma delta phi v1 v2 alpha P' => delta

| @con_r OC gamma delta phi alpha P' => phi :: delta

| @refl OC gamma delta v alpha P' => delta


| @ex_l OC gamma delta n alpha P' => delta

| @ex_r OC gamma delta n alpha P' => bury delta n


| @wkn OC gamma delta sigma pi alpha P' => delta ++ pi

| @rst OC gamma delta kappa alpha P' => delta

| @ug_l OC gamma delta phi v alpha P' => delta

| @ug_r OC gamma delta phi v alpha P' => (univ v phi) :: delta

| @bnd_l OC gamma delta phi lambda kappa alpha P' => delta

| @bnd_r OC gamma delta phi lambda kappa alpha P' => (bnd lambda kappa phi) :: delta


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => delta

| @imp_r OC gamma delta phi psi alpha P' => (imp phi psi) :: delta


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => delta
end.

Definition ptree_constraint (P : ptree) : constraint :=
match P with
| bot => empty

| pred vec pn pure => empty

| equal v1 v2 => empty

| loop_head OC gamma delta P_Target => OC

| @con_l OC gamma delta phi v1 v2 alpha P' => OC

| @con_r OC gamma delta phi alpha P' => OC

| @refl OC gamma delta v alpha P' => OC


| @ex_l OC gamma delta n alpha P' => OC

| @ex_r OC gamma delta n alpha P' => OC


| @wkn OC gamma delta sigma pi alpha P' => OC

| @rst OC gamma delta kappa alpha P' => OC

| @ug_l OC gamma delta phi v alpha P' => OC

| @ug_r OC gamma delta phi v alpha P' => OC

| @bnd_l OC gamma delta phi lambda kappa alpha P' => OC

| @bnd_r OC gamma delta phi lambda kappa alpha P' => OC


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => OC

| @imp_r OC gamma delta phi psi alpha P' => OC


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => OC
end.

Definition ptree_deg (P : ptree) : ordinal :=
match P with
| bot => cast Zero

| pred vec pn pure => cast Zero

| equal v1 v2 => cast Zero

| loop_head OC1 OC2 gamma delta => cast Zero

| @con_l OC gamma delta phi v1 v2 alpha P' => alpha

| @con_r OC gamma delta phi alpha P' => alpha

| @refl OC gamma delta v alpha P' => alpha


| @ex_l OC gamma delta n alpha P' => alpha

| @ex_r OC gamma delta n alpha P' => alpha


| @wkn OC gamma delta sigma pi alpha P' => alpha

| @rst OC gamma delta L alpha P' => alpha

| @ug_l OC gamma delta phi v alpha P' => alpha

| @ug_r OC gamma delta phi v alpha P' => alpha

| @bnd_l OC gamma delta phi lambda kappa alpha P' => alpha

| @bnd_r OC gamma delta phi lambda kappa alpha P' => alpha


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => omax alpha1 alpha2

| @imp_r OC gamma delta phi psi alpha P' => alpha


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))
end.

Lemma ptree_eq_dec : forall (P1 P2 : ptree), {P1 = P2} + {P1 <> P2}.
Proof.
induction P1;
destruct P2.

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

2 : { try destruct (nat_eq_dec n n0) as [EQN | NEN];
      subst;
      try destruct (nvec_eq_dec vec vec0) as [EQVC | NEVC];
      subst;
      try destruct (prd_eq_dec pn pn0) as [EQP | NEP];
      subst.
      - rewrite (proof_irrelevance _ e e0). 
        apply (left (eq_refl)).
      - right.
        intros FAL.
        inversion FAL as [FAL'].
        repeat apply inj_pair2 in FAL'.
        apply NEP, FAL'.
      - right.
        intros FAL.
        inversion FAL as [[FAL' FAL'']].
        repeat apply inj_pair2 in FAL'.
        apply NEVC, FAL'.
      - right.
        intros FAL.
        inversion FAL as [[FAL' FAL'' FAL''']].
        apply NEN, FAL'. }

all : try destruct (nat_eq_dec n n0) as [EQN | NEN];
      try destruct (IHP1 P2) as [EQ | NE];
			try destruct (IHP1_1 P2_1) as [EQ1 | NE1];
      try destruct (IHP1_2 P2_2) as [EQ2 | NE2];
      try destruct (constraint_eq_dec OC OC0) as [EQO | NEO];
			try destruct (nat_eq_dec v v0) as [EQV | NEV];
			try destruct (nat_eq_dec v1 v0) as [EQV1 | NEV1];
			try destruct (nat_eq_dec v2 v3) as [EQV2 | NEV2];
      try destruct (list_eq_dec form_eq_dec gamma gamma0) as [EQG | NEG];
      try destruct (list_eq_dec form_eq_dec delta delta0) as [EQD | NED];
			try destruct (list_eq_dec form_eq_dec pi pi0) as [EQPI | NEPI];
			try destruct (list_eq_dec form_eq_dec sigma sigma0) as [EQS | NES];
      try destruct (form_eq_dec phi phi0) as [EQP1 | NEP1];
			try destruct (form_eq_dec psi psi0) as [EQP2 | NEP2];
			try destruct (ordinal_eq_dec alpha alpha0) as [EQA | NEA];
      try destruct (ordinal_eq_dec alpha1 alpha0) as [EQA1 | NEA1];
      try destruct (ordinal_eq_dec alpha2 alpha3) as [EQA2 | NEA2];
			try destruct (nat_eq_dec kappa kappa0) as [EQK | NEK];
      try destruct (nat_eq_dec lambda lambda0) as [EQL | NEL];
      subst;
			try apply (left (eq_refl));
      right;
      intros FAL;
      inversion FAL as [FAL'];
      try contradiction.
Qed.

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

| pred vec pn pure => []

| equal v1 v2 => []

| loop_head OC gamma delta P_Target => [P]

| con_l phi v1 v2 P' => leaves P'

| con_r phi P' => leaves P'

| refl v P' => leaves P'


| ex_l n P' => leaves P'

| ex_r n P' => leaves P'


| wkn gamma delta sigma pi P' => leaves P'

| rst kappa P' => leaves P'

| ug_l phi v P' => leaves P'

| ug_r phi v P' => leaves P'

| bnd_l phi lambda kappa P' => leaves P'

| bnd_r phi lambda kappa P' => leaves P'


| imp_l phi psi P1 P2 => leaves P1 ++ leaves P2

| imp_r phi psi P' => leaves P'


| cut phi P1 P2 => leaves P1 ++ leaves P2
end.

Definition path_marker := list bool.

Fixpoint path_fit (P : ptree) (M : path_marker) : list states :=
match P, M with
| bot, [true] => [ptree_state P]

| pred vec pn pure, [true] => [ptree_state P]

| equal v1 v2, [true] => [ptree_state P]

| loop_head OC gamma delta P_Target, true :: M' => (ptree_state P) :: path_fit P_Target M'

| con_l phi v1 v2 P', true :: M' => (ptree_state P) :: path_fit P' M'

| con_r phi P', true :: M' => (ptree_state P) :: path_fit P' M'

| refl v P', true :: M' => (ptree_state P) :: path_fit P' M'


| ex_l n P', true :: M' => (ptree_state P) :: path_fit P' M'

| ex_r n P', true :: M' => (ptree_state P) :: path_fit P' M'


| wkn gamma delta sigma pi P', true :: M' => (ptree_state P) :: path_fit P' M'

| rst kappa P', true :: M' => (ptree_state P) :: path_fit P' M'

| ug_l phi v P', true :: M' => (ptree_state P) :: path_fit P' M'

| ug_r phi v P', true :: M' => (ptree_state P) :: path_fit P' M'

| bnd_l phi lambda kappa P', true :: M' => (ptree_state P) :: path_fit P' M'

| bnd_r phi lambda kappa P', true :: M' => (ptree_state P) :: path_fit P' M'


| imp_l phi psi P1 P2, false :: M' => (ptree_state P) :: path_fit P1 M'

| imp_l phi psi P1 P2, true :: M' => (ptree_state P) :: path_fit P2 M'

| imp_r phi psi P', true :: M' => (ptree_state P) :: path_fit P' M'


| cut phi P1 P2, false :: M' => (ptree_state P) :: path_fit P1 M'

| cut phi P1 P2, true :: M' => (ptree_state P) :: path_fit P2 M'

| _ , _ => []
end.

Definition applicable (OC : constraint) (gamma delta : list formula) : Prop := (incl (flat_map vars_in gamma) (OC_list OC)) * (incl (flat_map vars_in delta) (OC_list OC)).

Fixpoint struct_valid (P : ptree) : Prop :=
match P with
| bot => true = true

| pred vec P pure => true = true

| equal v1 v2 => true = true

| loop_head OC gamma delta P_Target => (struct_valid P_Target) * applicable OC gamma delta * applicable (ptree_constraint P_Target) gamma delta * inhabited {sig : ovar -> ovar & coherent sig OC (ptree_constraint P_Target) /\ (incl (map (fun lambda => sig_subst lambda sig) (ptree_left P_Target)) gamma) /\ (incl (map (fun lambda => sig_subst lambda sig) (ptree_right P_Target)) delta)} * (In (loop_head OC gamma delta bot) (leaves P_Target))

| @con_l OC gamma delta phi v1 v2 alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = (equ v1 v2) :: phi :: (substitution phi v1 v2) :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| @con_r OC gamma delta phi alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = phi :: phi :: delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| @refl OC gamma delta v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = equ v v :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)


| @ex_l OC gamma delta n alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| @ex_r OC gamma delta n alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)


| @wkn OC gamma delta sigma pi alpha P' => struct_valid P' * applicable OC (gamma ++ sigma) (delta ++ pi) * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| @rst OC gamma delta kappa alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (~ In kappa (flat_map vars_in gamma)) * (~ In kappa (flat_map vars_in delta)) * {SUB : (OC_elt OC kappa) & ptree_constraint P' = restriction OC (children OC kappa) (children_subset OC kappa)} * (ptree_deg P' = alpha)

| @ug_l OC gamma delta phi v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| @ug_r OC gamma delta phi v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = phi :: delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| @bnd_l OC gamma delta phi lambda kappa alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (OC_rel OC lambda kappa = true) * (ptree_deg P' = alpha)

| @bnd_r OC gamma delta phi lambda kappa alpha P' => struct_valid P' * applicable OC gamma (phi :: delta) * (ptree_left P' = gamma) * (ptree_right P' = phi :: delta) * {NEW : ~ OC_elt OC lambda & {KIN : OC_elt OC kappa & ptree_constraint P' = add_fresh_child OC lambda kappa NEW KIN}} * (~ In lambda (flat_map vars_in gamma) /\ ~ In lambda (flat_map vars_in (phi :: delta))) * (ptree_deg P' = alpha)


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => struct_valid P1 * struct_valid P2 * applicable OC gamma delta * (ptree_left P1 = psi :: gamma) * (ptree_right P1 = delta) * (ptree_constraint P1 = OC) * (ptree_left P2 = gamma) * (ptree_right P2 = phi :: delta) * (ptree_constraint P2 = OC) * (ptree_deg P1 = alpha1) * (ptree_deg P2 = alpha2)

| @imp_r OC gamma delta phi psi alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = psi :: delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => struct_valid P1 * struct_valid P2 * applicable OC gamma delta * (ptree_left P1 = gamma) * (ptree_right P1 = phi :: delta) * (ptree_constraint P1 = OC) * (ptree_left P2 = phi :: gamma) * (ptree_right P2 = delta) * (ptree_constraint P2 = OC) * (ptree_deg P1 = alpha1) * (ptree_deg P2 = alpha2)
end.

(*
Fixpoint struct_valid (P : ptree) : Type :=
match P with
| bot => true = true

| pred vec P pure => true = true

| equal v1 v2 => true = true

| loop_head OC gamma delta P_Target => (struct_valid P_Target) * applicable OC gamma delta * applicable (ptree_constraint P_Target) gamma delta * {sig : ovar -> ovar & coherent sig OC (ptree_constraint P_Target) /\ (incl (map (fun lambda => sig_subst lambda sig) (ptree_left P_Target)) gamma) /\ (incl (map (fun lambda => sig_subst lambda sig) (ptree_right P_Target)) delta)} * (In (loop_head OC gamma delta bot) (leaves P_Target))

| con_l OC gamma delta phi v1 v2 alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = (equ v1 v2) :: phi :: (substitution phi v1 v2) :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| con_r OC gamma delta phi alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = phi :: phi :: delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| refl OC gamma delta v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = equ v v :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)


| ex_l OC gamma delta n alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| ex_r OC gamma delta n alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)


| wkn OC gamma delta sigma pi alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| rst OC gamma delta kappa alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = delta) * (~ In kappa (flat_map vars_in gamma)) * (~ In kappa (flat_map vars_in delta)) * {SUB : (OC_elt OC kappa) & ptree_constraint P' = restriction OC (children OC kappa) (children_subset OC kappa)} * (ptree_deg P' = alpha)

| ug_l OC gamma delta phi v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| ug_r OC gamma delta phi v alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = phi :: delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)

| bnd_l OC gamma delta phi lambda kappa alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (OC_rel OC lambda kappa = true) * (ptree_deg P' = alpha)

| bnd_r OC gamma delta phi lambda kappa alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = gamma) * (ptree_right P' = phi :: delta) * {NEW : ~ OC_elt OC lambda & {KIN : OC_elt OC kappa & ptree_constraint P' = add_fresh_child OC lambda kappa NEW KIN}} * (ptree_deg P' = alpha)


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => struct_valid P1 * struct_valid P2 * applicable OC gamma delta * (ptree_left P1 = psi :: gamma) * (ptree_right P1 = delta) * (ptree_constraint P1 = OC) * (ptree_left P2 = gamma) * (ptree_right P2 = phi :: delta) * (ptree_constraint P2 = OC) * (ptree_deg P1 = alpha1) * (ptree_deg P2 = alpha2)

| imp_r OC gamma delta phi psi alpha P' => struct_valid P' * applicable OC gamma delta * (ptree_left P' = phi :: gamma) * (ptree_right P' = psi :: delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha)


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => struct_valid P1 * struct_valid P2 * applicable OC gamma delta * (ptree_left P1 = gamma) * (ptree_right P1 = phi :: delta) * (ptree_constraint P1 = OC) * (ptree_left P2 = phi :: gamma) * (ptree_right P2 = delta) * (ptree_constraint P2 = OC) * (ptree_deg P1 = alpha1) * (ptree_deg P2 = alpha2)
end.
*)

Lemma in_leaves_path :
    forall (P PL : ptree),
        In PL (leaves P) ->
            {M : path_marker & {L : list states & path_fit P M = L ++ [ptree_state PL]}}.
Proof.
intros P.
pose (ptree_state P) as PS.
induction P;
intros PL IN.

1-3 : inversion IN.

1 : { apply in_single in IN.
      exists [true].
      exists [].
      unfold path_fit;
      fold path_fit.
      rewrite app_nil_l, IN;
      destruct P;
      reflexivity. }

12,14 : apply (@in_app_bor _ ptree_eq_dec) in IN as [IN1 | IN2];
        try destruct (IHP1 _ IN1) as [M1 [L EQ]];
        try destruct (IHP2 _ IN2) as [M2 [L EQ]];
        try exists (false :: M1);
        try exists (true :: M2);
        try exists (PS :: L);
        unfold path_fit;
        fold path_fit PS;
        try rewrite EQ;
        try reflexivity.

all : destruct (IHP PL IN) as [M [L EQ]];
      exists (true :: M);
      exists (PS :: L);
      unfold path_fit;
      fold path_fit PS;
      rewrite EQ;
      reflexivity.
Defined.

Lemma loop_struct_gives_path :
    forall (OC : constraint) (gamma delta : list formula) (P_Target : ptree),
        struct_valid (loop_head OC gamma delta P_Target) ->
            {M : path_marker & {L : list states & path_fit (loop_head OC gamma delta P_Target) M = (pair OC (pair gamma delta)) :: L ++ [pair OC (pair gamma delta)]}}.
Proof.
intros OC gamma delta P_Target PSV.
destruct PSV as [[[[PSV POC_app] PL_app] Psig] PLoop].
destruct (in_leaves_path _ _ PLoop) as [M [L EQ]].
exists (true :: M).
exists L.
unfold path_fit;
fold path_fit.
rewrite EQ.
reflexivity.
Defined.

Definition leaf_struct :
    forall (P PL : ptree),
        struct_valid P ->
            In PL (leaves P) ->
                struct_valid PL.
Proof.
induction P;
intros PL PSV IN.

1-3 : destruct PSV.
4 : destruct PSV as [[[[PSV POC_app] PL_app] Psig] PLoop].
5-10 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV P_app] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12-13 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
14 : destruct PSV as [[[[[[PSV P_app] PG] PD] POC] POC_rel] PDeg].
15 : destruct PSV as [[[[[[PSV P_app] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] P_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
17 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[[[[[P1SV P2SV] P_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : try inversion IN;
      try apply (IHP _ PSV IN).

1 : { subst.
      unfold struct_valid;
      fold struct_valid.
      apply (pair (pair (pair (pair PSV POC_app) PL_app) Psig) PLoop). }

1 : inversion H.

all : apply (@in_app_bor _ ptree_eq_dec) in IN as [IN1 | IN2];
      try apply (IHP1 _ P1SV IN1);
      apply (IHP2 _ P2SV IN2).
Defined.

Definition leaf_type :
    forall (P PL : ptree),
        struct_valid P ->
            In PL (leaves P) ->
                {PL' : ptree & PL = (loop_head (ptree_constraint PL) (ptree_left PL) (ptree_right PL) PL')}.
Proof.
induction P;
intros PL PSV IN.

1-3 : destruct PSV.
4 : destruct PSV as [[[[PSV POC_app] PL_app] Psig] PLoop].
5-10 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV P_app] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12-13 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
14 : destruct PSV as [[[[[[PSV P_app] PG] PD] POC] POC_rel] PDeg].
15 : destruct PSV as [[[[[[PSV P_app] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] P_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
17 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[[[[[P1SV P2SV] P_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : try inversion IN;
      try apply (IHP _ PSV IN).

1 : { apply in_single in IN.
      subst.
      exists P.
      reflexivity. }

all : apply (@in_app_bor _ ptree_eq_dec) in IN as [IN1 | IN2];
      try apply (IHP1 _ P1SV IN1);
      apply (IHP2 _ P2SV IN2).
Defined.

Definition leaf_stable {OC : constraint} {gamma delta : list formula} {P_Target : ptree} (PSV : struct_valid (loop_head OC gamma delta P_Target)) (kappa : ovar) : Prop :=
    forall (S : states),
        In S (path_fit (loop_head OC gamma delta P_Target) (projT1 (loop_struct_gives_path OC gamma delta P_Target PSV))) ->
            OC_elt (fst S) kappa.

Definition valid (P : ptree) : Type :=
  {PSV : (struct_valid P) & (forall (PL : ptree) (IN : In PL (leaves P)), {kappa : ovar & leaf_stable (eq_rect _ _ (leaf_struct P PL PSV IN) (loop_head _ _ _ _) (projT2 (leaf_type P PL PSV IN))) kappa})}.

Definition P_proves (P : ptree) (OC : constraint) (gamma delta : list formula) (alpha : ordinal) : Type :=
  (valid P) * (ptree_left P = gamma) * (ptree_right P = delta) * (ptree_constraint P = OC) * (applicable OC gamma delta) * (ptree_deg P = alpha).

Definition provable (OC : constraint) (gamma delta : list formula) (alpha : ordinal) : Type :=
  {P : ptree & (P_proves P OC gamma delta alpha)}.

(*
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
*)

(*Lemma ptree_left_non_empty :
    forall (P : ptree),
        struct_valid P ->
          ptree_left P <> [].
Proof.
induction P;
intros PSV.

1-3 : destruct PSV.
4 : destruct PSV as [[[[PSV POC_app] PL_app] [Psig [Psig_Coh [PG PD]]]] PLoop].
5-10 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV P_app] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12-13 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
14 : destruct PSV as [[[[[[PSV P_app] PG] PD] POC] POC_rel] PDeg].
15 : destruct PSV as [[[[[PSV P_app] PG] PD] [NEW [KIN POC]]] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] P_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
17 : destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[[[[[P1SV P2SV] P_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : unfold ptree_left;
      fold ptree_left;
      try discriminate;
      subst;
      try apply (IHP PSV).

- admit.

- admit.

- rewrite bury_nil.
  apply IHP, PSV.

- intros FAL.
  apply app_eq_nil in FAL as [FAL _].
  apply (IHP PSV FAL).

- admit.

- apply IHP1, P1SV.

Admitted.
*)

Lemma struct_OC_app :
    forall (P : ptree),
        struct_valid P ->
            applicable (ptree_constraint P) (ptree_left P) (ptree_right P).
Proof.
induction P;
intros PSV.

1-3 : destruct PSV.
4 : destruct PSV as [[[[PSV [PG_app PD_app]] PL_app] Psig] PLoop].
5-10 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12-13 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
14 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
17 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : repeat split.

1-6 : intros o IN;
      inversion IN.

all : try apply PG_app;
      try apply PD_app;
      try destruct (IHP PSV) as [IHP_left IHP_right];
      try rewrite PG in *;
      try rewrite PD in *;
      subst;
      try apply IHP_left;
      try apply IHP_right;
      intros o.

- refine ((incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ _ _) IHP_left) o).
  intros A [EQ | [EQ | IN]].
  apply (or_introl EQ).
  apply (or_intror (or_introl EQ)).
  apply (or_intror (or_intror (or_intror IN))).

- refine ((incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ _ _) IHP_right) o).
  intros A [EQ | IN].
  apply (or_introl EQ).
  apply (or_intror (or_intror IN)).

- unfold ptree_left;
  fold (ptree_left P).
  rewrite flat_map_bury_incl.
  apply PG_app.

- unfold ptree_right;
  fold (ptree_right P).
  rewrite flat_map_bury_incl.
  apply PD_app.

- intros [EQ | IN];
  subst.
  apply (proj2 (OC_null (ptree_constraint P) _ _ POC_rel)).
  apply in_app_or in IN as [IN1 | IN2].
  apply in_remove in IN1 as [IN1 _].
  apply IHP_left, (in_or_app _ _ _ (or_introl IN1)).
  apply IHP_left, (in_or_app _ _ _ (or_intror IN2)).

- unfold ptree_right.
  intros [EQ | IN];
  subst.
  apply KIN.
  apply in_app_or in IN as [IN1 | IN2].
  apply in_remove in IN1 as [IN1 _].
  apply PD_app, (in_or_app _ _ _ (or_introl IN1)).
  apply PD_app, (in_or_app _ _ _ (or_intror IN2)).

- destruct P2OC.
  intros IN.
  repeat apply in_app_or in IN as [IN | IN];
  fold vars_in in IN.
  + apply (snd (IHP2 P2SV)).
    rewrite P2D.
    apply (in_or_app _ _ _ (or_introl IN)).
  + apply (fst (IHP1 P1SV)).
    rewrite P1G.
    apply (in_or_app _ _ _ (or_introl IN)).
  + apply PG_app, IN.

- intros IN.
  repeat apply in_app_or in IN as [IN | IN];
  fold vars_in in IN.
  + apply (fst (IHP PSV)).
    apply (in_or_app _ _ _ (or_introl IN)).
  + apply (snd (IHP PSV)).
    apply (in_or_app _ _ _ (or_introl IN)).
  + apply PD_app, IN.
Qed.

Lemma ptree_con_l :
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (v1 v2 : ivar) (alpha : ordinal),
        provable OC (equ v1 v2 :: phi :: (substitution phi v1 v2) :: gamma) delta alpha ->
            provable OC (equ v1 v2 :: phi :: gamma) delta alpha.
Proof.
intros OC gamma delta phi v1 v2 alpha [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (con_l phi v1 v2 P) _).
repeat split.
- assert (struct_valid (@con_l (ptree_constraint P) gamma (ptree_right P) phi v1 v2 (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption.
    refine (incl_tran _ PG_app).
    refine (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (equ v1 v2 :: phi :: substitution phi v1 v2 :: gamma) (fun (A : formula) (IN : In A gamma) => (or_intror (or_intror (or_intror IN))))). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- refine (incl_tran _ PG_app).
  refine (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (equ v1 v2 :: phi :: substitution phi v1 v2 :: gamma) (fun (A : formula) => _)).
  intros [EQ1 | [EQ2 | IN]].
  apply (or_introl EQ1).
  apply (or_intror (or_introl EQ2)).
  apply (or_intror (or_intror (or_intror IN))).
- apply PD_app.
Qed.

Lemma ptree_con_r :
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha : ordinal),
        provable OC gamma (phi :: phi :: delta) alpha ->
            provable OC gamma (phi :: delta) alpha.
Proof.
intros OC gamma delta phi alpha [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (con_r phi P) _).
repeat split.
- assert (struct_valid (@con_r (ptree_constraint P) (ptree_left P) delta phi (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption.
    refine (incl_tran _ PD_app).
    refine (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (phi :: phi :: delta) (fun (A : formula) (IN : In A delta) => (or_intror (or_intror IN)))). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- apply PG_app.
- refine (incl_tran _ PD_app).
  refine (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (phi :: phi :: delta) (fun (A : formula) (IN : In A (phi :: delta)) => (or_intror IN))).
Qed.

Lemma ptree_refl : 
    forall (OC : constraint) (gamma delta : list formula) (v : ivar) (alpha : ordinal),
        provable OC (equ v v :: gamma) delta alpha ->
            provable OC gamma delta alpha.
Proof.
intros OC gamma delta v alpha [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (refl v P) _).
repeat split.
- assert (struct_valid (@refl (ptree_constraint P) gamma (ptree_right P) v (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption. }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- refine (incl_tran _ PG_app).
  refine (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (equ v v :: gamma) (fun (A : formula) (IN : In A gamma) => (or_intror IN))).
- apply PD_app.
Qed.

Lemma ptree_ex_l : 
    forall (OC : constraint) (gamma delta : list formula) (n : nat) (alpha : ordinal),
        provable OC gamma delta alpha ->
            provable OC (bury gamma n) delta alpha.
Proof.
intros OC gamma delta n alpha [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (ex_l n P) _).
repeat split.
- assert (struct_valid (@ex_l (ptree_constraint P) (ptree_left P) (ptree_right P) n (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption. }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- refine (incl_tran (fun A => proj1 (flat_map_bury_incl A)) PG_app).
- apply PD_app.
Qed.

Lemma ptree_ex_r : 
    forall (OC : constraint) (gamma delta : list formula) (n : nat) (alpha : ordinal),
        provable OC gamma delta alpha ->
            provable OC gamma (bury delta n) alpha.
Proof.
intros OC gamma delta n alpha [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (ex_r n P) _).
repeat split.
- assert (struct_valid (@ex_r (ptree_constraint P) (ptree_left P) (ptree_right P) n (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption. }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- apply PG_app. 
- refine (incl_tran (fun A => proj1 (flat_map_bury_incl A)) PD_app).
Qed.

Lemma ptree_weaken_left : 
    forall (gamma delta sigma : list formula) (OC : constraint) (alpha: ordinal),
        incl (flat_map vars_in sigma) (OC_list OC) ->
            provable OC gamma delta alpha ->
                provable OC (gamma ++ sigma) delta alpha.
Proof.
intros gamma delta sigma OC alpha SUB [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (wkn (ptree_left P) (ptree_right P) sigma [] P) _).
repeat split.
- assert (struct_valid (@wkn (ptree_constraint P) (ptree_left P) (ptree_right P) sigma [] (ptree_deg P) P)) as PSV'.
  { repeat split.
    apply PSV.
    rewrite flat_map_app.
    apply (incl_app PG_app SUB).
    rewrite app_nil_r.
    apply PD_app. }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' [PG_app' PD_app']]PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- apply app_nil_r.
- rewrite flat_map_app.
  apply (incl_app PG_app SUB).
- apply PD_app.
Qed.

Lemma ptree_weaken_right : 
    forall (gamma delta pi : list formula) (OC : constraint) (alpha: ordinal),
        incl (flat_map vars_in pi) (OC_list OC) ->
            provable OC gamma delta alpha ->
                provable OC gamma (delta ++ pi) alpha.
Proof.
intros gamma delta pi OC alpha SUB [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (wkn (ptree_left P) (ptree_right P) [] pi P) _).
repeat split.
- assert (struct_valid (@wkn (ptree_constraint P) (ptree_left P) (ptree_right P) [] pi (ptree_deg P) P)) as PSV'.
  { repeat split.
    apply PSV.
    rewrite app_nil_r.
    apply PG_app.
    rewrite flat_map_app.
    apply (incl_app PD_app SUB). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' [PG_app' PD_app']]PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- apply app_nil_r.
- apply PG_app.
- rewrite flat_map_app.
  apply (incl_app PD_app SUB).
Qed.

Lemma ptree_reset : 
    forall (gamma delta : list formula) (OC : constraint) (kappa : ovar) (alpha: ordinal),
        ~ In kappa (flat_map vars_in gamma) ->
            ~ In kappa (flat_map vars_in delta) ->
                OC_elt OC kappa ->
                    provable (restriction OC (children OC kappa) (children_subset OC kappa)) gamma delta alpha ->
                        provable OC gamma delta alpha.
Proof.
intros gamma delta OC kappa alpha NING NIND ELT [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (rst kappa P) _).
repeat split.
- assert (struct_valid (@rst OC (ptree_left P) (ptree_right P) kappa (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption.
    apply (incl_tran PG_app (incl_filter _ _)).
    apply (incl_tran PD_app (incl_filter _ _)). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[[[PSV' [PG_app' PD_app']] PG'] PD'] KNING'] KNIND'] [KIN' POC']] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- apply (incl_tran PG_app (incl_filter _ _)).
- apply (incl_tran PD_app (incl_filter _ _)).
Qed.

Lemma ptree_ug_l : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (v : ivar) (alpha : ordinal),
        provable OC (phi :: gamma) delta alpha ->
            provable OC ((univ v phi) :: gamma) delta alpha.
Proof.
intros OC gamma delta phi v alpha [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (ug_l phi v P) _).
repeat split.
- assert (struct_valid (@ug_l (ptree_constraint P) gamma (ptree_right P) phi v (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption.
    refine (incl_tran _ PG_app).
    refine (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (phi :: gamma) (fun (A : formula) (IN : In A gamma) => (or_intror IN))). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- apply PG_app. 
- apply PD_app.
Qed.

Lemma ptree_ug_r : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (v : ivar) (alpha : ordinal),
        provable OC gamma (phi :: delta) alpha ->
            provable OC gamma ((univ v phi) :: delta) alpha.
Proof.
intros OC gamma delta phi v alpha [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (ug_r phi v P) _).
repeat split.
- assert (struct_valid (@ug_r (ptree_constraint P) (ptree_left P) delta phi v (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption.
    refine (incl_tran _ PD_app).
    refine (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (phi :: delta) (fun (A : formula) (IN : In A delta) => (or_intror IN))). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- apply PG_app. 
- apply PD_app.
Qed.

Lemma ptree_bnd_l : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (lambda kappa : ovar) (alpha : ordinal),
        OC_rel OC lambda kappa = true ->
            provable OC (phi :: gamma) delta alpha ->
                provable OC ((bnd lambda kappa phi) :: gamma) delta alpha.
Proof.
intros OC gamma delta phi lambda kappa alpha rel [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (bnd_l phi lambda kappa P) _).
repeat split.
- assert (struct_valid (@bnd_l (ptree_constraint P) gamma (ptree_right P) phi lambda kappa (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption.
    refine (incl_tran _ PG_app).
    refine (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (phi :: gamma) (fun (A : formula) (IN : In A gamma) => (or_intror IN))). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[[PSV' POC_app'] PG'] PD'] POC'] POC_rel] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- intros o IN.
  apply in_app_or in IN as [[IN1 | IN2] | IN3].
  + subst.
    apply (OC_null _ _ _ rel).
  + apply in_remove in IN2 as [IN2 _].
    apply PG_app, in_or_app, or_introl, IN2.
  + apply PG_app, in_or_app, or_intror, IN3.
- apply PD_app.
Qed.

Lemma ptree_bnd_r : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (lambda kappa : ivar) (alpha : ordinal) (NEW : ~ OC_elt OC lambda) (KIN : OC_elt OC kappa),
        ~ In lambda (flat_map vars_in gamma) ->
            ~ In lambda (flat_map vars_in (phi :: delta)) ->
                provable (add_fresh_child OC lambda kappa NEW KIN) gamma (phi :: delta) alpha ->
                    provable OC gamma ((bnd lambda kappa phi) :: delta) alpha.
Proof.
intros OC gamma delta phi lambda kappa alpha NEW KIN NING NIND [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (bnd_r phi lambda kappa P) _).
repeat split.
- assert (struct_valid (@bnd_r OC (ptree_left P) delta phi lambda kappa (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption;
    try refine (existT _ NEW (existT _ KIN POC));
    intros o IN;
    try specialize (PG_app o IN);
    try specialize (PD_app o IN).
    unfold OC_list, add_fresh_child, projT1 in PG_app.
    destruct PG_app as [EQ | PG_app].
    subst.
    contradiction (NING IN).
    apply PG_app.
    destruct PD_app as [EQ | PD_app].
    subst.
    contradiction (NIND IN).
    apply PD_app. }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[[PSV' [PG_app' PD_app']] PG'] PD'] [NEW' [KIN' POC']]] [NING' NIND']] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- intros o IN.
  specialize (PG_app o IN).
  unfold OC_list, add_fresh_child, projT1 in PG_app.
  destruct PG_app as [EQ | PG_app].
  + subst.
    contradiction (NING IN).
  + apply PG_app.
- intros o [EQ | IN].
  + subst.
    apply KIN.
  + apply in_app_or in IN as [IN1 | IN2].
    * apply in_remove in IN1 as [IN1 _].
      specialize (PD_app o (in_or_app _ _ _ (or_introl IN1))).
      unfold OC_list, add_fresh_child, projT1 in PD_app.
      destruct PD_app as [EQ | PD_app].
      --  subst.
          contradiction (NIND (in_or_app _ _ _ (or_introl IN1))).
      --  apply PD_app.
    * specialize (PD_app o (in_or_app _ _ _ (or_intror IN2))).
      unfold OC_list, add_fresh_child, projT1 in PD_app.
      destruct PD_app as [EQ | PD_app].
      --  subst.
          contradiction (NIND (in_or_app _ _ _ (or_intror IN2))).
      --  apply PD_app. 
Qed.

Lemma ptree_imp_l : 
    forall (OC : constraint) (gamma delta : list formula) (phi psi : formula) (alpha1 alpha2 : ordinal),
        provable OC (psi :: gamma) delta alpha1 ->
            provable OC gamma (phi :: delta) alpha2 ->
                provable OC ((imp phi psi) :: gamma) delta (omax alpha1 alpha2).
Proof.
intros OC gamma delta phi psi alpha1 alpha2 [P1 [[[[[[P1SV P1Stab] P1G] P1D] P1OC] [P1G_app P1D_app]] P1Deg]] [P2 [[[[[[P2SV P2Stab] P2G] P2D] P2OC] [P2G_app P2D_app]] P2Deg]].
subst.
refine (existT _ (imp_l phi psi P1 P2) _).
repeat split.
- assert (struct_valid (@imp_l (ptree_constraint P1) (ptree_left P2) (ptree_right P1) phi psi (ptree_deg P1) (ptree_deg P2) P1 P2)) as PSV'.
  { repeat split;
    try assumption. }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[[[[[[P1SV' P2SV'] POC_app] P1G'] P1D'] P1OC'] P2G'] P2D'] P2OC'] PDeg1'] PDeg2'].
  fold leaves.
  rewrite (proof_irrelevance _ P1SV' P1SV).
  rewrite (proof_irrelevance _ P2SV' P2SV).
  intros PL IN.
  destruct in_app_bor as [IN1 | IN2].
  apply P1Stab.
  apply P2Stab.
- intros o IN.
  repeat apply in_app_or in IN as [IN | IN].
  apply P2D_app, (in_or_app _ _ _ (or_introl IN)).
  apply P1G_app, (in_or_app _ _ _ (or_introl IN)).
  apply P2G_app, IN.  
- apply P1D_app.
Qed.

Lemma ptree_imp_r : 
    forall (OC : constraint) (gamma delta : list formula) (phi psi : formula) (alpha : ordinal),
        provable OC (phi :: gamma) (psi :: delta) alpha ->
            provable OC gamma ((imp phi psi) :: delta) alpha.
Proof.
intros OC gamma delta phi psi alpha [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
subst.
refine (existT _ (imp_r phi psi P) _).
repeat split.
- assert (struct_valid (@imp_r (ptree_constraint P) gamma delta phi psi (ptree_deg P) P)) as PSV'.
  { repeat split;
    try assumption.
    refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (phi :: gamma) (fun (A : formula) (IN : In A gamma) => (or_intror IN))) PG_app).
    refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (psi :: delta) (fun (A : formula) (IN : In A delta) => (or_intror IN))) PD_app). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  rewrite (proof_irrelevance _ PSV' PSV).
  apply PStab.
- refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ (phi :: gamma) (fun (A : formula) (IN : In A gamma) => (or_intror IN))) PG_app).
- intros o IN.
  repeat apply in_app_or in IN as [IN | IN].
  apply PG_app, (in_or_app _ _ _ (or_introl IN)).
  apply PD_app, (in_or_app _ _ _ (or_introl IN)).
  apply PD_app, (in_or_app _ _ _ (or_intror IN)).
Qed.

Lemma ptree_cut : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha1 alpha2 : ordinal),
        provable OC gamma (phi :: delta) alpha1 ->
            provable OC (phi :: gamma) delta alpha2 ->
                provable OC gamma delta (omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))).
Proof.
intros OC gamma delta phi alpha1 alpha2 [P1 [[[[[[P1SV P1Stab] P1G] P1D] P1OC] [P1G_app P1D_app]] P1Deg]] [P2 [[[[[[P2SV P2Stab] P2G] P2D] P2OC] [P2G_app P2D_app]] P2Deg]].
subst.
refine (existT _ (cut phi P1 P2) _).
repeat split.
- assert (struct_valid (@cut (ptree_constraint P1) (ptree_left P1) (ptree_right P2) phi (ptree_deg P1) (ptree_deg P2) P1 P2)) as PSV'.
  { repeat split;
    try assumption. }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[[[[[[P1SV' P2SV'] POC_app] P1G'] P1D'] P1OC'] P2G'] P2D'] P2OC'] PDeg1'] PDeg2'].
  fold leaves.
  rewrite (proof_irrelevance _ P1SV' P1SV).
  rewrite (proof_irrelevance _ P2SV' P2SV).
  intros PL IN.
  destruct in_app_bor as [IN1 | IN2].
  apply P1Stab.
  apply P2Stab.
- apply P1G_app.
- apply P2D_app.
Qed.

Lemma commutative_left_aux :
    forall (LN : list nat) (gamma1 gamma2 delta : list formula) (OC : constraint) (alpha: ordinal),
        (set_bury gamma1 LN = gamma2) ->
            provable OC gamma1 delta alpha ->
                provable OC gamma2 delta alpha.
Proof.
induction LN;
intros gamma1 gamma2 delta OC alpha EQ PP.
- unfold set_bury in EQ.
  subst.
  apply PP.
- unfold set_bury in EQ;
  fold @set_bury in EQ.
  apply (IHLN _ _ _ _ _ EQ), ptree_ex_l, PP.
Qed.

Lemma ptree_comm_left :
    forall {gamma1 gamma2 delta : list formula} {OC : constraint} {alpha : ordinal},
        (perm gamma1 gamma2) ->
            provable OC gamma1 delta alpha ->
                provable OC gamma2 delta alpha.
Proof.
intros gamma1 gamma2 delta OC alpha perm.
pose proof (set_bury_eq_perm perm) as [LN EQ].
apply (commutative_left_aux LN _ _ _ _ _ EQ).
Defined.

Lemma ptree_con_l_better :
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha : ordinal),
        provable OC (phi :: phi :: gamma) delta alpha ->
            provable OC (phi :: gamma) delta alpha.
Proof.
intros OC gamma delta phi alpha PP.
apply (ptree_refl _ _ _ 0), ptree_con_l.
rewrite subst_eq_refl, <- (app_nil_r (phi :: phi :: gamma)).
apply (ptree_comm_left perm_head), ptree_weaken_left, PP.
apply incl_nil_l.
Qed.

Lemma prove_dups_left_aux :
    forall (n : nat) (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        length gamma = n ->
            provable OC gamma delta alpha ->
                provable OC (nodup form_eq_dec gamma) delta alpha.
Proof.
induction n;
intros gamma delta OC alpha EQ PP.
- destruct gamma.
  apply PP.
  inversion EQ.
- case (no_dup_dec_cases form_eq_dec gamma) as [NDG | DG].
  + rewrite (nodup_fixed_point _ NDG).
    apply PP.
  + destruct (has_dups_split form_eq_dec DG) as [A [gamma1 [gamma2 [gamma3 EQL]]]].
    subst.
    apply (ptree_comm_left (perm_sym (perm_nodup form_eq_dec double_perm_head))).
    rewrite nodup_double_cons.
    apply IHn, ptree_con_l_better, (ptree_comm_left (double_perm_head)), PP.
    rewrite app_length in EQ.
    unfold length in *;
    fold (@length formula) in *.
    repeat rewrite app_length in *.
    unfold length in EQ;
    fold (@length formula) in EQ.
    repeat rewrite <- plus_n_Sm in EQ.
    lia.
Qed.

Lemma ptree_nodups_left :
    forall (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        provable OC gamma delta alpha ->
            provable OC (nodup form_eq_dec gamma) delta alpha.
Proof.
intros gamma delta OC alpha PP.
apply (prove_dups_left_aux (length gamma) _ _ _ _ eq_refl PP).
Qed.


Lemma prove_extras_left_aux :
    forall (n : nat) (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        length gamma = n ->
            provable OC (nodup form_eq_dec gamma) delta alpha ->
                provable OC gamma delta alpha.
Proof.
induction n;
intros gamma delta OC alpha EQ PP.
- destruct gamma.
  apply PP.
  inversion EQ.
- case (no_dup_dec_cases form_eq_dec gamma) as [NDG | DG].
  + rewrite <- (nodup_fixed_point form_eq_dec NDG).
    apply PP.
  + destruct (has_dups_split form_eq_dec DG) as [A [gamma1 [gamma2 [gamma3 EQL]]]].
    subst.
    destruct (@nodup_split_perm _ form_eq_dec (A :: A :: gamma1 ++ gamma2 ++ gamma3)) as [sigma [PERM SUB]].
    apply (ptree_comm_left (perm_trans _ _ _ (perm_sym PERM) (perm_sym double_perm_head))), ptree_weaken_left, (ptree_comm_left (perm_nodup form_eq_dec double_perm_head)), PP.
    destruct PP as [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
    refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (incl_tran SUB (incl_tran (fun B IN => perm_in form_eq_dec (perm_sym double_perm_head) _ IN) (fun B IN => proj2 (nodup_In _ _ _) IN)))) PG_app).
Qed.

Lemma ptree_redups_left :
    forall (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        provable OC (nodup form_eq_dec gamma) delta alpha ->
            provable OC gamma delta alpha.
Proof.
intros gamma delta OC alpha PP.
apply (prove_extras_left_aux (length gamma) _ _ _ _ eq_refl PP).
Qed.

Lemma ptree_equiv_left :
    forall (gamma1 gamma2 delta : list formula) (OC : constraint) (alpha : ordinal),
        (forall A : formula, In A gamma1 <-> In A gamma2) ->
            provable OC gamma1 delta alpha ->
                provable OC gamma2 delta alpha.
Proof.
intros gamma1 gamma2 delta OC alpha EQUIV PP.
apply ptree_redups_left, (ptree_comm_left (equiv_nodup_perm form_eq_dec EQUIV)), ptree_nodups_left, PP.
Qed.

Lemma commutative_right_aux :
    forall (LN : list nat) (gamma delta1 delta2 : list formula) (OC : constraint) (alpha: ordinal),
        (set_bury delta1 LN = delta2) ->
            provable OC gamma delta1 alpha ->
                provable OC gamma delta2 alpha.
Proof.
induction LN;
intros gamma1 gamma2 delta OC alpha EQ PP.
- unfold set_bury in EQ.
  subst.
  apply PP.
- unfold set_bury in EQ;
  fold @set_bury in EQ.
  apply (IHLN _ _ _ _ _ EQ), ptree_ex_r, PP.
Qed.

Lemma ptree_comm_right :
    forall {gamma delta1 delta2 : list formula} {OC : constraint} {alpha : ordinal},
        (perm delta1 delta2) ->
            provable OC gamma delta1 alpha ->
                provable OC gamma delta2 alpha.
Proof.
intros gamma delta1 delta2 OC alpha perm.
pose proof (set_bury_eq_perm perm) as [LN EQ].
apply (commutative_right_aux LN _ _ _ _ _ EQ).
Defined.

Lemma prove_dups_right_aux :
    forall (n : nat) (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        length delta = n ->
            provable OC gamma delta alpha ->
                provable OC gamma (nodup form_eq_dec delta) alpha.
Proof.
induction n;
intros gamma delta OC alpha EQ PP.
- destruct delta.
  apply PP.
  inversion EQ.
- case (no_dup_dec_cases form_eq_dec delta) as [NDD | DD].
  + rewrite (nodup_fixed_point _ NDD).
    apply PP.
  + destruct (has_dups_split form_eq_dec DD) as [A [delta1 [delta2 [delta3 EQL]]]].
    subst.
    apply (ptree_comm_right (perm_sym (perm_nodup form_eq_dec double_perm_head))).
    rewrite nodup_double_cons.
    apply IHn, ptree_con_r, (ptree_comm_right (double_perm_head)), PP.
    rewrite app_length in EQ.
    unfold length in *;
    fold (@length formula) in *.
    repeat rewrite app_length in *.
    unfold length in EQ;
    fold (@length formula) in EQ.
    repeat rewrite <- plus_n_Sm in EQ.
    lia.
Qed.

Lemma ptree_nodups_right :
    forall (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        provable OC gamma delta alpha ->
            provable OC gamma (nodup form_eq_dec delta) alpha.
Proof.
intros gamma delta OC alpha PP.
apply (prove_dups_right_aux (length delta) _ _ _ _ eq_refl PP).
Qed.

Lemma prove_extras_right_aux :
    forall (n : nat) (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        length delta = n ->
            provable OC gamma (nodup form_eq_dec delta) alpha ->
                provable OC gamma delta alpha.
Proof.
induction n;
intros gamma delta OC alpha EQ PP.
- destruct delta.
  apply PP.
  inversion EQ.
- case (no_dup_dec_cases form_eq_dec delta) as [NDD | DD].
  + rewrite <- (nodup_fixed_point form_eq_dec NDD).
    apply PP.
  + destruct (has_dups_split form_eq_dec DD) as [A [delta1 [delta2 [delta3 EQL]]]].
    subst.
    destruct (@nodup_split_perm _ form_eq_dec (A :: A :: delta1 ++ delta2 ++ delta3)) as [pi [PERM SUB]].
    apply (ptree_comm_right (perm_trans _ _ _ (perm_sym PERM) (perm_sym double_perm_head))), ptree_weaken_right, (ptree_comm_right (perm_nodup form_eq_dec double_perm_head)), PP.
    destruct PP as [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
    refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (incl_tran SUB (incl_tran (fun B IN => perm_in form_eq_dec (perm_sym double_perm_head) _ IN) (fun B IN => proj2 (nodup_In _ _ _) IN)))) PD_app).
Qed.

Lemma ptree_redups_right :
    forall (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        provable OC gamma (nodup form_eq_dec delta) alpha ->
            provable OC gamma delta alpha.
Proof.
intros gamma delta OC alpha PP.
apply (prove_extras_right_aux (length delta) _ _ _ _ eq_refl PP).
Qed.

Lemma ptree_equiv_right :
    forall (gamma delta1 delta2 : list formula) (OC : constraint) (alpha : ordinal),
        (forall A : formula, In A delta1 <-> In A delta2) ->
            provable OC gamma delta1 alpha ->
                provable OC gamma delta2 alpha.
Proof.
intros gamma delta1 delta2 OC alpha EQUIV PP.
apply ptree_redups_right, (ptree_comm_right (equiv_nodup_perm form_eq_dec EQUIV)), ptree_nodups_right, PP.
Qed.

Lemma ptree_imp_r_inv : 
    forall (P : ptree) (OC : constraint) (gamma delta : list formula) (phi psi : formula) (alpha : ordinal),
        P_proves P OC gamma ((imp phi psi) :: delta) alpha ->
            provable OC (phi :: gamma) (psi :: delta) alpha.
Proof.
induction P;
intros OC' gamma' delta' phi' psi' alpha' [[[[[[PSV PStab'] PG'] PD'] POC'] [PG_app' PD_app']] PDeg'];
subst.

(*1-3 : destruct PSV.*)
4 : destruct PSV as [[[[PSV [PG_app PD_app]] PL_app] Psig] PLoop].
5-10 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12-13 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
14 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
17 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

all : subst.

1-3 : inversion PD'.

admit.

pose proof (@perm_head _ (equ v1 v2 :: phi :: gamma) [] phi') as PERM.
rewrite app_nil_r in PERM. 
apply (ptree_comm_left PERM).
apply ptree_con_l.
apply (ptree_comm_left (perm_sym (@perm_head _ (equ v1 v2 :: phi :: (substitution phi v1 v2) :: gamma) [] phi'))).
rewrite app_nil_r, <- PG.
apply IHP.
rewrite <- PD'.
repeat split;
try assumption.
exists PSV.
apply PStab'.
simpl in *.
admit.

simpl in *.
inversion PD' as [[EQ1 EQ2]].
subst.
apply ptree_con_r, ptree_con_l_better, IHP.
pose proof (@perm_head _ (phi :: delta) [] psi') as PERM.
rewrite app_nil_r in PERM. 
apply (ptree_comm_right PERM).
apply ptree_con_l.
apply (ptree_comm_left (perm_sym (@perm_head _ (equ v1 v2 :: phi :: (substitution phi v1 v2) :: gamma) [] phi'))).
rewrite app_nil_r, <- PG.
apply IHP.
rewrite <- PD'.
repeat split;
try assumption.
exists PSV.
apply PStab'.
simpl in *.
admit.

(*
Master destruct tactic.

1-3 : destruct PSV.
4 : destruct PSV as [[[[PSV [PG_app PD_app]] PL_app] Psig] PLoop].
5-10 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
11 : destruct PSV as [[[[[[[PSV [PG_app PD_app]] PG] PD] KNING] KNIND] [KIN POC]] PDeg].
12-13 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
14 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] POC] POC_rel] PDeg].
15 : destruct PSV as [[[[[[PSV [PG_app PD_app]] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg].
16 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].
17 : destruct PSV as [[[[[PSV [PG_app PD_app]] PG] PD] POC] PDeg].
18 : destruct PSV as [[[[[[[[[[P1SV P2SV] [PG_app PD_app]] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2].

*)