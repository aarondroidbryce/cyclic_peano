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

Definition ptree_left (P : ptree) : list formula :=
match P with
| bot => [fal]

| pred vec pn pure => [prd pn pure]

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

| pred vec pn pure => [prd pn pure]

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

Definition ptree_constraint (P : ptree) : constraint :=
match P with
| bot => empty

| pred vec pn pure => empty

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

Definition ptree_deg (P : ptree) : ordinal :=
match P with
| bot => cast Zero

| pred vec pn pure => cast Zero

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

| bnd_l OC gamma delta phi lambda kappa alpha P' => alpha

| bnd_r OC gamma delta phi lambda kappa alpha P' => alpha


| imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => omax alpha1 alpha2

| imp_r OC gamma delta phi psi alpha P' => alpha


| cut OC gamma delta phi alpha1 alpha2 P1 P2 => omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))
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

| pred vec pn pure, [true] => [ptree_state P]

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

Definition applicable (OC : constraint) (gamma delta : list formula) : Prop := (incl (flat_map vars_in gamma) (OC_list OC)) * (incl (flat_map vars_in delta) (OC_list OC)).

Fixpoint struct_valid (P : ptree) : Prop :=
match P with
| bot => true = true

| pred vec P pure => true = true

| equal v1 v2 => true = true

| loop_head OC gamma delta P_Target => (struct_valid P_Target) * applicable OC gamma delta * applicable (ptree_constraint P_Target) gamma delta * inhabited {sig : ovar -> ovar & coherent sig OC (ptree_constraint P_Target) /\ (incl (map (fun lambda => sig_subst lambda sig) (ptree_left P_Target)) gamma) /\ (incl (map (fun lambda => sig_subst lambda sig) (ptree_right P_Target)) delta)} * (In (loop_head OC gamma delta bot) (leaves P_Target))

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
(*destruct PSV as [[[[PSV POC_app] PL_app] [Psig [Psig_Coh [PG PD]]]] PLoop]. *)
destruct (in_leaves_path _ _ PLoop) as [M [L EQ]].
exists (true :: M).
exists L.
unfold path_fit;
fold path_fit.
rewrite EQ.
reflexivity.
Defined.

Ltac struct_type PSV :=
try destruct PSV as [[[[[[[[[[P1SV P2SV] P_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2];
try destruct PSV as [[[[[[[PSV P_app] PG] PD] KNING] KNIND] [KIN POC]] PDeg];
try destruct PSV as [[[[[[PSV P_app] PG] PD] POC] POC_rel] PDeg];
try destruct PSV as [[[[[PSV P_app] PG] PD] [NEW [KIN POC]]] PDeg];
try destruct PSV as [[[[[PSV P_app] PG] PD] POC] PDeg];
try destruct PSV as [[[[PSV POC_app] PL_app] [Psig [Psig_Coh [PG PD]]]] PLoop].

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
15 : destruct PSV as [[[[[PSV P_app] PG] PD] [NEW [KIN POC]]] PDeg].
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
15 : destruct PSV as [[[[[PSV P_app] PG] PD] [NEW [KIN POC]]] PDeg].
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


Lemma commutative_left_aux :
    forall (LN : list nat) (gamma1 gamma2 delta : list formula) (OC : constraint) (alpha: ordinal),
        (set_bury gamma1 LN = gamma2) ->
            provable OC gamma1 delta alpha ->
                provable OC gamma2 delta alpha.
Proof.
induction LN;
intros gamma1 gamma2 delta OC alpha EQ [P [[[[[[PSV PStab] PG] PD] POC] POC_app] PDeg]].
- unfold set_bury in EQ.
  subst.
  exists P.
  repeat split;
  try apply POC_app.
  apply (existT _ PSV PStab).
- unfold set_bury in EQ;
  fold @set_bury in EQ.
  refine (IHLN _ _ _ _ _ EQ (existT _ (ex_l _ _ _ _ _ P) _)).
  repeat split;
  try apply POC_app.
  + eassert (struct_valid (ex_l OC gamma1 delta a alpha P)) as PSV'.
    { repeat split;
      try assumption;
      apply POC_app. }
      refine (existT _ PSV' _).
      simpl.
      destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
      rewrite (proof_irrelevance _ PSV' PSV).
      apply PStab.
  + intros o.
    rewrite flat_map_bury_incl.
    apply POC_app.
Qed.

Lemma commutative_left :
    forall (gamma1 gamma2 delta : list formula) (OC : constraint) (alpha : ordinal),
        (perm gamma1 gamma2) ->
            provable OC gamma1 delta alpha ->
                provable OC gamma2 delta alpha.
Proof.
intros gamma1 gamma2 delta OC alpha perm.
pose proof (set_bury_eq_perm perm) as [LN EQ].
apply (commutative_left_aux LN _ _ _ _ _ EQ).
Qed.

Lemma commutative_left_leaves :
    forall {OC : constraint} {gamma1 gamma2 delta : list formula} {alpha : ordinal} (PERM : perm gamma1 gamma2) (PP : provable OC gamma1 delta alpha),
        leaves (projT1 (commutative_left gamma1 gamma2 delta OC alpha PERM PP)) = leaves (projT1 PP).
Proof.

Admitted.

Lemma commutative_left_leaf_struct :
    forall OC gamma1 gamma2 delta alpha PERM PP PSV1 PSV2 PL IN1 IN2,
        (leaf_struct (projT1 (commutative_left gamma1 gamma2 delta OC alpha PERM PP)) PL PSV1 IN1) = leaf_struct (projT1 PP) PL PSV2 IN2.
Proof.

Admitted.

Lemma commutative_left_leaf_type :
    forall OC gamma1 gamma2 delta alpha PERM PP PSV1 PSV2 PL IN1 IN2,
        (leaf_type (projT1 (commutative_left gamma1 gamma2 delta OC alpha PERM PP)) PL PSV1 IN1) = leaf_type (projT1 PP) PL PSV2 IN2.
Proof.

Admitted.

Lemma ptree_con_l_better :
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha : ordinal),
        provable OC (phi :: phi :: gamma) delta alpha ->
            provable OC (phi :: gamma) delta alpha.
Proof.
intros OC gamma delta phi alpha PP.
assert (provable OC (phi :: phi :: gamma ++ [equ 0 0]) delta alpha) as PP'.
{ inversion PP as [P [[[[[[PSV PStab] PG] PD] POC] POC_app] PDeg]].
  refine (existT _ (wkn OC (phi :: phi :: gamma) delta [equ 0 0] [] alpha P) _).
  repeat split;
  try apply POC_app.
  - assert (struct_valid (wkn OC (phi :: phi :: gamma) delta [equ 0 0] [] alpha P)) as PSV'.
    { repeat split;
      try assumption;
      try apply POC_app. }
    refine (existT _ PSV' _).
    simpl.
    destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
    rewrite (proof_irrelevance _ PSV' PSV).
    apply PStab.
  - unfold ptree_right.
    apply app_nil_r.
  - intros A IN.
    rewrite app_comm_cons, app_comm_cons, flat_map_app in IN.
    unfold flat_map at 2 in IN.
    unfold vars_in at 2 in IN.
    repeat rewrite app_nil_r in IN.
    destruct POC_app as [PG_app PD_app]. 
    apply PG_app, IN. }
assert (perm (phi :: phi :: gamma ++ [equ 0 0]) ((equ 0 0) :: phi :: phi :: gamma)) as PERM.
{ repeat rewrite app_comm_cons.
  rewrite <- app_nil_r.
  apply perm_head. }
refine (existT _ (refl OC (phi :: gamma) delta 0 alpha (con_l OC gamma delta phi 0 0 alpha (projT1 (commutative_left _ _ _ _ _ PERM PP')))) _).
repeat split.
- assert (struct_valid (refl OC (phi :: gamma) delta 0 alpha (con_l OC gamma delta phi 0 0 alpha (projT1 (commutative_left (phi :: phi :: gamma ++ [equ 0 0]) (equ 0 0 :: phi :: phi :: gamma) delta OC alpha PERM PP'))))) as PSV'.
  { pose proof (projT2 (commutative_left (phi :: phi :: gamma ++ [equ 0 0]) (equ 0 0 :: phi :: phi :: gamma) delta OC alpha PERM PP')) as [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg].
    (*destruct PP' as [P [[[[[[PSV PStab] PG] PD] POC] POC_app] PDeg]].*)
    repeat split;
    try assumption.
    - refine (incl_tran _ PG_app).
      apply (@flat_map_incl _ _ form_eq_dec nat_eq_dec).
      intros A IN.
      apply (or_intror (or_intror (or_intror IN))).
    - rewrite PG.
      admit.
    - unfold flat_map in PG_app;
      fold (flat_map vars_in (phi :: phi :: gamma)) in PG_app.
      rewrite app_nil_l in PG_app.
      refine (incl_tran _ PG_app).
      apply (@flat_map_incl _ _ form_eq_dec nat_eq_dec).
      intros A [EQ | IN].
      apply (or_introl EQ).
      apply (or_intror (or_intror IN)). }
  refine (existT _ PSV' _).
  simpl.
  destruct PSV' as [[[[[PSV' POC_app'] PG'] PD'] POC'] PDeg'].
  destruct PSV' as [[[[[PSV'' POC_app''] PG''] PD''] POC''] PDeg''].
  subst.
  intros PL IN.
  destruct PP' as [P [[[[[[PSV PStab] PG] PD] POC] POC_app] PDeg]].
  assert (In PL (leaves P)) as IN'.
  { rewrite commutative_left_leaves in IN.
    apply IN. }
  pose proof (commutative_left_leaf_struct OC (phi :: phi :: gamma ++ [equ 0 0]) ((equ 0 0) :: phi :: phi :: gamma) delta alpha PERM _ PSV'' PSV PL IN IN') as EQ.
  pose proof (commutative_left_leaf_type OC (phi :: phi :: gamma ++ [equ 0 0]) ((equ 0 0) :: phi :: phi :: gamma) delta alpha PERM _ PSV'' PSV PL IN IN') as EQ1.
  rewrite EQ, EQ1.  
  simpl.
  apply PStab.
- destruct PP' as [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
  refine (incl_tran _ PG_app).
  apply (@flat_map_incl _ _ form_eq_dec nat_eq_dec).
  intros A [EQ | IN].
  apply (or_introl EQ).
  apply (or_intror (or_intror (in_or_app _ _ _ (or_introl IN)))).
- destruct PP' as [P [[[[[[PSV PStab] PG] PD] POC] [PG_app PD_app]] PDeg]].
  apply PD_app.
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
    pose proof (commutative_left _ _ _ _ _ double_perm_head PP) as [P [[[[[[PSV PStab] PG] PD] POC] POC_app] PDeg]].
    assert (provable OC (A :: gamma1 ++ gamma2 ++ gamma3) delta alpha) as PP'.
    { exists ()
      repeat split.
      admit. }
    rewrite (perm_length double_perm_head) in EQ.
    inversion EQ as [EQ'].
    unfold length in EQ';
    fold (length (A :: gamma1 ++ gamma2 ++ gamma3)) in EQ'.
    refine (commutative_left _ _ _ _ _ _ (IHn _ _ _ _ EQ' PP')).

Lemma prove_dups_left :
    forall (gamma delta : list formula) (OC : constraint) (alpha: ordinal),
        provable OC gamma delta alpha ->
            provable OC (nodup form_eq_dec gamma) delta alpha.
Proof.
intros gamma delta OC alpha PP.
case (no_dup_dec_cases form_eq_dec gamma) as [NDG | DG].
- rewrite (nodup_fixed_point _ NDG).
  apply PP.
- induction (length gamma) eqn:EQ.
  + admit.
  +
destruct (has_dups_split form_eq_dec DG) as [A [gamma1 [gamma2 [gamma3 EQ]]]].
  subst.
  pose proof (commutative_left _ _ _ _ _ double_perm_head PP).
destruct PP as [P [[[[[[PSV PStab] PG] PD] POC] POC_app] PDeg]].

Lemma prove_dups :
    forall (gamma delta : list formula) (OC : constraint),
        provable gamma delta OC ->
            provable (nodup form_eq_dec gamma) delta OC.
Proof.

Lemma commutative_left :
    forall (gamma1 gamma2 delta : list formula) (OC : constraint),
        (forall A : formula, In A gamma1 <-> In A gamma2) ->
            provable gamma1 delta OC ->
                provable gamma2 delta OC.
Proof.
induction gamma1;
intros gamma2 delta OC EQUIV [P [[[[PSV PStab] PG] PD] POC]].
- enough (gamma2 = ptree_left P) as EQ.
  subst.
  exists P.
  repeat split.
  apply (existT _ PSV PStab).
  rewrite PG.
  destruct gamma2 as [ | A gamma2].
  reflexivity.
  contradiction (proj2 (EQUIV A) (or_introl eq_refl)).
- 
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