From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import constraints.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import substitute.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep_dec.


Inductive ptree : Type :=
| bot : ptree

| pred : forall (pn : predicate), pure_predicate pn = true -> ptree


| loop_head : forall (OC : constraint) (gamma delta : list (nat * ovar * formula)) (alpha : ordinal) (l : nat), ptree

(*| deg_up : forall (OC : constraint) (gamma delta : list formula) (alpha beta : ordinal) (LT : ord_lt alpha beta) (P' : ptree), ptree *)

| con_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (P' : ptree), ptree

| con_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (P' : ptree), ptree


| ex_l : forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} (P' : ptree), ptree

| ex_r : forall {OC : constraint} {gamma delta : list formula} (n : nat) {alpha : ordinal} (P' : ptree), ptree


| wkn_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (P' : ptree), ptree

| wkn_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha : ordinal} (P' : ptree), ptree

| rst : forall {OC : constraint} {gamma delta : list formula} (kappa : ovar) {alpha : ordinal} (P' : ptree), ptree


| bnd_l : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (lambda kappa : ovar) {alpha : ordinal} (P' : ptree), ptree

| bnd_r : forall {OC : constraint} {gamma delta : list formula} (phi : formula) (lambda kappa : ovar) {alpha : ordinal} (P' : ptree), ptree


| imp_l : forall {OC : constraint} {gamma delta : list formula} (phi psi : formula) {alpha1 alpha2 : ordinal} (P1 P2 : ptree), ptree

| imp_r : forall {OC : constraint} {gamma delta : list formula} (phi psi : formula) {alpha : ordinal} (P' : ptree), ptree


| cut : forall {OC : constraint} {gamma delta : list formula} (phi : formula) {alpha1 alpha2 : ordinal} (P1 P2 : ptree), ptree.

Definition ptree_left (P : ptree) : list formula :=
match P with
| bot => [fal]

| pred pn pure => [prd pn pure]

| loop_head OC gamma delta alpha l => fzip (uncurry nuk) gamma


| @con_l OC gamma delta phi alpha P' => phi :: gamma

| @con_r OC gamma delta phi alpha P' => gamma


| @ex_l OC gamma delta n alpha P' => bury gamma n

| @ex_r OC gamma delta n alpha P' => gamma


| @wkn_l OC gamma delta phi alpha P' => phi :: gamma

| @wkn_r OC gamma delta phi alpha P' => gamma

| @rst OC gamma delta kappa alpha P' => gamma


| @bnd_l OC gamma delta phi lambda kappa alpha P' => (bnd lambda kappa phi) :: gamma

| @bnd_r OC gamma delta phi lambda kappa alpha P' => gamma


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => (imp phi psi) :: gamma

| @imp_r OC gamma delta phi psi alpha P' => gamma


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => gamma
end.

Definition ptree_right (P : ptree) : list formula :=
match P with
| bot => []

| pred pn pure => [prd pn pure]

| loop_head OC gamma delta alpha l => fzip (uncurry nuk) delta

| @con_l OC gamma delta phi alpha P' => delta

| @con_r OC gamma delta phi alpha P' => phi :: delta


| @ex_l OC gamma delta n alpha P' => delta

| @ex_r OC gamma delta n alpha P' => bury delta n


| @wkn_l OC gamma delta phi alpha P' => delta

| @wkn_r OC gamma delta phi alpha P' => phi :: delta

| @rst OC gamma delta kappa alpha P' => delta


| @bnd_l OC gamma delta phi lambda kappa alpha P' => delta

| @bnd_r OC gamma delta phi lambda kappa alpha P' => (bnd lambda kappa phi) :: delta


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => delta

| @imp_r OC gamma delta phi psi alpha P' => (imp phi psi) :: delta


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => delta
end.

Definition ptree_constraint (P : ptree) : constraint :=
match P with
| bot => empty

| pred pn pure => empty

| loop_head OC gamma delta alpha l => OC

| @con_l OC gamma delta phi alpha P' => OC

| @con_r OC gamma delta phi alpha P' => OC


| @ex_l OC gamma delta n alpha P' => OC

| @ex_r OC gamma delta n alpha P' => OC


| @wkn_l OC gamma delta phi alpha P' => OC

| @wkn_r OC gamma delta phi alpha P' => OC

| @rst OC gamma delta kappa alpha P' => OC


| @bnd_l OC gamma delta phi lambda kappa alpha P' => OC

| @bnd_r OC gamma delta phi lambda kappa alpha P' => OC


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => OC

| @imp_r OC gamma delta phi psi alpha P' => OC


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => OC
end.

Definition ptree_deg (P : ptree) : ordinal :=
match P with
| bot => cast Zero

| pred pn pure => cast Zero

| loop_head OC gamma delta alpha l => cast Zero

| @con_l OC gamma delta phi alpha P' => alpha

| @con_r OC gamma delta phi alpha P' => alpha


| @ex_l OC gamma delta n alpha P' => alpha

| @ex_r OC gamma delta n alpha P' => alpha


| @wkn_l OC gamma delta phi alpha P' => alpha

| @wkn_r OC gamma delta phi alpha P' => alpha

| @rst OC gamma delta L alpha P' => alpha

| @bnd_l OC gamma delta phi lambda kappa alpha P' => alpha

| @bnd_r OC gamma delta phi lambda kappa alpha P' => alpha


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => omax alpha1 alpha2

| @imp_r OC gamma delta phi psi alpha P' => alpha


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))
end.

(*
Fixpoint ptree_height (P : ptree) : nat :=
match P with
| bot => 1

| pred pn pure => 1

| loop_head OC gamma delta alpha l => S (ptree_height l)

| @con_l OC gamma delta phi alpha P' => S (ptree_height P')

| @con_r OC gamma delta phi alpha P' => S (ptree_height P')


| @ex_l OC gamma delta n alpha P' => S (ptree_height P')

| @ex_r OC gamma delta n alpha P' => S (ptree_height P')


| @wkn_l OC gamma delta phi alpha P' => S (ptree_height P')

| @wkn_r OC gamma delta phi alpha P' => S (ptree_height P')

| @rst OC gamma delta kappa alpha P' => S (ptree_height P')

| @bnd_l OC gamma delta phi lambda kappa alpha P' => S (ptree_height P')

| @bnd_r OC gamma delta phi lambda kappa alpha P' => S (ptree_height P')


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => S (max (ptree_height P1) (ptree_height P2))

| @imp_r OC gamma delta phi psi alpha P' => S (ptree_height P')


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => S (max (ptree_height P1) (ptree_height P2))
end.
*)


Lemma pair_eq_dec {A B : Type} (DECA : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) (DECB : forall (b1 b2 : B), {b1 = b2} + {b1 <> b2}) : forall (X Y : A * B), {X = Y} + {X <> Y}.
Proof.
intros [A1 B1] [A2 B2].
case (DECA A1 A2) as [EQ1 | NE].
case (DECB B1 B2) as [EQ2 | NE].
subst.
apply left, eq_refl.
all : right; intros FAL; apply NE; inversion FAL; reflexivity.
Qed.

Lemma ptree_eq_dec : forall (P1 P2 : ptree), {P1 = P2} + {P1 <> P2}.
Proof.
induction P1;
destruct P2.

2-16 : right; discriminate.
3-17 : right; discriminate.
4-18 : right; discriminate.
5-19 : right; discriminate.
6-20 : right; discriminate.
7-21 : right; discriminate.
8-22 : right; discriminate.
9-23 : right; discriminate.
10-24 : right; discriminate.
11-25 : right; discriminate.
12-26 : right; discriminate.
13-27 : right; discriminate.
14-28 : right; discriminate.
15-29 : right; discriminate.

all : try destruct (nat_eq_dec n n0) as [EQN | NE];
      try destruct (IHP1 P2) as [EQ | NE];
			try destruct (IHP1_1 P2_1) as [EQ1 | NE];
      try destruct (IHP1_2 P2_2) as [EQ2 | NE];
      try destruct (prd_eq_dec pn pn0) as [EQP | NE];
      try destruct (constraint_eq_dec OC OC0) as [EQO | NE];
      try destruct (nat_eq_dec l l0) as [EQLEN | NE];
			try destruct (nat_eq_dec v v0) as [EQV | NE];
			try destruct (nat_eq_dec v1 v0) as [EQV1 | NE];
			try destruct (nat_eq_dec v2 v3) as [EQV2 | NE];
      try destruct (list_eq_dec form_eq_dec gamma gamma0) as [EQG | NE];
      try destruct (list_eq_dec (pair_eq_dec (pair_eq_dec nat_eq_dec nat_eq_dec) form_eq_dec) gamma gamma0) as [EQG | NE];
      try destruct (list_eq_dec form_eq_dec delta delta0) as [EQD | NE];
      try destruct (list_eq_dec (pair_eq_dec (pair_eq_dec nat_eq_dec nat_eq_dec) form_eq_dec) delta delta0) as [EQD | NE];
			try destruct (list_eq_dec form_eq_dec pi pi0) as [EQPI | NE];
			try destruct (list_eq_dec form_eq_dec sigma sigma0) as [EQS | NE];
      try destruct (form_eq_dec phi phi0) as [EQP1 | NE];
			try destruct (form_eq_dec psi psi0) as [EQP2 | NE];
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

(*
Fixpoint ptree_descends_from (P Source : ptree) : bool :=
match P with
| bot => false

| pred pn pure => false

| loop_head OC gamma delta alpha l => false

| con_l phi P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source

| con_r phi P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source


| ex_l n P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source

| ex_r n P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source


| wkn_l phi P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source

| wkn_r phi P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source

| rst kappa P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source

| bnd_l phi lambda kappa P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source

| bnd_r phi lambda kappa P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source


| imp_l phi psi P1 P2 => if ptree_eq_dec P1 Source then true else if ptree_eq_dec P2 Source then true else (ptree_descends_from P1 Source || ptree_descends_from P2 Source)

| imp_r phi psi P' => if ptree_eq_dec P' Source then true else ptree_descends_from P' Source


| cut phi P1 P2 => if ptree_eq_dec P1 Source then true else if ptree_eq_dec P2 Source then true else (ptree_descends_from P1 Source || ptree_descends_from P2 Source)
end.
*)

(*
Fixpoint ptree_equiv (P1 P2 : ptree) : Prop :=
match P1, P2 with
| bot, bot => True

| pred pn1 pure1, pred pn2 pure2 => prd_eqb pn1 pn2 = true

| loop_head OC1 gamma1 delta1 alpha1 l1, loop_head OC2 gamma2 delta2 alpha2 l2 =>
    OC1 = OC2 /\ gamma1 = gamma2 /\ delta1 = delta2 /\ (l1 = l2 \/ l2 = bot) /\ alpha1 = alpha2

| con_l phi1 P1, con_l phi2 P2 => phi1 = phi2 /\ ptree_equiv P1 P2

| con_r phi1 P1, con_r phi2 P2 => phi1 = phi2 /\ ptree_equiv P1 P2


| ex_l n1 P1, ex_l n2 P2 => n1 = n2 /\ ptree_equiv P1 P2

| ex_r n1 P1, ex_r n2 P2  => n1 = n2 /\ ptree_equiv P1 P2


| wkn_l phi1 P1, wkn_l phi2 P2 => phi1 = phi2 /\ ptree_equiv P1 P2

| wkn_r phi1 P1, wkn_r phi2 P2 => phi1 = phi2 /\ ptree_equiv P1 P2

| rst kappa1 P1, rst kappa2 P2 => kappa1 = kappa2 /\ ptree_equiv P1 P2

| bnd_l phi1 lambda1 kappa1 P1, bnd_l phi2 lambda2 kappa2 P2 => phi1 = phi2 /\ lambda1 = lambda2 /\ kappa1 = kappa2 /\ ptree_equiv P1 P2

| bnd_r phi1 lambda1 kappa1 P1, bnd_r phi2 lambda2 kappa2 P2 => phi1 = phi2 /\ lambda1 = lambda2 /\ kappa1 = kappa2 /\ ptree_equiv P1 P2


| imp_l phi1 psi1 P1 P2, imp_l phi2 psi2 P3 P4 => phi1 = phi2 /\ psi1 = psi2 /\ ptree_equiv P1 P3 /\ ptree_equiv P2 P4

| imp_r phi1 psi1 P1, imp_r phi2 psi2 P2 => phi1 = phi2 /\ psi1 = psi2 /\ ptree_equiv P1 P2


| cut phi1 P1 P2, cut phi2 P3 P4 => phi1 = phi2 /\ ptree_equiv P1 P3 /\ ptree_equiv P2 P4

| _ , _ => False
end.
*)

(*
Fixpoint leaves (P : ptree) : list (ptree * ptree) :=
match P with
| bot => []

| pred pn pure => []

| loop_head OC gamma delta alpha l => [pair P l]

| con_l phi P' => leaves P'

| con_r phi P' => leaves P'


| ex_l n P' => leaves P'

| ex_r n P' => leaves P'


| wkn_l phi P' => leaves P'

| wkn_r phi P' => leaves P'

| rst kappa P' => leaves P'

| bnd_l phi lambda kappa P' => leaves P'

| bnd_r phi lambda kappa P' => leaves P'


| imp_l phi psi P1 P2 => leaves P1 ++ leaves P2

| imp_r phi psi P' => leaves P'


| cut phi P1 P2 => leaves P1 ++ leaves P2
end.
*)

(*
Definition path_marker := list bool.

Fixpoint path_fit (P : ptree) (M : path_marker) : list ptree :=
match P, M with
| bot, [true] => [P]

| pred pn pure, [true] => [P]

| loop_head OC gamma delta alpha l, [true] => [P]

| con_l phi P', true :: M' => P :: path_fit P' M'

| con_r phi P', true :: M' => P :: path_fit P' M'


| ex_l n P', true :: M' => P :: path_fit P' M'

| ex_r n P', true :: M' => P :: path_fit P' M'


| wkn_l phi P', true :: M' => P :: path_fit P' M'

| wkn_r phi P', true :: M' => P :: path_fit P' M'

| rst kappa P', true :: M' => P :: path_fit P' M'

| bnd_l phi lambda kappa P', true :: M' => P :: path_fit P' M'

| bnd_r phi lambda kappa P', true :: M' => P :: path_fit P' M'


| imp_l phi psi P1 P2, false :: M' => P :: path_fit P1 M'

| imp_l phi psi P1 P2, true :: M' => P :: path_fit P2 M'

| imp_r phi psi P', true :: M' => P :: path_fit P' M'


| cut phi P1 P2, false :: M' => P :: path_fit P1 M'

| cut phi P1 P2, true :: M' => P :: path_fit P2 M'

| _ , _ => []
end.
*)

Definition option_decr (ON : option nat) : option nat :=
match ON with
| Some (S n) => Some n
| _ => None
end.

Fixpoint loop_traces (P : ptree) : list (option nat) :=
match P with
| bot => []

| pred pn pure => []

| loop_head OC gamma delta alpha l => [Some (S l)]

| con_l phi P' => map option_decr (loop_traces P')

| con_r phi P' => map option_decr (loop_traces P')

| ex_l n P' => map option_decr (loop_traces P')

| ex_r n P' => map option_decr (loop_traces P')

| wkn_l phi P' => map option_decr (loop_traces P')

| wkn_r phi P' => map option_decr (loop_traces P')

| rst kappa P' => map option_decr (loop_traces P')

| bnd_l phi lambda kappa P' => map option_decr (loop_traces P')

| bnd_r phi lambda kappa P' => map option_decr (loop_traces P')

| imp_l phi psi P1 P2 => map option_decr (loop_traces P1 ++ loop_traces P2)

| imp_r phi psi P' => map option_decr (loop_traces P')

| cut phi P1 P2 => map option_decr (loop_traces P1 ++ loop_traces P2)
end.

Fixpoint option_fill {A B : Type} (a : A) (LOB : list (option B)) (LLA : list (list A)) : list (list A) :=
match LOB, LLA with
| Some B :: LOB', LA :: LLA' => (a :: LA) :: (option_fill a LOB' LLA')
| None :: LOB', LA :: LLA' => LA :: (option_fill a LOB' LLA')
| _, _ => []
end.

Fixpoint loops (P : ptree) : list (list ptree) :=
match P with
| bot => []

| pred pn pure => []

| loop_head OC gamma delta alpha l => [[P]]

| con_l phi P' => option_fill P (loop_traces P) (loops P')

| con_r phi P' => option_fill P (loop_traces P) (loops P')

| ex_l n P' => option_fill P (loop_traces P) (loops P')

| ex_r n P' => option_fill P (loop_traces P) (loops P')

| wkn_l phi P' => option_fill P (loop_traces P) (loops P')

| wkn_r phi P' => option_fill P (loop_traces P) (loops P')

| rst kappa P' => option_fill P (loop_traces P) (loops P')

| bnd_l phi lambda kappa P' => option_fill P (loop_traces P) (loops P')

| bnd_r phi lambda kappa P' => option_fill P (loop_traces P) (loops P')

| imp_l phi psi P1 P2 => option_fill P (loop_traces P) (loops P1 ++ loops P2)

| imp_r phi psi P' => option_fill P (loop_traces P) (loops P')

| cut phi P1 P2 => option_fill P (loop_traces P) (loops P1 ++ loops P2)
end.

(*
Fixpoint traces (P : ptree) : list (option (list ptree)) :=
match P with
| bot => [None]

| pred pn pure => [None]

| loop_head OC gamma delta alpha l => [Some [P]]

| con_l phi P' => map (option_map (fun L => P :: L)) (traces P')

| con_r phi P' => map (option_map (fun L => P :: L)) (traces P')

| ex_l n P' => map (option_map (fun L => P :: L)) (traces P')

| ex_r n P' => map (option_map (fun L => P :: L)) (traces P')

| wkn_l phi P' => map (option_map (fun L => P :: L)) (traces P')

| wkn_r phi P' => map (option_map (fun L => P :: L)) (traces P')

| rst kappa P' => map (option_map (fun L => P :: L)) (traces P')

| bnd_l phi lambda kappa P' => map (option_map (fun L => P :: L)) (traces P')

| bnd_r phi lambda kappa P' => map (option_map (fun L => P :: L)) (traces P')

| imp_l phi psi P1 P2 => map (option_map (fun L => P :: L)) (traces P1 ++ traces P2)

| imp_r phi psi P' => map (option_map (fun L => P :: L)) (traces P')

| cut phi P1 P2 => map (option_map (fun L => P :: L)) (traces P1 ++ traces P2)
end.

Fixpoint loop_lengths (P : ptree) : list (option nat) :=
match P with
| bot => [None]

| pred pn pure => [None]

| loop_head OC gamma delta alpha l => [Some (S l)]

| con_l phi P' => loop_lengths P'

| con_r phi P' => loop_lengths P'

| ex_l n P' => loop_lengths P'

| ex_r n P' => loop_lengths P'

| wkn_l phi P' => loop_lengths P'

| wkn_r phi P' => loop_lengths P'

| rst kappa P' => loop_lengths P'

| bnd_l phi lambda kappa P' => loop_lengths P'

| bnd_r phi lambda kappa P' => loop_lengths P'

| imp_l phi psi P1 P2 => loop_lengths P1 ++ loop_lengths P2

| imp_r phi psi P' => loop_lengths P'

| cut phi P1 P2 => loop_lengths P1 ++ loop_lengths P2
end.

Definition loops (P : ptree) : list (list ptree) := map (fun L : (nat * (list ptree)) => firstn (fst L) (snd L)) (combine (simplify (loop_lengths P)) (simplify (traces P))).
*)

Definition applicable (OC : constraint) (P : ptree) : Prop := (incl (flat_map vars_in (ptree_left P)) (OC_list OC)) * (incl (flat_map vars_in (ptree_right P)) (OC_list OC)).

Fixpoint well_struct (P : ptree) : Type :=
match P with
| bot => true = true

| pred P pure => true = true

| loop_head OC gamma delta alpha l => applicable OC P

| @con_l OC gamma delta phi alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = phi :: phi :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha))

| @con_r OC gamma delta phi alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = gamma) * (ptree_right P' = phi :: phi :: delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha))


| @ex_l OC gamma delta n alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha))

| @ex_r OC gamma delta n alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha))


| @wkn_l OC gamma delta phi alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha))

| @wkn_r OC gamma delta phi alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha))

| @rst OC gamma delta kappa alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = gamma) * (ptree_right P' = delta) * (~ In kappa (flat_map vars_used gamma)) * (~ In kappa (flat_map vars_used delta)) * {SUB : (OC_elt OC kappa) & ptree_constraint P' = restriction OC (children OC kappa) (children_subset OC kappa)} * (ptree_deg P' = alpha))

| @bnd_l OC gamma delta phi lambda kappa alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = phi :: gamma) * (ptree_right P' = delta) * (ptree_constraint P' = OC) * (OC_rel OC lambda kappa = true) * (ptree_deg P' = alpha))

| @bnd_r OC gamma delta phi lambda kappa alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = gamma) * (ptree_right P' = phi :: delta) * {NEW : ~ OC_elt OC lambda & {KIN : OC_elt OC kappa & ptree_constraint P' = add_fresh_child OC lambda kappa NEW KIN}} * (~ In lambda (flat_map vars_used gamma) /\ ~ In lambda (flat_map vars_used (phi :: delta))) * (ptree_deg P' = alpha))


| @imp_l OC gamma delta phi psi alpha1 alpha2 P1 P2 => (well_struct P1 * well_struct P2) * (applicable OC P * (ptree_left P1 = psi :: gamma) * (ptree_right P1 = delta) * (ptree_constraint P1 = OC) * (ptree_left P2 = gamma) * (ptree_right P2 = phi :: delta) * (ptree_constraint P2 = OC) * (ptree_deg P1 = alpha1) * (ptree_deg P2 = alpha2))

| @imp_r OC gamma delta phi psi alpha P' => well_struct P' * (applicable OC P * (ptree_left P' = phi :: gamma) * (ptree_right P' = psi :: delta) * (ptree_constraint P' = OC) * (ptree_deg P' = alpha))


| @cut OC gamma delta phi alpha1 alpha2 P1 P2 => (well_struct P1 * well_struct P2) * (applicable OC P * (ptree_left P1 = gamma) * (ptree_right P1 = phi :: delta) * (ptree_constraint P1 = OC) * (ptree_left P2 = phi :: gamma) * (ptree_right P2 = delta) * (ptree_constraint P2 = OC) * (ptree_deg P1 = alpha1) * (ptree_deg P2 = alpha2))
end.

(*
Lemma path_fit_nil :
    forall (P : ptree),
        path_fit P [] = [].
Proof. induction P; reflexivity. Qed.

Lemma path_fit_single :
    forall (P : ptree),
        path_fit P [true] = [P].
Proof.
induction P;
unfold path_fit;
fold path_fit;
try rewrite path_fit_nil;
reflexivity.
Qed.

Lemma descends_is_path :
    forall (l P_Source : ptree),
        ptree_descends_from l P_Source = true ->
            {M : path_marker & {L : list ptree & path_fit l M = l :: L ++ [P_Source]}}.
Proof.
induction l;
intros P_Source DESC.

all : unfold ptree_descends_from in DESC;
      fold ptree_descends_from in DESC.

1-3 : inversion DESC.

12 :  { case (ptree_eq_dec l1 P_Source) as [EQ1 | NE1];
        subst.
        refine (existT _ [false; true] (existT _ [] _)).
        2 : case (ptree_eq_dec l2 P_Source) as [EQ2 | NE2];
            subst.
        2 : refine (existT _ [true; true] (existT _ [] _)).
        3 : unfold "||" in DESC;
            case (ptree_descends_from l1 P_Source) eqn:DESC1.
        3 : destruct (IHl1 _ DESC1) as [M [L EQ]];
            refine (existT _ (false :: M) (existT _ (l1 :: L) _)).
        4 : destruct (IHl2 _ DESC) as [M [L EQ]];
            refine (existT _ (true :: M) (existT _ (l2 :: L) _)).
        all : try rewrite app_nil_l;
              unfold path_fit;
              fold path_fit;
              try rewrite path_fit_single;
              try rewrite EQ;
              reflexivity. }

10 :  { case (ptree_eq_dec l1 P_Source) as [EQ1 | NE1];
        subst.
        refine (existT _ [false; true] (existT _ [] _)).
        2 : case (ptree_eq_dec l2 P_Source) as [EQ2 | NE2];
            subst.
        2 : refine (existT _ [true; true] (existT _ [] _)).
        3 : unfold "||" in DESC;
            case (ptree_descends_from l1 P_Source) eqn:DESC1.
        3 : destruct (IHl1 _ DESC1) as [M [L EQ]];
            refine (existT _ (false :: M) (existT _ (l1 :: L) _)).
        4 : destruct (IHl2 _ DESC) as [M [L EQ]];
            refine (existT _ (true :: M) (existT _ (l2 :: L) _)).
        all : try rewrite app_nil_l;
              unfold path_fit;
              fold path_fit;
              try rewrite path_fit_single;
              try rewrite EQ;
              reflexivity. }

all : case (ptree_eq_dec l P_Source) as [EQ | NE];
      subst.

1,3,5,7,9,11,13,15,17,19 :
  refine (existT _ [true; true] (existT _ [] _));
  rewrite app_nil_l;
  unfold path_fit;
  fold path_fit;
  rewrite path_fit_single;
  reflexivity.

all : destruct (IHl _ DESC) as [M [L EQ]];
      refine (existT _ (true :: M) (existT _ (l :: L) _));
      unfold path_fit;
      fold path_fit;
      rewrite EQ;
      reflexivity.
Defined.  
*)

Definition resets_var (P : ptree) (lambda : ovar) : Prop :=
match P with
| rst kappa P' => lambda = kappa
| _ => False
end.

(*
Definition well_formed (P : ptree) : Type :=
  (well_struct P) *
    (forall (P_Leaf l : ptree) (IN : In (pair P_Leaf l) (leaves P)),
        {P_Base : ptree &
            ((ptree_equiv P_Base l) *
            {DESC : (ptree_descends_from P_Base P_Leaf = true) &
                {kappa : ovar & 
                    (forall (P_path : ptree),
                        In P_path (path_fit P_Base (projT1 (descends_is_path P_Base P_Leaf DESC))) ->
                            OC_elt (ptree_constraint P_path) kappa) *
                    { P_reset : ptree & In P_reset (path_fit P_Base (projT1 (descends_is_path P_Base P_Leaf DESC))) /\ resets_var P_reset kappa}}})%type}).
*)

(*
Lemma loop_length_ge_1_aux :
    forall (P : ptree) (len : nat),
        In len (simplify (loop_lengths P)) ->
            1 <= len.
Proof.
induction P;
intros len IN;
unfold loop_lengths, simplify in IN;
fold loop_lengths @simplify in IN.
1-2 : inversion IN.
1 : apply in_single in IN.
    rewrite IN.
    lia.
all : try apply (IHP _ IN);
      rewrite simplify_app in IN;
      apply in_app_or in IN as [IN1 | IN2];
      try apply (IHP1 _ IN1);
      apply (IHP2 _ IN2).
Qed.

Lemma loop_length_ge_1 :
    forall (P : ptree) (Loop : list ptree),
        In Loop (loops P) ->
            1 <= length Loop.
Proof.
induction P;
intros Loop IN.
1,2 : inversion IN.
1 : unfold loops, traces, loop_lengths, combine, map, fst, snd, firstn, simplify in IN;
    fold (@firstn ptree) in IN.
    rewrite firstn_nil in IN.
    apply in_single in IN.
    rewrite IN.
    reflexivity.
all : unfold loops, traces, loop_lengths in *;
      fold traces loop_lengths in *;
      rewrite simplify_map_comm in IN;
      apply in_map_iff in IN as [[Loop_len Loop_elt] [EQ IN]];
      unfold fst, snd in EQ;
      apply in_combine_l in IN as INL;
      apply in_combine_r in IN as INR;
      apply in_map_iff in INR as [Loop_sub_elt [EQ' IN']];
      rewrite <- EQ, <- EQ';
      try rewrite simplify_app in INL;
      try apply in_app_or in INL as [INL1 | INL2];
      try pose proof (loop_length_ge_1_aux _ _ INL) as LE;
      try pose proof (loop_length_ge_1_aux _ _ INL1) as LE;
      try pose proof (loop_length_ge_1_aux _ _ INL2) as LE;
      destruct Loop_len;
      inversion LE;
      unfold firstn, length;
      lia.
Qed.
*)

(*
Definition well_formed (P : ptree) : Type :=
  (well_struct P) *
  (simplify (loop_lengths P) = map (@length ptree) (loops P)) *
  (forall (Loop : list ptree) (IN : In Loop (loops P)),
      { L_Start : ptree & { L_End : ptree & { L_Mid : list ptree & Loop = L_Start :: L_Mid ++ [L_End] /\
      (ptree_constraint L_Start = ptree_constraint L_End) *
      (ptree_left L_Start = ptree_left L_End) *
      (ptree_right L_Start = ptree_right L_End) *
      (ptree_deg L_Start = ptree_deg L_End)}}} *
      {kappa : ovar & 
          (forall (P_loop : ptree),
              In P_loop Loop ->
                  OC_elt (ptree_constraint P_loop) kappa) *
          { P_reset : ptree & In P_reset Loop}})%type.
*)

Definition well_formed (P : ptree) : Type :=
  (well_struct P) *
  ((Forall (eq None) (map option_decr (loop_traces P))) *
  (forall (Loop : list ptree) (IN : In Loop (loops P)),
      { L_Start : ptree & { L_End : ptree & { L_Mid : list ptree & Loop = L_Start :: L_Mid ++ [L_End] /\
      (ptree_constraint L_Start = ptree_constraint L_End) *
      (ptree_left L_Start = ptree_left L_End) *
      (ptree_right L_Start = ptree_right L_End)}}} *
      {kappa : ovar & 
          (forall (P_loop : ptree),
              In P_loop Loop ->
                  OC_elt (ptree_constraint P_loop) kappa) *
          { P_reset : ptree & In P_reset Loop /\ resets_var P_reset kappa}})%type).


Definition P_proves (P : ptree) (OC : constraint) (gamma delta : list formula) (alpha : ordinal) : Type :=
  (well_formed P) * (ptree_left P = gamma) * (ptree_right P = delta) * (ptree_constraint P = OC) * (ptree_deg P = alpha).

Definition provable (OC : constraint) (gamma delta : list formula) (alpha : ordinal) : Type :=
  {P : ptree & (P_proves P OC gamma delta alpha)}.

Lemma struct_OC_app :
    forall (P : ptree),
        well_struct P ->
            applicable (ptree_constraint P) P.
Proof.
induction P;
intros PSV.

1-2 : destruct PSV.
3 : destruct PSV as [PG_app PD_app].
4-9 : destruct PSV as [PSV [[[[[PG_app PD_app] PG] PD] POC] PDeg]].
10 : destruct PSV as [PSV [[[[[[[PG_app PD_app] PG] PD] KNING] KNIND] [KIN POC]] PDeg]].
11 : destruct PSV as [PSV [[[[[[PG_app PD_app] PG] PD] POC] POC_rel] PDeg]].
12 : destruct PSV as [PSV [[[[[[PG_app PD_app] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg]].
13 : destruct PSV as [[P1SV P2SV] [[[[[[[[[PG_app PD_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2]].
14 : destruct PSV as [PSV [[[[[PG_app PD_app] PG] PD] POC] PDeg]].
15 : destruct PSV as [[P1SV P2SV] [[[[[[[[[PG_app PD_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2]].

all : repeat split;
      unfold ptree_left, ptree_right, flat_map, vars_in;
      fold vars_in (flat_map vars_in).

1-4 : intros o IN;
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
Qed.

(*
Lemma test {A : Type} {LA : list (nat * list A)} : (map (@length A) (map (fun L : nat * list A => firstn (fst L) (snd L)) LA) = map (fun L => Nat.min (fst L) (length (snd L))) LA).
Proof.
induction LA.
reflexivity.
unfold map in *.
rewrite firstn_length, IHLA.
reflexivity.
Qed.

Lemma nat_min_S_1 :
    forall (n : nat),
        Nat.min (S n) 1 = 1.
Proof.
induction n;
reflexivity.
Qed.
*)

Lemma option_fill_incl :
    forall (LON : list (option nat)) (LP : list ptree) (LLP : list (list ptree)) (P : ptree),
        In LP (option_fill P LON LLP) ->
            In LP LLP + {LP' & LP = P :: LP' /\ In LP' LLP}.
Proof.
induction LON as [ | [ n | ] LON];
intros LP LLP P INP;
unfold option_fill in INP;
fold @option_fill in INP;
induction LLP;
try contradiction INP;
rewrite <- (app_nil_l (option_fill _ _ _)), app_comm_cons in INP;
apply (in_app_bor (list_eq_dec ptree_eq_dec)) in INP;
destruct INP as [IN1 | IN2];
try apply in_single in IN1.
3 : apply inl, or_introl, eq_sym, IN1.
1 : apply inr, (existT _ a (conj IN1 (or_introl eq_refl))).
all : destruct (IHLON _ _ _ IN2) as [IN3 | [LP' [EQ IN4]]].
1,3 : apply inl, or_intror, IN3.
all : apply inr, (existT _ LP' (conj EQ (or_intror IN4))).
Qed.

Lemma option_fill_len {A B : Type} :
forall (LOB : list (option B)) (LLA : list (list A)) (a : A),
        length (LOB) = length (LLA) ->
            length (option_fill a LOB LLA) = length LOB.
Proof.
induction LOB as [ | [b | ] LOB];
destruct LLA as [ | LA LLA];
intros a EQ.
1 : reflexivity.
all : unfold option_fill, length;
      fold @option_fill (@length (list A)) (@length (option B));
      inversion EQ as [EQ'];
      rewrite (IHLOB _ _ EQ');
      reflexivity.
Qed.

Lemma loop_traces_loop_length :
    forall (P : ptree),
        well_struct P ->
            length (loop_traces P) = length (loops P).
Proof.
induction P;
intros PSV.
1-3 : reflexivity.
all : destruct PSV as [PSV _];
      unfold loops, loop_traces;
      fold loop_traces loops;
      apply eq_sym, option_fill_len;
      rewrite map_length;
      try apply (IHP PSV);
      destruct PSV as [P1SV P2SV];
      rewrite !app_length, (IHP1 P1SV), (IHP2 P2SV);
      reflexivity.
Qed.

Lemma decr_none_is_none :
    forall (n : nat),
        map option_decr (repeat None n) = repeat None n.
Proof.
induction n.
reflexivity.
unfold repeat;
fold (repeat (@None nat) n);
unfold map;
fold (map option_decr).
rewrite IHn.
reflexivity.
Qed.

Lemma fill_none_is_triv :
    forall (P : ptree) (LP : list (list ptree)),
        option_fill P (repeat (@None nat) (length LP)) LP = LP.
Proof.
intros P.
induction LP.
reflexivity.
unfold length, repeat, option_fill.
rewrite <- IHLP at 3.
reflexivity.
Qed.

Lemma option_fill_app {A B : Type} :
    forall (LOB1 LOB2 : list (option B)) (LLA1 LLA2 : list (list A)) (a : A),
        length LOB1 = length LLA1 ->
            length LOB2 = length LLA2 ->
                option_fill a (LOB1 ++ LOB2) (LLA1 ++ LLA2) = option_fill a LOB1 LLA1 ++ option_fill a LOB2 LLA2.
Proof.
induction LOB1 as [ | [ b | ] LOB1];
intros LOB2 LLA1 LLA2 a EQ1 EQ2.
1 : destruct LLA1 as [ | LA LLA1 ].
    reflexivity.
    inversion EQ1.
all : destruct LLA1 as [ | LA LLA1 ];
      inversion EQ1 as [EQ1'];
      rewrite <- !app_comm_cons;
      unfold option_fill;
      fold @option_fill;
      rewrite (IHLOB1 _ _ _ _ EQ1' EQ2);
      reflexivity.
Qed.

(*
Lemma well_formed_option_null :
    forall (P : ptree),
        well_formed P ->
            (map option_decr (loop_traces P)) = repeat None (length (loop_traces P)).
Proof.
induction P;
intros [PSV [PEnd PLoops]];
unfold loops in PLoops;
fold loops in PLoops;
unfold loop_traces;
fold loop_traces.
1,2 : reflexivity.
1 : specialize (PLoops _ (or_introl eq_refl)) as [_ [kappa [_ [P [INP RST]]]]].
    apply in_single in INP.
    subst.
    inversion RST.
all : rewrite map_length.
      rewrite IHP.
      apply decr_none_is_none.
      destruct PSV as [PSV _].
      split.
      apply PSV.
      unfold loop_traces in PLoops;
      fold loop_traces in PLoops.
*)

Lemma ptree_con_l :
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha : ordinal),
        provable OC (phi :: phi :: gamma) delta alpha ->
            provable OC (phi :: gamma) delta alpha.
Proof.
intros OC gamma delta phi alpha [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (con_l phi P) _).
repeat split;
try assumption.
1 : refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ (phi :: phi :: gamma) (fun (A : formula) (IN : In A (phi :: gamma)) => (or_intror IN))) _).
    rewrite <- PG.
    apply (fst (struct_OC_app _ PSV)).
1 : apply (snd (struct_OC_app _ PSV)).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_con_r :
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha : ordinal),
        provable OC gamma (phi :: phi :: delta) alpha ->
            provable OC gamma (phi :: delta) alpha.
Proof.
intros OC gamma delta phi alpha [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (con_r phi P) _).
repeat split;
try assumption.
1 : apply (fst (struct_OC_app _ PSV)).
1 : refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ (phi :: phi :: delta) (fun (A : formula) (IN : In A (phi :: delta)) => (or_intror IN))) _).
    rewrite <- PD.
    apply (snd (struct_OC_app _ PSV)).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_ex_l : 
    forall (OC : constraint) (gamma delta : list formula) (n : nat) (alpha : ordinal),
        provable OC gamma delta alpha ->
            provable OC (bury gamma n) delta alpha.
Proof.
intros OC gamma delta n alpha [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (ex_l n P) _).
repeat split;
try assumption.
1 : refine (incl_tran (fun A => proj1 (flat_map_bury_incl A)) (fst (struct_OC_app _ PSV))).
1 : apply (snd (struct_OC_app _ PSV)).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_ex_r : 
    forall (OC : constraint) (gamma delta : list formula) (n : nat) (alpha : ordinal),
        provable OC gamma delta alpha ->
            provable OC gamma (bury delta n) alpha.
Proof.
intros OC gamma delta n alpha [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (ex_r n P) _).
repeat split;
try assumption.
1 : apply (fst (struct_OC_app _ PSV)).
1 : refine (incl_tran (fun A => proj1 (flat_map_bury_incl A)) (snd (struct_OC_app _ PSV))).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_wkn_l : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha: ordinal),
        incl (vars_in phi) (OC_list OC) ->
            provable OC gamma delta alpha ->
                provable OC (phi :: gamma) delta alpha.
Proof.
intros OC gamma delta phi alpha SUB [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (wkn_l phi P) _).
repeat split;
try assumption.
1 : apply (incl_app SUB (fst (struct_OC_app _ PSV))).
1 : apply (snd (struct_OC_app _ PSV)).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_wkn_r : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha: ordinal),
        incl (vars_in phi) (OC_list OC) ->
            provable OC gamma delta alpha ->
                provable OC gamma (phi :: delta) alpha.
Proof.
intros OC gamma delta phi alpha SUB [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (wkn_r phi P) _).
repeat split;
try assumption.
1 : apply (fst (struct_OC_app _ PSV)).
1 : apply (incl_app SUB (snd (struct_OC_app _ PSV))).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.


Lemma ptree_weaken_left : 
    forall (gamma delta sigma : list formula) (OC : constraint) (alpha: ordinal),
        incl (flat_map vars_in sigma) (OC_list OC) ->
            provable OC gamma delta alpha ->
                provable OC (gamma ++ sigma) delta alpha.
Proof.
intros gamma delta sigma.
revert gamma delta.
apply (rev_ind_type (fun sigma => forall (gamma delta : list formula) (OC : constraint) (alpha : ordinal), incl (flat_map vars_in sigma) (OC_list OC) -> provable OC gamma delta alpha -> provable OC (gamma ++ sigma) delta alpha)).
- intros gamma delta OC alpha SUB PP.
  rewrite app_nil_r.
  apply PP.
- intros phi sigma' IND gamma delta OC alpha SUB PP.
  rewrite app_assoc.
  rewrite <- (app_nil_l ((gamma ++ sigma') ++ [phi])), <- (@bury_type _ phi [] (gamma ++ sigma')), app_nil_l.
  apply ptree_ex_l, ptree_wkn_l, IND, PP;
  rewrite flat_map_app in SUB.
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_intror (in_or_app _ _ _ (or_introl IN))))).
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_introl IN))).
Qed.

Lemma ptree_weaken_right : 
    forall (gamma delta pi : list formula) (OC : constraint) (alpha: ordinal),
        incl (flat_map vars_in pi) (OC_list OC) ->
            provable OC gamma delta alpha ->
                provable OC gamma (delta ++ pi) alpha.
Proof.
intros gamma delta pi.
revert gamma delta.
apply (rev_ind_type (fun pi => forall (gamma delta : list formula) (OC : constraint) (alpha : ordinal), incl (flat_map vars_in pi) (OC_list OC) -> provable OC gamma delta alpha -> provable OC gamma (delta ++ pi) alpha)).
- intros gamma delta OC alpha SUB PP.
  rewrite app_nil_r.
  apply PP.
- intros phi pi' IND gamma delta OC alpha SUB PP.
  rewrite app_assoc.
  rewrite <- (app_nil_l ((delta ++ pi') ++ [phi])), <- (@bury_type _ phi [] (delta ++ pi')), app_nil_l.
  apply ptree_ex_r, ptree_wkn_r, IND, PP;
  rewrite flat_map_app in SUB.
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_intror (in_or_app _ _ _ (or_introl IN))))).
  refine (fun o IN => SUB _ (in_or_app _ (flat_map vars_in [phi]) _ (or_introl IN))).
Qed.

Lemma ptree_reset : 
    forall (gamma delta : list formula) (OC : constraint) (kappa : ovar) (alpha: ordinal),
        ~ In kappa (flat_map vars_used gamma) ->
            ~ In kappa (flat_map vars_used delta) ->
                OC_elt OC kappa ->
                    provable (restriction OC (children OC kappa) (children_subset OC kappa)) gamma delta alpha ->
                        provable OC gamma delta alpha.
Proof.
intros gamma delta OC kappa alpha NING NIND ELT [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (rst kappa P) _).
repeat split;
try assumption.
1 : apply (incl_tran (fst (struct_OC_app _ PSV))).
2 : apply (incl_tran (snd (struct_OC_app _ PSV))).
1,2 : rewrite POC;
      apply incl_filter.
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_bnd_l : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (lambda kappa : ovar) (alpha : ordinal),
        OC_rel OC lambda kappa = true ->
            provable OC (phi :: gamma) delta alpha ->
                provable OC ((bnd lambda kappa phi) :: gamma) delta alpha.
Proof.
intros OC gamma delta phi lambda kappa alpha rel [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (bnd_l phi lambda kappa P) _).
repeat split;
try assumption.
1 : { intros o IN.
      apply in_app_or in IN as [[IN1 | IN2] | IN3].
      - subst.
        apply (OC_null _ _ _ rel).
      - apply in_remove in IN2 as [IN2 _].
        apply (fst (struct_OC_app _ PSV)).
        rewrite PG.
        apply in_or_app, or_introl, IN2.
      - apply (fst (struct_OC_app _ PSV)).
        rewrite PG.
        apply in_or_app, or_intror, IN3. }
1 : apply (snd (struct_OC_app _ PSV)).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_bnd_r : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (lambda kappa : ovar) (alpha : ordinal) (NEW : ~ OC_elt OC lambda) (KIN : OC_elt OC kappa),
        ~ In lambda (flat_map vars_used gamma) ->
            ~ In lambda (flat_map vars_used (phi :: delta)) ->
                provable (add_fresh_child OC lambda kappa NEW KIN) gamma (phi :: delta) alpha ->
                    provable OC gamma ((bnd lambda kappa phi) :: delta) alpha.
Proof.
intros OC gamma delta phi lambda kappa alpha NEW KIN NING NIND [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (bnd_r phi lambda kappa P) _).
repeat split;
try assumption.
3 : refine (existT _ NEW (existT _ KIN POC)).
1 : intros o IN.
    pose proof ((fst (struct_OC_app _ PSV)) o IN) as PG_app.
    rewrite POC in PG_app.
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
      all : pose proof ((snd (struct_OC_app _ PSV)) o) as PD_app;
            rewrite PD, POC in PD_app;
            try specialize (PD_app (in_or_app _ _ _ (or_introl IN1)));
            try specialize (PD_app (in_or_app _ _ _ (or_intror IN2)));
            unfold OC_list, add_fresh_child, projT1 in PD_app;
            destruct PD_app as [EQ | PD_app];
            subst.
      1 : contradiction (NIND (in_or_app _ _ _ (or_introl (vars_in_is_used _ _ IN1)))).
      1 : apply PD_app.
      1 : contradiction (NIND (in_or_app _ _ _ (or_intror (vars_in_list_is_used _ _  IN2)))).
      1 : apply PD_app. }
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_imp_l : 
    forall (OC : constraint) (gamma delta : list formula) (phi psi : formula) (alpha1 alpha2 : ordinal),
        provable OC (psi :: gamma) delta alpha1 ->
            provable OC gamma (phi :: delta) alpha2 ->
                provable OC ((imp phi psi) :: gamma) delta (omax alpha1 alpha2).
Proof.
intros OC gamma delta phi psi alpha1 alpha2 [P1 [[[[[P1SV [P1End P1Loops]] P1G] P1D] P1OC] P1Deg]] [P2 [[[[[P2SV [P2End P2Loops]] P2G] P2D] P2OC] P2Deg]].
subst.
refine (existT _ (imp_l phi psi P1 P2) _).
repeat split;
try assumption.
1 : intros o IN.
    repeat apply in_app_or in IN as [IN | IN].
1 : rewrite <- P2OC.
    apply (snd (struct_OC_app _ P2SV)).
    rewrite P2D.
    apply (in_or_app _ _ _ (or_introl IN)).
1 : apply (fst (struct_OC_app _ P1SV)).
    rewrite P1G.
    apply (in_or_app _ _ _ (or_introl IN)).
1 : rewrite <- P2OC.
    apply (fst (struct_OC_app _ P2SV)), IN.
1 : apply (snd (struct_OC_app _ P1SV)).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat P1End as EQ1.
    pose proof Forall_eq_repeat P2End as EQ2.
    rewrite map_app, EQ1, EQ2, <- repeat_app, decr_none_is_none, repeat_app, <- EQ1, <- EQ2, Forall_app.
    apply (conj P1End P2End).
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat P1End as EQ1;
      pose proof Forall_eq_repeat P2End as EQ2;
      rewrite map_app, EQ1, EQ2, <- repeat_app, !map_length, (loop_traces_loop_length _ P1SV), (loop_traces_loop_length _ P2SV), repeat_app, (option_fill_app _ _ _ _ _ (repeat_length _ _) (repeat_length _ _)), !fill_none_is_triv in IN;
      apply (in_app_bor (list_eq_dec ptree_eq_dec)) in IN as [IN1 | IN2];
      try destruct (P1Loops _ IN1) as [SPLIT RST];
      try destruct (P2Loops _ IN2) as [SPLIT RST].
1,2 : apply SPLIT.
1,2 : apply RST.
Qed.

Lemma ptree_imp_r : 
    forall (OC : constraint) (gamma delta : list formula) (phi psi : formula) (alpha : ordinal),
        provable OC (phi :: gamma) (psi :: delta) alpha ->
            provable OC gamma ((imp phi psi) :: delta) alpha.
Proof.
intros OC gamma delta phi psi alpha [P [[[[[PSV [PEnd PLoops]] PG] PD] POC] PDeg]].
subst.
refine (existT _ (imp_r phi psi P) _).
repeat split;
try assumption.
1 : refine (incl_tran _ (fst (struct_OC_app _ PSV))).
    rewrite PG.
    apply (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ (phi :: gamma) (fun (A : formula) (IN : In A gamma) => (or_intror IN))).
1 : intros o IN.
    repeat apply in_app_or in IN as [IN | IN].
1 : apply (fst (struct_OC_app _ PSV)).
    rewrite PG.
    apply (in_or_app _ _ _ (or_introl IN)).
1 : apply (snd (struct_OC_app _ PSV)).
    rewrite PD.
    apply (in_or_app _ _ _ (or_introl IN)).
1 : apply (snd (struct_OC_app _ PSV)).
    rewrite PD.
    apply (in_or_app _ _ _ (or_intror IN)).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat PEnd as EQ.
    rewrite EQ, decr_none_is_none, <- EQ.
    apply PEnd.
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat PEnd as EQ;
      rewrite EQ, map_length, (loop_traces_loop_length _ PSV), fill_none_is_triv in IN;
      destruct (PLoops _ IN) as [SPLIT RST].
1 : apply SPLIT.
1 : apply RST.
Qed.

Lemma ptree_cut : 
    forall (OC : constraint) (gamma delta : list formula) (phi : formula) (alpha1 alpha2 : ordinal),
        provable OC gamma (phi :: delta) alpha1 ->
            provable OC (phi :: gamma) delta alpha2 ->
                provable OC gamma delta (omax (omax alpha1 alpha2) (oadd (num_conn phi) (cast (nat_ord 1)))).
Proof.
intros OC gamma delta phi alpha1 alpha2 [P1 [[[[[P1SV [P1End P1Loops]] P1G] P1D] P1OC] P1Deg]] [P2 [[[[[P2SV [P2End P2Loops]] P2G] P2D] P2OC] P2Deg]].
subst.
refine (existT _ (cut phi P1 P2) _).
repeat split;
try assumption.
1 : apply (fst (struct_OC_app _ P1SV)).
1 : rewrite <- P2OC.
    apply (snd (struct_OC_app _ P2SV)).
1 : unfold loop_traces; fold loop_traces.
    pose proof Forall_eq_repeat P1End as EQ1.
    pose proof Forall_eq_repeat P2End as EQ2.
    rewrite map_app, EQ1, EQ2, <- repeat_app, decr_none_is_none, repeat_app, <- EQ1, <- EQ2, Forall_app.
    apply (conj P1End P2End).
1,2 : unfold loops, loop_traces in IN;
      fold loop_traces loops in IN;
      pose proof Forall_eq_repeat P1End as EQ1;
      pose proof Forall_eq_repeat P2End as EQ2;
      rewrite map_app, EQ1, EQ2, <- repeat_app, !map_length, (loop_traces_loop_length _ P1SV), (loop_traces_loop_length _ P2SV), repeat_app, (option_fill_app _ _ _ _ _ (repeat_length _ _) (repeat_length _ _)), !fill_none_is_triv in IN;
      apply (in_app_bor (list_eq_dec ptree_eq_dec)) in IN as [IN1 | IN2];
      try destruct (P1Loops _ IN1) as [SPLIT RST];
      try destruct (P2Loops _ IN2) as [SPLIT RST].
1,2 : apply SPLIT.
1,2 : apply RST.
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
    apply IHn, ptree_con_l, (ptree_comm_left (double_perm_head)), PP.
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
    apply (ptree_comm_left (perm_trans _ _ _ (perm_sym PERM) (perm_sym double_perm_head))), ptree_weaken_left, (ptree_comm_left (perm_nodup form_eq_dec double_perm_head)), PP;
    destruct PP as [P [[[[[PSV PTerm] PG] PD] POC] PDeg]].
    refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (incl_tran SUB (incl_tran (fun B IN => perm_in form_eq_dec (perm_sym double_perm_head) _ IN) (fun B IN => proj2 (nodup_In _ _ _) IN)))) _).
    rewrite <- PG, <- POC.
    apply (fst (struct_OC_app _ PSV)).
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
    apply (ptree_comm_right (perm_trans _ _ _ (perm_sym PERM) (perm_sym double_perm_head))), ptree_weaken_right, (ptree_comm_right (perm_nodup form_eq_dec double_perm_head)), PP;
    destruct PP as [P [[[[[PSV PTerm] PG] PD] POC] PDeg]].
    refine (incl_tran (@flat_map_incl _ _ form_eq_dec nat_eq_dec vars_in _ _ (incl_tran SUB (incl_tran (fun B IN => perm_in form_eq_dec (perm_sym double_perm_head) _ IN) (fun B IN => proj2 (nodup_In form_eq_dec _ _) IN)))) _).
    rewrite <- PD, <- POC.
    apply (snd (struct_OC_app _ PSV)).
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

(*
Master destruct tactic.

1-2 : destruct PSV.
3 : destruct PSV as [PG_app PD_app].
4-9 : destruct PSV as [PSV [[[[[PG_app PD_app] PG] PD] POC] PDeg]].
10 : destruct PSV as [PSV [[[[[[[PG_app PD_app] PG] PD] KNING] KNIND] [KIN POC]] PDeg]].
11 : destruct PSV as [PSV [[[[[[PG_app PD_app] PG] PD] POC] POC_rel] PDeg]].
12 : destruct PSV as [PSV [[[[[[PG_app PD_app] PG] PD] [NEW [KIN POC]]] [NING NIND]] PDeg]].
13 : destruct PSV as [[P1SV P2SV] [[[[[[[[[PG_app PD_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2]].
14 : destruct PSV as [PSV [[[[[PG_app PD_app] PG] PD] POC] PDeg]].
15 : destruct PSV as [[P1SV P2SV] [[[[[[[[[PG_app PD_app] P1G] P1D] P1OC] P2G] P2D] P2OC] PDeg1] PDeg2]].

*)