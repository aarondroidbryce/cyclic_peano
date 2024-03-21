From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.

Require Import Lia.
Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.EqdepFacts.

Open Scope bool_scope.
Open Scope list_scope.

Import ListNotations.


Definition constraint := {L : list ovar & {R : (ovar -> ovar -> bool) & (NoDup L) /\ (forall (lambda kappa : ovar), R kappa lambda = true -> In kappa L /\ In lambda L) /\ StrictOrder (fun (lambda kappa : ovar) => R lambda kappa = true)}}.

Definition OC_list (OC : constraint) := (projT1 OC).

Definition OC_elt (OC : constraint) (lambda : ovar) : Prop := In lambda (OC_list OC).

Definition OC_rel (OC : constraint) := (projT1 (projT2 OC)).

Definition OC_unique (OC : constraint) := proj1 (projT2 (projT2 OC)).

Definition OC_null (OC : constraint) := proj1 (proj2 (projT2 (projT2 OC))).

Definition OC_order (OC : constraint) := proj2 (proj2 (projT2 (projT2 OC))).

Definition progeny (OC : constraint) (kappa : ovar) : list ovar := filter (fun (lambda : ovar) => OC_rel OC lambda kappa) (OC_list OC).

Definition child (OC : constraint) (lambda kappa : ovar) : Prop := OC_rel OC lambda kappa = true /\ (forall eta, OC_rel OC eta kappa = true -> OC_rel OC lambda eta = false).

Definition children (OC : constraint) (kappa : ovar) : list ovar := filter (fun (lambda : ovar) => forallb (fun eta => negb (OC_rel OC lambda eta)) (progeny OC kappa)) (progeny OC kappa).

Definition add_fresh (OC : constraint) (lambda : ovar) (NEW : ~ OC_elt OC lambda) : constraint := (existT _ (lambda :: OC_list OC) (existT _ (OC_rel OC) (conj ((proj2 (NoDup_cons_iff _ _)) (conj NEW (OC_unique OC))) (conj (fun (eta iota : ovar) (REL : OC_rel OC iota eta = true) => conj (or_intror (proj1 (OC_null OC eta iota REL))) (or_intror (proj2 (OC_null OC eta iota REL)))) (OC_order OC))))).

Definition add_fresh_child (OC : constraint) (lambda kappa : ovar) (NEW : ~ OC_elt OC lambda) (KIN : OC_elt OC kappa) : constraint.
Proof.
refine (existT _ (lambda :: OC_list OC) (existT _ (fun (eta iota : ovar) => OC_rel OC eta iota || ((nat_eqb eta lambda && nat_eqb kappa iota) || (nat_eqb eta lambda && OC_rel OC kappa iota))) (conj ((proj2 (NoDup_cons_iff _ _)) (conj NEW (OC_unique OC))) (conj _ _)))).
intros eta iota COND.
case (OC_rel OC iota eta) eqn:REL1.
- apply (conj (or_intror (proj1 (OC_null OC eta iota REL1))) (or_intror (proj2 (OC_null OC eta iota REL1)))).
- case (nat_eqb iota lambda) eqn:EQ.
  + apply nat_eqb_eq in EQ.
    destruct EQ.
    case (nat_eqb kappa eta) eqn:EQ.
    * apply nat_eqb_eq in EQ.
      destruct EQ.
      apply (conj (or_introl eq_refl) (or_intror KIN)).
    * apply (conj (or_introl eq_refl) (or_intror (proj2 (OC_null OC eta kappa COND)))).
  + inversion COND.
- pose proof (OC_order OC) as [IREF TRANS].
  split.
  + intros eta refl.
    case (OC_rel OC eta eta) eqn:FAL.
    * apply (IREF eta FAL).
    * case (nat_eqb eta lambda) eqn:EQ.
      --  apply nat_eqb_eq in EQ.
          destruct EQ.
          case (nat_eqb kappa eta) eqn:EQ.
          ++  apply nat_eqb_eq in EQ.
              destruct EQ.
              apply (NEW KIN).
          ++  apply (NEW (proj2 (OC_null OC _ _ refl))).
      --  inversion refl.
  + intros eta iota zeta LT1 LT2.
    case (nat_eqb iota lambda) eqn:EQ1;
    case (nat_eqb eta lambda) eqn:EQ2;
    try apply nat_eqb_eq in EQ1 as EQ3;
    try apply nat_eqb_eq in EQ2 as EQ4;
    try destruct EQ3;
    try destruct EQ4;
    try rewrite Bool.orb_false_r in *.
    * apply LT2.
    * contradiction (proj2 (OC_null OC _ _ LT1)).
    * repeat apply or_bool_prop in LT1 as [LT1 | LT1].
      --  contradiction (proj1 (OC_null OC _ _ LT1)).
      --  apply nat_eqb_eq in LT1.
          destruct LT1.
          rewrite LT2.
          repeat rewrite orb_true_r.
          reflexivity.
      --  unfold OC_rel at 2.
          rewrite (TRANS _ _ _ LT1 LT2).
          repeat rewrite orb_true_r.
          reflexivity.
    * apply (TRANS _ _ _ LT1 LT2).
Defined.

Definition restriction (OC : constraint) (L : list ovar) (SUB : incl L (OC_list OC)) : constraint.
Proof.
refine (existT _ (filter (fun (eta : ovar) => if in_dec nat_eq_dec eta L then false else true) (OC_list OC)) (existT _ (fun eta iota => OC_rel OC eta iota && (if in_dec nat_eq_dec eta L then false else true) && if in_dec nat_eq_dec iota L then false else true) (conj (NoDup_filter _ (OC_unique OC)) (conj _ _)))).
- intros lambda kappa COND.
  apply and_bool_prop in COND as [COND NIN2].
  apply and_bool_prop in COND as [REL NIN1].
  apply conj;
  apply filter_In;
  apply conj.
  + apply (proj1 (OC_null OC _ _ REL)).
  + apply NIN1.
  + apply (proj2 (OC_null OC _ _ REL)).
  + apply NIN2.
- pose proof (OC_order OC) as [IREF TRANS].
  split.
  + intros lambda refl.
    repeat apply and_bool_prop in refl as [refl _].
    apply (IREF lambda refl).
  + intros lambda kappa eta LT1 LT2.
    repeat apply and_bool_prop in LT1 as [LT1 ?NIN].
    repeat apply and_bool_prop in LT2 as [LT2 ?NIN].
    rewrite NIN0, NIN1, andb_true_r, andb_true_r.
    apply (TRANS _ _ _ LT1 LT2).
Defined.

(*
Definition assignment (OC : constraint) := {val : (ovar -> ord) & forall (lambda kappa : ovar), OC_rel OC lambda kappa = true -> ord_lt (val lambda) (val kappa)}.

Fixpoint valuate {OC : constraint} (ASN : assignment OC) (o : ordinal) : ord :=
match o with
| cast alpha => alpha
| assn ov => (projT1 ASN) ov
| oadd o1 o2 => ord_add (valuate ASN o1) (valuate ASN o2)
| omax o1 o2 => ord_max (valuate ASN o1) (valuate ASN o2)
end.
*)

Lemma null_strict : StrictOrder (fun (lambda kappa : ovar) => false = true).
Proof.
split.
exact (fun (lambda : ovar) => diff_false_true).
exact (fun (lambda kappa eta : ovar) (FAL1 FAL2 : false = true) => FAL1).
Defined.

Definition empty : constraint.
refine (existT _ [] (existT _ (fun (lambda kappa : ovar) => false) (conj (NoDup_nil _) (conj (fun (lambda kappa : ovar) (FAL : false = true) => _) null_strict)))).
inversion FAL.
Defined.

Lemma progeny_irref : forall (OC : constraint) (lambda : ovar), ~ In lambda (progeny OC lambda).
intros OC lambda FAL.
pose proof (OC_order OC) as [IREF TRANS].
apply filter_In in FAL as [ELT FAL].
apply (IREF lambda FAL).
Qed.

Lemma rel_progeny_hd : forall (OC : constraint) (lambda kappa : ovar), (OC_rel OC) lambda kappa = true -> forall (L : list ovar), incl L (progeny OC lambda) -> incl (L ++ [lambda]) (progeny OC kappa).
Proof.
intros OC lambda kappa REL1.
induction L;
intros SUB.
- rewrite app_nil_l.
  intros eta IN.
  destruct IN as [[] | FAL];
  try inversion FAL.
  apply (proj2 (filter_In _ _ _) (conj (proj1 (OC_null OC _ _ REL1)) REL1)).
- apply incl_cons_inv in SUB as [IN SUB].
  refine (incl_cons _ (IHL SUB)).
  apply filter_In in IN as [IN REL2].
  pose proof (OC_order OC) as [IREF TRANS]. 
  apply (proj2 (filter_In _ _ _) (conj IN (TRANS _ _ _ REL2 REL1))).
Qed.

(*
Lemma assignment_exists : forall (OC : constraint), assignment OC.
Proof.
intros OC.
exists (fun (lambda : ovar) => nat_ord (length (progeny OC lambda))).
intros lambda kappa REL.
apply nat_ord_lt.
unfold "<".
assert (length ((progeny OC lambda) ++ [lambda]) = S (length (progeny OC lambda))) as EQ.
{ rewrite app_length.
  unfold length at 2.
  rewrite <- plus_n_Sm, <- plus_n_O.
  reflexivity. }
rewrite <- EQ.
apply NoDup_incl_length.
- rewrite <- rev_involutive, rev_unit.
  apply NoDup_rev, NoDup_cons, NoDup_rev, NoDup_filter, (OC_unique OC).
  rewrite <- in_rev.
  apply progeny_irref.
- apply (rel_progeny_hd _ _ _ REL _ (incl_refl _)).
Defined.
*)

Definition children_subset : forall (OC : constraint) (kappa : ovar), incl (children OC kappa) (OC_list OC) := (fun OC kappa => incl_tran (incl_filter _ _) (incl_filter _ _)).

Lemma children_are_child : forall (OC : constraint) (lambda kappa : ovar), In lambda (children OC kappa) -> child OC lambda kappa.
Proof.
intros OC lambda kappa IN.
repeat apply filter_In in IN as [IN ?COND].
split.
apply COND0.
intros eta REL.
rewrite forallb_forall in COND.
specialize (COND eta (proj2 (filter_In _ _ _) (conj (proj1 (OC_null _ _ _ REL)) REL))).
apply negb_true_iff, COND.
Qed.

Lemma all_child_are_children : forall (OC : constraint) (lambda kappa : ovar), child OC lambda kappa -> In lambda (children OC kappa).
Proof.
intros OC lambda kappa [REL COND].
apply filter_In.
refine (conj (proj2 (filter_In _ _ _) (conj (proj1 (OC_null OC _ _ REL)) REL)) _).
apply forallb_forall.
intros eta IN.
apply filter_In in IN as [_ REL'].
apply negb_true_iff, COND, REL'.
Qed.

Lemma rel_eq_dec : forall (OC1 OC2 : constraint), (OC_list OC1) = (OC_list OC2) -> {forall (lambda kappa : ovar), OC_rel OC1 lambda kappa = OC_rel OC2 lambda kappa} + {exists (lambda kappa : ovar), OC_rel OC1 lambda kappa <> OC_rel OC2 lambda kappa}.
Proof.
intros OC1 OC2 EQ.
destruct OC1 as [L1 [R1 [NDL1 [NULL1 ORD1]]]], OC2 as [L2 [R2 [NDL2 [NULL2 ORD2]]]].
unfold OC_list, OC_rel, projT1, projT2 in *.
destruct EQ.
assert (forall (lambda kappa : ovar), (~ In lambda L1 \/ ~ In kappa L1) -> R1 lambda kappa = R2 lambda kappa) as NULL_EQUIV.
{ intros lambda kappa [NIN1 | NIN2];
  case (R1 lambda kappa) eqn:REL1;
  case (R2 lambda kappa) eqn:REL2;
  try reflexivity;
  try destruct (NULL1 kappa lambda REL1) as [IN1 IN2];
  try destruct (NULL2 kappa lambda REL2) as [IN1 IN2];
  contradiction. }
pose proof (Forall_Exists_dec (fun lambda => (uncurry R1) lambda = (uncurry R2) lambda) (fun a => bool_dec (uncurry R1 a) (uncurry R2 a)) (list_prod L1 L1)) as [ALL | EXISTS].
- rewrite Forall_forall in ALL.
  left.
  intros lambda kappa.
  case (in_dec nat_eq_dec lambda L1) as [IN1 | NIN].
  case (in_dec nat_eq_dec kappa L1) as [IN2 | NIN].
  apply (ALL (pair lambda kappa)).
  apply (in_prod _ _ _ _ IN1 IN2).
  apply NULL_EQUIV, or_intror, NIN.
  apply NULL_EQUIV, or_introl, NIN.
- right.
  apply Exists_exists in EXISTS as [[lambda kappa] [IN NE]].
  exists lambda, kappa.
  apply NE.
Qed.

Lemma constraint_eq_dec : forall (OC1 OC2 : constraint), {OC1 = OC2} + {OC1 <> OC2}.
Proof.
intros OC1 OC2.
case (list_eq_dec nat_eq_dec (OC_list OC1) (OC_list OC2)) as [EQL | NEL].
- case (rel_eq_dec OC1 OC2 EQL) as [EQR | NER].
  + left.
    assert (OC_rel OC1 = OC_rel OC2) as EQR'.
    { apply functional_extensionality. intros lambda. apply functional_extensionality. apply EQR. }
    destruct OC1 as [L1 [R1 C1]], OC2 as [L2 [R2 C2]].
    unfold OC_list, OC_rel, projT1, projT2 in *.
    destruct EQL, EQR'.
    rewrite (proof_irrelevance _ C1 C2).
    reflexivity.
  + right.
    intros FAL.
    destruct NER as [lambda [kappa NER]].
    apply NER.
    destruct FAL.
    reflexivity.
- right.
  intros FAL.
  apply NEL.
  destruct FAL.
  reflexivity.
Qed.

Lemma restriction_exlusion :
    forall (OC : constraint) (L1 L2 : list ovar) (SUB : incl L2 (OC_list OC)) (o : ovar),
        In o L2 ->
            incl L1 (OC_list (restriction OC L2 SUB)) ->
                ~ In o L1.
Proof.
intros OC L1.
revert OC.
induction L1;
intros OC L2 SUB1 o IN SUB2 FAL.
apply FAL.
destruct FAL as [FAL1 | FAL2].
1 : subst;
    specialize (SUB2 o (or_introl eq_refl)).
2 : specialize (SUB2 o (or_intror FAL2)).
all : unfold restriction, OC_list, projT1 in SUB2;
  apply filter_In in SUB2 as [_ SUB2];
  case (in_dec nat_eq_dec o L2) as [_ | FAL];
  try contradiction (FAL IN);
  inversion SUB2.
Qed.

Lemma constraint_eq_case :
    forall {OC1 OC2 : constraint},
        OC_list OC1 = OC_list OC2 ->
            OC_rel OC1 = OC_rel OC2 ->
                OC1 = OC2.
Proof.
intros [L1 [R1 [NDL1 [NULL1 ORD1]]]] [L2 [R2 [NDL2 [NULL2 ORD2]]]] EQ1 EQ2.
unfold OC_list, OC_rel, projT1, projT2 in *.
subst.
rewrite (proof_irrelevance _ NULL1 NULL2).
rewrite (proof_irrelevance _ NDL1 NDL2).
rewrite (proof_irrelevance _ ORD1 ORD2).
reflexivity.
Qed.

Lemma restriction_add_fresh_comm :
    forall (OC : constraint) (L : list ovar) (SUB : incl L (OC_list OC)) (o : ovar) (NEW : ~ OC_elt OC o) (NEW' : ~ OC_elt (restriction OC L SUB) o) (SUB' : incl L (OC_list (add_fresh OC o NEW))),
        ~ In o L ->
            add_fresh (restriction OC L SUB) o NEW' = restriction (add_fresh OC o NEW) L SUB'.
Proof.
intros OC L SUB o NEW NEW' SUB' NIN.
destruct OC as [L1 [R [NDL [NULL ORD]]]].
apply constraint_eq_case.
- unfold add_fresh at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold add_fresh at 1, OC_list, OC_rel, projT1, projT2.
  unfold filter.
  case (in_dec nat_eq_dec o L) as [IN | NIN'].
  contradiction (NIN IN).
  reflexivity.
- reflexivity.
Qed.

Lemma restriction_add_fresh_child_comm :
    forall (OC : constraint) (L : list ovar) (SUB : incl L (OC_list OC)) (o kappa : ovar) (KIN : OC_elt OC kappa) (KIN' : OC_elt (restriction OC L SUB) kappa) (NEW : ~ OC_elt OC o) (NEW' : ~ OC_elt (restriction OC L SUB) o) (SUB' : incl L (OC_list (add_fresh_child OC o kappa NEW KIN))),
        ~ In o L ->
        (add_fresh_child (restriction OC L SUB) o kappa NEW' KIN') = (restriction (add_fresh_child OC o kappa NEW KIN) L SUB').
Proof.
intros OC L SUB o kappa KIN KIN' NEW NEW' SUB' NIN.
destruct OC as [L1 [R [NDL [NULL ORD]]]].
apply constraint_eq_case.
- unfold add_fresh_child at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold add_fresh_child at 1, OC_list, OC_rel, projT1, projT2.
  unfold filter.
  case (in_dec nat_eq_dec o L) as [IN | NIN'].
  contradiction (NIN IN).
  reflexivity.
- unfold add_fresh_child at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold add_fresh_child at 1, OC_list, OC_rel, projT1, projT2.
  apply functional_extensionality.
  intros eta.
  apply functional_extensionality.
  intros rho.
  apply filter_In in KIN' as [KIN' COND].
  case (in_dec nat_eq_dec kappa L) as [_ | NIN'].
  inversion COND.
  case (in_dec nat_eq_dec rho L) as [IN1 | NIN1].
  + rewrite !Bool.andb_false_r, Bool.orb_false_l, Bool.orb_false_r.
    case (nat_eqb eta o) eqn:EQ.
    2 : reflexivity.
    apply nat_eqb_eq in EQ.
    subst.
    case (nat_eqb kappa rho) eqn:EQ.
    2 : reflexivity.
    apply nat_eqb_eq in EQ.
    subst.
    contradiction (NIN' IN1).
  + rewrite !Bool.andb_true_r.
    case (in_dec nat_eq_dec eta L) as [IN2 | NIN2].
    * rewrite !Bool.andb_false_r, Bool.orb_false_l.
      case (nat_eqb eta o) eqn:EQ1.
      apply nat_eqb_eq in EQ1.
      subst.
      contradiction (NIN IN2).
      reflexivity.
    * rewrite !Bool.andb_true_r.
      reflexivity.
Qed.

Lemma restriction_comm :
    forall (OC : constraint) (L : list ovar) {kappa : ovar} (SUB : incl L (OC_list OC)) (SUB' : incl L (OC_list (restriction OC (children OC kappa) (children_subset OC kappa)))) (o : ovar) (NEW : ~ OC_elt OC o) (NEW' : ~ OC_elt (restriction OC L SUB) o),
        ~ In o L ->
            ~ In kappa L ->
                (forall (eta : ovar), In eta L -> forall (rho : ovar), OC_rel OC eta rho = false /\ OC_rel OC rho eta = false) ->
                    restriction (restriction OC (children OC kappa) (children_subset OC kappa)) L SUB' = restriction (restriction OC L SUB) (children (restriction OC L SUB) kappa) (children_subset (restriction OC L SUB) kappa).
Proof.
intros OC L kappa SUB SUB' o NEW NEW' NIN NIN' NONE.
destruct OC as [L1 [R [NDL [NULL ORD]]]].
apply constraint_eq_case.
- unfold OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1 3.
  unfold OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1.
  unfold OC_list, OC_rel, projT1, projT2.
  unfold children at 4, progeny, OC_list, OC_rel, projT1, projT2.
  unfold restriction.
  unfold OC_list, OC_rel, projT1, projT2.
  unfold children at 1, progeny, OC_list, OC_rel, projT1, projT2.
  rewrite !double_filter.
  unfold OC_rel, projT1, projT2 in NONE.
  apply filter_ext.
  intros eta.
  case (in_dec nat_eq_dec eta L) as [IN1 | NIN1].
  + rewrite Bool.andb_false_l, Bool.andb_false_r.
    reflexivity.
  + rewrite Bool.andb_true_l.
    case (in_dec nat_eq_dec eta (filter (fun lambda : ovar => forallb (fun eta0 : ovar => negb (R lambda eta0)) (filter (fun lambda0 : ovar => R lambda0 kappa) L1)) (filter (fun lambda : ovar => R lambda kappa) L1))) as [IN2 | NIN2].
    * apply filter_In in IN2 as [IN2 COND1].
      apply filter_In in IN2 as [IN2 COND2].
      rewrite forallb_forall in COND1.
      case (in_dec nat_eq_dec eta (filter
      (fun lambda : ovar =>
       forallb
         (fun eta0 : ovar =>
          negb
            (R lambda eta0 &&
             (if in_dec nat_eq_dec lambda L then false else true) &&
             (if in_dec nat_eq_dec eta0 L then false else true)))
         (filter
            (fun lambda0 : ovar =>
             R lambda0 kappa &&
             (if in_dec nat_eq_dec lambda0 L then false else true) &&
             (if in_dec nat_eq_dec kappa L then false else true))
            (filter
               (fun eta0 : ovar =>
                if in_dec nat_eq_dec eta0 L then false else true) L1)))
      (filter
         (fun lambda : ovar =>
          R lambda kappa &&
          (if in_dec nat_eq_dec lambda L then false else true) &&
          (if in_dec nat_eq_dec kappa L then false else true))
         (filter
            (fun eta0 : ovar =>
             if in_dec nat_eq_dec eta0 L then false else true) L1)))) as [IN3 | NIN3].
      reflexivity.
      case (in_dec nat_eq_dec kappa L) as [FAL | _].
      contradiction (NIN' FAL).
      contradiction NIN3.
      apply filter_In, conj.
      apply filter_In, conj.
      apply filter_In, conj.
      apply IN2.
      case (in_dec nat_eq_dec eta L) as [FAL | _].
      contradiction (NIN1 FAL).
      reflexivity.
      rewrite COND2, Bool.andb_true_l, Bool.andb_true_r.
      case (in_dec nat_eq_dec eta L) as [FAL | _].
      contradiction (NIN1 FAL).
      reflexivity.
      apply forallb_forall.
      intros rho IN'.
      apply negb_true_iff.
      apply filter_In in IN' as [IN' COND3].
      apply filter_In in IN' as [IN' COND4].
      case (in_dec nat_eq_dec eta L) as [FAL | _].
      contradiction (NIN1 FAL).
      case (in_dec nat_eq_dec rho L) as [_ | HELP].
      inversion COND4.
      rewrite !Bool.andb_true_r in *.
      apply negb_true_iff.
      apply COND1.
      apply filter_In, (conj IN'), COND3.
    * case (in_dec nat_eq_dec eta
        (filter
           (fun lambda : ovar =>
            forallb
              (fun eta0 : ovar =>
               negb
                 (R lambda eta0 &&
                  (if in_dec nat_eq_dec lambda L then false else true) &&
                  (if in_dec nat_eq_dec eta0 L then false else true)))
              (filter
                 (fun lambda0 : ovar =>
                  R lambda0 kappa &&
                  (if in_dec nat_eq_dec lambda0 L then false else true) &&
                  (if in_dec nat_eq_dec kappa L then false else true))
                 (filter
                    (fun eta0 : ovar =>
                     if in_dec nat_eq_dec eta0 L then false else true) L1)))
           (filter
              (fun lambda : ovar =>
               R lambda kappa &&
               (if in_dec nat_eq_dec lambda L then false else true) &&
               (if in_dec nat_eq_dec kappa L then false else true))
              (filter
                 (fun eta0 : ovar =>
                  if in_dec nat_eq_dec eta0 L then false else true) L1)))) as [IN3 | NIN3].
      2 : reflexivity.
      apply filter_In in IN3 as [IN3 COND1].
      apply filter_In in IN3 as [IN3 COND2].
      apply filter_In in IN3 as [IN3 COND3].
      rewrite forallb_forall in COND1.
      case (in_dec nat_eq_dec eta L) as [FAL | _].
      contradiction (NIN1 FAL).
      case (in_dec nat_eq_dec kappa L) as [FAL | _].
      contradiction (NIN' FAL).
      rewrite !Bool.andb_true_r in *.
      contradiction NIN2.
      apply filter_In, conj.
      apply filter_In, (conj IN3), COND2.
      apply forallb_forall.
      intros rho IN.
      apply filter_In in IN as [IN REL].    
      specialize (COND1 rho).
      case (in_dec nat_eq_dec rho L) as [IN4 | NIN4].
      rewrite (proj1 (NONE _ IN4 kappa)) in REL.
      inversion REL.
      rewrite !Bool.andb_true_r in *.
      apply COND1.
      apply filter_In, conj.
      apply filter_In, (conj IN).
      case (in_dec nat_eq_dec rho L) as [FAL | _].
      contradiction (NIN4 FAL).
      reflexivity.
      rewrite REL.
      case (in_dec nat_eq_dec rho L) as [FAL | _].
      contradiction (NIN4 FAL).
      reflexivity.

- unfold OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1 3.
  unfold OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold children at 4, progeny, OC_list, OC_rel, projT1, projT2.
  unfold children at 1, progeny, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold children at 5, progeny, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold children at 7, progeny, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  unfold restriction at 1, OC_list, OC_rel, projT1, projT2.
  apply functional_extensionality.
  intros eta.
  apply functional_extensionality.
  intros rho.
  unfold OC_elt, OC_list, OC_rel, projT1, projT2 in *.
  case (in_dec nat_eq_dec rho L) as [INR | NINR].
  rewrite !Bool.andb_false_r, !Bool.andb_false_l.
  reflexivity.
  case (in_dec nat_eq_dec eta L) as [INE | NINE].
  rewrite !Bool.andb_false_r, !Bool.andb_false_l.
  reflexivity.
  case (R eta rho) eqn:REL.
  2 : reflexivity.
  rewrite !Bool.andb_true_l.
  case (in_dec nat_eq_dec eta
    (filter
       (fun lambda : ovar =>
        forallb (fun eta0 : ovar => negb (R lambda eta0))
          (filter (fun lambda0 : ovar => R lambda0 kappa) L1))
       (filter (fun lambda : ovar => R lambda kappa) L1))) as [IN1 | NIN1].
  + rewrite Bool.andb_false_l.
    apply filter_In in IN1 as [IN1 COND1].
    apply filter_In in IN1 as [IN1 COND2].
    rewrite forallb_forall in COND1.
    case (in_dec nat_eq_dec eta
    (filter
       (fun lambda : ovar =>
        forallb
          (fun eta0 : ovar =>
           negb
             (R lambda eta0 &&
              (if in_dec nat_eq_dec lambda L then false else true) &&
              (if in_dec nat_eq_dec eta0 L then false else true)))
          (filter
             (fun lambda0 : ovar =>
              R lambda0 kappa &&
              (if in_dec nat_eq_dec lambda0 L then false else true) &&
              (if in_dec nat_eq_dec kappa L then false else true))
             (filter
                (fun eta0 : ovar =>
                 if in_dec nat_eq_dec eta0 L then false else true) L1)))
       (filter
          (fun lambda : ovar =>
           R lambda kappa &&
           (if in_dec nat_eq_dec lambda L then false else true) &&
           (if in_dec nat_eq_dec kappa L then false else true))
          (filter
             (fun eta0 : ovar =>
              if in_dec nat_eq_dec eta0 L then false else true) L1)))) as [IN2 | NIN2].
    reflexivity.
    contradiction NIN2.
    apply filter_In, conj.
    apply filter_In, conj.
    apply filter_In, conj.
    apply IN1.
    case (in_dec nat_eq_dec eta L) as [FAL | _].
    contradict (NINE FAL).
    reflexivity.
    rewrite COND2.
    case (in_dec nat_eq_dec eta L) as [FAL | _].
    contradict (NINE FAL).
    case (in_dec nat_eq_dec kappa L) as [FAL | _].
    contradict (NIN' FAL).
    reflexivity.
    apply forallb_forall.
    intros zeta IN.
    apply negb_true_iff.
    apply filter_In in IN as [IN COND3].
    apply filter_In in IN as [IN COND4].
    case (in_dec nat_eq_dec eta L) as [FAL | _].
    contradict (NINE FAL).
    case (in_dec nat_eq_dec kappa L) as [FAL | _].
    contradict (NIN' FAL).
    case (in_dec nat_eq_dec zeta L) as [_ | NIN3].
    inversion COND4.
    rewrite !Bool.andb_true_r in *.
    apply negb_true_iff, COND1, filter_In, (conj IN), COND3.
  + rewrite !Bool.andb_true_l.
    case (in_dec nat_eq_dec rho
    (filter
       (fun lambda : ovar =>
        forallb (fun eta0 : ovar => negb (R lambda eta0))
          (filter (fun lambda0 : ovar => R lambda0 kappa) L1))
       (filter (fun lambda : ovar => R lambda kappa) L1))) as [IN2 | NIN2].
    * rewrite !Bool.andb_false_l.
      apply filter_In in IN2 as [IN2 COND1].
      apply filter_In in IN2 as [IN2 COND2].
      rewrite forallb_forall in COND1.
      case (in_dec nat_eq_dec eta
          (filter
             (fun lambda : ovar =>
              forallb
                (fun eta0 : ovar =>
                 negb
                   (R lambda eta0 &&
                    (if in_dec nat_eq_dec lambda L then false else true) &&
                    (if in_dec nat_eq_dec eta0 L then false else true)))
                (filter
                   (fun lambda0 : ovar =>
                    R lambda0 kappa &&
                    (if in_dec nat_eq_dec lambda0 L then false else true) &&
                    (if in_dec nat_eq_dec kappa L then false else true))
                   (filter
                      (fun eta0 : ovar =>
                       if in_dec nat_eq_dec eta0 L then false else true) L1)))
             (filter
                (fun lambda : ovar =>
                 R lambda kappa &&
                 (if in_dec nat_eq_dec lambda L then false else true) &&
                 (if in_dec nat_eq_dec kappa L then false else true))
                (filter
                   (fun eta0 : ovar =>
                    if in_dec nat_eq_dec eta0 L then false else true) L1)))) as [IN3 | NIN3].
      reflexivity.
      case (in_dec nat_eq_dec rho
          (filter
             (fun lambda : ovar =>
              forallb
                (fun eta0 : ovar =>
                 negb
                   (R lambda eta0 &&
                    (if in_dec nat_eq_dec lambda L then false else true) &&
                    (if in_dec nat_eq_dec eta0 L then false else true)))
                (filter
                   (fun lambda0 : ovar =>
                    R lambda0 kappa &&
                    (if in_dec nat_eq_dec lambda0 L then false else true) &&
                    (if in_dec nat_eq_dec kappa L then false else true))
                   (filter
                      (fun eta0 : ovar =>
                       if in_dec nat_eq_dec eta0 L then false else true) L1)))
             (filter
                (fun lambda : ovar =>
                 R lambda kappa &&
                 (if in_dec nat_eq_dec lambda L then false else true) &&
                 (if in_dec nat_eq_dec kappa L then false else true))
                (filter
                   (fun eta0 : ovar =>
                    if in_dec nat_eq_dec eta0 L then false else true) L1)))) as [IN4 | NIN4].
      reflexivity.
      case (in_dec nat_eq_dec kappa L) as [FAL | _].
      contradiction (NIN' FAL).
      contradiction NIN4.
      apply filter_In, conj.
      apply filter_In, conj.
      apply filter_In, conj.
      apply IN2.
      case (in_dec nat_eq_dec rho L) as [FAL | _].
      contradiction (NINR FAL).
      reflexivity.
      rewrite COND2.
      case (in_dec nat_eq_dec rho L) as [FAL | _].
      contradiction (NINR FAL).
      reflexivity.
      apply forallb_forall.
      intros zeta IN.
      apply filter_In in IN as [IN COND3].
      apply filter_In in IN as [IN COND4].
      case (in_dec nat_eq_dec rho L) as [FAL | _].
      contradiction (NINR FAL).
      case (in_dec nat_eq_dec zeta L) as [_ | NIN5].
      inversion COND4.
      rewrite !Bool.andb_true_r in *.
      apply COND1, filter_In, (conj IN), COND3.
    * rewrite Bool.andb_true_l.
      case (in_dec nat_eq_dec eta
      (filter
         (fun lambda : ovar =>
          forallb
            (fun eta0 : ovar =>
             negb
               (R lambda eta0 &&
                (if in_dec nat_eq_dec lambda L then false else true) &&
                (if in_dec nat_eq_dec eta0 L then false else true)))
            (filter
               (fun lambda0 : ovar =>
                R lambda0 kappa &&
                (if in_dec nat_eq_dec lambda0 L then false else true) &&
                (if in_dec nat_eq_dec kappa L then false else true))
               (filter
                  (fun eta0 : ovar =>
                   if in_dec nat_eq_dec eta0 L then false else true) L1)))
         (filter
            (fun lambda : ovar =>
             R lambda kappa &&
             (if in_dec nat_eq_dec lambda L then false else true) &&
             (if in_dec nat_eq_dec kappa L then false else true))
            (filter
               (fun eta0 : ovar =>
                if in_dec nat_eq_dec eta0 L then false else true) L1)))) as [IN3 | NIN3].
      --  apply filter_In in IN3 as [IN3 COND1].
          apply filter_In in IN3 as [IN3 COND2].
          apply filter_In in IN3 as [IN3 COND3].
          case (in_dec nat_eq_dec eta L) as [FAL | _].
          contradiction (NINE FAL).
          clear COND3.
          rewrite forallb_forall in COND1.
          contradiction NIN1.
          case (in_dec nat_eq_dec kappa L) as [FAL | _].
          contradiction (NIN' FAL).
          rewrite !Bool.andb_true_r in *.
          apply filter_In, conj.
          apply filter_In, (conj IN3).
          apply COND2.
          apply forallb_forall.
          intros zeta IN.
          apply filter_In in IN as [IN COND3].
          specialize (COND1 zeta).
          case (in_dec nat_eq_dec zeta L) as [IN4 | NIN4].
          rewrite (proj1 (NONE _ IN4 kappa)) in COND3.
          inversion COND3.
          rewrite !Bool.andb_true_r in *.
          apply COND1.
          apply filter_In, conj.
          apply filter_In, (conj IN).
          case (in_dec nat_eq_dec zeta L) as [FAL | _].
          contradiction (NIN4 FAL).
          reflexivity.
          rewrite COND3.
          case (in_dec nat_eq_dec zeta L) as [FAL | _].
          contradiction (NIN4 FAL).
          reflexivity.
    --  case (in_dec nat_eq_dec rho
          (filter
             (fun lambda : ovar =>
              forallb
                (fun eta0 : ovar =>
                 negb
                   (R lambda eta0 &&
                    (if in_dec nat_eq_dec lambda L then false else true) &&
                    (if in_dec nat_eq_dec eta0 L then false else true)))
                (filter
                   (fun lambda0 : ovar =>
                    R lambda0 kappa &&
                    (if in_dec nat_eq_dec lambda0 L then false else true) &&
                    (if in_dec nat_eq_dec kappa L then false else true))
                   (filter
                      (fun eta0 : ovar =>
                       if in_dec nat_eq_dec eta0 L then false else true) L1)))
             (filter
                (fun lambda : ovar =>
                 R lambda kappa &&
                 (if in_dec nat_eq_dec lambda L then false else true) &&
                 (if in_dec nat_eq_dec kappa L then false else true))
                (filter
                   (fun eta0 : ovar =>
                    if in_dec nat_eq_dec eta0 L then false else true) L1)))) as [IN4 | NIN4].
        2 : reflexivity.
        apply filter_In in IN4 as [IN4 COND1].
        apply filter_In in IN4 as [IN4 COND2].
        apply filter_In in IN4 as [IN4 COND3].
        case (in_dec nat_eq_dec rho L) as [FAL | _].
        contradiction (NINR FAL).
        clear COND3.
        case (in_dec nat_eq_dec kappa L) as [FAL | _].
        contradiction (NIN' FAL).
        rewrite !Bool.andb_true_r in *.
        rewrite forallb_forall in COND1.
        contradiction NIN2.
        apply filter_In, conj.
        apply filter_In, (conj IN4), COND2.
        apply forallb_forall.
        intros zeta IN.
        apply filter_In in IN as [IN COND3].
        specialize (COND1 zeta).
        case (in_dec nat_eq_dec zeta L) as [IN5 | NIN5].
        rewrite (proj1 (NONE _ IN5 kappa)) in COND3.
        inversion COND3.
        rewrite !Bool.andb_true_r in *.
        apply COND1.
        apply filter_In, conj.
        apply filter_In, (conj IN).
        case (in_dec nat_eq_dec zeta L) as [FAL | _].
        contradiction (NIN5 FAL).
        reflexivity.
        rewrite COND3.
        case (in_dec nat_eq_dec zeta L) as [FAL | _].
        contradiction (NIN5 FAL).
        reflexivity.
Qed.

(*
Lemma restriction_add_fresh_comm : 
    restriction (add_fresh OC' lambda' NEW')
        (children (add_fresh OC' lambda' NEW') kappa)
            (children_subset (add_fresh OC' lambda' NEW') kappa)
           =
    (add_fresh (restriction OC' (children OC' kappa) (children_subset OC kappa) lambda NEW')
*)

(*
Definition constraint_type (OC : constraint) : Type := {o : ovar & OC_elt OC o}.

Lemma constraint_type_eq_dec (OC : constraint) :
    forall (o1 o2 : constraint_type OC),
        {o1 = o2} + {o1 <> o2}.
Proof.
intros [o1 IN1] [o2 IN2].
destruct OC as [L [REL [ND [NULL ORD]]]].
unfold OC_elt, OC_list, projT1 in *.
case (nat_eq_dec o1 o2) as [EQ | NE].
- left.
  subst.
  rewrite (proof_irrelevance _ IN1 IN2).
  reflexivity.
- right.
  intros FAL.
  apply NE.
  inversion FAL.
  reflexivity.
Qed.

Definition constraint_type_eqb {OC : constraint} (o1 o2 : constraint_type OC) : bool :=
match o1, o2 with
| (existT _ o1' _), (existT _ o2' _) => nat_eqb o1' o2'
end.

Lemma constraint_type_eqb_eq {OC : constraint} :
    forall (o1 o2 : constraint_type OC),
        constraint_type_eqb o1 o2 = true <-> o1 = o2.
Proof.
intros [o1 IN1] [o2 IN2].
split;
intros EQ.
unfold constraint_type_eqb in EQ.
apply nat_eqb_eq in EQ.
subst.
rewrite (proof_irrelevance _ IN1 IN2).
reflexivity.
inversion EQ as [EQ'].
subst.
unfold constraint_type_eqb.
apply nat_eqb_refl.
Qed.

Lemma constraint_type_eq_proj {OC : constraint} :
    forall (o1 o2 : constraint_type OC),
        projT1 o1 = projT1 o2 <-> o1 = o2.
Proof.
intros [o1 IN1] [o2 IN2];
split;
intros EQ;
unfold projT1 in *;
subst.
rewrite (proof_irrelevance _ IN1 IN2).
reflexivity.
inversion EQ as [EQ'].
reflexivity.
Qed.

Lemma sig_dec {OC1 OC2 : constraint} :
    forall (f g : (constraint_type OC1) -> constraint_type OC2),
        {f = g} + {f <> g}.
Proof.
intros f g.
assert (forall (F : constraint_type OC1 -> Type), (forall (o : ovar) (IN : OC_elt OC1 o), F (existT _ o IN)) -> forall (v : constraint_type OC1), F v) as FUNEXT.
{ intros F HYP v.
  destruct v as [o IN].
  apply HYP. }
assert ({forall (v : constraint_type OC1), f v = g v} + {~ forall (v : constraint_type OC1), f v = g v}) as [ALL | EXISTS].
{ assert ({forall v, constraint_type_eqb (f v) (g v) = true} + {~ forall v, constraint_type_eqb (f v) (g v) = true}) as [ALL | EXISTS].
  { assert ({forall (o : ovar) (IN : OC_elt OC1 o), constraint_type_eqb (f (existT _ o IN)) (g (existT _ o IN)) = true} + {~ forall (o : ovar) (IN : OC_elt OC1 o), constraint_type_eqb (f (existT _ o IN)) (g (existT _ o IN)) = true}) as [ALL | EXISTS].
    { assert (forall x : ovar,
    {(fun o : ovar =>
      forall IN : In o (OC_list OC1),
      constraint_type_eqb
        (f (existT (fun o0 : ovar => OC_elt OC1 o0) o IN))
        (g (existT (fun o0 : ovar => OC_elt OC1 o0) o IN)) = true) x} +
    {~
     (fun o : ovar =>
      forall IN : In o (OC_list OC1),
      constraint_type_eqb
        (f (existT (fun o0 : ovar => OC_elt OC1 o0) o IN))
        (g (existT (fun o0 : ovar => OC_elt OC1 o0) o IN)) = true) x}) as HELP.
    { intros o.
      case (in_dec nat_eq_dec o (OC_list OC1)) as [IN | NIN].
      case (constraint_type_eqb (f (existT _ o IN)) (g (existT _ o IN))) eqn:b.
      left.
      intros IN'.
      rewrite (proof_irrelevance _ IN' IN).
      apply b.
      right.
      intros FAL.
      rewrite (FAL IN) in b.
      inversion b.
      left.
      intros IN.
      contradiction (NIN IN). }
    destruct (Forall_dec (fun (o : ovar) => forall (IN : In o (OC_list OC1)), (constraint_type_eqb (f (existT _ o IN)) (g (existT _ o IN))) = true) HELP (OC_list OC1)) as [ALL | EXISTS].
    left.
    rewrite Forall_forall in ALL.
    intros o IN.
    apply ALL, IN.
    right.
    intros FAL.
    apply EXISTS.
    rewrite Forall_forall.
    intros o IN IN'.
    rewrite (proof_irrelevance _ IN' IN).
    apply FAL. }
    left.
    apply FUNEXT, ALL.
    right.
    intros FAL.
    apply EXISTS.
    intros o IN.
    apply FAL. }
  left.
  intros v.
  apply constraint_type_eqb_eq, ALL.
  right.
  intros FAL.
  apply EXISTS. 
  intros v.
  apply constraint_type_eqb_eq, FAL. }

- apply left, functional_extensionality, ALL.
- right.
  intros FAL.
  apply EXISTS.
  intros v.
  destruct FAL.
  reflexivity.
Qed.

Definition sig_generalise {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) : ovar -> ovar := fun o =>
match
in_dec nat_eq_dec o (OC_list OC1) with
| left IN => projT1 (sig (existT _ o IN))
| right _ => o
end.

Definition coherent {OC1 OC2 : constraint} (sig : constraint_type OC2 -> constraint_type OC1) : Prop :=
      (forall (lambda : constraint_type OC2),
          OC_elt OC1 (projT1 (sig lambda))) /\
      (forall (lambda kappa : constraint_type OC2),
          OC_rel OC2 (projT1 lambda) (projT1 kappa) = true <-> OC_rel OC1 (projT1 (sig lambda)) (projT1 (sig kappa)) = true) /\
          (forall (lambda kappa : constraint_type OC2),
              precedence nat_eq_dec (OC_list OC2) (projT1 lambda) (projT1 kappa) = true ->
                  precedence nat_eq_dec (OC_list OC1) (projT1 (sig lambda)) (projT1 (sig kappa)) = true).

Definition coherent_bijection {OC1 OC2 : constraint} (sig : constraint_type OC2 -> constraint_type OC1) : Type :=
  ((forall (lambda : constraint_type OC2),
      OC_elt OC1 (projT1 (sig lambda))) *
  (forall (lambda : constraint_type OC1),
      {kappa : constraint_type OC2 & sig kappa = lambda}) *
  (forall (lambda kappa : constraint_type OC2),
      OC_rel OC2 (projT1 lambda) (projT1 kappa) = true <-> OC_rel OC1 (projT1 (sig lambda)) (projT1 (sig kappa)) = true) *
      (forall (lambda kappa : constraint_type OC2),
          precedence nat_eq_dec (OC_list OC2) (projT1 lambda) (projT1 kappa) = true ->
              precedence nat_eq_dec (OC_list OC1) (projT1 (sig lambda)) (projT1 (sig kappa)) = true))%type.

(*
Lemma coherent_is_injective_aux {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) :
    coherent sig ->
        forall (o1 o2 : constraint_type OC1),
            o1 = o2 <-> sig o1 = sig o2.
Proof.
intros [SUB [REL_iff ORD]] o1 o2.
split;
intros EQ.
subst.
reflexivity.
destruct (precedence_cases nat_eq_dec (projT2 o1) (projT2 o2)) as [[Prec1 | Prec2] | EQ'].
- pose proof (ORD _ _ Prec1) as FAL.
  rewrite EQ in FAL.
  contradiction (eq_true_false_abs _ FAL (NoDup_precedence_asym _ (OC_unique OC2) FAL)).
- pose proof (ORD _ _ Prec2) as FAL.
  rewrite EQ in FAL.
  contradiction (eq_true_false_abs _ FAL (NoDup_precedence_asym _ (OC_unique OC2) FAL)).
- destruct o1 as [o1 IN1], o2 as [o2 IN2].
  unfold projT1 in EQ'.
  subst.
  rewrite (proof_irrelevance _ IN1 IN2).
  reflexivity.
Qed.
*)

Lemma coherent_bijective_is_injective {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) :
    coherent_bijection sig ->
        forall (o1 o2 : constraint_type OC1),
            o1 = o2 <-> sig o1 = sig o2.
Proof.
intros [[[INJ SUR] REL_iff] ORD] o1 o2.
split;
intros EQ.
subst.
reflexivity.
destruct (precedence_cases nat_eq_dec (projT2 o1) (projT2 o2)) as [[Prec1 | Prec2] | EQ'].
- pose proof (ORD _ _ Prec1) as FAL.
  rewrite EQ in FAL.
  contradiction (eq_true_false_abs _ FAL (NoDup_precedence_asym _ (OC_unique OC2) FAL)).
- pose proof (ORD _ _ Prec2) as FAL.
  rewrite EQ in FAL.
  contradiction (eq_true_false_abs _ FAL (NoDup_precedence_asym _ (OC_unique OC2) FAL)).
- destruct o1 as [o1 IN1], o2 as [o2 IN2].
  unfold projT1 in EQ'.
  subst.
  rewrite (proof_irrelevance _ IN1 IN2).
  reflexivity.
Qed.

Definition sig_inverse_single {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (o2 : constraint_type OC2) := {o1 : constraint_type OC1 & sig o1 = o2}.

Definition sig_image {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (o2 : constraint_type OC2) : Prop := inhabited (sig_inverse_single sig o2).

(*
Lemma sig_inverse_single_is_unique {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (o : constraint_type OC2) :
    coherent sig ->
        sig_image sig o ->
            forall (o1 o2 : sig_inverse_single sig o),
                o1 = o2.
Proof.
intros COH [[o' EQ]] [o1 EQ1] [o2 EQ2].
assert (sig o1 = sig o2) as EQ'.
{ rewrite EQ1, EQ2.
  reflexivity. }
apply (coherent_is_injective_aux _ COH) in EQ'.
subst.
rewrite (proof_irrelevance _ EQ1 EQ2).
reflexivity.
Qed.
*)

(*
Lemma sig_image_dec {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (o : constraint_type OC2) : {sig_image sig o} + {~ sig_image sig o}.
Proof.
unfold sig_image.
destruct (fun X => Forall_Exists_dec (fun (o1 : ovar) => forall (IN : OC_elt OC1 o1), (sig (existT _ o1 IN)) <> o) X (OC_list OC1)) as [FORALL | EXISTS].
- intros o'.
  case (in_dec nat_eq_dec o' (OC_list OC1)) as [IN | NIN].
  case (constraint_type_eq_dec _ (sig (existT (OC_elt OC1) o' IN)) o) as [EQ | NE].
  right.
  intros FAL.
  apply (FAL IN), EQ.
  left.
  intros IN'.
  rewrite (proof_irrelevance _ IN' IN).
  apply NE.
  left.
  intros FAL1 FAL2.
  apply NIN, FAL1.
- right.
  intros [[[o1 IN] FAL]].
  rewrite Forall_forall in FORALL.
  apply (FORALL o1 IN IN), FAL.
- left.
  apply Exists_exists in EXISTS as [o1 [IN NNEQ]].
  constructor.
  exists (existT _ o1 IN).
  case (constraint_type_eq_dec _ (sig (existT (OC_elt OC1) o1 IN)) o) as [EQ | NE].
  apply EQ.
  contradict NNEQ.
  intros IN'.
  rewrite (proof_irrelevance _ IN' IN).
  apply NE.
Qed.
*)

Lemma sig_image_dec_alt {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (o : constraint_type OC2) : {o1 : constraint_type OC1 & sig o1 = o} + {forall o1 : constraint_type OC1, sig o1 <> o}.
Proof.
destruct (fun X => Forall_Exists_dec (fun (o1 : ovar) => forall (IN : OC_elt OC1 o1), (sig (existT _ o1 IN)) <> o) X (OC_list OC1)) as [FORALL | EXISTS].
- intros o'.
  case (in_dec nat_eq_dec o' (OC_list OC1)) as [IN | NIN].
  case (constraint_type_eq_dec _ (sig (existT (OC_elt OC1) o' IN)) o) as [EQ | NE].
  right.
  intros FAL.
  apply (FAL IN), EQ.
  left.
  intros IN'.
  rewrite (proof_irrelevance _ IN' IN).
  apply NE.
  left.
  intros FAL1 FAL2.
  apply NIN, FAL1.
- right.
  intros [o1 IN] FAL.
  rewrite Forall_forall in FORALL.
  apply (FORALL o1 IN IN), FAL.
- left.
  assert ({o1 : ovar & OC_elt OC1 o1 /\ ~ (forall (IN : OC_elt OC1 o1), sig (existT (OC_elt OC1) o1 IN) <> o)}) as [o1 [IN NNEQ]].
  { refine (Exists_sig _ EXISTS).
    intros o'.
    case (in_dec nat_eq_dec o' (OC_list OC1)) as [IN | NIN].
    case (constraint_type_eq_dec _ (sig (existT (OC_elt OC1) o' IN)) o) as [EQ | NE].
    left.
    intros FAL.
    apply (FAL IN), EQ.
    right.
    intros FAL.
    apply FAL.
    intros IN'.
    rewrite (proof_irrelevance _ IN' IN).
    apply NE.
    right.
    intros FAL.
    apply FAL.
    intros IN'.
    contradiction. }
  refine (existT _ (existT _ o1 IN) _).
  case (constraint_type_eq_dec _ (sig (existT (OC_elt OC1) o1 IN)) o) as [EQ | NE].
  apply EQ.
  contradict NNEQ.
  intros IN'.
  rewrite (proof_irrelevance _ IN' IN).
  apply NE.
Qed.

Definition sig_inverse {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) : ovar -> ovar := fun o =>
match in_dec nat_eq_dec o (OC_list OC2) with
| left IN2 => match sig_image_dec_alt sig (existT _ o IN2) with
    | inleft IN1 => (projT1 (projT1 IN1))
    | inright _ => o
    end
| right _ => o
end.

(*
Program Definition sig_inverse_true {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (COH : coherent_bijection sig) : constraint_type OC2 -> constraint_type OC1 := fun o2 =>
match sig_image_dec_alt sig o2 with
| inleft IN => (projT1 IN)
| inright NE => _
end.
Next Obligation.
destruct COH as [[[INJ SUR] REL_iff] PREC].
destruct (SUR o2) as [o1 EQ].
contradiction (NE _ EQ).
Defined.

Lemma coherent_bijection_sig_inverse_better {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (COH : coherent_bijection sig) :
    forall (o : constraint_type OC2),
        sig (sig_inverse_true sig COH o) = o.
Proof.
intros o.
destruct COH as [[[INJ SUR] REL_iff] PREC].
unfold sig_inverse_true.
case (sig_image_dec_alt sig o) as [[[o1 IN1] EQ] | NE].
- unfold projT1.
  apply EQ.
- destruct (SUR o) as [o1 EQ].
  contradiction (NE _ EQ).
Qed.

Lemma coherent_bijection_sig_inverse_aux {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (COH : coherent_bijection sig) :
    forall (o : constraint_type OC2),
        (sig_generalise sig) (projT1 (sig_inverse_true sig COH o)) = (projT1 o).
Proof.
intros o.
destruct COH as [[[INJ SUR] REL_iff] PREC].
unfold sig_inverse_true, sig_generalise.
case (sig_image_dec_alt sig o) as [[[o1 IN1] EQ] | NE].
- unfold projT1 at 1 2 8 9 10 11.
  case (in_dec nat_eq_dec o1 (OC_list OC1)) as [IN | FAL].
  rewrite (proof_irrelevance _ IN IN1), EQ.
  reflexivity.
  contradiction (FAL IN1).
- destruct (SUR o) as [o1 EQ].
  contradiction (NE _ EQ).
Qed.
*)

Lemma coherent_bijection_sig_inverse {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) :
    coherent_bijection sig ->
        forall (o : ovar),
            OC_elt OC2 o ->
                (sig_generalise sig) (sig_inverse sig o) = o.
Proof.
intros [[[INJ SUR] REL_iff] PREC] o IN.
unfold sig_inverse, sig_generalise.
case (in_dec nat_eq_dec o (OC_list OC2)) as [IN' | FAL].
rewrite (proof_irrelevance _ IN' IN).
clear IN'.
case (sig_image_dec_alt sig (existT _ o IN)) as [[[o1 IN1] EQ] | NE].
- unfold projT1 at 1 2 8 9 10 11.
  case (in_dec nat_eq_dec o1 (OC_list OC1)) as [IN' | FAL].
  rewrite (proof_irrelevance _ IN' IN1), EQ.
  reflexivity.
  contradiction (FAL IN1).
- destruct (SUR (existT _ o IN)) as [o1 EQ].
  contradiction (NE _ EQ).
- contradiction (FAL IN).
Qed.
*)