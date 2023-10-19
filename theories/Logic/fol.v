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

(*Language*)
Definition ivar := nat.

Definition ovar := nat.

Inductive ordinal : Type :=
| cast : ord -> ordinal
| assn : ovar -> ordinal
| oadd : ordinal -> ordinal -> ordinal
| omax : ordinal -> ordinal -> ordinal.

Lemma ord_eq_dec : forall x y : ord, {x = y} + {x <> y}.
Proof.
induction x, y.
2,3 : right;
      discriminate.

1 : left.
    reflexivity.

destruct (IHx1 y1) as [[] | NE].
destruct (IHx2 y2) as [[] | NE].
destruct (nat_eq_dec n n0) as [[] | NE].

1 : left.
    reflexivity.

all : right;
      intros FAL;
      apply NE;
      inversion FAL;
      reflexivity.
Qed.

Lemma ordinal_eq_dec : forall x y : ordinal, {x = y} + {x <> y}.
Proof.
induction x;
destruct y;
try destruct (ord_eq_dec o o0) as [[] | NE];
try destruct (nat_eq_dec o o0) as [[] | NE].

13,18 :  case (IHx1 y1) as [[] | NE1];
         case (IHx2 y2) as [[] | NE2].
1,7,13,17 : left;
            reflexivity.

all : right;
      intros FAL;
      try apply NE;
      inversion FAL;
      try reflexivity;
      contradiction.
Qed.

Inductive nvec : nat -> Type :=
| Null : nvec 0
| New : forall (i : nat), nat -> nvec i -> nvec (S i).

Inductive predicate {n : nat} : nvec n -> Type :=
| Nullary : forall (i : nat) (pf : n = 0), predicate (eq_rect _ _ Null _ (eq_sym pf))
| Succary : forall {m : nat} {vec : nvec m} (i : nat) (v : ivar) (prd : predicate vec) (pf : n = S m), predicate (eq_rect _ _ (New m v vec) _ (eq_sym pf))
| Var : forall {vec : nvec n} (i : nat), predicate vec.

Fixpoint pure_predicate {n : nat} {vec : nvec n} (pn : predicate vec) : bool :=
match pn with
| Nullary _ _ => true
| Succary _ _ pn' _ => pure_predicate pn'
| Var _ => false
end.

(*
Inductive predicate : nat -> Type :=
| Nullary : forall (n : nat), predicate 0
| Succary : forall {i : nat} (n : nat) (v : ivar) (prd : predicate i), predicate (S i).
*)

Inductive formula : Type :=
| fal : formula
| equ : ivar -> ivar -> formula
| imp : formula -> formula -> formula
| univ : ivar -> formula -> formula
| bnd : ovar -> ovar -> formula -> formula
| prd : forall {n : nat} {vec : nvec n} (pn : predicate vec), pure_predicate pn = true -> formula.
(*
| mu : forall n, (predicate n) -> formula -> formula
| muk : forall n, (predicate n) -> ordinal -> formula -> formula.
*)

Definition constraint := {L : list ovar & {R : (ovar -> ovar -> bool) & (NoDup L) /\ (forall (lambda kappa : ovar), R kappa lambda = true -> In kappa L /\ In lambda L) /\ StrictOrder (fun (lambda kappa : ovar) => R lambda kappa = true)}}.

(*Definition constraint := {L : list ovar & {R : ((ovar_sub L) -> (ovar_sub L) -> bool) & (NoDup L) /\ StrictOrder (fun (lambda kappa : ovar_sub L) => R lambda kappa = true)}}.*)

Definition OC_list (OC : constraint) := (projT1 OC).

Definition OC_elt (OC : constraint) (lambda : ovar) : Prop := In lambda (OC_list OC).

Definition OC_rel (OC : constraint) := (projT1 (projT2 OC)).

Definition OC_unique (OC : constraint) := proj1 (projT2 (projT2 OC)).

Definition OC_null (OC : constraint) := proj1 (proj2 (projT2 (projT2 OC))).

Definition OC_order (OC : constraint) := proj2 (proj2 (projT2 (projT2 OC))).

Definition progeny (OC : constraint) (kappa : ovar) : list ovar := filter (fun (lambda : ovar) => OC_rel OC lambda kappa) (OC_list OC).

Definition child (OC : constraint) (lambda kappa : ovar) : Prop := OC_rel OC lambda kappa = true /\ (forall eta, OC_rel OC eta kappa = true -> OC_rel OC lambda eta = false).

Definition children (OC : constraint) (kappa : ovar) : list ovar := filter (fun (lambda : ovar) => if in_dec nat_eq_dec lambda (flat_map (fun eta => progeny OC eta) (progeny OC kappa)) then false else true) (progeny OC kappa).

Definition add_fresh (OC : constraint) (lambda : ovar) (NEW : ~ OC_elt OC lambda) : constraint := (existT _ (lambda :: OC_list OC) (existT _ (OC_rel OC) (conj ((proj2 (NoDup_cons_iff _ _)) (conj NEW (OC_unique OC))) (conj (fun (eta iota : ovar) (REL : OC_rel OC iota eta = true) => conj (or_intror (proj1 (OC_null OC eta iota REL))) (or_intror (proj2 (OC_null OC eta iota REL)))) (OC_order OC))))).

Definition add_fresh_child (OC : constraint) (lambda kappa : ovar) (NEW : ~ OC_elt OC lambda) (KIN : OC_elt OC kappa) : constraint.
Proof.
refine (existT _ (lambda :: OC_list OC) (existT _ (fun (eta iota : ovar) => OC_rel OC eta iota || ((nat_eqb eta lambda && nat_eqb kappa iota) || (nat_eqb eta lambda && OC_rel OC kappa iota))) (conj ((proj2 (NoDup_cons_iff _ _)) (conj NEW (OC_unique OC))) (conj _ _)))).
intros eta iota COND.
case (OC_rel OC iota eta) eqn:REL1.
- apply (conj (or_intror (proj1 (OC_null OC eta iota REL1))) (or_intror (proj2 (OC_null OC eta iota REL1)))).
- unfold "||" in COND.
  case (nat_eqb iota lambda) eqn:EQ.
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
    * unfold "||" in refl.
      case (nat_eqb eta lambda) eqn:EQ.
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
    unfold "&&" in *;
    try rewrite orb_false_r in *.
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
  repeat rewrite filter_In.
  repeat split.
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

Definition assignment (OC : constraint) := {val : (ovar -> ord) & forall (lambda kappa : ovar), OC_rel OC lambda kappa = true -> ord_lt (val lambda) (val kappa)}.

Fixpoint valuate {OC : constraint} (ASN : assignment OC) (o : ordinal) : ord :=
match o with
| cast alpha => alpha
| assn ov => (projT1 ASN) ov
| oadd o1 o2 => ord_add (valuate ASN o1) (valuate ASN o2)
| omax o1 o2 => ord_max (valuate ASN o1) (valuate ASN o2)
end.

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

Lemma children_subset : forall (OC : constraint) (kappa : ovar), incl (children OC kappa) (OC_list OC). exact (fun OC kappa => incl_tran (incl_filter _ _) (incl_filter _ _)). Qed.

Lemma children_are_child : forall (OC : constraint) (lambda kappa : ovar), In lambda (children OC kappa) -> child OC lambda kappa.
Proof.
intros OC lambda kappa IN.
repeat apply filter_In in IN as [IN ?COND].
split.
apply COND0.
intros eta REL.
case (in_dec nat_eq_dec lambda) as [_ | IN'].
inversion COND.
apply not_true_iff_false.
intros FAL.
apply IN', in_flat_map.
exists eta.
apply (conj (proj2 (filter_In _ _ _) (conj (proj1 (OC_null OC _ _ REL)) REL)) (proj2 (filter_In _ _ _) (conj (proj1 (OC_null OC _ _ FAL)) FAL))).
Qed.

Lemma all_child_are_children : forall (OC : constraint) (lambda kappa : ovar), child OC lambda kappa -> In lambda (children OC kappa).
Proof.
intros OC lambda kappa [REL COND].
apply filter_In.
refine (conj (proj2 (filter_In _ _ _) (conj (proj1 (OC_null OC _ _ REL)) REL)) _). 
case (in_dec nat_eq_dec lambda) as [IN | _].
apply in_flat_map in IN as [eta [IN1 IN2]].
apply filter_In in IN1 as [_ REL1],IN2 as [_ REL2].
specialize (COND eta REL1).
rewrite REL2 in COND.
inversion COND.
reflexivity.
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

Fixpoint num_conn (A : formula) : ordinal :=
match A with
| fal => cast Zero
| equ v1 v2 => cast Zero
| imp B C => oadd (oadd (num_conn B) (num_conn C)) (cast (nat_ord 1))
| univ v B => oadd (num_conn B) (cast (nat_ord 1))
| bnd o1 o2 B => oadd (num_conn B) (cast (nat_ord 1))
| prd pn pure => cast Zero
end.

Fixpoint vars_in (a : formula) : list ovar :=
match a with
| fal => []
| equ v1 v2 => []
| imp B C => (vars_in B) ++ (vars_in C)
| univ v B => (vars_in B)
| bnd o1 o2 B => o2 :: remove nat_eq_dec o1 (vars_in B)
| prd pn pure => []
end.

Fixpoint nvec_eqb {n1 n2 : nat} (vec1 : nvec n1) (vec2 : nvec n2) : bool :=
match vec1, vec2 with
| Null, Null => true (*nat_eqb m1 m2*)
| New _ m1 vec1', New _ m2 vec2' => nat_eqb m1 m2 && nvec_eqb vec1' vec2'
| _, _ => false
end.

Fixpoint prd_eqb {n1 n2 : nat} {vec1 : nvec n1} {vec2 : nvec n2} (pn1 : predicate vec1) (pn2 : predicate vec2) : bool :=
match nat_eqb n1 n2 with
| true => match nvec_eqb vec1 vec2 with
    | true => match pn1, pn2 with
        | Nullary i1 _, Nullary i2 _ => nat_eqb i1 i2
        | Succary i1 v1 pn1' _, Succary i2 v2 pn2' _  => nat_eqb i1 i2 && nat_eqb v1 v2 && prd_eqb pn1' pn2'
        | Var i1, Var i2 => nat_eqb i1 i2
        | _ , _ => false
        end
    | false => false
    end
| false => false
end.

Fixpoint form_eqb (A1 A2 : formula) : bool :=
match A1, A2 with
| fal, fal => true
| equ v1 v2, equ v3 v4 => nat_eqb v1 v3 && nat_eqb v2 v4
| imp B1 C1, imp B2 C2 => form_eqb B1 B2 && form_eqb C1 C2
| univ v1 B1, univ v2 B2 => nat_eqb v1 v2 && form_eqb B1 B2
| bnd o1 o2 B1, bnd o3 o4 B2 => nat_eqb o1 o3 && nat_eqb o2 o4 && form_eqb B1 B2
| prd pn1 _, prd pn2 _ => prd_eqb pn1 pn2
| _, _ => false
end.

Fixpoint substitution (A : formula) (i1 i2 : ivar) : formula :=
match A with
| fal => fal
| equ v1 v2 => match nat_eqb v1 i1, nat_eqb v2 i1 with
    | true, true => equ i2 i2
    | true, false => equ i2 v2
    | false, true => equ v1 i2
    | false, false => A
    end
| imp B C => imp (substitution B i1 i2) (substitution C i1 i2)
| univ v B => 
    (match nat_eqb v i1 with
    | true => A
    | false => univ v (substitution B i1 i2)
    end)
| bnd o1 o2 B => bnd o1 o2 (substitution B i1 i2)
| prd pn _ => A
end.

Lemma subst_eq_refl : forall (A : formula) (i : ivar), substitution A i i = A.
Proof.
induction A;
intros iv;
unfold substitution;
fold substitution;
try rewrite IHA;
try rewrite IHA1;
try rewrite IHA2;
try reflexivity.
all : case (nat_eqb i iv) eqn:EQ1;
      try reflexivity.
all : case (nat_eqb i0 iv) eqn:EQ2;
      try apply nat_eqb_eq in EQ1;
      try apply nat_eqb_eq in EQ2;
      subst;
      reflexivity.
Qed.

Lemma nvec_case :
    forall (n : nat) (P : nvec n -> Type),
        (forall (pf : n = 0),
            P (eq_rect 0 nvec Null n (eq_sym pf))) ->
        (forall (i m : nat) (vec : nvec i) (pf : n = S i), P (eq_rect (S i) nvec (New i m vec) n (eq_sym pf))) ->
            (forall (vec : nvec n), P vec).
Proof.
intros n P BC IND vec.
induction vec.
apply (BC eq_refl).
apply (IND _ _ _ eq_refl).
Defined.

Lemma nvec_0_null : forall (vec : nvec 0), vec = Null.
Proof.
apply nvec_case.
- intros pf.
  subst.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in * by apply nat_eq_dec.
  reflexivity.
- intros i m vec pf.
  inversion pf.
Qed.

Lemma nvec_Sn_new : forall {n : nat} (vec : nvec (S n)), {subvec : nvec n & {m : nat & vec = New n m subvec}}.
Proof.
intros n.
apply nvec_case.
- intros pf.
  inversion pf.
- intros i m vec pf.
  inversion pf as [pf'].
  subst.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in * by apply nat_eq_dec.
  apply (existT _ vec (existT _ m eq_refl)).
Defined.

Lemma nvec_eqb_eq :
    forall {n : nat} (vec1 vec2 : nvec n),
        nvec_eqb vec1 vec2 = true ->
            vec1 = vec2.
Proof.
induction n;
intros vec1 vec2 EQB.
- pose proof (nvec_0_null vec1).
  pose proof (nvec_0_null vec2).
  subst.
  reflexivity.
- pose proof (nvec_Sn_new vec1) as [vec3 [m1 EQ1]].
  pose proof (nvec_Sn_new vec2) as [vec4 [m2 EQ2]].
  subst.
  apply and_bool_prop in EQB as [EQ1 EQ2].
  apply nat_eqb_eq in EQ1.
  subst.
  rewrite (IHn _ _ EQ2).
  reflexivity.
Qed.

Lemma nvec_eqb_refl :
    forall {n : nat} (vec : nvec n),
        nvec_eqb vec vec = true.
Proof.
induction n;
intros vec.
- pose proof (nvec_0_null vec).
  subst.
  reflexivity.
- pose proof (nvec_Sn_new vec) as [vec' [m EQ]].
  subst.
  unfold nvec_eqb;
  fold @nvec_eqb.
  rewrite nat_eqb_refl.
  rewrite IHn.
  reflexivity.
Qed.

Definition nvec_eq_dec {n : nat}: forall (a b : nvec n), {a = b} + {a <> b}.
intros a b.
case (nvec_eqb a b) eqn:EQ.
- left. apply nvec_eqb_eq, EQ.
- right.
  intros FAL.
  subst.
  rewrite nvec_eqb_refl in EQ.
  inversion EQ.
Qed.

Lemma pred_case :
    forall (n : nat) (vec : nvec n) (P : predicate vec -> Type),
        (forall (i : nat) (pf : n = 0) (pfv : vec = (eq_rect 0 nvec Null n (eq_sym pf))),
            P (eq_rect _ predicate (Nullary i pf) _ (eq_sym pfv))) ->
        (forall (m : nat) (vec' : nvec m) (i : nat) (v : ivar) (prd : predicate vec') (pf : n = S m) (pfv : vec = eq_rect (S m) nvec (New m v vec') n (eq_sym pf)),
            P (eq_rect _ predicate (Succary i v prd pf) _ (eq_sym pfv))) ->
        (forall (i : nat), P (Var i)) ->
            (forall (pn : predicate vec), P pn).
Proof.
intros n vec P BC IND VARS pn.
pose proof (Eqdep_dec.eq_rect_eq_dec nat_eq_dec nvec vec (eq_sym eq_refl)).
induction pn.
apply (BC _ pf eq_refl).
apply (IND _ _ _ _ _ pf eq_refl).
apply VARS.
Qed.

Lemma prd_eqb_eq :
    forall {n : nat} {vec : nvec n} (pn1 pn2 : predicate vec),
        prd_eqb pn1 pn2 = true ->
            pn1 = pn2.
Proof.
intros n vec.
induction pn1.
- intros pn2.
  subst.
  unfold eq_rect, eq_sym in *.
  apply (pred_case 0 Null (fun (pn2 : predicate Null) => prd_eqb (Nullary i eq_refl) pn2 = true -> (Nullary i eq_refl) = pn2)).
  + intros i1 pf pfv EQB.
    rewrite pfv in EQB.
    unfold eq_rect, eq_sym in EQB.
    rewrite (UIP _ _ _ pf eq_refl) in EQB.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl in EQB.
    apply nat_eqb_eq in EQB.
    subst.
    pose proof (UIP_refl _ _ pf).
    subst.
    unfold eq_rect, eq_sym in pfv.
    pose proof (UIP_refl _ _ pfv).
    subst.
    reflexivity.
  + intros m vec i1 v pn1 pf pfv EQB.
    inversion pf.
  + intros i1 EQB.
    inversion EQB.
- intros pn3.
  subst.
  unfold eq_rect, eq_sym in *.
  apply (pred_case (S m) (New m v vec) (fun (pn2 : predicate (New m v vec)) => prd_eqb (Succary i v pn1 eq_refl) pn2 = true -> (Succary i v pn1 eq_refl) = pn2)).
  + intros i1 pf pfv EQB.
    inversion pf.
  + intros m2 vec2 i2 v2 pn2 pf pfv EQB.
    inversion pf as [pf'].
    subst.
    pose proof (UIP_refl _ _ pf).
    subst.
    unfold eq_rect, eq_sym in pfv.
    inversion pfv as [[EQ1 EQ2]].
    apply inj_pair2 in EQ2.
    subst.
    pose proof (UIP_refl _ _ pfv).
    subst.
    unfold eq_rect, eq_sym in *.
    unfold prd_eqb in EQB;
    fold @prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl, nat_eqb_refl, andb_true_r in EQB.
    apply and_bool_prop in EQB as [EQ1 EQ2].
    apply nat_eqb_eq in EQ1.
    specialize (IHpn1 _ EQ2) as EQ3.
    subst.
    reflexivity.
  + intros i1 EQB.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl in EQB.
    inversion EQB.
- intros pn2.
  apply (pred_case n vec (fun (pn2 : predicate vec) => prd_eqb (Var i) pn2 = true -> (Var i) = pn2)).
  + intros i1 pf pfv EQB.
    subst.
    inversion EQB.
  + intros m vec2 i1 v pn1 pf pfv EQB.
    subst.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl in EQB.
    inversion EQB.
  + intros i2 EQB.
    unfold prd_eqb in EQB.
    rewrite nat_eqb_refl, nvec_eqb_refl in EQB.
    apply nat_eqb_eq in EQB.
    subst.
    reflexivity.
Qed.

Lemma prd_eqb_refl :
    forall {n : nat} {vec : nvec n} (pn : predicate vec),
        prd_eqb pn pn = true.
Proof.
intros n vec pn.
induction pn;
unfold prd_eqb;
fold @prd_eqb;
repeat rewrite nat_eqb_refl;
rewrite nvec_eqb_refl;
try rewrite IHpn;
try reflexivity.
Qed.

Lemma prd_eqb_type : 
    forall {n1 n2 : nat} {vec1 : nvec n1} {vec2 : nvec n2} (pn1 : predicate vec1) (pn2 : predicate vec2),
        prd_eqb pn1 pn2 = true -> nat_eqb n1 n2 = true /\ nvec_eqb vec1 vec2 = true.
Proof.
intros n1 n2 vec1 vec2 pn1 pn2 EQB.
destruct pn1, pn2;
subst;
unfold prd_eqb, eq_rect, eq_sym in EQB;
fold @prd_eqb in EQB.
- split; reflexivity.
- inversion EQB.
- case (nat_eqb 0 n2) eqn:EQ1;
  case (nvec_eqb Null vec) eqn:EQ2;
  inversion EQB.
- inversion EQB.
- unfold eq_rect, eq_sym.
  case (nat_eqb (S m) (S m0)) eqn:EQ1.
  case (nvec_eqb (New m v vec) (New m0 v0 vec0)) eqn:EQ2.
  split; reflexivity.
  inversion EQB.
  inversion EQB.
- case (nat_eqb (S m) n2) eqn:EQ1;
  case (nvec_eqb (New m v vec) vec0) eqn:EQ2;
  inversion EQB.
- case (nat_eqb n1 0) eqn:EQ1;
  case (nvec_eqb vec Null) eqn:EQ2;
  inversion EQB.
- case (nat_eqb n1 (S m)) eqn:EQ1;
  case (nvec_eqb vec (New m v vec0)) eqn:EQ2;
  inversion EQB.
- case (nat_eqb n1 n2) eqn:EQ1;
  case (nvec_eqb vec vec0) eqn:EQ2;
  inversion EQB.
  split; reflexivity.
Qed.

Definition prd_eq_dec {n : nat} {vec : nvec n} : forall (a b : predicate vec), {a = b} + {a <> b}.
intros a b.
case (prd_eqb a b) eqn:EQ.
- left. apply prd_eqb_eq, EQ.
- right.
  intros FAL.
  subst.
  rewrite prd_eqb_refl in EQ.
  inversion EQ.
Qed.

Lemma form_eqb_eq :
    forall (A B : formula),
        form_eqb A B = true ->
            A = B.
Proof.
induction A;
intros B EQ;
destruct B;
inversion EQ as [EQ'];
repeat apply and_bool_prop in EQ as [EQ ?EQ];
try apply nat_eqb_eq in EQ as [];
try apply nat_eqb_eq in EQ0 as [];
try apply nat_eqb_eq in EQ1 as [].
- reflexivity.
- reflexivity.
- rewrite (IHA1 _ EQ),(IHA2 _ EQ0).
  reflexivity.
- rewrite (IHA _ EQ0).
  reflexivity.
- rewrite (IHA _ EQ0).
  reflexivity.
- destruct (prd_eqb_type _ _ EQ') as [EQ1 EQ2].
  apply nat_eqb_eq in EQ1.
  subst.
  apply nvec_eqb_eq in EQ2.
  subst.
  apply prd_eqb_eq in EQ'.
  subst.
  pose proof (UIP  _ _ _ e e0).
  subst.
  reflexivity.
Qed.

Lemma form_eqb_refl : forall (a : formula), form_eqb a a = true.
Proof.
intros a.
induction a;
unfold form_eqb;
fold form_eqb;
repeat rewrite nat_eqb_refl;
try rewrite IHa;
try rewrite IHa1;
try rewrite IHa2;
try reflexivity.
apply prd_eqb_refl.
Qed.

Definition form_eq_dec : forall (a b : formula), {a = b} + {a <> b}.
intros a b.
case (form_eqb a b) eqn:EQ.
- left. apply form_eqb_eq, EQ.
- right.
  intros FAL.
  subst.
  rewrite form_eqb_refl in EQ.
  inversion EQ.
Qed.

Definition sig_generalise {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) : ovar -> ovar := fun o =>
match
in_dec nat_eq_dec o (OC_list OC1) with
| left IN => projT1 (sig (existT _ o IN))
| right _ => o
end.

Fixpoint sig_subst (a : formula) (sig : ovar -> ovar) : formula :=
match a with
| fal => fal
| equ v1 v2 => equ v1 v2
| imp a1 a2 =>  imp (sig_subst a1 sig) (sig_subst a2 sig)
| univ v a => univ v (sig_subst a sig)
| bnd o1 o2 a => bnd o1 (sig o2) (sig_subst a (fun o => if nat_eq_dec o o1 then o else sig o))
| prd n pn => prd n pn
end.

Definition coherent {OC1 OC2 : constraint} (sig : constraint_type OC2 -> constraint_type OC1) : Prop :=
      (forall (lambda : constraint_type OC2),
          OC_elt OC1 (projT1 (sig lambda))) /\
      (forall (lambda kappa : constraint_type OC2),
          OC_rel OC2 (projT1 lambda) (projT1 kappa) = true <-> OC_rel OC1 (projT1 (sig lambda)) (projT1 (sig kappa)) = true) /\
          (forall (lambda kappa : constraint_type OC2),
              precedence nat_eq_dec (OC_list OC2) (projT1 lambda) (projT1 kappa) = true ->
                  precedence nat_eq_dec (OC_list OC1) (projT1 (sig lambda)) (projT1 (sig kappa)) = true).

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

Definition sig_inverse_single {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (o2 : constraint_type OC2) := {o1 : constraint_type OC1 & sig o1 = o2}.

Definition sig_image {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) (o2 : constraint_type OC2) : Prop := inhabited {o1 : constraint_type OC1 & sig o1 = o2}.

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


(*
Lemma coherent_is_injective {OC1 OC2 : constraint} (sig : constraint_type OC1 -> constraint_type OC2) :
    coherent OC2 OC1 sig ->
        forall phi1 phi2 : formula,
            phi1 = phi2 <-> sig_subst phi1 (sig_generalise sig) = sig_subst phi2 (sig_generalise sig).
Proof.
intros [SUB [REL_iff ORD]].
induction phi1;
intros phi2;
split;
intros EQ;
subst;
try reflexivity;
destruct phi2;
inversion EQ;
subst.
reflexivity.
reflexivity.
rewrite (proj2 (IHphi1_1 _) H0).
rewrite (proj2 (IHphi1_2 _) H1).
reflexivity.
rewrite (proj2 (IHphi1 _) H1).
reflexivity.
admit.
apply inj_pair2 in H1.
subst.
apply inj_pair2 in H2.
apply inj_pair2 in H2.
subst.
rewrite (proof_irrelevance _ e e0).
reflexivity.
Admitted.
*)