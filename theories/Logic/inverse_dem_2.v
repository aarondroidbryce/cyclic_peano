From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import PA_cyclic.

Require Import List.
Import ListNotations.

Definition demorgan2_sub_formula (A E F : formula) (S : subst_ind) : formula :=
    formula_sub_ind A (neg (lor E F)) (neg F) S.
  
Lemma demorgan2_sub_formula_closed :
    forall (A : formula),
        closed A = true ->
            forall (E F : formula) (S : subst_ind),
                closed (demorgan2_sub_formula A E F S) = true.
Proof.
intros A CA E F S.
unfold demorgan2_sub_formula.
apply (formula_sub_ind_closed _ _ _ CA).
unfold closed; fold closed.
apply and_bool_prop.
Qed.
  
Fixpoint demorgan2_sub_ptree_fit
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (demorgan2_sub_ptree_fit P' E F S)

| ord_up alpha P', _ => ord_up alpha (demorgan2_sub_ptree_fit P' E F S)

| node A, _ => node (demorgan2_sub_formula A E F S)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (demorgan2_sub_formula C E F S_C)
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (demorgan2_sub_formula C E F S_C)
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (demorgan2_sub_formula A E F S)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ =>
    (match form_eqb A E, form_eqb B F, S with
    | true, true, (1) =>
      (match nat_eqb d2 (ptree_deg P) with
      | true => ord_up (ptree_ord P) P2
      | false => deg_up (ptree_deg P) (ord_up (ptree_ord P) P2)
      end)
    | _, _, _ => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    (match form_eqb A E, form_eqb B F, S_AB with
    | true, true, (1) =>
      (match nat_eqb d2 (ptree_deg P) with
      | true =>
          ord_up
            (ptree_ord P)
            (demorgan2_sub_ptree_fit P2 E F (lor_ind (non_target (neg A)) S_D))
      | false =>
          deg_up
            (ptree_deg P)
              (ord_up
                (ptree_ord P)
                (demorgan2_sub_ptree_fit
                  P2 E F
                  (lor_ind (non_target (neg A)) S_D)))
      end)
    | _, _, _ =>
        demorgan_abd
          A B
          (demorgan2_sub_formula D E F S_D)
          d1 d2 alpha1 alpha2
          (demorgan2_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
          (demorgan2_sub_ptree_fit P2 E F (lor_ind (non_target (neg B)) S_D))
    end)

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (demorgan2_sub_formula D E F S_D)
      n t d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (0) S_D))

| loop_a A n d1 d2 alpha1 alpha2 P1 P2, _ => P

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_A =>
    loop_ca
      (demorgan2_sub_formula C E F S_C)
      A n d1 d2 alpha1 alpha2
      (demorgan2_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      P2

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (demorgan2_sub_formula C E F S)
      A d1 d2 alpha1 alpha2
      (demorgan2_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (demorgan2_sub_formula D E F S)
      d1 d2 alpha1 alpha2
      P1
      (demorgan2_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (demorgan2_sub_formula C E F S_C)
      A
      (demorgan2_sub_formula D E F S_D)
      d1 d2 alpha1 alpha2
      (demorgan2_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (demorgan2_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.
  
Definition demorgan2_sub_ptree
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => demorgan2_sub_ptree_fit P E F S
end.

Lemma demorgan2_ptree_formula_true :
    forall (P : ptree) (E F : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            demorgan2_sub_ptree_fit P E F S = demorgan2_sub_ptree P E F S.
Proof.
intros P E F S FS.
unfold demorgan2_sub_ptree.
rewrite FS.
reflexivity.
Qed.

Lemma dem2_axiom_id :
    forall (A E F : formula) (S : subst_ind),
        PA_cyclic_axiom A = true ->
            demorgan2_sub_formula A E F S = A.
Proof.
intros A E F S AX.
induction A;
inversion AX as [AX'];
unfold demorgan2_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
fold form_eqb;
case subst_ind_fit;
try reflexivity.
destruct A;
inversion AX as [AX''].
unfold form_eqb.
reflexivity.
Qed.

Lemma demorgan2_ptree_formula' :
    forall (P : ptree) (E F : formula),
        struct_valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    ptree_formula (demorgan2_sub_ptree P E F S) =
                        demorgan2_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F.
induction P;
try intros PSV S FS;
unfold demorgan2_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold demorgan2_sub_ptree_fit; fold demorgan2_sub_ptree_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : { unfold demorgan2_sub_ptree, demorgan2_sub_formula, formula_sub_ind.
      rewrite FS.
      reflexivity. }

1-2 : rewrite (demorgan2_ptree_formula_true _ _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PSV _ FS).

5 : reflexivity.

6,8,13,14,16 :
    unfold ptree_formula, demorgan2_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
    destruct S;
    try reflexivity.

all : destruct S; inversion FS as [FS'];
      try apply and_bool_prop in FS' as [FS1 FS2];
      unfold ptree_formula, demorgan2_sub_formula, formula_sub_ind, formula_sub_ind_fit;
      fold ptree_formula formula_sub_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ1;
      case (form_eqb b F) eqn:EQ2;
      unfold ptree_formula, demorgan2_sub_formula, formula_sub_ind, subst_ind_fit, formula_sub_ind_fit, form_eqb;
      fold ptree_formula form_eqb formula_sub_ind_fit subst_ind_fit;
      try rewrite EQ1;
      try rewrite EQ2;
      try reflexivity.

all : unfold "&&".

4 : { apply form_eqb_eq in EQ1,EQ2.
      destruct EQ1,EQ2.
      case (nat_eqb d2 (ptree_deg (demorgan_ab a b d1 d2 alpha1 alpha2 P1 P2))) eqn:EQ;
      unfold ptree_formula;
      fold ptree_formula;
      apply P2F. }

all : destruct S1;
      inversion FS as [FS''].

5 : { apply form_eqb_eq in EQ1,EQ2.
      destruct EQ1,EQ2.
      assert (subst_ind_fit (ptree_formula P2) (lor_ind (non_target (neg b)) S2) = true) as FS2'.
      { rewrite P2F.
        unfold subst_ind_fit, non_target; fold subst_ind_fit.
        apply FS. }
      case (nat_eqb d2 (ptree_deg (demorgan_abd a b d d1 d2 alpha1 alpha2 P1 P2))) eqn:EQ;
      unfold ptree_formula; fold ptree_formula;
      rewrite (demorgan2_ptree_formula_true _ _ _ _ FS2');
      rewrite (IHP2 P2SV _ FS2');
      unfold demorgan2_sub_formula;
      rewrite P2F;
      rewrite non_target_sub_lor;
      unfold formula_sub_ind;
      rewrite FS'';
      reflexivity. }

all : try apply and_bool_prop in FS1 as [FS1_1 FS1_2].

3 : destruct S1_1;
    inversion FS as [FS'''];
    apply and_bool_prop in FS1_1 as [FS1_1_1 FS1_1_2].

all : unfold ptree_formula, demorgan2_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
      fold ptree_formula form_eqb formula_sub_ind_fit;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS1_2;
      unfold "&&";
      try reflexivity.
Qed.

Lemma demorgan2_ptree_formula :
    forall (P : ptree) (E F : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_formula (demorgan2_sub_ptree P E F S) =
                    demorgan2_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F PSV S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (demorgan2_ptree_formula' _ _ _ PSV _ FS).
- unfold demorgan2_sub_ptree, demorgan2_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma demorgan2_ptree_deg :
    forall (P : ptree) (E F : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_deg (demorgan2_sub_ptree P E F S) = ptree_deg P.
Proof.
intros P E F PSV.
unfold demorgan2_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold demorgan2_sub_ptree_fit; fold demorgan2_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try reflexivity.

1 : destruct PSV as [[PSV OU] NO]. (*ord up*)
2-8 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
9 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)
10-12 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
13 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S;
      inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ1;
      case (form_eqb b F) eqn:EQ2;
      unfold ptree_deg; fold ptree_deg;
      try rewrite P1D;
      try rewrite P2D;
      case (nat_eqb (ptree_deg P2) (Nat.max (ptree_deg P1) (ptree_deg P2))) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try reflexivity.

4 : apply nat_eqb_eq in EQ;
    destruct EQ;
    try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.

- apply nat_eqb_eq in EQ;
  destruct EQ.
  rewrite <- (IHP2 P2SV (lor_ind (non_target (neg b)) S2)).
  rewrite P2F.
  unfold subst_ind_fit, non_target; fold subst_ind_fit.
  rewrite FS'.
  reflexivity.
Qed.

Lemma demorgan2_ptree_ord :
    forall (P : ptree) (E F : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_ord (demorgan2_sub_ptree P E F S) = ptree_ord P.
Proof.
intros P E F PSV.
unfold demorgan2_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold demorgan2_sub_ptree_fit; fold demorgan2_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try reflexivity.

1 : destruct PSV as [PSV DU]. (*deg up*)
2-8 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
9 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)
10-12 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
13 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ1;
      case (form_eqb b F) eqn:EQ2;
      unfold ptree_deg; fold ptree_deg;
      case (nat_eqb d2 (Nat.max d1 d2)) eqn:EQ;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_ord; fold ptree_ord;
      try reflexivity.
Qed.

Lemma dem2_not_ax_not_ax :
    forall (P : ptree) (E F : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (demorgan2_sub_ptree P E F S)) -> PA_cyclic_axiom A = false -> (exists (B : formula), In B (node_extract P) /\ PA_cyclic_axiom B = false)).
Proof.
  intros P E F.
  induction P;
  intros S PSV FS A IN NAX.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)
    
  1 : { unfold demorgan2_sub_ptree in IN.
        rewrite FS in IN.
        unfold demorgan2_sub_ptree_fit in IN.
        destruct IN as [EQ | FAL];
        try inversion FAL.
        destruct EQ.
        exists a.
        unfold node_extract.
        split.
        - left.
          reflexivity.
        - unfold demorgan2_sub_formula, formula_sub_ind in NAX.
          unfold ptree_formula in FS.
          rewrite FS in NAX.
          destruct a;
          unfold formula_sub_ind_fit, form_eqb in NAX;
          fold formula_sub_ind_fit form_eqb in NAX;
          try apply NAX;
          try reflexivity.
          case form_eqb eqn:EQ.
          + apply form_eqb_eq in EQ.
            rewrite EQ.
            reflexivity.
          + apply NAX. }

  3-6,8-15,18,20 : 
      destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

  4-6,17 :
      destruct S1; inversion FS' as [FS''];
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

  6 : destruct S1_1; inversion FS'' as [FS'''];
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].
  
  all : unfold demorgan2_sub_ptree in IN;
        rewrite FS in IN;
        unfold demorgan2_sub_ptree_fit in IN;
        fold demorgan2_sub_ptree_fit in IN;
        unfold node_extract in *;
        fold node_extract in *;
        try rewrite demorgan2_ptree_formula_true in IN;
        try rewrite demorgan2_ptree_formula_true in IN;
        try rewrite demorgan2_ptree_formula_true in IN;
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  all : try apply (fun FSUB => IHP _ PSV FSUB _ IN NAX);
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  3-6 : exists A;
        split;
        auto.

  1-4 : case (form_eqb a E) eqn:EQ1;
        case (form_eqb b F) eqn:EQ2;
        unfold node_extract, ptree_deg in IN;
        fold node_extract ptree_deg in IN.

  5,13 : case (nat_eqb d2 (max d1 d2)) eqn:EQ.

  1-19,21-22 :
      unfold node_extract in *;
      fold node_extract in *;
      try apply in_app_or in IN as [IN1 | IN2];
      try destruct (fun FSUB => IHP1 _ P1SV FSUB A IN1 NAX) as [B1 [INB1 BAX1]];
      try destruct (fun FSUB => IHP2 _ P2SV FSUB A IN2 NAX) as [B2 [INB2 BAX2]];
      try destruct (fun FSUB => IHP1 _ P1SV FSUB A IN NAX) as [B1 [INB1 BAX1]];
      try destruct (fun FSUB => IHP2 _ P2SV FSUB A IN NAX) as [B2 [INB2 BAX2]];
      try exists B1;
      try exists B2;
      try exists A;
      try split;
      try apply (in_or_app _ _ _ (or_intror IN));
      try apply (in_or_app _ _ _ (or_introl IN1));
      try apply (in_or_app _ _ _ (or_intror IN2));
      try apply (in_or_app _ _ _ (or_introl INB1));
      try apply (in_or_app _ _ _ (or_intror INB2));
      try apply NAX;
      try apply BAX1;
      try apply BAX2;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold ptree_formula in FS;
      fold ptree_formula in FS;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try reflexivity.

  1,2 : case (closed (univ n a)) eqn:CuA.

  3 : exists A;
      exact (conj IN NAX).


  2-3 : exists (univ n a);
        exact (conj (or_introl eq_refl) eq_refl).

  apply in_app_or in IN as [IN1 | IN2].

  { exists A.
    exact (conj (in_or_app _ _ _ (or_introl IN1)) NAX). }

  { destruct (fun FSUB => IHP1 _ P1SV FSUB A IN2 NAX) as [B1 [INB1 BAX1]].
    - rewrite P1F.
      unfold subst_ind_fit;
      fold subst_ind_fit.
      rewrite FS1.
      apply non_target_sub_fit.
    - exists B1.
      split.
      + apply (in_or_app _ _ _ (or_intror INB1)).
      + apply BAX1. }
Qed.

Lemma dem2_all_ax_trans : 
    forall (P : ptree) (E F : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true) ->
                    (forall (A : formula), In A (node_extract (demorgan2_sub_ptree P E F S)) -> PA_cyclic_axiom A = true).
Proof.
intros P E F S PSV FS PAX A INA.
case (PA_cyclic_axiom A) eqn:AX.
- reflexivity.
- destruct (dem2_not_ax_not_ax _ _ _ _ PSV FS _ INA AX) as [B [INB NAX]].
  rewrite (PAX _ INB) in NAX.
  inversion NAX.
Qed.

Lemma demorgan2_valid :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (demorgan2_sub_ptree P E F S).
Proof.
intros P E F [PSV PAX].
induction P; try intros S FS;
unfold demorgan2_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold demorgan2_sub_ptree_fit; fold demorgan2_sub_ptree_fit.

all : try apply (PSV,PAX).

1 : { repeat split.
      rewrite dem2_axiom_id;
      apply PAX.
      apply or_introl, eq_refl. }

  1 : destruct PSV as [PSV DU].
  2 : destruct PSV as [[PSV OU] NO].
  3-10 : destruct PSV as [[[PF PSV] PD] PO].
  11 : destruct PSV as [[[[PF PSV] PD] PO] FC].
  12-16: destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O].
  17: destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA].

  3-6,8-13,16,17 : 
      destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

  4-6,13 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

  6 : destruct S1_1; inversion FS'' as [FS'''];
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

  7,8,13,14 :
      case (form_eqb a E) eqn:EQ1;
      case (form_eqb b F) eqn:EQ2;
      unfold ptree_deg; fold ptree_deg;
      try apply (PSV,PAX).

11,19 : case (nat_eqb d2 (Nat.max d1 d2)) eqn:EQ.


all : unfold node_extract in *;
      fold node_extract in *;
      try apply form_eqb_eq in EQ1;
      try destruct EQ1;
      try apply form_eqb_eq in EQ2;
      try destruct EQ2;
      repeat rewrite demorgan2_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply (IHP1 P1SV);
      try apply (IHP2 P2SV);
      unfold ptree_deg; fold ptree_deg;
      try rewrite demorgan2_ptree_deg;
      try rewrite demorgan2_ptree_ord;
      try apply ptree_ord_nf_struct;
      unfold ptree_ord; fold ptree_ord;
      try rewrite demorgan2_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      repeat split;
      unfold demorgan2_sub_formula;
      repeat rewrite formula_sub_ind_lor;
      try rewrite formula_sub_ind_0;
      try rewrite non_target_sub;
      try rewrite non_target_sub_term;
      try apply PSV;
      try apply PAX;
      try apply PD;
      try rewrite PO;
      try apply P1SV;
      try rewrite P1D in *;
      try rewrite P1O;
      try apply P2SV;
      try rewrite P2D in *;
      try rewrite P2O;
      try apply FS;
      try apply DU;
      try apply OU;
      try apply NO;
      try apply INA;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit, non_target;
      fold subst_ind_fit non_target;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      unfold "&&";
      try reflexivity;
      try apply (fun B INB => PAX B (in_or_app _ _ _ (or_introl INB)));
      try apply (fun B INB => PAX B (in_or_app _ _ _ (or_intror INB)));
      try apply max_lem2;
      try apply EQ;
      try apply ord_lt_max_succ_r;
      try reflexivity.

  8 : { intros B INB.
        rewrite closed_free_list in INB.
        inversion INB.
        apply formula_sub_ind_closed.
        apply (valid_closed_formula PAX FC).
        intros CEF.
        apply and_bool_prop in CEF as [CE CF].
        apply CF. }

  all : unfold node_extract in *;
        fold node_extract in *;
        intros A IN;
        try apply in_app_or in IN as [IN1 | IN2];
        try apply (fun FSUB => dem2_all_ax_trans _ _ _ _ P1SV FSUB (fun B INB1 => PAX B (in_or_app _ _ _ (or_introl INB1))) _ IN1);
        try apply (fun FSUB => dem2_all_ax_trans _ _ _ _ P2SV FSUB (fun B INB2 => PAX B (in_or_app _ _ _ (or_intror INB2))) _ IN2);
        try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
        try apply (PAX _ (in_or_app _ _ _ (or_intror IN2)));
        try rewrite P1F;
        try rewrite P2F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS1;
        try rewrite FS2;
        try rewrite non_target_fit;
        try reflexivity.

  all : try case (closed (univ n a)) eqn:CuA;
        try pose proof (PAX _ (or_introl eq_refl)) as FAL;
        try inversion FAL;
        try apply (PAX _ (in_or_app _ _ _ (or_intror IN)));
        try apply in_app_or in IN as [IN1 | IN2];
        try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
        try apply (fun FSUB => dem2_all_ax_trans _ _ _ _ P1SV FSUB (fun B INB => PAX B (in_or_app _ _ _ (or_intror INB))) _ IN2);
        try rewrite P1F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS1, non_target_sub_fit;
        try reflexivity.
Qed.