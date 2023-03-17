From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import PA_cyclic.

Require Import Lia.

Require Import List.
Import ListNotations.

Fixpoint string_tree
    (P Q : ptree) : ptree :=
match P with
| deg_up d P' =>
    match (nat_ltb (ptree_deg Q) d) with
    | false => (string_tree P' Q)
    | true => deg_up d (string_tree P' Q)
    end

| ord_up alpha P' =>
    match ord_ltb (ptree_ord (string_tree P' Q)) alpha with
    | true => ord_up alpha (string_tree P' Q)
    | false => (string_tree P' Q)
    end

| node A =>
    match form_eqb (ptree_formula Q) A with
    | true => Q
    | false => match (ptree_deg Q) with
        | 0 => P
        | dQ => deg_up dQ P
        end
    end

| exchange_ab A B d alpha P' =>
    exchange_ab A B
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| exchange_cab C A B d alpha P'=>
    exchange_cab
      C A B
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| exchange_abd A B D d alpha P' =>
    exchange_abd
      A B D
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| exchange_cabd C A B D d alpha P' =>
    exchange_cabd
      C A B D
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| contraction_a A d alpha P' =>
    contraction_a
      A
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| contraction_ad A D d alpha P' =>
    contraction_ad
      A D
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| weakening_ad A D d alpha P' =>
    weakening_ad
      A D
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 =>
    demorgan_ab A B
      (ptree_deg (string_tree P1 Q))
      (ptree_deg (string_tree P2 Q))
      (ptree_ord (string_tree P1 Q))
      (ptree_ord (string_tree P2 Q))
      (string_tree P1 Q)
      (string_tree P2 Q)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 =>
    demorgan_abd
      A B D
      (ptree_deg (string_tree P1 Q))
      (ptree_deg (string_tree P2 Q))
      (ptree_ord (string_tree P1 Q))
      (ptree_ord (string_tree P2 Q))
      (string_tree P1 Q)
      (string_tree P2 Q)

| negation_a A d alpha P' =>
    negation_a
      A
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| negation_ad A D d alpha P' =>
    negation_ad
      A D
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| quantification_a A k t d alpha P' =>
    quantification_a
      A k t
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| quantification_ad A D k t d alpha P' =>
    quantification_ad
      A D k t
      (ptree_deg (string_tree P' Q))
      (ptree_ord (string_tree P' Q))
      (string_tree P' Q)

| loop_a A k d1 d2 alpha1 alpha2 P1 P2 =>
    match form_eqb (ptree_formula Q) A with
        | true => 
            loop_a
              A k
              (ptree_deg (string_tree P1 Q))
              d2
              (ptree_ord (string_tree P1 Q))
              alpha2
              (string_tree P1 Q) P2
        | false =>
            loop_a
              A k
              (ptree_deg (string_tree P1 Q))
              (ptree_deg (string_tree P2 Q))
              (ptree_ord (string_tree P1 Q))
              (ptree_ord (string_tree P2 Q))
              (string_tree P1 Q)
              (string_tree P2 Q)
        end

| loop_ca C A k d1 d2 alpha1 alpha2 P1 P2 => match form_eqb (ptree_formula Q) A with
    | true => 
        loop_ca
          C A k
          (ptree_deg (string_tree P1 Q))
          d2
          (ptree_ord (string_tree P1 Q))
          alpha2
          (string_tree P1 Q) P2
    | false =>
        loop_ca
          C A k
          (ptree_deg (string_tree P1 Q))
          (ptree_deg (string_tree P2 Q))
          (ptree_ord (string_tree P1 Q))
          (ptree_ord (string_tree P2 Q))
          (string_tree P1 Q)
          (string_tree P2 Q)
    end

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      C A
      (ptree_deg (string_tree P1 Q))
      (ptree_deg (string_tree P2 Q))
      (ptree_ord (string_tree P1 Q))
      (ptree_ord (string_tree P2 Q))
      (string_tree P1 Q)
      (string_tree P2 Q)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ad
      A D
      (ptree_deg (string_tree P1 Q))
      (ptree_deg (string_tree P2 Q))
      (ptree_ord (string_tree P1 Q))
      (ptree_ord (string_tree P2 Q))
      (string_tree P1 Q)
      (string_tree P2 Q)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 =>
    cut_cad
      C A D
      (ptree_deg (string_tree P1 Q))
      (ptree_deg (string_tree P2 Q))
      (ptree_ord (string_tree P1 Q))
      (ptree_ord (string_tree P2 Q))
      (string_tree P1 Q)
      (string_tree P2 Q)
end.

Lemma string_tree_formula :
    forall (P Q : ptree),
        (ptree_formula (string_tree P Q)) = (ptree_formula P).
Proof.
intros P Q.
induction P;
unfold string_tree, ptree_formula;
fold string_tree ptree_formula;
try reflexivity;
try apply IHP.

- case (form_eqb (ptree_formula Q) a) eqn:EQ.
  + apply form_eqb_eq in EQ.
    destruct EQ.
    reflexivity.
  + destruct (ptree_deg Q);
    reflexivity.

- case (nat_ltb (ptree_deg Q) d');
  apply IHP.

- case ord_ltb;
  apply IHP.

- case (form_eqb (ptree_formula Q) a) eqn:EQ;
  reflexivity.

- case (form_eqb (ptree_formula Q) a) eqn:EQ;
  reflexivity.
Qed.

Lemma string_tree_deg :
    forall (P Q : ptree),
        struct_valid P ->
            (ptree_deg (string_tree P Q)) = max (ptree_deg P) (ptree_deg Q).
Proof.
intros P Q PSV.
induction P;
unfold string_tree;
fold string_tree;
unfold ptree_deg;
fold ptree_deg.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

all : try rewrite (IHP PSV);
      try rewrite (IHP1 P1SV);
      try rewrite (IHP2 P2SV);
      try lia.

- case (form_eqb (ptree_formula Q) a) eqn:EQ.
  2 : destruct (ptree_deg Q);
      reflexivity.

  1 : lia.

- destruct (nat_semiconnex_bool (ptree_deg Q) d') as [LT | [GT | EQ]].
  + rewrite LT.
    rewrite (max_split2 _ _ LT).
    reflexivity.
  + rewrite (nat_ltb_asymm _ _ GT).
    rewrite (max_split1 _ _ GT).
    rewrite (max_split1 _ _ (nat_ltb_trans _ _ _ (nat_lt_ltb _ _ DU) GT)) in IHP.
    apply (IHP PSV).
  + apply nat_eqb_eq in EQ.
    destruct EQ.
    rewrite nat_ltb_irrefl.
    rewrite (PeanoNat.Nat.max_l _ _ (le_n _)).
    rewrite (PeanoNat.Nat.max_r _ _ (le_S_n _ _ (le_S _ _ DU))) in IHP.
    apply (IHP PSV).

- case ord_ltb;
  apply IHP, PSV.

- case form_eqb eqn:EQ;
  unfold ptree_deg;
  fold ptree_deg;
  lia.

- case form_eqb eqn:EQ;
  unfold ptree_deg;
  fold ptree_deg;
  lia.
Qed.

(*****)
(*Not True In This Version*)
(*****)
(*
Lemma string_tree_ord :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta),
        struct_valid P ->
            (ptree_ord (string_tree P Q QP)) = ord_add beta (ptree_ord P).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] PSV.
  induction P;
  unfold string_tree;
  fold string_tree;
  unfold ptree_ord;
  fold ptree_ord.
  
  1 : destruct PSV as [ID PSV].
  2 : destruct PSV as [[IO PSV] NO].
  3 : destruct PSV.
  4-9 : destruct PSV as [[[PF PSV] PD] PO].
  10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
  13-16 : destruct PSV as [[[PF PSV] PD] PO].
  11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

  all : unfold ptree_ord;
        fold ptree_ord;
        repeat rewrite ord_succ_add_succ;
        try rewrite ord_max_add_comm;
        try rewrite ord_add_assoc;
        try rewrite IHP;
        try rewrite IHP1;
        try rewrite IHP2;
        try apply PSV;
        try apply P1SV;
        try apply P2SV;
        try rewrite PO;
        try rewrite P1O;
        try rewrite P2O;
        try reflexivity;
        try apply nf_add;
        try apply nf_mult;
        try apply nf_nf_succ;
        try apply nf_ord_max;
        repeat apply single_nf;
        try apply zero_nf;
        try apply (ptree_ord_nf_struct _ PSV);
        try apply (ptree_ord_nf_struct _ P1SV);
        try apply (ptree_ord_nf_struct _ P2SV);
        try apply (ptree_ord_nf_struct_hyp _ _ QO QSV).
  
  - case (nat_ltb dQ d') eqn:LT;
    apply (IHP PSV).

  - case ord_ltb;

  
  - try case (form_eqb A a) eqn:EQ.
    + rewrite ord_add_zero.
      auto.
    + destruct beta;
      destruct dQ;
      rewrite ord_add_zero;
      reflexivity.
Qed.
*)

Lemma string_tree_node_remove :
    forall (P Q : ptree),
        struct_valid P ->
            incl (node_extract (string_tree P Q)) ((node_extract Q) ++ (remove form_eq_dec (ptree_formula Q) (node_extract P))).
Proof.
  intros P Q PSV.
  induction P;
  unfold string_tree;
  fold string_tree;
  unfold node_extract in *;
  fold node_extract in *.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

  1 : { unfold remove.
        case (form_eq_dec (ptree_formula Q) a) as [EQ | NE].
        - destruct EQ.
          rewrite form_eqb_refl.
          apply incl_appl, incl_refl.
        - case (form_eqb (ptree_formula Q) a) eqn:EQ.
          + contradict (NE (form_eqb_eq _ _ EQ)).
          + destruct (ptree_deg Q);
            apply incl_appr, incl_refl. }

  1 : { case nat_ltb eqn:LT;
        apply (IHP PSV). }

  1 : { case ord_ltb eqn:LT;
        apply (IHP PSV). }

  1-11 : apply (IHP PSV).

  1-5 : rewrite remove_app;
        pose proof (IHP1 P1SV) as SUB1;
        pose proof (IHP2 P2SV) as SUB2;
        apply (incl_app (incl_tran SUB1 (incl_app_app (incl_refl _) (incl_appl _ (incl_refl _)))) (incl_tran SUB2 (incl_app_app (incl_refl _) (incl_appr _ (incl_refl _))))).

  1,2 : case form_eqb eqn:FEQ;
        try apply form_eqb_eq in FEQ;
        try destruct FEQ;
        unfold node_extract;
        fold node_extract;
        rewrite remove_app;
        try rewrite remove_remove_eq in *;
        pose proof (IHP1 P1SV) as SUB1;
        pose proof (IHP2 P2SV) as SUB2.

  all : apply incl_app;
        try apply incl_appr, incl_appl, incl_refl;
        try apply (incl_tran SUB1), incl_app_app, incl_appr, incl_refl;
        try apply incl_refl;
        apply (incl_tran (remove_incl form_eq_dec a SUB2));
        rewrite remove_app;
        rewrite remove_remove_comm;
        apply incl_app_app;
        try apply incl_appl, incl_refl;
        apply incl_remove.
Qed.

Lemma string_tree_remove_sub :
    forall (P Q : ptree),
        struct_valid P ->
            incl (remove form_eq_dec (ptree_formula Q) (node_extract P)) (node_extract (string_tree P Q)).
Proof.
  intros P Q PSV.
  induction P;
  unfold string_tree;
  fold string_tree;
  unfold node_extract in *;
  fold node_extract in *.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

  1 : { unfold remove.
        case (form_eq_dec (ptree_formula Q) a) as [EQ | NE].
        - apply incl_nil_l.
        - case (form_eqb (ptree_formula Q) a) eqn:EQ.
          + contradict (NE (form_eqb_eq _ _ EQ)).
          + destruct (ptree_deg Q);
            apply incl_refl. }

  1 : { case nat_ltb eqn:LT;
        apply (IHP PSV). }

  1 : { case ord_ltb eqn:LT;
        apply (IHP PSV). }

  1-11 : apply (IHP PSV).

  1-5 : rewrite remove_app;
        apply (incl_app_app (IHP1 P1SV) (IHP2 P2SV)).

  1,2 : case form_eqb eqn:FEQ;
        try apply form_eqb_eq in FEQ;
        try destruct FEQ;
        unfold node_extract;
        fold node_extract;
        rewrite remove_app;
        try rewrite remove_remove_eq in *;
        apply incl_app_app;
        try apply incl_refl;
        try apply (IHP1 P1SV);
        rewrite remove_remove_comm;
        apply remove_incl;
        try apply (IHP2 P2SV).
Qed.

Lemma string_tree_struct_valid :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta),
        struct_valid P ->
            struct_valid (string_tree P Q).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] PSV.
  induction P;
  unfold string_tree;
  fold string_tree;
  unfold ptree_ord;
  fold ptree_ord.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

  1 : { case (form_eqb (ptree_formula Q) a) eqn:EQ.
        - apply QSV.
        - destruct (ptree_deg Q);
          repeat split;
          unfold ptree_deg;
          lia. }

  1 : { destruct (nat_semiconnex_type (ptree_deg Q) d') as [[GT | EQ] | LT];
        try apply nat_lt_ltb in LT;
        try apply nat_lt_ltb in GT;
        try destruct EQ;
        try rewrite nat_ltb_irrefl;
        try rewrite LT;
        try rewrite (nat_ltb_asymm _ _ GT);
        repeat split;
        try apply (IHP PSV);
        try rewrite (string_tree_deg _ _ PSV).
        apply nat_ltb_lt in LT.
        lia. }

  1 : { case ord_ltb eqn:LT;
        repeat split;
        try apply (IHP PSV).
        - apply ord_ltb_lt, LT.
        - apply NO. }

  1-16 : unfold node_extract in *;
        fold node_extract in *;
        repeat split;
        fold node_extract;
        try apply (IHP PSV);
        try apply (IHP1 P1SV);
        try apply (IHP2 P2SV);
        try rewrite string_tree_formula;
        try rewrite string_tree_ord;
        try apply PF;
        try apply P1F;
        try apply P2F;
        try rewrite PO;
        try rewrite P1O;
        try rewrite P2O;
        try apply P2D;
        try apply PSV;
        try apply P1SV;
        try apply P2SV;
        try reflexivity.

  1 : { rewrite (@map_nil_remove_flat _ _ form_eq_dec nat_eq_dec _ (ptree_formula Q)) in CPF.
        apply (incl_tran CPF), (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (string_tree_remove_sub _ _ PSV)).
        rewrite QF.
        apply closed_free_list, (provable_closed' Q _ (QSV,QAX) QF). }

  all : destruct form_eqb eqn:FEQ;
        try apply form_neb_ne_symm in FEQ;
        repeat split;
        try apply (IHP PSV);
        try apply (IHP1 P1SV);
        try apply (IHP2 P2SV);
        try rewrite string_tree_formula;
        try rewrite string_tree_ord;
        try apply PF;
        try apply P1F;
        try apply P2F;
        try rewrite PO;
        try rewrite P1O;
        try rewrite P2O;
        try apply P2D;
        try apply PSV;
        try apply P1SV;
        try apply P2SV;
        try reflexivity;
        try apply INA;
        try apply (string_tree_remove_sub _ _ P2SV _ (in_in_remove _ _ FEQ INA)).
Qed.

Lemma string_tree_valid :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta),
        struct_valid P ->
            (forall B : formula, In B (remove form_eq_dec A (node_extract P)) -> PA_cyclic_axiom B = true) ->
                valid (string_tree P Q).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] PSV PAX.
  induction P;
  unfold string_tree;
  fold string_tree;
  unfold ptree_ord;
  fold ptree_ord.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

  1 : { rewrite QF.
        case (form_eqb A a) eqn:EQ.
        - apply (QSV, QAX).
        - destruct (ptree_deg Q);
          repeat split;
          unfold ptree_ord;
          try apply zero_lt;
          try apply (ptree_ord_nf_struct_hyp _ _ QO QSV);
          unfold node_extract, ptree_deg;
          try lia;
          intros B INB;
          destruct INB as [EQ' | FAL];
          try inversion FAL;
          destruct EQ';
          try apply AX;
          apply PAX;
          unfold node_extract;
          fold node_extract;
          unfold remove;
          case form_eq_dec as [TT | FF];
          try destruct TT;
          try rewrite form_eqb_refl in EQ;
          try inversion EQ;
          try apply (or_introl eq_refl). }

  1 : { destruct (nat_semiconnex_type (ptree_deg Q) d') as [[GT | EQ] | LT];
        try apply nat_lt_ltb in LT;
        try apply nat_lt_ltb in GT;
        try destruct EQ;
        try rewrite nat_ltb_irrefl;
        try rewrite LT;
        try rewrite (nat_ltb_asymm _ _ GT);
        repeat split;
        try apply (IHP PSV PAX);
        try rewrite (string_tree_deg _ _ PSV).
        apply nat_ltb_lt in LT.
        lia. }

  1 : { case ord_ltb eqn:LT;
        repeat split;
        try apply (IHP PSV PAX).
        - apply ord_ltb_lt, LT.
        - apply NO. }

  all : unfold node_extract in *;
        fold node_extract in *;
        try rewrite remove_app in PAX;
        try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2];
        repeat split;
        try apply axiom_app_merge;
        try split;
        fold node_extract;
        try apply (IHP PSV PAX);
        try apply (IHP1 P1SV PAX1);
        try apply (IHP2 P2SV PAX2);
        try apply (IHP1 P1SV PAX2);
        try apply (IHP2 P2SV PAX1);
        try rewrite string_tree_formula;
        try rewrite string_tree_ord;
        try apply PF;
        try apply P1F;
        try apply P2F;
        try rewrite PO;
        try rewrite P1O;
        try rewrite P2O;
        try apply P2D;
        try apply PSV;
        try apply P1SV;
        try apply P2SV;
        try reflexivity.      

    { rewrite (@map_nil_remove_flat _ _ form_eq_dec nat_eq_dec _ (ptree_formula Q)) in CPF.
      apply (incl_tran CPF), (@flat_map_incl _ _ form_eq_dec nat_eq_dec _ _ _ (string_tree_remove_sub _ _ PSV)).
      rewrite QF.
      apply closed_free_list, (provable_closed' Q _ (QSV,QAX) QF). }

  all : destruct form_eqb eqn:FEQ.

  1,3,5,7 : apply form_eqb_eq in FEQ;
            destruct FEQ.

  5-8 : apply form_neb_ne_symm in FEQ.
        
  all : repeat rewrite QF in *;
        try rewrite (remove_remove_eq) in *;
        repeat split;
        unfold node_extract;
        fold node_extract;
        try apply axiom_app_merge;
        try split;
        try apply (IHP1 P1SV);
        try rewrite string_tree_formula;
        try rewrite string_tree_ord;
        try apply PF;
        try apply P1F;
        try apply P2F;
        try rewrite PO;
        try rewrite P1O;
        try rewrite P2O;
        try apply P2D;
        try apply PSV;
        try apply P1SV;
        try apply P2SV;
        try reflexivity;
        try apply INA;
        try apply PAX1;
        try apply PAX2;
        repeat rewrite <- QF in *;
        try apply (string_tree_remove_sub _ _ P2SV _ (in_in_remove _ _ FEQ INA)).

  1,3 : apply (string_tree_struct_valid _ _ (QF,(QSV,QAX),QD,QO)), P2SV.

  all : intros B INB;
        apply in_remove in INB as [INB NE];
        apply (string_tree_node_remove _ _ P2SV) in INB;
        apply in_app_or in INB as [INQ | IN2].

  1,3 : apply (QAX _ INQ).

  1,2 : rewrite remove_remove_comm in PAX1;
        apply (PAX1 _ (in_in_remove _ _ NE IN2)).
Qed.