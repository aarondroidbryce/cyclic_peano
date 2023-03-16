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

(*
Fixpoint left_leaves (P : ptree) : list formula :=
match P with
| deg_up d P' => left_leaves P'

| ord_up alpha P' => left_leaves P'

| node A => [A]

| exchange_ab A B d alpha P' => left_leaves P'

| exchange_cab C A B d alpha P' => left_leaves P'

| exchange_abd A B D d alpha P' => left_leaves P'

| exchange_cabd C A B D d alpha P' => left_leaves P'

| contraction_a A d alpha P' => left_leaves P'

| contraction_ad A D d alpha P' => left_leaves P'

| weakening_ad A D d alpha P' => left_leaves P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => left_leaves P1 ++ left_leaves P2

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => left_leaves P1 ++ left_leaves P2

| negation_a A d alpha P' => left_leaves P'

| negation_ad A D d alpha P' => left_leaves P'

| quantification_a A n t d alpha P' => left_leaves P'

| quantification_ad A D n t d alpha P' => left_leaves P'

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => left_leaves P1

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => left_leaves P1

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => left_leaves P1 ++ left_leaves P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => left_leaves P1 ++ left_leaves P2

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => left_leaves P1 ++ left_leaves P2
end.
*)

Fixpoint string_tree
    (P Q : ptree) {B : formula} {dQ : nat} {beta : ord} (QP : P_proves Q B dQ beta) (NAX : PA_cyclic_axiom B = false) : ptree :=
match P with
| deg_up d P' => match (nat_ltb dQ d) with
    | false => (string_tree P' Q QP NAX)
    | true => deg_up d (string_tree P' Q QP NAX)
    end

| ord_up alpha P' => ord_up (ord_add beta alpha) (string_tree P' Q QP NAX)

| node A => match form_eqb B A with
    | true => Q
    | _ => match beta with
        | Zero => (match dQ with
                  | 0 => P
                  | _ => deg_up dQ P
                  end)
        | _ => ord_up beta (match dQ with
            | 0 => P
            | _ => deg_up dQ P
            end)
        end
    end

| exchange_ab A B d alpha P' =>
    exchange_ab A B
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| exchange_cab C A B d alpha P'=>
    exchange_cab
      C A B
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| exchange_abd A B D d alpha P' =>
    exchange_abd
      A B D
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| exchange_cabd C A B D d alpha P' =>
    exchange_cabd
      C A B D
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| contraction_a A d alpha P' =>
    contraction_a
      A
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| contraction_ad A D d alpha P' =>
    contraction_ad
      A D
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| weakening_ad A D d alpha P' =>
    weakening_ad
      A D
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 =>
    demorgan_ab A B
      (ptree_deg (string_tree P1 Q QP NAX))
      (ptree_deg (string_tree P2 Q QP NAX))
      (ord_add beta alpha1)
      (ord_add beta alpha2)
      (string_tree P1 Q QP NAX)
      (string_tree P2 Q QP NAX)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 =>
    demorgan_abd
      A B D
      (ptree_deg (string_tree P1 Q QP NAX))
      (ptree_deg (string_tree P2 Q QP NAX))
      (ord_add beta alpha1)
      (ord_add beta alpha2)
      (string_tree P1 Q QP NAX)
      (string_tree P2 Q QP NAX)

| negation_a A d alpha P' =>
    negation_a
      A
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| negation_ad A D d alpha P' =>
    negation_ad
      A D
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| quantification_a A k t d alpha P' =>
    quantification_a
      A k t
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| quantification_ad A D k t d alpha P' =>
    quantification_ad
      A D k t
      (ptree_deg (string_tree P' Q QP NAX))
      (ord_add beta alpha)
      (string_tree P' Q QP NAX)

| loop_a A k d1 d2 alpha1 alpha2 P1 P2 =>
    loop_a
      A k
      (ptree_deg (string_tree P1 Q QP NAX))
      d2
      (ord_add beta alpha1)
      alpha2
      (string_tree P1 Q QP NAX) P2

| loop_ca C A k d1 d2 alpha1 alpha2 P1 P2 => (*match form_eqb B (univ k A) with
    | true => 
        loop_ca
          C A k
          (ptree_deg (string_tree P1 Q QP NAX))
          d2
          (ord_add beta alpha1)
          alpha2
          (string_tree P1 Q QP NAX) P2
    | false => *)
        loop_ca
          C A k
          (ptree_deg (string_tree P1 Q QP NAX))
          d2
          (ord_add beta alpha1)
          alpha2
          (string_tree P1 Q QP NAX) P2
(*    end*)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      C A
      (ptree_deg (string_tree P1 Q QP NAX))
      (ptree_deg (string_tree P2 Q QP NAX))
      (ord_add beta alpha1)
      (ord_add beta alpha2)
      (string_tree P1 Q QP NAX)
      (string_tree P2 Q QP NAX)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ad
      A D
      (ptree_deg (string_tree P1 Q QP NAX))
      (ptree_deg (string_tree P2 Q QP NAX))
      (ord_add beta alpha1)
      (ord_add beta alpha2)
      (string_tree P1 Q QP NAX)
      (string_tree P2 Q QP NAX)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 =>
    cut_cad
      C A D
      (ptree_deg (string_tree P1 Q QP NAX))
      (ptree_deg (string_tree P2 Q QP NAX))
      (ord_add beta alpha1)
      (ord_add beta alpha2)
      (string_tree P1 Q QP NAX)
      (string_tree P2 Q QP NAX)
end.

Lemma string_tree_formula :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        (ptree_formula (string_tree P Q QP NAX)) = (ptree_formula P).
Proof.
intros P Q A dQ beta QP NAX.
induction P;
unfold string_tree, ptree_formula;
fold string_tree ptree_formula;
try reflexivity;
try apply IHP.

- case (nat_ltb dQ d');
  try apply IHP.

- case (form_eqb A a) eqn:EQ.
  2 : destruct beta;
      destruct dQ;
      try reflexivity.

  1 : apply form_eqb_eq in EQ.
      destruct EQ.
      destruct QP as [[[QF QV] QD] QO].
      apply QF.

(*- case (form_eqb A (univ n a)) eqn:EQ;
  reflexivity. *)
Qed.

Lemma string_tree_deg :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        struct_valid P ->
            (ptree_deg (string_tree P Q QP NAX)) = max (ptree_deg P) dQ.
Proof.
intros P Q A dQ beta QP NAX PSV.
induction P;
unfold string_tree;
fold string_tree;
unfold ptree_deg;
fold ptree_deg.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

all : try rewrite (IHP PSV);
      try rewrite (IHP1 P1SV);
      try rewrite (IHP2 P2SV);
      try lia.

- destruct (nat_semiconnex_bool dQ d') as [LT | [GT | EQ]].
  + rewrite LT.
    rewrite (max_split2 _ _ LT).
    reflexivity.
  + rewrite (nat_ltb_asymm _ _ GT).
    rewrite (max_split1 _ _ GT).
    rewrite (max_split1 _ _ (nat_ltb_trans _ _ _ (nat_lt_ltb _ _ ID) GT)) in IHP.
    apply (IHP PSV).
  + apply nat_eqb_eq in EQ.
    destruct EQ.
    rewrite nat_ltb_irrefl.
    rewrite (PeanoNat.Nat.max_l _ _ (le_n _)).
    rewrite (PeanoNat.Nat.max_r _ _ (le_S_n _ _ (le_S _ _ ID))) in IHP.
    apply (IHP PSV).

- case (form_eqb A a) eqn:EQ.
  2 : destruct beta;
      destruct dQ;
      reflexivity.

  1 : destruct QP as [[[QF QV] QD] QO].
      lia.

(*- case (form_eqb A (univ n a)) eqn:EQ;
  unfold ptree_deg;
  fold ptree_deg;
  try lia. *)
Qed.

Lemma string_tree_ord :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        struct_valid P ->
            (ptree_ord (string_tree P Q QP NAX)) = ord_add beta (ptree_ord P).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] NAX PSV.
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

  all : try case (form_eqb A (univ n a)) eqn:EQ;
        unfold ptree_ord;
        fold ptree_ord;
        repeat rewrite ord_succ_add_succ;
        try rewrite ord_max_add_comm;
        try rewrite ord_add_assoc;
        try reflexivity;
        try apply nf_add;
        try apply nf_mult;
        try apply nf_nf_succ;
        try apply nf_ord_max;
        repeat apply single_nf;
        try apply zero_nf;
        try apply (ptree_ord_nf_struct_hyp _ _ PO PSV);
        try apply (ptree_ord_nf_struct_hyp _ _ P1O P1SV);
        try apply (ptree_ord_nf_struct_hyp _ _ P2O P2SV);
        try apply (ptree_ord_nf_struct_hyp _ _ QO QSV).
  
  - case (nat_ltb dQ d') eqn:LT;
    apply (IHP PSV).
  
  - try case (form_eqb A a) eqn:EQ.
    + rewrite ord_add_zero.
      auto.
    + destruct beta;
      destruct dQ;
      rewrite ord_add_zero;
      reflexivity.
Qed.

Lemma axiom_app_split :
    forall (L1 L2 : list formula),
        (forall B, In B (L1 ++ L2) -> PA_cyclic_axiom B = true) -> 
            (forall B, In B L1 -> PA_cyclic_axiom B = true) /\ (forall B, In B L2 -> PA_cyclic_axiom B = true).
Proof.
intros L1 L2.
exact (fun AX => conj (fun B INB => AX B (in_or_app _ _ _ (or_introl INB))) (fun B INB => AX B (in_or_app _ _ _ (or_intror INB)))).
Qed.

Lemma axiom_app_merge :
    forall (L1 L2 : list formula), 
        (forall B, In B L1 -> PA_cyclic_axiom B = true) /\ (forall B, In B L2 -> PA_cyclic_axiom B = true) ->
            (forall B, In B (L1 ++ L2) -> PA_cyclic_axiom B = true).
Proof.
intros L1 L2 [AX1 AX2] B INB.
apply in_app_or in INB as [IN1 | IN2].
apply (AX1 _ IN1).
apply (AX2 _ IN2).
Qed.

Lemma string_tree_node_not_in :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        struct_valid P ->
            ~ In A (node_extract P) ->
                (node_extract (string_tree P Q QP NAX)) = (node_extract P).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] NAX PSV NIN.
  induction P;
  unfold string_tree;
  fold string_tree;
  unfold node_extract in *;
  fold node_extract in *.
  
  1 : destruct PSV as [ID PSV].
  2 : destruct PSV as [[IO PSV] NO].
  3 : destruct PSV.
  4-9 : destruct PSV as [[[PF PSV] PD] PO].
  10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
  13-16 : destruct PSV as [[[PF PSV] PD] PO].
  11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

  all : try case (nat_ltb dQ d') eqn:LT;
        try case (form_eqb A (univ n a)) eqn:FEQ;
        unfold node_extract;
        try case (closed c) eqn:CC;
        fold node_extract;
        unfold "&&" in *;
        try apply (IHP PSV NIN);
        try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
        try split;
        try rewrite (IHP1 P1SV NIN1);
        try rewrite (IHP2 P2SV NIN2);
        try reflexivity.

  1 : { try case (form_eqb A a) eqn:FEQ.
        2 : destruct beta, dQ;
            reflexivity.
        1 : apply form_eqb_eq in FEQ.
            destruct FEQ.
            contradict (NIN (or_introl eq_refl)). }

  1,2,3,5 : case (closed (univ n a)) eqn:UnA.

  all : try apply not_in_cons in NIN as [NE NIN];
        try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
        try rewrite (IHP1 P1SV NIN2);
        try reflexivity.
Qed.

(*
Lemma string_tree_node_remove :
    forall (P Q : ptree) (A : formula) (dQ : nat) (beta : ord) (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        struct_valid P ->
            incl (node_extract (string_tree P Q QP NAX)) ((node_extract Q) ++ (remove form_eq_dec A (node_extract P))).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] NAX PSV.
  induction P;
  unfold string_tree;
  fold string_tree;
  unfold node_extract in *;
  fold node_extract in *.
  
  1 : destruct PSV as [ID PSV].
  2 : destruct PSV as [[IO PSV] NO].
  3 : destruct PSV.
  4-9 : destruct PSV as [[[PF PSV] PD] PO].
  10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
  13-16 : destruct PSV as [[[PF PSV] PD] PO].
  11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

  1-12,15-21 :
      try case (nat_ltb dQ d') eqn:LT;
      unfold node_extract;
      fold node_extract;
(*      try destruct (in_dec form_eq_dec A (node_extract P1)) as [IN1 | NIN1];
      try destruct (in_dec form_eq_dec A (node_extract P2)) as [IN2 | NIN2];
      try rewrite (string_tree_node_not_in _ _ _ P1SV NIN1);
      try rewrite (string_tree_node_not_in _ _ _ P2SV NIN2); *)
      try rewrite remove_app;
      (*try rewrite (notin_remove _ _ _ NIN1);
      try rewrite (notin_remove _ _ _ NIN2);*)
      try apply (IHP PSV);
      try pose proof (IHP1 P1SV) as SUB1;
      try pose proof (IHP2 P2SV) as SUB2;
      try apply (incl_app (incl_tran SUB1 (incl_app_app (incl_refl _) (incl_appl _ (incl_refl _)))) (incl_tran SUB2 (incl_app_app (incl_refl _) (incl_appr _ (incl_refl _)))));
      try apply (incl_app (incl_appr _ (incl_appl _ (incl_refl _))) (incl_tran SUB2 (incl_app_app (incl_refl _) (incl_appr _ (incl_refl _)))));
      try apply incl_refl;
      try apply (incl_appr _ (incl_refl _));
      try rewrite (app_assoc (node_extract Q) (remove form_eq_dec A (node_extract P1)) (node_extract P2));
      try apply (incl_app (incl_appl _ SUB1) (incl_appr _ (incl_refl _)));
      try reflexivity.

  1 : { unfold remove.
        case (form_eq_dec A a) as [EQ | NE].
        - destruct EQ.
          rewrite form_eqb_refl.
          apply incl_appl, incl_refl.
        - case (form_eqb A a) eqn:EQ.
          + contradict (NE (form_eqb_eq _ _ EQ)).
          + destruct beta;
            destruct dQ;
            apply incl_appr, incl_refl. }

  case (closed (univ n a)) eqn:CuA.
  apply incl_app.
  rewrite remove_app.
  rewrite (app_assoc (node_extract Q) (remove form_eq_dec a (node_extract P2)) (node_extract P1)).
      

Admitted.
*)

Lemma free_list_remove_non_ax_sub :
    forall (P : ptree) (A : formula),
        In A (node_extract P) ->
            (forall B : formula, In B (remove form_eq_dec A (node_extract P)) -> PA_cyclic_axiom B = true) ->
                incl (flat_map free_list (node_extract P)) (free_list A).
Proof.
intros P A INA AX n IN.
case (in_dec nat_eq_dec n (free_list A)) as [TT | FF].
- apply TT.
- pose proof (@flat_map_not_in_remove _ _ form_eq_dec nat_eq_dec _ _ _ _ IN FF) as FAL.
  apply in_flat_map in FAL as [B [INB FAL]].
  rewrite closed_free_list in FAL.
  inversion FAL.
  apply axiom_closed, AX, INB.
Qed.

Lemma in_app_bor {A : Type} {DEC : forall (a b : A), {a = b} + {a <> b}} :
    forall (L1 L2 : list A) (a : A),
        In a (L1 ++ L2) ->
            {In a L1} + {In a L2}.
Proof.
intros L1 L2 a IN.
case (in_dec DEC a L1) as [IN1 | NIN1].
- apply (left IN1).
- case (in_dec DEC a L2) as [IN2 | NIN2].
  + apply (right IN2).
  + pose proof (nin_merge _ _ _ (conj NIN1 NIN2) IN) as FAL.
    inversion FAL.
Qed.

Lemma string_tree_struct :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        struct_valid P ->
            struct_valid (string_tree P Q QP NAX).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] NAX PSV.
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

  1 : { destruct (nat_semiconnex_type dQ d') as [[GT | EQ] | LT];
        try apply nat_lt_ltb in LT;
        try apply nat_lt_ltb in GT;
        try destruct EQ;
        try rewrite nat_ltb_irrefl;
        try rewrite LT;
        try rewrite (nat_ltb_asymm _ _ GT);
        repeat split;
        try apply (IHP PSV);
        try rewrite (string_tree_deg _ _ _ _ PSV).
        apply nat_ltb_lt in LT.
        lia. }

  1 : { repeat split;
        try apply (IHP PSV).
        - rewrite (string_tree_ord _ _ _ _ PSV).
          apply add_right_incr, IO.
        - apply (nf_add _ _ (ptree_ord_nf_struct_hyp _ _ QO QSV) NO). }

  1 : { case (form_eqb A a) eqn:EQ.
        1 : apply (QSV, QAX).
        1 : destruct beta;
          destruct dQ;
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

    11 : case (form_eqb A (univ n a)) eqn:FEQ.

    all : unfold node_extract in *;
          fold node_extract in *;
          repeat split;
          try apply (IHP PSV);
          try apply (IHP1 P1SV);
          try apply (IHP2 P2SV);
          try rewrite string_tree_formula;
          (*try rewrite string_tree_ord;*)
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

    1 : { admit. }
Admitted.

Lemma string_tree_nin_valid :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        struct_valid P ->
            ~ In A (node_extract P) ->
                (forall B : formula, In B (remove form_eq_dec A (node_extract P)) -> PA_cyclic_axiom B = true) ->
                    valid (string_tree P Q QP NAX).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] NAX PSV NINA PAX.
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

  1 : { destruct (nat_semiconnex_type dQ d') as [[GT | EQ] | LT];
        try apply nat_lt_ltb in LT;
        try apply nat_lt_ltb in GT;
        try destruct EQ;
        try rewrite nat_ltb_irrefl;
        try rewrite LT;
        try rewrite (nat_ltb_asymm _ _ GT);
        repeat split;
        try apply (IHP PSV NINA PAX);
        try rewrite (string_tree_deg _ _ _ _ PSV).
        apply nat_ltb_lt in LT.
        lia. }

  1 : { repeat split;
        try apply (IHP PSV NINA PAX).
        - rewrite (string_tree_ord _ _ _ _ PSV).
          apply add_right_incr, IO.
        - apply (nf_add _ _ (ptree_ord_nf_struct_hyp _ _ QO QSV) NO). }

  1 : { case (form_eqb A a) eqn:EQ.
        1 : apply (QSV, QAX).
        1 : destruct beta;
          destruct dQ;
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

    11 : case (form_eqb A (univ n a)) eqn:FEQ.

    all : unfold node_extract in *;
          fold node_extract in *;
          try rewrite remove_app in PAX;
          try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2];
          try apply (nin_split form_eq_dec) in NINA as [NINA1 NINA2];
          repeat split;
          try apply axiom_app_merge;
          try split;
          fold node_extract;
          try apply (IHP PSV NINA PAX);
          try apply (IHP1 P1SV NINA1 PAX1);
          try apply (IHP2 P2SV NINA2 PAX2);
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

    1 : { rewrite (string_tree_node_not_in _ _ _ _ PSV NINA).
          apply FC. }

    all : unfold node_extract;
          fold node_extract;
          try case (closed c) eqn:CC;
          unfold "&&" in *;
          case (closed (univ n a)) eqn:CuA;
          try apply not_in_cons in NINA as [NE NINA];
          try rewrite (remove_not_head _ _ _ NE) in PAX;
          try rewrite remove_app in PAX;
          try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2];
          try apply (nin_split form_eq_dec) in NINA as [NINA1 NINA2];
          try apply (IHP1 P1SV NINA2 PAX2);
          try apply (IHP2 P2SV NINA1 PAX1);
          try pose proof (PAX _ (or_introl eq_refl)) as FAL;
          try inversion FAL;
          try apply axiom_app_merge;
          split;
          try apply (IHP1 P1SV NINA2 PAX2);
          try rewrite (notin_remove _ _ _ NINA1) in PAX1;
          try apply PAX1.
Qed.

Lemma open_loop_ax_head_one_empty_nodes :
    forall {P1 P2 : ptree} {a A : formula} {n : nat},
        (count_occ form_eq_dec (univ n a :: remove form_eq_dec a (node_extract P2) ++ node_extract P1) A = 1) ->
            (forall B : formula, In B (remove form_eq_dec A (univ n a :: remove form_eq_dec a (node_extract P2) ++ node_extract P1)) -> PA_cyclic_axiom B = true) ->
                ~ In A (remove form_eq_dec a (node_extract P2)) /\ ~In A (node_extract P1).
Proof.
intros P1 P2 a A n ONE PAX.
assert (univ n a = A) as FEQ.
{ unfold remove in PAX;
  fold (remove form_eq_dec) in PAX.
  case (form_eq_dec A (univ n a)) as [FEQ' | NE].
  - rewrite FEQ'.
    reflexivity.
  - pose proof (PAX _ (or_introl eq_refl)) as FAL.
    inversion FAL. }

rewrite (count_occ_cons_eq _ _ FEQ) in ONE.
inversion ONE as [ONE'].
rewrite count_occ_app in ONE'.
split;
apply (count_occ_not_In form_eq_dec);
destruct (count_occ form_eq_dec (remove form_eq_dec a (node_extract P2)) A);
try reflexivity;
try apply ONE';
try rewrite plus_Sn_m in ONE';
inversion ONE'.
Qed.

Lemma string_tree_nin_valid_strong :
    forall (P Q : ptree) {A : formula} {dQ : nat} {beta : ord} (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        struct_valid P ->
            ~ In A (node_extract P) ->
                (forall B : formula, In B (node_extract P) -> PA_cyclic_axiom B = true) ->
                    valid (string_tree P Q QP NAX).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] NAX PSV NINA PAX.
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

  1 : { destruct (nat_semiconnex_type dQ d') as [[GT | EQ] | LT];
        try apply nat_lt_ltb in LT;
        try apply nat_lt_ltb in GT;
        try destruct EQ;
        try rewrite nat_ltb_irrefl;
        try rewrite LT;
        try rewrite (nat_ltb_asymm _ _ GT);
        repeat split;
        try apply (IHP PSV NINA PAX);
        try rewrite (string_tree_deg _ _ _ _ PSV).
        apply nat_ltb_lt in LT.
        lia. }

  1 : { repeat split;
        try apply (IHP PSV NINA PAX).
        - rewrite (string_tree_ord _ _ _ _ PSV).
          apply add_right_incr, IO.
        - apply (nf_add _ _ (ptree_ord_nf_struct_hyp _ _ QO QSV) NO). }

  1 : { case (form_eqb A a) eqn:EQ.
        1 : apply (QSV, QAX).
        1 : destruct beta;
          destruct dQ;
          repeat split;
          unfold ptree_ord;
          try apply zero_lt;
          try apply PAX;
          try apply (ptree_ord_nf_struct_hyp _ _ QO QSV);
          unfold node_extract, ptree_deg;
          try lia. }

    11 : case (form_eqb A (univ n a)) eqn:FEQ.

    all : unfold node_extract in *;
          fold node_extract in *;
          try rewrite remove_app in PAX;
          try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2];
          try apply (nin_split form_eq_dec) in NINA as [NINA1 NINA2];
          repeat split;
          try apply axiom_app_merge;
          try split;
          fold node_extract;
          try apply (IHP PSV NINA PAX);
          try apply (IHP1 P1SV NINA1 PAX1);
          try apply (IHP2 P2SV NINA2 PAX2);
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

    1 : { rewrite (string_tree_node_not_in _ _ _ _ PSV NINA).
          apply FC. }

    all : unfold node_extract;
          fold node_extract;
          try case (closed c) eqn:CC;
          unfold "&&" in *;
          case (closed (univ n a)) eqn:CuA;
          try apply not_in_cons in NINA as [NE NINA];
          try rewrite (remove_not_head _ _ _ NE) in PAX;
          try rewrite remove_app in PAX;
          try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2];
          try apply (nin_split form_eq_dec) in NINA as [NINA1 NINA2];
          try apply (IHP1 P1SV NINA2 PAX2);
          try apply (IHP2 P2SV NINA1 PAX1);
          try pose proof (PAX _ (or_introl eq_refl)) as FAL;
          try inversion FAL;
          try apply axiom_app_merge;
          split;
          try apply (IHP1 P1SV NINA2 PAX2);
          try rewrite (notin_remove _ _ _ NINA1) in PAX1;
          try apply PAX1.
Qed.

Lemma open_loop_ax_head_one_split :
    forall {P1 P2 : ptree} {a A : formula} {n : nat},
        (count_occ form_eq_dec (univ n a :: remove form_eq_dec a (node_extract P2) ++ node_extract P1) A = 1) ->
            (forall B : formula, In B (remove form_eq_dec A (univ n a :: remove form_eq_dec a (node_extract P2) ++ node_extract P1)) -> PA_cyclic_axiom B = true) ->
                (forall B : formula, In B (remove form_eq_dec a (node_extract P2)) -> PA_cyclic_axiom B = true) /\                 (forall B : formula, In B (node_extract P1) -> PA_cyclic_axiom B = true).
Proof.
intros P1 P2 a A n ONE PAX.
destruct (open_loop_ax_head_one_empty_nodes ONE PAX) as [NIN2 NIN1].
unfold remove in PAX;
fold (remove form_eq_dec) in PAX.
case (form_eq_dec A (univ n a)) as [FEQ' | NE].
- rewrite remove_app in PAX.
  rewrite (notin_remove _ _ _ NIN1) in PAX.
  rewrite (notin_remove _ _ _ NIN2) in PAX.
  split.
  + apply (fun B INB => PAX B (in_or_app _ _ _ (or_introl INB))).
  + apply (fun B INB => PAX B (in_or_app _ _ _ (or_intror INB))).
- pose proof (PAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.
Qed.

Lemma string_tree_valid :
    forall (P Q : ptree) (A : formula) (dQ : nat) (beta : ord) (QP : P_proves Q A dQ beta) (NAX : PA_cyclic_axiom A = false),
        struct_valid P ->
            count_occ form_eq_dec (node_extract P) A = 1 ->
                (forall B : formula, In B (remove form_eq_dec A (node_extract P)) -> PA_cyclic_axiom B = true) ->
                    valid (string_tree P Q QP NAX).
Proof.
  intros P Q A dQ beta [[[QF [QSV QAX]] QD] QO] NAX PSV ONE PAX.
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

  1 : { destruct (nat_semiconnex_type dQ d') as [[GT | EQ] | LT];
        try apply nat_lt_ltb in LT;
        try apply nat_lt_ltb in GT;
        try destruct EQ;
        try rewrite nat_ltb_irrefl;
        try rewrite LT;
        try rewrite (nat_ltb_asymm _ _ GT);
        repeat split;
        try apply (IHP PSV ONE PAX);
        try rewrite (string_tree_deg _ _ _ _ PSV).
        apply nat_ltb_lt in LT.
        lia. }

  1 : { repeat split;
        try apply (IHP PSV ONE PAX).
        - rewrite (string_tree_ord _ _ _ _ PSV).
          apply add_right_incr, IO.
        - apply (nf_add _ _ (ptree_ord_nf_struct_hyp _ _ QO QSV) NO). }

  1 : { case (form_eqb A a) eqn:EQ.
        1 : apply (QSV, QAX).
        1 : destruct beta;
          destruct dQ;
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

(*  11 : case (form_eqb A (univ n a)) eqn:FEQ.*)

  all : unfold node_extract in *;
        fold node_extract in *;
        try rewrite remove_app in PAX;
        try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2];
        repeat split;
        try apply axiom_app_merge;
        try split;
        fold node_extract;
        try apply (IHP PSV ONE PAX);
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

    { assert (count_occ form_eq_dec (node_extract P) A > 0) as INA.
      { rewrite ONE.
        apply le_n. }
      apply count_occ_In in INA.
      pose proof (incl_tran FC (free_list_remove_non_ax_sub _ _ INA PAX)).
      admit. }

  1-8,13-24 :
      destruct (count_occ_app_one_split _ _ _ ONE) as [[ONE1 NIN2] | [ONE2 NIN1]];
      try apply (IHP1 P1SV ONE1 PAX1);
      try apply (IHP2 P2SV ONE2 PAX2);
      try apply (string_tree_nin_valid _ _ _ _ P1SV NIN1 PAX1);
      try apply (string_tree_nin_valid _ _ _ _ P2SV NIN2 PAX2).

  all : unfold node_extract;
      fold node_extract;
      try case (closed c) eqn:CC;
      unfold "&&" in *;
      try case (closed (univ n a)) eqn:CuA;
      try rewrite remove_app in PAX;
      try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2].

  1,5 :
      destruct (count_occ_app_one_split _ _ _ ONE) as [[ONE1 NIN2] | [ONE2 NIN1]];
      try apply (IHP1 P1SV ONE2 PAX2);
      try apply (string_tree_nin_valid _ _ _ _ P1SV NIN2 PAX2).

  1,4,5,6 :
      destruct (open_loop_ax_head_one_empty_nodes ONE PAX) as [NIN2 NIN1];
      apply (open_loop_ax_head_one_split ONE) in PAX as [PAX2 PAX1];
      try apply (string_tree_nin_valid_strong _ _ _ _ P1SV NIN1 PAX1).

  admit.

  admit.

(*  1-8,15-26 :*)
    1-8,13-24 :
      case (in_dec form_eq_dec A (node_extract P1)) as [IN1 | NIN1];
      case (in_dec form_eq_dec A (node_extract P2)) as [IN2 | NIN2];
      try apply (IHP1 P1SV IN1 PAX1);
      try apply (IHP2 P2SV IN2 PAX2);
      try apply (string_tree_nin_valid _ _ _ _ P1SV NIN1 PAX1);
      try apply (string_tree_nin_valid _ _ _ _ P2SV NIN2 PAX2).

  all : unfold node_extract;
        fold node_extract;
        try case (closed c) eqn:CC;
        unfold "&&" in *;
        try case (closed (univ n a)) eqn:CuA;
        try rewrite remove_app in PAX;
        try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2].

  1,5 : case (in_dec form_eq_dec A (node_extract P1)) as [IN1 | NIN1];
      try apply (IHP1 P1SV IN1 PAX2);
      try apply (string_tree_nin_valid _ _ _ _ P1SV NIN1 PAX2).

  admit. (*univ*)

  
  
  admit. (*ax*)

  admit. (*univ*)
  
  admit. (*univ*)

  admit. (*univ*)

  admit. (*univ*)

  admit. (*ax*)

  admit. (*univ*)

  admit. (*univ*)

  admit. (*univ*)


        (*

        admit.

  1,2,9,10 :
        case (in_dec form_eq_dec A (node_extract P1)) as [IN1 | NIN1];
        case (in_dec form_eq_dec A (node_extract P2)) as [IN2 | NIN2];
        try apply (IHP1 P1SV IN1 PAX2);
        try apply (IHP2 P2SV IN2 PAX1);
        try apply (string_tree_nin_valid _ _ _ _ P1SV NIN1 PAX2);
        try apply (string_tree_nin_valid _ _ _ _ P2SV NIN2 PAX1).

  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.

  all : unfold remove in PAX;
        fold (remove form_eq_dec) in PAX;
        try apply form_eqb_eq in FEQ;
        try rewrite FEQ in *;
        try case form_eq_dec as [TT | FF];
        try rewrite TT in FEQ;
        try rewrite form_eqb_refl in FEQ;
        try inversion FEQ as [FEQ'];
        try contradict (FF eq_refl);
        try pose proof (PAX _ (or_introl eq_refl)) as FAL;
        try inversion FAL.

  1,2,3 : try rewrite remove_app in PAX;
        try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2];
        destruct FEQ;
        case (in_dec form_eq_dec A (node_extract P1)) as [IN1 | NIN1];
        try apply (IHP1 P1SV IN1 PAX2);
        try apply (string_tree_nin_valid _ _ _ _ P1SV NIN1 PAX2).


        admit. admit. admit. admit. admit. admit. admit.
        
  1,2 : try rewrite remove_app in PAX;
        try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2];
        case (in_dec form_eq_dec A (node_extract P1)) as [IN1 | NIN1];
        try apply (IHP1 P1SV IN1 PAX2);
        try apply (string_tree_nin_valid _ _ _ _ P1SV NIN1 PAX2).


        admit. admit. admit. admit. admit.
        admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit.
  1-3,6-10 :
      unfold remove in PAX;
      fold (remove form_eq_dec) in PAX;
      apply form_eqb_eq in FEQ;
      destruct FEQ;
      case (form_eq_dec A A) as [_ | FAL];
      try symmetry in FAL;
      try destruct (not_eq_univ _ _ FAL);
      pose proof (PAX _ (or_introl eq_refl)) as FAL;
      inversion FAL.

  1,2 : 
      apply form_eqb_eq in FEQ;
      destruct FEQ;
      rewrite remove_remove_eq in PAX1;
      apply in_app_or in INA as [IN1 | IN2];
      try destruct (remove_In _ _ _ IN1);
      apply axiom_app_merge;
      split;
      try apply PAX1;
      apply (IHP1 P1SV IN2 PAX2).

      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.

   try rewrite remove_app in PAX.
    try destruct (axiom_app_split _ _ PAX) as [PAX1 PAX2].
        

  discriminate.
  discriminate FAL.

  1,2,5-11,14-18 :
      unfold remove in PAX;
      fold (remove form_eq_dec) in PAX;
      case form_eq_dec as [FEQ | FNE];
      try pose proof (PAX _ (or_introl eq_refl)) as FAL;
      try inversion FAL.

      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.

  all : try apply axiom_app_merge;
        try split;
        fold node_extract;
        case (in_dec form_eq_dec A (node_extract P1)) as [IN1 | NIN1];
        case (in_dec form_eq_dec A (remove form_eq_dec a (node_extract P2))) as [IN2 | NIN2];
        try apply (IHP1 P1SV IN1 PAX2);
        try apply (IHP2 P2SV IN2 PAX1);
        try apply (string_tree_nin_valid _ _ _ P1SV NIN1 PAX2);
        try apply (string_tree_nin_valid _ _ _ P2SV NIN2 PAX1);
        try rewrite (notin_remove _ _ _ NIN2) in PAX1;
        try apply PAX1.

        admit.
        rewrite (notin_remove _ _ _ NIN2) in PAX1.

           (*univ*)
  
  
Admitted.
