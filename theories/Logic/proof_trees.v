From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import PA_cyclic.
Require Import Lia.
Require Import List.
Import ListNotations.

Inductive ptree : Type :=
| deg_up : forall (d' : nat) (P' : ptree), ptree

| ord_up : forall (beta : ord) (P' : ptree), ptree

| node : forall (a : formula), ptree

| exchange_ab : forall (a b : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| exchange_cab : forall (c a b : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| exchange_abd : forall (a b d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| exchange_cabd : forall (c a b d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| contraction_a : forall (a : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| contraction_ad : forall (a d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| weakening_ad : forall (a d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| demorgan_ab : forall (a b : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| demorgan_abd : forall (a b d : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| negation_a : forall (a : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| negation_ad :  forall (a d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| quantification_a :  forall (a : formula) (m : nat) (t : c_term) (d : nat) (alpha : ord) (P' : ptree), ptree

| quantification_ad : forall (a d : formula) (m : nat) (t : c_term) (d : nat) (alpha : ord) (P' : ptree), ptree

| loop_a : forall (a : formula) (n d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| loop_ca : forall (c a : formula) (n d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| cut_ca : forall (c a : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| cut_ad : forall (a d : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| cut_cad : forall (c a d : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree.

Fixpoint ptree_formula (P : ptree) : formula :=
match P with
| deg_up d P' => ptree_formula P'

| ord_up alpha P' => ptree_formula P'

| node A => A

| exchange_ab A B d alpha P' => lor B A

| exchange_cab C A B d alpha P' => lor (lor C B) A

| exchange_abd A B D d alpha P' => lor (lor B A) D

| exchange_cabd C A B D d alpha P' => lor (lor (lor C B) A) D

| contraction_a A d alpha P' => A

| contraction_ad A D d alpha P' => lor A D

| weakening_ad A D d alpha P' => lor A D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => neg (lor A B)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => lor (neg (lor A B)) D

| negation_a A d alpha P' => neg (neg A)

| negation_ad A D d alpha P' => lor (neg (neg A)) D

| quantification_a A n t d alpha P' => neg (univ n A)

| quantification_ad A D n t d alpha P' => lor (neg (univ n A)) D

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => (univ n A)

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => lor C (univ n A)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => C

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => D

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => lor C D
end.


Fixpoint ptree_deg (P : ptree) : nat :=
match P with
| deg_up d P' => d

| ord_up alpha P' => ptree_deg P'

| node A => 0

| exchange_ab A B d alpha P' => d

| exchange_cab E A B d alpha P' => d

| exchange_abd A B D d alpha P' => d

| exchange_cabd E A B D d alpha P' => d

| contraction_a A d alpha P' => d

| contraction_ad A D d alpha P' => d

| weakening_ad A D d alpha P' => d

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| negation_a A d alpha P' => d

| negation_ad A D d alpha P' => d

| quantification_a A n t d alpha P' => d

| quantification_ad A D n t d alpha P' => d

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| loop_ca A D n d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))
end.

Fixpoint ptree_ord (P : ptree) : ord :=
match P with
| deg_up d P' => ptree_ord P'

| ord_up alpha P' => alpha

| node A => Zero

| exchange_ab A B d alpha P' => alpha

| exchange_cab E A B d alpha P' => alpha

| exchange_abd A B D d alpha P' => alpha

| exchange_cabd E A B D d alpha P' => alpha

| contraction_a A d alpha P' => alpha

| contraction_ad A D d alpha P' => alpha

| weakening_ad A D d alpha P' => (ord_succ alpha)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| negation_a A d alpha P' => ord_succ alpha

| negation_ad A D d alpha P' => ord_succ alpha

| quantification_a A n t d alpha P' => ord_succ alpha

| quantification_ad A D n t d alpha P' => ord_succ alpha

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_add alpha1 (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)))

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_add alpha1 (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)))

| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_succ (ord_max alpha1 alpha2))

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)
end.

Fixpoint node_extract (P : ptree) : list formula :=
match P with
| deg_up d P' => node_extract P'

| ord_up alpha P' => node_extract P'

| node A => [A]

| exchange_ab A B d alpha P' => node_extract P'

| exchange_cab C A B d alpha P' => node_extract P'

| exchange_abd A B D d alpha P' => node_extract P'

| exchange_cabd C A B D d alpha P' => node_extract P'

| contraction_a A d alpha P' => node_extract P'

| contraction_ad A D d alpha P' => node_extract P'

| weakening_ad A D d alpha P' => node_extract P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| negation_a A d alpha P' => node_extract P'

| negation_ad A D d alpha P' => node_extract P'

| quantification_a A n t d alpha P' => node_extract P'

| quantification_ad A D n t d alpha P' => node_extract P'

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 =>
    match closed (univ n A) with
    | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
    | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
    end

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => 
    match (closed C) && (closed (univ n A)) with
        | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        end

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2
end.

Fixpoint struct_valid (P : ptree) : Type :=
match P with
| deg_up d P' => (d > ptree_deg P') * (struct_valid P')

| ord_up alpha P' => (ord_lt (ptree_ord P') alpha) * (struct_valid P') * (nf alpha)

| node A => (true = true)

| exchange_ab A B d alpha P' =>
    (ptree_formula P' = lor A B) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_cab E A B d alpha P' =>
    (ptree_formula P' = lor (lor E A) B) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_abd A B D d alpha P' =>
    (ptree_formula P' = lor (lor A B) D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_cabd E A B D d alpha P' =>
    (ptree_formula P' = lor (lor (lor E A) B) D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| contraction_a A d alpha P' =>
    (ptree_formula P' = lor A A) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| contraction_ad A D d alpha P' =>
    (ptree_formula P' = lor (lor A A) D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| weakening_ad A D d alpha P' =>
    (ptree_formula P' = D) * (incl (free_list A) (flat_map free_list (node_extract P'))) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = neg A) * (struct_valid P1) *
    (ptree_formula P2 = neg B) * (struct_valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor (neg A) D) * (struct_valid P1) *
    (ptree_formula P2 = lor (neg B) D) * (struct_valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| negation_a A d alpha P' =>
    (ptree_formula P' = A) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| negation_ad A D d alpha P' =>
    (ptree_formula P' = lor A D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')


| quantification_a A n t d alpha P' =>
    (ptree_formula P' = neg (substitution A n (projT1 t))) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| quantification_ad A D n t d alpha P' =>
    (ptree_formula P' = lor (neg (substitution A n (projT1 t))) D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = substitution A n zero) * (struct_valid P1) *
    (ptree_formula P2 = substitution A n (succ (var n))) * (struct_valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor C (substitution A n zero)) * (struct_valid P1) *
    (ptree_formula P2 = (substitution A n (succ (var n)))) * (struct_valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor E A) * (struct_valid P1) *
    (ptree_formula P2 = neg A) * (struct_valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = A) * (struct_valid P1) *
    (ptree_formula P2 = lor (neg A) D) * (struct_valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor E A) * (struct_valid P1) *
    (ptree_formula P2 = lor (neg A) D) * (struct_valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)
end.

Definition valid (P : ptree) : Type := (struct_valid P) * (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true).

Definition P_proves (P : ptree) (A : formula) (d : nat) (alpha : ord) : Type :=
  (ptree_formula P = A) * (valid P) *
  (d = ptree_deg P) * (alpha = ptree_ord P).

Definition provable (A : formula) (d : nat) (alpha : ord) : Type :=
  {P : ptree & P_proves P A d alpha}.

Lemma structural_pre_theorem :
    forall {A : formula} {d : nat} {alpha : ord} {L : list formula} (ST : PA_cyclic_pre A d alpha L),
        {P : ptree & prod (prod( prod (prod (ptree_formula P = A) (struct_valid P)) (d = ptree_deg P)) (alpha = ptree_ord P)) (node_extract P = L)}.
intros A d alpha L TS.
induction TS;
try destruct IHTS as [P [[[[PF PSV] PD] PO] PN]];
try destruct IHTS1 as [P1 [[[[P1F P1SV] P1D] P1H] P1N]];
try destruct IHTS2 as [P2 [[[[P2F P2SV] P2D] P2H] P2N]].
- exists (deg_up d' P). repeat split; auto. lia.
- exists (ord_up beta P). repeat split; auto. rewrite <- PO. auto.
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
  rewrite P2N, P1N.
  destruct LSTC as [LSTn | LSTe].
  + rewrite LSTn, nat_eqb_refl, list_eqb_refl.
    unfold "&&".
    case (closed A);
    reflexivity.
  + rewrite LSTe.
    reflexivity.
- exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N, CC.
  destruct LSTC as [LSTn | LSTe].
  + rewrite LSTn.
    rewrite nat_eqb_refl.
    rewrite list_eqb_refl.
    unfold "&&".
    case (closed A);
    reflexivity.
  + rewrite LSTe.
    reflexivity.
- exists (loop_a A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N.
  destruct LSTN as [LSTn LSTe].
  destruct (free_list A) as [| m FLA] eqn:FL.
  + contradict LSTe.
    reflexivity.
  + case (closed A) eqn:CA.
    * apply closed_free_list in CA.
      rewrite CA in FL.
      inversion FL.
    * destruct FLA.
      --  case (nat_eqb m n) eqn:EQ.
          ++  apply nat_eqb_eq in EQ.
              destruct EQ.
              contradict LSTn.
              reflexivity.
          ++  unfold "&&".
              reflexivity.
      --  unfold list_eqb, "&&".
          case nat_eqb;
          reflexivity.
- exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N.
  destruct LSTN as [[LSTn LSTe] | CC].
  destruct (free_list A) as [| m FLA] eqn:FL.
  + contradict LSTe.
    reflexivity.
  + destruct FLA.
    * case (nat_eqb m n) eqn:EQ.
      --  apply nat_eqb_eq in EQ.
          destruct EQ.
          contradict LSTn.
          reflexivity.
      --  case (closed C);
          reflexivity.
    * unfold list_eqb, "&&".
      case (closed C), (nat_eqb m n);
      try reflexivity.
  + rewrite CC.
    reflexivity.
- exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
- exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
- exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
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
  intros B INB.
  rewrite P2L, P1L in INB.
  destruct LSTC as [LSTn | LSTe].
  + rewrite LSTn, nat_eqb_refl, list_eqb_refl in INB.
    unfold "&&" in INB.
    apply TAX, INB.
  + rewrite LSTe in INB.
    apply TAX, INB.
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  intros B INB.
  rewrite P2L, P1L, CC in INB.
  destruct LSTC as [LSTn | LSTe].
  + rewrite LSTn, nat_eqb_refl, list_eqb_refl in INB.
    unfold "&&" in INB.
    apply TAX, INB.
  + rewrite LSTe in INB.
    apply TAX, INB.
- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.
- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.
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
        PA_cyclic_pre (ptree_formula P) (ptree_deg P) (ptree_ord P) (node_extract P).
Proof.
intros P PSV. induction P.

1 : destruct PSV as [LT PSV]. (*deg up*)
2 : destruct PSV as [[LT PSV] NO]. (*ord up*)
3 : destruct PSV as []. (*node*)
4-9,13-16 :  destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF CPF] PSV] PD] PO]. (*weakening*)
15-21 : destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O]; (*double hyp*)
        rewrite P1F,<-P1D,<-P1O in IHP1;
        rewrite P2F,<-P2D,<-P2O in IHP2;
        pose proof (IHP1 P1SV) as P1';
        pose proof (IHP2 P2SV) as P2'.

1-14 :  try rewrite PF,<-PD,<-PO in IHP;
        try pose proof (IHP PSV) as P'.
      
1 : apply (deg_incr _ _ P' LT).
1 : apply (ord_incr _ _ P' LT NO).
1 : apply (axiom _).
1 : apply (exchange1 P').
1 : apply (exchange2 P').
1 : apply (exchange3 P').
1 : apply (exchange4 P').
1 : apply (contraction1 P').
1 : apply (contraction2 _ P').
1 : apply (negation1 P').
1 : apply (negation2 P').
1 : apply (quantification1 P').
1 : apply (quantification2 P').
1 : apply (weakening _ CPF P').
1 : apply (demorgan1 P1' P2').
1 : apply (demorgan2 P1' P2').
3 : apply (cut1 _ _ P1' P2').
3 : apply (cut2 _ _ P1' P2').
3 : apply (cut3 _ _ _ P1' P2').

all : unfold node_extract;
      fold node_extract;
      unfold closed;
      fold closed;
      try case (closed c) eqn:Cc;
      destruct (free_list a) as [| m L] eqn:FLa;
      try rewrite (free_list_closed _ FLa);
      unfold "&&";
      try apply (oneloop1 _ _ (or_intror FLa) (IHP1 P1SV) (IHP2 P2SV));
      try apply (oneloop2 _ _ (or_intror FLa) Cc (IHP1 P1SV) (IHP2 P2SV)).

  1,2 : case (closed a) eqn:CA.
  1,3 : apply closed_free_list in CA;
        rewrite FLa in CA;
        inversion CA.

  1,2 : destruct L;
        case (nat_eqb m n) eqn:EQB;
        try apply nat_eqb_eq in EQB as EQ;
        try destruct EQ.

all : try apply (oneloop1 _ _ (or_introl FLa) (IHP1 P1SV) (IHP2 P2SV));
      try apply (oneloop2 _ _ (or_introl FLa) Cc (IHP1 P1SV) (IHP2 P2SV)); (*finished loops*)
      try apply (multloop1 _ _ _ (IHP1 P1SV) (IHP2 P2SV));
      try apply (multloop2 _ _ (or_intror Cc) (IHP1 P1SV) (IHP2 P2SV)); (*closed multi loops*)
      try refine (multloop1 _ _ _ (IHP1 P1SV) (IHP2 P2SV));
      try refine (multloop2 _ _ (or_introl (conj _ _)) (IHP1 P1SV) (IHP2 P2SV)); (*open multi loops*)
      try rewrite FLa;
      try split;
      try discriminate; (*are open*)
      try intros FAL;
      try inversion FAL as [EQ'];
      try destruct EQ';
      try rewrite nat_eqb_refl in EQB;
      try inversion EQB. (*are multi loops*)
Qed.

Lemma theorem_provable' :
    forall (P : ptree),
        valid P ->
            PA_cyclic_theorem (ptree_formula P) (ptree_deg P) (ptree_ord P).
Proof.
intros P PV.
induction P.

1 : destruct PV as [[LT PSV] AX]. (*deg up*)
2 : destruct PV as [[[LT PSV] NO] AX]. (*ord up*)
3 : destruct PV as [_ AX]. (*node*)
4-9,13-16 :  destruct PV as [[[[PF PSV] PD] PO] AX]. (*single hyp*)
14 :  destruct PV as [[[[[PF CPF] PSV] PD] PO] AX]; (*weakening*)
      pose proof (pre_theorem_structural _ PSV) as P'.
15-21 : destruct PV as [[[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O] AX]; (*double hyp*)
        rewrite P1F,<-P1D,<-P1O in IHP1;
        rewrite P2F,<-P2D,<-P2O in IHP2;
        try pose proof (projT1 (projT2 (true_theorem (IHP1 (P1SV, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_introl INB)))))))) as P1';
        try pose proof (projT1 (projT2 (true_theorem (IHP2 (P2SV, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_intror INB)))))))) as P2';
        try pose proof (projT2 (projT2 (true_theorem (IHP1 (P1SV, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_introl INB)))))))) as AX1';
        try pose proof (projT2 (projT2 (true_theorem (IHP2 (P2SV, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_intror INB)))))))) as AX2';
        try fold node_extract in *.

1-14 :  try rewrite PF,<-PD,<-PO in IHP;
        try pose proof (projT1 (projT2 (true_theorem (IHP (PSV, AX))))) as P';
        try pose proof (projT2 (projT2 (true_theorem (IHP (PSV, AX))))) as AX'.
  
1 : apply (prune (deg_incr _ _ P' LT) AX').
1 : apply (prune (ord_incr _ _ P' LT NO) AX').
1 : apply (prune (axiom _) AX).
1 : apply (prune (exchange1 P') AX').
1 : apply (prune (exchange2 P') AX').
1 : apply (prune (exchange3 P') AX').
1 : apply (prune (exchange4 P') AX').
1 : apply (prune (contraction1 P') AX').
1 : apply (prune (contraction2 _ P') AX').
1 : apply (prune (negation1 P') AX').
1 : apply (prune (negation2 P') AX').
1 : apply (prune (quantification1 P') AX').
1 : apply (prune (quantification2 P') AX').
1 : rewrite <-PF, PD, PO. 
    apply (prune (weakening _ CPF P') AX).

1 : refine (prune (demorgan1 P1' P2') _).
2 : refine (prune (demorgan2 P1' P2') _).
5 : refine (prune (cut1 _ _ P1' P2') _).
6 : refine (prune (cut2 _ _ P1' P2') _).
7 : refine (prune (cut3 _ _ _ P1' P2') _).

1,2,5-7 : intros B INB;
          apply in_app_iff in INB as [INB1 | INB2];
          try apply (AX1' _ INB1);
          apply (AX2' _ INB2).

all : pose proof (pre_theorem_structural P1 P1SV) as P1';
      pose proof (pre_theorem_structural P2 P2SV) as P2';
      rewrite P1F, <-P1D, <-P1O in P1';
      rewrite P2F, <-P2D, <-P2O in P2'.

2 : refine (prune (oneloop2 _ _ _ _ P1' P2') _).

1 : refine (prune (oneloop1 _ _ _ P1' P2') _).

all : unfold node_extract in AX; fold node_extract in AX.

3-5 : case (closed c) eqn:CC.

all : case (closed (univ n a)) eqn:CuA;
      try apply closed_univ_list in CuA as [CA | FLn];
      try apply (or_intror CA);
      try apply (or_introl FLn);
      try pose proof (AX _ (or_introl eq_refl)) as FAL;
      try inversion FAL;
      try apply AX;
      try reflexivity.
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
            node_extract P <> [].
Proof.
induction P;
unfold node_extract;
fold node_extract.

all : try apply IHP.

1 : discriminate.

all : intros FAL;
      try case (closed c) eqn:CC;
      try case (closed (univ n a)) eqn:CuA;
      try inversion FAL;
      try apply app_eq_nil in FAL as [FAL1 FAL2];
      try apply (IHP1 FAL1);
      try apply (IHP1 FAL2);
      try apply (IHP2 FAL2).
Qed.

Lemma struct_node_sum_less_l {L : list formula} {P : ptree} :
    length L < length (L ++ (node_extract P)).
Proof.
rewrite app_length.
case (node_extract P) eqn:L2.
- destruct (struct_non_empty_nodes _ L2).
- unfold length;
  fold (@length formula).
  lia.
Qed.

Lemma struct_node_sum_less_r {L : list formula} {P : ptree} :
    length L < length ((node_extract P) ++ L).
Proof.
rewrite app_length.
case (node_extract P) eqn:L1.
- destruct (struct_non_empty_nodes _ L1).
- unfold length;
  fold (@length formula).
  lia.
Qed.


(*

Master destruct tactic.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].


*)