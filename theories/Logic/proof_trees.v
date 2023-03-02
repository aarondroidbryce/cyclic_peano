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
| deg_up : nat -> ptree -> ptree

| ord_up : ord -> ptree -> ptree

| node : formula -> ptree

| exchange_ab : formula -> formula -> nat -> ord -> ptree -> ptree

| exchange_cab : formula -> formula -> formula -> nat -> ord -> ptree -> ptree

| exchange_abd : formula -> formula -> formula -> nat -> ord -> ptree -> ptree

| exchange_cabd :
    formula -> formula -> formula -> formula -> nat -> ord -> ptree -> ptree

| contraction_a : formula -> nat -> ord -> ptree -> ptree

| contraction_ad : formula -> formula -> nat -> ord -> ptree -> ptree

| weakening_ad : formula -> formula -> nat -> ord -> ptree -> ptree

| demorgan_ab :
    formula -> formula ->  nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree

| demorgan_abd :
    formula -> formula -> formula -> nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree

| negation_a : formula -> nat -> ord -> ptree -> ptree

| negation_ad : formula -> formula -> nat -> ord -> ptree -> ptree

| quantification_a : formula -> nat -> c_term -> nat -> ord -> ptree -> ptree

| quantification_ad :
    formula -> formula -> nat -> c_term -> nat -> ord -> ptree -> ptree

| loop_a : formula -> nat -> nat -> ord -> ptree -> ptree

| loop_ad :
    formula -> formula -> nat -> nat -> ord -> ptree -> ptree

| cut_ca :
    formula -> formula ->  nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree

| cut_ad :
    formula -> formula ->  nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree

| cut_cad :
    formula -> formula -> formula -> nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree.

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

| loop_a A n d alpha g => univ n A

| loop_ad A D n d alpha g => lor (univ n A) D

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

| loop_a A n d alpha g => d

| loop_ad A D n d alpha g => d

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

| loop_a A n d alpha g => (ord_mult alpha (wcon (wcon Zero 0 Zero) 0 Zero))

| loop_ad A D n d alpha g => (ord_mult alpha (wcon (wcon Zero 0 Zero) 0 Zero))

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

| loop_a A n d alpha P' => match in_dec form_eq_dec A (node_extract P'), count_occ form_eq_dec (node_extract P') A with
    | left _, 0 => node_extract P'
    | left _, (S m) => match free_list A with
        | [] => (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
        | hd :: [] => match nat_eqb hd n with
            | true => (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
            | false => (univ n A) :: (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
            end
        | _ => (univ n A) :: (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
        end
    | right _, _ => node_extract P'
    end

| loop_ad A D n d alpha P' => match in_dec form_eq_dec A (node_extract P'), count_occ form_eq_dec (node_extract P') A with
    | left _, 0 => node_extract P'
    | left _, (S m) => match free_list A with
        | [] => (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
        | hd :: [] => match nat_eqb hd n with
            | true => (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
            | false => (univ n A) :: (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
            end
        | _ => (univ n A) :: (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
        end
    | right _, _ => node_extract P'
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
    (ptree_formula P' = D) * (closed A = true) * (struct_valid P') *
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

| loop_a A n d alpha P' =>
    (ptree_formula P' = substitution A n (succ (var n))) * (count_occ form_eq_dec (node_extract P') A = 1) *
    (struct_valid P') * (d >= ptree_deg P') * (alpha = ptree_ord P')

| loop_ad A D n d alpha P' =>
    (ptree_formula P' = lor (substitution A n (succ (var n))) D) * (count_occ form_eq_dec (node_extract P') A = 1) *
    (struct_valid P') * (d >= ptree_deg P') * (alpha = ptree_ord P')

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
  (d >= ptree_deg P) * (alpha = ptree_ord P).

Definition provable (A : formula) (d : nat) (alpha : ord) : Type :=
  {P : ptree & P_proves P A d alpha}.

Lemma structural_pre_theorem :
    forall {A : formula} {d : nat} {alpha : ord} {L : list formula} (ST : PA_cyclic_pre A d alpha L), {P : ptree & prod (prod( prod (prod (ptree_formula P = A) (struct_valid P)) (d >= ptree_deg P)) (alpha = ptree_ord P)) (node_extract P = L) }.
intros A d alpha L TS.
induction TS;
try destruct IHTS as [P [[[[PF PSV] PD] PO] PN]];
try destruct IHTS1 as [P1 [[[[P1F P1SV] P1D] P1H] P1N]];
try destruct IHTS2 as [P2 [[[[P2F P2SV] P2D] P2H] P2N]].
- exists (deg_up d' P). repeat split; auto. lia.
- exists (ord_up beta P). repeat split; auto. rewrite <- PO. auto.
- exists (node A). repeat split. simpl. lia.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (weakening_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. lia. rewrite P1N,P2N. reflexivity.
- exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. lia. rewrite P1N,P2N. reflexivity.
- exists (negation_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (negation_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_a A n c (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n c (ptree_deg P) alpha P). repeat split; auto.
- exists (loop_a A n d alpha P).
  repeat split; simpl; auto.
  + rewrite PN.
    apply OCC1.
  + rewrite PN, OCC1, app_nil_l.
    case in_dec as [ _ | NIN].
    * destruct LSTC as [LSTn | LSTn];
      rewrite LSTn;
      try rewrite nat_eqb_refl;
      reflexivity.
    * rewrite (notin_remove _ _ _ NIN).
      reflexivity.
- exists (loop_ad A D n d alpha P).
  repeat split; simpl; auto.
  + rewrite PN.
    apply OCC1.
  + rewrite PN, OCC1, app_nil_l.
    case in_dec as [ _ | NIN].
    * destruct LSTC as [LSTn | LSTn];
      rewrite LSTn;
      try rewrite nat_eqb_refl;
      reflexivity.
    * rewrite (notin_remove _ _ _ NIN).
      reflexivity.
- exists (loop_a A n d alpha P).
  repeat split; simpl; auto.
  + rewrite PN.
    apply OCC1.
  + rewrite PN, OCC1, app_nil_l.
    case in_dec as [ IN | NIN].
    * destruct LSTN as [LSTn LSTe].
      destruct (free_list A) as [| m FLA].
      --  contradict LSTe.
          reflexivity.
      --  destruct FLA.
          ++  case (nat_eqb m n) eqn:EQ.
              **  apply nat_eqb_eq in EQ.
                  destruct EQ.
                  contradict LSTn.
                  reflexivity.
              ** reflexivity.
          ++  reflexivity.
    * rewrite ((proj1 (count_occ_not_In form_eq_dec _ _) NIN)) in OCC1.
      discriminate.
- exists (loop_ad A D n d alpha P).
  repeat split; simpl; auto.
  + rewrite PN.
    apply OCC1.
  + rewrite PN, OCC1, app_nil_l.
    case in_dec as [ IN | NIN].
    * destruct LSTN as [LSTn LSTe].
      destruct (free_list A) as [| m FLA].
      --  contradict LSTe.
          reflexivity.
      --  destruct FLA.
          ++  case (nat_eqb m n) eqn:EQ.
              **  apply nat_eqb_eq in EQ.
                  destruct EQ.
                  contradict LSTn.
                  reflexivity.
              ** reflexivity.
          ++  reflexivity.
    * rewrite ((proj1 (count_occ_not_In form_eq_dec _ _) NIN)) in OCC1.
      discriminate.
- exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. lia. rewrite P1N,P2N. reflexivity.
- exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. lia. rewrite P1N,P2N. reflexivity.
- exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. lia. rewrite P1N,P2N. reflexivity.
Qed.

Lemma provable_theorem : forall (A : formula) (d : nat) (alpha : ord),
  PA_cyclic_theorem A d alpha -> provable A d alpha.
Proof.
intros A d alpha T.
apply true_theorem in T. 
destruct T as [L [TS TAX]].
unfold provable.
induction TS;
try destruct (IHTS TAX) as [P [[[PF [PSV PAX]] PD] PO]];
try destruct (IHTS1 (fun B INB => TAX B (proj2 (in_app_iff _ _ _) (or_introl INB)))) as [P1 [[[P1F [P1SV P1AX]] P1D] P1H]];
try destruct (IHTS2 (fun B INB => TAX B (proj2 (in_app_iff _ _ _) (or_intror INB)))) as [P2 [[[P2F [P2SV P2AX]] P2D] P2H]].
- exists (deg_up d' P). repeat split; auto. lia.
- exists (ord_up beta P). repeat split; auto. rewrite <- PO. auto.
- exists (node A). repeat split. intros A' IN. inversion IN. destruct H. apply TAX, or_introl, eq_refl. inversion H. auto.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (weakening_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. intros A' IN. apply in_app_iff in IN as [IN1 | IN2]. apply P1AX, IN1. apply P2AX, IN2. lia.
- exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. intros A' IN. apply in_app_iff in IN as [IN1 | IN2]. apply P1AX, IN1. apply P2AX, IN2. lia.
- exists (negation_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (negation_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_a A n c (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n c (ptree_deg P) alpha P). repeat split; auto.
- pose proof (structural_pre_theorem TS) as [P [[[[PF PSV] PD] PO] PL]].
  exists (loop_a A n d alpha P).
  repeat split; simpl; auto.
  + rewrite PL.
    apply OCC1.
  + intros B INB.
    case in_dec as [IN | NIN].
    * rewrite PL,OCC1 in INB.
      destruct LSTC as [LSTn | LSTn];
      rewrite LSTn in INB;
      try rewrite nat_eqb_refl in INB;
      apply TAX, INB.
    * rewrite PL in *.
      apply TAX.
      rewrite (notin_remove _ _ _ NIN).
      apply INB. 
- pose proof (structural_pre_theorem TS) as [P [[[[PF PSV] PD] PO] PL]].
  exists (loop_ad A D n d alpha P).
  repeat split; simpl; auto.
  + rewrite PL.
    apply OCC1.
  + intros B INB.
    case in_dec as [IN | NIN].
    * rewrite PL,OCC1 in INB.
      destruct LSTC as [LSTn | LSTn];
      rewrite LSTn in INB;
      try rewrite nat_eqb_refl in INB;
      apply TAX, INB.
    * rewrite PL in *.
      apply TAX.
      rewrite (notin_remove _ _ _ NIN).
      apply INB.
- pose proof (TAX (univ n A) (or_introl (eq_refl))) as FAL.
  inversion FAL.
- pose proof (TAX (univ n A) (or_introl (eq_refl))) as FAL.
  inversion FAL.
- exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. intros A' IN. apply in_app_iff in IN as [IN1 | IN2]. apply P1AX, IN1. apply P2AX, IN2. lia.
- exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. intros A' IN. apply in_app_iff in IN as [IN1 | IN2]. apply P1AX, IN1. apply P2AX, IN2. lia.
- exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. intros A' IN. apply in_app_iff in IN as [IN1 | IN2]. apply P1AX, IN1. apply P2AX, IN2. lia.
Qed.

Lemma theorem_provable' : forall (P : ptree),
  valid P -> PA_omega_theorem (ptree_formula P) (ptree_deg P) (ptree_ord P).
Proof.
intros P PV. induction P;
(try inversion PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1H] P2H]) ||
(try inversion PV as [[[PF PV'] PD] PH]); simpl;
try rewrite P1F in IHP1; try rewrite P2F in IHP2;
try rewrite P1D,P2D,P1H,P2H;
try rewrite PF in IHP; try rewrite PD,PH.

- inversion PV as [LT PV']. apply (deg_incr _ (ptree_deg P) _ _ (IHP PV') LT).
- inversion PV as [[LT PV'] N]. simpl. apply (ord_incr _ _ (ptree_ord P) _ (IHP PV') LT N). 
- inversion PV as [AX]. apply axiom. apply AX.
- apply exchange1. apply IHP. apply PV'.
- apply exchange2. apply IHP. apply PV'.
- apply exchange3. apply IHP. apply PV'.
- apply exchange4. apply IHP. apply PV'.
- apply contraction1. apply IHP. apply PV'.
- apply contraction2. apply IHP. apply PV'.
- destruct PF as [PF CF]. apply weakening.
  + apply CF.
  + rewrite <- PF. apply IHP. apply PV'.
- apply demorgan1.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
- apply demorgan2.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
- apply negation1. apply IHP. apply PV'.
- apply negation2. apply IHP. apply PV'.
- apply (quantification1 _ _ c). apply IHP. apply PV'.
- apply (quantification2 _ _ _ c). apply IHP. apply PV'.
- apply w_rule1. intros c.
  destruct (PV c) as [[[PF PV'] PD] PH].
  fold valid in PV'.
  rewrite <- PF. rewrite PH.
  apply (deg_monot _ _ _ _ PD).
  apply X. apply PV'.
- apply w_rule2. intros c.
  destruct (PV c) as [[[PF PV'] PD] PH].
  fold valid in PV'.
  rewrite <- PF. rewrite PH.
  apply (deg_monot _ _ _ _ PD).
  apply X. apply PV'.
- apply cut1.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
- apply cut2.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
- apply cut3.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
Qed.

Lemma theorem_provable : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> PA_omega_theorem A d alpha.
Proof.
intros A d alpha H. unfold provable in H. destruct H as [t [[[H1 H2] H3] H4]].
apply nat_ge_case_type in H3. destruct H3 as [H3 | H3].
- assert (valid (deg_up d t)). simpl. auto.
  assert (ptree_formula (deg_up d t) = A) as X1. auto.
  assert (ptree_ord (deg_up d t) = alpha) as X2. auto.
  assert (ptree_deg (deg_up d t) = d) as X3. auto.
  rewrite <- X1, <- X2, <- X3.
  apply theorem_provable'. auto.
- rewrite <- H1, H4. rewrite H3.
  apply theorem_provable'. auto.
Qed.

Lemma ptree_ord_nf : forall (P : ptree), valid P -> nf (ptree_ord P).
Proof.
intros.
pose proof (theorem_provable' _ X).
apply (ord_nf _ _ _ X0).
Qed.

Lemma ptree_ord_nf_hyp : forall (alpha : ord) (P : ptree), alpha = ptree_ord P -> valid P -> nf alpha.
Proof.
intros.
rewrite H.
apply ptree_ord_nf.
apply X.
Qed.
*)

Lemma associativity_1 : forall (C A B : formula) (d : nat) (alpha : ord),
  provable (lor (lor C A) B) d alpha -> provable (lor C (lor A B)) d alpha.
Proof.
unfold provable. intros C A B d alpha [P [[[PF [PSV PA]] PD] PO]].
exists (exchange_ab
          (lor A B) C (ptree_deg P) alpha
          (exchange_cab
              A C B (ptree_deg P) alpha
              (exchange_abd C A B (ptree_deg P) alpha P))).
repeat split; auto.
Qed.

Lemma associativity_2 : forall (C A B : formula) (d : nat) (alpha : ord),
  provable (lor C (lor A B)) d alpha -> provable (lor (lor C A) B) d alpha.
Proof.
unfold provable. intros C A B d alpha [P [[[PF [PSV PA]] PD] PO]].
exists (exchange_abd
            A C B (ptree_deg P) alpha
            (exchange_cab
                A B C (ptree_deg P) alpha
                (exchange_ab C (lor A B) (ptree_deg P) alpha P))).
repeat split; auto.
Qed.

(*
Lemma provable_closed : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> closed A = true.
Proof.
intros. apply (theorem_closed _ d alpha). apply theorem_provable. auto.
Qed.

Lemma provable_closed' : forall (P : ptree) (A : formula),
  valid P -> ptree_formula P = A -> closed A = true.
Proof.
intros. pose (ptree_deg P) as d. pose (ptree_ord P) as alpha.
apply (provable_closed _ d alpha). unfold provable. exists P.
unfold P_proves. repeat split; auto.
Qed.
*)