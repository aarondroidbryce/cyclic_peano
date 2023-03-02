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
    | left _, (S m) => match closed D with
        | true => match free_list A with
            | [] => (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
            | hd :: [] => match nat_eqb hd n with
                | true => (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
                | false => (univ n A) :: (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
                end
            | _ => (univ n A) :: (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
            end
        | false => (univ n A) :: (repeat A m) ++ (remove form_eq_dec A (node_extract P'))
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
    (struct_valid P') * (d = ptree_deg P') * (alpha = ptree_ord P')

| loop_ad A D n d alpha P' =>
    (ptree_formula P' = lor (substitution A n (succ (var n))) D) * (count_occ form_eq_dec (node_extract P') A = 1) *
    (struct_valid P') * (d = ptree_deg P') * (alpha = ptree_ord P')

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
- exists (weakening_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto.  rewrite P1N,P2N. reflexivity.
- exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
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
    * rewrite CD.
      destruct LSTC as [LSTn | LSTn];
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
    case in_dec as [IN | NIN].
    * destruct LSTN as [[LSTn LSTe] | CD].
      destruct (free_list A) as [| m FLA].
      --  contradict LSTe.
          reflexivity.
      --  destruct FLA.
          ++  case (nat_eqb m n) eqn:EQ.
              **  apply nat_eqb_eq in EQ.
                  destruct EQ.
                  contradict LSTn.
                  reflexivity.
              **  case (closed D);
                  reflexivity.
          ++  case (closed D);
              reflexivity.
      --  rewrite CD.
          reflexivity.
    * rewrite ((proj1 (count_occ_not_In form_eq_dec _ _) NIN)) in OCC1.
      discriminate.
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
  + auto.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (weakening_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
  + lia.
- exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
  + lia.
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
    * rewrite PL, OCC1, CD in INB.
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
- exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
  + lia.
- exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
  + lia.
- exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
  + lia.
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
15,16,19-21 : destruct PSV as [[[[[[[PF1 PSV1] PF2] PSV2] PD1] PD2] PO1] PO2]; (*double hyp*)
              rewrite PF1,<-PD1,<-PO1 in IHP1;
              rewrite PF2,<-PD2,<-PO2 in IHP2;
              pose proof (IHP1 PSV1) as P1';
              pose proof (IHP2 PSV2) as P2'.
20,21 : destruct PSV as [[[[PF OCC1] PSV] PD] PO]. (*loop*)

1-14 :  try rewrite PF,<-PD,<-PO in IHP;
        try pose proof (IHP PSV) as P'.

20,21 : try rewrite PF,<-PD,<-PO in IHP.
      
- apply (deg_incr _ _ P' LT).
- apply (ord_incr _ _ P' LT NO).
- apply (axiom _).
- apply (exchange1 P').
- apply (exchange2 P').
- apply (exchange3 P').
- apply (exchange4 P').
- apply (contraction1 P').
- apply (contraction2 _ P').
- apply (negation1 P').
- apply (negation2 P').
- apply (quantification1 P').
- apply (quantification2 P').
- apply (weakening _ CPF P').
- apply (demorgan1 P1' P2').
- apply (demorgan2 P1' P2').
- apply (cut1 _ _ P1' P2').
- apply (cut2 _ _ P1' P2').
- apply (cut3 _ _ _ P1' P2').

- unfold node_extract; fold node_extract.
  case in_dec as [IN | NIN].
  + rewrite OCC1.
    destruct (free_list f) as [| m L] eqn:FLf.
    * refine (oneloop1 _ OCC1 _ _).
      --  right.
          apply FLf.
      --  apply (IHP PSV).
    * destruct L.
      --  case (nat_eqb m n) eqn:EQ.
          ++  apply nat_eqb_eq in EQ.
              destruct EQ.
              refine (oneloop1 _ OCC1 _ _).
              **  left.
                  apply FLf.
              **  apply (IHP PSV).
          ++  refine (multloop1 _ OCC1 _ _).
              **  rewrite FLf. split.
                  { intros FAL.
                    inversion FAL as [EQ'].
                    destruct EQ'.
                    rewrite nat_eqb_refl in EQ.
                    inversion EQ. }
                  { discriminate. }
              **  apply (IHP PSV).
      --  refine (multloop1 _ OCC1 _ _).
          ++  rewrite FLf. split; discriminate.
          ++  apply (IHP PSV).
  + contradict NIN.
    rewrite count_occ_In.
    rewrite OCC1.
    lia.
- unfold node_extract; fold node_extract.
  case in_dec as [IN | NIN].
  + rewrite OCC1.
    case (closed f0) eqn:Cf.
    * destruct (free_list f) as [| m L] eqn:FLf.
      --  apply (oneloop2 _ OCC1 (or_intror FLf) Cf (IHP PSV)).
      --  destruct L.
          ++  case (nat_eqb m n) eqn:EQ.
              **  apply nat_eqb_eq in EQ.
                  destruct EQ.
                  apply (oneloop2 _ OCC1 (or_introl FLf) Cf (IHP PSV)).
              **  refine (multloop2 _ OCC1 _ _).
                  { rewrite FLf. left. split.
                    { intros FAL.
                      inversion FAL as [EQ'].
                      destruct EQ'.
                      rewrite nat_eqb_refl in EQ.
                      inversion EQ. }
                    { discriminate. } }
                  { apply (IHP PSV). }
          ++  refine (multloop2 _ OCC1 _ (IHP PSV)).
              rewrite FLf. left.
              split; discriminate.
    * refine (multloop2 _ OCC1 _ (IHP PSV)).
      right.
      apply Cf.
  + contradict NIN.
    rewrite count_occ_In.
    rewrite OCC1.
    lia.
Qed.

Lemma theorem_provable' :
    forall (P : ptree),
        valid P ->
            PA_cyclic_theorem (ptree_formula P) (ptree_deg P) (ptree_ord P).
Proof.
intros P PV. induction P.

1 : destruct PV as [[LT PSV] AX]. (*deg up*)
2 : destruct PV as [[[LT PSV] NO] AX]. (*ord up*)
3 : destruct PV as [_ AX]. (*node*)
4-9,13-16 :  destruct PV as [[[[PF PSV] PD] PO] AX]. (*single hyp*)
14 : destruct PV as [[[[[PF CPF] PSV] PD] PO] AX]. (*weakening*)
15,16,19-21 : destruct PV as [[[[[[[[PF1 PSV1] PF2] PSV2] PD1] PD2] PO1] PO2] AX]; (*double hyp*)
              rewrite PF1,<-PD1,<-PO1 in IHP1;
              rewrite PF2,<-PD2,<-PO2 in IHP2;
              pose proof (projT1 (projT2 (true_theorem (IHP1 (PSV1, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_introl INB)))))))) as P1';
              pose proof (projT1 (projT2 (true_theorem (IHP2 (PSV2, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_intror INB)))))))) as P2';
              pose proof (projT2 (projT2 (true_theorem (IHP1 (PSV1, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_introl INB)))))))) as AX1';
              pose proof (projT2 (projT2 (true_theorem (IHP2 (PSV2, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_intror INB)))))))) as AX2'.
20,21 : destruct PV as [[[[[PF OCC1] PSV] PD] PO] AX]. (*loop*)

1-14 :  try rewrite PF,<-PD,<-PO in IHP;
        try pose proof (projT1 (projT2 (true_theorem (IHP (PSV, AX))))) as P';
        try pose proof (projT2 (projT2 (true_theorem (IHP (PSV, AX))))) as AX'.

20,21 : try rewrite PF,<-PD,<-PO in IHP.
      
- apply (prune (deg_incr _ _ P' LT) AX').
- apply (prune (ord_incr _ _ P' LT NO) AX').
- apply (prune (axiom _) AX).
- apply (prune (exchange1 P') AX').
- apply (prune (exchange2 P') AX').
- apply (prune (exchange3 P') AX').
- apply (prune (exchange4 P') AX').
- apply (prune (contraction1 P') AX').
- apply (prune (contraction2 _ P') AX').
- apply (prune (negation1 P') AX').
- apply (prune (negation2 P') AX').
- apply (prune (quantification1 P') AX').
- apply (prune (quantification2 P') AX').
- apply (prune (weakening _ CPF P') AX').

- refine (prune (demorgan1 P1' P2') _).
  intros B INB.
  apply in_app_iff in INB as [INB1 | INB2].
  + apply (AX1' _ INB1).
  + apply (AX2' _ INB2).
- refine (prune (demorgan2 P1' P2') _).
  intros B INB.
  apply in_app_iff in INB as [INB1 | INB2].
  + apply (AX1' _ INB1).
  + apply (AX2' _ INB2).
- refine (prune (cut1 _ _ P1' P2') _).
  intros B INB.
  apply in_app_iff in INB as [INB1 | INB2].
  + apply (AX1' _ INB1).
  + apply (AX2' _ INB2).
- refine (prune (cut2 _ _ P1' P2') _).
  intros B INB.
  apply in_app_iff in INB as [INB1 | INB2].
  + apply (AX1' _ INB1).
  + apply (AX2' _ INB2).
- refine (prune (cut3 _ _ _ P1' P2') _).
  intros B INB.
  apply in_app_iff in INB as [INB1 | INB2].
  + apply (AX1' _ INB1).
  + apply (AX2' _ INB2).

- refine (prune (oneloop1 _ OCC1 _ _ ) _).
  + unfold node_extract in AX; fold node_extract in AX.
    case in_dec as [IN | NIN].
    * rewrite OCC1 in AX.
      destruct (free_list f) as [| m L].
      --  right.
          reflexivity.
      --  destruct L.
          ++  case (nat_eqb m n) eqn:EQ.
              **  apply nat_eqb_eq in EQ.
                  destruct EQ.
                  left.
                  reflexivity.
              **  pose proof (AX (univ n f) (or_introl eq_refl)) as FAL.
                  unfold PA_cyclic_axiom in FAL.
                  inversion FAL.
          ++  pose proof (AX (univ n f) (or_introl eq_refl)) as FAL.
              unfold PA_cyclic_axiom in FAL.
              inversion FAL.
    * contradict NIN.
      rewrite count_occ_In.
      rewrite OCC1.
      lia.
  + rewrite <- PF, PD, PO.
    apply (pre_theorem_structural P PSV).
  + unfold node_extract in AX; fold node_extract in AX.
    case in_dec as [IN | NIN].
    * rewrite OCC1 in AX.
      destruct (free_list f) as [| m L].
      --  rewrite app_nil_l in AX.
          apply AX.
      --  destruct L.
          ++  case (nat_eqb m n) eqn:EQ.
              **  apply nat_eqb_eq in EQ.
                  destruct EQ.
                  rewrite app_nil_l in AX.
                  apply AX.
              **  pose proof (AX (univ n f) (or_introl eq_refl)) as FAL.
                  unfold PA_cyclic_axiom in FAL.
                  inversion FAL.
          ++  pose proof (AX (univ n f) (or_introl eq_refl)) as FAL.
              unfold PA_cyclic_axiom in FAL.
              inversion FAL.
    * intros B INB.
      apply (AX _ (proj1 (in_remove _ _ _ _ INB))).
- refine (prune (oneloop2 _ OCC1 _ _ _) _).
  + unfold node_extract in AX; fold node_extract in AX.
    case in_dec as [IN | NIN].
    * rewrite OCC1 in AX.
      destruct (free_list f) as [| m L].
      --  right.
          reflexivity.
      --  destruct L.
          ++  case (nat_eqb m n) eqn:EQ.
              **  apply nat_eqb_eq in EQ.
                  destruct EQ.
                  left.
                  reflexivity.
              **  case (closed f0) eqn:CF0;
                  pose proof (AX (univ n f) (or_introl eq_refl)) as FAL;
                  unfold PA_cyclic_axiom in FAL;
                  inversion FAL.
          ++  case (closed f0) eqn:CF0;
              pose proof (AX (univ n f) (or_introl eq_refl)) as FAL;
              unfold PA_cyclic_axiom in FAL;
              inversion FAL.
    * contradict NIN.
      rewrite count_occ_In.
      rewrite OCC1.
      lia.
  + unfold node_extract in AX; fold node_extract in AX.
    rewrite OCC1 in AX.
    case (closed f0) eqn:Cf0. reflexivity.
    case (in_dec form_eq_dec f (node_extract P)) as [_ | NIN].
    * pose proof (AX (univ n f) (or_introl eq_refl)) as FAL;
      unfold PA_cyclic_axiom in FAL;
      inversion FAL.
    * contradict NIN.
      rewrite count_occ_In.
      rewrite OCC1.
      lia.
  + rewrite <- PF, PD, PO.
    apply (pre_theorem_structural P PSV).
  + unfold node_extract in AX; fold node_extract in AX.
    case in_dec as [IN | NIN].
    * rewrite OCC1 in AX.
      destruct (free_list f) as [| m L].
      --  rewrite app_nil_l in AX.
          case (closed f0) eqn:CF0.
          ++  apply AX.
          ++  pose proof (AX (univ n f) (or_introl eq_refl)) as FAL.
              unfold PA_cyclic_axiom in FAL.
              inversion FAL.
      --  destruct L.
          ++  case (nat_eqb m n) eqn:EQ.
              **  apply nat_eqb_eq in EQ.
                  destruct EQ.
                  rewrite app_nil_l in AX.
                  case (closed f0) eqn:CF0.
                  { apply AX. }
                  { pose proof (AX (univ m f) (or_introl eq_refl)) as FAL.
                    unfold PA_cyclic_axiom in FAL.
                    inversion FAL. }
              **  case (closed f0) eqn:CF0;
                  pose proof (AX (univ n f) (or_introl eq_refl)) as FAL;
                  unfold PA_cyclic_axiom in FAL;
                  inversion FAL.
          ++  case (closed f0) eqn:CF0;
              pose proof (AX (univ n f) (or_introl eq_refl)) as FAL;
              unfold PA_cyclic_axiom in FAL;
              inversion FAL.
    * intros B INB.
      apply (AX _ (proj1 (in_remove _ _ _ _ INB))).
Qed.

Lemma theorem_provable :
    forall (A : formula) (d : nat) (alpha : ord),
        provable A d alpha ->
            PA_cyclic_theorem A d alpha.
Proof.
intros A d alpha [P [[[PF [PSV PAX]] PD] PO]].
apply nat_ge_case_type in PD as [PD | PD].
- rewrite <- PF, PO.
  assert (valid (deg_up d P)) as PDV. split; simpl; auto.
  apply (theorem_provable' _ PDV).
- rewrite <- PF, PD, PO.
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