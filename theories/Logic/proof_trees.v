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

| loop_a : forall (a : formula) (n d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| loop_ca : forall (c a : formula) (n d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| loop_ad : forall (a d : formula) (n d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| loop_cad : forall (c a d : formula) (n d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

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

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => (univ n A)

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => lor C (univ n A)

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2 => lor (univ n A) D

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2 => lor (lor C (univ n A)) D

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

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

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

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2 => ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2 => ord_add (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)) alpha1

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
    match free_list A with
    | [] => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
    | hd :: [] =>
        match nat_eqb hd n with
        | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        end
    | _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
    end

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => 
    match closed C with
        | true =>
            match free_list A with
            | [] => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            | hd :: [] =>
                match nat_eqb hd n with
                | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                end
            | _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            end
        | false => (univ n A) ::  (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        end

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2 =>
    match closed D with
        | true =>
            match free_list A with
            | [] => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            | hd :: [] =>
                match nat_eqb hd n with
                | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                end
            | _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            end
        | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
        end

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2 => 
    match closed C, closed D with
        | true, true =>
            match free_list A with
            | [] => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            | hd :: [] =>
                match nat_eqb hd n with
                | true => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                | false => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
                end
            | _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
            end
        | _, _ => (univ n A) :: (remove form_eq_dec A (node_extract P2)) ++ node_extract P1
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
    (ptree_formula P1 = substitution A n zero) * (ptree_formula P2 = substitution A n (succ (var n))) *
    (struct_valid P1) * (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (struct_valid P2) * (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor C (substitution A n zero)) * (ptree_formula P2 = (substitution A n (succ (var n)))) *
    (struct_valid P1) * (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (struct_valid P2) * (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = (substitution A n zero)) * (ptree_formula P2 = lor (substitution A n (succ (var n))) D) *
    (struct_valid P1) * (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (struct_valid P2) * (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor C (substitution A n zero)) * (ptree_formula P2 = lor (substitution A n (succ (var n))) D) *
    (struct_valid P1) * (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (struct_valid P2) * (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)

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
  destruct LSTC as [LSTn | LSTn];
  rewrite LSTn;
  try rewrite nat_eqb_refl;
  reflexivity.
- exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N, CC.
  destruct LSTC as [LSTn | LSTn];
  rewrite LSTn;
  try rewrite nat_eqb_refl;
  reflexivity.
- exists (loop_ad A D n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N, CD.
  destruct LSTC as [LSTn | LSTn];
  rewrite LSTn;
  try rewrite nat_eqb_refl;
  reflexivity.
- exists (loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N, CD, CC.
  destruct LSTC as [LSTn | LSTn];
  rewrite LSTn;
  try rewrite nat_eqb_refl;
  reflexivity.
- exists (loop_a A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N.
  destruct LSTN as [LSTn LSTe].
  destruct (free_list A) as [| m FLA].
  + contradict LSTe.
    reflexivity.
  + destruct FLA.
    * case (nat_eqb m n) eqn:EQ.
      --  apply nat_eqb_eq in EQ.
          destruct EQ.
          contradict LSTn.
          reflexivity.
      -- reflexivity.
    *  reflexivity.
- exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N.
  destruct LSTN as [[LSTn LSTe] | CC].
  destruct (free_list A) as [| m FLA].
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
    * case (closed C);
      reflexivity.
  + rewrite CC.
    reflexivity.
- exists (loop_ad A D n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N.
  destruct LSTN as [[LSTn LSTe] | CD].
  destruct (free_list A) as [| m FLA].
  + contradict LSTe.
    reflexivity.
  + destruct FLA.
    * case (nat_eqb m n) eqn:EQ.
      --  apply nat_eqb_eq in EQ.
          destruct EQ.
          contradict LSTn.
          reflexivity.
      --  case (closed D);
          reflexivity.
    * case (closed D);
      reflexivity.
  + rewrite CD.
    reflexivity.
- exists (loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  rewrite P2N, P1N.
  destruct LSTN as [[LSTn LSTe] | CDC].
  destruct (free_list A) as [| m FLA].
  + contradict LSTe.
    reflexivity.
  + destruct FLA.
    * case (nat_eqb m n) eqn:EQ.
      --  apply nat_eqb_eq in EQ.
          destruct EQ.
          contradict LSTn.
          reflexivity.
      --  case (closed C);
          case (closed D);
          reflexivity.
    * case (closed C);
      case (closed D);
      reflexivity.
  + destruct CDC as [CC | CD].
    * rewrite CC.
      reflexivity.
    * rewrite CD.
      case (closed C);
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
  + auto.
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
  + lia.
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
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_a A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  intros B INB.
  rewrite P2L, P1L in INB.
  destruct LSTC as [LSTn | LSTn];
  rewrite LSTn in INB;
  try rewrite nat_eqb_refl in INB;
  apply TAX, INB.
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  intros B INB.
  rewrite P2L, P1L, CC in INB.
  destruct LSTC as [LSTn | LSTn];
  rewrite LSTn in INB;
  try rewrite nat_eqb_refl in INB;
  apply TAX, INB.
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_ad A D n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  intros B INB.
  rewrite P2L, P1L, CD in INB.
  destruct LSTC as [LSTn | LSTn];
  rewrite LSTn in INB;
  try rewrite nat_eqb_refl in INB;
  apply TAX, INB.
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  intros B INB.
  rewrite P2L, P1L, CC, CD in INB.
  destruct LSTC as [LSTn | LSTn];
  rewrite LSTn in INB;
  try rewrite nat_eqb_refl in INB;
  apply TAX, INB.
- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.
- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.
- pose proof (TAX _ (or_introl eq_refl)) as FAL.
  inversion FAL.
- pose proof (TAX _ (or_introl eq_refl)) as FAL.
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
15,16,21-23 : destruct PSV as [[[[[[[PF1 PSV1] PF2] PSV2] PD1] PD2] PO1] PO2]; (*double hyp*)
              rewrite PF1,<-PD1,<-PO1 in IHP1;
              rewrite PF2,<-PD2,<-PO2 in IHP2;
              pose proof (IHP1 PSV1) as P1';
              pose proof (IHP2 PSV2) as P2'.
20-23 : destruct PSV as [[[[[[[P1F P2F] P1SV] P1D] P1O] P2SV] P2D] P2O]. (*loop*)

1-14 :  try rewrite PF,<-PD,<-PO in IHP;
        try pose proof (IHP PSV) as P'.

20-23 : rewrite P1F,<-P1D,<-P1O in IHP1;
        rewrite P2F,<-P2D,<-P2O in IHP2.
      
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
1 : apply (cut1 _ _ P1' P2').
1 : apply (cut2 _ _ P1' P2').
1 : apply (cut3 _ _ _ P1' P2').

all : unfold node_extract;
      fold node_extract;
      try case (closed c) eqn:Cc;
      try case (closed d) eqn:Cd;
      destruct (free_list a) as [| m L] eqn:FLa;
      try apply (oneloop1 _ _ (or_intror FLa) (IHP1 P1SV) (IHP2 P2SV));
      try apply (oneloop2 _ _ (or_intror FLa) Cc (IHP1 P1SV) (IHP2 P2SV));
      try apply (oneloop3 _ _ (or_intror FLa) Cd (IHP1 P1SV) (IHP2 P2SV));
      try apply (oneloop4 _ _ (or_intror FLa) Cc Cd (IHP1 P1SV) (IHP2 P2SV)).

1,2,5,8 : destruct L;
          case (nat_eqb m n) eqn:EQB;
          try apply nat_eqb_eq in EQB as EQ;
          try destruct EQ.

all : try apply (oneloop1 _ _ (or_introl FLa) (IHP1 P1SV) (IHP2 P2SV));
      try apply (oneloop2 _ _ (or_introl FLa) Cc (IHP1 P1SV) (IHP2 P2SV));
      try apply (oneloop3 _ _ (or_introl FLa) Cd (IHP1 P1SV) (IHP2 P2SV));
      try apply (oneloop4 _ _ (or_introl FLa) Cc Cd (IHP1 P1SV) (IHP2 P2SV)); (*finished loops*)
      try apply (multloop1 _ _ _ (IHP1 P1SV) (IHP2 P2SV));
      try apply (multloop2 _ _ (or_intror Cc) (IHP1 P1SV) (IHP2 P2SV));
      try apply (multloop3 _ _ (or_intror Cd) (IHP1 P1SV) (IHP2 P2SV));
      try apply (multloop4 _ _ (or_intror (or_intror Cd)) (IHP1 P1SV) (IHP2 P2SV));
      try apply (multloop4 _ _ (or_intror (or_introl Cc)) (IHP1 P1SV) (IHP2 P2SV)); (*closed multi loops*)
      try refine (multloop1 _ _ _ (IHP1 P1SV) (IHP2 P2SV));
      try refine (multloop2 _ _ (or_introl (conj _ _)) (IHP1 P1SV) (IHP2 P2SV));
      try refine (multloop3 _ _ (or_introl (conj _ _)) (IHP1 P1SV) (IHP2 P2SV));
      try refine (multloop4 _ _ (or_introl (conj _ _)) (IHP1 P1SV) (IHP2 P2SV)); (*open multi loops*)
      try rewrite FLa;
      try split;
      try discriminate; (*are open*)
      intros FAL;
      inversion FAL as [EQ'];
      destruct EQ';
      try rewrite nat_eqb_refl in EQB;
      try inversion EQB. (*are multi loops*)
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
14 :  destruct PV as [[[[[PF CPF] PSV] PD] PO] AX]; (*weakening*)
      pose proof (pre_theorem_structural _ PSV) as P'.
15,16,21-23 : destruct PV as [[[[[[[[PF1 PSV1] PF2] PSV2] PD1] PD2] PO1] PO2] AX]; (*double hyp*)
              rewrite PF1,<-PD1,<-PO1 in IHP1;
              rewrite PF2,<-PD2,<-PO2 in IHP2;
              pose proof (projT1 (projT2 (true_theorem (IHP1 (PSV1, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_introl INB)))))))) as P1';
              pose proof (projT1 (projT2 (true_theorem (IHP2 (PSV2, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_intror INB)))))))) as P2';
              pose proof (projT2 (projT2 (true_theorem (IHP1 (PSV1, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_introl INB)))))))) as AX1';
              pose proof (projT2 (projT2 (true_theorem (IHP2 (PSV2, (fun B INB => AX B (proj2 (in_app_iff _ _ _) (or_intror INB)))))))) as AX2';
              fold node_extract in *.
20-23 : destruct PV as [[[[[[[[P1F P2F] P1SV] P1D] P1O] P2SV] P2D] P2O] AX]. (*loop*)

1-14 :  try rewrite PF,<-PD,<-PO in IHP;
        try pose proof (projT1 (projT2 (true_theorem (IHP (PSV, AX))))) as P';
        try pose proof (projT2 (projT2 (true_theorem (IHP (PSV, AX))))) as AX'.

20-23 : rewrite P1F,<-P1D,<-P1O in IHP1;
        rewrite P2F,<-P2D,<-P2O in IHP2.
  
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
3 : refine (prune (cut1 _ _ P1' P2') _).
4 : refine (prune (cut2 _ _ P1' P2') _).
5 : refine (prune (cut3 _ _ _ P1' P2') _).

1-5 : intros B INB;
      apply in_app_iff in INB as [INB1 | INB2];
      try apply (AX1' _ INB1);
      apply (AX2' _ INB2).

all : pose proof (pre_theorem_structural P1 P1SV) as P1';
      pose proof (pre_theorem_structural P2 P2SV) as P2';
      rewrite P1F, <-P1D, <-P1O in P1';
      rewrite P2F, <-P2D, <-P2O in P2'.

4 : refine (prune (oneloop4 _ _ _ _ _ P1' P2') _).

3 : refine (prune (oneloop3 _ _ _ _ P1' P2') _).

2 : refine (prune (oneloop2 _ _ _ _ P1' P2') _).

1 : refine (prune (oneloop1 _ _ _ P1' P2') _).

all : unfold node_extract in AX; fold node_extract in AX.

1,2,3,5,6,8,9,12 : destruct (free_list a) as [| m L].

1,5,9,13 : right; reflexivity.

all : try destruct L;
      try case (nat_eqb m n) eqn:EQB; (*relevant cases for all*)
      try apply nat_eqb_eq in EQB;
      try destruct EQB;
      repeat rewrite app_nil_l in AX;
      try left;
      try reflexivity; (*shows list equalities hold*)
      try case (closed c) eqn:Cc;
      try case (closed d) eqn:Cd;
      try reflexivity; (*shows closures hold*) 
      try apply AX;
      pose proof (AX _ (or_introl eq_refl)) as FAL;
      unfold PA_cyclic_axiom in FAL;
      inversion FAL. (*everything else is contradictory*)
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

Require Import Coq.Arith.Wf_nat.


Lemma pre_LEM :
    forall {A : formula},
            {P : ptree & prod (ptree_formula P = (lor (neg A) A)) (struct_valid P)}.
Proof.
induction A as [A IND] using (induction_ltof1 _ num_conn);
unfold ltof in IND.
destruct A.
- destruct (structural_pre_theorem (pre_LEM_atomic a)) as [P [[[[PF PSV] PD] PO] PL]].
  apply (existT _ P (PF, PSV)).
- destruct (IND _ (le_n _)) as [P [PF PSV]].
  exists (negation_ad A (neg A) (ptree_deg P) (ptree_ord P) (exchange_ab (neg A) A (ptree_deg P) (ptree_ord P) P)).
  repeat split.
  + apply PF.
  + apply PSV.
- assert (num_conn A1 < num_conn (lor A1 A2)) as IE1. {unfold num_conn. lia. }
  assert (num_conn A2 < num_conn (lor A1 A2)) as IE2. {unfold num_conn. lia. }
  destruct (IND _ IE1) as [P1 [P1F P1SV]].
  destruct (IND _ IE2) as [P2 [P2F P2SV]].
  exists (demorgan_abd A1 A2 (lor A1 A2) (ptree_deg P1) (ptree_deg P2) (ptree_ord P1) (ord_succ (ptree_ord P2)) P1 (weakening_ad A1 A2 (ptree_deg P2) (ptree_ord P2) P2)).
  repeat split; simpl.

Qed.