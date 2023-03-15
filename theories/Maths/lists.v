Require Import Lia.
Require Import Nat.
Require Import List.
Require Import Classes.DecidableClass.

From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Logic Require Import definitions.

Require Import Coq.Arith.Wf_nat.

Open Scope bool_scope.
Open Scope list_scope.

Import ListNotations.

Notation nat_eq_dec := PeanoNat.Nat.eq_dec.

Lemma in_app_comm {A : Type} :
    forall (L1 L2 : list A) (a : A),
      In a (L1 ++ L2) <-> In a (L2 ++ L1).
Proof.
intros.
rewrite (in_app_iff L1).
rewrite (in_app_iff L2).
rewrite or_comm.
reflexivity.
Qed.

Lemma nin_split {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L1 L2 : list A) (a : A),
        ~ In a (L1 ++ L2) ->
            ~ In a L1 /\ ~ In a L2.
Proof.
intros L1 L2 a NIN.
case (in_dec DEC a L1) as [IN' | NIN'].
contradict NIN.
apply in_or_app, or_introl, IN'.
apply (conj NIN').
case (in_dec DEC a L2) as [IN'' | NIN''].
contradict NIN.
apply in_or_app, or_intror, IN''.
apply NIN''.
Qed.

Lemma nin_merge {A : Type} :
    forall (L1 L2 : list A) (a : A),
        ~ In a L1 /\ ~ In a L2 ->
            ~ In a (L1 ++ L2).
Proof.
intros L1 L2 a [NIN1 NIN2] IN.
apply in_app_or in IN as [IN1 | IN2].
apply (NIN1 IN1).
apply (NIN2 IN2).
Qed.

Lemma nin_ne_weaken {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L : list A) (a b : A),
        a <> b ->
            ~ In a (remove DEC b L) ->
                ~ In a L.
Proof.
intros L a b NE NIN IN.
apply NIN.
apply (in_in_remove _ _ NE IN).
Qed.

Lemma incl_head {A : Type} {L1 L2 : list A} {a : A} :
    incl L1 L2 -> incl (a :: L1)  (a:: L2).
Proof.
intros SUB b IN.
destruct IN as [EQ | IN].
- apply (or_introl EQ).
- apply (or_intror (SUB _ IN)).
Qed.

Lemma remove_not_head {A : Type} {DEC : forall (a b : A), {a = b} + {a <> b}} :
    forall (a b : A) (L : list A),
        a <> b ->
            remove DEC a (b :: L) = b :: (remove DEC a L).
Proof.
intros a b.
induction L;
intros NE;
unfold remove;
fold (remove DEC);
case DEC as [FAL | _].
- contradict NE.
  apply FAL.
- reflexivity.
- contradict NE.
  apply FAL.
- reflexivity.
Qed.

Lemma flat_map_remove_in {A B : Type} {DEC : forall (a b : A), {a = b} + {a <> b}} :
    forall (f : A -> list B) (a : A) (L : list A) (b : B),
        In b (flat_map f (remove DEC a L)) ->
            In b (flat_map f L).
Proof.
intros f a.
induction L;
intros b IN.
- apply IN.
- unfold remove in IN.
  fold (remove DEC) in IN.
  case DEC as [EQ | NE].
  + destruct EQ.
    apply in_app_iff, or_intror, IHL, IN.
  + apply in_app_iff in IN as [IN | IN].
    * apply in_app_iff, or_introl, IN.
    * apply in_app_iff, or_intror, IHL, IN.
Qed.

Lemma flat_map_remove_in_other {A B : Type} {DECA : forall (a b : A), {a = b} + {a <> b}}  {DECB : forall (a b : B), {a = b} + {a <> b}} :
    forall (f : A -> list B) (a : A) (L : list A) (b : B),
        In b (flat_map f (remove DECA a L)) ->
            (~ In b (f a)) + {c : A & In c (remove DECA a L) /\ In b (f c)}.
Proof.
intros f a.
induction L;
intros b IN.
- inversion IN.
- unfold remove in IN.
  fold (remove DECA) in IN.
  case DECA as [EQ | NE].
  + destruct EQ.
    destruct (IHL _ IN) as [NIN | Elem].
    * left.
      apply NIN.
    * right.
      rewrite remove_cons.
      apply Elem.
  + apply in_app_iff in IN.
    fold (flat_map f) in IN.
    case (in_dec DECB b (f a0)) as [IN' | NIN].
    * right.
      exists a0.
      rewrite (remove_not_head _ _ _ NE).
      exact (conj (or_introl eq_refl) IN').
    * assert (In b (flat_map f (remove DECA a L))) as IN''.
      { destruct IN as [IN | IN]. contradict IN. apply NIN. apply IN. }
      destruct (IHL _ IN'') as [NIN' | [c [INr INb]]].
      --  left.
          apply NIN'.
      --  right.
          rewrite (remove_not_head _ _ _ NE).
          exact (existT _ c (conj (or_intror INr) INb)).
Qed.

Lemma flat_map_not_in_remove {A B : Type} {DECA : forall (a b : A), {a = b} + {a <> b}}  {DECB : forall (a b : B), {a = b} + {a <> b}} :
    forall (f : A -> list B) (a : A) (L : list A) (b : B),
        In b (flat_map f L) ->
            (~ In b (f a)) ->
                In b (flat_map f (remove DECA a L)).
Proof.
intros f a.
induction L;
intros b IN NIN.
- inversion IN.
- unfold remove.
  fold (remove DECA).
  case DECA as [EQ | NE].
  + destruct EQ.
    apply in_app_iff in IN as [IN | IN].
    * contradict NIN.
      apply IN.
    * apply (IHL _ IN NIN).
  + apply in_app_iff in IN as [IN | IN].
    * apply in_app_iff, or_introl, IN.
    * apply in_app_iff, or_intror, (IHL _ IN NIN).
Qed.

Lemma flat_map_in_other_remove {A B : Type} {DECA : forall (a b : A), {a = b} + {a <> b}}  {DECB : forall (a b : B), {a = b} + {a <> b}} :
    forall (f : A -> list B) (a : A) (L : list A) (b : B),
        In b (flat_map f L) ->
            forall (c : A),
                In b (f c) ->
                    In c (remove DECA a L) ->
                        In b (flat_map f (remove DECA a L)).
Proof.
intros f a.
induction L;
intros b INb c INf INc.
- inversion INb.
- unfold remove in INc.
  fold (remove DECA) in INc.
  case DECA as [EQ | NE].
  + destruct EQ.
    rewrite remove_cons.
    apply in_flat_map.
    exists c.
    exact (conj INc INf).
  + rewrite (remove_not_head _ _ _ NE).
    apply in_app_iff in INb as [INb | INb].
    * apply in_app_iff, or_introl, INb.
    * destruct INc as [EQ | INc].
      --  destruct EQ.
          apply in_app_iff, or_introl, INf.
      --  apply in_app_iff, or_intror, (IHL _ INb _ INf INc).
Qed.

Fixpoint list_eqb (l1 l2 : list nat) : bool :=
match l1,l2 with
| [],[] => true
| m :: l1',[] => false
| [], n :: l2' => false
| m :: l1', n :: l2' => nat_eqb m n && list_eqb l1' l2'
end.

Lemma list_eqb_eq :
    forall (l1 l2 : list nat),
        list_eqb l1 l2 = true ->
            l1 = l2.
Proof.
induction l1;
intros l2 EQ.
- destruct l2.
  + reflexivity. 
  + inversion EQ.
- destruct l2.
  + inversion EQ.
  + unfold list_eqb in EQ; fold list_eqb in EQ.
    destruct (and_bool_prop _ _ EQ) as [EQ1 EQ2].
    rewrite (IHl1 l2 EQ2).
    rewrite (nat_eqb_eq _ _ EQ1).
    reflexivity.
Qed.

Lemma list_eqb_refl :
    forall (l : list nat),
        list_eqb l l = true.
Proof.
induction l.
- reflexivity.
- unfold list_eqb; fold list_eqb.
  rewrite nat_eqb_refl.
  apply IHl.
Qed.

Fixpoint member (n : nat) (l : list nat) : bool :=
match l with
| nil => false
| m :: l' => 
  (match nat_eqb m n with
  | true => true
  | false => member n l'
  end)
end.

Lemma member_in (n : nat) (l : list nat) : member n l = true <-> In n l.
Proof.
induction l;
split;
intros IN.
- inversion IN.
- inversion IN.
- unfold In; fold (@In nat).
  unfold member in IN;
  fold member in IN.
  case (nat_eqb a n) eqn:EQB.
  + apply nat_eqb_eq in EQB.
    left.
    apply EQB.
  + right.
    apply IHl, IN.
- unfold member;
  fold member.
  destruct IN as [EQ | IN].
  + destruct EQ.
    rewrite nat_eqb_refl.
    reflexivity.
  + case (nat_eqb a n).
    * reflexivity.
    * apply IHl, IN.
Qed.

Lemma not_member_nin (n : nat) (l : list nat) : member n l = false <-> ~In n l.
Proof.
destruct (in_dec nat_eq_dec n l) as [IN | NIN];
split;
intros NIN'.
- rewrite (proj2 (member_in _ _) IN) in NIN'.
  inversion NIN'.
- contradict (NIN' IN).
- apply NIN.
- case (member n l) eqn:IN.
  + contradict (NIN (proj1 (member_in _ _) IN)).
  + reflexivity.
Qed.

Lemma remove_dups_empty :
    forall (l : list nat),
        nodup nat_eq_dec l = [] -> l = [].
Proof.
intros l lE.
induction l.
- reflexivity.
- unfold nodup in lE.
  fold (nodup nat_eq_dec) in lE.
  case (in_dec nat_eq_dec a l) as [IN | NIN].
  + rewrite (IHl lE) in IN.
    inversion IN.
  + inversion lE.
Qed.

Lemma remove_dups_order :
    forall (l : list nat) (n : nat),
        remove nat_eq_dec n (nodup nat_eq_dec l) = nodup nat_eq_dec (remove nat_eq_dec n l).
Proof.
intros l n.
induction l.
- reflexivity.
- unfold nodup; fold (nodup nat_eq_dec);
  unfold remove; fold (remove nat_eq_dec).
  case (nat_eq_dec a n) as [EQ | NE];
  try destruct EQ;
  destruct nat_eq_dec as [EQ | NE'];
  unfold nodup; fold (nodup nat_eq_dec);
  unfold remove; fold (remove nat_eq_dec).
  + rewrite <- IHl.
    case (in_dec nat_eq_dec a l) as [IN | NIN].
    * reflexivity.
    * apply remove_cons.
  + contradict (NE' eq_refl).
  + contradict NE.
    destruct EQ.
    reflexivity.
  + rewrite <- IHl.
    case (in_dec nat_eq_dec a l) as [IN | NIN];
    case (in_dec nat_eq_dec a (remove nat_eq_dec n l)) as [IN' | NIN'].
    * reflexivity.
    * contradict (NIN' (in_in_remove nat_eq_dec _ NE IN)).
    * contradict (NIN (proj1 (in_remove nat_eq_dec _ _ _ IN'))).
    * unfold remove; fold (remove nat_eq_dec).
      case nat_eq_dec as [EQ | _].
      --  contradict (NE' EQ).
      --  reflexivity.
Qed.

Lemma remove_n_dups_empty :
    forall (l : list nat) (n : nat),
        remove nat_eq_dec n (nodup nat_eq_dec l) = [] ->
            nodup nat_eq_dec l = [n] \/ nodup nat_eq_dec l = [].
Proof.
intros l n RlE.
induction l.
- right.
  reflexivity.
- unfold nodup; fold (nodup nat_eq_dec).
  rewrite remove_dups_order in *.
  unfold remove in *; fold (remove nat_eq_dec) in *.
  case (nat_eq_dec n a) as [EQ | NE].
  + destruct EQ.
    destruct (IHl RlE) as [Ln | Le];
    case (in_dec nat_eq_dec n l) as [IN | NIN].
    * left.
      apply Ln.
    * contradict NIN.
      refine ((proj1 (nodup_incl nat_eq_dec [n] _)) _ _ (in_eq _ _)).
      rewrite Ln.
      apply incl_refl.
    * right.
      apply Le.
    * left.
      rewrite Le.
      reflexivity.
  + unfold nodup in RlE; fold (nodup nat_eq_dec) in RlE.
    case in_dec as [IN | NIN].
    * rewrite <- nodup_In, RlE in IN.
      inversion IN.
    * inversion RlE.
Qed.

Lemma remove_dups_twice : forall (l : list nat),
  nodup nat_eq_dec (nodup nat_eq_dec l) = nodup nat_eq_dec l.
Proof.
intros l.
apply nodup_fixed_point, NoDup_nodup.
Qed.

Lemma member_remove' : forall (l : list nat) (m n : nat),
  nat_eqb m n = false ->
  member n l = true ->
  member n (remove nat_eq_dec m l) = true.
Proof.
intros l m n NE' IN.
induction l.
- apply IN.
- unfold member in IN.
  fold member in IN.
  unfold remove.
  fold (remove nat_eq_dec).
  case (nat_eq_dec m a) as [EQ | NE].
  + destruct EQ.
    case (nat_eqb m n) eqn:EQB.
    * inversion NE'.
    * apply IHl, IN.
  + unfold member.
    fold member.
    case (nat_eqb a n) eqn:EQB.
    * reflexivity.
    * apply IHl, IN.
Qed.

Lemma member_remove : forall (l : list nat) (m n : nat),
  nat_eqb m n = false ->
  member n (remove nat_eq_dec m l) = false ->
  member n l = false.
Proof.
intros l m n NEB NMEM.
case (member n l) eqn:MEM.
- rewrite (member_remove' _ _ _ NEB MEM) in NMEM. apply NMEM.
- reflexivity.
Qed.

Lemma member_remove_dups : forall (l : list nat) (n : nat),
  member n (nodup nat_eq_dec l) = false -> member n l = false.
Proof.
intros. induction l; auto.
simpl. simpl in H.
case in_dec as [IN | NIN];
destruct (nat_eqb a n) eqn:EQB.
- apply nat_eqb_eq in EQB.
  destruct EQB.
  apply not_member_nin in H.
  contradict H.
  apply nodup_In, IN.
- apply IHl, H.
- apply nat_eqb_eq in EQB.
  destruct EQB.
  unfold member in H.
  rewrite nat_eqb_refl in H.
  inversion H.
- apply IHl.
  unfold member in H.
  rewrite EQB in H.
  apply H.
Qed.

Lemma member_concat' : forall (l1 l2 : list nat) (n : nat),
  member n (l1 ++ l2) = true ->
  member n l1 = true \/ member n l2 = true.
Proof.
intros. induction l1.
- right. apply H.
- simpl in H. simpl. destruct (nat_eqb a n) eqn:Hx.
  + left. auto.
  + destruct (IHl1 H).
    * left. apply H0.
    * right. apply H0.
Qed.

Lemma member_concat : forall (l1 l2 : list nat) (n : nat),
  member n (l1 ++ l2) = false ->
  member n l1 = false /\ member n l2 = false.
Proof.
intros. induction l1; auto.
simpl. case_eq (nat_eqb a n); intros; simpl in H; rewrite H0 in H.
- inversion H.
- apply (IHl1 H).
Qed.

Lemma member_remove_dups_concat : forall (l1 l2 : list nat) (n : nat),
  member n (nodup nat_eq_dec (l1 ++ l2)) = false ->
  member n l1 = false /\ member n l2 = false.
Proof.
intros.
apply member_concat.
apply member_remove_dups.
apply H.
Qed.

Lemma concat_member : forall (l l' : list nat) (n : nat),
  member n l = true -> member n (l ++ l') = true.
Proof.
intros. destruct (member n (l ++ l')) eqn:Hn; auto.
destruct (member_concat _ _ _ Hn). rewrite H0 in H. inversion H.
Qed.

Lemma remove_dups_member : forall (l : list nat) (n : nat),
  member n l = true -> member n (nodup nat_eq_dec l) = true.
Proof.
intros. destruct (member n (nodup nat_eq_dec l)) eqn:Hn; auto.
apply member_remove_dups in Hn. rewrite Hn in H. inversion H.
Qed.

Fixpoint repeated_element_n (l : list nat) (n : nat) : bool :=
match l with
| [] => true
| m :: l' => nat_eqb m n && repeated_element_n l' n
end.

Lemma in_reapeated_is : forall (m n : nat) (L : list nat), repeated_element_n L n = true -> In m L -> m = n.
Proof.
induction L;
intros RL IN.
- inversion IN.
- destruct IN as [EQ | IN].
  + destruct EQ.
    apply (nat_eqb_eq _ _ (proj1 (and_bool_prop _ _ RL))).
  + apply (IHL (proj2 (and_bool_prop _ _ RL)) IN).
Qed.

Lemma remove_dups_repeated_element : forall (l : list nat) (n : nat),
  repeated_element_n l n = true ->
  sum (nodup nat_eq_dec l = [n]) (l = []).
Proof.
intros.
induction l; auto.
left.
apply and_bool_prop in H as [X1 X2].
fold repeated_element_n in X2.
destruct (IHl X2) as [H3 | H3].
- simpl. rewrite H3. 
  apply nat_eqb_eq in X1.
  destruct X1.
  unfold repeated_element_n in X2.
  destruct l.
  + inversion H3.
  + apply and_bool_prop in X2 as [X1 X2].
    apply nat_eqb_eq in X1.
    destruct X1.
    case (in_dec nat_eq_dec n (n :: l)) as [_ | FAL].
    * reflexivity.
    * contradict FAL.
      left.
      reflexivity.
- rewrite H3. rewrite (nat_eqb_eq _ _ X1). reflexivity.
Qed.

Lemma nodup_nil : forall l : list nat, nodup nat_eq_dec l = [] -> l = [].
Proof.
induction l;
intros EQ.
- reflexivity.
- unfold nodup in EQ.
  fold (nodup nat_eq_dec) in EQ.
  case in_dec as [IN | NIN].
  + rewrite (IHl EQ) in IN.
    inversion IN.
  + inversion EQ.
Qed.

Lemma remove_dups_repeated_element' : forall (l : list nat) (n : nat),
  nodup nat_eq_dec l = [n] ->
  repeated_element_n l n = true.
Proof.
intros. induction l; auto.
simpl. inversion H.
case in_dec as [IN | NIN].
- pose proof (IHl H1).
  destruct (in_reapeated_is _ _ _ H0 IN).
  rewrite nat_eqb_refl.
  apply H0.
- inversion H1.
  destruct H2.
  rewrite nat_eqb_refl.
  rewrite (nodup_nil _ H3).
  reflexivity.
Qed.

Lemma repeated_element_n_concat_aux : forall (l1 l2 : list nat) (m n : nat),
  repeated_element_n (l1 ++ (m :: l2)) n = true ->
  nat_eqb m n && repeated_element_n l2 n = true.
Proof.
intros. induction l1; simpl in H.
- apply H.
- apply IHl1. destruct (and_bool_prop _ _ H). apply H1.
Qed.

Lemma repeated_element_n_concat : forall (l1 l2 : list nat) (n : nat),
  repeated_element_n (l1 ++ l2) n = true ->
  repeated_element_n l1 n = true /\ repeated_element_n l2 n = true.
Proof.
intros. split.
- induction l1; auto.
  simpl. simpl in H. destruct (and_bool_prop _ _ H).
  rewrite H0, (IHl1 H1). auto.
- induction l2; auto. simpl.
  apply (repeated_element_n_concat_aux l1 l2 a n), H.
Qed.

Lemma remove_dup_single_right : forall l1 l2 m, nodup nat_eq_dec (l1 ++ l2) = [m] -> nodup nat_eq_dec l2 = [m] \/ nodup nat_eq_dec l2 = [].
Proof.
intros. pose proof (remove_dups_repeated_element' _ _ H). pose proof (repeated_element_n_concat _ _ _ H0). destruct H1. destruct (remove_dups_repeated_element _ _ H2); auto. rewrite e. auto.
Qed.

Lemma remove_dup_single_left : forall l1 l2 m, nodup nat_eq_dec (l1 ++ l2) = [m] -> nodup nat_eq_dec l1 = [m] \/ nodup nat_eq_dec l1 = [].
Proof.
intros. pose proof (remove_dups_repeated_element' _ _ H). pose proof (repeated_element_n_concat _ _ _ H0). destruct H1. destruct (remove_dups_repeated_element _ _ H1); auto. rewrite e. auto.
Qed.

Lemma remove_not_in : forall l n, list_eqb (remove nat_eq_dec n l) [n] = false.
Proof.
intros. induction l. auto. simpl. case (nat_eq_dec n a) as [EQ | NE].
- auto.
- simpl.
  case (nat_eqb a n) eqn:Y.
  + contradict NE.
    symmetry.
    apply nat_eqb_eq, Y.
  + reflexivity.
Qed. 

Lemma remove_not_member : forall l n, member n (remove nat_eq_dec n l) = false.
Proof.
intros. induction l. auto. simpl.  case (nat_eq_dec n a) as [EQ | NE].
- auto.
- simpl.
  case (nat_eqb a n) eqn:Y.
  + contradict NE.
    symmetry.
    apply nat_eqb_eq, Y.
  + apply IHl.
Qed. 

Lemma member_remove_true : forall l n m, member n (remove nat_eq_dec m l) = true -> member n l = true.
Proof.
intros. induction l; inversion H. rewrite H1. simpl. case (nat_eqb a n) eqn:X; auto.
case (nat_eq_dec m a) as [EQ | NE]; auto.
- simpl in H1. rewrite X in H1. auto.
Qed.

Lemma remove_member_false : forall l n m, member n l = false -> member n (remove nat_eq_dec m l) = false.
Proof.
intros. case (nat_eqb n m) eqn:X.
- apply nat_eqb_eq in X. destruct X. apply remove_not_member.
- induction l. auto. simpl. inversion H. case (nat_eqb a n) eqn:X1; auto. inversion H1. rewrite H1. case (nat_eq_dec m a) as [EQ | NE]; auto. simpl. rewrite X1. auto.
Qed.

Lemma member_remove_dups_true : forall l n, member n (nodup nat_eq_dec l) = true -> member n l = true.
Proof.

intros. induction l; inversion H. simpl. case (nat_eqb a n) eqn:X; auto.
case in_dec as [IN | NIN];
rewrite H1; apply IHl.
- apply H1.
- unfold member in H1.
  rewrite X in H1.
  apply H1.
Qed.  

Lemma nodups_incl_app : forall L1 L2, (forall m, In m L1 -> In m L2) -> nodup nat_eq_dec (L1 ++ L2) = nodup nat_eq_dec L2. 
Proof.
induction L1; intros.
- rewrite app_nil_l. reflexivity.
- rewrite <- app_comm_cons.
  unfold nodup; fold (nodup nat_eq_dec).
  case in_dec as [IN | NIN].
  + apply IHL1.
    apply (fun m HY => H m (or_intror HY)).
  + contradict NIN.
    apply in_or_app.
    right.
    apply H.
    left.
    reflexivity.
Qed.

Lemma remove_dups_concat_self : forall L, nodup nat_eq_dec (L ++ L) = nodup nat_eq_dec L.
Proof.
intros.
apply nodups_incl_app.
auto.
Qed.

Lemma remove_dups_double_cons_ne : forall n m l, nodup nat_eq_dec (n :: m :: l) = n :: m :: l -> nat_eqb m n = false.
Proof.
intros.
case (nat_eqb m n) eqn:EQB.
- apply nat_eqb_eq in EQB.
  destruct EQB.
  pose proof (NoDup_nodup nat_eq_dec (m :: m :: l)).
  rewrite H in H0.
  inversion H0.
  contradict H3.
  left.
  reflexivity.
- reflexivity.
Qed.

Lemma remove_idem_not_mem : forall l n, remove nat_eq_dec n l = l -> member n l = false.
Proof.
intros. induction l. auto. simpl in *. case (nat_eqb a n) eqn:X.
- apply nat_eqb_eq in X. destruct X. pose proof (remove_not_member l a). 
  case nat_eq_dec as [_ | FAL].
  + rewrite H in H0. simpl in H0. rewrite nat_eqb_refl in H0. apply H0.
  + contradict FAL.
    reflexivity.
- case nat_eq_dec as [FAL | _].
+ destruct FAL.
  rewrite nat_eqb_refl in X.
  inversion X.
+ inversion H.
  rewrite H1.
  apply IHl, H1.
Qed.

Lemma remove_not_mem_idem : forall l n, member n l = false -> remove nat_eq_dec n l = l.
Proof.
intros. induction l. auto. simpl in *. case (nat_eqb a n) eqn:X. inversion H. rewrite IHl; auto.
case (nat_eq_dec n a) as [FAL | _].
- destruct FAL.
  rewrite nat_eqb_refl in X.
  inversion X.
- reflexivity.
Qed.

Lemma remove_dups_idem_remove_false : forall l n, nodup nat_eq_dec (n :: l) = n :: l -> member n l = false.
Proof.
intros.
apply nodup_inv in H.
apply not_member_nin, H.
Qed.

Lemma not_mem_dupes : forall l n, member n l = false -> member n (nodup nat_eq_dec l) = false.
Proof.
intros.
apply not_member_nin.
apply not_member_nin in H.
intros FAL.
apply H.
apply nodup_In in FAL.
apply FAL.
Qed.

Lemma remove_dups_idem_remove_triv : forall l n, nodup nat_eq_dec (n :: l) = n :: l -> remove nat_eq_dec n (n :: l) = l.
Proof.
intros.
pose proof (remove_dups_idem_remove_false _ _ H).
unfold remove; fold (remove nat_eq_dec).
case nat_eq_dec as [_ | FAL].
- apply notin_remove, not_member_nin, H0.
- contradict FAL.
  reflexivity.
Qed.

Lemma remove_idem_tail : forall l n, nodup nat_eq_dec (n :: l) = n :: l -> nodup nat_eq_dec l = l.
Proof.
intros.
pose proof (remove_dups_idem_remove_false _ _ H).
unfold nodup in H.
fold (nodup nat_eq_dec) in H.
case in_dec as [FAL | _].
- apply member_in in FAL.
  rewrite H0 in FAL.
  inversion FAL.
- inversion H.
  repeat rewrite H2.
  reflexivity.
Qed.

Lemma member_split : forall l n, member n l = true -> exists l1 l2, l = l1 ++ (n :: l2).
Proof.
intros. induction l. inversion H. simpl in H. case (nat_eqb a n) eqn:X.
- apply nat_eqb_eq in X. destruct X. exists [], l. auto.
- destruct (IHl H) as [l1 [l2 HL]]. exists (a :: l1), l2. rewrite HL. auto.
Qed.

Lemma member_split_first : forall l n, member n l = true -> exists l1 l2, l = l1 ++ (n :: l2) /\ member n l1 = false.
Proof.
intros. induction l. inversion H. simpl in H. case (nat_eqb a n) eqn:X.
- apply nat_eqb_eq in X. destruct X. exists [], l. auto.
- destruct (IHl H) as [l1 [l2 [HL1 Hl2]]]. exists (a :: l1), l2. split. rewrite HL1. auto. simpl. rewrite X. auto.
Qed.

Lemma split_member : forall l1 l2 n, member n (l1 ++ (n :: l2)) = true.
Proof.
intros l1. induction l1. intros. simpl. rewrite nat_eqb_refl. auto. intros. simpl. case (nat_eqb a n); auto.
Qed.