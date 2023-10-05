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


Lemma In_single :
    forall {A : Type} {a b : A}, In a [b] -> a = b.
Proof.
intros A a b IN.
destruct IN as [EQ | FAL].
apply eq_sym, EQ.
inversion FAL.
Qed.

Lemma combine_eq_len :
    forall {A B : Type} {L1 L3 : list A} {L2 L4 : list B},
        length L1 = length L2 ->
            combine L1 L2 ++ combine L3 L4 = combine (L1 ++ L3) (L2 ++ L4).
Proof.
intros A B L1.
induction L1;
intros L3 L2 L4 EQ;
destruct L2.
- reflexivity.
- inversion EQ.
- inversion EQ.
- repeat rewrite <- app_comm_cons.
  unfold combine;
  fold (@combine A A).
  rewrite <- IHL1.
  reflexivity.
  apply eq_add_S, EQ.
Qed.

Lemma combine_filter_fst :
    forall {A B : Type} {L1 : list A} {L2 : list B} (f : A -> bool),
        length L1 = length L2 ->
            length (filter (fun X => f (fst X)) (combine L1 L2)) = length (filter f L1).
Proof.
intros A B L1.
induction L1;
intros L2 f EQL;
destruct L2.
- reflexivity.
- inversion EQL.
- inversion EQL.
- unfold combine;
  fold (@combine A B).
  unfold filter;
  fold (filter f) (filter (fun (X : A * B) => f (fst X))).
  unfold fst at 1.
  case (f a) eqn:T.
  + unfold length;
    fold (@length A) (@length (A*B)).
    rewrite IHL1.
    reflexivity.
    apply eq_add_S, EQL.
  + apply IHL1, eq_add_S, EQL.
Qed.

Lemma eq_app_eq :
    forall {A : Type} {L1 L2 L3 L4 : list A},
        L1 = L2 -> L3 = L4 -> L1 ++ L3 = L2 ++ L4.
Proof.
intros A L1 L2 L3 L4 EQ1 EQ2.
rewrite EQ1, EQ2.
reflexivity.
Qed.

Lemma fst_split :
    forall {A B : Type} {L : list (A * B)} {a : A} {b : B},
        fst (split ((a,b) :: L)) = a :: fst (split L).
Proof.
intros A B L a b.
unfold split at 1.
fold (split L).
unfold fst at 1.
destruct (split L).
reflexivity.
Qed.

Lemma snd_split :
    forall {A B : Type} {L : list (A * B)} {a : A} {b : B},
        snd (split ((a,b) :: L)) = b :: snd (split L).
Proof.
intros A B L a b.
unfold split at 1.
fold (split L).
unfold snd at 1.
destruct (split L).
reflexivity.
Qed.

Lemma split_type : 
    forall {A B : Type} {L : list (A * B)},
        split L = pair (fst (split L)) (snd (split L)).
Proof.
intros A B L.
induction L.
reflexivity.
destruct a.
rewrite fst_split, snd_split.
unfold split at 1.
fold (split L).
rewrite IHL at 1.
reflexivity.
Qed.

Lemma app_split :
    forall {A B : Type} {L1 L2 : list (A * B)},
        split (L1 ++ L2) = pair (fst (split L1) ++ (fst (split L2))) (snd (split L1) ++ (snd (split L2))).
Proof.
intros A B L1.
induction L1;
intros L2.
repeat rewrite app_nil_l.
apply split_type.
destruct a.
rewrite fst_split, snd_split.
rewrite <- app_comm_cons.
unfold split at 1.
fold (split (L1 ++ L2)).
rewrite IHL1 at 1.
reflexivity.
Qed.

Lemma combine_with_filter_split :
    forall {A B : Type} (f : A -> bool) {L1 : list A} {L2 : list B},
        length L1 = length L2 ->
            combine (filter f L1) (snd (split (filter (fun X => f (fst X)) (combine L1 L2)))) = (filter (fun X => f (fst X)) (combine L1 L2)).
Proof.
intros A B f.
induction L1;
intros L2 EQL;
destruct L2.
- reflexivity.
- inversion EQL.
- inversion EQL.
- unfold length in EQL;
  fold (@length A) (@length B) in EQL.
  unfold combine;
  fold (@combine A B).
  unfold filter;
  fold (@filter A f) (@filter (A * B) (fun X => f (fst X))).
  unfold fst at 1 4.
  case (f a) eqn:Val.
  + rewrite snd_split.
    unfold combine at 1.
    fold (@combine A B).
    rewrite IHL1.
    reflexivity.
    apply (eq_add_S _ _ EQL).
  + rewrite IHL1.
    reflexivity.
    apply (eq_add_S _ _ EQL).
Qed.

Lemma filter_fst_non_target : 
    forall {A B : Type} (f : A -> bool) (m : A -> B) (L : list A),
        (snd (split (filter (fun X => f (fst X)) (combine L (map m L))))) = map m (filter (fun X => f X) L).
Proof.
intros A B f m L.
induction L.
- reflexivity.
- unfold combine, map.
  fold (map m) (combine L (map m L)).
  unfold filter;
  fold (filter f) (filter (fun (X : A * B) => (f (fst X)))).
  unfold fst at 1.
  case (f a) eqn:T;
  try rewrite snd_split;
  rewrite IHL;
  reflexivity.
Qed.

Lemma skipn_app2 {A : Type} {n : nat} : forall (l1 l2 : list A),
    skipn (length l1 + n) (l1 ++ l2) = (skipn n l2).
Proof.
intros L1 L2.
rewrite skipn_app.
rewrite minus_n_plus_m.
rewrite skipn_all2.
reflexivity.
destruct n.
rewrite <- plus_n_O.
reflexivity.
apply le_S_n.
rewrite <- plus_n_Sm.
repeat rewrite <- plus_Sn_m.
apply (@nat_lt_add_trans_l _ _ (S n) _ (le_n _)).
rewrite <- plus_n_Sm.
reflexivity.
Qed.

Fixpoint bury {A : Type} (L : list A) (n : nat) : list A :=
match L with
| [] => []
| hd :: tl => match n with
    | 0 => tl ++ [hd]
    | S m => hd :: bury tl m
    end
end.

Lemma in_bury {A : Type} {L : list A} {n : nat} : forall (a : A), In a L <-> In a (bury L n).
Proof.
generalize n.
induction L;
intros b;
split;
intros IN.
1,2 : inversion IN.
- destruct IN as [[] | IN];
  destruct b.
  + apply in_or_app, or_intror, or_introl, eq_refl.
  + apply or_introl, eq_refl.
  + apply in_or_app, or_introl, IN.
  + apply or_intror, IHL, IN.
- destruct b;
  try destruct IN as [[] | IN];
  try apply in_app_or in IN as [IN | [[] |[]]].
  + apply or_intror, IN.
  + apply or_introl, eq_refl.
  + apply or_introl, eq_refl.
  + apply or_intror.
    apply <- IHL.
    apply IN. 
Qed.

Lemma bury_map {A B : Type} {L : list A} {f : A -> B} {n : nat} : map f (bury L n) = bury (map f L) n.
Proof.
generalize n.
induction L.
reflexivity.
intros m.
destruct m.
apply map_app.
unfold bury, map;
fold (@bury A) (@bury B) (map f).
rewrite IHL.
reflexivity.
Qed.

Lemma bury_combine {A B : Type} {L1 : list A} {L2 : list B} {n : nat} : length L1 = length L2 -> combine (bury L1 n) (bury L2 n) = bury (combine L1 L2) n.
Proof.
generalize L2 n.
induction L1;
induction L0;
intros m LEN;
try inversion LEN as [LEN'].
reflexivity.
destruct m.
- unfold bury, combine;
  fold (@combine A B).
  rewrite <- (combine_eq_len LEN').
  reflexivity.
- unfold bury, combine;
  fold (@bury A) (@bury B) (@bury (A*B)) (@combine A B).
  rewrite (IHL1 _ _ LEN').
  reflexivity.
Qed.

Lemma bury_split {A B : Type} {L : list (A * B)} {n : nat} : split (bury L n) = pair (bury (fst (split L)) n) (bury (snd (split L)) n).
Proof.
generalize n.
induction L;
intros m.
reflexivity.
destruct m.
- destruct a.
  rewrite fst_split, snd_split.
  unfold bury.
  rewrite app_split.
  reflexivity.
- unfold bury, combine;
  fold (@bury A) (@bury B) (@bury (A*B)) (@combine A B).
  destruct a.
  unfold split at 1.
  fold (split (bury L m)).
  rewrite IHL, fst_split, snd_split.
  reflexivity.
Qed.

Lemma bury_nil {A : Type} {L  : list A} {n : nat} : bury L n = [] <-> L = [].
Proof.
split;
intros EQ.
destruct L.
reflexivity.
destruct n;
destruct L;
inversion EQ.
rewrite EQ.
reflexivity.
Qed.

Lemma bury_length {A : Type} {L  : list A} {n : nat} : length (bury L n) = length L.
Proof.
generalize n.
induction L.
reflexivity.
destruct n0;
unfold bury, length;
fold (@bury A) (@length A).
rewrite app_length.
unfold length;
fold (@length A).
rewrite <- plus_n_Sm, <- plus_n_O.
reflexivity.
rewrite IHL.
reflexivity.
Qed.

Lemma bury_type {A : Type} {a : A} {L1 L2 : list A} : (bury (L1 ++ a :: L2) (length L1)) = L1 ++ L2 ++ [a].
Proof.
induction L1.
reflexivity.
unfold length;
fold (@length A).
repeat rewrite <- app_comm_cons.
unfold bury;
fold (@bury A).
rewrite IHL1.
reflexivity.
Qed.

Lemma bury_ge {A : Type} {L : list A} {n : nat} : n >= length L -> bury L n = L.
Proof.
generalize n.
induction L;
intros m GE.
reflexivity.
destruct m;
inversion GE as [ GE' | x GE' EQ];
unfold bury;
fold (@bury A);
rewrite IHL;
unfold ge;
try reflexivity.
unfold length in GE';
fold (@length A) in GE'.
apply le_S_n, le_S, GE'.
Qed.

Lemma length_split_n {A : Type} {L : list A} {n : nat} : n < length L -> {L1 : list A & {L2 : list A & {a : A & length L1 = n /\ L1 ++ a :: L2 = L}}}.
Proof.
intros LT.
refine (existT _ (firstn n L) (existT _ (tl (skipn n L)) _)).
case (skipn n L) eqn:EQ.
- apply length_zero_iff_nil in EQ.
  pose proof LT as LT'. 
  rewrite <- (firstn_skipn n L), app_length, EQ, <- plus_n_O, firstn_length in LT'.
  rewrite min_l in LT'.
  + lia.
  + apply le_S_n, le_S, LT.
- refine (existT _ a (conj _ _)).
  + rewrite firstn_length.
    apply min_l.
    apply le_S_n, le_S, LT.
  + unfold tl.
    rewrite <- EQ.
    apply firstn_skipn.
Qed.

Lemma nth_pre_bury {A : Type} {L : list A} {n m : nat} {a : A} : n < m -> nth n (bury L m) a = nth n L a.
Proof.
intros LT.
destruct (nat_semiconnex m (length L)) as [LT' | [GT | EQ]].
- destruct (length_split_n LT') as [L1 [L2 [b [LEN EQ]]]].
  rewrite <- EQ, <- LEN, bury_type, app_nth1, app_nth1.
  reflexivity.
  all : rewrite LEN;
        apply LT.
- rewrite bury_ge.
  reflexivity.
  apply le_S_n, le_S, GT.
- rewrite bury_ge.
  reflexivity.
  rewrite EQ.
  apply le_n.
Qed.

Lemma nth_post_bury {A : Type} {L : list A} {n m : nat} {a : A} : n >= m -> S n <> (length L) -> nth n (bury L m) a = nth (S n) L a.
Proof.
intros GT NE.
destruct (nat_semiconnex m (length L)) as [LT | [GT' | EQ]].
destruct (nat_semiconnex n (length L)) as [LT' | [GT' | EQ']].
1 : { destruct (length_split_n LT) as [L1 [L2 [b [LEN EQ]]]].
      { rewrite <- EQ, <- LEN, bury_type, app_nth2, app_nth1, app_nth2, minus_ge_succ.
        reflexivity.
        all : rewrite LEN;
              try apply GT.
        1 : apply le_S, GT.
        1 : assert (S n < length L) as LT''.
            lia.
            rewrite <- EQ in LT''.
            rewrite app_length in LT''.
            rewrite <- (plus_n_Sm _ (length L2)) in LT''.
            lia. } }
all : repeat rewrite nth_overflow;
      try rewrite bury_length;
      try reflexivity;
      try lia.
Qed.

Lemma nth_end_bury {A : Type}  {L : list A} {n m : nat} {a : A} : m < (length L) -> S n = (length L) -> nth n (bury L m) a = nth m L a.
Proof.
generalize n m.
induction L;
intros l1 l2 LE EQ;
inversion EQ as [EQ'].
destruct l1.
- symmetry in EQ'.
  apply length_zero_iff_nil in EQ'.
  destruct (eq_sym EQ').
  unfold length.
  destruct EQ.
  inversion LE as [EQ''| x FAL].
  reflexivity.
  inversion FAL.
- pose proof (fun X => IHL l1 l2 X EQ').
  destruct l2;
  unfold bury;
  fold (@bury A).
  + rewrite plus_n_O at 1.
    apply (app_nth2_plus L [a0]).
  + unfold nth;
    fold (@nth A).
    rewrite <- EQ'.
    apply (IHL _ _ (le_S_n _ _ LE) EQ').
Qed.

Lemma map_tail {A B : Type} {L : list A} {F : A -> B} : tl (map F L) = map F (tl L).
Proof. induction L; reflexivity. Qed.

Lemma nth_tail {A : Type} {L : list A} {a : A} {n : nat} : nth n (tl L) a = nth (S n) L a.
Proof. induction L; destruct n; reflexivity. Qed.

Lemma combine_tail {A B : Type} {L1 : list A} {L2 : list B} : combine (tl L1) (tl L2) = tl (combine L1 L2).
Proof. induction L1; induction L2; try reflexivity. destruct L1; reflexivity. Qed.

Lemma cons_tl_len {A : Type} : forall (L : list A), [] <> L -> length (tl L) = length L - 1.
Proof.
induction L;
intros EQ.
destruct EQ.
reflexivity.
unfold tl.
unfold length;
fold (@length A).
unfold minus.
rewrite minus_n_0.
reflexivity.
Qed.

Lemma app_tail {A : Type} {L1 L2 : list A} : L1 <> [] -> (tl L1) ++ L2 = tl (L1 ++ L2).
Proof. induction L1; intros NE. contradict NE. reflexivity. rewrite <- app_comm_cons. reflexivity. Qed.

Lemma tail_len_eq {A B : Type} {L1 : list A} {L2 : list B} : length L1 = length L2 -> length (tl L1) = length (tl L2).
Proof.
intros EQ.
destruct L1;
destruct L2;
inversion EQ.
reflexivity.
apply H0.
Qed.

Lemma in_tail {A : Type} {L : list A} {a : A} : In a (tl L) -> In a L.
Proof. intros IN. destruct L. inversion IN. apply or_intror, IN. Qed.

Lemma in_double_head {A : Type} {L : list A} {a : A} : forall (b : A), In b (a :: a :: L) -> In b (a :: L).
Proof.
intros B [[] | INB].
apply or_introl, eq_refl.
apply INB.
Qed.

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

Lemma flat_map_split {A B : Type} {a : A} {L1 L2 : list A} {F : A -> list B} : flat_map F (L1 ++ a :: L2) = (flat_map F L1) ++ (F a) ++ (flat_map F L2).
Proof. apply flat_map_app. Qed.

Lemma flat_map_bury_type {A B : Type} {a : A} {L1 L2 : list A} {F : A -> list B} : flat_map F (bury (L1 ++ a :: L2) (length L1)) = (flat_map F L1) ++ (flat_map F L2) ++ (F a).
Proof.
rewrite bury_type.
repeat rewrite flat_map_app.
unfold flat_map;
rewrite app_nil_r.
reflexivity.
Qed.

Lemma flat_map_bury_incl {A B : Type} {L : list A} {F : A -> list B} {n : nat} : forall (b : B), In b (flat_map F (bury L n)) <-> In b (flat_map F L).
Proof.
destruct (nat_semiconnex n (length L)) as [LT | [GT | EQ]].

all : intros b.

2,3 : rewrite bury_ge;
      try reflexivity;
      unfold ge.

3 : rewrite EQ;
    reflexivity.

2 : apply le_S_n, le_S, GT.

split;
rewrite <- (firstn_skipn n L).

1 : rewrite <- (PeanoNat.Nat.min_l n (length L) (le_S_n _ _ (le_S _ _ LT))) at 3.
2 : rewrite <- (PeanoNat.Nat.min_l n (length L) (le_S_n _ _ (le_S _ _ LT))) at 5.

all : rewrite <- firstn_length;
      case (skipn n L) eqn:SKIP.

1,3 : pose proof (skipn_length n L) as FAL;
      rewrite SKIP in FAL;
      unfold length in FAL;
      fold (@length A) in FAL;
      symmetry in FAL;
      contradict (minus_lt_not_zero _ _ LT FAL).

all : rewrite flat_map_bury_type, flat_map_split;
      intros IN;
      apply in_app_or in IN as [IN1 | IN];
      try apply in_app_or in IN as [IN2 | IN3];
      try apply in_or_app, or_introl, IN1;
      try apply in_or_app, or_intror, in_or_app, or_intror, IN2;
      try apply in_or_app, or_intror, in_or_app, or_introl, IN3.
Qed.

Lemma flat_map_nth_ext {A B : Type} {L1 L2 : list A} {F : A -> list B} {a : A} : length L1 = length L2 -> (forall (n : nat), F (nth n L1 a) = F (nth n L2 a)) -> flat_map F L1 = flat_map F L2.
Proof.
generalize L2.
induction L1;
induction L0;
intros LEN HYP.
- reflexivity.
- inversion LEN.
- inversion LEN.
- unfold flat_map;
  fold (flat_map F).
  pose proof (HYP 0) as HD.
  unfold nth in HD.
  rewrite HD.
  inversion LEN as [LEN'].
  rewrite (IHL1 _ LEN').
  reflexivity.
  intros n.
  apply (HYP (S n)).
Qed.

Lemma flat_map_nth_ext_bury {A B : Type} {L1 L2 : list A} {F : A -> list B} {a : A} {n : nat} : length L1 = length L2 -> (forall (n : nat), F (nth n L1 a) = F (nth n L2 a)) -> flat_map F (bury L1 n) = flat_map F (bury L2 n).
Proof.
generalize n.
generalize L2.
induction L1;
induction L0;
intros m LEN HYP.
- reflexivity.
- inversion LEN.
- inversion LEN.
- destruct m.
  + unfold bury.
    pose proof (HYP 0) as HD.
    unfold nth in HD.
    repeat rewrite flat_map_app.
    unfold flat_map at 2 4.
    rewrite HD, app_nil_r.
    inversion LEN as [LEN'].
    rewrite (@flat_map_nth_ext _ _ L1 L0 _ a LEN').
    reflexivity.
    intros x.
    apply (HYP (S x)).
  + unfold bury;
    fold (@bury A).
    unfold flat_map;
    fold (flat_map F).
    pose proof (HYP 0) as HD.
    unfold nth in HD.
    rewrite HD.
    inversion LEN as [LEN'].
    rewrite (IHL1 _ _ LEN').
    reflexivity.
    intros x.
    apply (HYP (S x)).
Qed.

Lemma flat_map_nth_ext_tl {A B : Type} {L1 L2 : list A} {F : A -> list B} {a : A} : length L1 = length L2 -> (forall (n : nat), F (nth n L1 a) = F (nth n L2 a)) -> flat_map F (tl L1) = flat_map F (tl L2).
Proof.
generalize L2.
induction L1;
induction L0;
intros LEN HYP.
- reflexivity.
- inversion LEN.
- inversion LEN.
- unfold tl.
  inversion LEN as [LEN'].
  rewrite (@flat_map_nth_ext _ _ L1 L0 _ a LEN').
  reflexivity.
  intros x.
  apply (HYP (S x)).
Qed.

Lemma nth_app_split {A : Type} {L1 L2 L3 L4 : list A} {a : A} : length L1 = length L2 -> length L3 = length L4 -> (forall (n : nat), nth n L1 a = nth n L2 a) -> (forall (n : nat), nth n L3 a = nth n L4 a) -> (forall (n : nat), nth n (L1 ++ L3) a = nth n (L2 ++ L4) a).
Proof.
intros EQ1 EQ2 EX1 EX2 n.
destruct (nat_semiconnex n (length L1)) as [LT | [GT | EQ]].
- repeat rewrite app_nth1.
  apply EX1.
  rewrite <- EQ1.
  apply LT.
  apply LT.
- repeat rewrite app_nth2.
  rewrite EQ1.
  apply EX2.
  lia.
  lia.
- repeat rewrite app_nth2.
  rewrite EQ1.
  apply EX2.
  lia.
  lia.
Qed.

Lemma len_1_head {A : Type} {L : list A} {a : A} : length L = 1 -> [(hd a L)] = L.
Proof.
intros LEN.
destruct L.
inversion LEN.
destruct L.
reflexivity.
inversion LEN.
Qed.

Lemma head_tail_combine {A : Type} {L : list A} {a : A} : L <> [] -> hd a L :: tl L = L.
Proof.
intros NE.
destruct L.
contradict (NE eq_refl).
reflexivity.
Qed.

Lemma nin_head {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall {L : list A} {a b : A},
        ~ In b (a :: L) ->
            ~ In b L.
Proof.
intros L a b NIN.
case (in_dec DEC b L) as [IN' | NIN'].
contradict NIN.
apply or_intror, IN'.
apply NIN'.
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

Lemma incl_remove {A : Type} {DEC : forall (a b : A), {a = b} + {a <> b}} :
    forall (a : A) (L : list A),
        incl (remove DEC a L) L.
Proof.
intros a L b.
apply (fun INB => proj1 (in_remove DEC _ _ _ INB)).
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

Fixpoint precedence {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) (L : list A) (a b : A) : bool :=
match L with
| [] => false
| hd :: tl => if DEC hd a then if (in_dec DEC b tl) then true else false else if DEC hd b then false else precedence DEC tl a b
end.

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

Lemma map_nil_remove_flat {A B : Type} {DECA : forall (a b : A), {a = b} + {a <> b}}  {DECB : forall (a b : B), {a = b} + {a <> b}} :
    forall (f : A -> list B) (a : A) (L : list A),
        f a = [] ->
            (flat_map f L) = (flat_map f (remove DECA a L)).
Proof.
intros f a L NIL.
induction L.
- reflexivity.
- unfold remove;
  fold (remove DECA).
  unfold flat_map;
  fold (flat_map f).
  case (DECA a a0) as [EQ | NE].
  + destruct EQ.
    rewrite NIL.
    apply IHL.
  + unfold flat_map.
    fold (flat_map f).
    rewrite IHL.
    reflexivity.
Qed.

Lemma flat_map_incl {A B : Type} {DECA : forall (a b : A), {a = b} + {a <> b}}  {DECB : forall (a b : B), {a = b} + {a <> b}} :
    forall (f : A -> list B) (L1 L2 : list A),
        incl L1 L2 ->
            incl (flat_map f L1) (flat_map f L2).
Proof.
intros f L1 L2 SUB b INB.
apply in_flat_map in INB as [a [INA INB]].
apply in_flat_map.
exists a.
apply (conj (SUB _ INA) INB).
Qed.

(*
Lemma flat_map_equiv {A B : Type} {DECA : forall (a b : A), {a = b} + {a <> b}}  {DECB : forall (a b : B), {a = b} + {a <> b}} :
forall (f : A -> list B) (A1 A2 : A) (L1 L2 : list A),
    f A1 = f A2 ->
        incl L1 L2 ->
            In A1 L1 ->
                incl (flat_map f (remove DECA A1 L1)) (flat_map f (remove DECA A2 L2)).
Proof.
intros f A1 A2 L1 L2 EQ SUB INA b INB.
destruct (@flat_map_remove_in_other _ _ DECA DECB f _ _ _ INB) as [NIN | [C [INC INBC]]].
- rewrite EQ in NIN.
  apply (@flat_map_not_in_remove _ _ DECA DECB _ _ _ _ (@flat_map_incl _ _ DECA DECB _ _ _ SUB _ (flat_map_remove_in _ _ _ _ INB)) NIN).
- destruct (DECA C A2) as [EQ1 | NE1].
  + destruct EQ1.
    rewrite <- EQ in INBC.
    apply (@flat_map_in_other_remove _ _ DECA DECB _ _ _ _ (@flat_map_incl _ _ DECA DECB _ _ _ SUB _ (flat_map_remove_in _ _ _ _ INB)) A1 INBC (in_in_remove _ _ (fun FAL => (proj2 (in_remove _ _ _ _ INC)) (eq_sym FAL)) (SUB _ INA))).
  + apply (@flat_map_in_other_remove _ _ DECA DECB _ _ _ _ (@flat_map_incl _ _ DECA DECB _ _ _ SUB _ (flat_map_remove_in _ _ _ _ INB)) C INBC ((in_in_remove _ _ NE1) (SUB _ (proj1 (in_remove _ _ _ _ INC))))).
Qed.
*)
(*
Lemma flat_map_equiv {A B : Type} {DECA : forall (a b : A), {a = b} + {a <> b}}  {DECB : forall (a b : B), {a = b} + {a <> b}} :
forall (f : A -> list B) (A1 A2 : A) (L1 L2 : list A),
    f A1 = f A2 ->
        incl (flat_map f L1) (flat_map f L2) ->
            In A1 L1 ->
                incl (flat_map f (remove DECA A1 L1)) (flat_map f (remove DECA A2 L2)).
Proof.
intros f A1 A2 L1 L2 EQ SUB INA b INB.
destruct (@flat_map_remove_in_other _ _ DECA DECB f _ _ _ INB) as [NIN | [C [INC INBC]]].
- rewrite EQ in NIN.
  apply (@flat_map_not_in_remove _ _ DECA DECB _ _ _ _ (SUB _ (flat_map_remove_in _ _ _ _ INB)) NIN).
- destruct (DECA C A2) as [EQ1 | NE1].
  + destruct EQ1.
    rewrite <- EQ in INBC.
    apply (@flat_map_in_other_remove _ _ DECA DECB _ _ _ _ (SUB _ (flat_map_remove_in _ _ _ _ INB)) A1 INBC).
    apply (in_in_remove _ _ (fun FAL => (proj2 (in_remove _ _ _ _ INC)) (eq_sym FAL))). (SUB _ INA))).
    admit.
  + apply (@flat_map_in_other_remove _ _ DECA DECB _ _ _ _ (SUB _ (flat_map_remove_in _ _ _ _ INB)) C INBC ((in_in_remove _ _ NE1) (SUB _ (proj1 (in_remove _ _ _ _ INC))))).
Qed.
*)

Lemma count_occ_app_one_cases {A : Type} {DEC : forall (a b : A), {a = b} + {a <> b}} :
    forall (a : A) (L1 L2 : list A),
        count_occ DEC (L1 ++ L2) a = 1 ->
            {In a L1 /\ ~In a L2} + {In a L2 /\ ~In a L1}.
Proof.
intros a L1 L2 ONE.
case (in_dec DEC a L1) as [IN1 | NIN1];
case (in_dec DEC a L2) as [IN2 | NIN2].
- apply (count_occ_In DEC) in IN1.
  apply (count_occ_In DEC) in IN2.
  rewrite count_occ_app in ONE.
  destruct (count_occ DEC L1 a).
  contradict IN1.
  intros FAL;
  inversion FAL.
  destruct (count_occ DEC L2 a).
  contradict IN2.
  intros FAL;
  inversion FAL.
  contradict ONE.
  rewrite <- plus_n_Sm.
  intros FAL.
  inversion FAL.
- left.
  apply (conj IN1 NIN2).
- right.
  apply (conj IN2 NIN1).
- apply (count_occ_not_In DEC) in NIN1.
  apply (count_occ_not_In DEC) in NIN2.
  rewrite count_occ_app, NIN1, NIN2 in ONE.
  discriminate.
Qed.

Lemma count_occ_app_one_split {A : Type} {DEC : forall (a b : A), {a = b} + {a <> b}} :
    forall (a : A) (L1 L2 : list A),
        count_occ DEC (L1 ++ L2) a = 1 ->
            {count_occ DEC L1 a = 1 /\ ~In a L2} + {count_occ DEC L2 a = 1 /\ ~In a L1}.
Proof.
intros a L1 L2 ONE.
rewrite count_occ_app in ONE.
destruct (count_occ DEC L1 a) eqn:O1.
- right.
  split.
  apply ONE.
  apply (count_occ_not_In DEC), O1.
- left.
  rewrite plus_Sn_m in ONE.
  destruct n.
  + destruct (count_occ DEC L2 a) eqn:O2.
    * split.
      reflexivity.
      apply (count_occ_not_In DEC), O2.
    * contradict ONE.
      discriminate.
  + contradict ONE.
    discriminate.
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