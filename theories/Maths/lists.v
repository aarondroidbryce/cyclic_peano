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

Lemma rev_list_ind_type {A : Type} :
    forall (P : list A -> Type),
        P [] ->
            (forall (a : A) (L : list A), P (rev L) -> P (rev (a :: L))) ->
                forall (L : list A), P (rev L).
Proof.
intros P ? ? L; induction L; auto.
Qed.

Theorem rev_ind_type {A : Type} :
    forall (P : list A -> Type),
        P [] ->
          (forall (a : A) (L : list A), P L -> P (L ++ [a])) ->
              forall (L : list A), P L.
Proof.
intros P ? ? L. rewrite <- (rev_involutive L).
apply (rev_list_ind_type P); cbn; auto.
Qed.

Lemma in_single :
    forall {A : Type} {a b : A}, In a [b] -> a = b.
Proof.
intros A a b IN.
destruct IN as [EQ | FAL].
apply eq_sym, EQ.
inversion FAL.
Qed.

Lemma in_swap {A : Type} :
    forall (a b c : A) (L1 L2 : list A),
        In a (L1 ++ b :: c :: L2) <-> In a (L1 ++ c :: b :: L2).
Proof.
intros a b c L1 L2.
split;
intros IN;
apply in_app_iff;
apply in_app_iff in IN as [INL1 | [[] | [[] | INL2]]];
firstorder.
Qed.

Lemma in_cont {A : Type} :
    forall (a b : A) (L1 L2 : list A),
        In a (L1 ++ b :: b :: L2) <-> In a (L1 ++ b :: L2).
Proof.
intros a b L1 L2.
split;
intros IN;
apply in_app_iff;
try apply in_app_iff in IN as [INL1 | [[] | [[] | INL2]]];
try apply in_app_iff in IN as [INL1 | [[] | INL2]];
firstorder.
Qed.

Lemma in_split_dec {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} {a : A} : In a L -> {L1 : list A & {L2 : list A & L = L1 ++ a :: L2}}.
Proof.
induction L;
intros IN.
- contradiction IN.
- destruct (DEC a0 a) as [EQ | NE].
  + subst.
    refine (existT _ [] (existT _ L eq_refl)).
  + assert (In a L) as IN'.
    { destruct IN as [EQ | IN].
      contradiction.
      apply IN. }
    destruct (IHL IN') as [L1 [L2 EQ]].
    subst.
    refine (existT _ (a0 :: L1) (existT _ L2 eq_refl)).
Qed.

Lemma in_split_dec_first {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} {a : A} : In a L -> {L1 : list A & {L2 : list A & L = L1 ++ a :: L2 /\ ~ In a L1}}.
Proof.
induction L;
intros IN.
- contradiction IN.
- destruct (DEC a0 a) as [EQ | NE].
  + subst.
    refine (existT _ [] (existT _ L (conj eq_refl (@in_nil _ a)))).
  + assert (In a L) as IN'.
    { destruct IN as [EQ | IN].
      contradiction.
      apply IN. }
    destruct (IHL IN') as [L1 [L2 [EQ NIN]]].
    subst.
    refine (existT _ (a0 :: L1) (existT _ L2 (conj eq_refl _))).
    intros [FAL | FAL].
    apply (NE FAL).
    apply (NIN FAL).
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

Fixpoint unbury {A : Type} (L : list A) (n : nat) : list A :=
match L with
| [] => []
| hd :: tl => match n with
    | 0 => match rev tl with
        | [] => L
        | tlhd :: tltl => tlhd :: hd :: rev tltl
        end
    | S m => hd :: unbury tl m
    end
end.

Lemma unbury_bury {A : Type} {L : list A} {n : nat} : unbury (bury L n) n = L.
Proof.
revert n.
induction L;
intros n.
- reflexivity.
- destruct n.
  + unfold bury.
    destruct L;
    try rewrite <- app_comm_cons;
    unfold unbury;
    fold @unbury.
    * reflexivity.
    * rewrite rev_app_distr.
      unfold rev at 1.
      rewrite app_nil_l, <- app_comm_cons, app_nil_l, rev_involutive.
      reflexivity.
  + unfold bury;
    fold @bury.
    unfold unbury;
    fold @unbury.
    rewrite IHL.
    reflexivity.
Qed.

Lemma rev_nil {A : Type} {L : list A} : (rev L) = [] <-> L = [].
Proof.
destruct L.
reflexivity.
split;
intros EQ.
apply app_eq_nil in EQ as [EQ1 EQ2].
inversion EQ2.
inversion EQ.
Qed.

Lemma bury_unbury {A : Type} {L : list A} {n : nat} : bury (unbury L n) n = L.
Proof.
revert n.
induction L;
intros n.
- reflexivity.
- destruct n.
  + unfold unbury.
    destruct (rev L) eqn:EQ.
    * rewrite rev_nil in EQ.
      subst.
      reflexivity.
    * unfold bury.
      rewrite <- rev_involutive.
      unfold rev at 3.
      fold (rev L).
      rewrite EQ.
      rewrite rev_app_distr.
      reflexivity.
  + unfold unbury;
    fold @unbury.
    unfold bury;
    fold @bury.
    rewrite IHL.
    reflexivity.
Qed.

Fixpoint set_bury {A : Type} (LA : list A) (LN : list nat) : list A :=
match LN with
| [] => LA
| n :: LN' => set_bury (bury LA n) LN'
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

Lemma in_set_bury {A : Type} {L : list A} {LN : list nat} : forall (a : A), In a L <-> In a (set_bury L LN).
Proof.
generalize L.
induction LN as [| n LN];
intros L1 a.
- reflexivity.
- unfold set_bury;
  fold @set_bury.
  rewrite <- IHLN, <- in_bury.
  reflexivity.
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

Lemma bury_nil {A : Type} {L : list A} {n : nat} : bury L n = [] <-> L = [].
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

Lemma bury_succ {A : Type} {L : list A} {a : A} {n : nat} : bury (a :: L) (S n) = a :: (bury L n). Proof. reflexivity. Qed.

Lemma set_bury_succ {A : Type} :
    forall {LN : list nat} {L : list A} {a : A},
        set_bury (a :: L) (map S LN) = a :: (set_bury L LN).
Proof.
induction LN;
intros L b.
- reflexivity.
- unfold map;
  fold (@map _ _ S).
  unfold set_bury;
  fold @set_bury.
  rewrite bury_succ.
  apply IHLN.
Qed.

Lemma set_bury_app {A : Type} :
    forall {LN1 LN2 : list nat} {L : list A},
        set_bury L (LN1 ++ LN2) = set_bury (set_bury L LN1) LN2.
Proof.
induction LN1;
intros LN2 L.
- reflexivity.
- rewrite <- app_comm_cons.
  unfold set_bury;
  fold @set_bury.
  apply IHLN1.
Qed.

Lemma set_bury_rev_hyp {A : Type} :
    forall (L : list A),
        {LN : list nat & (forall (n : nat), In n LN -> n < (length LN)) /\ set_bury L LN = rev L}.
Proof.
induction L.
- refine (existT _ [] (conj (fun n IN => _) eq_refl)).
  inversion IN.
- destruct IHL as [LN [LT EQ]].
  refine (existT _ ((map S LN) ++ [0]) (conj (fun n IN => _) _)).
  + apply in_app_or in IN as [IN1 | IN2].
    * apply in_map_iff in IN1 as [m [EQ1 IN1]].
      subst.
      rewrite app_length, map_length.
      unfold length at 2.
      rewrite <- plus_n_Sm, <- plus_n_O.
      specialize (LT m IN1).
      lia.
    * inversion IN2 as [[]|[]].
      rewrite app_length.
      unfold length at 2.
      lia.
  + rewrite set_bury_app, set_bury_succ.
    unfold set_bury;
    fold @set_bury.
    unfold bury, rev;
    fold (@rev A).
    rewrite EQ.
    reflexivity.
Qed.

Lemma set_bury_rev {A : Type} :
    forall (L : list A),
        {LN : list nat & set_bury L LN = rev L}. 
Proof.
intros L.
refine (existT _ (projT1 (set_bury_rev_hyp L)) (proj2 (projT2 (set_bury_rev_hyp L)))).
Qed.

Lemma set_bury_swap {A : Type} :
    forall (L : list A) (a b : A),
        {LN : list nat & set_bury (a :: b :: L) LN = b :: a :: L}.
Proof.
intros L a b.
exists (projT1 (set_bury_rev (a :: b :: L)) ++ [length L] ++ (projT1 (set_bury_rev (rev (b :: a :: L))))).
repeat rewrite set_bury_app.
rewrite (projT2 (set_bury_rev (a :: b :: L))).
unfold rev;
fold (@rev A).
unfold set_bury at 2.
rewrite <- app_assoc, <- app_assoc, <- app_comm_cons, app_nil_l, <- rev_length, bury_type.
rewrite (projT2 (set_bury_rev (rev L ++ [a] ++ [b]))), app_assoc, rev_unit, rev_unit, rev_involutive.
reflexivity.
Qed.

Inductive perm {A : Type} : list A -> list A -> Type :=
| perm_nil: perm [] []
| perm_skip a L1 L2 : perm L1 L2 -> perm (a::L1) (a::L2)
| perm_swap a b L : perm (b::a::L) (a::b::L)
| perm_trans L1 L2 L3 :
    perm L1 L2 -> perm L2 L3 -> perm L1 L3.

Lemma perm_refl {A : Type} {L : list A} : perm L L.
Proof.
induction L.
apply perm_nil.
apply perm_skip, IHL.
Qed.

(*
Theorem perm_ind_prop {A : Type} :
 forall P : list A -> list A -> Prop,
   P [] [] ->
   (forall a L1 L2, perm L1 L2 -> P L1 L2 -> P (a :: L1) (a :: L2)) ->
   (forall a b L1 L2, perm L1 L2 -> P L1 L2 -> P (b :: a :: L1) (a :: b :: L2)) ->
   (forall L1 L2 L3, perm L1 L2 -> P L1 L2 -> perm L2 L3 -> P L2 L3 -> P L1 L3) ->
   forall L1 L2, perm L1 L2 -> P L1 L2.
Proof.
intros P Hnil Hskip Hswap Htrans.
induction 1.
- apply Hnil.
- apply (Hskip _ _ _ X IHX).
- apply Htrans with (a :: b :: L).
  + apply perm_swap.
  + apply Hswap.
    apply perm_refl.
    induction L.
    * apply Hnil.
    * apply (Hskip _ _ _ perm_refl IHL).
  + apply perm_refl.
  + refine (Hskip _ _ _ perm_refl (Hskip _ _ _ perm_refl _)).
    induction L.
    * apply Hnil.
    * apply (Hskip _ _ _ perm_refl IHL).
- apply (Htrans _ _ _ X1 IHX1 X2 IHX2).
Qed.


Theorem perm_ind_set {A : Type} :
 forall P : list A -> list A -> Set,
   P [] [] ->
   (forall a L1 L2, perm L1 L2 -> P L1 L2 -> P (a :: L1) (a :: L2)) ->
   (forall a b L1 L2, perm L1 L2 -> P L1 L2 -> P (b :: a :: L1) (a :: b :: L2)) ->
   (forall L1 L2 L3, perm L1 L2 -> P L1 L2 -> perm L2 L3 -> P L2 L3 -> P L1 L3) ->
   forall L1 L2, perm L1 L2 -> P L1 L2.
Proof.
intros P Hnil Hskip Hswap Htrans.
induction 1.
- apply Hnil.
- apply (Hskip _ _ _ X IHX).
- apply Htrans with (a :: b :: L).
  + apply perm_swap.
  + apply Hswap.
    apply perm_refl.
    induction L.
    * apply Hnil.
    * apply (Hskip _ _ _ perm_refl IHL).
  + apply perm_refl.
  + refine (Hskip _ _ _ perm_refl (Hskip _ _ _ perm_refl _)).
    induction L.
    * apply Hnil.
    * apply (Hskip _ _ _ perm_refl IHL).
- apply (Htrans _ _ _ X1 IHX1 X2 IHX2).
Qed.*)

Theorem perm_ind_type {A : Type} :
 forall P : list A -> list A -> Type,
   P [] [] ->
   (forall a L1 L2, perm L1 L2 -> P L1 L2 -> P (a :: L1) (a :: L2)) ->
   (forall a b L1 L2, perm L1 L2 -> P L1 L2 -> P (b :: a :: L1) (a :: b :: L2)) ->
   (forall L1 L2 L3, perm L1 L2 -> P L1 L2 -> perm L2 L3 -> P L2 L3 -> P L1 L3) ->
   forall L1 L2, perm L1 L2 -> P L1 L2.
Proof.
intros P Hnil Hskip Hswap Htrans L1 L2 perm.
induction perm.
- apply Hnil.
- apply (Hskip _ _ _ perm0 IHperm).
- apply Htrans with (a :: b :: L).
  + apply perm_swap.
  + apply Hswap.
    apply perm_refl.
    induction L.
    * apply Hnil.
    * apply (Hskip _ _ _ perm_refl IHL).
  + apply perm_refl.
  + refine (Hskip _ _ _ perm_refl (Hskip _ _ _ perm_refl _)).
    induction L.
    * apply Hnil.
    * apply (Hskip _ _ _ perm_refl IHL).
- apply (Htrans _ _ _ perm1 IHperm1 perm2 IHperm2).
Qed.

Lemma perm_sym {A : Type} : forall {L1 L2 : list A}, perm L1 L2 -> perm L2 L1.
Proof.
intros L1 L2 perm.
induction perm.
- apply perm_nil.
- apply perm_skip, IHperm.
- apply perm_swap.
- apply perm_trans with L2.
  apply IHperm2.
  apply IHperm1.
Qed.

Lemma perm_length {A : Type} {L1 L2 : list A} : perm L1 L2 -> length L1 = length L2.
Proof.
intros perm.
induction perm;
unfold length;
fold (@length A);
try rewrite IHperm;
try rewrite IHperm1;
try rewrite IHperm2;
reflexivity.
Qed.

Lemma perm_in {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} :
    perm L1 L2 ->
        forall (a : A),
            In a L1 ->
                In a L2.
Proof.
intros perm.
induction perm;
intros c IN.
- inversion IN.
- destruct IN as [EQ | IN].
  + apply (or_introl EQ).
  + apply (or_intror (IHperm _ IN)).
- destruct IN as [EQ | [EQ | IN]].
  + apply (or_intror (or_introl EQ)).
  + apply (or_introl EQ).
  + apply (or_intror (or_intror IN)).
- apply IHperm2, IHperm1, IN.
Qed.

Lemma perm_head {A : Type} {L1 L2 : list A} {a : A} : perm (L1 ++ a :: L2) (a :: L1 ++ L2).
Proof.
induction L1.
- apply perm_refl.
- apply perm_trans with (a0 :: a :: L1 ++ L2).
  apply perm_skip.
  apply IHL1.
  apply perm_swap.
Qed.

Lemma double_perm_head {A : Type} {L1 L2 L3 : list A} {a : A} : perm (L1 ++ a :: L2 ++ a :: L3) (a :: a :: L1 ++ L2 ++ L3).
Proof.
apply perm_trans with (a :: (L1 ++ L2 ++ a :: L3)).
apply (@perm_head _ L1 _ a).
apply perm_skip.
repeat rewrite app_assoc.
apply (@perm_head _ _ L3 a).
Qed.

Lemma nodup_equiv_perm {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} :
    NoDup L1 ->
        NoDup L2 ->
            (forall (a : A), In a L1 <-> In a L2) ->
                perm L1 L2.
Proof.
intros ND1.
revert L2.
induction L1;
intros L2 ND2 EQUIV.
- destruct L2.
  + apply perm_refl.
  + contradiction (proj2 (EQUIV a) (or_introl eq_refl)).
- apply NoDup_cons_iff in ND1 as [NIN1 ND1].
  specialize (IHL1 ND1).
  pose proof (in_split_dec DEC (proj1 (EQUIV _) (or_introl eq_refl))) as [L3 [L4 EQ]].
  subst.
  apply NoDup_remove in ND2 as [ND2 NIN2].
  refine (perm_trans _ _ _ (perm_skip _ _ _ (IHL1 _ ND2 (fun b => (conj (fun IN => _) (fun IN => _))))) (perm_sym perm_head)).
  + pose proof (in_app_or _ _ _ (proj1 (EQUIV b) (or_intror IN))) as [IN1 | [EQ | IN2]].
    * apply (in_or_app _ _ _ (or_introl IN1)).
    * destruct EQ.
      contradiction.
    * apply (in_or_app _ _ _ (or_intror IN2)).
  + apply in_app_or in IN as [IN | IN]. 
    * pose proof (proj2 (EQUIV b) (in_or_app _ _ _ (or_introl IN))) as [EQ | IN1].
      --  subst.
          rewrite in_app_iff in NIN2.
          contradiction (NIN2 (or_introl IN)).
      --  apply IN1.
    * pose proof (proj2 (EQUIV b) (in_or_app _ (a :: L4) _ (or_intror (or_intror IN)))) as [EQ | IN2].
      --  subst.
          rewrite in_app_iff in NIN2.
          contradiction (NIN2 (or_intror IN)).
      --  apply IN2.
Qed.

Lemma equiv_nodup_perm {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} :
    (forall (a : A), In a L1 <-> In a L2) ->
          perm (nodup DEC L1) (nodup DEC L2).
Proof.
intros EQUIV.
apply (nodup_equiv_perm DEC (NoDup_nodup _ _) (NoDup_nodup _ _)).
intros a.
repeat rewrite nodup_In.
apply EQUIV.
Qed.

Lemma perm_nodup {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} :
    perm L1 L2 ->
        perm (nodup DEC L1) (nodup DEC L2).
Proof.
intros perm.
induction perm;
unfold nodup;
fold (nodup DEC).  
- apply perm_refl.
- case (in_dec DEC a L1) as [IN1 | NIN1];
  case (in_dec DEC a L2) as [IN2 | NIN2].
  + apply IHperm.
  + contradiction (NIN2 (perm_in DEC perm0 _ IN1)).
  + contradiction (NIN1 (perm_in DEC (perm_sym perm0) _ IN2)).
  + apply perm_skip, IHperm.
- simpl.
  case (DEC a b) as [EQ1 | NE1];
  case (DEC b a) as [EQ2 | NE2];
  subst;
  try contradiction (NE1 eq_refl);
  try contradiction (NE2 eq_refl);
  try case (in_dec DEC a L) as [IN1 | NIN1];
  case (in_dec DEC b L) as [IN2 | NIN2];
  try apply perm_refl.
  apply perm_swap.
- apply (perm_trans _ _ _ IHperm1 IHperm2).
Qed.

Lemma incl_head {A : Type} {L1 L2 : list A} {a : A} :
    incl L1 L2 -> incl (a :: L1)  (a:: L2).
Proof.
intros SUB b IN.
destruct IN as [EQ | IN].
- apply (or_introl EQ).
- apply (or_intror (SUB _ IN)).
Qed.

Lemma nodup_split_perm {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 : list A} : {L2 : list A & ((perm L1 ((nodup DEC L1) ++ L2)) * (incl L2 L1))%type}.
Proof.
induction L1.
- refine (existT _ [] (pair perm_refl (incl_refl _))).
- unfold nodup;
  fold (nodup DEC).
  destruct IHL1 as [L2 [PERM SUB]].
  case (in_dec DEC a L1) as [IN | NIN].
  + refine (existT _ (a :: L2) (pair (perm_trans _ _ _ (perm_skip _ _ _ PERM) (perm_sym perm_head)) (incl_head SUB))).
  + refine (existT _ L2 (pair (perm_skip _ _ _ PERM) (fun b IN => (or_intror (SUB b IN))))).
Qed.

Lemma set_bury_eq_perm {A : Type} :
    forall {L1 L2 : list A},
        perm L1 L2 ->
            {LN : list nat & set_bury L1 LN = L2}.
Proof.
apply perm_ind_type.
- refine (existT _ [] eq_refl).
- intros a L1 L2 perm [LN EQ].
  refine (existT _ (map S LN) _).
  rewrite set_bury_succ, EQ.
  reflexivity.
- intros a b L1 L2 perm [LN1 EQ1].
  destruct (set_bury_swap L1 b a) as [LN2 EQ2].
  refine (existT _ (LN2 ++ (map S (map S LN1))) _).
  rewrite set_bury_app, EQ2, set_bury_succ, set_bury_succ, EQ1.
  reflexivity.
- intros L1 L2 L3 perm1 [LN1 EQ1] perm2 [LN2 EQ2].
  exists (LN1 ++ LN2).
  rewrite set_bury_app, EQ1, EQ2.
  reflexivity.
Defined.

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

Lemma no_dup_dec_cases {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) (L : list A) : {NoDup L} + {~ NoDup L}.
Proof.
induction L.
- left.
  apply NoDup_nil.
- destruct IHL as [ND | D].
  destruct (in_dec DEC a L) as [IN | NIN].
  + right.
    intros FAL.
    apply NoDup_cons_iff in FAL as [FAL _].
    apply FAL, IN.
  + left.
    apply (NoDup_cons _ NIN ND).
  + right.
    intros FAL.
    apply NoDup_cons_iff in FAL as [_ FAL].
    apply D, FAL.
Qed.

Lemma has_dups_split {A : Type} {L : list A} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    ~ NoDup L ->
        {a : A & {L1 : list A & {L2 : list A & {L3 : list A & L = L1 ++ a :: L2 ++ a :: L3}}}}.
Proof.
intros D.
induction L.
- contradiction D.
  apply NoDup_nil.
- destruct (in_dec DEC a L) as [IN | NIN].
  + destruct (in_split_dec DEC IN) as [L1 [L2 EQ]].
    subst.
    refine (existT _ a (existT _ [] (existT _ L1 (existT _ L2 eq_refl)))).
  + rewrite NoDup_cons_iff in D.
    assert (~ NoDup L) as D'.
    { intros FAL.
      apply D.
      apply (conj NIN FAL). }
    destruct (IHL D') as [b [L1 [L2 [L3 EQ]]]].
    subst.
    refine (existT _ b (existT _ (a :: L1) (existT _ L2 (existT _ L3 eq_refl)))).
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

Fixpoint sublist {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) (L1 L2 : list A) : bool :=
match L1 with
| [] => true
| a1 :: L1' => match L2 with
  | [] => false
  | a2 :: L2' => if DEC a1 a2 then sublist DEC L1' L2' else sublist DEC L1 L2'
  end
end.

Fixpoint sublist_filter {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) (L1 L2 : list A) : list bool :=
match L1, L2 with
| [], _ => repeat false (length L2)
| a1 :: L1', a2 :: L2' => (if DEC a1 a2 then true :: sublist_filter DEC L1' L2' else false :: sublist_filter DEC L1 L2') 
| _ , _ => []
end.

(*
Inductive sublist_p {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) : list A -> list A -> Prop :=
| sublist_p_nil : forall L : list A, sublist_p DEC [] L
| sublist_p_head : forall (L1 L2 : list A) (a : A), sublist_p DEC L1 L2 -> sublist_p DEC (a :: L1) (a :: L2)
| sublist_p_add : forall (L1 L2 L3 : list A), L2 <> [] -> sublist_p DEC L1 L3 -> sublist_p DEC L1 (L2 ++ L3).
*)

(*
Fixpoint list_filter {A : Type} (LA : list A) (LB : list bool) : list A :=
match LA with
| [] => []
| a :: LA' => match LB with
    | [] => LA
    | false :: LB' => list_filter LA' LB'
    | true :: LB' => a :: list_filter LA' LB'
    end
end.
*)

Fixpoint list_filter {A : Type} (LA : list A) (LB : list bool) : list A :=
match LB with
| [] => []
| b :: LB' => match LA with
    | [] => []
    | a :: LA' => match b with 
        | true => a :: list_filter LA' LB'
        | false => list_filter LA' LB'
        end
    end
end.

Lemma filter_false_nil {A : Type} {L : list A} : [] = list_filter L (repeat false (length L)).
Proof.
induction L.
reflexivity.
rewrite IHL.
reflexivity.
Qed.

Lemma sublist_nil {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} :
    sublist DEC [] L = true.
Proof. destruct L; reflexivity. Qed.

Lemma sublist_cons {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} (a : A) :
    sublist DEC L1 L2 = true ->
        sublist DEC (a :: L1) (a :: L2) = true.
Proof.
revert L2.
induction L1;
intros L2 SL;
unfold sublist;
fold @sublist;
case (DEC a a) as [_ | FAL];
try contradiction (FAL eq_refl);
apply SL.
Qed.

(*
Lemma sublist_cons_inv {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} {a : A} :
    sublist DEC (a :: L1) (a :: L2) = true ->
        sublist DEC L1 L2 = true.
Proof.
revert L2.
induction L1;
intros L2 SL;
unfold sublist in *;
fold @sublist in *;
case (DEC a a) as [_ | FAL];
try contradiction (FAL eq_refl).
destruct L2; reflexivity.
apply SL.
Qed.
*)

Lemma sublist_refl {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} : sublist DEC L L = true.
Proof. induction L. reflexivity. unfold sublist. fold @sublist. case (DEC a a) as [_ | FAL]. apply IHL. contradiction (FAL eq_refl). Qed.

Lemma sublist_cons_type {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} {a : A} :
    sublist DEC L1 (a :: L2) = true ->
        {L3 : list A & {L1 = a :: L3 /\ sublist DEC L3 L2 = true} + {sublist DEC L1 L2 = true}}.
Proof.
revert L2.
induction L1;
intros L2 SL.
refine (existT _ [] (right (sublist_nil _))).
unfold sublist in SL;
fold @sublist in SL.
case (DEC a0 a) as [EQ | _].
subst.
refine (existT _ L1 (left (conj eq_refl SL))).
refine (existT _ L1 (right SL)).
Qed.

Lemma sublist_cons_inv_front {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} {a : A} :
    sublist DEC (a :: L1) L2 = true ->
        sublist DEC L1 L2 = true.
Proof.
revert L1 a.
induction L2;
intros L1 b SL.
inversion SL.
unfold sublist in SL;
fold @sublist in SL.
case (DEC b a) as [EQ | NE].
subst.
- destruct L1.
  reflexivity.
  pose proof (IHL2 _ _ SL) as SL'.
  unfold sublist;
  fold @sublist.
  rewrite SL,SL'.
  case (DEC a0 a) as [_ | _];
  reflexivity.
- pose proof (IHL2 _ _ SL) as SL'.
  destruct L1.
  reflexivity.
  pose proof (IHL2 _ _ SL') as SL''.
  unfold sublist;
  fold @sublist.
  rewrite SL', SL''.
  case (DEC a0 a) as [_ | _];
  reflexivity.
Qed.

Lemma sublist_cons_inv_back {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 : list A} {a : A} :
    sublist DEC L1 L2 = true ->
        sublist DEC L1 (a :: L2) = true.
Proof.
revert L2 a.
induction L1;
intros L2 b SL.
reflexivity.
unfold sublist;
fold @sublist.
rewrite SL.
rewrite (sublist_cons_inv_front DEC SL).
case (DEC a b) as [_ | _];
reflexivity.
Qed.

Lemma sublist_trans {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 L3 : list A} :
    sublist DEC L1 L2 = true ->
        sublist DEC L2 L3 = true ->
            sublist DEC L1 L3 = true.
Proof.
revert L1 L2;
induction L3;
intros L1 L2 SL1 SL2.
- destruct L2.
  destruct L1.
  reflexivity.
  inversion SL1.
  inversion SL2.
- destruct (sublist_cons_type DEC SL2) as [L4 [[EQ SL3] | SL3]].
  subst.
  destruct (sublist_cons_type DEC SL1) as [L2 [[EQ SL4] | SL4]].
  subst.
  apply sublist_cons, (IHL3 _ _ SL4 SL3).
  apply sublist_cons_inv_back, (IHL3 _ _ SL4 SL3).
  apply sublist_cons_inv_back, (IHL3 _ _ SL1 SL3).
Qed.

Lemma sublist_app  {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L1 L2 L3 : list A} :
    sublist DEC L1 L2 = true ->
        sublist DEC L1 (L3 ++ L2) = true.
Proof.
revert L1 L2.
induction L3;
intros L1 L2 SL.
rewrite app_nil_l.
apply SL.
apply sublist_cons_inv_back, IHL3, SL.
Qed.

Lemma sublist_filter_sublist {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) (L1 L2 : list A) :
    sublist DEC L1 L2 = true ->
        L1 = list_filter L2 (sublist_filter DEC L1 L2).
Proof.
revert L1.
induction L2;
intros L1 SL;
destruct L1.
reflexivity.
inversion SL.
unfold sublist_filter.
apply filter_false_nil.
unfold sublist in SL;
fold @sublist in SL.
unfold sublist_filter;
fold @sublist_filter.
case (DEC a0 a) as [EQ | NE];
subst;
unfold list_filter;
fold @list_filter.
rewrite <- (IHL2 _ SL).
reflexivity.
apply (IHL2 _ SL).
Qed.

Lemma precedence_cons {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} {a b c : A} : 
    a <> b ->
        precedence DEC (a :: L) b c = true -> precedence DEC L b c = true.
Proof.
intros NE Prec.
unfold precedence in Prec;
fold @precedence in Prec.
case (DEC a b) as [FAL | _].
contradiction.
case (DEC a c) as [_ | _].
inversion Prec.
apply Prec.
Qed.

Lemma precedence_is_in {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} {a b : A} :
      precedence DEC L a b = true ->
          (In a L /\ In b L).
Proof.
intros Prec.
induction L;
unfold precedence in Prec;
fold @precedence in Prec.
inversion Prec.
case (DEC a0 a) as [EQ | NE].
subst.
case (in_dec DEC b L) as [IN | NIN].
apply (conj (or_introl eq_refl) (or_intror IN)).
inversion Prec.
case (DEC a0 b) as [EQ | NE'].
inversion Prec.
apply (conj (or_intror (proj1 (IHL Prec))) (or_intror (proj2 (IHL Prec)))).
Qed.

Lemma in_tail_prec {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} {a b : A} :
    In b L -> precedence DEC (a :: L) a b = true.
Proof.
intros IN.
unfold precedence;
fold @precedence.
case (DEC a a) as [[] | FAL].
case (in_dec DEC b L) as [_ | FAL].
reflexivity.
contradict (FAL IN).
contradict (FAL eq_refl).
Qed.

Lemma NoDup_precedence_asym {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} {a b : A} :
      NoDup L ->
          precedence DEC L a b = true ->
            precedence DEC L b a = false.
Proof.
intros ND Prec.
induction L as [ | a1 L].
- inversion Prec.
- unfold precedence in *;
  fold @precedence in *.
  case (DEC a1 a) as [EQ | NE1].
  + subst.
    case (in_dec DEC b L) as [IN1 | _].
    * case (DEC a b) as [EQ | NE1].
      subst.
      inversion ND.
      contradiction (H1 IN1).
      reflexivity.
    * inversion Prec.
  + case (DEC a1 b) as [_ | NE2].
    inversion Prec.
    refine (IHL _ Prec).
    inversion ND.
    apply H2.
Qed.

Lemma precedence_cases {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) {L : list A} {a b : A} :
    In a L ->
        In b L ->
            {precedence DEC L a b = true} +
                {precedence DEC L b a = true} +
                    {a = b}.
Proof.
induction L;
intros INa INb.
inversion INa.
unfold precedence;
fold @precedence.
case (DEC a0 a) as [EQ1 | NE1];
case (DEC a0 b) as [EQ2 | NE2];
subst.
- right.
  reflexivity.
- left.
  left.
  destruct INb as [FAL | INb].
  contradiction (NE2 FAL).
  case (in_dec DEC b L) as [_ | FAL].
  reflexivity.
  contradiction (FAL INb).
- left.
  right.
  destruct INa as [FAL | INa].
  contradiction (NE1 FAL).
  case (in_dec DEC a L) as [_ | FAL].
  reflexivity.
  contradiction (FAL INa).
- destruct IHL as [[Prec1 | Prec2] | EQ].
  destruct INa as [FAL | INa].
  contradiction (NE1 FAL).
  apply INa.
  destruct INb as [FAL | INb].
  contradiction (NE2 FAL).
  apply INb.
  + left.
    left.
    apply Prec1.
  + left.
    right.
    apply Prec2.
  + right.
    apply EQ.
Qed.

Lemma precedence_eq_sublist {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L1 L2 : list A),
        incl L1 L2 ->
            NoDup L1 ->
                NoDup L2 ->
                    (forall (a b : A), precedence DEC L1 a b = true -> precedence DEC L2 a b = true) ->
                        sublist DEC L1 L2 = true.
Proof.
intros L1 L2;
revert L1.
induction L2;
intros L1 SUB ND1 ND2 Prec;
destruct L1.
reflexivity.
contradiction (SUB _ (or_introl eq_refl)).
reflexivity.
unfold sublist;
fold @sublist.
apply NoDup_cons_iff in ND1 as [NIN1 ND1].
apply NoDup_cons_iff in ND2 as [NIN2 ND2].
case (DEC a0 a) as [EQ | NE1].
- subst.
  assert (forall a b : A, precedence DEC L1 a b = true -> precedence DEC L2 a b = true) as PREC'.
  { intros a1 b1 Prec1.
    specialize (Prec a1 b1).
    case (DEC a a1) as [EQ | NE].
    subst.
    contradiction (NIN1 (proj1 (precedence_is_in DEC Prec1))).
    apply (precedence_cons DEC NE), Prec.
    unfold precedence;
    fold @precedence.
    rewrite Prec1.
    case (DEC a a1) as [EQ | _].
    contradiction (NE EQ).
    case (DEC a b1) as [EQ | _].
    subst.
    contradiction (NIN1 (proj2 (precedence_is_in DEC Prec1))).
    reflexivity. }
  refine (IHL2 _ (fun b IN => _) ND1 ND2 PREC').
  destruct (SUB _ (or_intror IN)) as [FAL | IN'].
  subst.
  contradict (NIN1 IN).
  apply IN'.
- assert (precedence DEC (a :: L2) a a0 = true) as PR1.
  { apply in_tail_prec.
    destruct (SUB _ (or_introl eq_refl)) as [FAL | IN'].
    subst.
    contradict (NE1 eq_refl).
    apply IN'. }
  assert (~ In a L1) as NIN.
  { intros IN.
    pose proof (Prec _ _ (in_tail_prec DEC IN)) as FAL.
    rewrite (NoDup_precedence_asym _ (proj2 (NoDup_cons_iff _ _ ) (conj NIN2 ND2)) PR1) in FAL.
    inversion FAL. }
  assert (forall a b : A, precedence DEC (a0 :: L1) a b = true -> precedence DEC L2 a b = true) as PREC'.
  { intros a1 b1 Prec1.
    specialize (Prec a1 b1).
    unfold precedence in *;
    fold @precedence in *.
    case (DEC a0 a1) as [EQ | NE2].
    + subst.
      case (in_dec DEC b1 L1) as [IN | _].
      * specialize (Prec Prec1).
        case (DEC a a1) as [EQ | _].
        contradiction (NE1 (eq_sym EQ)).
        case (DEC a b1) as [_ | _].
        inversion Prec.
        apply Prec.
      * inversion Prec1.
    + case (DEC a0 b1) as [EQ | NE3].
      inversion Prec1.
      specialize (Prec Prec1).
      case (DEC a a1) as [EQ | NE4].
      * subst.
        contradiction (NIN (proj1 (precedence_is_in DEC Prec1))).
      * case (DEC a b1) as [EQ | NE5].
        inversion Prec.
        apply Prec. }
refine (IHL2 _ _ (proj2 (NoDup_cons_iff _ _) (conj NIN1 ND1)) ND2 PREC').
intros b IN.
destruct (SUB _ IN) as [EQ | IN'].
subst.
destruct IN as [EQ | IN].
contradiction (NE1 EQ).
contradict (NIN IN).
apply IN'.
Qed.

Lemma in_filter_in {A : Type} {L : list A} {a : A} :
    forall (LB : list bool),
        In a (list_filter L LB) -> In a L.
Proof.
induction L;
intros LB IN;
destruct LB;
try inversion IN.
destruct b.
destruct IN as [EQ | IN].
apply (or_introl EQ).
apply (or_intror (IHL _ IN)).
apply (or_intror (IHL _ IN)).
Qed.

Lemma NoDup_filter_unique {A : Type} {L : list A} :
    NoDup L ->
        forall (L1 L2 : list bool),
            length L = length L1 ->
                length L = length L2 ->
                    list_filter L L1 = list_filter L L2 <-> L1 = L2.
Proof.
induction L;
intros ND L1 L2 EQ1 EQ2;
split;
intros EQ.
1,2 : destruct L1;
      destruct L2;
      inversion EQ1;
      inversion EQ2;
      reflexivity.
- apply NoDup_cons_iff in ND as [NIN ND].
  destruct L1;
  inversion EQ1 as [EQ1'].
  destruct L2;
  inversion EQ2 as [EQ2'].
  unfold list_filter in EQ;
  fold @list_filter in EQ.
  case b eqn:bb;
  case b0 eqn:b0b.
  inversion EQ as [EQ'].
  rewrite (proj1 (IHL ND _ _ EQ1' EQ2') EQ').
  reflexivity.
  contradict NIN.
  apply (in_filter_in L2).
  rewrite <- EQ.
  apply (or_introl eq_refl).
  contradict NIN.
  apply (in_filter_in L1).
  rewrite EQ.
  apply (or_introl eq_refl).
  inversion EQ as [EQ'].
  rewrite (proj1 (IHL ND _ _ EQ1' EQ2') EQ').
  reflexivity.
- destruct L1;
  inversion EQ1 as [EQ1'].
  destruct L2;
  inversion EQ2 as [EQ2'].
  unfold list_filter;
  fold @list_filter.
  case b eqn:bb;
  case b0 eqn:b0b;
  inversion EQ as [EQ'];
  reflexivity.
Qed.

Lemma filter_nil {A : Type} {L : list A} : list_filter L [] = [].
Proof. induction L; reflexivity. Qed.

Lemma sublist_cons_split {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L1 L2 : list A) (a : A),
        sublist DEC (a :: L1) L2 = true ->
            {L3 : list A & {L4 : list A & sublist DEC L1 L4 = true /\ L2 = L3 ++ a :: L4 /\ ~ In a L3}}.
Proof.
intros L1 L2 b SL.
induction L2.
inversion SL.
unfold sublist in SL;
fold @sublist in SL.
case (DEC b a) as [EQ | NE].
subst.
refine (existT _ [] (existT _ L2 (conj SL (conj (app_nil_l _) (fun FAL => FAL))))).
destruct (IHL2 SL) as [L3 [L4 [SL' [EQ NIN]]]].
refine (existT _ (a :: L3) (existT _ L4 (conj SL' (conj _ (fun FAL => _))))).
rewrite EQ, app_comm_cons.
reflexivity.
destruct FAL as [EQ' | IN].
contradiction (NE (eq_sym EQ')).
contradiction (NIN IN).
Qed.

Lemma sublist_cons_split_filter {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L1 L2 L3 : list A) (a : A),
        sublist DEC (a :: L1) (L2 ++ a :: L3) = true ->
            ~ In a L2 ->
                (sublist_filter DEC (a :: L1) (L2 ++ a :: L3) = (repeat false (length L2)) ++ true :: (sublist_filter DEC L1 L3)).
Proof.
intros L1 L2 L3 b SL NIN.
induction L2.
- rewrite !app_nil_l in *.
  unfold sublist_filter;
  fold @sublist_filter.
  case (DEC b b) as [_ | FAL].
  reflexivity.
  contradiction (FAL eq_refl).
- rewrite <- !app_comm_cons in *.
  unfold sublist in SL;
  fold @sublist in SL.
  unfold length;
  fold (@length A).
  unfold repeat;
  fold (@repeat bool).
  rewrite <- app_comm_cons.
  unfold sublist_filter;
  fold @sublist_filter.
  case (DEC b a) as [EQ | _].
  subst.
  contradiction (NIN (or_introl eq_refl)).
  rewrite (IHL2 SL).
  reflexivity.
  intros FAL.
  apply NIN, or_intror, FAL.
Qed.

Lemma list_filter_app {A : Type} :
    forall (L1 L2 : list A) (LB : list bool),
        length (L1 ++ L2) = length LB ->
            list_filter (L1 ++ L2) LB = list_filter L1 (firstn (length L1) LB) ++ list_filter L2 (skipn (length L1) LB).
Proof.
induction L1;
intros L2 LB EQ.
rewrite !app_nil_l in *.
reflexivity.
destruct LB.
inversion EQ.
rewrite <- !app_comm_cons.
unfold list_filter;
fold @list_filter.
unfold length;
fold (@length A).
unfold firstn;
fold (@firstn bool).
unfold skipn;
fold (@skipn bool).
destruct b;
rewrite IHL1;
rewrite <- app_comm_cons in EQ;
inversion EQ as [EQ'];
reflexivity.
Qed.

Lemma sublist_filter_length {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L1 L2 : list A),
        sublist DEC L1 L2 = true ->
            length (sublist_filter DEC L1 L2) = length L2.
Proof.
intros L1 L2.
revert L1.
induction L2;
intros L1 SL.
destruct L1.
reflexivity.
inversion SL.
destruct L1.
unfold sublist_filter.
apply repeat_length.
unfold sublist_filter;
fold @sublist_filter.
unfold sublist in SL;
fold @sublist in SL.
case (DEC a0 a) as [_ | _];
unfold length;
fold (@length bool) (@length A);
apply eq_S, IHL2, SL.
Qed.

Fixpoint count_true (L : list bool) : nat :=
match L with
| [] => 0
| false :: L' => count_true L'
| true :: L' => S (count_true L')
end.

Lemma count_true_repeat_false_O {n : nat} : count_true (repeat false n) = 0.
Proof. induction n. reflexivity. apply IHn. Qed.

Lemma sublist_count_length {A : Type} : 
    forall (L1 : list A) (L2 : list bool),
        length L1 = length L2 ->
            length (list_filter L1 L2) = count_true L2.
Proof.
induction L1;
induction L2;
intros LEN;
inversion LEN as [LEN'].
- reflexivity.
- unfold list_filter;
  fold @list_filter.
  destruct a0.
  + apply eq_S.
    apply (IHL1 _ LEN').
  + apply (IHL1 _ LEN').
Qed.

Lemma sublist_filter_true {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L1 L2 : list A),
        sublist DEC L1 L2 = true ->
            count_true (sublist_filter DEC L1 L2) = length L1.
Proof.
intros L1 L2.
revert L1.
induction L2;
intros L1 SL.
destruct L1.
reflexivity.
inversion SL.
destruct L1;
unfold sublist_filter;
fold @sublist_filter.
apply count_true_repeat_false_O.
unfold sublist in SL;
fold @sublist in SL.
case (DEC a0 a) as [_ | _];
unfold length, count_true;
fold (@length bool) (@length A) count_true.
apply eq_S, IHL2, SL.
apply IHL2, SL.
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

Lemma nodup_double_cons {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall {L : list A} {a : A},
        nodup DEC (a :: a :: L) = nodup DEC (a :: L).
Proof.
intros L a.
induction L;
simpl;
destruct (DEC a a) as [EQ | NE];
try reflexivity;
contradiction (NE eq_refl).
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