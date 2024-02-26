From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.

Require Import List.
Require Import Nat.
Require Import Lia.
Require Import Bool.
Import ListNotations.

Definition subst_ind : Type := list bool.

Lemma subst_eq_dec :
    forall (S1 S2 : subst_ind),
        {S1 = S2} + {S1 <> S2}.
Proof.
apply list_eq_dec, Bool.bool_dec.
Qed.

Definition non_target (gamma : list formula) : subst_ind := repeat false (length gamma).

Definition target (gamma : list formula) : subst_ind := repeat true (length gamma).

(*
Fixpoint form_equiv (A1 A2 : formula) (depth : nat) : bool :=
match A1, A2 with
| fal, fal => true
| equ v1 v2, equ v3 v4 => (nat_eqb v1 v3 || (nat_leb depth v1 && nat_leb depth v3)) && (nat_eqb v2 v4 || (nat_leb depth v2 && nat_leb depth v4))
| imp B1 C1, imp B2 C2 => form_equiv B1 B2 depth && form_equiv C1 C2 depth
| univ B1, univ B2 => form_equiv B1 B2 (S depth)
| bnd lambda1 kappa1 B1, bnd lambda2 kappa2 B2 => nat_eqb lambda1 lambda2 && nat_eqb kappa1 kappa2 && form_equiv B1 B2 depth
| prd vec1 pn1 _, prd vec2 pn2 _ => prd_eqb pn1 pn2
| _, _ => false
end.
*)

(*
Fixpoint form_equiv (A1 A2 : formula) (depth : nat) : bool :=
match A1, A2 with
| fal, fal => true
| equ v1 v2, equ v3 v4 =>
    if nat_eqb v1 v2
    then nat_eqb v3 v4
    else (nat_eqb v1 v3 ||
            (nat_leb depth v1 && nat_leb depth v3)) &&
          (nat_eqb v2 v4 ||
              (nat_leb depth v2 && nat_leb depth v4))
| imp B1 C1, imp B2 C2 => form_equiv B1 B2 depth && form_equiv C1 C2 depth
| univ B1, univ B2 => form_equiv B1 B2 (S depth)
| bnd lambda1 kappa1 B1, bnd lambda2 kappa2 B2 => nat_eqb lambda1 lambda2 && nat_eqb kappa1 kappa2 && form_equiv B1 B2 depth
| prd vec1 pn1 _, prd vec2 pn2 _ => prd_eqb pn1 pn2
| _, _ => false
end.
*)

(*
Lemma form_equiv_shift_subst_aux :
    forall (phi : formula) (v1 v2 : ivar) (d : nat),
        d <= v1 ->
        form_equiv phi (shift_substitution phi v1 v2) d = true.
Proof.
induction phi;
intros v1 v2 d LT;
unfold shift_substitution;
fold shift_substitution;
unfold form_equiv;
fold form_equiv;
try rewrite !nat_eqb_refl;
try rewrite prd_eqb_refl;
try rewrite IHphi;
try rewrite IHphi1;
try rewrite IHphi2;
try reflexivity;
unfold form_depth in *;
fold form_depth in *;
try lia.
case (nat_eqb i v1) eqn:EQ1;
case (nat_eqb i0 v1) eqn:EQ2;
try apply nat_eqb_eq in EQ1;
try apply nat_eqb_eq in EQ2;
subst;
try rewrite !nat_eqb_refl;
try rewrite nat_eqb_symm in EQ2;
try rewrite EQ2;
try rewrite EQ1;
try rewrite nat_eqb_symm in EQ1;
try rewrite EQ1;
assert (d <= v1 + v2) as LT';
try lia;
try rewrite (Compare_dec.leb_correct _ _ LT);
try rewrite (Compare_dec.leb_correct _ _ LT');
try rewrite !nat_eqb_refl;
try rewrite !orb_true_l;
try rewrite !orb_true_r;
unfold "&&";
try reflexivity.
case (nat_eqb i i0); reflexivity.
Qed.
*)

(*
Lemma form_equiv_shift_subst :
    forall (phi : formula) (v1 v2 : ivar),
        form_equiv phi (shift_substitution phi v1 v2) 0 = true.
Proof. intros phi v1 v2. apply form_equiv_shift_subst_aux. apply le_0_n. Qed.
*)

(*
Lemma free_sub_means_equiv :
    forall (phi : formula) (v1 v2 : ivar) (d : nat),
        (form_depth phi) + d < v1 ->
            (form_depth phi) + d < v2 ->
                form_equiv (substitution phi v1 v2) phi d = true.
Proof.
induction phi;
intros v1 v2 d LT1 LT2;
unfold substitution;
fold substitution;
unfold form_depth;
fold form_depth;
unfold form_equiv;
fold form_equiv;
try rewrite !nat_eqb_refl;
try rewrite prd_eqb_refl;
try rewrite IHphi;
try rewrite IHphi1;
try rewrite IHphi2;
try reflexivity;
unfold form_depth in *;
fold form_depth in *;
try lia.
case (nat_eqb i v1) eqn:EQ1;
case (nat_eqb i0 v1) eqn:EQ2;
try apply nat_eqb_eq in EQ1;
try apply nat_eqb_eq in EQ2;
subst;
unfold form_equiv;
fold form_equiv;
try rewrite !nat_eqb_refl;
try rewrite plus_O_n in *;
try rewrite (nat_lt_ltb _ _ LT1);
try rewrite (nat_lt_ltb _ _ LT2);
try rewrite !orb_true_l;
try rewrite !orb_true_r;
try rewrite !andb_true_r;
try reflexivity;
rewrite !Compare_dec.leb_correct;
lia.
Qed.
*)

(*
Lemma form_equiv_succ_form :
    forall (phi : formula) (d v1 v2 : nat),
        d < (S v1) -> d < (S v2)  -> 
        form_equiv (substitution_depth phi 0 (S v1) (S v2)) phi d = true ->
            form_equiv (substitution_depth phi 1 (S v1) (S v2)) phi (S d) = true.
Proof.
induction phi;
intros d v1 v2 LT1 LT2 EQ;
unfold substitution_depth in *;
fold substitution_depth in *;
unfold form_equiv in *;
fold form_equiv in *;
try reflexivity.
- case (nat_eqb i (S v1)) eqn:EQ1;
  case (nat_eqb i0 (S v1)) eqn:EQ2;
  try apply nat_eqb_eq in EQ1;
  try apply nat_eqb_eq in EQ2;
  subst;
  unfold form_equiv in *;
  fold form_equiv in *;
  try rewrite !nat_eqb_refl;
  try rewrite !orb_true_l;
  try rewrite andb_true_l;
  try rewrite andb_true_r;
  try rewrite !Compare_dec.leb_correct;
  try lia.
- apply and_bool_prop in EQ as [EQ1 EQ2].
  rewrite IHphi1, IHphi2;
  try assumption;
  try reflexivity.
- unfold nat_ltb, Nat.leb in EQ.
- repeat apply and_bool_prop in EQ as [EQ ?EQ].
  rewrite !nat_eqb_refl, !andb_true_l.
  apply IHphi;
  assumption.
- apply EQ.
Admitted.

Lemma free_sub_means_equiv_other :
    forall (phi : formula) (v1 v2 : ivar) (d2 : nat),
        d2 < v1 ->
          d2 < v2 ->
            form_equiv (substitution_depth phi 0 v1 v2) phi d2 = true.
Proof.
induction phi;
intros v1 v2 d LT1 LT2;
unfold substitution_depth;
fold substitution_depth;
unfold form_depth;
fold form_depth;
unfold form_equiv;
fold form_equiv;
try rewrite !nat_eqb_refl;
try rewrite prd_eqb_refl;
try rewrite IHphi;
try rewrite IHphi1;
try rewrite IHphi2;
try reflexivity;
unfold form_depth in *;
fold form_depth in *;
try lia.
case (nat_eqb i v1) eqn:EQ1;
case (nat_eqb i0 v1) eqn:EQ2;
try apply nat_eqb_eq in EQ1;
try apply nat_eqb_eq in EQ2;
subst;
unfold form_equiv;
fold form_equiv;
try rewrite !nat_eqb_refl;
try rewrite plus_O_n in *;
try rewrite (nat_lt_ltb _ _ LT1);
try rewrite (nat_lt_ltb _ _ LT2);
try rewrite !orb_true_l;
try rewrite !orb_true_r;
try reflexivity;
try rewrite !Compare_dec.leb_correct;
try lia.

destruct v1.
inversion LT1.
destruct v2.
inversion LT2.
unfold nat_ltb, Nat.leb.
unfold form_equiv;
fold form_equiv.
pose proof (IHphi (S v1) (S v2) d LT1 LT2).
apply form_equiv_succ_form in H.
apply H.
all : lia.
Qed.
*)

(*
Lemma form_equiv_sym :
    forall (phi1 phi2 : formula) (d : nat),
        form_equiv phi1 phi2 d = form_equiv phi2 phi1 d.
Proof.
induction phi1;
destruct phi2;
intros d;
unfold form_equiv;
fold form_equiv;
try rewrite (nat_eqb_symm i i1);
try rewrite (nat_eqb_symm i0 i2);
try rewrite (nat_eqb_symm o o1);
try rewrite (nat_eqb_symm o0 o2);
try rewrite (andb_comm (nat_leb _ i1));
try rewrite (andb_comm (nat_leb _ i2));
try rewrite prd_eqb_sym;
try rewrite IHphi1;
try rewrite IHphi1_1, IHphi1_2;
try reflexivity.
admit.
Admitted.
*)

(*
Lemma form_equiv_trans :
    forall (phi1 phi2 phi3 : formula) (d : nat),
        form_equiv phi1 phi2 d = true ->
            form_equiv phi2 phi3 d = true ->
                form_equiv phi1 phi3 d = true.
Proof.
induction phi1;
destruct phi2, phi3;
intros d EQ1 EQ2;
try reflexivity;
inversion EQ1 as [EQ1'];
try rewrite EQ1';
inversion EQ2 as [EQ2'];
try rewrite EQ2';
unfold form_equiv;
fold form_equiv;
try case (nat_eqb i i0) eqn:EQB1;
try rewrite EQ1' in EQ2';
try apply and_bool_prop in EQ1' as [EQ3 EQ4];
try apply and_bool_prop in EQ2' as [EQ5 EQ6].
- apply EQ2'.
- case (nat_eqb i1 i2) eqn:EQB2.
  apply nat_eqb_eq in EQB2,EQ2'.
  subst.
  apply or_bool_prop in EQ3 as [EQ3 | LT1];
  apply or_bool_prop in EQ4 as [EQ4 | LT3];
  try apply nat_eqb_eq in EQ3;
  try apply nat_eqb_eq in EQ4;
  subst;
  try apply and_bool_prop in LT1 as [LT1 LT2];
  try apply and_bool_prop in LT3 as [LT3 LT4];
  try rewrite nat_eqb_refl in EQB1;
  try inversion EQB1;
  try rewrite LT1;
  try rewrite LT2;
  try rewrite LT3;
  try rewrite LT4.
  try rewrite orb_true_l.
  admit.
  admit.
  
  
  apply or_bool_prop in EQ3 as [EQ3 | LT1];
  apply or_bool_prop in EQ4 as [EQ4 | LT3];
  apply or_bool_prop in EQ5 as [EQ5 | LT5];
  apply or_bool_prop in EQ6 as [EQ6 | LT7];
  try apply nat_eqb_eq in EQ3;
  try apply nat_eqb_eq in EQ4;
  try apply nat_eqb_eq in EQ5;
  try apply nat_eqb_eq in EQ6;
  try apply and_bool_prop in LT1 as [LT1 LT2];
  try apply and_bool_prop in LT3 as [LT3 LT4];
  try apply and_bool_prop in LT5 as [LT5 LT6];
  try apply and_bool_prop in LT7 as [LT7 LT8];
  subst;
  try rewrite !nat_eqb_refl;
  try rewrite LT1;
  try rewrite LT2;
  try rewrite LT3;
  try rewrite LT4;
  try rewrite LT5;
  try rewrite LT6;
  try rewrite LT7;
  try rewrite LT8;
  try rewrite !orb_true_l;
  try rewrite !orb_true_r;
  try reflexivity.
- rewrite (IHphi1_1 _ _ _ EQ3 EQ5), (IHphi1_2 _ _ _ EQ4 EQ6).
  reflexivity.
- apply (IHphi1 _ _ _ EQ1' EQ2').
- apply and_bool_prop in EQ3 as [EQ3 EQ7].
  apply and_bool_prop in EQ5 as [EQ5 EQ8].
  apply nat_eqb_eq in EQ3,EQ5,EQ7,EQ8.
  subst.
  rewrite !nat_eqb_refl.
  apply (IHphi1 _ _ _ EQ4 EQ6).
- pose proof (prd_eqb_type _ _ EQ1') as EQN1.
  pose proof (prd_eqb_type _ _ EQ2') as EQN2.
  apply nat_eqb_eq in EQN1,EQN2.
  subst.
  apply prd_eqb_eq in EQ1',EQ2'.
  subst.
  apply prd_eqb_refl.
Qed.
*)

Definition formula_sub (phi A1 A2 : formula) (b : bool) : formula :=
match form_eqb phi A1, b with
| true, true => A2
| _, _ => phi
end.

Fixpoint batch_sub_fit (gamma : list formula) (A1 A2 : formula) (S : subst_ind) : list formula :=
match gamma, S with
| phi :: gamma', b :: S' => (formula_sub phi A1 A2 b) :: batch_sub_fit gamma' A1 A2 S'
| _ , _ => gamma
end.

Definition batch_sub (gamma : list formula) (A1 A2 : formula) (S : subst_ind) : list formula :=
match nat_eqb (length gamma) (length S) with
| false => gamma
| true => batch_sub_fit gamma A1 A2 S
end.

Lemma formula_sub_false {phi A1 A2 : formula} :
    formula_sub phi A1 A2 false = phi.
Proof. unfold formula_sub. case (form_eqb phi A1); reflexivity. Qed.

Lemma batch_sub_nil :
    forall (gamma : list formula) (A1 A2 : formula),
        batch_sub_fit gamma A1 A2 [] = gamma.
Proof. induction gamma; reflexivity. Qed.

Lemma batch_sub_fit_true :
    forall {gamma : list formula} {A1 A2 : formula} {S : subst_ind},
        nat_eqb (length gamma) (length S) = true ->
            batch_sub_fit gamma A1 A2 S = batch_sub gamma A1 A2 S.
Proof. intros gamma A1 A2 S EQ. unfold batch_sub. rewrite EQ. reflexivity. Qed.

Lemma batch_sub_single :
    forall (phi : formula) (A1 A2 : formula) (b : bool),
            batch_sub [phi] A1 A2 [b] = [formula_sub phi A1 A2 b].
Proof. reflexivity. Qed.

Lemma batch_sub_false_head :
    forall (phi : formula) (gamma : list formula) (A1 A2 : formula) (S : subst_ind),
            batch_sub (phi :: gamma) A1 A2 (false :: S) = phi :: batch_sub gamma A1 A2 S.
Proof.
intros phi gamma A1 A2 S.
unfold batch_sub, length, nat_eqb.
fold nat_eqb (@length formula) (@length bool).
case (nat_eqb (length gamma) (length S));
unfold batch_sub_fit;
try rewrite formula_sub_false;
reflexivity.
Qed.

Lemma batch_app_split :
    forall (gamma1 gamma2 : list formula) (A1 A2 : formula) (S1 S2 : subst_ind),
        length gamma1 = length S1 ->
            length gamma2 = length S2 ->
                batch_sub (gamma1 ++ gamma2) A1 A2 (S1 ++ S2) = batch_sub gamma1 A1 A2 S1 ++ batch_sub gamma2 A1 A2 S2.
Proof.
induction gamma1;
intros gamma2 A1 A2 S1 S2 EQ1 EQ2;
destruct S1;
inversion EQ1 as [EQ].
reflexivity.
unfold batch_sub.
rewrite !app_length, EQ1, EQ2, !nat_eqb_refl, <- !app_comm_cons.
unfold batch_sub_fit;
fold batch_sub_fit.
rewrite !batch_sub_fit_true, IHgamma1.
reflexivity.
5 : rewrite !app_length.
all : try rewrite EQ;
      try rewrite EQ2;
      try rewrite nat_eqb_refl;
      reflexivity.
Qed.

Lemma batch_bury_comm_aux :
    forall (n : nat) (LF : list formula) (S : subst_ind) (A1 A2 : formula),
        bury (batch_sub LF A1 A2 S) n = batch_sub (bury LF n) A1 A2 (bury S n).
Proof.
induction n;
intros LF LS A v;
unfold batch_sub;
rewrite !bury_length;
case (nat_eqb (length LF) (length LS)) eqn:EQ;
try reflexivity;
destruct LF;
destruct LS;
try inversion EQ as [EQ'];
unfold bury;
fold @bury;
unfold batch_sub_fit;
fold batch_sub_fit;
unfold bury;
fold @bury;
try rewrite !batch_sub_fit_true;
try rewrite !batch_app_split;
try rewrite !bury_length;
try apply (nat_eqb_eq _ _ EQ');
try rewrite !app_length;
try apply EQ';
try rewrite batch_sub_single;
try rewrite IHn;
try reflexivity.

unfold length;
fold (@length formula);
fold (@length bool).
rewrite <- !plus_n_Sm, <- !plus_n_O.
apply EQ.
Qed.

Lemma batch_bury_comm :
    forall (LF : list formula) (LS : subst_ind) (n : nat) (A1 A2 : formula),
        bury (batch_sub LF A1 A2 (unbury LS n)) n = batch_sub (bury LF n) A1 A2 LS.
Proof.
intros LF LS n A1 A2.
rewrite <- (@bury_unbury _ LS n) at 2.
apply batch_bury_comm_aux.
Qed.

Lemma batch_sub_app {A1 A2 : formula} :
    forall (L1 L2 : list formula) (S : subst_ind),
        length (L1 ++ L2) = length S ->
            batch_sub (L1 ++ L2) A1 A2 S = batch_sub L1 A1 A2 (firstn (length L1) S) ++ batch_sub L2 A1 A2 (skipn (length L1) S).
Proof.
induction L1;
intros L2 S EQ.
rewrite !app_nil_l in *.
reflexivity.
destruct S.
inversion EQ.
unfold batch_sub.
rewrite firstn_length, skipn_length, <- !EQ, nat_eqb_refl, app_length, minus_n_plus_m, nat_eqb_refl, min_l, nat_eqb_refl.
rewrite <- !app_comm_cons in *.
unfold length in *;
fold (@length formula) (@length bool) in *.
apply eq_add_S in EQ.
unfold firstn, skipn;
fold (@firstn bool) (@skipn bool).
unfold batch_sub_fit;
fold batch_sub_fit.
rewrite !batch_sub_fit_true, (IHL1 _ _ EQ).
reflexivity.
rewrite skipn_length, <- EQ, app_length, minus_n_plus_m.
apply nat_eqb_refl.
rewrite firstn_length, <- EQ, app_length, min_l.
apply nat_eqb_refl.
apply PeanoNat.Nat.le_add_r.
rewrite EQ.
apply nat_eqb_refl.
apply PeanoNat.Nat.le_add_r.
Qed.

Lemma batch_sub_is_map_combine : 
    forall (L : list formula) (A1 A2 : formula) (S : subst_ind),
        length L = length S ->
            batch_sub L A1 A2 S = (map (fun PAIR => formula_sub (fst PAIR) A1 A2 (snd (PAIR))) (combine L S)).
Proof.
induction L;
intros A1 A2 S EQ;
unfold combine, batch_sub, batch_sub_fit, map;
fold batch_sub_fit (@combine formula bool);
rewrite EQ, nat_eqb_refl.
- reflexivity.
- destruct S;
  inversion EQ as [EQ'].
  fold (map (fun PAIR => formula_sub (fst PAIR) A1 A2 (snd (PAIR)))).
  unfold fst at 1, snd at 1.
  rewrite batch_sub_fit_true, IHL.
  reflexivity.
  apply EQ'.
  rewrite EQ'.
  apply nat_eqb_refl.
Qed.

Lemma batch_sub_length : 
    forall (L : list formula) (A1 A2 : formula) (S : subst_ind),
        length L = length S ->
            length L = length (batch_sub L A1 A2 S).
Proof.
intros L A1 A2 S EQ.
rewrite (batch_sub_is_map_combine _ _ _ _ EQ), map_length, combine_length, EQ, min_l;
reflexivity.
Qed.

Lemma batch_sub_false :
    forall (gamma : list formula) (A1 A2 : formula) (n : nat),
            batch_sub_fit gamma A1 A2 (repeat false n) = gamma.
Proof.
induction gamma;
intros A1 A2 n.
reflexivity.
destruct n.
reflexivity.
unfold repeat;
fold (@repeat bool).
unfold batch_sub_fit;
fold batch_sub_fit.
rewrite IHgamma, formula_sub_false.
reflexivity.
Qed.

(*vars_in form*)
Lemma var_ne_neb :
    forall (phi A : formula) (o : ovar),
        In o (vars_in A) ->
            ~ In o (vars_in phi) ->
                form_eqb phi A = false.
Proof.
induction phi;
intros A ov IN NIN;
destruct A;
unfold formula_sub, form_eqb;
fold formula_sub form_eqb;
try reflexivity.
- inversion IN.
- apply (nin_split nat_eq_dec) in NIN as [NIN1 NIN2].
  apply in_app_or in IN as [IN1 | IN2].
  + rewrite (IHphi1 _ _ IN1 NIN1).
    apply andb_false_l.
  + rewrite (IHphi2 _ _ IN2 NIN2).
    apply andb_false_r.
- assert (ov <> o0) as NE1.
  { intros FAL.
    subst.
    apply NIN, or_introl, eq_refl. }
  apply (nin_head nat_eq_dec) in NIN.
  fold vars_in in NIN.
  case (nat_eqb ov o) eqn:EQ.
  + apply nat_eqb_eq in EQ.
    subst.
    destruct IN as [EQ | IN].
    * subst.
      case (nat_eqb o0 o) eqn:EQ'.
      apply nat_eqb_eq in EQ'.
      contradiction (NE1 (eq_sym EQ')).
      rewrite andb_false_r.
      apply andb_false_l.
    * apply in_remove in IN as [_ NE].
      case (nat_eqb o o1) eqn:EQ.
      apply nat_eqb_eq in EQ.
      contradiction (NE EQ).
      apply andb_false_l.
  + assert (ov <> o) as NE.
    { intros FAL.
      subst.
      rewrite nat_eqb_refl in EQ.
      inversion EQ. }
    apply (nin_ne_weaken _ _ _ _ NE) in NIN.
    destruct IN as [EQ' | IN].
    * subst.
      case (nat_eqb o0 ov) eqn:EQ'.
      apply nat_eqb_eq in EQ'.
      contradiction (NE1 (eq_sym EQ')).
      rewrite andb_false_r.
      apply andb_false_l.
    * apply in_remove in IN as [IN _].
      rewrite (IHphi _ _ IN NIN).
      apply andb_false_r.
- contradiction (NIN IN).
- unfold vars_in in *;
  fold vars_in in *.
  rewrite (IHphi _ _ IN NIN), andb_false_r.
  reflexivity.
- unfold vars_in in *;
  fold vars_in in *.
  assert (ov <> o) as NE.
  { intros FAL.
    apply NIN, or_introl, eq_sym, FAL. }
  destruct IN as [EQ | IN].
  + subst.  
    case (nat_eqb o ov) eqn:FAL.
    apply nat_eqb_eq in FAL.
    contradiction (NE (eq_sym FAL)).
    rewrite andb_false_r, andb_false_l.
    reflexivity.
  + apply (nin_head nat_eq_dec) in NIN.
    rewrite (IHphi _ _ IN NIN), andb_false_r.
    reflexivity.
Qed.

Lemma var_ne_sub_triv :
    forall (phi A1 A2 : formula) (o : ovar) (b : bool),
        In o (vars_in A1) ->
            ~ In o (vars_in phi) ->
                formula_sub phi A1 A2 b = phi.
Proof.
induction phi;
intros A1 A2 ov b IN NIN;
destruct A1;
unfold formula_sub, form_eqb;
fold formula_sub form_eqb;
try reflexivity.
- inversion IN.
- apply (nin_split nat_eq_dec) in NIN as [NIN1 NIN2].
  apply in_app_or in IN as [IN1 | IN2].
  + rewrite (var_ne_neb _ _ _ IN1 NIN1), andb_false_l.
    reflexivity.
  + rewrite (var_ne_neb _ _ _ IN2 NIN2), andb_false_r.
    reflexivity.
- assert (ov <> o0) as NE1.
  { intros FAL.
    subst.
    apply NIN, or_introl, eq_refl. }
  apply (nin_head nat_eq_dec) in NIN.
  fold vars_in in NIN.
  case (nat_eqb ov o) eqn:EQ.
  + apply nat_eqb_eq in EQ.
    subst.
    destruct IN as [EQ | IN].
    * subst.
      case (nat_eqb o0 o) eqn:EQ'.
      apply nat_eqb_eq in EQ'.
      contradiction (NE1 (eq_sym EQ')).
      rewrite andb_false_r, andb_false_l.
      reflexivity.
    * apply in_remove in IN as [_ NE].
      case (nat_eqb o o1) eqn:EQ.
      apply nat_eqb_eq in EQ.
      contradiction (NE EQ).
      rewrite andb_false_l.
      reflexivity.
  + assert (ov <> o) as NE.
    { intros FAL.
      subst.
      rewrite nat_eqb_refl in EQ.
      inversion EQ. }
    apply (nin_ne_weaken _ _ _ _ NE) in NIN.
    destruct IN as [EQ' | IN].
    * subst.
      case (nat_eqb o0 ov) eqn:EQ'.
      apply nat_eqb_eq in EQ'.
      contradiction (NE1 (eq_sym EQ')).
      rewrite andb_false_r, andb_false_l.
      reflexivity.
    * apply in_remove in IN as [IN _].
      rewrite (var_ne_neb _ _ _ IN NIN), andb_false_r.
      reflexivity.
- contradiction (NIN IN).
- unfold vars_in in *;
  fold vars_in in *.
  rewrite (var_ne_neb _ _ _ IN NIN), andb_false_r.
  reflexivity.
- unfold vars_in in *;
  fold vars_in in *.
  assert (ov <> o) as NE.
  { intros FAL.
    apply NIN, or_introl, eq_sym, FAL. }
  destruct IN as [EQ | IN].
  + subst.  
    case (nat_eqb o ov) eqn:FAL.
    apply nat_eqb_eq in FAL.
    contradiction (NE (eq_sym FAL)).
    rewrite andb_false_r, andb_false_l.
    reflexivity.
  + apply (nin_head nat_eq_dec) in NIN.
    rewrite (var_ne_neb _ _ _ IN NIN), andb_false_r.
    reflexivity.
Qed.

Lemma var_ne_batch_sub_triv :
    forall (gamma : list formula) (A1 A2 : formula) (o : ovar) (S : subst_ind),
        In o (vars_in A1) ->
            ~ In o (flat_map vars_in gamma) ->
                batch_sub gamma A1 A2 S = gamma.
Proof.
induction gamma;
intros A1 A2 o S IN NIN;
unfold batch_sub, batch_sub_fit;
fold batch_sub_fit;
case nat_eqb eqn:EQ;
destruct S;
try reflexivity.
rewrite batch_sub_fit_true.
rewrite (var_ne_sub_triv _ _ _ _ _ IN (proj1 (nin_split nat_eq_dec _ _ _ NIN))), (IHgamma _ _ _ _ IN (proj2 (nin_split nat_eq_dec _ _ _ NIN))).
reflexivity.
apply EQ.
Qed.

(*vars_used form*)
(*
Lemma var_ne_neb :
    forall (phi A : formula) (o : ovar),
        In o (vars_used A) ->
            ~ In o (vars_used phi) ->
                form_eqb phi A = false.
Proof.
induction phi;
intros A ov IN NIN;
destruct A;
unfold formula_sub, form_eqb;
fold formula_sub form_eqb;
try reflexivity.
- inversion IN.
- apply (nin_split nat_eq_dec) in NIN as [NIN1 NIN2].
  apply in_app_or in IN as [IN1 | IN2].
  + rewrite (IHphi1 _ _ IN1 NIN1).
    apply andb_false_l.
  + rewrite (IHphi2 _ _ IN2 NIN2).
    apply andb_false_r.
- assert (ov <> o0) as NE1.
  { intros FAL.
    subst.
    apply NIN, or_introl, eq_refl. }
  apply (nin_head nat_eq_dec) in NIN.
  fold vars_used in NIN.
  destruct IN as [EQ | IN].
  + subst.
    case (nat_eqb o0 ov) eqn:EQ'.
    apply nat_eqb_eq in EQ'.
    contradiction (NE1 (eq_sym EQ')).
    rewrite andb_false_r.
    apply andb_false_l.
  + rewrite (IHphi _ _ IN NIN).
    apply andb_false_r.
- contradiction (NIN IN).
Qed.

Lemma var_ne_sub_triv :
    forall (phi A1 A2 : formula) (o : ovar) (b : bool),
        In o (vars_used A1) ->
            ~ In o (vars_used phi) ->
                formula_sub phi A1 A2 b = phi.
Proof.
induction phi;
intros A1 A2 ov b IN NIN;
destruct A1;
unfold formula_sub, form_eqb;
fold formula_sub form_eqb;
try reflexivity.
- inversion IN.
- apply (nin_split nat_eq_dec) in NIN as [NIN1 NIN2].
  apply in_app_or in IN as [IN1 | IN2].
  + rewrite (var_ne_neb _ _ _ IN1 NIN1), andb_false_l.
    reflexivity.
  + rewrite (var_ne_neb _ _ _ IN2 NIN2), andb_false_r.
    reflexivity.
- assert (ov <> o0) as NE1.
  { intros FAL.
    subst.
    apply NIN, or_introl, eq_refl. }
  apply (nin_head nat_eq_dec) in NIN.
  fold vars_used in NIN.
  destruct IN as [EQ | IN].
  + subst.
    case (nat_eqb o0 ov) eqn:EQ'.
    apply nat_eqb_eq in EQ'.
    contradiction (NE1 (eq_sym EQ')).
    rewrite andb_false_r, andb_false_l.
    reflexivity.
  + rewrite (var_ne_neb _ _ _ IN NIN), andb_false_r.
    reflexivity.
- contradiction (NIN IN).
Qed.

Lemma var_ne_batch_sub_triv :
    forall (gamma : list formula) (A1 A2 : formula) (o : ovar) (S : subst_ind),
        In o (vars_used A1) ->
            ~ In o (flat_map vars_used gamma) ->
                batch_sub gamma A1 A2 S = gamma.
Proof.
induction gamma;
intros A1 A2 o S IN NIN;
unfold batch_sub, batch_sub_fit;
fold batch_sub_fit;
case nat_eqb eqn:EQ;
destruct S;
try reflexivity.
rewrite batch_sub_fit_true.
rewrite (var_ne_sub_triv _ _ _ _ _ IN (proj1 (nin_split nat_eq_dec _ _ _ NIN))), (IHgamma _ _ _ _ IN (proj2 (nin_split nat_eq_dec _ _ _ NIN))).
reflexivity.
apply EQ.
Qed.
*)

(*
Lemma map_batch_sub : 
    forall (gamma : list formula) (A1 A2 : formula) (d : nat) (S : subst_ind) (F : formula -> formula),
        (forall (phi1 phi2 : formula),
            phi1 = phi2 <-> F phi1 = F phi2) ->
            map F (batch_sub gamma A1 A2 d S) = batch_sub (map F gamma) (F A1) (F A2) d S.
Proof.
induction gamma;
intros A1 A2 d S F INJ;
unfold batch_sub, batch_sub_fit.
- destruct S;
  rewrite map_length;
  reflexivity.
- unfold map;
  fold (map F) batch_sub_fit.
  unfold length;
  fold (@length bool) (@length formula).
  rewrite map_length.
  destruct S.
  reflexivity.
  unfold length at 2 4.
  fold (@length bool).
  unfold nat_eqb;
  fold nat_eqb.
  case (nat_eqb (length gamma) (length S)) eqn:EQB.
  + unfold map;
    fold (map F).
    rewrite !batch_sub_fit_true.
    rewrite IHgamma.
    unfold formula_sub.
    case (form_equiv a A1 d) eqn:EQF;
    destruct b;
    try apply form_eqb_eq in EQF;
    subst;
    try rewrite !form_eqb_refl;
    try reflexivity.
    * case (form_eqb (F a) (F A1)) eqn:FAL.
      apply form_eqb_eq, INJ in FAL.
      subst.
      rewrite form_eqb_refl in EQF.
      inversion EQF.
      reflexivity.
    * case (form_eqb (F a) (F A1)) eqn:FAL;
      reflexivity.
    * apply INJ.
    * rewrite map_length.
      apply EQB.
    * apply EQB.
  + reflexivity.
Qed.
*)

Lemma batch_sub_sublist :
    forall (L1 L2 : list formula) (A1 A2 : formula) (S : subst_ind),
        sublist form_eq_dec L1 L2 = true ->
            length L2 = length S ->
                sublist form_eq_dec (batch_sub L1 A1 A2 (list_filter S ((sublist_filter form_eq_dec L1 L2)))) (batch_sub L2 A1 A2 S) = true.
Proof.
induction L1;
intros L2 A1 A2 S SL EQ.
unfold batch_sub, batch_sub_fit.
fold batch_sub_fit.
rewrite EQ at 1.
rewrite nat_eqb_refl.
case nat_eqb;
apply sublist_nil.
destruct (sublist_cons_split form_eq_dec _ _ _ SL) as [L3 [L4 [SL' [EQ' NIN]]]].
subst.
assert (Nat.min (length L3) (length S) = length L3) as EQ'.
{ rewrite <- EQ, app_length.
  apply min_l, PeanoNat.Nat.le_add_r. }

rewrite (sublist_cons_split_filter form_eq_dec _ _ _ _ SL NIN).
rewrite (batch_sub_app _ _ _ EQ).
rewrite <- (firstn_skipn (length L3) S) at 1.
rewrite list_filter_app.
- rewrite firstn_length.
  rewrite EQ'.
  rewrite (plus_n_O (length L3)) at 2 5.
  rewrite <- (repeat_length false (length L3)) at 2 5.
  rewrite firstn_app_2.
  rewrite skipn_app2.
  rewrite firstn_O.
  rewrite app_nil_r.
  rewrite <- EQ' at 2.
  rewrite <- firstn_length.
  rewrite <- filter_false_nil.
  rewrite app_nil_l.
  unfold skipn at 2.
  apply sublist_app.
  unfold batch_sub.
  assert (length (skipn (length L3) S) = length (a :: L4)) as LEN.
  { rewrite skipn_length, <- EQ, app_length.
    apply minus_n_plus_m. }
  rewrite LEN, nat_eqb_refl.
  rewrite sublist_count_length.
  2 : rewrite LEN;
      apply eq_S, eq_sym, sublist_filter_length, SL'.
  unfold count_true;
  fold count_true.
  unfold length at 1;
  fold (@length formula).
  rewrite (sublist_filter_true _ _ _ SL'), nat_eqb_refl.
  destruct (skipn (length L3) S) eqn:EQ'';
  inversion LEN as [LEN'].
  unfold list_filter;
  fold @list_filter.
  unfold batch_sub_fit;
  fold batch_sub_fit.
  unfold sublist;
  fold @sublist.
  rewrite !batch_sub_fit_true.
  + case form_eq_dec as [_ | FAL].
    apply (IHL1 _ _ _ _ SL' (eq_sym LEN')).
    contradiction (FAL eq_refl).
  + rewrite LEN'.
    apply nat_eqb_refl.
  + rewrite sublist_count_length, (sublist_filter_true _ _ _ SL').
    apply nat_eqb_refl.
    rewrite (sublist_filter_length _ _ _ SL').
    apply LEN'.
- rewrite (firstn_skipn (length L3) S), <- EQ, !app_length, repeat_length.
  unfold length at 2 4;
  fold (@length formula) (@length bool).
  rewrite (sublist_filter_length _ _ _ SL').
  reflexivity.
Qed.

Lemma batch_sub_fold_head :
    forall {phi A B : formula} {gamma : list formula} {b : bool} {S : subst_ind},
        (length gamma =? length S) = true ->
            formula_sub phi A B b :: batch_sub_fit gamma A B S = batch_sub (phi :: gamma) A B (b :: S).
Proof.
intros phi A B gamma b S EQ.
unfold batch_sub, length, nat_eqb in *.
rewrite EQ.
reflexivity.
Qed.

(*
Lemma sub_fit_true :
    forall (L : list formula) (D E : formula) (S : subst_ind),
        subst_ind_fit L S = true ->
            formula_sub_ind L D E S = formula_sub_ind_fit L D E S.
Proof.
intros L D E S FS.
unfold formula_sub_ind.
rewrite FS.
reflexivity.
Qed.

Lemma sub_fit_false :
    forall (L : list formula) (D E : formula) (S : subst_ind),
        subst_ind_fit L S = false ->
            formula_sub_ind L D E S = L.
Proof.
intros L D E S FS.
unfold formula_sub_ind.
rewrite FS.
reflexivity.
Qed.
*)

(*
Lemma formula_sub_ind_fit_0 :
    forall (L : list formula) (D E : formula),
        formula_sub_ind_fit L D E [] = L.
Proof.
intros L D E.
destruct L;
reflexivity.
Qed.

Lemma formula_sub_ind_0 :
    forall (A D E : formula),
        formula_sub_ind A D E (0) = A.
Proof.
intros A D E.
case (subst_ind_fit A (0)) eqn:HA;
unfold formula_sub_ind;
rewrite HA.
- rewrite formula_sub_ind_fit_0.
  reflexivity.
- reflexivity.
Qed.

Lemma formula_sub_ind_lor :
    forall (A B D E : formula) (S_A S_B : subst_ind),
        subst_ind_fit A S_A && subst_ind_fit B S_B = true ->
            formula_sub_ind (lor A B) D E (lor_ind S_A S_B) = 
                lor (formula_sub_ind A D E S_A) (formula_sub_ind B D E S_B).
Proof.
intros A B D E S_A S_B FS.
unfold formula_sub_ind.
destruct (and_bool_prop _ _ FS) as [FSA FSB].
rewrite FSA,FSB.
unfold subst_ind_fit; fold subst_ind_fit.
rewrite FS.
unfold formula_sub_ind_fit; fold formula_sub_ind_fit.
reflexivity.
Qed.
*)

(*
Lemma non_target_eq_sub_non_target :
    forall (L : list formula) (n : nat) (t : term),
        subst_ind_fit (substitution A n t) (non_target A) = true.
Proof.
intros A n t.
unfold subst_ind_fit, non_target, substitution.
induction A.
3 : rewrite IHA1, IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.

Lemma target_sub_fit :
    forall (A : formula) (n : nat) (t : term),
        subst_ind_fit (substitution A n t) (target A) = true.
Proof.
intros A n t.
unfold subst_ind_fit, target, substitution.
induction A.
3 : rewrite IHA1, IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.

Lemma non_target_sub' :
    forall (A D E : formula),
        formula_sub_ind_fit A D E (non_target A) = A.
Proof.
intros A D E.
induction A;
unfold non_target, formula_sub_ind_fit;
fold non_target formula_sub_ind_fit.
4 : case (form_eqb (univ n A) D).
3 : rewrite IHA1, IHA2.
2 : case (form_eqb (neg A) D).
1 : case (form_eqb (atom a) D).
all : reflexivity.
Qed.

Lemma non_target_sub :
    forall (A C D : formula),
        formula_sub_ind A C D (non_target A) = A.
Proof.
intros A C D.
unfold formula_sub_ind.
rewrite non_target_fit.
apply non_target_sub'.
Qed.

Lemma non_target_sub_lor :
    forall (A B D E : formula) (S : subst_ind),
        formula_sub_ind (lor A B) D E (lor_ind (non_target A) S) =
            lor A (formula_sub_ind B D E S).
Proof.
intros A B D E S.
unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit;
fold subst_ind_fit formula_sub_ind_fit.
rewrite non_target_fit, non_target_sub'.
case (subst_ind_fit B S) eqn:HB;
reflexivity.
Qed.

Lemma non_target_term_sub :
    forall (A : formula) (n : nat) (t : term),
        non_target A = non_target (substitution A n t).
Proof.
intros A n t.
induction A;
unfold non_target, substitution;
fold non_target substitution.
3 : rewrite IHA1,IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.

Lemma target_term_sub :
    forall (A : formula) (n : nat) (t : term),
        target A = target (substitution A n t).
Proof.
intros A n t.
induction A;
unfold target, substitution;
fold target substitution.
3 : rewrite IHA1,IHA2.
4 : case (nat_eqb n0 n).
all : reflexivity.
Qed.


Lemma non_target_sub_term' :
    forall (A C D: formula) (n : nat) (t : term),
        formula_sub_ind_fit (substitution A n t) C D (non_target A) = (substitution A n t).
Proof.
intros.
rewrite (non_target_term_sub _ n t).
apply non_target_sub'.
Qed.


Lemma non_target_sub_term :
    forall (A C D: formula) (n : nat) (t : term),
        formula_sub_ind (substitution A n t) C D (non_target A) = (substitution A n t).
Proof.
intros.
rewrite (non_target_term_sub _ n t).
apply non_target_sub.
Qed.

Lemma formula_sub_ind_free_list :
    forall (A B C : formula),
        (free_list B = free_list C) ->
            forall (S : subst_ind),
                free_list (formula_sub_ind_fit A B C S) = free_list A.
Proof.
intros A B C FREE.
induction A;
intros S;
unfold formula_sub_ind.

all : unfold formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      try case form_eqb eqn:EQ;
      destruct S;
      try apply form_eqb_eq in EQ;
      try destruct EQ, FREE;
      try reflexivity.

1 : unfold free_list;
    fold free_list.
    rewrite IHA1,IHA2.
    reflexivity.
Qed.

Lemma formula_sub_ind_free_list_sub :
    forall (A B C : formula),
        (incl (free_list C) (free_list B)) ->
            forall (S : subst_ind),
                incl (free_list (formula_sub_ind_fit A B C S)) (free_list A).
Proof.
intros A B C FREE.
induction A;
intros S m IN;
unfold formula_sub_ind.

all : unfold formula_sub_ind_fit in IN;
      try case form_eqb eqn:EQ;
      destruct S;
      try apply form_eqb_eq in EQ;
      fold formula_sub_ind_fit in IN;
      try destruct EQ;
      try apply IN;
      try apply (FREE _ IN).

1 : unfold free_list in *;
    fold free_list in *.
    apply nodup_In.
    apply nodup_In in IN.
    apply in_app_or in IN as [IN1 | IN2].
    apply (in_or_app _ _ _ (or_introl (IHA1 _ _ IN1))).
    apply (in_or_app _ _ _ (or_intror (IHA2 _ _ IN2))).
Qed.

Lemma formula_sub_ind_closed :
    forall (A B C : formula),
        closed A = true ->
            (closed B = true -> closed C = true) ->
                forall (S : subst_ind),
                    closed (formula_sub_ind A B C S) = true.
Proof.
intros A B C.
induction A;
intros CA CBC S;
unfold formula_sub_ind.
4 : case (subst_ind_fit (univ n A) S).
3 : case (subst_ind_fit (lor A1 A2) S) eqn:FS.
2 : case (subst_ind_fit (neg A) S).
1 : case (subst_ind_fit (atom a) S).
all : try apply CA;
      unfold formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      destruct S;
      try apply CA.
7 : { unfold formula_sub_ind, formula_sub_ind_fit, subst_ind_fit, closed in *;
      fold formula_sub_ind formula_sub_ind_fit subst_ind_fit closed in *.
      destruct (and_bool_prop _ _ CA) as [CA1 CA2].
      destruct (and_bool_prop _ _ FS) as [FS1 FS2].
      pose proof (IHA1 CA1 CBC S1) as CFA1.
      rewrite FS1 in CFA1.
      rewrite CFA1.
      pose proof (IHA2 CA2 CBC S2) as CFA2.
      rewrite FS2 in CFA2.
      rewrite CFA2.
      reflexivity. }
7-9 : case (form_eqb (univ n A) B) eqn:EQ.
4-6 : case (form_eqb (neg A) B) eqn:EQ.
1-3 : case (form_eqb (atom a) B) eqn:EQ.
all : try apply CA;
      apply form_eqb_eq in EQ;
      destruct EQ;
      apply (CBC CA).
Qed.

Lemma formula_sub_ind_1 :
    forall (A B : formula),
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind A A B (1) = B.
Proof.
intros A B FS.
destruct A;
unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit.
3 : inversion FS.
all : rewrite form_eqb_refl;
      reflexivity.
Qed.

Theorem lor_sub_right:
    forall C A E,
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind (lor C A) A E (lor_ind (non_target C) (1)) = lor C E.
Proof.
intros C A E FS.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ E FS).
  rewrite non_target_sub.
  reflexivity.
- rewrite non_target_fit.
  apply FS.
Qed.

Theorem lor_sub_left:
    forall A D E,
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind (lor A D) A E (lor_ind (1) (non_target D)) = lor E D.
Proof.
intros A D E FS.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ E FS).
  rewrite non_target_sub.
  reflexivity.
- rewrite FS.
  apply non_target_fit.
Qed.
*)