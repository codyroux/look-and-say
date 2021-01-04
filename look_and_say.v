(**********************************************************************
*
* This file contains a definition of the "look and say" sequence
* https://en.wikipedia.org/wiki/Look-and-say_sequence
*
* Along with a proof that it contains only numbers <= 3 and is decidable.
*
* MIT License
*
* Copyright (c) 2021 Cody Roux (codyroux), see LICENSE file for details.
*
*
*
***********************************************************************)



Require Import List Arith Lia.

Import ListNotations.


Print List.

Inductive LookAndSay : list nat -> list nat -> Prop :=
| LAS_nil : LookAndSay [] []
| LAS_Cons : forall l1 l2 a k, 0 < k -> hd_error l1 <> Some a -> LookAndSay l1 l2 -> LookAndSay ((repeat a k) ++ l1) (k::a::l2)
.

Hint Constructors LookAndSay.

Goal LookAndSay [1;1;1;2;2] [3;1;2;2].
Proof.
  replace ([1; 1; 1; 2; 2]) with (repeat 1 3 ++ repeat 2 2 ++ []) by reflexivity.
  apply LAS_Cons; [lia | simpl; congruence | ].
  apply LAS_Cons; [lia | simpl; congruence | ].
  now auto.
Qed.


Inductive LookAndSay_n : nat -> list nat -> Prop :=
  | LAS_n_0 : LookAndSay_n 0 [1]
  | LAS_n_S : forall n l l', LookAndSay_n n l -> LookAndSay l l' -> LookAndSay_n (S n) l'
.


Lemma skipn_repeat : forall A n (a : A) k, skipn n (repeat a k) = repeat a (k - n).
Proof.
  induction n; simpl.
  - intros; rewrite Nat.sub_0_r; now auto.
  - induction k; simpl; auto.
Qed.


Inductive val_and_len_bounded : list nat -> Prop :=
| val_and_len_bounded_nil : val_and_len_bounded []
| val_and_len_bounded_cons : forall l1 l2 a k,
    0 < k <= 3 ->
    a <= 3 ->
    hd_error l1 <> Some a ->
    val_and_len_bounded l1 ->
    l2 = repeat a k ++ l1 ->
    val_and_len_bounded l2
.

Hint Constructors val_and_len_bounded.

Lemma bounded_cons : forall n l, val_and_len_bounded l -> val_and_len_bounded (skipn n l).
Proof.
  induction n using lt_wf_ind.
  intros l h.
  inversion h; subst; auto.
  - rewrite skipn_nil; auto.
  - rewrite skipn_app.
    rewrite repeat_length.
    rewrite skipn_repeat.
    destruct (Nat.le_gt_cases k n).
    + replace (k - n) with 0 by lia; simpl.
      apply H; [lia | now auto].
    + replace (n - k) with 0 by lia; simpl.
      apply val_and_len_bounded_cons with (l1 := l1) (a := a) (k := k - n); first [lia | congruence].
Qed.

Lemma skipn_len_app : forall A l1 l2, skipn(A:=A) (length l1) (l1 ++ l2) = l2.
Proof.
  induction l1; simpl; auto.
Qed.

Lemma bounded_extensions : forall l1 l2, val_and_len_bounded (l1 ++ l2) -> val_and_len_bounded l2.
Proof.
  intros.
  replace l2 with (skipn (length l1) (l1 ++ l2)) by apply skipn_len_app; auto.
  apply bounded_cons; auto.
Qed.


(* Require Import Coq.Program.Equality. *)

Lemma LAS_hd_second : forall l1 l2 k, LookAndSay l1 (k::l2) -> hd_error l1 = hd_error l2.
Proof.
  intros l1 l2 k h; inversion h.
  destruct k; simpl; [lia| now auto].
Qed.


Lemma LAS_bounded : forall l l', LookAndSay l l' -> val_and_len_bounded l -> val_and_len_bounded l'.
Proof.
  intros l l' h.
  induction h.
  - auto.
  - intros h'.
    inversion h'.
    + destruct k; [lia| simpl in *; congruence].
    + clear H6.
      assert (a = a0) by (destruct k; destruct k0; simpl in H5; first [lia | congruence]).
      subst a0.
      destruct (Nat.eq_dec k a); subst.
      -- destruct l2.
         ++ apply val_and_len_bounded_cons with (l1 := []) (a := a) (k := 2);
              simpl; first [lia | congruence | constructor | idtac].
         ++ assert (hd_error l2 <> Some a) by (erewrite <- LAS_hd_second; [exact H0| exact h]).
            destruct (Nat.eq_dec a n); subst.
            { apply val_and_len_bounded_cons with (l1 := l2) (a := n) (k := 3); simpl; first [lia | congruence | auto].
              replace l2 with (skipn 1 (n::l2)) by reflexivity.
              apply bounded_cons.
              apply IHh.
              eapply bounded_extensions; eauto. }
            apply val_and_len_bounded_cons with (l1 := (n::l2)) (a := a) (k := 2); simpl; first [lia | congruence | auto].
            apply IHh; eapply bounded_extensions; eauto.
      -- assert (k = k0).
         (* Ugh I can make this a lemma as well... *)
         { revert H5 H3 H0; clear.
           revert k0 l0 l1 a.
           induction k; induction k0; simpl; auto.
           - intros.
             exfalso.
             destruct l1; simpl in *; congruence.
           - intros.
             destruct l0; simpl in *; congruence.
           - intros; f_equal; eapply IHk; inversion H5; eauto. }
         subst.
         apply val_and_len_bounded_cons with (l1 := (a::l2)) (a := k0) (k := 1); simpl; first [lia | congruence | auto].
         destruct l2.
         ++ apply val_and_len_bounded_cons with (l1 := []) (a := a) (k := 1);
              simpl; first [lia | congruence | constructor | idtac].
         ++ destruct (Nat.eq_dec a n0); subst.
            {
              assert (hd_error l2 <> Some n0) by (erewrite <- LAS_hd_second; [exact H0| exact h]).
              apply val_and_len_bounded_cons with (l1 := l2) (a := n0) (k := 2); simpl; first [lia | congruence | auto].
              replace l2 with (skipn 1 (n0::l2)) by reflexivity.
              apply bounded_cons.
              apply IHh.
              eapply bounded_extensions; eauto. }
            apply val_and_len_bounded_cons with (l1 := (n0::l2)) (a := a) (k := 1);
              simpl; first [lia | congruence | constructor | idtac].
            apply IHh; eapply bounded_extensions; eauto.
Qed.

Lemma bounded_In : forall l a, val_and_len_bounded l -> In a l -> a <= 3.
Proof.
  intros l a h; revert a; induction h.
  - intros a h; inversion h.
  - intros b; rewrite H2.
    intros h'.
    generalize (in_app_or _ _ _ h').
    intro h''; destruct h''.
    + generalize (repeat_spec k a b H3); intros; subst; now auto.
    + now auto.
Qed.

Lemma bounded_init : val_and_len_bounded [1].
Proof.
  apply val_and_len_bounded_cons with (l1 := []) (a := 1) (k := 1); simpl; first [lia | congruence | auto].
Qed.

Theorem LookAndSay_less_than_3 : forall n l a, LookAndSay_n n l -> In a l -> a <= 3.
Proof.
  intros n l a h.
  apply bounded_In.
  induction h; [apply bounded_init |].
  eapply LAS_bounded; eauto.
Qed.







(*****************************************************************************************************)

Fixpoint get_prefix_tl (l : list nat) (a : nat) : list nat :=
  match l with
  | [] => []
  | b::l' =>
    if a =? b then
      get_prefix_tl l' a
    else l
  end.

Fixpoint get_prefix_len (l : list nat) (a : nat) : nat :=
  match l with
  | [] => 0
  | b::l' => if a =? b then
               S (get_prefix_len l' a)
             else 0
  end.


Eval compute in (get_prefix_len [1;1;1;1;1;1;1;2;1;1] 1).
Eval compute in (get_prefix_tl [1;1;1;1;1;1;1;2;1;1] 1).


Lemma get_prefix_len_gt : forall l a, hd_error l = Some a <-> 0 < get_prefix_len l a.
Proof.
  split.
  - destruct l; simpl; [congruence|].
    intros.
    inversion H.
    rewrite <- beq_nat_refl.
    lia.
  - destruct l; simpl; [lia|].
    case_eq (a =? n).
    + intro h; rewrite (beq_nat_true _ _ h); now auto.
    + lia.
Qed.

Lemma get_prefix_len_aux : forall l a, length (get_prefix_tl l a) + (get_prefix_len l a) = length l.
Proof.
  induction l; simpl; auto.
  intros b.
  destruct (b =? a); auto.
  erewrite <- IHl; now eauto.
Qed.

Lemma get_prefix_aux_head : forall l a, hd_error (get_prefix_tl l a) <> Some a.
Proof.
  induction l; simpl; [congruence|].
  intro b; case_eq (b =? a); intro eq_a; simpl.
  - apply IHl.
  - assert (b <> a) by (apply beq_nat_false; now auto).
    congruence.
Qed.

Lemma get_prefix_repeat : forall l a, l = (repeat a (get_prefix_len l a)) ++ (get_prefix_tl l a).
Proof.
  induction l; simpl; auto.
  intros b; case_eq (b =? a); intro eq_a.
  - assert (H : b = a) by (apply beq_nat_true; now auto).
    rewrite H; simpl.
    f_equal; now auto.
  - simpl; now auto.
Qed.

Lemma LAS_empty : forall l, LookAndSay [] l -> l = [].
Proof.
  intros l h; inversion h; auto.
  destruct k; simpl in *; first [lia | congruence].
Qed.


Fixpoint look_and_say (gas : nat) (l : list nat) : option (list nat) :=
  match gas with
  | 0 => None
  | S k =>
    match l with
    | [] => Some []
    | a::l' =>
      option_map (fun l'' => S (get_prefix_len l' a) :: a :: l'') (look_and_say k (get_prefix_tl l' a))
    end
  end.

Lemma look_and_say_gas : forall k l, length l < k -> look_and_say k l <> None.
Proof.
  induction k; simpl.
  - lia.
  - intros l len.
    destruct l.
    + congruence.
    + unfold option_map.
       simpl in len.
       assert (length (get_prefix_tl l n) <= length l).
      -- erewrite <- (get_prefix_len_aux l) with (a := n).
         lia.
      -- assert (len' : length (get_prefix_tl l n) < k) by lia.
         generalize (IHk _ len'); intro H'.
         case_eq (look_and_say k (get_prefix_tl l n)); intros; simpl; congruence.
Qed.

Lemma get_prefix_tl_repeat : forall l a k,
 hd_error l <> Some a ->
    get_prefix_tl (repeat a k ++ l) a = l.
  induction k; simpl.
  - induction l; simpl; auto.
    intro neq.
    assert (a <> a0) by congruence.
    rewrite<- Nat.eqb_neq in *.
    rewrite H; auto.
  - rewrite<- beq_nat_refl.
    auto.
Qed.

Lemma get_prefix_len_repeat : forall l a k,
 hd_error l <> Some a ->
 get_prefix_len (repeat a k ++ l) a = k.
Proof.
  induction k; simpl.
  - induction l; simpl; auto.
    intro neq.
    assert (a <> a0) by congruence.
    rewrite<- Nat.eqb_neq in *.
    rewrite H; auto.
  - rewrite<- beq_nat_refl.
    auto.
Qed.


Lemma look_and_say_repeat : forall gas l a k,
    0 < k ->
    hd_error l <> Some a ->
    look_and_say (S gas) ((repeat a k) ++ l) = option_map (fun l'' => k :: a :: l'') (look_and_say gas l).
Proof.
  intros.
  simpl.
  destruct k; simpl; first [lia | congruence | idtac].
  rewrite get_prefix_len_repeat; auto.
  rewrite get_prefix_tl_repeat; auto.
Qed.


Lemma LAS_cons : forall l l', LookAndSay l l' ->
                              forall gas,
                                length l < gas ->
                                Some l' = look_and_say gas l.
Proof.
  intros l l' las.
  induction las.
  - simpl; destruct gas; first [lia | auto].
  - rewrite app_length, repeat_length.
    intros.
    destruct gas; [lia |].
    rewrite look_and_say_repeat; auto.
    erewrite <- IHlas; [eauto | lia ].
Qed.
