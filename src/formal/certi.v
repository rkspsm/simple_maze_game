Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Setoid.
Require Import model.

Theorem beq_locP : forall l1 l2, reflect (l1 = l2) (beq_loc l1 l2).
Proof.
  intros l1 l2. apply iff_reflect. split.
  - intros h ; rewrite h. destruct l2 ; simpl ; trivial.
  - intros h. destruct l1, l2 ; try solve [ inversion h ] ; reflexivity.
Qed.

Fixpoint loc_map_length' (lm : loc_map) {struct lm} : option nat :=
  match lm with
  | [] => None
  | [l] => Some (length l)
  | l::ls => match loc_map_length' ls with
             | Some n => match beq_nat (length l) n with
                         | true => Some (length l)
                         | false => None
                         end
             | None => None
             end
  end.

Lemma loc_map_length'_head1 : forall l lm n,
    loc_map_length' (l :: lm) = Some n -> length l = n.
Proof.
  intros l lm.
  generalize dependent l.
  induction lm.
  - intros l n h. simpl in h. inversion h. trivial.
  - intros l n h.
    rename IHlm into ih.
    remember (a :: lm) as l' eqn:er1.
    destruct (loc_map_length' l') eqn:dr1.
    unfold loc_map_length' in h. unfold loc_map_length' in dr1. rewrite dr1 in h.
    clear dr1. subst l'.
    destruct (length l =? n0) eqn:dr2. inversion h ; trivial.
    inversion h.
    unfold loc_map_length' in h, dr1. rewrite dr1 in h. clear dr1.
    rewrite er1 in h. inversion h.
Qed.

Lemma loc_map_length'_head2 : forall l1 l2 lm n,
    loc_map_length' (l1 :: l2 :: lm) = Some n -> length l1 = length l2 /\ length l1 = n.
Proof.
  intros l1 l2 lm n h.
  split.
  - assert (length l1 = n). {
      pose (loc_map_length'_head1 _ _ _ h) as ep1. assumption. }
    remember (l2 :: lm) as l' eqn:er1.
    unfold loc_map_length' in h. fold loc_map_length' in h.
    destruct (loc_map_length' l') eqn:ed1.
    assert (n = n0). {
      rewrite er1 in h. rewrite H in h. destruct (n =? n0) eqn:ed2.
      apply beq_nat_true. assumption. inversion h. }
    subst n0. subst l'. apply loc_map_length'_head1 in ed1. congruence.
    rewrite er1 in h. inversion h.
  - apply loc_map_length'_head1 in h. assumption.
Qed.

Lemma loc_map_length'_tail2 : forall lm l1 l2 n,
    loc_map_length' (l1 :: l2 :: lm) = Some n -> loc_map_length' (l2 :: lm) = Some n.
Proof.
  intros lm.
  induction lm.
  - intros. simpl in H.
    simpl. destruct (length l1 =? length l2) eqn:ed1.
    apply beq_nat_true in ed1. rewrite <- ed1. assumption.
    inversion H.
  - rename IHlm into ih.
    intros l1 l2 n h. clear ih.
    remember (a :: lm) as l' eqn:er1.
    destruct (loc_map_length' (l2 :: l')) eqn:ed1.
    pose (loc_map_length'_head2 _ _ _ _ h). destruct a0.
    pose (loc_map_length'_head1 _ _ _ ed1). rewrite <- H0.
    rewrite <- e. rewrite H. reflexivity.
    unfold loc_map_length' in h,ed1. rewrite ed1 in h. clear ed1. inversion h.
Qed.

Lemma loc_map_length'_in : forall lm n,
    loc_map_length' lm = Some n -> (forall l, In l lm -> length l = n).
Proof.
  intros lm.
  induction lm.
  - intros n h l hin. inversion hin.
  - rename IHlm into ih.
    intros n h l hin. inversion hin ; clear hin.
    + subst. apply loc_map_length'_head1 in h. assumption.
    + assert (length a = n). {
        apply loc_map_length'_head1 in h. assumption. }
      destruct lm as [| l' lm']. inversion H.
      apply loc_map_length'_tail2 in h.
      auto.
Qed.  

Definition loc_map_length_valid (lm : loc_map) : bool :=
  match lm with
  | [] => true
  | _::_ => match loc_map_length' lm with
            | Some _ => true
            | None => false
            end
  end.

Lemma loc_map_length_valid_next : forall l lm,
    loc_map_length_valid (l :: lm) = true -> loc_map_length_valid lm = true.
Proof.
  intros l lm.
  generalize dependent l.
  induction lm.
  - intros l h. compute. reflexivity.
  - rename IHlm into ih.
    intros l h. unfold loc_map_length_valid in h.
    destruct (loc_map_length' (l :: a :: lm)) eqn:de1.
    + remember (a :: lm) as l' eqn:er1.
      destruct (loc_map_length' l') eqn:ed1.
      unfold loc_map_length_valid. rewrite er1. rewrite er1 in ed1. rewrite ed1. reflexivity.
      unfold loc_map_length' in de1,ed1. rewrite ed1 in de1. clear ed1.
      rewrite er1 in de1. congruence.
    + inversion h.
Qed.

Theorem loc_map_length_fr : forall lm,
    loc_map_length_valid lm = true ->
    (forall l1 l2, In l1 lm -> In l2 lm -> length l1 = length l2).
Proof.
  intros lm.
  induction lm ;
    try rename IHlm into ih ;
    intros h l1 l2 in1 in2.
  - inversion in1.
  - unfold loc_map_length_valid in h.
    destruct (loc_map_length' (a::lm)) eqn:ed1.
    assert (length l1 = n). {
      eapply loc_map_length'_in. exact ed1. assumption. }
    assert (length l2 = n). {
      eapply loc_map_length'_in. exact ed1. assumption. }
    congruence. inversion h.
Qed.
    
Definition loc_map_validf (lm : loc_map) : bool :=
  andb (loc_map_length_valid lm)
       (andb (beq_nat (loc_map_count lm loc_player) 1)
             (Nat.leb 1 (loc_map_count lm loc_door))).

Theorem loc_map_valid_fr : forall lm,
    loc_map_validf lm = true -> loc_map_valid lm.
Proof.
  intros lm. unfold loc_map_valid, loc_map_valid.
  intros h.
  apply andb_prop in h. inversion h as [h1 h'].
  apply andb_prop in h'. inversion h' as [h2 h3].
  clear h h'.
  apply beq_nat_true in h2.
  apply leb_complete in h3.
  split ; [ | split ; assumption ].
  apply loc_map_length_fr.
  assumption.
Qed.
