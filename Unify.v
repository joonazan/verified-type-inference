Require Import String Arith.
Require Import Program.

Definition name := string.
Definition tvarname := nat.

Inductive Tipe : Type :=
  TVar : tvarname -> Tipe
| TConst : name -> Tipe
| TApp : Tipe -> Tipe -> Tipe.

Definition eq_dec (a : Tipe) (b : Tipe) : { a = b } + { ~ a = b }.
repeat decide equality.
Defined.

Definition Subst := nat -> Tipe.
Definition identity x := TVar x.
Definition sole_sub x t y :=
  if Nat.eq_dec x y then t else TVar y.

Fixpoint apply s t :=
match t with
  TVar x => s x
| TConst x => TConst x
| TApp a b => TApp (apply s a) (apply s b)
end.

Definition sequence (s2 : Subst) (s : Subst) := fun x => apply s2 (s x).

Definition unifies s a b := apply s a = apply s b.

Definition isMGU s a b := forall s', unifies s' a b
  -> exists delta, forall t, apply s' t = apply delta (apply s t).

Theorem identity_does_nothing : forall x, apply identity x = x.
Proof.
intros. induction x.
- easy.
- easy.
- unfold apply. unfold apply in IHx1. unfold apply in IHx2.
  rewrite IHx1. rewrite IHx2. reflexivity.
Qed.

Theorem sole_sub_works : forall a t, apply (sole_sub a t) (TVar a) = t.
Proof.
intros. unfold apply. unfold sole_sub. destruct (Nat.eq_dec a a).
- reflexivity.
- contradiction.
Qed.

Theorem sequence_application : forall x, forall u, forall v,
  apply (sequence v u) x = apply v (apply u x).
Proof.
intros.
induction x. easy. easy.
- unfold apply. unfold apply in IHx1. unfold apply in IHx2.
  rewrite IHx1. rewrite IHx2. reflexivity.
Qed.

Theorem apply_goes_into_tapp : forall s, forall a, forall b,
  apply s (TApp a b) = TApp (apply s a) (apply s b).
Proof.
unfold apply. reflexivity.
Qed.

Inductive Contains : Tipe -> Tipe -> Prop :=
  Here : forall t, Contains t t
| InLeft : forall a t t2, Contains a t -> Contains a (TApp t t2)
| InRight : forall a t t2, Contains a t -> Contains a (TApp t2 t).

Definition contains_dec t t2 : { Contains t t2 } + { ~ Contains t t2 }.
destruct (eq_dec t t2).
- left. rewrite e. apply Here.
- induction t2.
  * right. intro. dependent destruction H. congruence.
  * right. intro. dependent destruction H. congruence.
  * destruct (eq_dec t t2_1).
    + left. apply InLeft. rewrite e. apply Here.
    + apply IHt2_1 in n0. destruct n0. left. apply InLeft. assumption.
      destruct (eq_dec t t2_2). left. apply InRight. rewrite e. apply Here.
      apply IHt2_2 in n1. destruct n1. left. apply InRight. assumption.
      right. intro. dependent destruction H. contradiction. easy. easy.
Defined.

Theorem map_containment : forall s x t,
  Contains x t -> Contains (apply s x) (apply s t).
Proof.
intros. induction H.
- apply Here.
- rewrite apply_goes_into_tapp. apply InLeft. assumption.
- rewrite apply_goes_into_tapp. apply InRight. assumption.
Qed.

Theorem containment_transitive : forall a b c,
  Contains a b -> Contains b c -> Contains a c.
Proof.
intros. induction H0. assumption.
apply InLeft. apply IHContains. assumption.
apply InRight. apply IHContains. assumption.
Qed.

Theorem bad_recursion_left : forall a b, a <> TApp a b.
Proof.
intros. induction a.
- easy.
- easy.
- intro. injection H. intros. rewrite H0 in H1. apply IHa1 in H1. assumption.
Qed.

Theorem bad_recursion_right : forall a b, b <> TApp a b.
Proof.
intros. induction b.
- easy.
- easy.
- intro. injection H. intros. rewrite H1 in H0. apply IHb2 in H0. assumption.
Qed.

Fixpoint size x :=
match x with
  TVar _ => 1
| TConst _ => 1
| TApp a b => size a + size b
end.

Lemma size_is_nonzero : forall x, 0 < size x.
induction x.
- compute; easy.
- compute; easy.
- simpl. rewrite IHx1. apply Nat.lt_add_pos_r. assumption.
Qed.

Lemma contained_is_smaller : forall a b, Contains a b -> a <> b -> size a < size b.
intros.
dependent induction H.
contradiction.
destruct (eq_dec a t);
  [ rewrite e; simpl; apply Nat.lt_add_pos_r; apply size_is_nonzero 
  | apply IHContains in n; rewrite n; simpl; apply Nat.lt_add_pos_r; apply size_is_nonzero ].
destruct (eq_dec a t);
  [ rewrite e; simpl; apply Nat.lt_add_pos_l; apply size_is_nonzero 
  | apply IHContains in n; rewrite n; simpl; apply Nat.lt_add_pos_l; apply size_is_nonzero ].
Qed.

Theorem impossible_loop {a b}
  (ainb : Contains a b) (bina : Contains b a) (anotb : a <> b) : False.
pose proof contained_is_smaller.
apply H in ainb.
apply H in bina.
rewrite ainb in bina; apply Nat.lt_irrefl in bina. assumption.
intuition. assumption.
Qed.

Theorem sole_sub_does_nothing : forall a t t2,
  ~ Contains (TVar a) t2 -> apply (sole_sub a t) t2 = t2.
Proof.
intros. induction t2.
- unfold apply. unfold sole_sub. destruct (Nat.eq_dec a t0).
  * rewrite e in H. pose (Here (TVar t0)). contradiction.
  * reflexivity.
- unfold apply. reflexivity.
- assert (~ Contains (TVar a) t2_1). intro. exact (H (InLeft _ _ _ H0)).
  assert (~ Contains (TVar a) t2_2). intro. exact (H (InRight _ _ _ H1)).
  apply IHt2_1 in H0. apply IHt2_2 in H1.
  rewrite apply_goes_into_tapp. rewrite H0. rewrite H1.
  reflexivity.
Qed.

Theorem occurs_check : forall a t,
  Contains (TVar a) t -> t = TVar a \/ forall s, ~ unifies s (TVar a) t.
Proof.
intros. induction H.
- left. reflexivity.
- right. intro. intro. unfold unifies in H0.
  rewrite apply_goes_into_tapp in H0. apply (map_containment s) in H.
  rewrite H0 in H.
  pose proof (impossible_loop H). pose InLeft. apply H1 in c. assumption.
  apply Here.
  intro. apply eq_sym in H2. apply bad_recursion_left in H2. assumption.
- right. intro. intro. unfold unifies in H0.
  rewrite apply_goes_into_tapp in H0. apply (map_containment s) in H.
  rewrite H0 in H.
  pose proof (impossible_loop H). pose InRight. apply H1 in c. assumption.
  apply Here.
  intro. apply eq_sym in H2. apply bad_recursion_right in H2. assumption.
Qed.

Definition bind (a : nat) (t : Tipe) :
  { s | unifies s (TVar a) t /\ isMGU s (TVar a) t } + { forall s, ~ unifies s (TVar a) t }.
refine (
  if contains_dec (TVar a) t then
    _
  else
    inleft _
).
- pose proof (occurs_check _ _ c). destruct t.
  * left. exists identity. dependent destruction c. 
    split. easy.
    unfold isMGU. intros. exists s'. intro. rewrite identity_does_nothing.
    reflexivity.
  * right. dependent destruction c.
  * right. destruct H. congruence. assumption.

- exists (sole_sub a t).
  assert (TVar a <> t). intro. rewrite H in n. exact (n (Here t)).
  split.
  * unfold unifies. rewrite sole_sub_works. rewrite sole_sub_does_nothing.
    reflexivity. assumption.
  * unfold isMGU. unfold unifies. intros. exists s'. intro.
    induction t0.
    + refine (if Nat.eq_dec a t0 then _ else _).
      rewrite <- e. rewrite H0. rewrite sole_sub_works. reflexivity.
      rewrite sole_sub_does_nothing. reflexivity.
      intro. dependent destruction H1. easy.
    + easy.
    + repeat rewrite apply_goes_into_tapp.
      rewrite <- IHt0_1. rewrite <- IHt0_2.
      reflexivity.
Defined.

Definition reverse_bind : forall a t,
   { s | unifies s (TVar a) t /\ isMGU s (TVar a) t } + { forall s, ~ unifies s (TVar a) t }
-> { s | unifies s t (TVar a) /\ isMGU s t (TVar a) } + { forall s, ~ unifies s t (TVar a) }.
Proof.
intros. destruct H.
- left. destruct s. destruct a0. exists x. split. easy.
  unfold isMGU. intros. unfold isMGU in H0. specialize H0 with s'. destruct H0.
  unfold unifies. unfold unifies in H1. apply eq_sym. assumption.
  exists x0. assumption.
- right. intro. intro. unfold unifies in H. apply eq_sym in H. apply n in H. assumption.
Defined.

Inductive less_tvars_or_size : Tipe -> Tipe -> Prop :=
  less_tvars : forall a b, (exists x, ~ Contains (TVar x) a /\ Contains (TVar x) b) -> less_tvars_or_size a b
| less_size : forall a b, (forall x, Contains (TVar x) a -> Contains (TVar x) a) -> size a < size b -> less_tvars_or_size a b.

Program Fixpoint unify (a : Tipe) (b : Tipe) {measure a (less_tvars_or_size)} :
  { s | unifies s a b /\ isMGU s a b } + { forall s, ~ unifies s a b } :=
match a, b with
  TConst x, TConst y => if string_dec x y then inleft identity else inright _
| TApp a1 a2, TApp b1 b2 =>
  match unify a1 b1 with
    inleft (exist _ s1 p1) => match unify (apply s1 a2) (apply s1 b2) with
      inleft (exist _ s2 p2) => inleft (sequence s2 s1)
    | inright fail => inright _
    end
  | inright fail => inright _
  end
| TVar a, t => bind a t
| t, TVar a => reverse_bind _ _ (bind a t)
| not, equal => inright _
end.

Next Obligation.
split;
[ compute; reflexivity
| unfold isMGU; intros; exists s'; intro;
  rewrite identity_does_nothing; reflexivity
].
Qed.

Next Obligation.
compute; intro; injection H0; assumption.
Qed.

Next Obligation.
apply less_size; [easy | apply contained_is_smaller ].
- apply InLeft. apply Here.
- apply bad_recursion_left.
Qed.

Lemma substitution_removes_tvars : forall s x,
  apply s x = x \/ exists a, ~ Contains (TVar a) (apply s x) /\ Contains (TVar a) x.
intros. .

Next Obligation.


Fixpoint unify (a : Tipe) (b : Tipe) :
  { s | unifies s a b /\ isMGU s a b } + { forall s, ~ unifies s a b }.
refine (
  match a, b with
    TConst x, TConst y => if string_dec x y then inleft _ else inright _
  | TApp a1 a2, TApp b1 b2 =>
    match unify a1 b1 with
      inleft (exist _ s1 p1) => match unify (apply s1 a2) (apply s1 b2) with
        inleft (exist _ s2 p2) => inleft _
      | inright fail => inright _
      end
    | inright fail => inright _
    end
  | TVar a, t => bind a t
  | t, TVar a => reverse_bind _ _ (bind a t)
  | not, equal => inright _
  end
).

(* TConst *)
- exists identity. split.
  * compute. rewrite e. reflexivity.
  * unfold isMGU. intros. exists s'. intros.
    pose proof identity_does_nothing. rewrite H0. reflexivity.
- compute. intro. intro. injection H. assumption.

(* mismatch *)
- intuition.
  unfold unifies in H. unfold apply in H. congruence.
- intuition. unfold unifies in H. simpl in H. congruence.

(* TApp *)
- exists (sequence s2 s1).
  pose proof sequence_application as unseq.
  pose proof apply_goes_into_tapp as distribute.
  split.
  * unfold unifies.
    assert (apply (sequence s2 s1) a1 = apply (sequence s2 s1) b1).
    rewrite unseq. rewrite unseq.
    destruct p1. unfold unifies in H. rewrite H.
    reflexivity.

    assert (apply (sequence s2 s1) a2 = apply (sequence s2 s1) b2).
    rewrite unseq. rewrite unseq.
    destruct p2. unfold unifies in H1. assumption.

    rewrite distribute. rewrite distribute.
    rewrite H. rewrite H0.
    reflexivity.

  * destruct p1. destruct p2. unfold isMGU. intros.
    unfold isMGU in H0. unfold isMGU in H2.
    unfold unifies in H3. repeat rewrite distribute in H3. injection H3.
    intros.
    unfold unifies in H0. apply H0 in H5. destruct H5.
    repeat rewrite H5 in H4. unfold unifies in H2. apply H2 in H4.
    destruct H4.
    exists x0. intro. rewrite unseq. rewrite <- H4. rewrite <- H5.
    reflexivity.

- unfold not. intros. unfold unifies in H.
  repeat rewrite apply_goes_into_tapp in H. injection H. intros.
  destruct p1. unfold isMGU in H3. apply H3 in H1. destruct H1.
  specialize fail with x. unfold unifies in fail. repeat rewrite <- H1 in fail.
  contradiction.

- unfold not. intros. unfold unifies in H. injection H. intros.
  apply fail in H1. assumption.
Defined.
