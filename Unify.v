Require Import String Arith.
Require Import Program Omega List ListSet.

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
Hint Resolve identity_does_nothing.

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

Hint Constructors Contains.

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

Definition unifying_subst s source :=
  ((forall x, apply s x = x) \/ exists a, Contains (TVar a) source /\ forall x, ~ Contains (TVar a) (apply s x))
  /\ forall a x, Contains (TVar a) (apply s x) -> (Contains (TVar a) source \/ Contains (TVar a) x).

Definition less_vars a b :=
  (exists x, ~ Contains (TVar x) a /\ Contains (TVar x) b)
  /\ forall v, Contains (TVar v) a -> Contains (TVar v) b.

Definition bind (a : nat) (t : Tipe) :
  { s | unifies s (TVar a) t /\ isMGU s (TVar a) t /\ unifying_subst s (TApp (TVar a) t) } + { forall s, ~ unifies s (TVar a) t }.
refine (
  if contains_dec (TVar a) t then
    _
  else
    inleft _
).
- pose proof (occurs_check _ _ c). destruct t.
  * left. exists identity. dependent destruction c. 
    split. easy. split.
    unfold isMGU. intros. exists s'. intro. rewrite identity_does_nothing.
    reflexivity.
    unfold unifying_subst. split.
    left. apply identity_does_nothing.
    intros. right. rewrite identity_does_nothing in H0.  assumption.
  * right. dependent destruction c.
  * right. destruct H. congruence. assumption.

- exists (sole_sub a t).
  assert (TVar a <> t). intro. rewrite H in n. exact (n (Here t)).
  split; [idtac | split].
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
  * unfold unifying_subst. split.
    right. exists a. split.
    auto.
    intro. induction x.
    + pose (Nat.eq_dec a t0). destruct s.
      rewrite <- e. rewrite sole_sub_works. assumption.
      rewrite sole_sub_does_nothing.
      all: (intro; dependent destruction H0; contradiction).
    + now compute.
    + rewrite apply_goes_into_tapp. intro. dependent destruction H0.
      contradiction. contradiction.
  + intros. induction x.
    pose (Nat.eq_dec a0 t0). destruct s.
    rewrite e. auto.
    left. pose (Nat.eq_dec a t0). destruct s.
    destruct e. rewrite sole_sub_works in H0. auto.
    rewrite sole_sub_does_nothing in H0. dependent destruction H0. contradiction.
    intro. dependent destruction H1. contradiction.
    compute in H0. dependent destruction H0.
    rewrite apply_goes_into_tapp in H0. dependent destruction H0.
    apply IHx1 in H0. destruct H0. auto. auto.
    apply IHx2 in H0. destruct H0. auto. auto.
Defined.

Definition reverse_bind : forall a b t,
   { s | unifies s (TVar a) t /\ isMGU s (TVar a) t /\ unifying_subst s (TApp (TVar a) b) } + { forall s, ~ unifies s (TVar a) t }
-> { s | unifies s t (TVar a) /\ isMGU s t (TVar a) /\ unifying_subst s (TApp b (TVar a)) } + { forall s, ~ unifies s t (TVar a) }.
Proof.
intros. destruct H.
- left. destruct s. destruct a0. destruct H0. exists x. split. easy. split.
  unfold isMGU. intros. unfold isMGU in H0. specialize H0 with s'. destruct H0.
  unfold unifies. unfold unifies in H1. apply eq_sym. assumption.
  exists x0. assumption.
  destruct H1. unfold unifying_subst. split. destruct H1. auto.
  destruct H1. destruct H1. right. exists x0. split. dependent destruction H1. auto. auto.
  assumption. intros. apply H2 in H3. destruct H3. left. dependent destruction H3. auto. auto. auto.
- right. intro. intro. unfold unifies in H. apply eq_sym in H. apply n in H. assumption.
Defined.

Definition le_n_vars n t :=
  exists vars, List.length vars = n /\ (forall a, Contains (TVar a) t -> set_In a vars).

Lemma removing_shortens : forall n a s,
  set_In a s -> List.length s = S n -> List.length (set_remove Nat.eq_dec a s) = n.
fix rec 1. intros.
destruct s. easy.
pose (Nat.eq_dec n0 a). destruct s0.
  rewrite e. simpl. destruct Nat.eq_dec. auto. easy.
  simpl. destruct Nat.eq_dec. auto. simpl. destruct n.
    destruct H. easy.
    simpl in H0. destruct s. destruct H. simpl in H0. easy.
  apply eq_S. destruct H. easy. apply rec. assumption.
    simpl in H0. auto.
Defined.

Inductive less_tvars_or_size : nat * Tipe -> nat * Tipe -> Prop :=
| less_tvars : forall n a a', less_tvars_or_size (n, a) (S n, a')
| less_size_l : forall n a b, less_tvars_or_size (n, a) (n, TApp a b)
| less_size_r : forall n a b, less_tvars_or_size (n, a) (n, TApp b a).

Program Fixpoint unify (n : nat) (a : Tipe) (b : Tipe) (nvars : le_n_vars n (TApp a b)) {measure (n, a) (less_tvars_or_size) } :
  { s | unifies s a b /\ isMGU s a b /\ unifying_subst s (TApp a b) } + { forall s, ~ unifies s a b } :=

match a, b with
  TConst x, TConst y => if string_dec x y then inleft identity else inright _
| TApp a1 a2, TApp b1 b2 =>
  match unify n a1 b1 _ with
    inleft (exist _ s1 p1) =>
      if eq_dec a1 b1 then
        match unify n a2 b2 _ with
        | inleft (exist _ s p) => inleft s
        | inright fail => inright _
        end
      else
        match unify (n - 1) (apply s1 a2) (apply s1 b2) _ with
          inleft (exist _ s2 p2) => inleft (sequence s2 s1)
        | inright fail => inright _
        end
  | inright fail => inright _
  end
| TVar a, t => bind a t
| t, TVar a => reverse_bind _ _ _ (bind a t)
| not, equal => inright _
end.

Next Obligation.
split; [compute; reflexivity | split].
unfold isMGU; intros; exists s'; intro;
  rewrite identity_does_nothing; reflexivity.
unfold unifying_subst. split. auto.
intros. right. rewrite identity_does_nothing in H. assumption.
Qed.

Next Obligation.
compute; intro; injection H0; assumption.
Qed.

Ltac dd :=
match goal with
| [H : _ |- _] => dependent destruction H; [auto | auto]
end.

Next Obligation.
destruct nvars.
destruct H.
unfold le_n_vars.
exists x. split. assumption.
intros. dd.
Qed.

Next Obligation.
apply less_size_l.
Qed.

Next Obligation.
destruct nvars. destruct a. exists x. split. assumption.
  intros. apply s. dd.
Qed.

Next Obligation.
apply less_size_r.
Qed.

Next Obligation.
unfold unifies. unfold unifies in u.
intuition.
- repeat rewrite apply_goes_into_tapp. rewrite u. reflexivity.
- unfold isMGU. intros. unfold isMGU in i.
  unfold unifies in H. repeat rewrite apply_goes_into_tapp in H. injection H. intros. apply i in H0.
  destruct H0. exists x. assumption.
- unfold unifying_subst. destruct u0. split. destruct o. left. assumption.
  right. destruct e. destruct a. exists x. split. dd. assumption.
  intros. apply o0 in H. destruct H. dd. auto.
Qed.

Next Obligation.
unfold unifies. repeat rewrite apply_goes_into_tapp. intro. injection H. intro.
apply fail in H0. assumption.
Qed.

Next Obligation.
destruct u0. destruct o. unfold unifies in u. pose proof u. repeat rewrite e in H0. contradiction.
destruct n. destruct nvars. destruct a. destruct x. destruct e. destruct a.
  exfalso. pose proof (s x). apply H0. dd.
  easy.
simpl. rewrite <- minus_n_O.
unfold le_n_vars. destruct e. destruct a. destruct nvars.
exists (set_remove Nat.eq_dec x x0). destruct a. split. apply removing_shortens.
  apply s. dd.
  assumption.
intros. pose (Nat.eq_dec a x). rewrite <- apply_goes_into_tapp in H0. destruct s0.
  rewrite e0 in H0. apply n0 in H0. easy.
  apply set_remove_3. apply s. apply o0 in H0. destruct H0. dd. dd. assumption.
Qed.

Lemma subst_sequencing_variable_loss : forall s1 s2 a1 a2 b1 b2,
  unifying_subst s1 (TApp a1 b1) -> unifying_subst s2 (TApp (apply s1 a2) (apply s1 b2))
-> unifying_subst (sequence s2 s1) (TApp (TApp a1 a2) (TApp b1 b2)).
Proof.
intros. destruct H. destruct H0. unfold unifying_subst. split.
destruct H; destruct H0.
left. intro. rewrite sequence_application. rewrite H. easy.
right. destruct H0. exists x. destruct H0. split.
repeat rewrite H in H0. dd.
intro. rewrite sequence_application. easy.
right. destruct H. destruct H. exists x. split. dd.
intro. rewrite sequence_application. rewrite H0. easy.
right. destruct H0. destruct H0. exists x. split.
dependent destruction H0.
  apply H1 in H0; destruct H0;[dd | auto].
  apply H1 in H0; destruct H0;[dd | auto].
intro. rewrite sequence_application. easy.

intros. rewrite sequence_application in H3.
pose (H2 _ _ H3). destruct o.
dependent destruction H4.
all: apply H1 in H4; destruct H4; [ dd | auto].
Qed.

Next Obligation.
destruct n. destruct nvars. destruct x. destruct a.
  destruct u0. destruct o. pose proof u. unfold unifies in H0. repeat rewrite e0 in H0. contradiction.
  destruct e0. destruct a. exfalso. pose proof (s x). apply H0. dd.
  destruct a; easy.
simpl. rewrite <- minus_n_O. apply less_tvars.
Qed.

Next Obligation.
unfold unifies. unfold unifies in u. unfold unifies in u1.
intuition.
- repeat rewrite apply_goes_into_tapp. repeat rewrite sequence_application.
  rewrite u1. rewrite u. reflexivity.
- unfold isMGU. intros. unfold isMGU in i. unfold isMGU in i0.
  unfold unifies in H0. repeat rewrite apply_goes_into_tapp in H0. injection H0. intros. apply i0 in H2.
  destruct H2.
  repeat rewrite H2 in H1. apply i in H1. destruct H1.
  exists x0. intro. rewrite sequence_application. rewrite <- H1. rewrite H2. reflexivity.
- apply subst_sequencing_variable_loss. assumption. assumption.
Qed.

Next Obligation.
intro. injection H0. intros. apply i in H2. destruct H2. repeat rewrite H2 in H1. apply fail in H1.
assumption.
Qed.

Next Obligation.
intro. unfold unifies in H. simpl in H. injection H. intros. apply fail in H1. assumption.
Qed.

(** failure case *)
Next Obligation.
intro. destruct a.
refine (H0 _ _ _). easy.
destruct b.
  refine (H1 _ _ _). easy.
  refine (H2 _ _ _). easy.
  unfold unifies in H3. simpl in H3. congruence.
destruct b.
  now refine (H1 _ _ _).
  compute in H3. congruence.
  now refine (H _ _ _ _ _).
Qed.

Next Obligation.
repeat split. all: easy.
Qed.

Next Obligation.
repeat split. all: easy.
Qed.

Lemma less_tvars_or_size_wf : forall n x, Acc less_tvars_or_size (n, x).
fix less_vars_rec 1.
intros.
destruct n.

induction x.
  apply Acc_intro. intros. dependent destruction H.
  apply Acc_intro. intros. dependent destruction H.
  apply Acc_intro. intros. dependent destruction H. assumption. assumption.

induction x. all: apply Acc_intro; intros; dependent destruction H.
  apply less_vars_rec. apply less_vars_rec. apply less_vars_rec.
  assumption. assumption.
Qed.

Next Obligation.
unfold well_founded. intros.
pose proof less_tvars_or_size_wf. destruct a. destruct s. specialize H with x x0. destruct H.
apply Acc_intro. intros. destruct y. destruct s0. specialize H with (x1, x2).
Qed.