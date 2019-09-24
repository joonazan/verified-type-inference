From Coq Require Import Init.Prelude Unicode.Utf8.
From Coq Require Import String Arith.
Open Scope string_scope.
From Coq Require Import Program Lia List.
From Coq Require Import RelationClasses.

Definition name := string.
Definition tvarname := nat.

Inductive Tipe : Type :=
| TVar : tvarname -> Tipe
| TConst : name -> Tipe
| TApp : Tipe -> Tipe -> Tipe.

Definition tipe_dec (a : Tipe) (b : Tipe) : { a = b } + { ~ a = b }.
repeat decide equality.
Defined.
Definition Subst := nat -> Tipe.
Definition identity x := TVar x.
Definition sole_sub x t y :=
  if Nat.eq_dec x y then t else TVar y.

Fixpoint apply s t :=
match t with
| TVar x => s x
| TConst x => TConst x
| TApp a b => TApp (apply s a) (apply s b)
end.

Definition sequence (s2 : Subst) (s : Subst) := fun x => apply s2 (s x).

Definition unifies s a b := apply s a = apply s b.

Definition isMGU s a b := forall s', unifies s' a b
  -> exists delta, forall t, apply s' t = apply delta (apply s t).

Theorem identity_does_nothing : forall x, apply identity x = x.
induction x; auto.
cbn; congruence.
Qed.
Hint Resolve identity_does_nothing.

Theorem sole_sub_works : forall a t, apply (sole_sub a t) (TVar a) = t.
intros.
unfold sole_sub. cbn.
destruct (Nat.eq_dec a a); easy.
Qed.

Theorem sequence_application : forall x, forall u, forall v,
  apply (sequence v u) x = apply v (apply u x).
induction x; auto.
cbn; congruence.
Qed.

Theorem apply_goes_into_tapp : forall s, forall a, forall b,
  apply s (TApp a b) = TApp (apply s a) (apply s b).
easy.
Qed.

Inductive Contains : Tipe -> Tipe -> Prop :=
| Here : forall t, Contains t t
| InLeft : forall a t t2, Contains a t -> Contains a (TApp t t2)
| InRight : forall a t t2, Contains a t -> Contains a (TApp t2 t).

Hint Constructors Contains.
Notation "a <= b" := (Contains a b) (at level 70).

Program Instance Contains_Reflexive : Reflexive Contains.
Instance Contains_Transitive : Transitive Contains.
compute; intros.
induction H0; auto.
Qed.

Definition contains_dec t t2 : { t <= t2 } + { ~ t <= t2 }.
destruct (tipe_dec t t2).
- left. rewrite e. apply Here.
- induction t2.
  right; intro; now dependent destruction H.
  right; intro; now dependent destruction H.
  destruct (tipe_dec t t2_1).
  * rewrite e. auto.
  * apply IHt2_1 in n0. destruct n0.
    auto.
    destruct (tipe_dec t t2_2). rewrite e. auto.
    apply IHt2_2 in n1. destruct n1. auto.
    right. intro. dependent destruction H; contradiction.
Defined.

Theorem map_containment : forall s x t,
  x <= t -> apply s x <= apply s t.
  intros. induction H; auto;
  cbn; eauto using transitivity.
Qed.

Hint Resolve map_containment.

Fixpoint size x :=
match x with
| TVar _ => 1
| TConst _ => 1
| TApp a b => size a + size b
end.

Lemma size_is_nonzero : forall x, 0 < size x.
  induction x; cbn; lia.
Qed.

Lemma containment_to_size : forall a b,
    a <= b -> (size a <= size b)%nat.
  induction b; intro; dependent destruction H; auto.
  apply IHb1 in H; cbn; lia.
  apply IHb2 in H; cbn; lia.
Qed.

Theorem bad_recursion_left : forall a b, ~ TApp a b <= a.
  intuition.
  apply containment_to_size in H; cbn in H.
  pose proof size_is_nonzero b.
  lia.
Qed.

Theorem bad_recursion_right : forall a b, ~ TApp a b <= b.
  intuition.
  apply containment_to_size in H; cbn in H.
  pose proof size_is_nonzero a.
  lia.
Qed.

Theorem sole_sub_does_nothing : forall a t t2,
  ~ TVar a <= t2 -> apply (sole_sub a t) t2 = t2.
Proof.
intros. induction t2.
unfold sole_sub. simpl. destruct (Nat.eq_dec a t0). destruct e.
contradiction H. easy.
easy.
easy.
cbn. rewrite IHt2_1. rewrite IHt2_2. all: auto.
Qed.

Theorem occurs_check : forall a t,
  TVar a <= t -> TVar a = t \/ forall s, ~ unifies s (TVar a) t.
intros. induction H.
- left. reflexivity.
- right. intro. intro.
  apply (map_containment s) in H. rewrite H0 in H.
  now apply bad_recursion_left in H.
- right. intro. intro.
  apply (map_containment s) in H. rewrite H0 in H.
  now apply bad_recursion_right in H.
Qed.

Require Import ListSet.

Fixpoint variables x :=
match x with
| TVar a => [a]
| TConst _ => []
| TApp a b => set_union Nat.eq_dec (variables a) (variables b)
end.

Hint Constructors NoDup.

Lemma variables_nodup : forall x, NoDup (variables x).
  induction x; simpl; auto.
  apply set_union_nodup; auto.
Qed.

Notation "x ∈ S" := (set_In x S) (at level 20).
Notation "S1 ∪ S2" := (set_union Nat.eq_dec S1 S2) (at level 21, left associativity).
Notation "S1 ⊆ S2" := (incl S1 S2) (at level 20).

Lemma variables_spec : forall a x, TVar a <= x <-> a ∈ variables x.
  split; intro.
  induction x;
    dependent destruction H; simpl;
      auto using set_union_intro.
  induction x;
    cbn in H.
  destruct H. rewrite H. easy. easy.
  easy.
  apply set_union_elim in H; destruct H; auto.
Qed.

Lemma sole_sub_does_nothing3 : forall a b,
    ~ a = b -> forall x, apply (sole_sub a x) (TVar b) = TVar b.
  intros. unfold sole_sub. cbn.
  destruct Nat.eq_dec; easy.
Qed.

Lemma in_to_set_in : forall (x : nat) s, In x s = set_In x s.
  auto.
Qed.

Hint Resolve set_union_nodup.
Hint Resolve variables_nodup.

Ltac canonicalize_unify :=
  try intro;
  unfold unifies in *;

  try rewrite sole_sub_works in *;
  try rewrite in_to_set_in in *;
  try match goal with
      | |- context[apply _ (TApp _ _)] => rewrite apply_goes_into_tapp
      | H : context[apply _ (TApp _ _)] |- _ => rewrite apply_goes_into_tapp in H
      | |- context[apply identity] => rewrite identity_does_nothing
      | H : context[apply identity] |- _ => rewrite identity_does_nothing in H
      | |- context[sequence _ _] => rewrite sequence_application
      | H : context[sequence _ _] |- _ => rewrite sequence_application in H
      | |- set_In _ (_ ∪ _) => apply set_union_intro
      | H : set_In _ (_ ∪ _) |- _ => apply set_union_elim in H
      | H : ¬ TVar ?a <= ?x |- context[apply (sole_sub ?a _) ?x] =>
        rewrite (sole_sub_does_nothing _ _ _ H)
      | H : ¬ TVar ?a <= ?x, H2 : context[apply (sole_sub ?a _) ?x] |- _ =>
        rewrite (sole_sub_does_nothing _ _ _ H) in H2
      | H : ~ ?a = ?b |- context[apply (sole_sub ?a _) (TVar ?b)] => rewrite (sole_sub_does_nothing3 _ _ H)
      | |- _ /\ _ => split
      | H : _ /\ _ |- _ => destruct H
      | H : _ \/ _ |- _ => destruct H
      | H : _ ∈ (_ ∪ _) |- _ => destruct H
  end.

Ltac head t :=
  match t with
  | ?t' _ => head t'
  | _ => t
  end.

Ltac head_constructor t :=
  let t' := head t in is_constructor t'.

Ltac smasher canonicalize :=
  repeat (canonicalize);

  try eauto;
  try congruence;
  try lia;

  try match goal with
      | |- _ \/ _ =>
        first [(solve [left; smasher canonicalize])
              | (solve [right; smasher canonicalize])]
      | H : _ <= ?rhs |- _ =>
        head_constructor rhs;
        solve [dependent destruction H; smasher canonicalize]
      end.

Local Ltac smash := smasher canonicalize_unify.

Definition idempotent s := forall x, apply s (apply s x) = apply s x.

Lemma sole_sub_idempotent : forall a x, ~ TVar a <= x -> idempotent (sole_sub a x).
  intros. unfold idempotent.
  induction x0; smash.

  destruct (Nat.eq_dec a t). destruct e. smash.
  smash.
Qed.

(** MGUs can contain unnecessary cycles. An idempotent MGU won't.
    For example an identity MGU could just as well be
    [fun a => TVar (a+1)] or a cycle involving 0 1 and 2. *)

Notation minimal_MGU s a b := (unifies s a b /\ isMGU s a b /\ idempotent s).

Definition augment_sub s k (v : Tipe) a :=
  if Nat.eq_dec a k then
    v
  else
    s a.

Lemma augment_sub_hlp s k v x : ¬ TVar k <= x -> apply (augment_sub s k v) x = apply s x.
  induction x; smash.
  unfold augment_sub. simpl. destruct Nat.eq_dec. destruct H. rewrite e. smash.
  easy.

  cbn.
  rewrite IHx1. rewrite IHx2. reflexivity.
  all: smash.
Qed.

Lemma no_unnecessary_mappings s a b :
  minimal_MGU s a b ->
  forall v, ~ TVar v <= a -> ~ TVar v <= b -> s v = TVar v.
  smash.
  assert (forall t, exists d, forall x, apply s (apply (sole_sub v t) x) = apply d (apply s x)).
  intro. destruct (H0 (sequence s (sole_sub v t))).
  smash.
  exists x. intro. specialize H4 with x0. rewrite sequence_application in H4. auto.

  destruct (s v) eqn:?.
  destruct (Nat.eq_dec t v). congruence.

  unfold idempotent in H1. specialize H1 with (TVar v). cbn in H1. rewrite Heqt in H1. cbn in H1.
  destruct (H0 (augment_sub s v (TVar v))).
  unfold unifies. now repeat rewrite augment_sub_hlp.

  pose proof H5 (TVar v).
  pose proof H5 (TVar t).
  unfold augment_sub in *.
  cbn in *.
  destruct Nat.eq_dec.
  destruct Nat.eq_dec. contradiction.
  congruence. contradiction.

  destruct (H4 (TApp (TConst "") (TConst "")));
    specialize H5 with (TVar v); smash; cbn in H5; rewrite Heqt in H5; cbn in H5; smash.

  destruct (H4 (TConst ""));
    specialize H5 with (TVar v); smash; cbn in H5; rewrite Heqt in H5; cbn in H5; smash.
Qed.

Lemma hlp s x : apply s x = x -> forall a, TVar a <= x -> s a = TVar a.
  induction x; smash.
  simpl in H. injection H. smash.
Qed.

Lemma no_new_variables s a b :
  minimal_MGU s a b ->
  forall x v, TVar v <= apply s x -> TVar v <= a \/ TVar v <= b \/ TVar v <= x.
  intros.
  destruct (contains_dec (TVar v) a); smash.
  destruct (contains_dec (TVar v) b); smash.
  destruct (contains_dec (TVar v) x); smash.
  exfalso.

  destruct (H1 (sequence s (sole_sub v (TConst "")))); smash.

  pose proof H3 (TVar v).
  smash. cbn in H4.
  rewrite (no_unnecessary_mappings s a b) in H4; smash. cbn in H4.
  pose proof H3 x.
  smash.
  apply eq_sym in H5. pose proof hlp _ _ H5 v H0.
  congruence.
Qed.

Lemma idempotent_removes_from_all s :
  idempotent s ->
  forall a x, TVar a <= x -> ~ TVar a <= apply s x ->
  forall t, ~ TVar a <= apply s t.
  smash.
  apply (hlp s) in H2; smash.
  apply H1.
  rewrite <- H2.
  assert (s a = apply s (TVar a)). smash.
  rewrite H3.
  apply map_containment.
  smash.
Qed.

Lemma idempotent_occurs s : idempotent s -> forall t, TVar t <= s t -> s t = TVar t.
  intros.
  apply (hlp _ _ (H (TVar t))).
  smash.
Qed.

Lemma misses_var_dec s x :
  idempotent s ->
  {exists v, TVar v <= x /\ ~ TVar v <= apply s x} + {apply s x = x}.
  intro.
  induction x; simpl.

  destruct (contains_dec (TVar t) (s t)).
  right. apply idempotent_occurs; smash.
  left. exists t; smash.

  smash.

  destruct IHx1.
  left. destruct e.
  exists x. smash.
  dependent destruction H1;
    eapply (idempotent_removes_from_all _ H _ _ H0 H2); smash.

  destruct IHx2.
  left. destruct e0.
  exists x. smash.
  dependent destruction H1;
    eapply (idempotent_removes_from_all _ H _ _ H0 H2); smash.

  right; smash.
Qed.

Program Definition bind (a : nat) (t : Tipe) :
  { s | minimal_MGU s (TVar a) t } +
  { forall s, ~ unifies s (TVar a) t } :=
  if tipe_dec (TVar a) t then
    inleft (exist _ identity _)
  else
    if contains_dec (TVar a) t then
      inright _
    else
      inleft (exist _ (sole_sub a t) _).

Next Obligation.
  smash. exists s'. smash.
Qed.

Next Obligation.
  pose proof (occurs_check _ _ H0).
  smash.
Qed.

Next Obligation.
  smash.

  exists s'. intro.
  induction t0.
  destruct (Nat.eq_dec a t0).
  destruct e; smash. smash.
  easy.
  cbn. congruence.

  now apply sole_sub_idempotent.
Qed.

Lemma unifies_sym : forall s a b, unifies s a b -> unifies s b a.
easy.
Qed.
Hint Resolve unifies_sym.

Lemma isMGU_sym : forall s a b, isMGU s a b -> isMGU s b a.
  smash.
Qed.
Hint Resolve isMGU_sym.

Definition reverse_bind : forall a b,
    { s | minimal_MGU s a b } +
    { forall s, ~ unifies s a b }
    -> { s | minimal_MGU s b a } +
       { forall s, ~ unifies s b a }.
  intros. destruct H.
  left. destruct s. smash.
  right; smash.
Defined.

Inductive less_vars_or_size : nat * nat -> nat * nat -> Prop :=
| less_vars : forall v1 v2 s1 s2, v1 < v2 -> less_vars_or_size (v1, s1) (v2, s2)
| less_size : forall v1 v2 s1 s2, v1 ≤ v2 -> s1 < s2 -> less_vars_or_size (v1, s1) (v2, s2).
Hint Constructors less_vars_or_size.

Lemma less_vars_or_size_acc vars : forall size, Acc less_vars_or_size (vars, size).
  induction vars; intros.
  induction size0.

  apply Acc_intro; destruct y; intro;
    dependent destruction H; easy.

  apply Acc_intro; destruct y; intro;
    dependent destruction H. easy.

  apply le_n_0_eq in H. destruct H.
  destruct (Nat.eq_dec n0 size0). smash.
  eapply Acc_inv. apply IHsize0.
  apply less_size; smash.

  induction size0.
  apply Acc_intro. destruct y; intro; dependent destruction H.
  destruct (Nat.eq_dec n vars).
  rewrite e; easy.
  eapply Acc_inv.
  apply (IHvars 0).
  apply less_vars; smash.

  easy.

  apply Acc_intro; destruct y; intro; dependent destruction H.
  eauto using Acc_inv.
  destruct (Nat.eq_dec n (S vars)).

  rewrite e.
  destruct (Nat.eq_dec n0 size0). smash.
  eapply Acc_inv.
  apply IHsize0.
  apply less_size; smash.

  destruct (Nat.eq_dec n vars). rewrite e. auto.
  eapply Acc_inv.
  apply (IHvars 0).
  apply less_vars; smash.
Defined.

Lemma less_vars_or_size_wf : well_founded less_vars_or_size.
  unfold well_founded.
  destruct a.
  apply less_vars_or_size_acc.
Defined.

Program Fixpoint unify (a : Tipe) (b : Tipe)
        {measure (List.length (set_union Nat.eq_dec (variables a) (variables b)), size a) (less_vars_or_size) } :
  { s | minimal_MGU s a b } + { forall s, ~ unifies s a b } :=

match a, b with
|  TConst x, TConst y => if string_dec x y then inleft identity else inright _
| TApp a1 a2, TApp b1 b2 =>
  match unify a1 b1 with
    inleft (exist _ s1 p1) =>
      if tipe_dec a1 b1 then
        match unify a2 b2 with
        | inleft (exist _ s p) => inleft s
        | inright fail => inright _
        end
      else
        match unify (apply s1 a2) (apply s1 b2) with
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
  smash.
  exists s'; smash.
Qed.

Next Obligation.
  smash.
  injection H0.
  assumption.
Qed.

Ltac less_size_auto :=
  apply less_size;
  [ apply NoDup_incl_length; repeat (smash; simpl)
  | simpl;
    match goal with
    | [|- _ < size ?x + size ?y ] =>
      pose proof size_is_nonzero x;
      pose proof size_is_nonzero y
    end;
    smash
  ].

Next Obligation.
  less_size_auto.
Qed.

Next Obligation.
  less_size_auto.
Qed.

Next Obligation.
  smash.
  cbn. smash.
  destruct (i s').
  cbn in H; smash.
  exists x; smash.
Qed.

Next Obligation.
  smash.
Qed.


Lemma progress_proof_help s a1 a2 b1 b2 :
  minimal_MGU s a1 b1 ->
  (∃ v : tvarname, TVar v <= a2 ∧ ¬ TVar v <= apply s a2) ->
  length
    (variables (apply s a2) ∪ variables (apply s b2)) <
  length
    (variables a1 ∪ variables a2 ∪ (variables b1 ∪ variables b2)).

  intros.
  destruct H0.
  smash.

  destruct (Nat.eq_dec (Datatypes.length
    (variables (apply s a2) ∪ variables (apply s b2)))
  (Datatypes.length
    (variables (TApp a1 a2) ∪ variables (TApp b1 b2)))).
  apply eq_sym in e. apply Nat.eq_le_incl in e.
  eapply NoDup_length_incl in e.
  pose proof (e x).
  apply set_union_elim in H4; smash.
  rewrite <- variables_spec in H4. smash.
  rewrite <- variables_spec in H4.
  exfalso. eapply idempotent_removes_from_all. apply H3. apply H0. easy. eauto.

  simpl in *. rewrite variables_spec in H0. smash.
  smash.

  pose proof no_new_variables s a1 b1.
  unfold incl.
  smash.
  specialize H4 with a2 a.
  repeat rewrite <- variables_spec in *.
  destruct H4; smash.

  specialize H4 with b2 a.
  repeat rewrite <- variables_spec in *.
  destruct H4; smash.

  assert (forall a b, ~ a = b -> a ≤ b -> a < b). smash.
  apply H4; smash.
  apply NoDup_incl_length; smash.

  all: rewrite <- variables_spec in H5;
    apply (no_new_variables s a1 b1) in H5;
    repeat rewrite variables_spec in H5;
    smash.
Qed.

Lemma set_union_sym a b : NoDup a -> NoDup b -> length (a ∪ b) = length (b ∪ a).
  intros.
  assert ((a ∪ b) ⊆ (b ∪ a)). smash.
  assert ((b ∪ a) ⊆ (a ∪ b)). smash.
  apply NoDup_incl_length in H1; smash.
  apply NoDup_incl_length in H2; smash.
Qed.

Next Obligation.
  simpl.
  destruct (misses_var_dec s1 a2); smash.
  apply less_vars.
  apply progress_proof_help; smash.

  destruct (misses_var_dec s1 b2); smash.
  apply less_vars.
  rewrite set_union_sym; smash.
  rewrite (set_union_sym (variables a1 ∪ variables a2)); smash.
  apply progress_proof_help; smash.

  rewrite e.
  rewrite e0.
  less_size_auto.
Qed.

Next Obligation.
  smash. cbn. smash.

  cbn in *; injection H0; intros.
  destruct (i1 s'). auto.
  destruct (i x). smash.
  exists x0; smash.

  pose proof no_new_variables s2 (apply s1 a2) (apply s1 b2).

  destruct (misses_var_dec s1 (apply s2 (apply s1 x))); smash.
  exfalso. destruct e. smash.
  pose proof idempotent_removes_from_all _ i2 _ _ H1 H2.
  specialize H0 with (apply s1 x) x0. destruct H0. smash. smash.
  eapply H3; smash.
  destruct H0; eapply H3; smash.
Qed.

Next Obligation.
  smash.
  destruct (i s);
    injection H0; smash.
Qed.

Next Obligation.
  smash.
Qed.

Ltac stupid :=
match goal with
| [H : _ |- _] => solve [exfalso; eapply H; smash]
end.

Next Obligation.
  destruct a; destruct b; try stupid;
  unfold unifies; simpl; smash.
Qed.

Next Obligation.
  smash.
Qed.

Next Obligation.
  smash.
Qed.

Next Obligation.
  apply measure_wf.
  apply less_vars_or_size_wf.
Qed.

Extraction Inline unify_func.
Extraction Inline reverse_bind.
Extraction unify.
