Load Unify.
Open Scope string_scope.

Definition uncurry {A B C} (f : A -> B -> C) (x : A * B) :=
  match x with (a, b) => f a b end.

Definition unifies_all s xs :=
  forall a b, In (a, b) xs -> unifies s a b.

Definition isMGU_many s xs := forall s', unifies_all s' xs
  -> exists delta, forall t, apply s' t = apply delta (apply s t).

Program Fixpoint unify_many (xs : list (Tipe * Tipe)) {measure (length xs)} :
  {s : Subst | unifies_all s xs /\ isMGU_many s xs } + {forall s, ~ unifies_all s xs} :=
match xs with
| [] => inleft identity
| (a, b) :: t =>
  match unify_many t with
  | inleft s =>
    match unify (apply s a) (apply s b) with
    | inleft s2 => inleft (sequence s2 s)
    | inright _ => inright _
    end
  | inright _ => inright _
  end
end.

Next Obligation.
unfold unifies_all. intuition.
unfold isMGU_many. intros. exists s'. intro. rewrite identity_does_nothing. easy.
Qed.

Next Obligation. split.
unfold unifies_all. intros. unfold unifies. repeat rewrite sequence_application.
destruct H.
  injection H. intros. destruct H1. destruct H0. easy.
  apply u0 in H. destruct H. reflexivity.

unfold isMGU_many. intros.
destruct (i0 s'). unfold unifies_all. intros. apply H. right; easy.
destruct (i x). unfold unifies. repeat rewrite <- H0. rewrite (H a b). easy.
  left; easy.
exists x0. intro. rewrite sequence_application. rewrite <- H1. rewrite <- H0. reflexivity.
Qed.

Lemma uncons_unifies_all : forall s a b t, unifies_all s ((a, b) :: t) -> unifies s a b /\ unifies_all s t.
intros. split.
  apply H. left. easy.
  unfold unifies_all. intros. apply H. right. easy.
Qed.

Next Obligation.
intro. apply uncons_unifies_all in H. destruct H.
destruct (i s0). assumption. apply (wildcard' x).
unfold unifies. repeat rewrite <- H1. easy.
Qed.

Next Obligation.
intro. unfold unifies_all in H.
apply (wildcard' s). unfold unifies_all. intros. apply H. right. assumption.
Qed.

Require Import FMapInterface Equalities.

Instance string_Equivalence : Equivalence eq (A := string) := {}.

Module string_EQ <: DecidableType.
  Definition t := string.
  Definition eq := eq (A := t).
  Definition eq_equiv := string_Equivalence.
  Definition eq_dec := string_dec.
End string_EQ.

Module old_string_EQ := Backport_DT string_EQ.
Module Infer (Map : WSfun old_string_EQ).

Definition unify_sets sets : list (Tipe * Tipe) :=
let set_to_pairs set :=
  match set with
  | [] => []
  | h :: t => map (fun x => (h, x)) t
  end
in
  concat (map set_to_pairs sets).

Definition nonempty_list A := { xs : list A | xs <> [] }.
Program Definition head_nonempty {A} (xs : nonempty_list A) : A :=
match xs with [] => _ | h :: t => h end.
Next Obligation.
destruct xs. compute in Heq_xs. congruence.
Qed.
Definition to_normal_list {A} (xs : nonempty_list A) := proj1_sig xs.

Program Definition cons_option (acc : option (nonempty_list Tipe)) (x : option Tipe) : option (nonempty_list Tipe) :=
match acc, x with
| Some acc', Some x' => Some (x' :: acc')
| Some acc', None => Some acc'
| None, Some x' => Some [x']
| None, None => None
end.

Definition Env := Map.t Tipe.
Definition values {A} (m : Map.t A) : list A := map snd (Map.elements m).
Definition singleton a (x : Tipe) := Map.add a x (Map.empty _).
Lemma singleton_values : forall n a b, In b (values (singleton n a)) -> a = b.
intros. pose proof Map.elements_2. specialize H0 with Tipe (singleton n a) n b.
destruct (eq_dec a b). assumption.
pose proof Map.add_3. Admitted.

Lemma MapsTo_in_values {A} : forall v m k, Map.MapsTo k v m -> In v (values (A := A) m).
intros. unfold values. apply Map.elements_1 in H.
Admitted.

Lemma values_in_map {A} : forall v m, In v (values (A := A) m) -> exists k, Map.MapsTo k v m.
Admitted.

Definition merge_envs (envs : list Env) : Env * list (Tipe * Tipe) :=
let
  merged := fold_left (Map.map2 cons_option) envs (Map.empty _)
in
  (Map.map head_nonempty merged
  , unify_sets (map to_normal_list (values merged))
  ).

Inductive expression :=
| Var : name -> expression
| Lambda : name -> expression -> expression
| Call : expression -> expression -> expression.

Fixpoint esize e :=
match e with
| Lambda _ e2 => S (esize e2)
| Call a b => esize a + esize b
| _ => 1
end.
Lemma esize_is_nonzero : forall e, 0 < esize e.
induction e. auto. simpl. auto. simpl. intuition.
Qed.

Notation "a '-> b" := (TApp (TApp (TConst "->") a) b) (at level 59, right associativity).

Definition vars_below n t := forall v, Contains (TVar v) t -> v < n.

Inductive typing :=
  mk_typing : forall t e (n : nat),
  vars_below n t /\ (forall t2, In t2 (values e) -> vars_below n t2)
  -> typing.

Fixpoint add_to_tvars x t :=
match t with
| TVar y => TVar (x + y)
| TConst a => TConst a
| TApp a b => TApp (add_to_tvars x a) (add_to_tvars x b)
end.

Program Fixpoint infer (e : expression) {measure (esize e)} : option typing :=
match e with
| Var a => Some (mk_typing (TVar 0) (singleton a (TVar 0)) 1 _)
| Lambda x b =>
  match infer b with
  | Some (mk_typing t env n _) =>
    match Map.find x env with
    | Some argt => Some (mk_typing (argt '-> t) (Map.remove x env) n _)
    | None => Some (mk_typing (TVar n '-> t) env (S n) _)
    end
  | None => None
  end
| Call f x =>
  match infer f, infer x with
  | Some (mk_typing f_t f_env f_n _), Some (mk_typing x_t_ x_env_ x_n _) =>
    let x_t := add_to_tvars f_n x_t_ in
    let x_env := Map.map (add_to_tvars f_n) x_env_ in
    let (env, pairs) := merge_envs [f_env; x_env] in
    let return_value := TVar (f_n + x_n) in
    match unify_many ((f_t, x_t '-> return_value) :: pairs) with
    | inleft _ s => Some (mk_typing (apply s return_value) (Map.map (apply s) env) (S (f_n + x_n)) _)
    | _ => None
    end
  | _, _ => None
  end
end.

Next Obligation.
split; [ | intros; apply singleton_values in H; destruct H ].
all: compute; intros; dependent destruction H; easy.
Qed.

Next Obligation.
apply eq_sym in Heq_anonymous. apply Map.find_2 in Heq_anonymous. apply MapsTo_in_values in Heq_anonymous.
apply v0 in Heq_anonymous.
split.
unfold vars_below. intros. dependent destruction H. dependent destruction H.
  dependent destruction H. auto. auto.
intros. apply v0. apply values_in_map in H. destruct H. apply Map.remove_3 in H. apply MapsTo_in_values in H.
assumption.
Qed.

Next Obligation.
split.
  unfold vars_below. intros. dependent destruction H. dependent destruction H. dependent destruction H.
    dependent destruction H. omega.
    apply v in H. auto.
  intros. apply v0 in H. unfold vars_below. intros. unfold vars_below in H. apply H in H0. omega.
Qed.

Next Obligation.
simpl. pose proof (esize_is_nonzero x). omega.
Qed.

Next Obligation.
simpl. pose proof (esize_is_nonzero f). omega.
Qed.

Next Obligation.
Admitted.