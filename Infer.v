Load Unify.
From Hammer Require Import Reconstr.
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
rsimple (@identity_does_nothing) (@unifies_all, @isMGU_many, @Coq.Lists.List.In).
Qed.

Next Obligation. split.
unfold unifies_all. intros. unfold unifies. repeat rewrite sequence_application.
destruct H;
  rcrush Reconstr.Empty (@unifies_all, @unifies).

unfold isMGU_many. intros.
destruct (i0 s'). unfold unifies_all. intros. apply H. right; easy.
destruct (i x). unfold unifies. rexhaustive1 Reconstr.Empty (@Coq.Lists.List.In, @unifies_all, @unifies).
exists x0. intro. rewrite sequence_application. scrush.
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

Require Import FMapFacts Equalities.

Instance string_Equivalence : Equivalence eq (A := string) := {}.

Module string_EQ <: DecidableType.
  Definition t := string.
  Definition eq := eq (A := t).
  Definition eq_equiv := string_Equivalence.
  Definition eq_dec := string_dec.
End string_EQ.

Module old_string_EQ := Backport_DT string_EQ.
Module Infer (Map : WSfun old_string_EQ).
Module MF := WFacts_fun old_string_EQ Map.

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
Lemma singleton_MapsTo : forall k v, Map.MapsTo k v (singleton k v).
intros. compute. apply Map.add_1. reflexivity.
Qed.
Lemma singleton_MapsTo_one_thing : forall a b c d, Map.MapsTo a b (singleton c d) -> a = c /\ b = d.
intros.
destruct (string_dec a c); destruct (eq_dec b d).
  auto.
  assert (Map.MapsTo a d (singleton c d)). apply Map.add_1. easy.
    apply Map.find_1 in H. apply Map.find_1 in H0. rewrite H in H0.
    injection H0. auto.
  all: apply Map.add_3 in H; [ apply Map.empty_1 in H; contradiction | auto ].
Qed.

Lemma MapsTo_in_values {A} : forall k v m, Map.MapsTo k v m -> In v (values (A := A) m).
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

Definition typing : Type := Tipe * Env.

Inductive well_typed : expression -> typing -> Prop :=
| wt_Var : forall name env t,
    Map.find name env = Some t -> well_typed (Var name) (t, env)
| wt_Lambda : forall name body env argt returnt,
    well_typed body (returnt, Map.add name argt env) -> well_typed (Lambda name body) (argt '-> returnt, env)
| wt_Call : forall f x argt returnt env,
    well_typed f (argt '-> returnt, env) -> well_typed x (argt, env) -> well_typed (Call f x) (returnt, env).

Lemma equal_env_wt : forall e t env env2,
  well_typed e (t, env) -> Map.Equal env env2 -> well_typed e (t, env2).
induction e.
  intros. dependent destruction H. apply wt_Var. rewrite H0 in H. assumption.
  intros. dependent destruction H. apply wt_Lambda.
    apply (IHe returnt (Map.add n argt env)). assumption. compute. intros.
    destruct (string_dec y n).
      repeat rewrite MF.add_eq_o. easy. easy. easy.
      repeat rewrite MF.add_neq_o. auto. auto. auto.
  intros. dependent destruction H. apply (wt_Call e1 e2 argt).
    apply (IHe1 (argt '-> t) env). assumption. assumption.
    apply (IHe2 argt env). assumption. assumption.
Qed.

Definition most_general_type e (t : typing) := forall t2, well_typed e t2
  -> exists s, (apply s (fst t) = fst t2
  /\ forall x a, Map.find x (snd t) = Some a -> Map.find x (snd t2) = Some (apply s a)).

Definition typing_with_varcount : Type := typing * nat.

Inductive typing_nvars : typing_with_varcount -> Prop :=
  mk_typing_nvars : forall t e (n : nat),
  vars_below n t /\ (forall t2, In t2 (values e) -> vars_below n t2)
  -> typing_nvars (t, e, n).

Fixpoint add_to_tvars x t :=
match t with
| TVar y => TVar (x + y)
| TConst a => TConst a
| TApp a b => TApp (add_to_tvars x a) (add_to_tvars x b)
end.

Definition unifies_typings s a b :=
    unifies s (fst a) (fst b) /\
    forall k v1 v2,
      Map.MapsTo k v1 (snd a) -> Map.MapsTo k v2 (snd b) -> unifies s v1 v2.

Definition typing_MGU s a b :=
  unifies_typings s a b /\
  forall s',
    unifies_typings s' a b ->
    exists diff,
    forall t, apply s' t = apply diff (apply s t).

Definition try_pair {t} (a b : option t) : option (t * t) :=
  match a, b with
  | Some a', Some b' => Some (a', b')
  | _, _ => None
  end.

Program Definition unify_typings (t1 t2 : typing) :
  { s | typing_MGU s t1 t2 } + { forall s, ~ unifies_typings s t1 t2 } :=
  let pairs := values (Map.map2 try_pair (snd t1) (snd t2)) in
  match unify_many ((fst t1, fst t2) :: pairs) with
  | inleft s => inleft s
  | inright _ => inright _
  end.

Next Obligation.
split.
unfold unifies_typings.
split.
apply u. intuition.

intros.
apply u.
cbn. right.
Admitted.

Next Obligation.
Admitted.
  
Program Fixpoint infer (e : expression) {measure (esize e)} :
  { t | well_typed e (fst t) /\ most_general_type e (fst t) /\ typing_nvars t} + { forall t, ~ well_typed e t } :=
match e with
| Var a => inleft (TVar 0, (singleton a (TVar 0)), 1)
| Lambda x b =>
  match infer b with
  | inleft (exist _ (t, env, n) _) =>
    match Map.find x env with
    | Some argt => inleft (argt '-> t, Map.remove x env, n)
    | None => inleft (TVar n '-> t, env, (S n))
    end
  | inright _ => inright _
  end
| Call f x =>
  match infer f with
  | inleft (exist _ (f_t, f_env, f_n) _) =>
    match infer x with
    | inleft (exist _ (x_t_, x_env_, x_n_) _) =>
      let x_t := add_to_tvars f_n x_t_ in
      let x_env := Map.map (add_to_tvars f_n) x_env_ in
      let x_n := x_n_ + f_n in
      let (env, pairs) := merge_envs [f_env; x_env] in
      let return_value := TVar x_n in
      match unify_many ((f_t, x_t '-> return_value) :: pairs) with
      | inleft _ s => inleft (apply s return_value, Map.map (apply s) env, S x_n)
      | _ => inright _
      end
    | _ => inright _
    end
  | _ => inright _
  end
end.

Next Obligation. split.
apply wt_Var. apply Map.find_1. apply singleton_MapsTo.

split.
unfold most_general_type. intros. dependent destruction H. simpl.
exists (sole_sub 0 t). split. easy.
intros. apply Map.find_2 in H0. apply singleton_MapsTo_one_thing in H0. destruct H0. destruct H0. rewrite H1.
easy.

apply mk_typing_nvars.
split; [ | intros; apply values_in_map in H; destruct H;
  apply singleton_MapsTo_one_thing in H; destruct H; rewrite H0 ].
compute; intros; dependent destruction H; easy.
compute. intros. dependent destruction H1. easy.
Qed.

Next Obligation. split.
apply wt_Lambda. apply (equal_env_wt b t env). assumption.
unfold Map.Equal. intro. destruct (string_dec x y).
  rewrite MF.add_eq_o. congruence. assumption.
  rewrite MF.add_neq_o. rewrite MF.remove_neq_o. reflexivity. assumption. assumption.

split.
unfold most_general_type. intros.
destruct t2. simpl. dependent destruction H. apply m in H. destruct H. simpl in H.
destruct H.
exists x0. split.
  rewrite H. apply eq_sym in Heq_anonymous. apply H0 in Heq_anonymous.
  rcrush (@Infer.MF.add_eq_o) (@Map.key, @Infer.Env, @name).

  intros. destruct(old_string_EQ.eq_dec x x1).
    rewrite MF.remove_eq_o in H1; easy.
    rewrite MF.remove_neq_o in H1. apply H0 in H1.
    rewrite MF.add_neq_o in H1; easy. easy.

apply mk_typing_nvars. dependent destruction t0. destruct a. split.
unfold vars_below. intros. dependent destruction H. dependent destruction H.
  dependent destruction H. apply v0 in H. assumption. apply (MapsTo_in_values x argt env). apply MF.find_mapsto_iff. auto. auto.
intros. apply v0. apply values_in_map in H. destruct H. apply Map.remove_3 in H. apply MapsTo_in_values in H.
assumption.
Qed.

Next Obligation. split.
apply wt_Lambda.
(* prove that unique extra variable is harmless *) give_up.

split.
unfold most_general_type. intros.
dependent destruction H. apply m in H. destruct H. simpl in H. simpl.
destruct H.
  exists x0. split.
  rewrite H. give_up.

  intros. destruct(old_string_EQ.eq_dec x x1);
    reasy (@Infer.MF.add_neq_o) (@name, @Map.key).

dependent destruction t0. destruct a. split. split.
  unfold vars_below. intros. dependent destruction H. dependent destruction H. dependent destruction H.
    dependent destruction H. omega.
    apply v in H. auto.
  intros. apply v0 in H. unfold vars_below. intros. unfold vars_below in H. apply H in H0. omega.
Admitted.

Next Obligation.
scrush.
Qed.

Next Obligation.
simpl. pose proof (esize_is_nonzero x). omega.
Qed.

Next Obligation.
simpl. pose proof (esize_is_nonzero f). omega.
Qed.

Next Obligation.
split.
apply (wt_Call f x x_t_).
pose proof (u f_t (add_to_tvars f_n x_t_ '-> TVar (x_n_ + f_n))).
unfold unifies in H.
simpl in H.
