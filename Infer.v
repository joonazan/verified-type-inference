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

Lemma try_pair_some : forall t a b c d,
    try_pair (t := t) a b = Some (c, d) -> a = Some c /\ b = Some d.
intros.
destruct a eqn:?. destruct b eqn:?.
cbn in H.
injection H.
intros.
split; congruence.
all: cbn in H; congruence.
Qed.

Program Definition unify_typings (t1 t2 : typing) :
  { s | typing_MGU s t1 t2 } + { forall s, ~ unifies_typings s t1 t2 } :=
  let pairs := values (Map.map2 try_pair (snd t1) (snd t2)) in
  match unify_many ((fst t1, fst t2) :: pairs) with
  | inleft s => inleft s
  | inright _ => inright _
  end.

Lemma unifies_all_typings_equiv : forall s t t2 e e2,
  unifies_all s ((t, t2) :: values (Map.map2 try_pair e e2)) <->
  unifies_typings s (t, e) (t2, e2).
split.
intros.
unfold unifies_typings. cbn.
split.
apply H.
left. easy.
intros.
apply Map.find_1 in H0.
apply Map.find_1 in H1.
apply H. cbn. right.
rewrite In_values_MapsTo_equiv. exists k.
apply Map.find_2.
rewrite Map.map2_1.
rewrite H0. rewrite H1. easy.
left. rewrite MF.in_find_iff. congruence.

unfold unifies_all.
intros.
destruct H. cbn in *.
destruct H0.
injection H0. intros. rewrite <- H2. rewrite <- H3. easy.
rewrite In_values_MapsTo_equiv in H0. destruct H0.
apply Map.find_1 in H0.
rewrite MF.map2_1bis in H0.
apply try_pair_some in H0.
destruct H0.
apply (H1 x); apply Map.find_2; easy.
easy.
Qed.

Inductive well_typed : expression -> Tipe -> Env -> Prop :=
| wt_Var : forall name env t,
    Map.MapsTo name t env -> well_typed (Var name) t env
| wt_Lambda : forall name body env argt returnt,
    well_typed body returnt (Map.add name argt env) -> well_typed (Lambda name body) (argt '-> returnt) env
| wt_Call : forall f x argt returnt env,
    well_typed f (argt '-> returnt) env -> well_typed x argt env -> well_typed (Call f x) (returnt) env.

Lemma well_typed_proper : forall e t env env2,
  Map.Equal env env2 -> well_typed e t env -> well_typed e t env2.
induction e.
  intros. dependent destruction H0. apply wt_Var. rewrite MF.Equal_mapsto_iff in H. apply H. easy.
  intros. dependent destruction H0. apply wt_Lambda.
    apply (IHe returnt (Map.add n argt env)).
    compute. intro. rewrite H. reflexivity. assumption. 
  intros. dependent destruction H0. apply (wt_Call e1 e2 argt).
    apply (IHe1 (argt '-> returnt) env); assumption.
    apply (IHe2 argt env); assumption.
Qed.

Definition most_general_type e (t : typing) :=
  well_typed e (fst t) (snd t) /\
  forall t2,
    well_typed e (fst t2) (snd t2) ->
    exists s,
      (apply s (fst t) = fst t2 /\
       forall x a, Map.MapsTo x a (snd t) -> Map.MapsTo x (apply s a) (snd t2)).

Definition typing_with_varcount : Type := typing * nat.

Definition typing_nvars (tup : typing_with_varcount) : Prop :=
  match tup with
    (t, e, n) =>
    vars_below n t /\ (forall t2, In t2 (values e) -> vars_below n t2)
  end.

Fixpoint add_to_tvars x t :=
match t with
| TVar y => TVar (x + y)
| TConst a => TConst a
| TApp a b => TApp (add_to_tvars x a) (add_to_tvars x b)
end.

Next Obligation.
destruct t1. destruct t2.
split.
apply unifies_all_typings_equiv. easy.
intros. apply i. apply unifies_all_typings_equiv. easy.
Qed.

Next Obligation.
intro.
apply unifies_all_typings_equiv in H.
pose (wildcard' s). easy.
Qed.

Definition merge {T} : Map.t T -> Map.t T -> Map.t T :=
  Map.map2
    (fun a b =>
       match a with
       | Some x => Some x
       | None => b
       end).

Program Fixpoint infer (exp : expression) {measure (esize exp)} :
  { t | most_general_type exp (fst t) /\ typing_nvars t} +
  { forall t env, ~ well_typed exp t env } :=
match exp with
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
      let ret_t := TVar x_n in
      match unify_typings (f_t, f_env) (x_t '-> ret_t, x_env) with
      | inleft _ s => inleft (apply s ret_t, Map.map (apply s) (merge f_env x_env), S x_n)
      | _ => inright _
      end
    | _ => inright _
    end
  | _ => inright _
  end
end.

Next Obligation. split.
split.
apply wt_Var. apply singleton_MapsTo.

intros. destruct t2. simpl in *.
exists (sole_sub 0 t). split. easy.
intros.
apply singleton_MapsTo_one_thing in H0. destruct H0. rewrite H1.
cbn. cbn in H. dependent destruction H. congruence.

split; [ | intros; apply In_values_MapsTo_equiv in H; destruct H;
           apply singleton_MapsTo_one_thing in H; destruct H; rewrite H0 ].

compute; intros; dependent destruction H; easy.
compute; intros; dependent destruction H1; easy.
Qed.

Next Obligation.
split.
destruct m.
simpl in *.

split.
apply wt_Lambda. apply (well_typed_proper b t env). simpl.
unfold Map.Equal. intro. destruct (string_dec x y).
  rewrite MF.add_eq_o. congruence. assumption.
  rewrite MF.add_neq_o. rewrite MF.remove_neq_o. reflexivity. assumption. assumption.
assumption.

intros.
destruct t2. simpl in *. dependent destruction H.
pose proof (e (returnt, Map.add x argt0 env0)). apply H0 in H. simpl in H.
destruct H. destruct H.
exists x0. split.
  rewrite H. apply eq_sym in Heq_anonymous. apply Map.find_2 in Heq_anonymous. apply H1 in Heq_anonymous.
  Reconstr.rcrush (@Infer.MF.add_mapsto_iff) (@name, @Map.key).

  intros. destruct(old_string_EQ.eq_dec x x1).
    Reconstr.rcrush (@Infer.MF.remove_mapsto_iff) (@Infer.Env).
    Reconstr.rcrush (@Map.add_3, @Map.remove_3) (@name, @Infer.Env, @Map.key).

split.
unfold vars_below. intros. dependent destruction H. dependent destruction H.
dependent destruction H. apply v0 in H. assumption.
apply In_values_MapsTo_equiv. exists x. apply MF.find_mapsto_iff. auto. auto.
intros. apply v0. apply In_values_MapsTo_equiv in H.
destruct H. apply Map.remove_3 in H. apply In_values_MapsTo_equiv.
exists x0. easy.
Qed.

Lemma map_add_order {V} : forall k k2 (v v2 : V) m,
    k <> k2 ->
    Map.Equal (Map.add k v (Map.add k2 v2 m)) (Map.add k2 v2 (Map.add k v m)).
intros.
unfold Map.Equal.
intro.
destruct (string_dec k y).
rewrite MF.add_eq_o.
rewrite MF.add_neq_o.
rewrite MF.add_eq_o.
reflexivity.
easy.
congruence.
easy.

destruct (string_dec k2 y).
rewrite MF.add_neq_o.
repeat rewrite MF.add_eq_o.
reflexivity.
easy.
easy.
easy.

repeat rewrite MF.add_neq_o; easy.
Qed.

Lemma extra_variable_harmless : forall b t env x y,
  well_typed b t env ->
  Map.find x env = None ->
  well_typed b t (Map.add x y env).
induction b.
intros.
apply wt_Var.
dependent destruction H.
apply Map.add_2.
apply Map.find_1 in H. congruence.
assumption.

intros.
dependent destruction H.
apply wt_Lambda.
destruct (string_dec x n).

apply (well_typed_proper _ _ (Map.add n argt env)).
unfold Map.Equal. intro.
rewrite e.
destruct (string_dec n y0).
repeat rewrite MF.add_eq_o; easy.
repeat rewrite MF.add_neq_o; easy.
assumption.

apply (well_typed_proper _ _ (Map.add x y (Map.add n argt env))).
apply map_add_order.
assumption.
apply IHb. assumption.
rewrite MF.add_neq_o. assumption.
congruence.

intros.
dependent destruction H.
apply (wt_Call _ _ argt).
apply IHb1; assumption.
apply IHb2; assumption.
Qed.

Lemma vars_small : forall n s argt t,
    vars_below n t ->
    apply (fun x => if Nat.eq_dec x n then argt else s x) t = apply s t.
induction t.
cbn. intro.
destruct Nat.eq_dec.
rewrite e in H. compute in H. specialize H with n.
pose proof Here. apply H in H0. omega.
reflexivity.

cbn. reflexivity.

cbn. intro.
unfold vars_below in H.
rewrite IHt1.
rewrite IHt2.
reflexivity.
all: unfold vars_below; auto.
Qed.

Next Obligation.
split.
unfold most_general_type.
destruct m. simpl in *.
split.
apply wt_Lambda.
apply extra_variable_harmless; easy.

intros.
dependent destruction H.
destruct t2. simpl in *. destruct x.
pose proof (e (returnt, Map.add x0 argt e0) H). 
destruct H0. simpl in H0. destruct H0.

exists (fun v => if Nat.eq_dec v n then argt else x v). split.

rewrite vars_small.
destruct Nat.eq_dec; congruence.
assumption.

intros.
rewrite vars_small.  
destruct (string_dec x1 x0).
apply Map.find_1 in H2. congruence.
rcrush (@Map.add_3) (@Map.key, @Infer.Env, @name).
apply v0. apply In_values_MapsTo_equiv. eauto.

split.
unfold vars_below.
intros.
dependent destruction H.
dependent destruction H.
dependent destruction H.
dependent destruction H.
omega.
assert (S v1 <= n).
apply v. assumption.
omega.

intros.
assert (vars_below n t2).
apply v0. assumption.
compute.
intros.
assert (S v1 <= n).
apply H0. assumption.
omega.
Qed.

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
destruct m0.
destruct m.
simpl in *.

split.
split.
simpl.
apply (wt_Call _ _ (add_to_tvars f_n x_t_)).
Admitted.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

Next Obligation.
Admitted.
