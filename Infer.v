From Coq Require Import Unicode.Utf8.
From Coq Require Import Program.
Require Import Unify.
Require Import List String Arith.
From Equations Require Import Equations.
Open Scope string_scope.

Definition uncurry {A B C} (f : A -> B -> C) (x : A * B) :=
  match x with (a, b) => f a b end.

Definition unifies_all s xs :=
  forall a b, In (a, b) xs -> unifies s a b.

Lemma uncons_unifies_all : forall s a b t, unifies_all s ((a, b) :: t) -> unifies s a b /\ unifies_all s t.
  repeat canonicalize_unify.
  apply H. simpl. auto.
  apply H. apply in_cons. assumption.
Qed.

Ltac canonicalize_infer :=
  match goal with
  | [H : unifies_all _ ((_, _) :: _) |- _] => apply uncons_unifies_all in H
  | [H : In _ ((_, _) :: _) |- _] => apply in_inv in H
 (* | [H : In _ (values _) |- _] => apply In_values_MapsTo_equiv in H *)
  end.

Ltac can := try canonicalize_infer; try canonicalize_unify.
Ltac smash := smasher can.

Definition isMGU_many s xs := forall s', unifies_all s' xs
  -> exists delta, forall t, apply s' t = apply delta (apply s t).

Equations unify_many (xs : list (Tipe * Tipe)) :
  {s : Subst | unifies_all s xs /\ isMGU_many s xs } + {forall s, ~ unifies_all s xs} :=

  unify_many [] := inleft (exist _ identity _);
  unify_many ((a, b) :: t) with unify_many t => {
    | inleft (exist _ s _) with unify (apply s a) (apply s b) => {
      | inleft (exist _ s2 _) := inleft (exist _ (sequence s2 s) _);
      | inright _ := inright _ };
    | inright _ := inright _ }.

Next Obligation.
  smash.
  destruct H.
  exists s'; smash.
Defined.

Next Obligation.
  smash.
  apply H in H4. smash.

  destruct (H0 s'). smash. now apply H5.
  destruct (H2 x). smash.
  exists x0. smash.
Qed.

Next Obligation.
  smash.
  destruct (H0 s0). smash. apply H2. smash.
  smash.
Qed.

Next Obligation.
  apply (wildcard2 s). now apply uncons_unifies_all in H.
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

Definition nonempty_list A := { xs : list A | xs <> [] }.

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
destruct (string_dec a c); destruct (tipe_dec b d).
  auto.
  assert (Map.MapsTo a d (singleton c d)). apply Map.add_1. easy.
    apply Map.find_1 in H. apply Map.find_1 in H0. rewrite H in H0.
    injection H0. auto.
  all: apply Map.add_3 in H; [ apply Map.empty_1 in H; contradiction | auto ].
Qed.

Lemma In_values_MapsTo_equiv {A} : forall v m,
    In v (values (A := A) m) <-> exists k, Map.MapsTo k v m.
Admitted.

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
  induction e; simpl; smash.
Qed.

Notation "a '-> b" := (TApp (TApp (TConst "->") a) b) (at level 59, right associativity).

Definition vars_below n t := forall v, Contains (TVar v) t -> v < n.

Definition typing : Type := Tipe * Env.

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
  all: cbn in H; smash.
Qed.

Equations unify_typings (t1 t2 : typing) :
  { s | typing_MGU s t1 t2 } + { forall s, ~ unifies_typings s t1 t2 } :=

  unify_typings (t, env) (t2, env2) with
    unify_many ((t, t2) :: values (Map.map2 try_pair env env2)) => {
      | inleft (exist _ s _) => inleft (exist _ s _);
      | inright _ => inright _ }.

Lemma unifies_all_typings_equiv : forall s t t2 e e2,
  unifies_all s ((t, t2) :: values (Map.map2 try_pair e e2)) <->
  unifies_typings s (t, e) (t2, e2).
  split.
  intros.
  unfold unifies_typings. cbn.
  smash.
  apply Map.find_1 in H1.
  apply Map.find_1 in H2.
  apply H0.
  rewrite In_values_MapsTo_equiv. exists k.
  apply Map.find_2.
  rewrite Map.map2_1.
  rewrite H1. rewrite H2. smash.
  left. rewrite MF.in_find_iff. congruence.

  smash. injection H0. smash.
  destruct H. cbn in *. smash.
  rewrite In_values_MapsTo_equiv in H0. destruct H0.
  apply Map.find_1 in H0.
  rewrite MF.map2_1bis in H0.
  apply try_pair_some in H0.
  smash.
  destruct H.
  apply (H2 x); apply Map.find_2; smash.
  smash.
Qed.

Next Obligation.
split.
apply unifies_all_typings_equiv. assumption.
intros. apply H0. apply unifies_all_typings_equiv. assumption.
Qed.

Next Obligation.
intro.
apply unifies_all_typings_equiv in H.
pose (wildcard0 s). easy.
Qed.

Inductive well_typed : expression -> Tipe -> Env -> Prop :=
| wt_Var : forall name env t,
    Map.MapsTo name t env ->
    well_typed (Var name) t env

| wt_Lambda : forall name body env argt returnt,
    well_typed body returnt (Map.add name argt env) ->
    well_typed (Lambda name body) (argt '-> returnt) env

| wt_Call : forall f x argt returnt env,
    well_typed f (argt '-> returnt) env ->
    well_typed x argt env ->
    well_typed (Call f x) (returnt) env.

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

Definition merge {T} : Map.t T -> Map.t T -> Map.t T :=
  Map.map2
    (fun a b =>
       match a with
       | Some x => Some x
       | None => b
       end).

Program Definition lambda_case exp t env n x
  (_ : most_general_type exp (t, env)) (_ : typing_nvars (t, env, n)) :
  { t' | most_general_type (Lambda x exp) (fst t') /\ typing_nvars t'} :=
  match Map.find x env with
  | Some argt => exist _ (argt '-> t, Map.remove x env, n) _
  | None => exist _ (TVar n '-> t, env, (S n)) _
  end.

Next Obligation.
  destruct H.
  smash. split.

  simpl.
  apply wt_Lambda. apply (well_typed_proper _ t env).
  unfold Map.Equal. intro. destruct (string_dec x y).
  rewrite MF.add_eq_o; smash.
  rewrite MF.add_neq_o. rewrite MF.remove_neq_o; smash. assumption.
  assumption.

  smash.
  destruct t2. simpl in *. dependent destruction H3.
  pose proof (H2 (returnt, Map.add x argt0 env0) H3). simpl in H4.
  destruct H4.
  exists x0. smash.
  rewrite H4. specialize H5 with x argt. apply MF.add_mapsto_iff in H5. smash.
  apply Map.find_2. smash.

  apply Map.find_1 in H6. rewrite MF.remove_o in H6.
  destruct old_string_EQ.eq_dec; smash.
  eapply Map.add_3.
  apply n0. apply H5. apply Map.find_2. assumption.

  apply variables_spec in H3. dependent destruction H3. dependent destruction H3.
  dependent destruction H3. apply (H1 argt). apply In_values_MapsTo_equiv.
  exists x. apply Map.find_2. auto. auto.
  now apply H0.
  apply (H1 t2). apply In_values_MapsTo_equiv. apply In_values_MapsTo_equiv in H3.
  destruct H3.
  apply Map.remove_3 in H3. exists x0. assumption.
  apply variables_spec. assumption.
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

Next Obligation.
  smash. split.
  simpl. apply wt_Lambda.
  apply extra_variable_harmless.
  destruct H. easy. easy.

  destruct H. smash. destruct t2. simpl in *.
  dependent destruction H3.
  destruct (H2 (returnt, (Map.add x argt env0))). easy.
  simpl in H4.
  exists (augment_sub x0 n argt).
  smash.
  rewrite augment_sub_hlp.
  unfold augment_sub. destruct Nat.eq_dec; smash.
  intro. apply variables_spec in H6. apply H0 in H6. smash.

  rewrite augment_sub_hlp.
  eapply Map.add_3.
  intro. rewrite <- H7 in H6. apply Map.find_1 in H6.
  rewrite H6 in Heq_anonymous. congruence.
  apply H5; smash.
  intro. specialize H1 with a. rewrite In_values_MapsTo_equiv in H1.
  apply variables_spec in H7. apply H1 in H7; smash.
  exists x1; smash.

  apply variables_spec in H2.
  dependent destruction H2.
  dependent destruction H2.
  dependent destruction H2.
  dependent destruction H2; smash.
  apply Nat.lt_lt_succ_r. now apply H0.

  apply Nat.lt_lt_succ_r. apply variables_spec in H3. apply (H1 t2); auto.
Qed.

Equations infer (exp : expression) :
  { t | most_general_type exp (fst t) /\ typing_nvars t} +
  { forall t env, ~ well_typed exp t env } :=

infer (Var a) := inleft (exist _ (TVar 0, (singleton a (TVar 0)), 1) _);

infer (Lambda x b) with infer b => {
  | inleft (exist _ (t, env, n) _) => inleft (lambda_case b t env n _ _ _);
  | inright _ := inright _ };

infer (Call f x) with infer f => {
  | inleft (exist _ (f_t, f_env, f_n) _) with infer x => {
    | inleft (exist _ (x_t_, x_env_, x_n_) _) :=
      let x_t := add_to_tvars f_n x_t_ in
      let x_env := Map.map (add_to_tvars f_n) x_env_ in
      let x_n := x_n_ + f_n in
      let ret_t := TVar x_n in
      match unify_typings (f_t, f_env) (x_t '-> ret_t, x_env) with
      | inleft _ (exist _ s _) =>
        inleft (exist _ (apply s ret_t, Map.map (apply s) (merge f_env x_env), S x_n) _)
      | _ => inright _
      end;
    | _ => inright _ };
  | inright _ := inright _ }.

Next Obligation.
  smash.
  split.
  apply wt_Var. apply singleton_MapsTo.

  intros. destruct t2. simpl in *.
  exists (sole_sub 0 t). smash.
  apply singleton_MapsTo_one_thing in H0. smash. rewrite H1.
  cbn. dependent destruction H. congruence.

  destruct H; smash. destruct H.

  apply In_values_MapsTo_equiv in H. destruct H. apply singleton_MapsTo_one_thing in H.
  smash. rewrite H1 in H0. destruct H0; smash. destruct H0.
Qed.

Next Obligation.
  intro. dependent destruction H.
  now apply wildcard0 in H.
Qed.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

Next Obligation.
  intro. dependent destruction H2. now apply n0 in H2_0.
Qed.

Next Obligation.
  intro. dependent destruction H. now apply wildcard2 in H.
Qed.
