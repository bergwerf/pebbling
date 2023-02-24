(*
A4. Algorithms on Lists
=======================
*)

From graph_pebbling Require Import A1_misc A3_arith.

Notation lprod la lb := (foldr (λ a, ((a,.) <$> lb ++.)) [] la).
Notation summation := (foldr (+) 0).
Notation product := (foldr Nat.mul 1).
Notation concat := (foldr (++) []).

Lemma non_empty_length {A} (l : list A) : l ≠ [] ↔ length l ≠ 0.
Proof. destruct l; done. Qed.

Lemma non_empty_inv {A} (l : list A) : l ≠ [] -> ∃ a, a ∈ l.
Proof. destruct l; [done|eexists]; apply elem_of_list_here. Qed.

Lemma non_empty_elem {A} (a : A) l : a ∈ l -> l ≠ [].
Proof. destruct l; set_solver. Qed.

Lemma head_elem_of {A} (a : A) l : head l = Some a -> a ∈ l.
Proof. intros H; apply head_Some in H as (l' & ->); set_solver. Qed.

Lemma fmap_const {A B} (a : A) (l : list B) :
  const a <$> l = repeat a (length l).
Proof. induction l; cbn; congruence. Qed.

Lemma foldr_comm `{left_id : LeftId A (=) e f, assoc : Assoc A (=) f}
  (l l' : list A) : foldr f e (l ++ l') = f (foldr f e l) (foldr f e l').
Proof.
induction l; cbn; [symmetry; apply left_id|].
rewrite IHl; apply assoc.
Qed.

(*
Sublists and permutations
-------------------------
*)
Section Sublists.

Global Instance left_comm_cons_app {A} (a : A) :
  CondLeftComm (≡ₚ) (λ _, True) (cons a) (++).
Proof. repeat intro; done. Qed.

Lemma foldr_Permutation `{assoc : Assoc A (=) f, comm : Comm A A (=) f}
  a0 la1 la2 : la1 ≡ₚ la2 -> foldr f a0 la1 = foldr f a0 la2.
Proof. induction 1; cbn; congruence. Qed.

Lemma submseteq_fmap {A B} (f : A -> B) l l' :
  l' ⊆+ l -> f <$> l' ⊆+ f <$> l.
Proof. induction 1; econstructor; done. Qed.

Lemma submseteq_Forall {A} (P : A -> Prop) l l' :
  l' ⊆+ l -> Forall P l -> Forall P l'.
Proof. induction 1; inversion 1; subst; auto; inv H3; auto. Qed.

Lemma sublist_fmap_inv {A B} (f : A -> B) la lb :
  lb `sublist_of` f <$> la -> ∃ la', la' `sublist_of` la ∧ lb = f <$> la'.
Proof.
revert lb; induction la; cbn; intros ? H.
- apply sublist_nil_r in H as ->; exists []; done.
- assert (H' := H); apply sublist_cons_r in H as [H|(lb' & -> & H)];
  apply IHla in H as (la' & H & ->).
  + exists la'; split; [|done]; constructor; done.
  + exists (a :: la'); cbn; split; [|done]; constructor; done.
Qed.

Lemma sublist_concat {A} (l l' : list (list A)) :
  l' `sublist_of` l -> concat l' `sublist_of` concat l.
Proof.
revert l'; induction l; cbn; intros ? H.
- apply sublist_nil_r in H as ->; done.
- apply sublist_cons_r in H as [H|(l'' & -> & H)]; cbn.
  + apply sublist_app_r; exists []; eexists; cbn; repeat split.
    apply sublist_nil_l. apply IHl; done.
  + apply sublist_app; [done|].
    apply IHl; done.
Qed.

End Sublists.

(*
Ordered lists
-------------
*)
Section Ordered_Lists.

Context {A : Type}.
Variable R : relation A.

Inductive ordered : list A -> Prop :=
  | ordered_nil : ordered []
  | ordered_singleton a : ordered [a]
  | ordered_cons a0 a1 l : R a0 a1 ->
    ordered (a1 :: l) -> ordered (a0 :: a1 :: l).

Lemma ordered_cons_inv_hd `{refl : Reflexive _ R} a l :
  ordered (a :: l) -> R a (hd a l).
Proof. destruct l; cbn; inversion_clear 1; [apply refl|done]. Qed.

Lemma ordered_cons_inv_tl a l :
  ordered (a :: l) -> ordered l.
Proof. destruct l; inversion_clear 1; [constructor|done]. Qed.

End Ordered_Lists.

(*
Cartesian product of lists
--------------------------
*)
Section Cartesian_Product.

Context {A B : Type}.
Implicit Types la : list A.
Implicit Types lb : list B.

Lemma lprod_enum `{Finite A, Finite B} :
  enum (A * B) = lprod (enum A) (enum B).
Proof. done. Qed.

Lemma elem_of_lprod la lb a b :
  a ∈ la -> b ∈ lb -> (a, b) ∈ lprod la lb.
Proof. induction la; set_solver. Qed.

Lemma elem_of_lprod_inv la lb a b :
  (a, b) ∈ lprod la lb -> a ∈ la ∧ b ∈ lb.
Proof. induction la; set_solver. Qed.

Lemma lprod_app la1 la2 lb :
  lprod (la1 ++ la2) lb = lprod la1 lb ++ lprod la2 lb.
Proof. induction la1; cbn; [done|]. rewrite IHla1, (assoc app); done. Qed.

Lemma NoDup_lprod la lb :
  NoDup la -> NoDup lb -> NoDup (lprod la lb).
Proof.
induction la; cbn; intros. constructor.
inv H; apply NoDup_app; repeat split.
- apply NoDup_fmap; [|done]. repeat intro; congruence.
- intros [] H1 H2; apply elem_of_lprod_inv in H2; set_solver.
- apply IHla; done.
Qed.

End Cartesian_Product.

(*
Concatenation of lists
----------------------
*)
Section Concatenation.

Lemma elem_of_concat {A} (a : A) l ls :
  a ∈ l -> l ∈ ls -> a ∈ concat ls.
Proof. set_solver. Qed.

Lemma concat_repeat_nil {A} n :
  concat (@repeat (list A) [] n) = [].
Proof. induction n; cbn; done. Qed.

Lemma concat_fmap_singleton {A} (l : list A) :
  concat ((λ a, [a]) <$> l) = l.
Proof. induction l; cbn; congruence. Qed.

Lemma fmap_concat_comm {A B} (f : A -> B) l :
  f <$> concat l = concat (@fmap list _ _ _ f <$> l).
Proof.
induction l; cbn; [done|].
rewrite fmap_app, IHl; done.
Qed.

Lemma concat_lprod {A B} (f : A -> B -> nat) la lb :
  concat ((λ a, f a <$> lb) <$> la) = uncurry f <$> lprod la lb.
Proof.
induction la; cbn; [done|].
rewrite fmap_app, IHla, <-list_fmap_compose; done.
Qed.

Lemma sublist_concat_r {A} (l : list A) ls :
  l ∈ ls -> l `sublist_of` concat ls.
Proof.
induction ls; cbn; [set_solver|]; intros.
simpl_elem_of; apply sublist_app_r; [exists l, []|exists [], l].
- repeat split; [rewrite app_nil_r; done|done|apply sublist_nil_l].
- repeat split; [apply sublist_nil_l|apply IHls; done]. 
Qed.

End Concatenation.

(*
Altering a list
---------------
*)
Section Fold_FMap_Alter.

Lemma fmap_no_alter `{EqDecision A} {B} (l : list A) k (f : A -> B) g :
  k ∉ l -> alter g k f <$> l = f <$> l.
Proof.
induction l; cbn; intros Hk; [done|].
apply not_elem_of_cons in Hk as [].
simpl_alter; rewrite IHl; done.
Qed.

Context `{f_comm : Comm A A R f}.
Context `{l_domi : LeftDominant A P f}.
Context `{l_comm : CondLeftComm A R P g f}.
Context `{equiv_R : Equivalence A R}.
Context `{proper_P : Proper _ (R ==> iff) P}.
Context `{proper_g : Proper _ (R ==> R) g}.
Context `{proper_f : Proper _ (R ==> R ==> R) f}.

Lemma foldr_left_dominant a x l :
  x ∈ l -> P x -> P (foldr f a l).
Proof.
intros Hl Hx; induction l; cbn; simpl_elem_of.
- apply l_domi; done.
- rewrite f_comm; apply l_domi, IHl, Hl.
Qed.

Lemma foldr_alter `{EqDecision B} (l : list B) k a h :
  P (h k) -> k ∈ l -> NoDup l ->
  R (foldr f a (alter g k h <$> l)) (g (foldr f a (h <$> l))).
Proof.
intros Hh; induction l; cbn; intros Hk; simpl_elem_of; inversion_clear 1.
- simpl_alter; rewrite l_comm, fmap_no_alter; done.
- simpl_alter; [|congruence].
  rewrite IHl, f_comm, l_comm, f_comm; try done.
  apply foldr_left_dominant with (x:=h k); [|done].
  apply elem_of_list_fmap_1; done.
Qed.

End Fold_FMap_Alter.

(*
Summing a list of numbers
-------------------------
*)
Section Summation.

Global Instance summation_Permutation : Proper ((≡ₚ) ==> (=)) summation.
Proof. intros xs ys H; apply foldr_Permutation. done. Qed.

Lemma summation_const {A} (l : list A) k :
  summation (const k <$> l) = k * length l.
Proof. induction l; clia. Qed.

Lemma summation_bound l k :
  Forall (ge k) l -> summation l ≤ k * length l.
Proof. induction l; cbn; inversion_clear 1; intuition; lia. Qed.

Lemma summation_add {A} f g (l : list A) :
  summation (f .+ g <$> l) = summation (f <$> l) + summation (g <$> l).
Proof. induction l; clia. Qed.

Lemma summation_mul_const {A} n f (l : list A) :
  summation (const n .* f <$> l) = n * summation (f <$> l).
Proof. induction l; clia. Qed.

Lemma summation_app l1 l2 :
  summation (l1 ++ l2) = summation l1 + summation l2.
Proof.
induction l1; cbn; [done|].
rewrite IHl1, (assoc (+)); done.
Qed.

Lemma submseteq_summation l1 l2 :
  l1 ⊆+ l2 -> summation l1 ≤ summation l2.
Proof.
intros H; apply submseteq_Permutation in H as [lc ->].
rewrite summation_app; lia.
Qed.

Corollary elem_of_summation n l :
  n ∈ l -> n ≤ summation l.
Proof.
intros H; replace n with (summation [n]) by clia.
apply submseteq_summation, singleton_submseteq_l, H.
Qed.

Lemma summation_le {A} (f g : A -> nat) l :
  (∀ a, a ∈ l -> f a ≤ g a) ->
  summation (f <$> l) ≤ summation (g <$> l).
Proof.
induction l; cbn; intros. done.
apply Nat.add_le_mono. set_solver. apply IHl; set_solver.
Qed.

Lemma summation_lt {A} (f g : A -> nat) x l :
  (∀ a, a ∈ l -> f a ≤ g a) -> x ∈ l -> f x < g x ->
  summation (f <$> l) < summation (g <$> l).
Proof.
induction l; cbn; intros; simpl_elem_of.
- apply Nat.add_lt_le_mono. done. apply summation_le; set_solver.
- apply Nat.add_le_lt_mono. set_solver. apply IHl; set_solver.
Qed.

Lemma summation_sub {A} (f g : A -> nat) l :
  (∀ a, a ∈ l -> g a ≤ f a) ->
  summation (f .- g <$> l) = summation (f <$> l) - summation (g <$> l).
Proof.
induction l; cbn; intros; [done|].
assert (Hl : ∀ a, a ∈ l -> f a ≥ g a) by set_solver;
assert (Ha : a ∈ a :: l) by set_solver;
apply summation_le in Hl as H_le; apply H in Ha.
rewrite IHl; [lia|done].
Qed.

Lemma summation_concat {A} (f : A -> list nat) l :
  summation ((λ a, summation (f a)) <$> l) = summation (concat (f <$> l)).
Proof.
induction l; cbn; [done|].
rewrite summation_app; congruence.
Qed.

Lemma summation_lprod {A B} (f : A -> B -> nat) la lb :
  summation ((λ a, summation (f a <$> lb)) <$> la) =
  summation (uncurry f <$> lprod la lb).
Proof.
rewrite summation_concat, concat_lprod; done.
Qed.

Lemma summation_nonzero l :
  summation l > 0 -> ∃ n, n ∈ l ∧ n > 0.
Proof.
unfold size; induction l as [|n l]; cbn; intros; [lia|].
dec (0 < n); [exists n; set_solver|]; destruct IHl as (m & ? & ?); [lia|].
exists m; set_solver.
Qed.

End Summation.

(*
Filtering a list
----------------
*)
Section List_Filter.

Context {A : Type}.
Variable P : A -> Prop.
Context `{dec : ∀ a, Decision (P a)}.

Fixpoint dsig_filter (l : list A) : list (dsig P) :=
  match l with
  | [] => []
  | a :: l' =>
    let tl := dsig_filter l' in
    match decide (P a) with
    | left P => dexist a P :: tl
    | right _ => tl
    end
  end.

Lemma filter_app_Permutation (l : list A) :
  l ≡ₚ filter P l ++ filter (not ∘ P) l.
Proof.
induction l; cbn; [done|].
dec (P a); dec (¬ P a); try done; cbn;
rewrite <-?Permutation_middle, <-IHl; done.
Qed.

Lemma filter_NoDup_Permutation l l' :
  (∀ a, P a -> a ∈ l ↔ a ∈ l') ->
  (∀ a, a ∈ l' -> P a) ->
  NoDup l -> NoDup l' ->
  filter P l ≡ₚ l'.
Proof.
revert l'; induction l; cbn; intros l' H1 H2 H3 H4.
- destruct l'; set_solver.
- inv H3; dec (P a); [|apply IHl; set_solver].
  assert (H3 : a ∈ l') by set_solver.
  apply elem_of_Permutation in H3 as [l'' H3]; rewrite H3 in *; inv H4.
  apply Permutation_cons; [done|]; apply IHl; try done; intros b Hb.
  + apply H1 in Hb; rewrite H3 in Hb; set_solver.
  + intros; apply H2; rewrite H3; set_solver.
Qed.

Lemma elem_of_dsig_filter_inv a l :
  a ∈ dsig_filter l -> P (`a) ∧ `a ∈ l.
Proof.
induction l; cbn; [set_solver|].
destruct (decide _); set_solver.
Qed.

Lemma elem_of_dsig_filter a l :
  `a ∈ l -> a ∈ dsig_filter l.
Proof.
induction l; cbn; [set_solver|]; rewrite elem_of_cons; intros [<-|Hl].
- dec (P (`a)).
  + rewrite dexists_proj1; apply elem_of_list_here.
  + destruct a as [a H1]; apply bool_decide_unpack in H1 as H2; cbn in *; done.
- destruct (decide _); [apply elem_of_list_further|]; apply IHl; done.
Qed.

Lemma NoDup_dsig_filter l :
  NoDup l -> NoDup (dsig_filter l).
Proof.
induction l; cbn; [constructor|inversion_clear 1].
destruct (decide _); [constructor|]; try (apply IHl; done).
intros H; apply elem_of_dsig_filter_inv in H as [_ H]; done.
Qed.

End List_Filter.

(*
Searching a vector
------------------
*)
Section Vector_Find.

Context {A : Type}.
Variable P : A -> Prop.
Context `{∀ a : A, Decision (P a)}.

Fixpoint vec_find {n} (v : vec A n) : option (fin n) :=
  match v with
  | [#] => None
  | vcons a v' =>
    if decide (P a) then Some (0%fin)
    else FS <$> vec_find v'
  end.

Lemma vec_find_sound {n} (v : vec A n) i :
  vec_find v = Some i -> P (v !!! i).
Proof.
induction v; cbn; [done|].
dec (P h); [intros; simplify_eq; done|];
inv_fin i; destruct (vec_find v); cbn; try done.
intros; apply IHv; simplify_eq; done.
Qed.

Lemma vec_find_complete {n} (v : vec A n) i :
  P (v !!! i) -> vec_find v ≠ None.
Proof.
induction v; cbn; [inv_fin i|].
dec (P h); [done|]; inv_fin i; cbn; [done|]; intros i Hi.
apply IHv in Hi; destruct (vec_find v) eqn:E; done.
Qed.

End Vector_Find.

(*
Enumerating all vectors
-----------------------
*)
Section Vector_Enumeration.

Context `{fin : Finite A}.

Fixpoint vec_enum l n : list (vec A n) :=
  match n with
  | 0 => [[#]]
  | S m => a ← l; vcons a <$> vec_enum l m
  end.

Lemma NoDup_bind {B} (f : A -> list B) l :
  (∀ a a' b, b ∈ f a -> b ∈ f a' -> a = a') ->
  (∀ a, NoDup (f a)) -> NoDup l -> NoDup (l ≫= f).
Proof.
intros inj Hf Hl; induction l; cbn; [constructor|inv Hl].
apply NoDup_app; repeat split; auto. intros b H3 H4.
apply elem_of_list_bind in H4 as (a' & H5 & H6).
apply (inj a a') in H3; subst; done.
Qed.

Lemma NoDup_vec_enum l n :
  NoDup l -> NoDup (vec_enum l n).
Proof.
induction n; cbn; intros; [apply NoDup_singleton|apply NoDup_bind]; intros.
- apply elem_of_list_fmap in H0 as (v & -> & _), H1 as (v' & E & _); congruence.
- apply NoDup_fmap; auto; apply inj_vcons_tl.
- done.
Qed.

Global Program Instance vec_finite n : Finite (vec A n) :=
  {| enum := vec_enum (enum A) n |}.
Next Obligation.
intros; apply NoDup_vec_enum, NoDup_enum.
Qed.
Next Obligation.
induction x; cbn. set_solver.
apply elem_of_list_bind; exists h; split.
apply elem_of_list_fmap_1; done. apply elem_of_enum.
Qed.

End Vector_Enumeration.
