(*
A6. Natural Valuation Functions - Part I
========================================
*)

From graph_pebbling Require Import A1_misc A2_lift A3_arith A4_lists.

Notation valuation A := (A -> nat).

Section Valuation_Functions.

Context `{fin : Finite A}.

Section Size.

Definition size (f : valuation A) := summation (f <$> enum A).

Lemma size_const k : size (const k) = k * card A.
Proof. unfold size; apply summation_const. Qed.

Lemma size_lwb f a : f a ≤ size f.
Proof. apply elem_of_summation, elem_of_list_fmap_1, elem_of_enum. Qed.

Lemma size_add f g : size (f .+ g) = size f + size g.
Proof. apply summation_add. Qed.

Lemma size_mul_const n f : size (const n .* f) = n * size f.
Proof. apply summation_mul_const. Qed.

Lemma size_sub f g : g .≤ f -> size (f .- g) = size f - size g.
Proof. intros; apply summation_sub; firstorder. Qed.

Lemma size_alter
  `{dominant : LeftDominant _ P (+)}
  `{l_comm : CondLeftComm _ (=) P g (+)} f a :
  P (f a) -> size (alter g a f) = g (size f).
Proof.
unfold size; intros; apply foldr_alter.
done. apply elem_of_enum. apply NoDup_enum.
Qed.

Lemma size_nonzero f :
  size f > 0 -> ∃ a, f a > 0.
Proof.
unfold size; induction (enum A) as [|a l]; cbn; intros; [lia|].
dec (0 < f a); [exists a; done|]; apply IHl; lia.
Qed.

Lemma size_zero f :
  size f = 0 -> f = const 0.
Proof.
dec (∀ a, f a = 0).
- intros _; extensionality a; apply H.
- intros Hf; exfalso.
  apply not_forall_exists in H as [a H].
  assert (Ha := size_lwb f a); lia.
Qed.

Lemma fn_nat_ind (P : valuation A -> Prop) :
  P (const 0) -> (∀ f a, P f -> P (alter add1 a f)) -> ∀ f, P f.
Proof.
intros H0 H1; apply (induction_ltof1 _ size);
unfold ltof; intros f IH; dec (size f = 0).
- apply size_zero in H as ->; done.
- assert (Hf : size f > 0) by lia; apply size_nonzero in Hf as [a Ha].
  replace f with (alter add1 a (alter (subtract 1) a f)).
  + apply H1, IH; rewrite size_alter; clia.
  + extensionality b; dec (b = a); simpl_alter; clia.
Qed.

End Size.

Section Support.

Definition supp (f : valuation A) := size (min 1 ∘ f).

Lemma supp_add f g : supp (f .+ g) ≤ supp f + supp g.
Proof. unfold supp; rewrite <-size_add; apply summation_le; clia. Qed.

Lemma supp_sub f g : supp (f .- g) ≤ supp f.
Proof. unfold supp, size; apply summation_le; clia. Qed.

Lemma supp_le_size f : supp f ≤ size f.
Proof. unfold supp, size; apply summation_le; intros a _; clia. Qed.

Lemma supp_le_card f :
  supp f ≤ card A.
Proof.
trans (size (const 1)).
- unfold supp, size; apply summation_le; intros a _; clia.
- rewrite size_const; lia.
Qed.

Lemma partial_supp_lt f (l z : list A) :
  Forall ((=) 0) (f <$> z) -> z ⊆+ l ->
  summation (min 1 ∘ f <$> l) ≤ length l - length z.
Proof.
intros Hf Hz; apply submseteq_Permutation in Hz as (nz & ->).
rewrite app_length, fmap_app, summation_app; trans (length nz); [|lia].
replace (summation (min 1 ∘ f <$> z)) with 0; [induction nz; clia|].
symmetry; apply Nat.le_0_r; etrans; [apply summation_bound with (k:=0)|lia].
rewrite list_fmap_compose; eapply Forall_fmap, Forall_impl; [|apply Hf]. clia.
Qed.

Corollary supp_lt_card f z :
  NoDup z -> Forall ((=) 0) (f <$> z) ->
  supp f ≤ card A - length z.
Proof.
intros; apply partial_supp_lt; [done|].
apply NoDup_submseteq; [done|intros; apply elem_of_enum].
Qed.

End Support.

Section Minors.

Lemma fn_partial_minor (f : valuation A) l n :
  summation (f <$> l) ≥ n -> NoDup l -> ∃ f', f' .≤ f ∧
  summation (f' <$> l) = n ∧ ∀ a, a ∉ l -> f' a = 0.
Proof.
revert n; induction l; cbn; intros n Hn; inversion_clear 1.
- exists (const 0); repeat split; clia.
- destruct (IHl (n - f a)) as (f' & H3 & H4 & H5); [lia|done|].
  apply H5 in H0 as H6; exists (alter ((+) (min n (f a))) a f'); repeat split.
  + intros b; inst H3 b; cbn; dec (b = a); simpl_alter; lia.
  + simpl_alter; rewrite fmap_no_alter; [|done]; lia.
  + intros; rewrite fn_lookup_alter_ne; set_solver.
Qed.

Corollary fn_minor f n :
  size f ≥ n -> ∃ f', f' .≤ f ∧ size f' = n.
Proof.
unfold size; intros Hn; apply fn_partial_minor in Hn as (f' & H1 & H2 & H3).
exists f'; done. apply NoDup_enum.
Qed.

Lemma fn_minor_eq_supp f n :
  size f ≥ n -> supp f ≤ n -> ∃ f', f' .≤ f ∧ size f' = n ∧ supp f' = supp f.
Proof.
intros; destruct (fn_minor (f .- min 1 ∘ f) (n - supp f)) as (f' & H1 & H2).
- rewrite size_sub; unfold supp; clia.
- exists (min 1 ∘ f .+ f'); unfold supp in *; rewrite ?size_add; repeat split.
  intros a; cbn; inst H1 a; lia. lia.
  f_equal; extensionality a; cbn; inst H1 a; lia.
Qed.

End Minors.

Section Extraction.

Definition rsize (k : nat) (f : valuation A) := size f - (k - 1) * (supp f - 1).

Lemma rsize_le k l f : k ≤ l -> rsize l f ≤ rsize k f.
Proof. unfold rsize; nia. Qed.

Lemma rsize_add_pos k f g :
  rsize k f > 0 -> rsize k g > 0 ->
  rsize k (f .+ g) ≥ rsize k f + rsize k g - (k - 1).
Proof.
unfold rsize; rewrite size_add.
assert (H := supp_add f g); nia.
Qed.

Lemma rsize_add k f g :
  ∃ h, h .≤ f .+ g ∧ rsize k h ≥ rsize k f + rsize k g - (k - 1).
Proof.
dec (rsize k f = 0); dec (rsize k g = 0);
[exists (const 0)|exists g|exists f|exists (f .+ g)]; split; try clia.
apply rsize_add_pos; lia.
Qed.

Lemma rsize_sub k f g :
  g .≤ f -> rsize k (f .- g) ≥ rsize k f - size g.
Proof.
unfold rsize; intros; rewrite size_sub; [|done].
assert (H1 := supp_sub f g); nia.
Qed.

Lemma supp_pigeon_hole f n :
  size f > n * supp f -> ∃ a, f a > n.
Proof.
unfold supp, size; induction (enum A) as [|a l]; cbn; intros; [lia|].
dec (n < f a); [exists a; done|]; apply IHl; nia.
Qed.

Lemma rsize_pigeon_hole f k n :
  0 < n ≤ k -> rsize k f ≥ n -> ∃ a, f a ≥ n.
Proof.
unfold rsize; intros; assert (Hf : size f > (n - 1) * supp f) by nia.
apply supp_pigeon_hole in Hf as (a & Ha); exists a; lia.
Qed.

Lemma rsize_minor k f m n :
  0 < n ≤ k -> rsize k f ≥ m*n -> ∃ f', const n .* f' .≤ f ∧ size f' = m.
Proof.
intros; induction m; cbn.
- exists (const 0); rewrite ?size_const; split; clia.
- destruct IHm as (f' & H1 & H2); [lia|]; subst.
  assert (rsize k (f .- (const n .* f')) ≥ n).
  + red; etrans; [|apply rsize_sub; done]; rewrite size_mul_const; lia.
  + apply rsize_pigeon_hole in H2 as (a & Ha); [|done]; cbn in Ha.
    exists (alter add1 a f'); split.
    * intros b; inst H1 b; cbn; dec (b = a); simpl_alter; lia.
    * rewrite size_alter; lia.
Qed.

End Extraction.

End Valuation_Functions.

Section Injection.

Context `{fin_A : Finite A, fin_B : Finite B}.
Context `{Inj A B (=) (=) f}.
Hypothesis equiv : card A = card B.

Lemma size_compose g :
  size (g ∘ f) = size g.
Proof.
apply foldr_Permutation; rewrite list_fmap_compose.
rewrite finite_inj_Permutation; done.
Qed.

Corollary supp_compose g : supp (g ∘ f) = supp g.
Proof. unfold supp; rewrite assoc_compose; apply size_compose. Qed.

Corollary rsize_compose k g : rsize k (g ∘ f) = rsize k g.
Proof. unfold rsize; rewrite size_compose, supp_compose; done. Qed.

End Injection.

Section Product_Sub_Valuation.

Context `{Finite A, Finite B}.

Definition prod_sub_val a f (p : A * B) : nat :=
  if decide (p.1 = a) then f p.2 else 0.

Global Arguments prod_sub_val _ _ _ /.

Lemma prod_sub_val_add a f f' :
  prod_sub_val a (f .+ f') = prod_sub_val a f .+ prod_sub_val a f'.
Proof. extensionality p; destruct p as [a' b]; cbn; dec (a' = a); done. Qed.

Lemma summation_prod_sub_val_1 a f l :
  summation (prod_sub_val a f <$> ((a,.) <$> l)) = summation (f <$> l).
Proof. induction l; cbn; [done|]. dec (a = a); rewrite IHl; done. Qed.

Lemma summation_prod_sub_val_2 a f a' l :
  a ≠ a' -> summation (prod_sub_val a f <$> ((a',.) <$> l)) = 0.
Proof. intros; induction l; cbn; [done|]. dec (a' = a); rewrite IHl; done. Qed.

Lemma summation_prod_sub_val_3 a f la lb :
  a ∉ la -> summation (prod_sub_val a f <$> lprod la lb) = 0.
Proof.
intros; induction la; cbn; [done|].
rewrite fmap_app, summation_app, summation_prod_sub_val_2, IHla; set_solver.
Qed.

Lemma size_prod_sub_val a f :
  size (prod_sub_val a f) = size f.
Proof.
unfold size; rewrite lprod_enum.
assert (H1 : a ∈ enum A) by apply elem_of_enum;
assert (H2 : NoDup (enum A)) by apply NoDup_enum;
revert H1 H2; generalize (enum A) (enum B); intros la lb.
revert lb; induction la as [|a' la]; cbn; intros; [set_solver|].
rewrite fmap_app, summation_app; inv H1; inv H2.
- rewrite summation_prod_sub_val_1, summation_prod_sub_val_3; [lia|done].
- rewrite summation_prod_sub_val_2, IHla; set_solver.
Qed.

Lemma compose_min1_prod_sub_val a f :
  min 1 ∘ prod_sub_val a f = prod_sub_val a (min 1 ∘ f).
Proof.
extensionality p; cbn; dec (p.1 = a); lia.
Qed.

Lemma rsize_prod_sub_val k a f :
  rsize k (prod_sub_val a f) = rsize k f.
Proof.
unfold rsize, supp;
rewrite compose_min1_prod_sub_val, ?size_prod_sub_val; done.
Qed.

End Product_Sub_Valuation.
