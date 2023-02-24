(*
A6. Natural Valuation Functions - Part II
=========================================
*)

From graph_pebbling Require Import
  A1_misc A2_lift A3_arith A4_lists A6_valuation_I.

Section Finite_Inverse.

Context `{fin_A : Finite A, fin_B : Finite B}.
Variable f : A -> B.

Definition inv (b : B) := filter (λ a, f a = b) (enum A).

Lemma elem_of_inv a : a ∈ inv (f a).
Proof. apply elem_of_list_filter; split; [done|apply elem_of_enum]. Qed.

Lemma NoDup_inv b : NoDup (inv b).
Proof. apply list.NoDup_filter, NoDup_enum. Qed.

Lemma elem_of_inv_spec a b : a ∈ inv b -> f a = b.
Proof. intros H; apply elem_of_list_filter in H as [H _]; done. Qed.

Lemma not_elem_of_inv_spec a b :
  a ∉ inv b -> f a ≠ b.
Proof.
intros H1 H2; apply H1, elem_of_list_filter.
split; [done|apply elem_of_enum].
Qed.

Lemma inv_not_nil `{surj : Surj _ _ (=) f} b :
  inv b ≠ [].
Proof.
intros H; destruct (surj b) as [a Ha].
eapply filter_nil_not_elem_of; [apply H|apply Ha|apply elem_of_enum].
Qed.

Lemma concat_inv_Permutation_partial la lb :
  (∀ a, a ∈ la ↔ f a ∈ lb) ->
  NoDup la -> NoDup lb ->
  concat (inv <$> lb) ≡ₚ la.
Proof.
revert la; induction lb as [|b lb]; cbn; intros la H1 H2 H3.
- destruct la; set_solver.
- etrans; [|symmetry]; [apply Permutation_app|apply filter_app_Permutation
  with (P:=λ a, f a = b)(l:=la)].
  + apply filter_NoDup_Permutation; intros.
    * split; intros; [|apply elem_of_enum].
      apply elem_of_list_filter; set_solver.
    * apply elem_of_list_filter in H; set_solver.
    * apply NoDup_enum.
    * apply list.NoDup_filter; done.
  + inv H3; apply IHlb.
    * intros; rewrite elem_of_list_filter; set_solver.
    * apply list.NoDup_filter; done.
    * done.
Qed.

Lemma concat_inv_Permutation :
  concat (inv <$> enum B) ≡ₚ enum A.
Proof.
apply concat_inv_Permutation_partial; try apply NoDup_enum.
split; intros; apply elem_of_enum.
Qed.

End Finite_Inverse.

Section Support_Injection.

Context `{fin_A : Finite A, fin_B : Finite B}.
Context `(m : A -> option B, f : valuation A, g : valuation B).

Hypothesis inj : ∀ a a' b, f a > 0 -> f a' > 0 ->
  m a = Some b -> m a' = Some b -> a = a'.

Lemma supp_inj_le_partial la lb :
  NoDup la -> NoDup lb ->
  (∀ a, a ∈ la -> f a > 0 -> ∃ b, b ∈ lb ∧ m a = Some b ∧ g b > 0) ->
  summation (min 1 ∘ f <$> la) ≤ summation (min 1 ∘ g <$> lb).
Proof.
revert lb; induction la; cbn; intros lb H1 H2;
intros; [lia|]; inv H1; dec (f a = 0).
- replace (min _ _) with 0 by lia; cbn.
  apply IHla; [done|done|]; intros; eapply H; [set_solver|done].
- assert (Ha : f a > 0) by lia.
  apply H in Ha as (b & Hb & Ha & ?); [|set_solver].
  apply elem_of_Permutation in Hb as (lb' & Hlb').
  rewrite Hlb' in *; inv H2; cbn; repeat replace (min _ _) with 1 by lia.
  apply Nat.add_le_mono_l, IHla; [done|done|]; intros a' ? Ha'.
  apply H in Ha' as Hb'; [|set_solver]; destruct Hb' as (b' & H1b' & H2b' & ?).
  rewrite Hlb' in H1b'; simpl_elem_of.
  + exfalso; apply (inj a a') in H2b'; [subst; done|lia|done|done].
  + eexists; done. 
Qed.

Lemma supp_inj_le :
  (∀ a, f a > 0 -> ∃ b, m a = Some b ∧ g b > 0) ->
  supp f ≤ supp g.
Proof.
intros; apply supp_inj_le_partial. 1,2: apply NoDup_enum.
intros a _ Ha; apply H in Ha as (b & -> & ?);
eexists; repeat split; [apply elem_of_enum|done].
Qed.

End Support_Injection.

Section Domain_Mapping.

Context `{fin_A : Finite A, fin_B : Finite B}.
Context `{surj : Surj A B (=) h}.

Definition inv_hd := head ∘ inv h.

Definition dmap (f : valuation A) : valuation B :=
  λ b, summation (f <$> inv h b).

Definition inv_dmap (f : valuation B) : valuation A :=
  λ v, if decide (inv_hd (h v) = Some v) then f (h v) else 0.

Lemma dmap_sub f g :
  g .≤ f -> dmap (f .- g) = dmap f .- dmap g.
Proof.
intros H; extensionality b; unfold dmap; cbn.
rewrite summation_sub; [done|]; intros; apply H.
Qed.

Lemma inv_surj b :
  ∃ a l, inv h b = a :: l.
Proof.
assert (H := inv_not_nil h b).
destruct (inv _ _); [done|repeat eexists; done].
Qed.

Lemma inv_dmap_pos f a :
  inv_dmap f a > 0 -> inv_hd (h a) = Some a.
Proof.
unfold inv_dmap; destruct (decide _); [done|lia].
Qed.

Lemma lookup_inv_dmap b a l f :
  inv h b = a :: l -> inv_dmap f a = f b.
Proof.
intros H; assert (Ha : a ∈ inv h b) by (rewrite H; set_solver).
apply elem_of_inv_spec in Ha as <-; unfold inv_dmap, inv_hd; cbn.
rewrite H; cbn; destruct (decide _); done.
Qed.

Lemma lookup_inv_dmap_zero b a a' l f :
  inv h b = a :: l -> a' ∈ l -> inv_dmap f a' = 0.
Proof.
intros H ?; assert (Ha : a' ∈ inv h b) by (rewrite H; set_solver).
assert (Hl : NoDup (a :: l)) by (rewrite <-H; apply NoDup_inv); inv Hl.
apply elem_of_inv_spec in Ha as <-; unfold inv_dmap, inv_hd; cbn.
rewrite H; cbn; destruct (decide _); [congruence|done].
Qed.

Lemma fmap_inv_dmap b a l f g :
  f .≤ inv_dmap g -> inv h b = a :: l ->
  summation (f <$> inv h b) = f a ∧ f a ≤ g b.
Proof.
intros H1 H2; rewrite H2; cbn; split.
- replace (summation _) with 0; [lia|].
  assert (summation (f <$> l) ≤ 0 * length (f <$> l)); [|lia].
  apply summation_bound; decompose_Forall; red; etrans; [apply H1|].
  erewrite lookup_inv_dmap_zero; [done|done|].
  eapply elem_of_list_lookup_2; done.
- etrans; [apply H1|]; erewrite lookup_inv_dmap; done.
Qed.

Lemma dmap_le f g :
  f .≤ inv_dmap g -> dmap f .≤ g.
Proof.
intros ? b; cbn; unfold dmap.
destruct (inv_surj b) as (a & l & ?).
edestruct fmap_inv_dmap as [-> ?]; done.
Qed.

Lemma inv_dmap_spec f :
  dmap (inv_dmap f) = f.
Proof.
extensionality b; unfold dmap.
destruct (inv_surj b) as (a & l & H).
edestruct fmap_inv_dmap as [-> _]; [done|done|].
assert (Ha : a ∈ inv h b) by (rewrite H; set_solver).
eapply lookup_inv_dmap; done.
Qed.

Lemma size_dmap f :
  size (dmap f) = size f.
Proof.
unfold size, dmap; rewrite summation_concat; apply summation_Permutation.
replace (λ _, f <$> _) with (fmap f ∘ inv h) by done; rewrite list_fmap_compose.
rewrite <-fmap_concat_comm; apply fmap_Permutation, concat_inv_Permutation.
Qed.

Lemma supp_dmap f :
  supp (dmap f) ≤ supp f.
Proof.
apply supp_inj_le with (m:=λ b, head (filter (λ a, 0 < f a) (inv h b))).
- intros b b' a ? ? Hb Hb'; intros.
  apply head_elem_of, elem_of_list_filter in Hb as [_ Hb], Hb' as [_ Hb'].
  apply elem_of_inv_spec in Hb, Hb'; congruence.
- unfold dmap; intros b Hb.
  apply summation_nonzero in Hb as (n & Hn & ?).
  apply elem_of_list_fmap in Hn as (a & -> & Ha).
  destruct (head _) as [a'|] eqn:E; [eexists; split; [done|]|exfalso].
  + apply head_elem_of, elem_of_list_filter in E as [? _]; done.
  + apply head_None in E; eapply filter_nil_not_elem_of; [done|cbn|done]; done.
Qed.

Lemma supp_inv_dmap f :
  supp (inv_dmap f) = supp f.
Proof.
apply Nat.le_antisymm.
- apply supp_inj_le with (m:=Some ∘ h); cbn.
  + intros a a' b Ha Ha' ? ?; simplify_eq.
    apply inv_dmap_pos in Ha, Ha'; congruence.
  + intros a; unfold inv_dmap; destruct (decide _); [|lia].
    intros; eexists; done.
- apply supp_inj_le with (m:=inv_hd); cbn.
  + intros b b' a ? ? Hb Hb'.
    apply head_elem_of, elem_of_inv_spec in Hb, Hb'; congruence.
  + intros b ?; destruct (inv_surj b) as (a & l & Hb); exists a; split.
    * unfold inv_hd; cbn; rewrite Hb; done.
    * erewrite lookup_inv_dmap; done.
Qed.

Corollary size_inv_dmap f :
  size (inv_dmap f) = size f.
Proof.
rewrite <-size_dmap, inv_dmap_spec; done.
Qed.

Corollary rsize_inv_dmap k f :
  rsize k (inv_dmap f) = rsize k f.
Proof.
unfold rsize; rewrite size_inv_dmap, supp_inv_dmap; done.
Qed.

Corollary rsize_dmap k f :
  rsize k (dmap f) ≥ rsize k f.
Proof.
unfold rsize; rewrite size_dmap; assert (Hf := supp_dmap f); nia.
Qed.

End Domain_Mapping.

Global Arguments dmap {_ _ _ _ _} _ _ _ /.
Global Arguments inv_dmap {_ _ _ _ _} _ _ _ /.
