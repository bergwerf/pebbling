(*
C4. Pebbling in graphs with diameter 2
======================================
*)

From graph_pebbling Require Import A_primitives B_pebbling.

Section Diameter_2.

Context `{graph_G : Basic_Graph G, pebb_G : Pebbling_Graph G}.

Notation V := (V G).
Notation E := (E G).

Hypothesis diam2 : ∀ u v, u = v ∨ E u v ∨ ∃ w, E u w ∧ E w v.
Hypothesis weight2 : ∀ u v, weight G u v = 2.

Ltac edge_neq u v :=
  match goal with
  | H : E u v |- _ => apply irrefl_neq in H as ?
  end.

Ltac move_pebble s t := eapply rtc_l;
  [eapply one_pebble_step with (u:=s)(v:=t);
  cbn; rewrite ?weight2; [done|try (lia || simpl_alter; clia)|done]|].

Lemma list_choice {X Y} (P : X -> Y -> Prop) xs :
  (∀ x, x ∈ xs -> ∃ y, P x y) -> ∃ ys, Forall2 P xs ys.
Proof.
Admitted.

Lemma unnest_fallback {X} (P : X -> Prop) Q (xs : list X) :
  (∀ x, x ∈ xs -> P x ∨ Q) -> (∀ x, x ∈ xs -> P x) ∨ Q.
Proof.
Admitted.

Lemma NoDup_dec_witness {X} (xs : list X) :
  NoDup xs + {∃ i j x, i ≠ j ∧ xs !! i = Some x ∧ xs !! j = Some x}.
Proof.
Admitted.

Notation vs := (enum V).

Theorem pebbling_diameter_2 :
  pebbling_bound G (card V + 1).
Proof.
intros t c H; unfold card in H.
(* Partition the vertices into three sets. *)
pose (vs0 := filter (λ v, c v = 0) vs);
pose (vs1 := filter (λ v, c v = 1) vs);
pose (xs := filter (λ v, 2 ≤ c v) vs);
assert (xs_nodup : NoDup xs) by (apply list.NoDup_filter, NoDup_enum);
assert (partition : vs ≡ₚ vs0 ++ vs1 ++ xs). { unfold vs0, vs1, xs; etrans.
  eapply filter_app_Permutation. apply Permutation_app_head; etrans.
  apply filter_app_Permutation with (P:=λ v, c v = 1). apply Permutation_app;
  erewrite list_filter_filter, list_filter_iff; [done|clia|done|clia]. }
(* Simplify configuration size. *)
unfold size in H; rewrite partition in H;
rewrite ?fmap_app, ?summation_app, ?app_length, ?Nat.add_assoc in H.
assert (filter_eq : ∀ k, Forall (eq k) (c <$> filter (λ v, c v = k) vs)).
{ intros k; apply list.Forall_forall; intros i Hi.
  apply elem_of_list_fmap in Hi as (v & -> & Hv).
  apply elem_of_list_filter in Hv as [-> _]; done. }
assert (H0 : summation (c <$> vs0) = 0).
{ erewrite summation_forall_eq; [|apply filter_eq]; done. }
assert (H1 : summation (c <$> vs1) = length vs1).
{ erewrite summation_forall_eq; [|apply filter_eq];
  rewrite fmap_length; cbn; done. }
rewrite H0, H1 in H; cbn in H; clear H0 H1.
(* Determine c t = 0. *)
dec (c t = 0); [|eexists; split; [done|lia]].
(* Determine ys with Forall2 (λ x y, E x y ∧ E y t) xs ys. *)
assert (Hxs : ∀ x, x ∈ xs -> (∃ y, E x y ∧ E y t) ∨ solvable G t 1 c).
{ unfold xs; intros x Hx; apply elem_of_list_filter in Hx as [Hx _].
  assert (x ≠ t) by (intro; subst; lia).
  destruct (diam2 x t) as [|[]]; [done|right|left; done].
  eexists; split; [move_pebble x t; done|simpl_alter; lia]. }
apply unnest_fallback in Hxs as [Hxs|]; [|done].
apply list_choice in Hxs as [ys ys_spec].
(* Determine ∀ y, y ∈ ys -> c y = 0. *)
assert (ys_zero : ∀ y, y ∈ ys -> c y = 0 ∨ solvable G t 1 c).
{ intros y Hy; dec (c y = 0); [left; done|right].
  apply elem_of_list_lookup_1 in Hy as [i Hi].
  eapply Forall2_lookup_r in Hi as (x & Hi & Hx); [|done]; destruct Hx.
  assert (Hx : x ∈ xs) by (eapply elem_of_list_lookup_2; done).
  eapply elem_of_list_filter in Hx as [Hx _]. edge_neq x y; edge_neq y t.
  eexists; split. move_pebble x y; move_pebble y t; done.
  simpl_alter; [|intro; subst]; lia. }
apply unnest_fallback in ys_zero as [ys_zero|]; [|done].
(* Determine NoDup ys. *)
destruct (NoDup_dec_witness ys) as [ys_nodup|(i & j & y & ? & Hi & Hj)]. 2:
{ eapply Forall2_lookup_r in Hi as (x1 & Hi & Hx); [|done]; destruct Hx;
  eapply Forall2_lookup_r in Hj as (x2 & Hj & Hx); [|done]; destruct Hx.
  edge_neq x1 y; edge_neq x2 y; edge_neq y t;
  assert (x1 ≠ x2) by (intro; subst; eapply NoDup_lookup in xs_nodup; done);
  assert (Hx1 : x1 ∈ xs) by (eapply elem_of_list_lookup_2; done);
  assert (Hx2 : x2 ∈ xs) by (eapply elem_of_list_lookup_2; done).
  eapply elem_of_list_filter in Hx1 as [Hx1 _], Hx2 as [Hx2 _].
  eexists; split. move_pebble x1 y; move_pebble x2 y; move_pebble y t; done.
  simpl_alter; [lia|intro|intro]; subst; lia. }
(* Determine length vs0 ≥ length xs + 1. *)
assert (length0 : t :: ys ⊆+ vs0).
{ apply NoDup_submseteq.
  - apply list.NoDup_cons; split; [|done]; intros Ht.
    apply elem_of_list_lookup_1 in Ht as [i Hi].
    eapply Forall2_lookup_r in Hi as (x & Hi & Hx); [|done]; destruct Hx.
    edge_neq t t; done.
  - intros v Hv; apply elem_of_cons in Hv as []; subst;
    apply elem_of_list_filter; split; try apply elem_of_enum; auto. }
apply submseteq_length in length0; cbn in length0.
erewrite <-Forall2_length in length0; [|done].
(* Determine v with c v ≥ 3 and xs ≡ₚ v :: xs'. *)
destruct (decide (Forall (λ k, k ≤ 2) (c <$> xs))) as [Hxs|Hxs].
apply summation_forall_le in Hxs; rewrite fmap_length in Hxs; lia.
apply not_Forall_Exists in Hxs; [|solve_decision].
apply list.Exists_exists in Hxs as (k & H1k & H2k); cbn in H2k.
apply elem_of_list_fmap in H1k as (v & -> & Hv).
apply elem_of_Permutation in Hv as [xs' Hxs'].
(* Determine zs with Forall2 (λ x z, E x z ∧ E z v) xs' zs. *)
(* Determine length vs0 ≥ 2 * length xs. *)
(* Determine w with c w ≥ 4. *)
Admitted.

End Diameter_2.
