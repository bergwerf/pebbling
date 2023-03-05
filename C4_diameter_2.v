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
Hypothesis undirected : Symmetric E.

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

Lemma Forall2_elem_of_r {X Y} (P : X -> Y -> Prop) xs ys y :
  Forall2 P xs ys -> y ∈ ys -> ∃ x, x ∈ xs ∧ P x y.
Proof.
intros HP Hy; apply elem_of_list_lookup_1 in Hy as [i Hi].
eapply Forall2_lookup_r in Hi as (x & Hx & Hxy); [exists x|done].
split; [apply elem_of_list_lookup_2 in Hx|]; done.
Qed.

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
rewrite H0, H1 in H; cbn in H; clear H0 H1 filter_eq.
(* Determine c t = 0. *)
destruct (decide (c t = 0)) as [Ht|?]; [|eexists; split; [done|lia]].
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
  eapply Forall2_elem_of_r in Hy as (x & Hx & Hxy); [|done]; destruct Hxy.
  eapply elem_of_list_filter in Hx as [Hx _].
  edge_neq x y; edge_neq y t; eexists; split.
  move_pebble x y; move_pebble y t; done.
  simpl_alter; [|intro; subst]; lia. }
apply unnest_fallback in ys_zero as [ys_zero|]; [|done].
assert (xs_ys : ∀ x y, x ∈ xs -> y ∈ ys -> x ≠ y).
{ intros x y Hx Hy; apply elem_of_list_filter in Hx as [Hx _].
  apply ys_zero in Hy; intro; subst; lia. }
(* Determine NoDup ys. *)
destruct (NoDup_dec_witness ys) as [ys_nodup|(i & j & y & ? & Hi & Hj)]. 2:
{ eapply Forall2_lookup_r in Hi as (x1 & Hi & Hx); [|done]; destruct Hx;
  eapply Forall2_lookup_r in Hj as (x2 & Hj & Hx); [|done]; destruct Hx;
  assert (x1 ≠ x2) by (intro; subst; eapply NoDup_lookup in xs_nodup; done);
  apply elem_of_list_lookup_2 in Hi, Hj;
  edge_neq x1 y; edge_neq x2 y; edge_neq y t.
  eapply elem_of_list_filter in Hi as [Hx1 _], Hj as [Hx2 _].
  eexists; split. move_pebble x1 y; move_pebble x2 y; move_pebble y t; done.
  simpl_alter; [lia|intro|intro]; subst; lia. }
(* Determine length vs0 ≥ length xs + 1. *)
assert (length0 : t :: ys ⊆+ vs0).
{ apply NoDup_submseteq.
  - apply list.NoDup_cons; split; [|done]; intros Hys.
    eapply Forall2_elem_of_r in Hys as (x & Hx & Hxt); [|done];
    destruct Hxt; edge_neq t t; done.
  - intros v Hv; apply elem_of_cons in Hv as []; subst;
    apply elem_of_list_filter; split; try apply elem_of_enum; auto. }
apply submseteq_length in length0; cbn in length0.
erewrite <-Forall2_length in length0; [|done].
(* Determine v with c v ≥ 3 and xs ≡ₚ v :: xs'. *)
destruct (decide (Forall (λ k, k ≤ 2) (c <$> xs))) as [Hxs|Hxs].
apply summation_forall_le in Hxs; rewrite fmap_length in Hxs; lia.
apply not_Forall_Exists in Hxs; [|solve_decision]; clear length0.
apply list.Exists_exists in Hxs as (k & Hk & Hv); cbn in Hv.
apply elem_of_list_fmap in Hk as (v & -> & Hvxs).
apply elem_of_Permutation in Hvxs as [xs' Hxs].
assert (Hvxs : v ∈ xs) by (rewrite Hxs; set_solver).
apply elem_of_list_lookup_1 in Hvxs as [i Hi].
eapply Forall2_lookup_l in Hi as (y & Hy & HE); [|done]; destruct HE.
apply elem_of_list_lookup_2 in Hy; clear i; edge_neq v y; edge_neq y t;
assert (v ≠ t) by (intro; subst; lia).
rewrite Hxs in xs_nodup; inversion_clear xs_nodup as [|? ? ? xs'_nodup].
(* Determine zs with Forall2 (λ x z, z ≠ t ∧ E x z ∧ E z v) xs' zs. *)
assert (Hxs' : ∀ x, x ∈ xs' -> (∃ z, z ≠ t ∧ E x z ∧ E z v) ∨ solvable G t 1 c).
{ intros x ?; assert (Hx : x ∈ xs) by (rewrite Hxs; set_solver).
  apply elem_of_list_filter in Hx as Hcx; destruct Hcx as [Hcx _].
  assert (x ≠ v) by congruence.
  destruct (diam2 x v) as [|[|(z & ? & ?)]]; [done|right|].
  - dec (y = x); [apply ys_zero in Hy; lia|].
    eexists; split. move_pebble x v; move_pebble v y; move_pebble v y;
    move_pebble y t; done. simpl_alter; [|intro; subst]; lia.
  - dec (z = t); [right|left].
    + eexists; split; [edge_neq t v; move_pebble v t; done|simpl_alter; lia].
    + exists z; done. }
apply unnest_fallback in Hxs' as [Hxs'|]; [|done].
apply list_choice in Hxs' as [zs zs_spec].
(* Determine ∀ z, z ∈ zs → z ∉ ys. *)
assert (zs_ys : ∀ z, z ∈ zs -> z ∉ ys ∨ solvable G t 1 c).
{ intros z Hz; destruct (decide (z ∈ ys)) as [Hys|Hys]; [right|left; done].
  eapply Forall2_elem_of_r in Hz as (x&Hx'&Hz); [|done]; destruct Hz as (?&?&?).
  eapply Forall2_elem_of_r in Hys as (x'&_&Hz); [|done]; destruct Hz.
  assert (Hx : x ∈ xs) by (rewrite Hxs; set_solver);
  assert (x ≠ v) by (intro; congruence).
  apply elem_of_list_filter in Hx as [Hx _].
  edge_neq x z; edge_neq z v; eexists; split.
  move_pebble v z; move_pebble x z; move_pebble z t; done.
  simpl_alter; [|intro; subst]; lia. }
apply unnest_fallback in zs_ys as [zs_ys|]; [|done].
(* Determine ∀ z, z ∈ zs -> c z = 0. *)
assert (zs_zero : ∀ z, z ∈ zs -> c z = 0 ∨ solvable G t 1 c).
{ intros z Hz; dec (c z = 0); [left; done|right].
  assert (y ≠ z) by (intro; subst; apply zs_ys in Hz; done).
  eapply Forall2_elem_of_r in Hz as (x&Hz&Hx); [|done]; destruct Hx as (?&?&?).
  assert (Hx : x ∈ xs) by (rewrite Hxs; set_solver);
  assert (x ≠ y) by (apply xs_ys; done);
  assert (x ≠ v) by congruence;
  eapply elem_of_list_filter in Hx as [Hx _].
  edge_neq x z; edge_neq z v; eexists; split.
  move_pebble x z; move_pebble z v;
  move_pebble v y; move_pebble v y; move_pebble y t; done.
  simpl_alter. lia. intro; subst; lia. }
apply unnest_fallback in zs_zero as [zs_zero|]; [|done].
(* Determine NoDup zs. *)
destruct (NoDup_dec_witness zs) as [zs_nodup|(i & j & z & ? & Hi & Hj)]. 2:
{ assert (Hz : z ∈ zs) by (apply elem_of_list_lookup_2 in Hi; done);
  assert (y ≠ z) by (intro; subst; apply zs_ys in Hz; done);
  eapply Forall2_lookup_r in Hi as (x1&Hi&Hx); [|done]; destruct Hx as (?&?&?);
  eapply Forall2_lookup_r in Hj as (x2&Hj&Hx); [|done]; destruct Hx as (?&?&?).
  assert (x1 ≠ x2) by (intro; subst; eapply NoDup_lookup in xs'_nodup; done).
  apply elem_of_list_lookup_2 in Hi, Hj. 
  assert (x1 ≠ v) by congruence;
  assert (x2 ≠ v) by congruence;
  assert (Hx1 : x1 ∈ xs) by (rewrite Hxs; revert Hi; clear; set_solver);
  assert (Hx2 : x2 ∈ xs) by (rewrite Hxs; revert Hj; clear; set_solver);
  assert (x1 ≠ y) by (apply xs_ys; done);
  assert (x2 ≠ y) by (apply xs_ys; done).
  apply elem_of_list_filter in Hx1 as [Hx1 _], Hx2 as [Hx2 _].
  edge_neq x1 z; edge_neq x2 z; edge_neq z v; eexists; split.
  move_pebble x1 z; move_pebble x2 z; move_pebble z v;
  move_pebble v y; move_pebble v y; move_pebble y t; done.
  simpl_alter; [|intro|intro]; subst; lia. }
(* Determine length vs0 ≥ 2 * length xs. *)
assert (length0 : t :: zs ++ ys ⊆+ vs0).
{ apply NoDup_submseteq.
  - apply list.NoDup_cons; split; [|apply list.NoDup_app; done].
    intros Hxy; apply elem_of_app in Hxy as [Hxy|Hxy];
    apply elem_of_list_lookup_1 in Hxy as [i Hi];
    eapply Forall2_lookup_r in Hi as (x & Hi & Hx); [idtac|done|idtac|done];
    destruct Hx; [|edge_neq t t]; done.
  - intros w Hw; apply elem_of_cons in Hw as [Hw|Hw]; subst;
    apply elem_of_list_filter; split; try apply elem_of_enum; try done.
    apply elem_of_app in Hw as []; auto. }
apply submseteq_length in length0; cbn in length0;
rewrite app_length in length0.
(* Determine w with c w ≥ 4. *)
Admitted.

End Diameter_2.
