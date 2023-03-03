(*
B3. Pebbling with Flow Networks
===============================
*)

From graph_pebbling Require Import A_primitives B1_graph_pebbling.

Section Pebble_Flow.

Context `{graph_G : Basic_Graph G, pebb_G : Pebbling_Graph G}.

Notation V := (V G).
Notation E := (E G).
Notation weight := (weight G).
Notation ω := (uncurry weight).
Notation conf := (conf G).
Notation flow := (V * V -> nat).
Notation vertices := (enum V).

Definition flux (d : V -> V * V) (f : flow) := summation (f ∘ d <$> vertices).
Definition x_in : V -> V -> V * V := (λ v, (., v)).
Definition x_out : V -> V -> V * V := (λ v, (v ,.)).

Global Arguments x_in _ _ /.
Global Arguments x_out _ _ /.

Notation inflow v := (flux (x_in v)).
Notation outflow v := (flux (x_out v)).
Notation total_inflow f := (summation ((λ v, inflow v f) <$> vertices)).
Notation total_outflow f := (summation ((λ v, outflow v f) <$> vertices)).

Definition excess (v : V) (c : conf) (f : flow) :=
  c v + inflow v f - outflow v (ω .* f).

Record feasible (c : conf) (f : flow) : Prop := {
  feasible_support : ∀ u v, f (u, v) > 0 -> E u v;
  feasible_excess : ∀ v, outflow v (ω .* f) ≤ c v + inflow v f;
}.

Inductive flow_step : conf * flow -> conf * flow -> Prop :=
  flow_one_pebble (c c' : conf) (f f' : flow) (u v : V)
  (H_edge : E u v)
  (H_conf : weight u v ≤ c u)
  (H_flow : 1 ≤ f (u, v))
  (R_conf : c' = alter S v (alter (subtract (weight u v)) u c))
  (R_flow : f' = alter (subtract 1) (u, v) f) :
  flow_step (c, f) (c', f').

Global Instance : Step (conf * flow) := flow_step.

Definition realized c f :=
  ∀ v, excess v c f ≤ c v.

Definition realizable (c : conf) (f : flow) :=
  ∃ c' f', (c, f) -->* (c', f') ∧ realized c' f'.

Definition unidirectional (f : flow) :=
  ∀ u v, f (u, v) = 0 ∨ f (v, u) = 0.

Section Equivalence.

Section Helper_lemmas.

Global Instance inj_x_in v : Inj eq eq (x_in v).
Proof. intros ? ?; cbn; congruence. Qed.

Global Instance inj_x_out v : Inj eq eq (x_out v).
Proof. intros ? ?; cbn; congruence. Qed.

Lemma flux_bound d v f :
  flux d f ≥ f (d v).
Proof.
apply elem_of_summation, elem_of_list_fmap.
eexists; split; [done|apply elem_of_enum].
Qed.

Lemma weight_cases f u v :
  (∀ u v, f (u, v) > 0 -> E u v) ->
  f (u, v) = 0 ∨ weight u v > 1.
Proof.
intros H; dec (f (u, v) = 0); [left; done|].
assert (Hf : f (u, v) > 0) by lia.
eapply H, pebbling_weight_gt1 in Hf; right; done.
Qed.

Lemma outflow_bound v f :
  (∀ u v, f (u, v) > 0 -> E u v) ->
  outflow v (ω .* f) ≥ outflow v f.
Proof.
intros H; apply summation_le; intros u _; cbn.
apply (weight_cases f v u) in H; nia.
Qed.

Lemma flow_mul_alter `{distr : LeftDistr _ _ (=) Nat.mul g}
  (f1 f2 : flow) e n :
  f1 .* alter (g n) e f2 = alter (g (f1 e * n)) e (f1 .* f2).
Proof.
extensionality e'; cbn; dec (e = e');
simpl_alter; cbn; done.
Qed.

Lemma flux_sub d f1 f2 :
  f2 .≤ f1 -> flux d (f1 .- f2) = flux d f1 - flux d f2.
Proof.
intros H; unfold flux; rewrite right_distr_compose_lift2.
apply summation_sub; intros v _; apply H.
Qed.

Section Alter.

Context `{l_domi : LeftDominant _ P (+)}.
Context `{l_comm : CondLeftComm _ (=) P g (+)}.

Variable f : flow.
Variable d : V -> V * V.
Hypothesis inj_d : Inj (=) (=) d.

Lemma flux_alter v e :
  d v = e -> P (f e) -> flux d (alter g e f) = g (flux d f).
Proof.
unfold flux; rewrite ?list_fmap_compose.
intros <- H; apply foldr_alter. done.
- apply elem_of_list_fmap_1, elem_of_enum.
- apply NoDup_fmap; [done|apply NoDup_enum].
Qed.

Lemma flux_alter_ne e :
  (∀ v, d v ≠ e) -> flux d (alter g e f) = flux d f.
Proof.
unfold flux; rewrite ?list_fmap_compose.
intros; f_equal; apply fmap_no_alter; intros H_in.
apply elem_of_list_fmap in H_in as (v & Hv & _); eapply H; done.
Qed.

End Alter.

End Helper_lemmas.

Ltac done_or_nia := try (done || nia).

Ltac rw_flux_ne := rewrite flux_alter_ne;
  [|unfold x_in, x_out; congruence].

Ltac rw_inflow w u := rewrite flux_alter with (d:=x_in w)(v:=u); cbn;
  [|apply inj_x_in|done_or_nia|done_or_nia].

Ltac rw_outflow w u := rewrite flux_alter with (d:=x_out w)(v:=u); cbn;
  [|apply inj_x_out|done_or_nia|done_or_nia].

Ltac rw_conf := repeat (rewrite fn_lookup_alter in * ||
  (rewrite fn_lookup_alter_ne in *; [|done_or_nia])).

Ltac flow_cases u v w :=
  replace S with ((+) 1) by done; rewrite ?flow_mul_alter;
  dec (w = u); [dec (v = u)|dec (w = v)]; rw_conf;
    [rw_inflow u u; rw_outflow u u
    |rw_outflow u v; rw_flux_ne
    |rw_inflow v u; rw_flux_ne
    |repeat rw_flux_ne]; cbn in *; lia || nia.

Ltac flux_le v abbr H_supp :=
  unfold abbr, outflow, inflow; rewrite ?right_distr_compose_lift2;
  apply summation_le; intros u _; cbn;
  lia || nia || apply (weight_cases _ v u) in H_supp; nia.

Lemma flow_step_pebble_step c c' f f' :
  (c, f) --> (c', f') -> c --> c'.
Proof. inversion_clear 1; eapply one_pebble_step; done. Qed.

Lemma flow_step_feasible c c' f f' :
  (c, f) --> (c', f') -> feasible c f -> feasible c' f'.
Proof.
inversion_clear 1; intros [H1f H2f]; split.
- intros x y; dec ((x, y) = (u, v)); [done|]; simpl_alter; apply H1f.
- intros w; assert (Hw := H2f w); subst; flow_cases u v w.
Qed.

Lemma flow_step_excess c c' f f' w :
  (c, f) --> (c', f') -> excess w c f = excess w c' f'.
Proof.
inversion 1; subst; unfold excess;
assert (H_out := flux_bound (x_out u) v (ω .* f));
assert (H_in := flux_bound (x_in v) u f); cbn in H_in, H_out, H_conf;
flow_cases u v w.
Qed.

Lemma flow_balance f :
  total_inflow f = total_outflow f.
Proof.
unfold flux, compose, x_in, x_out; rewrite ?summation_lprod.
erewrite list_fmap_ext with (g:=f ∘ swap); [|intros i [] _; done].
erewrite list_fmap_ext with (g:=f)(f:=uncurry _); [|intros i [] _; done].
apply summation_Permutation, submseteq_Permutation_length_eq.
- rewrite ?fmap_length, ?prod_length; done.
- rewrite list_fmap_compose; apply submseteq_fmap, NoDup_submseteq.
  + apply NoDup_fmap. apply inj_swap. apply NoDup_lprod; apply NoDup_enum.
  + intros; apply elem_of_list_fmap in H as ([u v] & -> & _); cbn.
    apply elem_of_lprod; apply elem_of_enum.
Qed.

Lemma minimum_weight_outflow u f :
  outflow u f > 0 -> ∃ v, f (u, v) > 0 ∧
  weight u v * outflow u f ≤ outflow u (ω .* f).
Proof.
unfold outflow; generalize vertices as vs;
induction vs as [|v vs]; cbn; intros; [lia|].
dec (summation (f ∘ x_out u <$> vs) = 0).
exists v; lia. destruct IHvs as (w & H1 & H2); [lia|].
dec (0 < f (u, v) ∧ weight u v < weight u w);
[exists v|exists w]; cbn in *; nia.
Qed.

Theorem pebble_flow_realizable c f :
  feasible c f -> realizable c f.
Proof.
revert c f; apply (induction_ltof1 _ size (λ c, ∀ f, _ -> _)); unfold ltof.
intros c IH f [H1f H2f].
(* 1. Find a vertex r where the excess is not realized: inflow r > outflow r *)
destruct (decide (realized c f)) as [Hr|Hr]. exists c, f; split; done.
apply not_forall_exists in Hr as [r Hx]; unfold excess in Hx.
assert (Ho := outflow_bound r f H1f);
assert (Hr : inflow r f > outflow r f) by lia; clear Hx.
(* 2. Find complementary vertex s using flow balance: inflow s < outflow s *)
destruct (decide (∀ s, outflow s f ≤ inflow s f)) as [Hs|Hs]; [exfalso|].
{ assert (H3f := flow_balance f).
  assert (H4f : total_outflow f < total_inflow f).
  apply summation_lt with (x:=r); try done; apply elem_of_enum. lia. }
(* 3. Determine a minimum weight outflow edge of s. *)
apply not_forall_exists in Hs as [s Hs]; assert (H1s := H2f s);
assert (H2s : outflow s f > inflow s f) by lia; clear Hs;
assert (Hc : size c ≥ c s) by apply size_lwb.
destruct (minimum_weight_outflow s f) as (t & H1t & H2t); [lia|].
(* 4. Add one flow step and solve using induction hypothesis. *)
pose (c1 := alter S t (alter (subtract (weight s t)) s c));
pose (f1 := alter (subtract 1) (s, t) f);
assert (H_step : (c, f) --> (c1, f1)).
- apply flow_one_pebble with (u:=s)(v:=t).
  apply H1f; done. nia. lia. done. done.
- destruct IH with (y:=c1)(f:=f1) as (c' & f' & H1 & H2).
  + eapply pebble_step_size, flow_step_pebble_step, H_step.
  + eapply flow_step_feasible; done.
  + exists c', f'; split; [|done]. eapply rtc_l; done.
Qed.

Theorem pebble_flow_sound t c f :
  feasible c f -> solvable G t (excess t c f) c.
Proof.
intros; destruct (pebble_flow_realizable c f) as (c' & f' & H1 & H2); [done|].
exists c'; split.
- replace c with (c, f).1 by done;
  replace c' with (c', f').1 by done.
  apply @rtc_congruence with (R:=step); [|done].
  intros [] []; apply flow_step_pebble_step.
- replace (excess t c f) with (excess t c' f'); [apply H2|].
  eapply rtc_congruence with (f:=λ p, excess t p.1 p.2), unwrap_rtc in H1.
  done. intros [] []; apply flow_step_excess.
Qed.

Theorem pebble_flow_complete t n c :
  solvable G t n c -> ∃ f, feasible c f ∧ n ≤ excess t c f.
Proof.
intros (c' & Hc & Hn); induction Hc as [c|c1 c2 c']. 
- (* Base: zero flow. *)
  exists (const 0); repeat split; cbn; intros. lia. all: unfold excess, flux;
  rewrite list_fmap_ext with (f:=(_.*_)∘_)(g:=const 0); cbn;
  rewrite ?summation_const; lia.
- (* Step: add one flow unit. *)
  apply IHHc in Hn as (f2 & [H1f2 H2f2] & Hn); clear IHHc; inversion_clear H.
  exists (alter S (u, v) f2); repeat split.
  + intros x y; dec ((x, y) = (u, v)); [done|]; simpl_alter; apply H1f2.
  + intros w; assert (Hw := H2f2 w); subst; flow_cases u v w.
  + unfold excess in *; subst; flow_cases u v t.
Qed.

Theorem pebble_flow_unidirectional c f :
  feasible c f -> ∃ f', feasible c f' ∧ unidirectional f' ∧
  ∀ v, excess v c f ≤ excess v c f'.
Proof.
intros [H_supp H_excess]; exists (f .- lift_min f (f ∘ swap));
repeat split; intros.
- apply H_supp; cbn in *; lia.
- rewrite left_distr, ?flux_sub; repeat intro; cbn; [|lia|nia].
  assert (Hv := H_excess v); pose (g := lift_min f (f ∘ swap));
  assert (outflow v (ω .* g) ≥ inflow v g) by flux_le v g H_supp.
  unfold g in *; lia.
- intros u v; clia.
- unfold excess; rewrite left_distr, ?flux_sub; repeat intro; cbn; [|nia|lia].
  pose (g := lift_min f (f ∘ swap));
  assert (inflow v f ≥ inflow v g) by flux_le v g H_supp.
  assert (outflow v (ω .* f) ≥ outflow v (ω .* g)) by flux_le v g H_supp.
  assert (outflow v (ω .* g) ≥ inflow v g) by flux_le v g H_supp.
  unfold g in *; lia.
Qed.

Corollary pebble_flow_spec t n c :
  (∃ c', c -->* c' ∧ n ≤ c' t) ↔
  (∃ f, feasible c f ∧ unidirectional f ∧ n ≤ excess t c f).
Proof.
split.
- intros H; apply pebble_flow_complete in H as (f & Hf & Ht).
  apply pebble_flow_unidirectional in Hf as (f' & H1 & H2 & H3).
  exists f'; split; [done|split]; [done|etrans]; done.
- intros (f & Hf & _ & Ht); apply (pebble_flow_sound t c) in Hf.
  destruct Hf as (c' & H1 & H2); exists c'; split; [done|etrans]; done.
Qed.

End Equivalence.

End Pebble_Flow.

Notation flow G := (V G * V G -> nat).
Notation inflow v := (flux (x_in v)).
Notation outflow v := (flux (x_out v)).

Global Arguments excess _ {_}.
Global Arguments feasible _ {_}.
Global Arguments realized _ {_}.
Global Arguments realizable _ {_}.
Global Arguments unidirectional {_}.
