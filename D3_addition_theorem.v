(*
D3. The Addition Theorem of Lemke and Kleitman
==============================================
*)

From graph_pebbling Require Import
  A_primitives
  B_pebbling
  C3_divisor_lattice
  D1_zero_sum_sequence
  D2_pebbling_construction.

Section Lemke_Kleitman.

Variable d : nat.

Definition well_placed p l :=
  l ≠ [] ∧ p ∣ summation l ∧ summation (gcd d <$> l) ≤ p.

Lemma gcd_pebbling_step p k (ls : list (list nat)) :
  p ≠ 0 -> k ≠ 0 -> Forall (well_placed p) ls -> length ls = k ->
  ∃ l, l ⊆+ concat ls ∧ well_placed (k * p) l.
Proof.
intros Hp Hk H1_ls H2_ls; pose (f l := summation l / p).
edestruct zero_sum_sublist with (l:=f <$> ls) as (l & H1 & H2 & H3).
- apply non_empty_length; rewrite fmap_length, H2_ls; done.
- apply non_empty_length in H1; revert H3; rewrite fmap_length, H2_ls; intros.
  apply sublist_fmap_inv in H2 as (ls' & H2 & ->); rewrite fmap_length in H1.
  exists (concat ls'); repeat split.
  + apply sublist_submseteq, sublist_concat; done.
  + (* The result is non-empty. *)
    apply non_empty_length, non_empty_inv in H1 as [l H1].
    assert (Hl : well_placed p l).
    * eapply list.Forall_forall; [done|].
      eapply elem_of_submseteq; [|apply sublist_submseteq]; done.
    * destruct Hl as (Hl & _ & _); apply non_empty_inv in Hl as [i Hi].
      eapply non_empty_elem, elem_of_concat; done.
  + (* The result is a multiple of k*p. *)
    destruct H3 as [m H3]; exists m; unfold f in *.
    eapply submseteq_Forall in H1_ls; [|apply sublist_submseteq; done].
    rewrite (assoc Nat.mul), <-H3; revert Hp H1_ls; clear; intros Hp.
    induction ls' as [|l ls]; cbn; inversion_clear 1; [done|].
    rewrite summation_app, right_distr, <-IHls; [|done].
    destruct H as (_ & [m ->] & _); rewrite Nat.div_mul; done.
  + (* The result GCD sum is at most k*p. *)
    rewrite fmap_concat_comm, <-summation_concat.
    etrans; [apply summation_bound with (k:=p)|]; [|rewrite fmap_length].
    * apply list.Forall_forall; intros i Hi.
      apply elem_of_list_fmap in Hi as (l & -> & Hl); red.
      eapply list.Forall_forall in H1_ls as (_ & _ & H). done.
      eapply elem_of_submseteq; [|apply sublist_submseteq]; done.
    * apply sublist_length in H2; nia.
Qed.

Theorem Lemke_Kleitman_addition_theorem (l : list nat) :
  length l = d -> d > 0 ->
  ∃ l', l' ≠ [] ∧ l' ⊆+ l ∧ d ∣ summation l' ∧ summation (gcd d <$> l') ≤ d.
Proof.
intros Hl Hd; assert (non_zero : Premise (d > 0)) by done.
edestruct @pebbling_construction with (pebbles:=l) as (l' & Hl').
3: rewrite Hl; apply vertex_pebbling_bound_divisor_lattice.
- (* Each number can be placed on a vertex. *)
  intros i Hi.
  assert (H : gcd d i ∣ d) by apply Nat.gcd_divide; exists (dexist (gcd d i) H).
  instantiate (1 := λ v p, well_placed (`v) p); cbn; split; [done|cbn].
  split; rewrite Nat.add_0_r; [apply Nat.gcd_divide|done].
- (* Each step can be constructed. *)
  cbn; intros [p Hp] [q Hq]; cbn; apply bool_decide_unpack in Hp, Hq.
  intros ls [_ [k ->]] H1_ls H2_ls; assert (p ≠ 0) by (destruct Hp; lia).
  rewrite Nat.div_mul in H2_ls; [|done].
  apply gcd_pebbling_step; [done|destruct Hq; nia|done|done].
- cbn in Hl'; destruct Hl' as [H1 (H2 & H3 & H4)]; eexists; done.
Qed.

End Lemke_Kleitman.

Corollary Erdos_Lemke_conjecture (l : list nat) d n :
  length l = d -> d > 0 -> n > 0 -> d ∣ n -> (∀ a, a ∈ l -> a ∣ n) ->
  ∃ l', l' ≠ [] ∧ l' ⊆+ l ∧ d ∣ summation l' ∧ summation l' ≤ n.
Proof.
intros ? ? ? [m Hm] Hl; destruct (Lemke_Kleitman_addition_theorem d l)
as (l' & ? & ? & ? & ?); [done|done|]; exists l'; repeat split; try done.
replace l' with (gcd n <$> l').
- etrans; [apply summation_le with (g:=const m .* gcd d)|].
  + intros a ?; cbn; assert (Ha : a ∈ l) by (eapply elem_of_submseteq; done).
    apply Hl in Ha; rewrite <-Nat.gcd_mul_mono_l, <-Hm; apply Nat.divide_pos_le.
    * destruct (gcd _ _) eqn:E; [|lia]; apply Nat.gcd_eq_0_l in E; lia.
    * apply Nat.gcd_greatest, Nat.divide_mul_r; apply Nat.gcd_divide.
  + rewrite summation_mul_const, Hm; apply Nat.mul_le_mono; done.
- erewrite list_fmap_ext; [apply list_fmap_id|]; intros i a Ha; cbn.
  rewrite Nat.gcd_comm; apply Nat.divide_gcd_iff; [lia|].
  eapply Hl, elem_of_submseteq; [|done].
  eapply elem_of_list_lookup_2; done.
Qed.
