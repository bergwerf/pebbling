(*
D1. Zero Sum Sequences
======================
We prove that given an infinite sequence α and a number n, there exists numbers
i and k such that 0 < k and i + k ≤ n and the sequence α_{i}..α_{i+k} sums to 0
modulo n. The proof for this theorem is based on a "sliding window" over the
first n elements of α.
*)

From graph_pebbling Require Import A_primitives.

Lemma unfold_mod i n :
  n ≠ 0 -> ∃ m, i `mod` n = i - n * m ∧ n * m ≤ i.
Proof. exists (i `div` n); nia. Qed.

Ltac unfold_mod m :=
  let H := fresh "H" in
  edestruct unfold_mod as (m & -> & H); [done|].

Theorem zero_sum_sequence (α : nat -> nat) n :
  n ≠ 0 -> ∃ i k, 0 < k ∧ i + k ≤ n ∧ n ∣ summation (α <$> seq i k).
Proof.
intros Hn; pose (β i := summation (α <$> seq 0 i) `mod` n).
destruct (nat_pigeonhole β (S n) n) as (i&j&H1&H2); unfold β in *; [lia|lia|].
exists i, (j - i); repeat split; [lia|lia|]; revert H2.
replace j with (i + (j - i)) at 1 by lia.
rewrite seq_app, fmap_app, summation_app; cbn.
unfold_mod m_i; unfold_mod m_j; exists (m_j - m_i); nia.
Qed.

Lemma fmap_seq_take_drop {A} (α : nat -> A) i k l :
  (∀ j, i ≤ j < i + k -> l !! j = Some (α j)) ->
  α <$> seq i k = take k (drop i l).
Proof.
induction k; intros.
- symmetry; apply take_0.
- erewrite seq_S, take_S_r, fmap_app, IHk. done.
  + intros; apply H; lia.
  + rewrite lookup_drop; apply H; lia.
Qed.

Corollary zero_sum_sublist (l : list nat) :
  l ≠ [] -> ∃ l', l' ≠ [] ∧ l' `sublist_of` l ∧ length l ∣ summation l'.
Proof.
intros Hl; apply non_empty_length in Hl; pose (α i := default 0 (l !! i)).
destruct (zero_sum_sequence α (length l)) as (i & k & H1 & H2 & H3); [done|].
eexists; split; [|split; [|done]].
- apply non_empty_length; rewrite fmap_length, seq_length; lia.
- erewrite fmap_seq_take_drop.
  + etrans; [apply sublist_take|apply sublist_drop].
  + intros; unfold α; destruct (l !! j) eqn:E; [done|exfalso].
    apply lookup_ge_None in E; lia.
Qed.
