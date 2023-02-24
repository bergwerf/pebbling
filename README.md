Graph Pebbling in Coq
=====================
This repository holds the formalization of various graph pebbling results, which
I produced over the course of my master's thesis. The Coq source is split over
multiple files which are ordered by their prefix. The prefix starts with a
a letter that indicates to which part the file belongs. There are four parts:

- **Part A** - Utility library
- **Part B** - General graph pebbling
- **Part C** - Concrete pebbling bounds
- **Part D** - Number theory constructions

This formalization was developed using *Coq 8.16.0* and *Coq-stdpp 1.8.0*. To
check the formalization, install the stdpp library ([1]) and run these commands:
```
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

[1]: https://gitlab.mpi-sws.org/iris/stdpp

Results
-------

### Unidirectional solutions via pebble flows
```
Corollary pebble_flow_spec t n c :
  (∃ c', c -->* c' ∧ n ≤ c' t) ↔
  (∃ f, feasible c f ∧ unidirectional f ∧ n ≤ excess t c f).
```

### Pebbling bound of an n-cube with generalized weights
```
Corollary pebbling_bound_hypercube :
  pebbling_bound (hypercube n ks) (product ks).
```

### Pebbling bound of n in the divisor lattice of n
```
Corollary vertex_pebbling_bound_divisor_lattice n (non_zero : Premise (n > 0)) :
  vertex_pebbling_bound (divisor_lattice n) n (top_divisor n).
```

### The Erdős-Lemke conjecture
```
Corollary Erdos_Lemke_conjecture (l : list nat) d n :
  length l = d -> d > 0 -> n > 0 -> d ∣ n -> (∀ a, a ∈ l -> a ∣ n) ->
  ∃ l', l' ≠ [] ∧ l' ⊆+ l ∧ d ∣ summation l' ∧ summation l' ≤ n.
```
