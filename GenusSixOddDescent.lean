module

public import GenusSixOddDescent.Statement
public import GenusSixOddDescent.Reduction
public import GenusSixOddDescent.Cost
public import GenusSixOddDescent.Hole
public import GenusSixOddDescent.HoleClass
public import GenusSixOddDescent.Chain
public import GenusSixOddDescent.BridgeChain
public import GenusSixOddDescent.Moves
public import GenusSixOddDescent.Swap
public import GenusSixOddDescent.HubSystem
public import GenusSixOddDescent.Main

-- A one-file public interface: the library's main theorems restated in full
-- and checked by the kernel against the real declarations.
public import GenusSixOddDescent.Highlights

@[expose] public section

/-!
# Genus-six odd-subdivision descent

This library proves that a degree-four pencil on an **odd** regular subdivision
of a connected genus-six graph descends to the graph itself, and derives from
this a conditional Brill--Noether existence theorem in genus six.  It imports
only `Utilities` and external dependencies.

## Headline declarations

* `GenusSixOddDescent.descent_odd`: for a connected genus-six graph `G` whose
  core is bridgeless and every odd `N ≥ 3`, a divisor of degree four and rank at
  least one on the `N`-fold regular subdivision of `G` yields one on `G`.
* `GenusSixOddDescent.descent_one`: at scale one the same holds for every graph,
  since the one-fold subdivision is a relabeling.
* `GenusSixOddDescent.bnExists_genus_six_of_oddWitness`: assuming
  `GenusSixOddDescent.GenusSixOddSubdivisionWitness` — every connected genus-six
  graph has an odd regular subdivision carrying a degree-four pencil — every
  connected genus-six graph satisfies Brill--Noether existence for every
  `r ≥ 0` and every `d` with `ρ(6, r, d) ≥ 0`.  No bridgelessness hypothesis
  remains: the descent is run on the fossil of the graph.
* `GenusSixOddDescent.bnExists_genus_six_of_rankOneDegreeFour`: in genus six the
  pencil `(r, d) = (1, 4)` implies every other admissible pair.

`GenusSixOddSubdivisionWitness` enters only as an explicit hypothesis of
`bnExists_genus_six_of_oddWitness`; every other result of the library is
unconditional.  The hypothesis is proved separately, by the Draisma--Vargas
count, in the library `DraismaVargasCount`.

## The modules

* `Statement`: the predicates `DescendsAt` and `GenusSixOddSubdivisionWitness`.
* `Reduction`: genus-six existence reduces to the single pair `(1, 4)`.
* `Cost`: the slot cost `Delta` of a fine divisor, the non-selection predicate
  `NotSelected` (every effective representative of the class costs at least
  `N`), and the rounding step `bnExists_one_four_of_Delta_lt`, which turns a
  representative of cost less than `N` into a pencil on the coarse graph.
* `Hole`, `HoleClass`: the hole branches through a state and the
  classification of their legal firing sets.
* `Chain`: states, the pivot lemma, reducedness and uniqueness of states,
  connectivity of the chip-slot complement of a state (`lemmaQ`), and the
  state / non-state dichotomy under non-selection.
* `BridgeChain`: the multi-firing bridge move between two states.
* `Moves`, `Swap`: the classification of the moves at a state, and the swap of
  states performed by a bridge move.
* `HubSystem`: `hub_system` builds a hub system from a non-selected rank-one
  class, and `no_hub_system` shows that none exists in genus six.
* `Main`: the assembly of the descent and of the conditional existence theorem.

The combinatorial modules state their results for an abstract subdivision
presentation, in the namespace `Utilities.Certificate.SubdivisionGraph.Spec`;
the statements about graphs live in the namespace `GenusSixOddDescent`.

Add an import line above whenever a module is added under
`GenusSixOddDescent/`, or `lake build GenusSixOddDescent` will silently skip it.
-/
