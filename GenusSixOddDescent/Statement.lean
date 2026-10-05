module

public import Utilities.Subdivision.OddSubdivisionDescent
public import Utilities.Subdivision.SquareRootDescent

@[expose] public section

/-!
# Statements for genus-six odd-subdivision descent

Two definitions, and nothing else.

* `DescendsAt G N hN`: a degree-four pencil on the `N`-fold regular subdivision of `G`
  descends to `G`.
* `GenusSixOddSubdivisionWitness`: every connected genus-six graph has an odd regular
  subdivision carrying a degree-four pencil. This is the hypothesis of the conditional
  existence theorem `GenusSixOddDescent.bnExists_genus_six_of_oddWitness`.

The witness is a hypothesis here, not a theorem of this library. It is proved separately,
by a mod-2 form of the Draisma--Vargas count, in the library `DraismaVargasCount`.

The witness is the combinatorial form of a prediction from algebraic geometry, due to
K. Christ and Q. Ma, *Bounding the number of graph refinements for Brill--Noether existence*,
arXiv:2304.07405. Degenerate a curve to one with dual graph `G`. A closed point of degree `k` of
the Brill--Noether scheme `W¹₄` of the generic fibre gives, by Baker's specialization lemma, a
degree-four pencil on the `k`-fold regular subdivision of `G` (their Proposition 4). That scheme
has degree five, the number of degree-four pencils on a general curve of genus six, which is
the bound of their Theorem 1. Five is odd, so some closed point has odd degree: some odd
regular subdivision carries a degree-four pencil, which is what the witness asserts.

The proofs are in `GenusSixOddDescent.Main`.
-/

namespace GenusSixOddDescent

open Utilities

universe u

/-- A degree-four pencil on the `N`-fold regular subdivision descends to the graph. -/
def DescendsAt (G : CFGraph) (N : ℕ) (hN : 0 < N) : Prop :=
  BNExists (Gonality.regularSubdivision G N hN) 1 4 → BNExists G 1 4

/-- Every connected genus-six graph has an odd regular subdivision carrying a degree-four
pencil. It is stated for all graphs at once so that it can be applied to the fossil of the
graph whose Brill--Noether existence is being proved. -/
def GenusSixOddSubdivisionWitness : Prop :=
  ∀ H : CFGraph.{u}, graph_connected H → genus H = 6 →
    ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
      BNExists (Gonality.regularSubdivision H N hN) 1 4

end GenusSixOddDescent
