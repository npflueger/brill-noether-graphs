import Utilities.Subdivision.OddSubdivisionDescent
import Utilities.Subdivision.SquareRootDescent

/-!
# Statements for genus-six odd-subdivision descent

Two definitions, and nothing else.

* `DescendsAt G N hN`: a degree-four pencil on the `N`-fold regular subdivision of `G`
  descends to `G`.
* `GenusSixOddSubdivisionWitness`: every connected genus-six graph has an odd regular
  subdivision carrying a degree-four pencil. This is the hypothesis of the conditional
  existence theorem `GenusSixOddDescent.bnExists_genus_six_of_oddWitness`.

The witness is a hypothesis here, not a theorem of this library. It is proved separately,
by the Draisma--Vargas count, which is to be published as the library `DraismaVargasCount`.
It is also motivated by algebraic geometry: Baker's specialization lemma, applied to a
degeneration of a genus-six curve with dual graph `G`, carries a degree-four pencil of the
curve to a degree-four pencil on some regular subdivision of `G`; the witness asks for a
subdivision of odd scale.

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
