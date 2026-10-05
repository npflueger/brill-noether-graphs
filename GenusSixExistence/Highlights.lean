module

public import GenusSixExistence.Existence
public import GenusSixExistence.OnceMarked

@[expose] public section

/-!
# Highlights: Brill--Noether existence in genus six

The headline statements of the library, restated as `example`s so that they are checked against
the proved declarations.
-/

namespace GenusSixExistence.Highlights

open Utilities

universe u

/-- **Brill--Noether existence in genus six.** Every connected graph of genus six has, for all
integers `r ≥ 0` and `d` with `ρ = g - (r + 1)(g - d + r) ≥ 0`, a divisor of degree `d` and rank
at least `r`. -/
example (G : CFGraph.{u}) (hG : graph_connected G) (hGenus : genus G = 6) {r d : ℤ}
    (hr : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) : BNExists G r d :=
  GenusSixExistence.bnExists G hG hGenus hr hRho

/-- **Brill--Noether existence through genus six**, in the form of the Atanasov--Ranganathan
theorem through genus five. -/
example : ∀ (G : CFGraph.{0}) (hG : graph_connected G), genus G ≤ 6 →
    ∀ r d : ℤ, brill_noether_conjecture hG r d :=
  GenusSixExistence.brillNoetherExistenceThroughSix

/-- **Once-marked Brill--Noether existence through genus five**, at every vertex. -/
example : ∀ (G : CFGraph.{0}), graph_connected G → genus G ≤ 5 →
    ∀ x : G.V, OnceMarkedBNExistence G x :=
  GenusSixExistence.onceMarkedBNExistenceThroughFive

end GenusSixExistence.Highlights
