import DraismaVargasCount.Assembly

/-!
# Highlights: the genus-six odd-subdivision witness

The headline statements of the library, restated as `example`s so that they are checked against
the proved declarations.
-/

namespace DraismaVargas.Count.Highlights

open Utilities

universe u

/-- **The genus-six odd-subdivision witness.** Every connected graph of genus six has a regular
subdivision of odd order carrying a divisor of degree four and rank at least one. -/
example : ∀ H : CFGraph.{u}, graph_connected H → genus H = 6 →
    ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
      BNExists (Gonality.regularSubdivision H N hN) 1 4 :=
  DraismaVargas.Count.genusSix_witness

/-- **The base count.** Over the genus-six caterpillar of loops, at every positive request, the
fibre of degree-four tropical morphisms to trees has exactly five open classes, each of
multiplicity one. -/
example {request : Fin (6 * 2 + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot) :
    GeometricFibre.openOddCount (FibreCaterpillar.catCore 2) request (2 + 2) = 5 :=
  Assembly.openOddCount_caterpillar hRequest

/-- **Propagation.** Over every connected cubic core of genus six, at every positive general
request, the number of open classes of odd multiplicity is odd. -/
example : CountSchedule.C34 2 :=
  Assembly.c34_genusSix

end DraismaVargas.Count.Highlights
