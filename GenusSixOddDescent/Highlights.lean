import GenusSixOddDescent.Main

/-!
# Highlights of the `GenusSixOddDescent` library

**A public interface, in one file.**  The main results of this library are
restated below as `example`s whose types are written out in full and whose
proofs are the real declarations.  There is not a single new definition or
theorem here.

* **For a reader.**  The complete statements of the odd-subdivision descent and
  of the conditional genus-six existence theorem, with all of their hypotheses,
  are visible in one screen.
* **For the build.**  Each `example` is checked by the kernel against the real
  declaration, so a change to a statement is detected in this file.

**The shape of the argument.**  In genus six, Brill–Noether existence reduces
to a single critical pencil: a divisor of degree four and rank at least one.  A
pencil on an odd regular subdivision `σ_N(G)` descends to `G`: some
representative of its class has chips that round to `G`, unless every
representative is too expensive, and that alternative is ruled out by building
a *hub system* that cannot exist in genus six.  Running the descent on the
fossil of `G` removes every structural hypothesis, so a supply of pencils on
odd subdivisions — the hypothesis `GenusSixOddSubdivisionWitness` — gives
Brill–Noether existence for every connected genus-six graph.  That hypothesis
is proved separately, by the Draisma–Vargas count, which is to be published as
the library `DraismaVargasCount`.

Throughout, `regularSubdivision G N hN` is the `N`-fold regular subdivision
`σ_N(G)` (`Utilities/Gonality/GonalityTransport.lean`), and
`UnitSubdivisionPresentation.spec G` presents `G` itself as a subdivision with
all slot lengths one (`Utilities/Subdivision/UnitSubdivisionPresentation.lean`).
-/

namespace GenusSixOddDescent.Highlights

open Utilities Utilities.Gonality Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph

universe u

/-! ## The headline theorem and its hypothesis -/

/-- **The odd-subdivision witness**, unfolded: every connected genus-six graph
has an odd regular subdivision carrying a divisor of degree four and rank at
least one.  (`GenusSixOddDescent/Statement.lean`) -/
example : GenusSixOddDescent.GenusSixOddSubdivisionWitness.{u} ↔
    ∀ H : CFGraph.{u}, graph_connected H → genus H = 6 →
      ∃ (N : ℕ) (hN : 0 < N), Odd N ∧ BNExists (regularSubdivision H N hN) 1 4 :=
  Iff.rfl

/-- **Conditional Brill–Noether existence in genus six.**  Given the witness,
every connected genus-six graph has, for every `r ≥ 0` and every `d` with
`ρ(6, r, d) ≥ 0`, a divisor of degree `d` and rank at least `r`.  There is no
minimum-degree, wedge, or bridgelessness hypothesis.
(`GenusSixOddDescent/Main.lean`) -/
example (hwit : GenusSixOddDescent.GenusSixOddSubdivisionWitness.{u})
    (G : CFGraph.{u}) (hconn : graph_connected G) (hgenus : genus G = 6)
    {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d) :
    BNExists G r d :=
  GenusSixOddDescent.bnExists_genus_six_of_oddWitness hwit G hconn hgenus hr hρ

/-! ## The descent -/

/-- **Odd-subdivision descent.**  For a connected genus-six graph `G` without
bridges (in the form: the core of its unit presentation is bridgeless) and every
odd `N ≥ 3`, a degree-four pencil on `σ_N(G)` yields one on `G`.
(`GenusSixOddDescent/Main.lean`) -/
example (G : CFGraph) (N : ℕ) (hN : 0 < N) (hodd : Odd N) (h3N : 3 ≤ N)
    (hconn : graph_connected G) (hgenus : genus G = 6)
    (hbridge : (UnitSubdivisionPresentation.spec G).core.Bridgeless) :
    BNExists (regularSubdivision G N hN) 1 4 → BNExists G 1 4 :=
  GenusSixOddDescent.descent_odd G N hN hodd h3N hconn hgenus hbridge

/-- **Scale one.**  `σ_1(G)` is a relabeling of `G`, so the descent holds for
every graph, with no hypothesis at all. -/
example (G : CFGraph) (h1 : 0 < 1) :
    BNExists (regularSubdivision G 1 h1) 1 4 → BNExists G 1 4 :=
  GenusSixOddDescent.descent_one G h1

/-- The predicate `DescendsAt G N hN`, unfolded.
(`GenusSixOddDescent/Statement.lean`) -/
example (G : CFGraph) (N : ℕ) (hN : 0 < N) :
    GenusSixOddDescent.DescendsAt G N hN ↔
      (BNExists (regularSubdivision G N hN) 1 4 → BNExists G 1 4) :=
  Iff.rfl

/-- **Every positive odd scale at once**: the two cases above, as `DescendsAt`. -/
example (G : CFGraph.{u}) (hconn : graph_connected G) (hgenus : genus G = 6)
    (hbridge : (UnitSubdivisionPresentation.spec G).core.Bridgeless)
    (N : ℕ) (hN : 0 < N) (hodd : Odd N) :
    GenusSixOddDescent.DescendsAt G N hN :=
  GenusSixOddDescent.hdesc_of_descent_odd G hconn hgenus hbridge N hN hodd

/-! ## The reduction to the critical pencil -/

/-- **One pencil suffices in genus six.**  The pair `(r, d) = (1, 4)` implies
every other admissible pair: `(2, 6)` by Riemann–Roch duality, `(1, 5)` by adding
a chip, and the rest are elementary.  (`GenusSixOddDescent/Reduction.lean`) -/
example {G : CFGraph} (hG : graph_connected G) (hgenus : genus G = 6)
    (hpencil : BNExists G 1 4) {r d : ℤ} (hr : 0 ≤ r) (hρ : 0 ≤ bnNumber G r d) :
    BNExists G r d :=
  GenusSixOddDescent.bnExists_genus_six_of_rankOneDegreeFour hG hgenus hpencil hr hρ

/-! ## Inside the descent: selection

The descent rounds the four chips of a cheap representative to `G`.  The cost
`Delta` of a representative is the total distance of its slot offset sums from
multiples of `N` (`GenusSixOddDescent/Cost.lean`), and `NotSelected` says that
every effective representative costs at least `N`.  Non-selection produces a
hub system, and no hub system exists in genus six; both statements are made for
an abstract subdivision presentation `spec`. -/

/-- **Selection.**  A degree-four class of rank at least one on `σ_N(G)` has a
representative by four fine chips of total cost less than `N`.
(`GenusSixOddDescent/Main.lean`) -/
example (G : CFGraph) (N : ℕ) (hN : 0 < N) (hodd : Odd N) (h3N : 3 ≤ N)
    (hconn : graph_connected G) (hgenus : genus G = 6)
    (hbridge : (UnitSubdivisionPresentation.spec G).core.Bridgeless)
    (A : CFDiv (regularSubdivision G N hN)) (hdeg : deg A = 4)
    (hrank : rank (regularSubdivision G N hN) A ≥ 1) :
    ∃ ys : Fin 4 → (regularSubdivision G N hN).V,
      linear_equiv (regularSubdivision G N hN) A (∑ i, one_chip (ys i)) ∧
        (UnitSubdivisionPresentation.spec G).Delta N hN (∑ i, one_chip (ys i)) < N :=
  GenusSixOddDescent.selection_odd G N hN hodd h3N hconn hgenus hbridge A hdeg hrank

/-- **Non-selection gives a hub system.**  (`GenusSixOddDescent/HubSystem.lean`) -/
example {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N) (hunit : spec.IsUnit)
    (hcore : spec.core.Connected) (hbridgeless : spec.core.Bridgeless)
    (hodd : Odd N) (h3N : 3 ≤ N) {A : CFDiv (spec.scale N hN).graph}
    (hNS : spec.NotSelected N hN A) (hdeg : deg A = 4)
    (hrank : rank (spec.scale N hN).graph A ≥ 1) (hn : 2 ≤ n) :
    Nonempty (spec.HubSystem N hN) :=
  Spec.hub_system spec N hN hunit hcore hbridgeless hodd h3N hNS hdeg hrank hn

/-- **No hub system in genus six**, at any scale: a connected core with
`|E| = |V| + 5` carries none.  (`GenusSixOddDescent/HubSystem.lean`) -/
example {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N) (hunit : spec.IsUnit)
    (hcore : spec.core.Connected) (hgenus : (p : ℤ) = (n : ℤ) + 5) :
    IsEmpty (spec.HubSystem N hN) :=
  Spec.no_hub_system spec N hN hunit hcore hgenus

end GenusSixOddDescent.Highlights
