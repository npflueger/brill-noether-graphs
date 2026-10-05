module

public import Utilities.Gonality.CoreBridgeless
public import GenusSixOddDescent.Chain
public import GenusSixOddDescent.Cost
public import GenusSixOddDescent.HubSystem
public import Utilities.Iso.FossilTopology
public import GenusSixOddDescent.Reduction
public import GenusSixOddDescent.Statement

@[expose] public section

/-!
# Odd subdivision descent and conditional genus-six existence

`not_notSelected_odd` rules out nonselection by constructing a hub system and
applying the confinement obstruction. `selection_odd` then chooses four fine
chips with total slot cost less than `N`, and `descent_odd` applies the generic
rounding engine. These results require a bridgeless core and odd `N ≥ 3`.

The final theorem `bnExists_genus_six_of_oddWitness` applies the explicit
universal `GenusSixOddSubdivisionWitness` to the fossil of the input graph.
Scale one is a relabeling; every larger odd scale descends on the fossil.
Fossil invariance transports the pencil back, and the genus-six Riemann–Roch
reduction gives all nonnegative-rho pairs. Thus the final graph has no extra
minimum-degree, wedge, or bridgelessness hypothesis.

The witness `GenusSixOddSubdivisionWitness` is a hypothesis of the final
theorem, not an axiom and not an admitted theorem.  It is proved separately, by
the Draisma--Vargas count, in the library `DraismaVargasCount`.  It is the
combinatorial form of a prediction of K. Christ and Q. Ma (*Bounding the number
of graph refinements for Brill--Noether existence*, arXiv:2304.07405), obtained
from Baker's specialization of linear systems from curves to graphs; see
`GenusSixOddDescent.Statement`.  The descent implication itself is
unconditional.
-/

namespace GenusSixOddDescent

open Utilities Utilities.Gonality Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-! ## The selection property (S) at odd `N` -/

/-- **(S) at odd `N ≥ 3`.**  For a connected genus-six graph whose core is
bridgeless, a degree-four class of rank at least one on `G^{(N)}` cannot satisfy
(¬S): some effective representative has total slot cost less than `N`.

This is where the two halves of the argument meet: `Spec.hub_system` turns (¬S)
into a hub system on `G`, and `Spec.no_hub_system` (the confinement theorem of
`GenusSixOddDescent/HubSystem.lean`) says none exists in genus six.

The hypotheses `hodd` and `h3N` are those of `Spec.hub_system`.  No transport is
needed between `regularSubdivision G N hN` and
`((UnitSubdivisionPresentation.spec G).scale N hN).graph`: the former is by
definition the latter (`Utilities/Gonality/GonalityTransport.lean`). -/
theorem not_notSelected_odd (G : CFGraph) (N : ℕ) (hN : 0 < N) (hodd : Odd N)
    (h3N : 3 ≤ N) (hconn : graph_connected G) (hgenus : genus G = 6)
    (hbridge : (UnitSubdivisionPresentation.spec G).core.Bridgeless)
    {A : CFDiv (regularSubdivision G N hN)} (hdeg : deg A = 4)
    (hrank : rank (regularSubdivision G N hN) A ≥ 1) :
    ¬ (UnitSubdivisionPresentation.spec G).NotSelected N hN A := by
  intro hNS
  obtain ⟨hs⟩ :=
    Spec.hub_system (UnitSubdivisionPresentation.spec G) N hN (isUnit_unitSpec G)
      (coreConnected_unitSpec G hconn) hbridge hodd h3N hNS
      hdeg hrank (two_le_card_vertices G (by omega))
  exact (Spec.no_hub_system (UnitSubdivisionPresentation.spec G) N hN
    (isUnit_unitSpec G) (coreConnected_unitSpec G hconn)
    (by have h := genus_unitSpec G; omega)).false hs

/-- **(S), in the form the descent consumes.**  A degree-four class of rank at
least one on `G^{(N)}`, `N` odd and at least three, has an effective
representative presented by four fine chips of total slot cost less than `N`.

The cost is the `Delta` weight of `GenusSixOddDescent/Cost.lean`; at `N = 3` the
bound `Delta < 3` says that at most two slots are bad (`Delta_three`), the
hypothesis of `Utilities.Gonality.bnExists_one_four_of_badEdges_le_two`.  The
proof unfolds `Spec.NotSelected`, takes the cheap effective representative it
denies, and splits it into four chips with `effective_divisor_decomposition` and
`exists_chip_pair_of_effective_deg_two`. -/
theorem selection_odd (G : CFGraph) (N : ℕ) (hN : 0 < N) (hodd : Odd N)
    (h3N : 3 ≤ N) (hconn : graph_connected G) (hgenus : genus G = 6)
    (hbridge : (UnitSubdivisionPresentation.spec G).core.Bridgeless)
    (A : CFDiv (regularSubdivision G N hN)) (hdeg : deg A = 4)
    (hrank : rank (regularSubdivision G N hN) A ≥ 1) :
    ∃ ys : Fin 4 → (regularSubdivision G N hN).V,
      linear_equiv (regularSubdivision G N hN) A (∑ i, one_chip (ys i)) ∧
        (UnitSubdivisionPresentation.spec G).Delta N hN (∑ i, one_chip (ys i)) < N := by
  classical
  have hns : ¬ ∀ D : CFDiv (regularSubdivision G N hN), effective D →
      linear_equiv (regularSubdivision G N hN) A D →
      N ≤ (UnitSubdivisionPresentation.spec G).Delta N hN D :=
    not_notSelected_odd G N hN hodd h3N hconn hgenus hbridge hdeg hrank
  obtain ⟨D, hDeff, hDlin, hDcost⟩ : ∃ D : CFDiv (regularSubdivision G N hN),
      effective D ∧ linear_equiv (regularSubdivision G N hN) A D ∧
        (UnitSubdivisionPresentation.spec G).Delta N hN D < N := by
    by_contra hcon
    exact hns fun D hDeff hDlin => by
      by_contra hbad
      exact hcon ⟨D, hDeff, hDlin, by omega⟩
  have hDdeg : deg D = 4 := by
    rw [← linear_equiv_preserves_deg _ A D hDlin]; exact hdeg
  obtain ⟨E, F, hE, hF, hEdeg, hFdeg, hsplit⟩ :=
    effective_divisor_decomposition (regularSubdivision G N hN) D 2 2 hDeff
      (by rw [hDdeg]; norm_num)
  obtain ⟨x₁, x₂, hx⟩ :=
    exists_chip_pair_of_effective_deg_two _ E hE (by rw [hEdeg]; norm_num)
  obtain ⟨y₁, y₂, hy⟩ :=
    exists_chip_pair_of_effective_deg_two _ F hF (by rw [hFdeg]; norm_num)
  obtain ⟨ys, hys⟩ : ∃ ys : Fin 4 → (regularSubdivision G N hN).V,
      ∑ i, one_chip (ys i) = D := by
    refine ⟨![x₁, x₂, y₁, y₂], ?_⟩
    rw [Fin.sum_univ_four, hsplit, hx, hy]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    abel
  refine ⟨ys, by rw [hys]; exact hDlin, ?_⟩
  have hys' : (∑ i, one_chip (ys i) :
      CFDiv ((UnitSubdivisionPresentation.spec G).scale N hN).graph) = D := hys
  have hcost : (UnitSubdivisionPresentation.spec G).Delta N hN
      (∑ i, one_chip (ys i))
      = (UnitSubdivisionPresentation.spec G).Delta N hN D := by rw [hys']
  omega

/-! ## Odd-subdivision descent at odd `N ≥ 3` -/

/-- **Odd-subdivision descent.**  For a connected genus-six graph whose core is
bridgeless and every odd `N ≥ 3`, Brill--Noether existence for `w¹₄` on the
`N`-fold regular subdivision descends to `G` itself.

The proof is the assembly the whole chain exists to make: (S) supplies four fine
chips spanning the class of total slot cost less than `N`, and
`bnExists_one_four_of_Delta_lt` — `EdgeSumDescent.rank_ge_of_edge_sum` read
through `Delta_eq_edgeSumCost` of `GenusSixOddDescent/Cost.lean` — rounds them
to `G`. -/
theorem descent_odd (G : CFGraph) (N : ℕ) (hN : 0 < N) (hodd : Odd N)
    (h3N : 3 ≤ N) (hconn : graph_connected G) (hgenus : genus G = 6)
    (hbridge : (UnitSubdivisionPresentation.spec G).core.Bridgeless) :
    BNExists (regularSubdivision G N hN) 1 4 → BNExists G 1 4 := by
  intro hFine
  obtain ⟨A, hdeg, hrank⟩ := hFine
  obtain ⟨ys, hlin, hcost⟩ :=
    selection_odd G N hN hodd h3N hconn hgenus hbridge A hdeg hrank
  refine bnExists_one_four_of_Delta_lt G N hN ys hcost ?_
  rw [← Utilities.rank_eq_of_linear_equiv (regularSubdivision G N hN) hlin]
  exact hrank

end GenusSixOddDescent

namespace GenusSixOddDescent

open Utilities Utilities.Gonality Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph

universe u

/-- `descent_odd`, packaged as the `DescendsAt` predicate of
`GenusSixOddDescent/Statement.lean`. -/
theorem descendsAt_odd (G : CFGraph) (N : ℕ) (hN : 0 < N) (hodd : Odd N)
    (h3N : 3 ≤ N) (hconn : graph_connected G) (hgenus : genus G = 6)
    (hbridge : (UnitSubdivisionPresentation.spec G).core.Bridgeless) :
    DescendsAt G N hN :=
  descent_odd G N hN hodd h3N hconn hgenus hbridge

/-! ## Scale one -/

/-- **Descent at `N = 1` is a relabeling.**  `σ₁ G` is `G` up to the scale-one
relabeling of the unit subdivision presentation, so `BNExists` transports both
ways.  This is the `N = 1` rung of `DescendsAt`, and it needs no hypothesis at
all — in particular no `3 ≤ N`, which `Odd N` alone does not give. -/
theorem descent_one (H : CFGraph) (h1 : 0 < 1) :
    BNExists (Gonality.regularSubdivision H 1 h1) 1 4 → BNExists H 1 4 := by
  intro hFine
  have hscale :
      BNExists ((UnitSubdivisionPresentation.spec H).scale 1 h1).graph 1 4 := hFine
  have hspec : BNExists (UnitSubdivisionPresentation.spec H).graph 1 4 :=
    ((Spec.laplacianEquiv _ _
      (UnitSubdivisionPresentation.spec H).scaleOneRelabeling).bnExists_iff 1 4).mp
      hscale
  exact ((UnitSubdivisionPresentation.laplacianEquiv H).bnExists_iff 1 4).mpr hspec

/-- `descent_one`, packaged as `DescendsAt`. -/
theorem descendsAt_one (H : CFGraph) (h1 : 0 < 1) : DescendsAt H 1 h1 :=
  descent_one H h1

/-! ## All positive odd scales -/

/-- Uniform odd-scale descent on connected genus-six graphs with bridgeless
core. Split off scale one; every other positive odd scale is at least three. -/
theorem hdesc_of_descent_odd :
    ∀ H : CFGraph.{u}, graph_connected H → genus H = 6 →
      (UnitSubdivisionPresentation.spec H).core.Bridgeless →
      ∀ (N : ℕ) (hN : 0 < N), Odd N → DescendsAt H N hN := by
  intro H hconn hgenus hbridge N hN hodd
  by_cases h1 : N = 1
  · subst h1
    exact descendsAt_one H hN
  · have h3N : 3 ≤ N := by
      have := Nat.odd_iff.mp hodd
      omega
    exact descendsAt_odd H N hN hodd h3N hconn hgenus hbridge

/-! ## The headline -/

/-- **Conditional Brill--Noether existence in genus six.**  Given the
odd-subdivision witness, *every* connected genus-six graph satisfies
Brill--Noether existence at every admissible `(r, d)`.  There is no
minimum-degree hypothesis, no `NotPositiveWedge`, and no two-edge-connectivity
hypothesis: the whole chain is run on `Utilities.fossil G`, which supplies
bridgelessness of the core through `twoEdgeCutCondition_fossil` and
`core_bridgeless_of_twoEdgeCutCondition`, and `BNExists_fossil_iff` carries the
pencil back to `G`.

The witness is proved separately, by the Draisma--Vargas count, in the library
`DraismaVargasCount`. -/
theorem bnExists_genus_six_of_oddWitness (hwit : GenusSixOddSubdivisionWitness.{u})
    (G : CFGraph.{u}) (hconn : graph_connected G) (hgenus : genus G = 6)
    {r d : ℤ} (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d := by
  have hFconn : graph_connected (fossil G) := graph_connected_fossil G hconn
  have hFgenus : genus (fossil G) = 6 := by rw [genus_fossil G hconn]; exact hgenus
  have hFbridge : (UnitSubdivisionPresentation.spec (fossil G)).core.Bridgeless :=
    Gonality.core_bridgeless_of_twoEdgeCutCondition (fossil G) hFconn
      (twoEdgeCutCondition_fossil G hconn)
  obtain ⟨N, hN, hodd, hBN⟩ := hwit (fossil G) hFconn hFgenus
  have hF : BNExists (fossil G) 1 4 :=
    hdesc_of_descent_odd (fossil G) hFconn hFgenus hFbridge N hN hodd hBN
  exact bnExists_genus_six_of_rankOneDegreeFour hconn hgenus
    ((BNExists_fossil_iff G hconn 1 4).mpr hF) hR hRho

end GenusSixOddDescent
