import DraismaVargas.LocalCases.OrientedTraversal
import DraismaVargas.LocalCases.SeedDeterminant

/-!
# The genus receipt at a terminal face, for a *fixed* specification

At a terminal state the requested specification `spec : Spec n p` is fixed,
while the gluing datum -- the cover the classifier produces -- is a choice.
This module isolates the one global condition the specification imposes on
that choice, the genus receipt

```lean
SourceGenusMatches spec datum : genus datum.sourceGraph = genus spec.graph
```

-- the quotient source of the gluing datum has the genus of the requested
stable specification -- and packages what a local case owes at one terminal
state as `TerminalCertificate`.

## 1.  The refined counts see the specification only through `n` and `p`

`survivingCount` is the number of source occurrences a cleared face does not
contract, counted along the displayed rows; it mentions no specification and no
interface.  `iface.slot` is an equivalence `Fin p ≃ coordinate`, so the counts
of the refined specification are read off it: `refinedSpec_p_eq_survivingCount`
(the refined slot count is `survivingCount`) and `refinedSpec_n_add_eq` (the
refined core count is `n` plus that number, less `p`).  The state pins `p` (it
is `Fintype.card coordinate`, through `iface.slot`) and the slot lengths
(through `iface.matrixMap`), but it does not pin `n`, and `n` is the whole of
the specification these counts can see.  What decides the global count is the
datum.

## 2.  The genus receipt

`SourceGenusMatches` mentions the datum and the two numbers `n`, `p` and
nothing else: no interface, no strong presentation, no cleared face, no
contraction topology and no relabeling.  So a classifier discharges it when it
*builds* the datum, by a computation such as
`SeedDeterminant.genus_sourceGraph_starDatum`.  `sourceGenusMatches_iff`
unfolds it to the integer identity `p - n + 1 = genus datum.sourceGraph`.

## 3.  At a fixed specification both truth values occur

For a **fixed** `spec`, vary the datum over the concrete star covers of
`SeedDeterminant`:

```lean
sourceGenusMatches_starDatum (spec : Spec n p) (k : ℕ) :
  SourceGenusMatches spec (starDatum k) ↔ (k : ℤ) = (p : ℤ) - (n : ℤ) + 2
exists_sourceGenusMatches_and_not (spec : Spec n p) ((n : ℤ) ≤ (p : ℤ) + 2) :
  ∃ k l, SourceGenusMatches spec (starDatum k) ∧ ¬ SourceGenusMatches spec (starDatum l)
```

Both truth values occur among the concrete star covers, so no argument from the
fixed specification alone can settle the receipt: it is a genuine condition on
the datum.  This is a statement about the receipt only; it does not construct
completed terminal faces over those covers, which would need an actual
`Candidate` and `ClearedFace`.

## 4.  The terminal certificate

`TerminalCertificate` is what a local case owes at one terminal state: the
cover and its candidate, the strong presentation, the interface and row
dictionary, the placement conditions (`spanning`, and injectivity of the
canonical `vertexClass`, the local half), the chart identity, the target
hypotheses, and the genus receipt as the single field `sourceGenus` (the
global half), which is about the gluing datum alone.

`RowDictionary`, `refinedSpec` and `starDatum` are used, not modified.  The new
names are `survivingCount`, `SourceGenusMatches` and `TerminalCertificate`.
-/

namespace DraismaVargas.LocalCases.TerminalExhausts

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.TraversalPresentation

/-! ## 1.  The refined counts see the specification only through `n` and `p` -/

section Independent

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ} {n p m : ℕ} {spec : Spec n p}

/-- The number of source occurrences a cleared face does **not** contract,
counted along the displayed rows.  No specification and no interface enter:
the sum is over the coordinate type itself. -/
def survivingCount (face : ClearedFace candidate presentation coordinates) : ℕ :=
  ∑ row : coordinate, (presentation.path row).countP
    fun edge ↦ decide (0 < face.realization.sourceLength edge)

/-- The refined slot count is that number. -/
theorem refinedSpec_p_eq_survivingCount
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    (refinedSpec iface face).p = survivingCount face := by
  rw [refinedSpec_p_eq_countP]
  exact Equiv.sum_comp iface.slot fun row ↦ (presentation.path row).countP
    fun edge ↦ decide (0 < face.realization.sourceLength edge)

/-- and the refined core count is `n` plus that number, less `p`. -/
theorem refinedSpec_n_add_eq
    (iface : InputInterface spec presentation coordinates)
    (face : ClearedFace candidate presentation coordinates) :
    (refinedSpec iface face).n + p = n + survivingCount face := by
  have hn := refinedSpec_n iface face
  have hp := refinedSpec_p iface face
  have hs := refinedSpec_p_eq_survivingCount iface face
  omega

end Independent

/-! ## 2.  The condition: the datum's source has the requested genus -/

section Condition

variable {target : CFGraph} {degree : ℕ} {n p : ℕ}

/-- **The genus receipt.**  The quotient source of the gluing datum has the
genus of the requested stable specification.

It mentions the datum and the two numbers `n`, `p` and nothing else: no
interface, no strong presentation, no cleared face, no contraction topology and
no relabeling.  So it is a statement a classifier can discharge at the moment it
*builds* the datum, by the same kind of computation as
`SeedDeterminant.genus_sourceGraph_starDatum`. -/
def SourceGenusMatches (spec : Spec n p) (datum : GluingDatum target degree) :
    Prop :=
  genus datum.sourceGraph = genus spec.graph

/-- Unfolded against `Spec.genus_graph`: the receipt is the Euler identity
`p - n + 1 = genus datum.sourceGraph`. -/
theorem sourceGenusMatches_iff (spec : Spec n p)
    (datum : GluingDatum target degree) :
    SourceGenusMatches spec datum ↔
      (p : ℤ) - (n : ℤ) + 1 = genus datum.sourceGraph := by
  rw [SourceGenusMatches, Spec.genus_graph]
  exact eq_comm

end Condition

/-! ## 3.  At a *fixed* specification both truth values of the receipt occur -/

section Discrimination

open DraismaVargas.LocalCases.SeedDeterminant

variable {target : CFGraph} {degree : ℕ} {n p : ℕ}

/-- **The source of the `k`-ray star cover carries the receipt for exactly one
`k`.**  `SeedDeterminant.genus_sourceGraph_starDatum` computes that genus in
closed form, so the receipt is decided by an integer comparison. -/
theorem sourceGenusMatches_starDatum (spec : Spec n p) (k : ℕ) :
    SourceGenusMatches spec (starDatum k) ↔ (k : ℤ) = (p : ℤ) - (n : ℤ) + 2 := by
  rw [sourceGenusMatches_iff, genus_sourceGraph_starDatum]
  omega

/-- so for every specification of nonnegative genus there is a concrete valid
gluing datum carrying it. -/
theorem exists_sourceGenusMatches (spec : Spec n p)
    (hGenus : (n : ℤ) ≤ (p : ℤ) + 2) :
    ∃ k : ℕ, SourceGenusMatches spec (starDatum k) := by
  refine ⟨((p : ℤ) - (n : ℤ) + 2).toNat, ?_⟩
  rw [sourceGenusMatches_starDatum]
  omega

/-- and a concrete valid gluing datum failing it. -/
theorem exists_not_sourceGenusMatches (spec : Spec n p) :
    ∃ k : ℕ, ¬ SourceGenusMatches spec (starDatum k) := by
  by_cases hZero : SourceGenusMatches spec (starDatum 0)
  · refine ⟨1, fun hOne ↦ ?_⟩
    rw [sourceGenusMatches_starDatum] at hZero hOne
    omega
  · exact ⟨0, hZero⟩

/-- **The fixed-specification dichotomy.**  Hold the requested specification
fixed and vary the gluing datum, which is what a terminal construction actually
gets to choose.  Both truth values of the genus receipt occur among the
concrete star covers of `SeedDeterminant`, so the receipt is not determined by
the fixed specification: it is a condition the datum either carries or does
not. -/
theorem exists_sourceGenusMatches_and_not (spec : Spec n p)
    (hGenus : (n : ℤ) ≤ (p : ℤ) + 2) :
    ∃ k l : ℕ, SourceGenusMatches spec (starDatum k) ∧
      ¬ SourceGenusMatches spec (starDatum l) := by
  obtain ⟨k, hk⟩ := exists_sourceGenusMatches spec hGenus
  obtain ⟨l, hl⟩ := exists_not_sourceGenusMatches spec
  exact ⟨k, l, hk, hl⟩

end Discrimination

/-! ## 4.  The terminal certificate -/

section Payoff

open Utilities
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.SemanticAtlasMarch

variable {coordinate chart : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- **What a local case owes at one terminal state**: the cover, its
presentation and row dictionary, the placement conditions and the target
hypotheses, with the genus obligation reduced to the single field
`sourceGenus`, which is about the gluing datum alone. -/
structure TerminalCertificate {n p : ℕ} (spec : Spec n p)
    (state : State degree matrix baseStart baseFinish)
    (hTerminal : state.Terminal) where
  /-- The target of the cover the classifier produces. -/
  target : CFGraph.{0}
  /-- and the gluing datum over it. -/
  gluing : GluingDatum target degree
  /-- the wall vertex it is expanded at, -/
  wall : target.V
  /-- and the candidate it assembles into. -/
  candidate : Candidate target degree gluing wall
  /-- The strong presentation displaying the stable paths. -/
  strong : StrongPresentation candidate.datum coordinate
  /-- The labelling of the stable slots by matrix rows. -/
  iface : InputInterface spec strong.toPresentation
    state.toMatrixState.currentFinish
  /-- The row dictionary: the three-field `TraversalPresentation.CoreDictionary`
  (it mentions no face). -/
  dict : RowDictionary strong spec iface
  /-- The placement lands on row ends only, so every refined core vertex sits
  on a surviving vertex and reaches a kept class. -/
  spanning : StrongRefinement.Spanning (RowDictionary.coreDictionary dict)
  /-- The local half of the carried field: distinct refined core vertices land
  on distinct contraction classes. -/
  injective : ∀ topology : ClearedFace.SourceContractionTopology
      (ZeroFreeTerminalFace.clearedFaceOfTerminal hTerminal candidate
        strong.toPresentation),
    Function.Injective (RowDictionary.vertexClass dict topology)
  /-- **The global half, as a receipt on the datum.**  It is not determined by
  the specification (§3), and it is one integer identity between the datum and
  the requested specification. -/
  sourceGenus : SourceGenusMatches spec candidate.datum
  /-- The presentation displays the chart matrix of the state. -/
  presentation_matrix :
    GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.toMatrixState.label
  /-- and the usual target hypotheses. -/
  valid : gluing.Valid
  /-- The target is connected, -/
  connected : graph_connected target
  /-- and a tree. -/
  targetGenus : genus target = 0

end Payoff

end DraismaVargas.LocalCases.TerminalExhausts
