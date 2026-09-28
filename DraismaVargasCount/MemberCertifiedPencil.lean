import DraismaVargasCount.MemberCoreDarts
import DraismaVargasCount.FibreCaterpillar
import DraismaVargas.LocalCases.CaterpillarSeed
import DraismaVargas.LocalCases.SeedFromContraction
import DraismaVargas.LocalCases.TerminalIdentification
import DraismaVargas.LocalCases.TrackedState
import Utilities.Subdivision.ConnectedCheckFast

/-!
# The certified pencil from a fibre member

**Source.**  Vargas, Part II (arXiv:2609.09109): the labelled fibre of the count and
the endgame of the proof of the main theorem (`thm`); Draisma--Vargas Part I
(arXiv:1909.12924): the terminal step of the atlas march, which turns a terminal
tracked state into a pencil.  This file produces a certified pencil, in the sense of
Part I's march, directly from a fibre member.

## Why the march's own terminal state is not reused

The terminal tracked state of Part I's march can have **even** determinantal
multiplicity (in computer experiments, almost all closed members found this way
have `|Mult| = 2`), so the endgame cannot be completed by handing Part I's
terminal state to the pencil construction.  Nothing here does.  `seedState` builds
a **synthetic one-chart march state** out of an *arbitrary* member: one chart,
whose matrix is the member's own length matrix, whose terminal coordinate vector
is the member's own `coords`, and whose payload is the member's own candidate.  No
step is ever taken, no wall is ever crossed, and the vector the pencil is cleared at
is the member's, not the walk's.  Consequently the multiplicity of the object
produced is the *member's* multiplicity, and what has to be plugged in here is a
closed member of odd multiplicity.

## What is proved

* `coreIdentOfEquivalence` -- a stable-graph incidence dictionary carries a
  `Count.CoreIdentification`, in the shape `Count.transportIdent`
  has for a `DatumIso`.
* `seedState`, `carriesCertifiedPencil_of_seed` -- **the producer**: a
  `LocalCases.SeedCandidate.Seed`, a full-dimensional presentation of its
  candidate on the request's slot type, a core identification of that candidate,
  and the realization equation produce
  `LocalCases.CertifiedPencil.CarriesCertifiedPencil spec degree A start coords`.
  The oriented `endpoint` isomorphism that
  `LocalCases.TerminalIdentification.carriesCertifiedPencil_of_tracked` demands is
  `MemberCoreDarts.coreIso`; the slot equivalence is the composite
  `fd.labelling.row.symm.trans ident.row`.
* `MemberSeed` -- the one receipt a `Count.FibreMember` needs beyond its own
  fields in order to be presented as a `BalancedGlobal.Candidate`: a target edge
  with distinct ends, joined by no other edge, whose source fibre is a forest.
  A candidate always lives over a one-edge expansion of *its* target, so a bare
  member cannot be one; `LocalCases.SeedFromContraction` contracts that edge and
  re-expands, and `MemberSeed.matrix_eq` and `MemberSeed.ident_row` record that
  neither the length matrix nor the slot dictionary moves.
* `carriesCertifiedPencil_of_member` -- the same statement at a
  `Count.FibreMember spec.core (fun slot => (spec.length slot : ℚ)) degree`.
* `caterpillarMemberSeed`, `caterpillarCoreIso` -- non-vacuity (§5).

## Whether the producer needs `Closed`, and whether it needs odd multiplicity

No statement here mentions a multiplicity, and no proof here uses one: **the
producer is count-independent**.  More precisely:

* `carriesCertifiedPencil_of_member` needs **neither** `member.Closed` **nor**
  `Odd member.oddMult`.  `CarriesCertifiedPencil` states its certificate half
  *under* the hypothesis that the finish vector is nonnegative, so the predicate
  is meaningful, and provable, at every member.
* Nonnegativity of `member.coords`, i.e. `member.Closed`, is exactly terminality
  of the synthetic state.
* `Odd member.oddMult` is used **nowhere**.  It enters later, on the scale of the
  pencil: odd multiplicity gives odd denominators (`OddDenominator`) and the
  slot-moment divisibility (`SurvivingSlotMap`).

## What is NOT proved (every hypothesis, explicitly)

* `spec.core.Cubic` and `spec.core.Connected` are explicit hypotheses
  everywhere.  They are what `LocalCases.CubicCoreDarts.ofCore` needs, and
  nothing here derives them from the member.
* `2 ≤ degree` is an explicit hypothesis, inherited from
  `LocalCases.TrackedPencil.of_tracks`, which uses it for the source-genus
  conjunct.  It is harmless at the endgame's `degree = 4`.
* `MemberSeed member` is an explicit hypothesis, and it is a genuine one: a
  member is *not* by itself a candidate.  It is inhabited (below), but not
  derived here: `MemberSeedExists.nonempty_memberSeed_of_member` derives it at
  degree at least three.
* A strictly positive `start : Fin p → ℚ` is an explicit argument.  It is
  unconstrained -- `1` will do -- and is used only to clear a positive pencil at
  the state's start vector, which the payload's shape requires.
* **No inhabitant of the `Spec`-indexed conclusion is exhibited here.**  The
  caterpillar member `Count.FibreCaterpillar.caterpillarMember` has the caterpillar
  *of loops* as its core, which is not a `SubdivisionGraph.Spec.core` (`Spec`
  demands `core_loopless`).  What is inhabited below is the receipt `MemberSeed`
  and the oriented dart dictionary, both at the genus-six caterpillar.
* Nothing here counts anything, and nothing here produces the member.

## Consumers

`MemberSeedTree` and `MemberSeedExists` reduce and then discharge the `MemberSeed`
receipt.  The receipt and the synthetic one-chart state are used to present frame
members as candidates at type-change walls (`FacetAdapterPilot`,
`LinkReceiptExport`, `ColumnReceiptExport`), and `StepSupplyGenusSix` uses the
cubicity and connectivity of `catCore 2` proved in §5.
-/

namespace DraismaVargas.Count.MemberCertifiedPencil

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.Count.MemberCoreDarts
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ}

/-! ## 1.  Transport of a core identification, and two cast lemmas -/

/-- A stable-graph incidence dictionary carries a core identification. -/
def coreIdentOfEquivalence {core : Core n p} {target₁ target₂ : CFGraph.{0}}
    {degree₁ degree₂ : ℕ} {first : GluingDatum target₁ degree₁}
    {second : GluingDatum target₂ degree₂}
    (dict : StableGraphIncidence.Equivalence first second)
    (ident : CoreIdentification core first) : CoreIdentification core second where
  vertex := dict.vertex.symm.trans ident.vertex
  row := dict.row.symm.trans ident.row
  incidence branch slot := by
    have hdict := dict.incidence (dict.vertex.symm branch) (ident.row.symm slot)
    have hident := ident.incidence (dict.vertex.symm branch) slot
    rw [Equiv.apply_symm_apply] at hdict
    exact hdict.symm.trans hident

section Cast

variable {T : CFGraph.{0}} {core : Core n p}

theorem cast_labelling_matrix {d₁ d₂ : GluingDatum T degree} (h : d₁ = d₂)
    (fd : FullDimensionalSourcePresentation d₁ (Fin p)) :
    GluingDatum.LengthMatrixPresentation.matrix (h ▸ fd).labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation := by
  subst h; rfl

theorem cast_ident_row {d₁ d₂ : GluingDatum T degree} (h : d₁ = d₂)
    (fd : FullDimensionalSourcePresentation d₁ (Fin p))
    (ident : CoreIdentification core d₁) (r : Fin p) :
    (h ▸ ident).row ((h ▸ fd).labelling.row.symm r) =
      ident.row (fd.labelling.row.symm r) := by
  subst h; rfl

end Cast

/-! ## 2.  The producer from a candidate-presented member -/

section Seed

variable {spec : Spec n p} {seed : SeedCandidate.Seed degree}
  (fd : FullDimensionalSourcePresentation seed.candidate.datum (Fin p))
  (ident : CoreIdentification spec.core seed.candidate.datum)

/-- The chart matrix of a candidate-presented member. -/
noncomputable def seedMatrix : Matrix (Fin p) (Fin p) ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation

/-- Matrix rows are read as core slots through the identification. -/
noncomputable def seedSlots : Fin p ≃ Fin p := fd.labelling.row.symm.trans ident.row

/-- The requested stable metric, in matrix-row coordinates. -/
noncomputable def seedBaseFinish : Fin p → ℚ :=
  fun r ↦ ((spec.length (seedSlots fd ident r) : ℕ) : ℚ)

/-- **The synthetic one-chart march state.**  No march is run: the state is a
data container whose terminal coordinate vector is the member's own `coords`,
whose start is an arbitrary strictly positive vector, and whose payload is the
member's own candidate.  This is what keeps the construction independent of the
walk and of the walk's terminal multiplicity. -/
noncomputable def seedState (hDegree : 2 ≤ degree)
    (coords start : Fin p → ℚ) (hStart : ∀ i, 0 < start i)
    (hRealizes : (seedMatrix fd).mulVec coords = seedBaseFinish fd ident) :
    TrackedState degree (TrackedPencil.seedGraph seed fd)
      (TrackedPencil.seedLabel seed fd) (fun _ : Unit ↦ seedMatrix fd)
      ((seedMatrix fd).mulVec start) (seedBaseFinish fd ident) where
  toMatrixState := FiniteAtlasMarch.State.initial () start coords hStart rfl hRealizes
  carriesTrackedPencil := TrackedPencil.ofSeed hDegree seed fd start hStart

/-- **The producer, at a candidate-presented member.** -/
theorem carriesCertifiedPencil_of_seed
    (hCubic : spec.core.Cubic) (hCoreConnected : spec.core.Connected)
    (hDegree : 2 ≤ degree) (coords start : Fin p → ℚ) (hStart : ∀ i, 0 < start i)
    (hRealizes : (seedMatrix fd).mulVec coords = seedBaseFinish fd ident) :
    CertifiedPencil.CarriesCertifiedPencil spec degree (seedMatrix fd) start coords := by
  refine TerminalIdentification.carriesCertifiedPencil_of_tracked (F := ∅)
    hCubic hCoreConnected
    (coreIso fd.connected fd.pathEnds ident fd.trivalent hCubic hCoreConnected)
    (seedSlots fd ident) ?_ ?_
    (seedState fd ident hDegree coords start hStart hRealizes)
  · intro d
    show seedSlots fd ident (fd.labelling.row (row seed.candidate.datum d)) =
      (dartEquiv fd.connected fd.pathEnds ident d).1
    rw [dartEquiv_fst]
    show ident.row (fd.labelling.row.symm (fd.labelling.row (row seed.candidate.datum d))) = _
    rw [Equiv.symm_apply_apply]
  · funext r
    simp [seedBaseFinish]

end Seed

/-! ## 3.  The contraction receipt that presents a member as a candidate -/

/-- **The one receipt the producer needs beyond the member itself.**  A `FibreMember`
carries a target and a datum, not a `BalancedGlobal.Candidate`, and a candidate
lives over a *one-edge expansion* of its own target.  So a member has to be
presented as the re-expansion of a contraction of its own target: one target
edge with distinct ends, joined by no other edge, whose source fibre is a
forest.  This is exactly the input of
`LocalCases.SeedFromContraction.seed`, and the only thing it adds to the
member's own full-dimensionality receipt. -/
structure MemberSeed {core : Core n p} {y : Fin p → ℚ}
    (member : FibreMember core y degree) where
  /-- The first end of the contracted target edge. -/
  first : member.target.V
  /-- The second end of the contracted target edge. -/
  second : member.target.V
  /-- The contracted target edge itself. -/
  contracted : member.target.edges
  /-- Its stored endpoints. -/
  endpoints : (contracted : member.target.V × member.target.V) = (first, second)
  /-- It is not a loop. -/
  distinct : first ≠ second
  /-- It is the only edge joining its ends. -/
  numEdges : num_edges member.target first second = 1
  /-- Its source fibre is a forest, so contracting preserves validity. -/
  forest : ContractionRamification.ContractionForest member.data first second contracted

namespace MemberSeed

variable {core : Core n p} {y : Fin p → ℚ} {member : FibreMember core y degree}
  (ms : MemberSeed member)

/-- The contraction/re-expansion isomorphism of targets. -/
noncomputable def targetIso := SeedFromContraction.iso ms.endpoints ms.distinct ms.numEdges

/-- The member, presented as a neutral seed candidate. -/
noncomputable def seed : SeedCandidate.Seed degree :=
  SeedFromContraction.seed member.data ms.endpoints ms.distinct ms.numEdges
    member.fullDim.targetConnected member.fullDim.targetGenus member.fullDim.valid ms.forest

theorem datumEq :
    GluingTransport.transport ms.targetIso member.data = ms.seed.candidate.datum :=
  (SeedFromContraction.seed_datum member.data ms.endpoints ms.distinct ms.numEdges
    member.fullDim.targetConnected member.fullDim.targetGenus member.fullDim.valid
    ms.forest).symm

/-- The member's full-dimensional presentation, moved to the transported datum. -/
noncomputable def transportedFullDim :
    FullDimensionalSourcePresentation
      (GluingTransport.transport ms.targetIso member.data) (Fin p) :=
  RelabelFullDimensional.targetPresentation ms.targetIso member.fullDim

/-- The member's core identification, moved to the transported datum. -/
noncomputable def transportedIdent :
    CoreIdentification core (GluingTransport.transport ms.targetIso member.data) :=
  coreIdentOfEquivalence
    (TargetRelabelStable.graphEquivalence ms.targetIso member.data member.fullDim.valid.1)
    member.ident

/-- The member's full-dimensional presentation, on the seed's candidate. -/
noncomputable def fullDim :
    FullDimensionalSourcePresentation ms.seed.candidate.datum (Fin p) :=
  ms.datumEq ▸ ms.transportedFullDim

/-- The member's core identification, on the seed's candidate. -/
noncomputable def ident : CoreIdentification core ms.seed.candidate.datum :=
  ms.datumEq ▸ ms.transportedIdent

/-- The presentation is the member's own length matrix: the contraction and
re-expansion append no column and permute no row. -/
theorem matrix_eq :
    GluingDatum.LengthMatrixPresentation.matrix ms.fullDim.labelling.presentation =
      member.matrix :=
  (cast_labelling_matrix ms.datumEq ms.transportedFullDim).trans
    (RelabelFullDimensional.target_matrix_eq ms.targetIso member.data
      member.fullDim.valid.1 member.fullDim.labelling)

/-- The core slot a matrix row names is unchanged by the presentation. -/
theorem ident_row (r : Fin p) :
    ms.ident.row (ms.fullDim.labelling.row.symm r) =
      member.ident.row (member.fullDim.labelling.row.symm r) := by
  refine (cast_ident_row ms.datumEq ms.transportedFullDim ms.transportedIdent r).trans ?_
  show member.ident.row ((TargetRelabelStable.stablePathEquiv ms.targetIso member.data
      member.fullDim.valid.1).symm ((TargetRelabelStable.stablePathEquiv ms.targetIso
        member.data member.fullDim.valid.1) (member.fullDim.labelling.row.symm r))) = _
  rw [Equiv.symm_apply_apply]

end MemberSeed

/-! ## 4.  The producer at a labelled fibre member -/

section Member

variable {spec : Spec n p}
  {member : FibreMember spec.core (fun slot ↦ ((spec.length slot : ℕ) : ℚ)) degree}

theorem seedMatrix_memberSeed (ms : MemberSeed member) :
    seedMatrix ms.fullDim = member.matrix := ms.matrix_eq

theorem realizes_memberSeed (ms : MemberSeed member) :
    (seedMatrix ms.fullDim).mulVec member.coords = seedBaseFinish ms.fullDim ms.ident := by
  rw [seedMatrix_memberSeed]
  refine member.realizes.trans ?_
  funext r
  show ((spec.length (member.ident.row (member.fullDim.labelling.row.symm r)) : ℕ) : ℚ) = _
  rw [seedBaseFinish]
  show _ = ((spec.length (ms.ident.row (ms.fullDim.labelling.row.symm r)) : ℕ) : ℚ)
  rw [ms.ident_row]

/-- **The producer.**  A labelled fibre member over the requested cubic core,
presented as a candidate by one contraction receipt, carries a certified
pencil.  The member is arbitrary: neither its multiplicity nor its being closed
is used here. -/
theorem carriesCertifiedPencil_of_member (ms : MemberSeed member)
    (hCubic : spec.core.Cubic) (hCoreConnected : spec.core.Connected)
    (hDegree : 2 ≤ degree) (start : Fin p → ℚ) (hStart : ∀ i, 0 < start i) :
    CertifiedPencil.CarriesCertifiedPencil spec degree member.matrix start member.coords := by
  have h := carriesCertifiedPencil_of_seed ms.fullDim ms.ident hCubic hCoreConnected
    hDegree member.coords start hStart (realizes_memberSeed ms)
  rwa [seedMatrix_memberSeed] at h

end Member

/-! ## 5.  Non-vacuity -/

section Witness

open DraismaVargas.Count.FibreCaterpillar

/-- **The receipt is inhabited.**  The caterpillar-of-loops member of every
even genus carries one: the first slope-two spine occurrence of
`LocalCases.CaterpillarSeed`, whose edge partition equals both of its endpoint
partitions, so every contracted source fibre is a single edge. -/
noncomputable def caterpillarMemberSeed (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    MemberSeed (caterpillarMember m request) where
  first := CaterpillarTree.catParent m (CaterpillarSeed.cutIndex m)
  second := (CaterpillarSeed.cutIndex m).succ
  contracted := CaterpillarSeed.cut m
  endpoints := CaterpillarTree.occ_coe m (CaterpillarSeed.cutIndex m)
  distinct := CaterpillarSeed.cut_endpoints_ne m
  numEdges := CaterpillarSeed.cut_num_edges m
  forest := CaterpillarSeed.cut_forest m

/-- The presented caterpillar member still displays the caterpillar's own
length matrix. -/
theorem caterpillarMemberSeed_matrix (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    GluingDatum.LengthMatrixPresentation.matrix
        (caterpillarMemberSeed m request).fullDim.labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix
        (CaterpillarRows.labelling m).presentation :=
  (caterpillarMemberSeed m request).matrix_eq

/-- Genus six: the caterpillar-of-loops core is cubic. -/
theorem catCore_two_cubic : (catCore 2).Cubic := by
  unfold Core.Cubic
  decide +kernel

/-- Genus six: the caterpillar-of-loops core is connected. -/
theorem catCore_two_connected : (catCore 2).Connected :=
  Core.connected_of_connectedCheckFast (by decide +kernel)

/-- **The oriented dictionary is inhabited.**  The stable graph of the
genus-six caterpillar member is its own core as a cubic dart graph, with each
stable row's two darts at the two named ends of its slot -- including the `g`
self-loops, whose two darts sit at the one branch vertex. -/
noncomputable def caterpillarCoreIso (request : Fin (6 * 2 + 3) → ℚ) :=
  coreIso (caterpillarMember 2 request).fullDim.connected
    (caterpillarMember 2 request).fullDim.pathEnds
    (caterpillarMember 2 request).ident
    (caterpillarMember 2 request).fullDim.trivalent
    catCore_two_cubic catCore_two_connected

end Witness

end DraismaVargas.Count.MemberCertifiedPencil
