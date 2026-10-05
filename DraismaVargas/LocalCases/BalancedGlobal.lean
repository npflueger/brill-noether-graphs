module

public import DraismaVargas.LocalCases.BalancingValencyTwo
public import DraismaVargas.LocalCases.GlobalAssembly
public import DraismaVargas.Infrastructure.RationalRealization
public import DraismaVargas.Infrastructure.TargetTreePotential

@[expose] public section

/-!
# Balanced families of global wall resolutions

The local case analysis in Draisma--Vargas produces several resolutions of a
single contracted target edge. Two logically distinct facts are needed:

* every resolution is an actual valid gluing datum with the prescribed wall;
* their length-matrix determinants satisfy a positive balancing relation.

This file joins those facts. The first theorem extracts a valid resolution
whose determinant has the opposite sign from any chosen nondegenerate member.
The second applies the one-column cone-wall calculation and produces the
positive outgoing deformation step. Thus a concrete local case can finish
its continuation proof by supplying only its resolution receipts, length
matrices, common off-wall columns, and one of the balance identities already
proved in `BalancingValencyTwo` or `BalancingRemaining`.

## The nonsingularity gate on `hSystems`

Both exit theorems ask for a compatible velocity system
`M_in · v = M_out · v'` only at those members whose length matrix is
**nonsingular**.  `PositiveBalance` is a *signed* balance
(see its definition in `BalancingValencyTwo`), so it explicitly permits
`det = 0`: a
degenerate member is a resolution that is not full-dimensional, and the wall
figures contain those.  For such a member the system need not be solvable at
all, so an ungated obligation is not merely inelegant, it is refutable —
`ClassifiedContinuation.SingularMember.no_total_registration_of_singularFamily`
exhibits a `PresentedFamily` with a provably singular member and derives
`False` from the ungated form.  Nothing is lost by gating: both proofs use the
system only at the member `exists_opposite_of_positiveBalance` selects, and
that member satisfies `d_in * d_out < 0`, hence `det ≠ 0`
(`det_ne_zero_of_mul_det_neg`).  A caller holding an ungated hypothesis
`h : ∀ outgoing, …` supplies `fun outgoing _ ↦ h outgoing`.
-/

namespace DraismaVargas.LocalCases.BalancedGlobal

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.ResolutionM11

variable {target : CFGraph} {degree : ℕ}

/-- All occurrence-level data needed to install one blockwise resolution of a
wall vertex. Its outgoing datum and validity proof are derived, not stored. -/
structure Candidate (target : CFGraph) (degree : ℕ)
    (data : GluingDatum target degree) (wall : target.V) where
  right : target.edges → Bool
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ anchor,
    (resolution anchor).ContractsTo (data.vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ anchor, (data.edgePartition edge).RefinesOnBlock
      (if right edge then (resolution anchor).right
        else (resolution anchor).left)
      (data.vertexPartition wall) anchor
  leftEdges : List target.edges
  rightEdges : List target.edges
  leftEdges_eq : (leftEdges : Multiset target.edges) =
    (wallEdgesAssigned target wall right false).val
  rightEdges_eq : (rightEdges : Multiset target.edges) =
    (wallEdgesAssigned target wall right true).val
  left_riemannHurwitz : ∀ anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (resolution anchor).left
      ((resolution anchor).newEdge ::
        leftEdges.map data.edgePartition) anchor
  right_riemannHurwitz : ∀ anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (resolution anchor).right
      ((resolution anchor).newEdge ::
        rightEdges.map data.edgePartition) anchor

namespace Candidate

/-- The actual occurrence-labelled outgoing datum represented by a candidate. -/
noncomputable def datum
    (candidate : Candidate target degree data wall) :
    GluingDatum (TargetExpansion.graph target wall candidate.right) degree :=
  GlobalAssembly.datum data wall candidate.right candidate.resolution
    candidate.contracts candidate.exterior

/-- The actual new quotient-source edge occurrence through a chosen sheet in
the globally assembled candidate. -/
noncomputable def newSourceEdge
    (candidate : Candidate target degree data wall) (sheet : Fin degree) :
    candidate.datum.SourceEdge :=
  GlobalResolution.newSourceEdge data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
      candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right
      candidate.resolution candidate.contracts candidate.exterior)
    sheet

/-- The regrown source edge lies above the distinguished new target
occurrence in the canonical `Option` labelling of the expansion. -/
@[simp] theorem newSourceEdge_target
    (candidate : Candidate target degree data wall) (sheet : Fin degree) :
    (candidate.newSourceEdge sheet).1.1 =
      TargetExpansion.occurrenceEquiv target wall candidate.right none := rfl

@[simp] theorem newSourceEdge_sheet
    (candidate : Candidate target degree data wall) (sheet : Fin degree) :
    (candidate.newSourceEdge sheet).1.2 =
      (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
        candidate.contracts).newEdge.repr sheet := rfl

/-- Its dilation index is the new-edge block cardinality in the pasted local
resolution. -/
@[simp] theorem sourceEdgeIndex_newSourceEdge
    (candidate : Candidate target degree data wall) (sheet : Fin degree) :
    candidate.datum.sourceEdgeIndex (candidate.newSourceEdge sheet) =
      (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
        candidate.contracts).newEdge.blockCard sheet := by
  exact GlobalResolution.sourceEdgeIndex_newSourceEdge data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
      candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right
      candidate.resolution candidate.contracts candidate.exterior)
    sheet

/-- Lift a literal old quotient-source occurrence into the retained target
edge of a globally assembled candidate. -/
noncomputable def oldSourceEdge
    (candidate : Candidate target degree data wall) (edge : data.SourceEdge) :
    candidate.datum.SourceEdge :=
  GlobalResolution.oldSourceEdge data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
      candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right
      candidate.resolution candidate.contracts candidate.exterior)
    edge

/-- A retained source edge lies above the canonically labelled copy of its
old target occurrence. -/
@[simp] theorem oldSourceEdge_target
    (candidate : Candidate target degree data wall) (edge : data.SourceEdge) :
    (candidate.oldSourceEdge edge).1.1 =
      TargetExpansion.occurrenceEquiv target wall candidate.right
        (some edge.1.1) := rfl

/-- Retaining an old source occurrence preserves its canonical sheet
representative literally. -/
@[simp] theorem oldSourceEdge_sheet
    (candidate : Candidate target degree data wall) (edge : data.SourceEdge) :
    (candidate.oldSourceEdge edge).1.2 = edge.1.2 := rfl

/-- Retaining an old source occurrence in a candidate preserves its dilation
index. -/
@[simp] theorem sourceEdgeIndex_oldSourceEdge
    (candidate : Candidate target degree data wall) (edge : data.SourceEdge) :
    candidate.datum.sourceEdgeIndex (candidate.oldSourceEdge edge) =
      data.sourceEdgeIndex edge := by
  exact GlobalResolution.sourceEdgeIndex_oldSourceEdge data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
      candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right
      candidate.resolution candidate.contracts candidate.exterior)
    edge

/-- Every candidate assembled from the recorded local receipts is globally
valid whenever the contracted datum is valid. -/
theorem datum_valid (candidate : Candidate target degree data wall)
    (hValid : data.Valid) :
    candidate.datum.Valid := by
  exact GlobalAssembly.datum_valid data wall candidate.right
    candidate.resolution candidate.contracts candidate.exterior hValid
    candidate.leftEdges candidate.rightEdges candidate.leftEdges_eq
    candidate.rightEdges_eq candidate.left_riemannHurwitz
    candidate.right_riemannHurwitz

/-- A positive rational metric on any globally assembled candidate clears to
an explicit integral source subdivision carrying the degree-`degree`
rank-one pencil.  Connectedness and genus zero of the old target are preserved
by the one-edge target expansion. -/
theorem bnExists_of_positiveRational
    (candidate : Candidate target degree data wall)
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (targetLength :
      (TargetExpansion.graph target wall candidate.right).edges → ℚ)
    (hPositive : ∀ edge, 0 < targetLength edge) :
    BNExists
      ((GluingDatum.IntegralRealization.ofPositiveRational candidate.datum
        targetLength hPositive).sourceSpec.graph) 1 degree := by
  let realization :=
    GluingDatum.IntegralRealization.ofPositiveRational candidate.datum
      targetLength hPositive
  exact
    (realization.bnExists_and_effective_of_connected_genus_zero_target
      (candidate.datum_valid hValid).1
      (TargetExpansion.graph_connected target wall candidate.right
        hTargetConnected)
      (by rw [TargetExpansion.graph_genus target wall candidate.right,
        hTargetGenus])
      (TargetExpansion.oldVertex target root)).1

/-- The explicit semantic object obtained by clearing one candidate's
positive rational coordinate vector. -/
structure ClearedPencil
    (candidate : Candidate target degree data wall)
    {coordinate : Type*}
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) where
  realization : candidate.datum.IntegralRealization
  scale : ℕ
  scale_pos : 0 < scale
  targetLength_eq : ∀ column,
    (realization.targetLength (presentation.targetEdge column) : ℚ) =
      (scale : ℚ) * coordinates column
  bnExists : BNExists realization.sourceSpec.graph 1 degree

/-- Clear positive target coordinates and retain their exact common scale in
the resulting subdivision pencil. -/
noncomputable def clearedPencil
    (candidate : Candidate target degree data wall)
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    {coordinate : Type*}
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (coordinates : coordinate → ℚ) (hPositive : ∀ i, 0 < coordinates i) :
    ClearedPencil candidate presentation coordinates := by
  let targetLength :
      (TargetExpansion.graph target wall candidate.right).edges → ℚ := fun edge ↦
    coordinates (presentation.targetEdge.symm edge)
  have hTargetPositive : ∀ edge, 0 < targetLength edge := by
    intro edge
    exact hPositive (presentation.targetEdge.symm edge)
  let realization :=
    GluingDatum.IntegralRealization.ofPositiveRational candidate.datum
      targetLength hTargetPositive
  let scale := candidate.datum.rationalRealizationScale targetLength
  refine {
    realization := realization
    scale := scale
    scale_pos := candidate.datum.rationalRealizationScale_pos targetLength
    targetLength_eq := ?_
    bnExists := candidate.bnExists_of_positiveRational hValid
      hTargetConnected hTargetGenus root targetLength hTargetPositive
  }
  intro column
  change
    ((GluingDatum.IntegralRealization.ofPositiveRational candidate.datum
      targetLength hTargetPositive).targetLength
        (presentation.targetEdge column) : ℚ) =
      (candidate.datum.rationalRealizationScale targetLength : ℚ) *
        coordinates column
  rw [GluingDatum.IntegralRealization.ofPositiveRational_targetLength_cast]
  simp [targetLength]

end Candidate

/-- A globally valid outgoing candidate, allowing different resolutions to
have different expanded target types. The validity implication is populated
by an occurrence-level construction such as `Candidate.certified`, rather
than postulated by the balancing argument. -/
structure CertifiedCandidate (data : GluingDatum target degree) where
  outgoingTarget : CFGraph
  datum : GluingDatum outgoingTarget degree
  valid_of_old : data.Valid → datum.Valid

namespace Candidate

/-- Forget the presentation of a locally assembled resolution while retaining
its outgoing datum and the derived global validity theorem. -/
noncomputable def certified
    (candidate : Candidate target degree data wall) : CertifiedCandidate data where
  outgoingTarget := TargetExpansion.graph target wall candidate.right
  datum := candidate.datum
  valid_of_old := candidate.datum_valid

end Candidate

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Nonsingularity of the member selected by an opposite-sign balance.  This
is what discharges the nonsingularity gate on `hSystems` in both exit
theorems below, from the `d_in * d_out < 0` that
`exists_opposite_of_positiveBalance` returns. -/
theorem det_ne_zero_of_mul_det_neg {A B : Matrix coordinate coordinate ℚ}
    (h : A.det * B.det < 0) : B.det ≠ 0 := by
  intro hzero
  rw [hzero, mul_zero] at h
  exact lt_irrefl 0 h

/-- A finite family of globally meaningful wall resolutions whose length
matrices share their non-wall columns and satisfy the paper's positive
determinant balance. -/
structure Family (n : ℕ) (data : GluingDatum target degree) where
  candidate : Fin n → CertifiedCandidate data
  matrix : Fin n → Matrix coordinate coordinate ℚ
  wallColumn : coordinate
  weight : Fin n → ℚ
  positiveBalance : PositiveBalance weight (fun i ↦ (matrix i).det)
  agreeOffWall : ∀ first second,
    AgreeOffColumn (matrix first) (matrix second) wallColumn

/-- A balanced family before forgetting the actual global candidates and
their length-matrix presentations.  This is the semantic form needed to turn
the selected positive exit into a subdivision pencil. -/
structure PresentedFamily (n : ℕ) (data : GluingDatum target degree)
    (wall : target.V) where
  candidate : Fin n → Candidate target degree data wall
  presentation : ∀ i,
    (candidate i).datum.LengthMatrixPresentation coordinate
  wallColumn : coordinate
  weight : Fin n → ℚ
  positiveBalance : PositiveBalance weight
    (fun i ↦ (GluingDatum.LengthMatrixPresentation.matrix
      (presentation i)).det)
  agreeOffWall : ∀ first second,
    AgreeOffColumn
      (GluingDatum.LengthMatrixPresentation.matrix (presentation first))
      (GluingDatum.LengthMatrixPresentation.matrix (presentation second))
      wallColumn

namespace PresentedFamily

/-- Forget presentations only after recording the semantic family. -/
noncomputable def toFamily
    (family : PresentedFamily (coordinate := coordinate) n data wall) :
    Family (coordinate := coordinate) n data where
  candidate := fun i ↦ (family.candidate i).certified
  matrix := fun i ↦
    GluingDatum.LengthMatrixPresentation.matrix (family.presentation i)
  wallColumn := family.wallColumn
  weight := family.weight
  positiveBalance := family.positiveBalance
  agreeOffWall := family.agreeOffWall

/-- A presented balanced family selects a valid opposite-sign candidate and,
at every sufficiently small positive outgoing step, an explicit cleared
rank-one pencil realizing that candidate's coordinates.  `hSystems` is gated
on nonsingularity of the outgoing member; see the gate discussion in the
module docstring. -/
theorem exists_valid_positive_exit_with_pencil
    {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree} {wall : target.V}
    (family : PresentedFamily (coordinate := coordinate) n data wall)
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (incoming : Fin n)
    (hincoming :
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation incoming)).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin n → coordinate → ℚ)
    (hz : z family.wallColumn = 0)
    (hzpos : ∀ i, i ≠ family.wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation outgoing)).mulVec
          (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity family.wallColumn < 0) :
    ∃ outgoing,
      (family.candidate outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          (family.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (family.presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation outgoing)).mulVec
              (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation incoming)).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              (family.presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (Candidate.ClearedPencil (family.candidate outgoing)
          (family.presentation outgoing)
          (z + t • outgoingVelocity outgoing)) := by
  obtain ⟨outgoing, hsign⟩ :=
    exists_opposite_of_positiveBalance family.positiveBalance hincoming
  have hOutgoingValid := (family.candidate outgoing).datum_valid hValid
  obtain ⟨δ, hδ, hstep⟩ := crosses_into_positive_cone
    (family.agreeOffWall incoming outgoing) hsign hz hzpos
    (hSystems outgoing (det_ne_zero_of_mul_det_neg hsign)) hIncomingDirection
  refine ⟨outgoing, hOutgoingValid, hsign, δ, hδ, ?_⟩
  intro t ht htd
  rcases hstep t ht htd with ⟨hPositive, hMetric⟩
  exact ⟨hPositive, hMetric,
    ⟨@Candidate.clearedPencil target degree data wall
      (family.candidate outgoing) hValid hTargetConnected hTargetGenus root
      coordinate (family.presentation outgoing)
      (z + t • outgoingVelocity outgoing) hPositive⟩⟩

end PresentedFamily

namespace Family

/-- The balancing condition produces a globally valid resolution with
determinant sign opposite to any chosen nondegenerate incoming resolution. -/
theorem exists_valid_opposite
    (family : Family (coordinate := coordinate) n data)
    (hValid : data.Valid) (incoming : Fin n)
    (hincoming : (family.matrix incoming).det ≠ 0) :
    ∃ outgoing,
      (family.candidate outgoing).datum.Valid ∧
      (family.matrix incoming).det * (family.matrix outgoing).det < 0 := by
  obtain ⟨outgoing, hsign⟩ :=
    exists_opposite_of_positiveBalance family.positiveBalance hincoming
  exact ⟨outgoing, (family.candidate outgoing).valid_of_old hValid, hsign⟩

/-- The complete rational local-continuation step. Besides the finite local
receipts packaged by `Family`, its hypotheses are precisely the incoming and
outgoing solutions of the compatible length systems at a wall point, and the
latter are required only at the **nonsingular** members; see the gate
discussion in the module docstring. -/
theorem exists_valid_positive_exit
    (family : Family (coordinate := coordinate) n data)
    (hValid : data.Valid) (incoming : Fin n)
    (hincoming : (family.matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin n → coordinate → ℚ)
    (hz : z family.wallColumn = 0)
    (hzpos : ∀ i, i ≠ family.wallColumn → 0 < z i)
    (hSystems : ∀ outgoing, (family.matrix outgoing).det ≠ 0 →
      (family.matrix incoming).mulVec incomingVelocity =
        (family.matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity family.wallColumn < 0) :
    ∃ outgoing,
      (family.candidate outgoing).datum.Valid ∧
      (family.matrix incoming).det * (family.matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (family.matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (family.matrix incoming).mulVec z +
            t • (family.matrix incoming).mulVec incomingVelocity := by
  obtain ⟨outgoing, hOutgoingValid, hsign⟩ :=
    family.exists_valid_opposite hValid incoming hincoming
  obtain ⟨δ, hδ, hstep⟩ := crosses_into_positive_cone
    (family.agreeOffWall incoming outgoing) hsign hz hzpos
    (hSystems outgoing (det_ne_zero_of_mul_det_neg hsign)) hIncomingDirection
  exact ⟨outgoing, hOutgoingValid, hsign, δ, hδ, hstep⟩

end Family


/-! ## Gauge-mixed families: one base datum per member

`PresentedFamily.candidate` fixes **one** `data`, and several of the wall
figures of Draisma--Vargas Part I do not.  The four members of Figure 28 there
(Case `w3-r1-nd3-t2-(a=k4)`) need opposite gauge conditions on the two branches
at the wall, so `M⁽¹⁾` and `M⁽²⁾` are assembled over
branch-swapped copies of the incoming datum; the middle member of
`GlobalM11Arbitrary.candidates` sits over `GlobalM11Arbitrary.SwappedDatum …`
for the same reason.  Such a member does not even share a *type* with a
`Candidate target degree data wall`, so no amount of rewriting turns those
families into a `PresentedFamily`.

Nothing essential is lost.  What `exists_valid_positive_exit_with_pencil`
actually uses of the base datum is `data.Valid` -- to validate the selected
member and to clear its pencil -- and the shared `target`, for connectedness,
genus and a root.  The branch swap preserves the first
(`ResolutionM11.wallBranchSwap_preserves_valid`, in the packaged forms
`W3FourDisjointness.BranchGauge.valid` and
`GlobalM11Arbitrary.SwappedDatum`'s validity) and does not touch the second, so
the same exit goes through for a family whose members sit over *different*
data, one per member.

`GaugeFamily` is that structure, `GaugeFamily.exists_valid_positive_exit_with_pencil`
is that theorem -- proved by the same three steps as
`PresentedFamily.exists_valid_positive_exit_with_pencil`:
`exists_opposite_of_positiveBalance`, `crosses_into_positive_cone`,
`Candidate.clearedPencil` -- and `PresentedFamily.toGaugeFamily` is the
constant-base instance, which agrees with `PresentedFamily` field for field.
`W3FourClosure.GaugeFamily` abbreviates this structure. -/

/-- A balanced family of wall resolutions whose members sit over possibly
different, but gauge-equivalent, gluing data on one target.  Setting every
`base i` to `data` recovers `PresentedFamily` (`PresentedFamily.toGaugeFamily`). -/
structure GaugeFamily (n : ℕ) (data : GluingDatum target degree)
    (wall : target.V) where
  /-- The datum member `i` is built on -- a branch-swapped copy of `data`. -/
  base : Fin n → GluingDatum target degree
  /-- Each copy is valid whenever the incoming datum is; this is exactly
  `W3FourDisjointness.BranchGauge.valid`. -/
  valid_of_old : ∀ i, data.Valid → (base i).Valid
  candidate : ∀ i, Candidate target degree (base i) wall
  presentation : ∀ i, (candidate i).datum.LengthMatrixPresentation coordinate
  wallColumn : coordinate
  weight : Fin n → ℚ
  positiveBalance : PositiveBalance weight
    (fun i ↦ (GluingDatum.LengthMatrixPresentation.matrix
      (presentation i)).det)
  agreeOffWall : ∀ first second,
    AgreeOffColumn
      (GluingDatum.LengthMatrixPresentation.matrix (presentation first))
      (GluingDatum.LengthMatrixPresentation.matrix (presentation second))
      wallColumn

namespace GaugeFamily

/-- **The positive exit with a cleared pencil, for a gauge-mixed family.**
Verbatim `PresentedFamily.exists_valid_positive_exit_with_pencil`, except that
each member's validity is routed through its own gauge.  The nonsingularity gate
on `hSystems` is the same one, and for the same reason: `PositiveBalance` is a
signed balance, so a member with `det = 0` need not have a solvable velocity
system, and the selected member always has `det ≠ 0`. -/
theorem exists_valid_positive_exit_with_pencil {n : ℕ}
    {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree} {wall : target.V}
    (family : GaugeFamily (coordinate := coordinate) n data wall)
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (incoming : Fin n)
    (hincoming :
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation incoming)).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin n → coordinate → ℚ)
    (hz : z family.wallColumn = 0)
    (hzpos : ∀ i, i ≠ family.wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation outgoing)).mulVec
          (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity family.wallColumn < 0) :
    ∃ outgoing,
      (family.candidate outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          (family.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (family.presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation outgoing)).mulVec
              (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation incoming)).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              (family.presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (Candidate.ClearedPencil (family.candidate outgoing)
          (family.presentation outgoing)
          (z + t • outgoingVelocity outgoing)) := by
  obtain ⟨outgoing, hsign⟩ :=
    exists_opposite_of_positiveBalance family.positiveBalance hincoming
  have hBaseValid : (family.base outgoing).Valid :=
    family.valid_of_old outgoing hValid
  have hOutgoingValid := (family.candidate outgoing).datum_valid hBaseValid
  obtain ⟨δ, hδ, hstep⟩ := crosses_into_positive_cone
    (family.agreeOffWall incoming outgoing) hsign hz hzpos
    (hSystems outgoing (det_ne_zero_of_mul_det_neg hsign)) hIncomingDirection
  refine ⟨outgoing, hOutgoingValid, hsign, δ, hδ, ?_⟩
  intro t ht htd
  rcases hstep t ht htd with ⟨hPositive, hMetric⟩
  exact ⟨hPositive, hMetric,
    ⟨Candidate.clearedPencil (family.candidate outgoing) hBaseValid
      hTargetConnected hTargetGenus root (family.presentation outgoing)
      (z + t • outgoingVelocity outgoing) hPositive⟩⟩

end GaugeFamily

namespace PresentedFamily

/-- **Every presented family is a gauge family with a constant base.**  The
conversion is the identity on every field a march consumer reads -- `candidate`,
`presentation`, `wallColumn`, `weight`, `positiveBalance`, `agreeOffWall` -- and
`valid_of_old` is `fun _ h ↦ h`.  So a wall-input constructor that builds a
`PresentedFamily` needs no further hypothesis to produce a gauge family; it only
composes with this. -/
def toGaugeFamily
    (family : PresentedFamily (coordinate := coordinate) n data wall) :
    GaugeFamily (coordinate := coordinate) n data wall where
  base := fun _ ↦ data
  valid_of_old := fun _ h ↦ h
  candidate := family.candidate
  presentation := family.presentation
  wallColumn := family.wallColumn
  weight := family.weight
  positiveBalance := family.positiveBalance
  agreeOffWall := family.agreeOffWall

@[simp] theorem toGaugeFamily_base
    (family : PresentedFamily (coordinate := coordinate) n data wall) (i : Fin n) :
    family.toGaugeFamily.base i = data := rfl

@[simp] theorem toGaugeFamily_candidate
    (family : PresentedFamily (coordinate := coordinate) n data wall) (i : Fin n) :
    family.toGaugeFamily.candidate i = family.candidate i := rfl

@[simp] theorem toGaugeFamily_presentation
    (family : PresentedFamily (coordinate := coordinate) n data wall) (i : Fin n) :
    family.toGaugeFamily.presentation i = family.presentation i := rfl

@[simp] theorem toGaugeFamily_wallColumn
    (family : PresentedFamily (coordinate := coordinate) n data wall) :
    family.toGaugeFamily.wallColumn = family.wallColumn := rfl

@[simp] theorem toGaugeFamily_weight
    (family : PresentedFamily (coordinate := coordinate) n data wall) :
    family.toGaugeFamily.weight = family.weight := rfl

/-- The gauge exit on a constant-base family is the presented exit. -/
theorem toGaugeFamily_exists_valid_positive_exit_with_pencil
    {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree} {wall : target.V} {n : ℕ}
    (family : PresentedFamily (coordinate := coordinate) n data wall)
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (incoming : Fin n)
    (hincoming :
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation incoming)).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin n → coordinate → ℚ)
    (hz : z family.wallColumn = 0)
    (hzpos : ∀ i, i ≠ family.wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation outgoing)).mulVec
          (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity family.wallColumn < 0) :
    ∃ outgoing,
      (family.candidate outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          (family.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (family.presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation outgoing)).mulVec
              (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation incoming)).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              (family.presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (Candidate.ClearedPencil (family.candidate outgoing)
          (family.presentation outgoing)
          (z + t • outgoingVelocity outgoing)) :=
  family.toGaugeFamily.exists_valid_positive_exit_with_pencil hValid
    hTargetConnected hTargetGenus root incoming hincoming z incomingVelocity
    outgoingVelocity hz hzpos hSystems hIncomingDirection

end PresentedFamily

end DraismaVargas.LocalCases.BalancedGlobal
