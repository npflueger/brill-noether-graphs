import DraismaVargasCount.GeneralKReceipts
import DraismaVargasCount.ColumnReceiptExport

/-!
# The general-`K` exit at a four-valent wall: shared setup

This module holds the shared definitions for the `K ≥ 1` exit at a four-valent
wall (Vargas, Part II, arXiv:2609.09109, case `{v4-nd4}` of the section on changing
combinatorial type, `subsec-case-v4`), together with three results about them.  The modules
that build the general-`K` background, trivalence, path ends and the outgoing presentation
import it; they feed the valency-four clause of the type changes
(`CensusAssembly.V4ClauseSupply`, used in step 3 of the genus-six assembly).

* `CanonicalBackground`: the rigid background of the non-anchor wall blocks,
  written as a hypothesis on a `GeneralKReceipts.PairingBackground`.  It is not
  satisfiable in general; see the warning before its definition.
* `candK`: the general-`K` candidate at the wall data of the outer walk, with
  every implicit argument spelled out.
* `candidate_sourceGenus`: the candidate keeps the source genus of the wall datum.
* `sameMetricLimit_of_columnReceipt`: *any* column-receipted type-change link
  puts the far regrowth in the regrowth's own labelled metric limit.
* `odd_mSpecializesRight_of_columnReceipt`: its consequence for oddness.

**Two silent elaboration traps.**
* A `local notation` used inside a `variable` binder elaborated `wd.hab` and
  `wd.hOne` to `sorryAx` with no error, and the declarations after it vanished.
  That is why `position`'s type below is written out in full.
* `Position`'s implicit wall vertex is not recovered by unification from
  `position` alone.  That is why `candK` is an `abbrev` with an explicit type.

## What is not proved here

* That a `CanonicalBackground` exists over the general-`K` gauged datum; in general it
  does not.  Nothing here produces a `geometry`; it is a variable throughout.
* Anything about the candidate beyond its genus: trivalence, the dangling
  `K + K'` extra new-edge singletons, bridge survival, path ends, and the
  outgoing presentation with its common minor.
* The `K`-member `TypeChangeLink` itself.  `sameMetricLimit_of_columnReceipt` and
  `odd_mSpecializesRight_of_columnReceipt` only say what follows once a column-receipted
  link is in hand.
* That different `K` give different classes (`K`-rigidity).  It is proved in
  `Count/ValencyFourRigidity.lean` (`kIndexL_injective_of_v4`, `kIndexR_injective_of_v4`),
  and per-`K` realisation on both sides in `Count/ValencyFourRealisation.lean`
  (`hex_of_resolved`); together they give the valency-four clause at genus six
  (`ValencyFourRealisation.v4ClauseSupply_genusSix`).
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKExitSetup

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.Count.GeneralKReceipts


/-! ## B.  At the wall data of the outer walk -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
    ⟨wd.a, wd.hab⟩)
  (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlock) = 4)
  (pairing : Fin 3)

local notation "vSrc" =>
  (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    wallStar (wd.hForest m) anchorBlock hAnchor)
local notation "vNG" =>
  (NonTrivalentUniqueFourValent.wall_noGlue wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m))
local notation "vProf" =>
  (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne wallStar (wd.hForest m) wd.coordinates (label m.base) wd.hRows
    wd.hZeroCoord anchorBlock hAnchor)
local notation "vConn" =>
  (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne)
local notation "vGen" =>
  (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)

variable (position : GeneralKReceipts.Position
    (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      wallStar (wd.hForest m) anchorBlock hAnchor) pairing
    (smallerSide (NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wallStar (wd.hForest m) anchorBlock hAnchor) pairing))
  (geometry : GeneralKReceipts.PairingBackground position.datum wallStar pairing
    anchorBlock.1)


/-! **Warning: `CanonicalBackground` below is not satisfiable in general.**
The literal equality with `W4Assembly.blockwiseResolution`, combined with the global
`PairingBackground.exterior`, is unsatisfiable at an ordinary nd3 block whose partner branch
has index at least two (`GeneralKBackground.not_exists_literalBackground`, and its `K = 0`
form `not_exists_literalBackground_of_K_zero`).  Use
`GeneralKSourceFacts.LocalCanonicalBackground` instead: the same resolution localized to its
own block, inhabited at every wall (`exists_localCanonicalBackground`).  Theorems taking
`CanonicalBackground` as a hypothesis may be vacuous. -/

/-- The canonical background, as a hypothesis on `geometry`.  Not satisfiable in general;
see the warning above. -/
abbrev CanonicalBackground : Prop :=
  ∀ block, ¬(position.datum.vertexPartition ⟨wd.a, wd.hab⟩).Rel anchorBlock.1 block →
    geometry.resolution block =
      W4Assembly.blockwiseResolution position.datum wallStar (vProf).pattern pairing block

/-- The general-`K` candidate at the wall data, with every implicit argument
spelled out (unification does not recover the wall vertex from `position`
alone). -/
noncomputable abbrev candK :
    BalancedGlobal.Candidate (contract wd.coverTarget wd.hab wd.hOne) degree position.datum
      ⟨wd.a, wd.hab⟩ :=
  position.candidate vConn vGen vNG geometry

local notation "cK" => (candK m wd wallStar anchorBlock hAnchor pairing position geometry)


/-- **The candidate keeps the source genus.**  The candidate has the source
genus of the wall datum.  This is the genus input of
`NonTrivalentValencyTwoExit.ofTypeChange`. -/
theorem candidate_sourceGenus
    (hBg : CanonicalBackground m wd wallStar anchorBlock hAnchor pairing position geometry) :
    genus (cK).datum.sourceGraph =
      genus (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceGraph := by
  rw [position.candidate_sourceGenus vConn vGen vNG geometry ?_,
    position.gauge.gaugedData_sourceGenus]
  intro block hBlock
  rw [hBg block hBlock]
  exact NonTrivalentValencyFourRows.euler_of_isStar
    (NonTrivalentValencyFourRows.isStar_blockwiseResolution (star := wallStar) pairing
      (vProf).pattern block) block

end Wall

/-! ## The metric limit of a column-receipted link -/

section Facet

open FacetAdapterPilot MemberCertifiedPencil ValencyThreeGeneral FacetMachine
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)

variable {n p degree : ℕ} {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- ***Any* type-change link with a column receipt
puts the far regrowth in the regrowth's own labelled metric limit.**  This is
the per-link content of `ValencyThreeGeneral.metricLinkReceipts_of_column`.
Applied to the `K`-links of a four-valent wall, it gives the census one far class per
admissible `K` in the same `MetricFacetLimit`. -/
theorem sameMetricLimit_of_columnReceipt (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms))
    (hrec : ColumnReceiptExport.ColumnReceipt link) :
    SameMetricLimit (c := c.core) (c' := (farCore m').core) (Sum.inl w)
      (Sum.inr (farRegrowth m' hd hG hDegree w ms link)) := by
  obtain ⟨iso, hiso⟩ := ColumnReceiptExport.column_of_receipt m' hd hG hDegree w ms link hrec
  refine ⟨iso, fun e ↦ ⟨?_, ?_⟩⟩
  · exact (congrArg ((farRegrowth m' hd hG hDegree w ms link).frame.coordsAt y₀) (hiso e)).trans
      (congrFun (farFrame_coordsAt m' hd hG hDegree w ms link) (limitCol w e))
  · exact (congrArg (slotColumn (farFrame m' hd hG hDegree w ms link)) (hiso e)).trans
      (slotColumn_farFrame m' hd hG hDegree w ms link _ (limitCol_ne_column w e))

/-- **Oddness is carried along** (from `sameMetricLimit_of_columnReceipt`).  The far class
of any column-receipted link is odd exactly when the regrowth's class is odd, and it
specialises to the same labelled metric limit.  Instantiated at the `K`-links of a
four-valent wall, this gives the census consumer
(`FacetCensus.facetParity_of_metric_injective_index`) one odd far class per admissible `K`;
that these classes are distinct is `K`-rigidity (`ValencyFourRigidity`). -/
theorem odd_mSpecializesRight_of_columnReceipt (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms))
    (hrec : ColumnReceiptExport.ColumnReceipt link) :
    ((FrameClass.mk (farFrame m' hd hG hDegree w ms link)).IsOdd ↔
        (FrameClass.mk w.frame).IsOdd) ∧
      MSpecializesRight (FrameClass.mk (farFrame m' hd hG hDegree w ms link))
        (MetricFacetLimit.ofLeft (c' := (farCore m').core) w) :=
  ⟨farFrame_isOdd_iff m' hd hG hDegree w ms link,
    farRegrowth m' hd hG hDegree w ms link, rfl,
    (Quotient.sound (sameMetricLimit_of_columnReceipt m' hd hG hDegree w ms link hrec)).symm⟩

end Facet

end DraismaVargas.Count.GeneralKExitSetup
