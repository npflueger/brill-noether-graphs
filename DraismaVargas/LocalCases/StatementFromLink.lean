import DraismaVargas.LocalCases.RowsMeetEndsOnly
import DraismaVargas.LocalCases.OuterWalkInterior
import DraismaVargas.LocalCases.TerminalIdentification

/-!
# From `DraismaVargas.Statement`'s hypotheses to the type-change link

**Source.**  Vargas, Part II (arXiv:2609.09109), Sections 4.3--4.4 (wall
crossing, and the outer walk in the proofs of the main theorems), together with
Draisma--Vargas Part I
(arXiv:1909.12924), the proof of the main theorem (a non-trivalent requested
type presented as a point of the *closed* cone of a trivalent one, with zero
length on exactly the collapsed edges).  Neither paper gives a detailed proof
of the exact integral-scale transport, so §3--§4 below are original to this
formalization, adapted from the closed-cone reading.

## What is proved

A reduction of the theorem
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one`
(see `DraismaVargas/Statement.lean`) to two named hypotheses, both of which
are discharged elsewhere.  Nothing here touches that statement; the theorems
are stated with *its* hypotheses `(spec, hconn, hGenus, hEven)` verbatim and
*its* conclusion `Nonempty (SubdivisionPencil spec ((p + 2 - n) / 2 + 1))`.

* §1 `exists_walkIndex` -- the Statement's `6 ≤ p + 1 - n` and
  `Even (p + 1 - n)` name the outer walk's index `m`:
  `p + 1 - n = 2 * m + 2`, `(p + 2 - n) / 2 + 1 = m + 2`, `2 ≤ m`, `n < p`.
  (`p + 1 - n` is truncated subtraction, so `hGenus` is what keeps it honest.)

* §3 the general-forest terminal payout.  `keptClasses_nonempty_of_spanning`
  proves at a general forest `F` that a spanning placement keeps a class (the
  forest enters only through the type of the dictionary).
  `RetainedRelabeling` names the relabeling at a general forest that the
  construction needs, and `nonempty_subdivisionPencil_of_certified_expansion`
  turns the general-`F` certificate of the terminal identification into a
  `SubdivisionPencil` of the **reduced requested** specification `spec₀` at
  the terminal face's own scale.

* §4 `nonempty_evenSubdivisionPencil_of_link` -- the Statement's conclusion for
  an **arbitrary** connected request, from the type-change link and
  `RetainedRelabeling`.  Route: the reduction to a cubic model
  (`RequestedExpandedEndpoints.exists_expansionModel`) → the outer walk run at
  the endpoint vector `RequestedExpandedEndpoints.expandedFinish` (zero on the
  expansion forest) → the terminal identification
  `TerminalIdentification.carriesCertifiedPencil_of_tracked_expanded` → §3 →
  the scale-wise Brill--Noether transport of the reduction.
  `nonempty_evenSubdivisionPencil_of_receipts` is the same theorem with the two
  hypotheses pulled out in front of the Statement's own four binders.

## What is NOT proved here -- the hypotheses that remain explicit

1. **`link`**: `OuterWalk.TypeChangeLink` at every wall datum of every
   graph the Whitehead chain reaches from the caterpillar seed, at the index
   `m` the genus names.  It is a hypothesis of the theorems below;
   `NonTrivalentValencyTwoBaseOneLink.link_all` proves it with no hypothesis.
2. **`relabel`**: `RetainedRelabeling` at every expansion datum, i.e. a
   `LaplacianEquiv` from the canonical positive refinement cut on the retained
   cubic slots (`InputRefinementData.Retained.refinedSpec`) onto the terminal
   face's pruned contracted source.  It is the general-forest analogue of
   `OrientedTraversal.RowDictionary.laplacianEquiv`.  At a nonempty forest the
   whole of `OrientedTraversal` §3--§4 (`slotEquiv`, `positiveRow`,
   `vertexClass`, `sourceModel`) must be re-indexed through the
   `RetainedIndex`, because `Retained.refinedSpec` additionally cuts each
   retained row at the marker positions (`Infrastructure.OrderedBlockSplit`),
   adding one bivalent refined vertex per interior cut.
   `laplacianEquiv_of_coreModel` (§3) is a **sufficient, not necessary**, form
   of it: a `RefinementCore.CoreModel` of the retained segment data on the
   pruned contracted source, i.e. the retained analogue of
   `RefinementCore.SourceModel`.  It is not a reduction: at a straddled marker
   no such `CoreModel` exists at all
   (`RetainedRelabeling.isEmpty_coreModel_of_straddle`).  The form that holds is
   `RetainedRelabeling.CutRelabeling`, which `RetainedCut` further reduces to
   one `RefinementCore.CoreModel` on `RetainedCut.cutSpec` with both
   cardinalities proved; `RetainedClassInjectivity.cutRelabeling_of_expansion`
   supplies `CutRelabeling` unconditionally for the expansion the reduction
   produces.

Everything else -- the interior tracked progress of the march, the terminal
identification, the reduction to a cubic model, the endpoint vector, the
general-`F` forest property, the `SourceContractionTopology`, the
`ContractedGluing` and the kept class -- is discharged inside the proofs below.
In particular `ClearedFace.ContractedGluing` *does* have a producer,
`TerminalGluing.contractedGluing_of_incoming`, which needs no interface and no
forest.

## Why the empty-forest terminal certificate is not used at `F ≠ ∅`

The empty-forest route takes `CarriesCertifiedPencil spec degree matrix start
finish` at the default forest `∅`, and factors through
`TerminalExhausts.TerminalCertificate`, whose `iface` field is again at `∅`.
An `InputInterface spec … ∅` asserts that every row total is `spec.length`,
which `Spec.length_pos` makes strictly positive, while the walk is run at a
vector that is **zero** on every forest row.  So at a nonempty forest no such
interface exists at that finish for any labelling, and the empty-forest
terminal construction does not apply at the cubic model; nor at `spec₀`, whose
slot count `p₀` differs from `Fintype.card coordinate = Q`.  What the terminal
face still yields is assembled by hand in §3: the expansion rows are contracted
whole inside the face (`InputRefinementData.sourceLength_eq_zero_of_mem_forest`),
so the refinement re-bases on the retained rows and the pencil that comes out
is a pencil of `spec₀`.

## Consumers

`RetainedStatement`, which discharges the two hypotheses and assembles the
statement.
-/

namespace DraismaVargas.LocalCases.StatementFromLink

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TerminalExhausts
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.W4StableSource

/-! ## 1.  The genus arithmetic of the Statement's hypotheses -/

/-- **The Statement's hypotheses name the walk's index.**  `6 ≤ p + 1 - n` and
`Even (p + 1 - n)` give an `m` with `p + 1 - n = 2 * m + 2`, the outer walk's
genus equation, and identify the requested degree `(p + 2 - n) / 2 + 1` with
the walk's `m + 2`.  Both subtractions are truncated, so `hGenus` is doing
real work: it forces `n + 5 ≤ p`, hence `n < p`, which is the hypothesis of the
reduction to a cubic model. -/
theorem exists_walkIndex {n p : ℕ} (hGenus : 6 ≤ p + 1 - n) (hEven : Even (p + 1 - n)) :
    ∃ m : ℕ, p + 1 - n = 2 * m + 2 ∧ (p + 2 - n) / 2 + 1 = m + 2 ∧ 2 ≤ m ∧ n < p := by
  obtain ⟨k, hk⟩ := hEven
  exact ⟨k - 1, by omega, by omega, by omega, by omega⟩

/-! ## 3.  The terminal payout at a general expansion forest -/

section Kept

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}
  {strong : StrongPresentation candidate.datum coordinate}
  {iface : InputInterface spec strong.toPresentation coordinates F}
  {face : ClearedFace candidate strong.toPresentation coordinates}

/-- **A spanning placement keeps a class, at every forest.**
The interface's forest `F` is free: the forest enters only through the type of the
dictionary, and the proof uses only `Spanning`, `spec.core_nonempty` and the
two path-end fields of the strong presentation.  The conclusion mentions no
interface at all. -/
theorem keptClasses_nonempty_of_spanning
    (dictionary : CoreDictionary spec strong iface)
    (hSpanning : Spanning dictionary)
    (topology : ClearedFace.SourceContractionTopology face) :
    (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty := by
  obtain ⟨row, vertex, hRow⟩ : ∃ (row : coordinate) (vertex : candidate.datum.SourceVertex),
      vertex = strong.start row ∨ vertex = strong.finish row := by
    rcases hSpanning ⟨0, spec.core_nonempty⟩ with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨iface.slot i, _, Or.inl hi⟩
    · exact ⟨iface.slot i, _, Or.inr hi⟩
  have hne : strong.toPresentation.path row ≠ [] := strong.path_ne_nil row
  obtain ⟨edge, hIncident⟩ : ∃ edge : candidate.datum.SourceEdge,
      edge ∈ strong.toPresentation.path row ∧ Incident candidate.datum edge vertex := by
    rcases hRow with rfl | rfl
    · obtain ⟨edge, hEdge⟩ := strong.exists_head row
      exact ⟨edge, List.mem_of_mem_head? hEdge, strong.head_incident row edge hEdge⟩
    · have hLast : (strong.toPresentation.path row).getLast? =
          some ((strong.toPresentation.path row).getLast hne) :=
        List.getLast?_eq_getLast_of_ne_nil hne
      exact ⟨_, List.getLast_mem hne, strong.getLast_incident row _ hLast⟩
  refine ⟨topology.degSpec.classIndex
    (ClearedFace.SourceContractionTopology.classOf topology vertex), ?_⟩
  refine ClearedFace.SourceContractionTopology.mem_keptClasses_classIndex topology
    ⟨vertex, rfl, ?_⟩
  exact ClearedFace.SourceContractionTopology.nonDanglingValency_pos_of_incident
    (strong.decomposes.not_isDangling_of_mem hIncident.1) hIncident.2

end Kept

/-- **The relabeling at a general forest.**

`InputRefinementData.Retained.inputRefinement` -- the only producer of
`ClearedFace.InputRefinement small topology` when the forest is nonempty --
takes exactly one thing it does not build: a `LaplacianEquiv` identifying the
canonical positive refinement cut on the retained slots
(`Retained.refinedSpec`) with the terminal face's pruned contracted source.

Everything the derivation of that equivalence uses at `F = ∅` is put inside the
binder here, so this is the honest general-forest analogue of
`OrientedTraversal.RowDictionary.laplacianEquiv` and **not** a statement about
arbitrary candidates: the core dictionary, its faithfulness and spanning, the
quotient source's connectivity and the datum-level genus hypothesis all appear
as hypotheses.  At `F = ∅` the corresponding equivalence is
`OrientedTraversal.RowDictionary.laplacianEquiv`. -/
def RetainedRelabeling {N Q n p : ℕ} (model : Spec N Q) (F : Finset (Fin Q))
    (small : Spec n p) (idx : RetainedIndex model F small) : Prop :=
  ∀ (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
    (tgt : CFGraph.{0}) (gdata : GluingDatum tgt degree) (wall : tgt.V)
    (candidate : Candidate tgt degree gdata wall)
    (strong : StrongPresentation candidate.datum coordinate)
    (coordinates : coordinate → ℚ)
    (iface : InputInterface model strong.toPresentation coordinates F)
    (dict : CoreDictionary model strong iface),
    Faithful dict → Spanning dict → candidate.datum.Connected →
    SourceGenusMatches model candidate.datum →
    ∀ (face : ClearedFace candidate strong.toPresentation coordinates)
      (topology : ClearedFace.SourceContractionTopology face)
      (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty),
      Nonempty (LaplacianEquiv (Retained.refinedSpec iface face idx).graph
        (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).graph)

/-- **A sufficient condition for the relabeling, not a reduction of it.**
`Retained.refinedSpec` is `refineAllSlots` of `Retained.segmentData` by
definition, and `RefinementCore.CoreModel` is stated at an *arbitrary*
`SegmentData`, so a core model of the retained segment data on the pruned
contracted source suffices for the relabeling.

**It is not a reduction** (`RetainedRelabeling`): at a straddled marker the
retained refinement has one more slot than the pruned contracted source
(`RetainedRelabeling.sum_segments_eq_card_keptSlots_add`), so no such
`CoreModel` exists there at all (`RetainedRelabeling.isEmpty_coreModel_of_straddle`,
which already happens for the expansion the reduction produces).  The form that
holds is `RetainedRelabeling.CutRelabeling`: a canonical split chain out of the
pruned contracted spec together with a core model of the retained segment data
on *its* end, which costs nothing extra since a canonical bivalent split does
not change the graph.  `RetainedCut` reduces `CutRelabeling` further to one
`RefinementCore.CoreModel` on `RetainedCut.cutSpec` alone, with both of that
core model's cardinalities proved, and
`RetainedClassInjectivity.cutRelabeling_of_expansion` supplies `CutRelabeling`
unconditionally for the expansion the reduction produces.

What follows is accordingly a genuine but non-optimal sufficient condition: to
inhabit *this* definition's hypothesis at a nonempty forest one needs the
retained analogue of `RefinementCore.SourceModel` -- a bijection of the
retained refined slots with the kept slots, a bijection of the retained
refined vertices (the requested core vertices together with the row
breakpoints, one extra per marker cut) with the kept classes, and the three
endpoint equations (compare `RetainedVertexModel`).  At `F = ∅` that analogue
is `OrientedTraversal.RowDictionary.sourceModel`; the general-`F` producer has
to re-index `OrientedTraversal` §3's `slotEquiv`, `positiveRow` and
`vertexClass` through the `RetainedIndex`. -/
noncomputable def laplacianEquiv_of_coreModel {target : CFGraph} {degree : ℕ}
    {gdata : GluingDatum target degree} {wall : target.V}
    {candidate : Candidate target degree gdata wall}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    {presentation : candidate.datum.LengthMatrixPresentation coordinate}
    {coordinates : coordinate → ℚ} {N Q n p : ℕ} {model : Spec N Q}
    {F : Finset (Fin Q)} {small : Spec n p}
    {face : ClearedFace candidate presentation coordinates}
    (iface : InputInterface model presentation coordinates F)
    (idx : RetainedIndex model F small)
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (cm : RefinementCore.CoreModel (Retained.segmentData iface face idx)
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)) :
    LaplacianEquiv (Retained.refinedSpec iface face idx).graph
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).graph :=
  cm.laplacianEquiv

/-- **The payout at a general expansion forest, from the terminal certificate.**

Given the expansion datum `D` of the reduction, with its Euler count, the general-forest
relabeling, and a certified pencil of the **cubic model** `D.bigSpec` at a
nonnegative endpoint vector and at the forest `expansionForest D`, the terminal
face carries a `SubdivisionPencil` of the **reduced requested** specification
`spec₀`, at the face's own denominator-clearing scale.

Every intermediate ingredient is produced here:
`ClearedFace.SourceContractionTopology` by
`RowsMeetEndsOnly.sourceContractionTopology_of_forest` on
`ForestReceiptGeneral.isForest_expansionForest`, the kept class by §3,
`ClearedFace.ContractedGluing` by `TerminalGluing.contractedGluing_of_incoming`,
the input refinement by `InputRefinementData.Retained.inputRefinement` on
`RetainedIndexProducer.retainedIndex`, and the pencil by
`ClearedFace.exists_subdivisionPencil`.  Only `relabel` is assumed. -/
theorem nonempty_subdivisionPencil_of_certified_expansion
    {n₀ p₀ N Q degree : ℕ} {spec₀ : Spec n₀ p₀} {D : ExpansionData n₀ p₀ N Q}
    (hCond : D.Conditions spec₀.core) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (hEuler : N + p₀ = Q + n₀)
    (relabel : RetainedRelabeling (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀
      (RetainedIndexProducer.retainedIndex hCond hN hL))
    {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
    {matrix : Matrix coordinate coordinate ℚ} {start finish : coordinate → ℚ}
    (hFinish : ∀ i, 0 ≤ finish i)
    (certified : CertifiedPencil.CarriesCertifiedPencil (D.bigSpec spec₀ hN hL) degree
      matrix start finish (expansionForest D)) :
    Nonempty (DraismaVargas.SubdivisionPencil spec₀ degree) := by
  classical
  obtain ⟨tgt, gdata, wall, candidate, fullDim, strong, hMatrixFD, hStrongMatrix,
    hValid, hTgtConn, hTgtGenus, hPencil, hSource, hCert⟩ := certified
  obtain ⟨iface, dict, hFaithful, hSpanning⟩ := hCert hFinish
  set face := BalancedGlobal.Candidate.clearedFace candidate strong.toPresentation
    finish hFinish with hface
  have hTEconn : graph_connected (TargetExpansion.graph tgt wall candidate.right) :=
    TargetExpansion.graph_connected tgt wall candidate.right hTgtConn
  have hTEgenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0 := by
    rw [TargetExpansion.graph_genus tgt wall candidate.right, hTgtGenus]
  have hForest : Utilities.Certificate.ContractionForestCensusGeneral.IsForest
      (D.bigSpec spec₀ hN hL).core (expansionForest D) :=
    ForestReceiptGeneral.isForest_expansionForest hCond hEuler
  set topology := RowsMeetEndsOnly.sourceContractionTopology_of_forest strong iface face
    dict hFaithful hSpanning hForest hTEconn hTEgenus with htopology
  have hKept := keptClasses_nonempty_of_spanning dict hSpanning topology
  have hDatumConn : candidate.datum.Connected := (candidate.datum_valid hValid).1
  have relabeling := (relabel degree coordinate tgt gdata wall candidate strong finish
    iface dict hFaithful hSpanning hDatumConn hSource face topology hKept).some
  have input := Retained.inputRefinement iface
    (RetainedIndexProducer.retainedIndex hCond hN hL) hKept relabeling
  have contracted := TerminalGluing.contractedGluing_of_incoming face topology hValid
    hTgtConn hTgtGenus
  obtain ⟨w, -⟩ := ClearedFace.exists_subdivisionPencil contracted input hDatumConn
  exact ⟨w⟩

/-! ## 4.  Arbitrary connected requests -/

/-- **The Statement's conclusion for an arbitrary connected request, from the
type-change link and the relabeling.**

The hypotheses are exactly those of
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one` plus
two named hypotheses, both discharged elsewhere (see "What is NOT proved"
above): `link` (at the index the genus names) and `relabel`, the relabeling at
every expansion datum.  There is no cubicity hypothesis: the reduction to a
cubic model supplies the cubic model and the endpoint vector that is zero on
its expansion forest.

The chain: `RequestedExpandedEndpoints.exists_expansionModel` gives the reduced
`spec₀` and the datum `D` whose `bigSpec` is a cubic connected loopless model
of the same genus; the walk
(`OuterWalkInterior.exists_terminal_of_chain''`, which is finish-agnostic --
it asks only `0 ≤ requestedLength e`) is run on that model at
`RequestedExpandedEndpoints.expandedFinish`; the terminal tracked state is
identified by `TerminalIdentification.carriesCertifiedPencil_of_tracked_expanded`;
§3 contracts the expansion rows inside the terminal face and delivers a pencil
of `spec₀`; and the scale-wise two-way Brill--Noether transport of the
reduction carries it to the original request at the same scale. -/
theorem nonempty_evenSubdivisionPencil_of_link {n p : ℕ} (spec : Spec n p)
    (hconn : graph_connected spec.graph) (hGenus : 6 ≤ p + 1 - n)
    (hEven : Even (p + 1 - n))
    (link : ∀ m : ℕ, p + 1 - n = 2 * m + 2 →
      ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (relabel : ∀ {n₀ p₀ : ℕ} (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e)
      (hCond : D.Conditions spec₀.core),
      RetainedRelabeling (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀
        (RetainedIndexProducer.retainedIndex hCond hN hL)) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) := by
  classical
  obtain ⟨m, hm, hdeg, -, hnp⟩ := exists_walkIndex hGenus hEven
  have hCoreConnected : spec.core.Connected :=
    Utilities.Certificate.PseudocorePresentation.core_connected_of_graph_connected spec hconn
  rw [hdeg]
  obtain ⟨n₀, p₀, spec₀, D, hCond, hCubic, hConnBig, hL, hN, hc₀, hlt₀, hg₀, hbn₀, hbns₀⟩ :=
    exists_expansionModel spec hCoreConnected hnp
  -- the cubic model, its forest, and the endpoint vector on it
  set model : Spec (2 * (p₀ - n₀)) (3 * (p₀ - n₀)) := D.bigSpec spec₀ hN hL with hmodel
  set F : Finset (Fin (3 * (p₀ - n₀))) := expansionForest D with hF
  have hCubic' : model.core.Cubic := hCubic
  have hConn' : model.core.Connected := hConnBig
  have hmg : 3 * (p₀ - n₀) + 1 - 2 * (p₀ - n₀) = 2 * m + 2 := by omega
  have hEuler : 2 * (p₀ - n₀) + p₀ = 3 * (p₀ - n₀) + n₀ := by omega
  set req : Fin (3 * (p₀ - n₀)) → ℚ :=
    fun e ↦ ((if e ∈ F then 0 else model.length e : ℕ) : ℚ) with hreq
  have hReqNonneg : ∀ e, 0 ≤ req e := fun e ↦ by positivity
  -- the outer walk on the cubic model, at that endpoint vector
  obtain ⟨last, endpoint, slots, hReach, hslots, baseStart, hStart, hGeneric,
      initial, final, hZero, hreach, hterminal, hTrackedPencil, hClearedFace⟩ :=
    OuterWalkInterior.exists_terminal_of_chain'' m model.core hCubic' hConn' hmg
      (link m hm) req hReqNonneg
  have hBase : (fun row ↦ req (slots row)) = expandedFinish model F slots.symm := rfl
  -- the terminal identification at the terminal tracked state, at the forest
  have certified :=
    TerminalIdentification.carriesCertifiedPencil_of_tracked_expanded
      (spec := model) (F := F) hCubic' hConn' endpoint slots hslots hBase final
  -- the pencil of the reduced request, then the transport of the reduction
  obtain ⟨w⟩ := nonempty_subdivisionPencil_of_certified_expansion hCond hN hL hEuler
    (relabel spec₀ D hN hL hCond) hterminal certified
  obtain ⟨w', -⟩ := DraismaVargas.SubdivisionPencil.exists_of_BNExists (spec := spec)
    w.scale_pos ((hbns₀ w.scale w.scale_pos 1 ((m + 2 : ℕ) : ℤ)).mp w.bnExists)
  exact ⟨w'⟩

/-- **The Statement's conclusion from two hypotheses.**  The same theorem with
the two hypotheses pulled out in front of the Statement's own binders and stated
once for every index, so that what the statement needs beyond this file is
visibly two hypotheses and nothing else: the type-change link at every reached
wall of every `m`, and the relabeling at every expansion datum.  Both are
theorems
(`NonTrivalentValencyTwoBaseOneLink.link_all`,
`RetainedClassInjectivity.cutRelabeling_of_expansion`).

The conclusion and the four binders `spec`, `hconn`, `hGenus`, `hEven` are
`nonempty_evenSubdivisionPencil_ceil_half_genus_add_one`'s verbatim. -/
theorem nonempty_evenSubdivisionPencil_of_receipts
    (link : ∀ m : ℕ,
      ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (relabel : ∀ {n₀ p₀ : ℕ} (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e)
      (hCond : D.Conditions spec₀.core),
      RetainedRelabeling (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀
        (RetainedIndexProducer.retainedIndex hCond hN hL))
    {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph)
    (hGenus : 6 ≤ p + 1 - n) (hEven : Even (p + 1 - n)) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  nonempty_evenSubdivisionPencil_of_link spec hconn hGenus hEven
    (fun m _ ↦ link m) relabel

end

end DraismaVargas.LocalCases.StatementFromLink
