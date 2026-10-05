module

public import DraismaVargasCount.RowGeodesic
public import DraismaVargasCount.RowRegrowth
public import DraismaVargas.LocalCases.A04FourTags

@[expose] public section

/-!
# The outgoing member's row calculus, once, on the outgoing-candidate interface

**Source.**  Vargas, Part II (arXiv:2609.09109): `lemma-edge-deno` cases (a) and
(b), `proposition-at-most-two-weights`, and the proof of `prop-signed-mult` (1),
whose parenthesis **"whenever `c⁽q⁾ ≠ 0`"** is the gate every statement below
carries.  Part I's case `{w2-r2-nd3-M-1k}` is Figure 33 of Draisma--Vargas Part I
(arXiv:1909.12924).

`RowRegrowth` reduces the upper half `d₀ ∣ k` of `lemma-edge-deno` (b) to two
member-side receipts; the first is
`RowRamificationAtMostOne member memberRow` together with
`RowAtMostOneTransition member memberRow`, which are theorems of `RowWalk` as
soon as the member carries a `FullDimensionalSourcePresentation` **and its row
avoids leaves**.

This file discharges that receipt.  It is stated once, on the interface through
which *every* wall family presents its outgoing members --
`LocalCases.A04FourTags.FullDimSupply` over a
`LocalCases.WallProgress.WallInput` -- so it serves all ten trivalent
deformation cases, not only Figure 33.

## The two observations

1. **Leaf avoidance is free on a ramified row.**  `RowAvoidsLeaves` looked like
   a second hypothesis; it is not.  `Count.EdgeDenominator`'s case (a) says
   every occurrence displayed on a leaf-passing row has dilation index `1`
   (`sourceEdgeIndex_eq_one_of_passesAboveLeaf`, proved with no hypothesis at
   all).  So a row that displays a single occurrence of index `≠ 1` cannot pass
   above a leaf: `rowAvoidsLeaves_of_index_ne_one`.  On the two perturbed rows
   of Figure 33 the witness is free -- the member's copy of `e₂` (resp. `e₃`)
   has index `k`, and `Shape.one_lt_k` is `1 < k`.
2. **`SimpleTarget` is free on a full-dimensional presentation.**
   `Count.RowGeodesic.simpleTarget_of_genusZero` derives it from connectivity
   and genus zero, and both are *fields* of
   `FullDimensionalSourcePresentation` (`targetConnected`, `targetGenus`).  So
   `Count.RowWalk.rowAtMostOneTransition_of_simpleTarget` needs nothing beyond
   the presentation itself.

Together: on a full-dimensional presentation over a connected genus-zero
target, a row carrying one ramified occurrence has ramification at most one at
every interior vertex and at most one transition, **with no further
hypothesis**.  That is `rowCalculus_of_index_ne_one`.

## What is proved

* `rowAvoidsLeaves_of_index_ne_one` -- observation 1, on a bare
  `FullDimensionalSourcePresentation`, any universe.
* `simpleTarget_of_fullDim` -- observation 2.
* `rowRamificationAtMostOne_of_index_ne_one`,
  `rowAtMostOneTransition_of_index_ne_one`, `rowCalculus_of_index_ne_one` --
  the member's row calculus on an arbitrary full-dimensional presentation over a
  `CFGraph.{0}` target.  No `RowAvoidsLeaves`, no `SimpleTarget`, no
  `DanglingEdgeNoGlue`, no `HasPathEnds`: all four are derived.
* `rowCalculus_of_supply` -- **the same statement on the outgoing-candidate
  interface**: for any member of any wall family carrying an
  `A04FourTags.FullDimSupply`, gated exactly on that member's own
  `det ≠ 0`.  This is one statement for all ten wall types, not ten.
* `forall_index_dvd_of_transport_of_fullDim`,
  `incomingRowDenominator_dvd_of_transport_of_fullDim` --
  `Count.RowRegrowth`'s §3 with receipt 1 removed: the upper half of
  `lemma-edge-deno` (b), transported to an incoming row, needing only the
  member's full-dimensional presentation, the regrown transition's siting and
  the transport.
* `forall_index_dvd_of_transport_of_supply` -- the same, read at a member of an
  outgoing-candidate interface, so that the only gate left is `c⁽q⁾ ≠ 0`.

## What is NOT proved -- every hypothesis that remains explicit

* **`c⁽q⁾ ≠ 0`.**  Every statement about a member is gated on that member's own
  determinant being nonzero, in the form `det ≠ 0` or as the argument of
  `FullDimSupply.fullDim`.  This is not an oversight: `Count.IndexPattern`'s
  `not_two_transitions_on_one_row` *is* the vanishing of a determinant with two
  column relations, so a member with `det = 0` genuinely may carry two
  transitions on one row.  Part II's own parenthesis "whenever `c⁽q⁾ ≠ 0`" in the
  proof of `prop-signed-mult` says the same.
  The dichotomy that makes the gate harmless -- a member with `det = 0`
  contributes `0` to `Σ_q Mult φ_q` whatever its denominator -- is carried out
  for Figure 33 in `Count.W2M1kMemberBalance`.
* **The siting of the regrown transition** (`hTransition`, `hRegrownSurvives`,
  `hRegrownIncident`, `hPartnerSurvives`, `hPartnerIncident`, `hPartnerNe`,
  `hTerminal`, `hPartnerIndex`).  These are `Count.RowRegrowth`'s own
  hypotheses, unchanged; nothing here weakens or discharges them.  For Figure 33
  they are census facts of `LocalCases.W2M1kStableGraph` named in
  `Count.RowRegrowth`'s module docstring.
* **`hTransport`** -- the index-preserving injection of the incoming row's
  occurrences into the member's row.  Untouched.
* Nothing here is conditional on integrality, on `D_q = D₀` (which
  is false in general), on the genus or degree of the source, or on any
  sharp incoming denominator.

## Non-vacuity

No structure is introduced.  §5 instantiates the headline on the caterpillar
full-dimensional morphism over `T^CL_g`: a pair edge carries a row of constant index
`2` (`Count.EdgeDenominator.rowDenominator_cat_pairEdge`), so
`rowAvoidsLeaves_of_index_ne_one` applies with a genuinely ramified witness and
`rowCalculus_of_index_ne_one` returns the row calculus there.  The
outgoing-candidate interface itself is inhabited at seven of the ten tags by
`LocalCases.A04MoreTags`, and for `{w2-r2-nd3-M-1k}` by
`LocalCases.A04M1kWiring.m1kAlignedSupply` / `m1kSeparatedSupply`.

## Consumers

The two index hypotheses of
`Count.RowGeodesic.sum_signedMult_canonical_eq_zero_of_genusZero`, the
conditional cases of the multiplicity balances at the walls, and the balance at a
type change.  `Count.W2M1kMemberBalance` is the `{w2-r2-nd3-M-1k}` consumer.
-/

namespace DraismaVargas.Count.OutgoingRowCalculus

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.RowWalk

/-! ## 1.  Leaf avoidance is free on a row that carries a ramified occurrence -/

section Basic

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`RowAvoidsLeaves` from one occurrence of index `≠ 1`.**

`Count.EdgeDenominator.sourceEdgeIndex_eq_one_of_passesAboveLeaf` is
`lemma-edge-deno` (a) in its sharpest form: *every* occurrence displayed on a
leaf-passing row has dilation index one, with no hypothesis.  So a single
displayed occurrence of index `≠ 1` certifies that the row avoids leaves. -/
theorem rowAvoidsLeaves_of_index_ne_one
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hIndex : data.sourceEdgeIndex edge ≠ 1) :
    RowAvoidsLeaves data path := by
  have hRow : fd.labelling.row.symm (fd.labelling.row path) = path := by simp
  rw [← hRow, rowAvoidsLeaves_iff_not_passesAboveLeaf]
  intro hPasses
  exact hIndex (EdgeDenominator.sourceEdgeIndex_eq_one_of_passesAboveLeaf fd hPasses
    ((mem_rowEdges_iff_onRow fd.labelling (fd.labelling.row path) edge).mpr (by rwa [hRow])))

/-- **`r ≤ 1` at every interior vertex of a ramified row**, with no leaf
hypothesis. -/
theorem rowRamificationAtMostOne_of_index_ne_one
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hIndex : data.sourceEdgeIndex edge ≠ 1) :
    RowRamificationAtMostOne data path :=
  rowRamificationAtMostOne_of_rowAvoidsLeaves fd
    (rowAvoidsLeaves_of_index_ne_one fd hEdge hIndex)

end Basic

/-! ## 2.  `SimpleTarget` is a field of the presentation -/

section GenusZero

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`Count.RowWalk.SimpleTarget` of a full-dimensional presentation's own
target.**  `RowGeodesic.simpleTarget_of_genusZero` applied to the presentation's
`targetConnected` and `targetGenus` fields; no hypothesis is added. -/
theorem simpleTarget_of_fullDim
    (fd : FullDimensionalSourcePresentation data coordinate) : SimpleTarget target :=
  RowGeodesic.simpleTarget_of_genusZero fd.targetConnected fd.targetGenus

/-- **The row calculus, on a bare full-dimensional presentation.**  A stable row
carrying one occurrence of dilation index `≠ 1` has at most one transition.  The
only inputs are the presentation itself and that one occurrence. -/
theorem rowAtMostOneTransition_of_index_ne_one
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hIndex : data.sourceEdgeIndex edge ≠ 1) :
    RowAtMostOneTransition data path :=
  rowAtMostOneTransition_of_simpleTarget fd (simpleTarget_of_fullDim fd)
    (rowAvoidsLeaves_of_index_ne_one fd hEdge hIndex)

/-- **Both halves of `Count.RowRegrowth`'s receipt 1 at once.** -/
theorem rowCalculus_of_index_ne_one
    (fd : FullDimensionalSourcePresentation data coordinate)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hIndex : data.sourceEdgeIndex edge ≠ 1) :
    RowRamificationAtMostOne data path ∧ RowAtMostOneTransition data path :=
  ⟨rowRamificationAtMostOne_of_index_ne_one fd hEdge hIndex,
    rowAtMostOneTransition_of_index_ne_one fd hEdge hIndex⟩

end GenusZero

/-! ## 3.  The same on the outgoing-candidate interface

`LocalCases.WallProgress.WallInput` is the one dispatcher every wall passes
through, and its `family` field is a `BalancedGlobal.GaugeFamily`, so *every*
outgoing member of *every* wall family is a
`BalancedGlobal.Candidate`.  `LocalCases.A04FourTags.FullDimSupply` is the
object that turns such a member into a `FullDimensionalSourcePresentation`,
gated on that member's own nonsingularity -- Part II's "whenever
`c⁽q⁾ ≠ 0`".  A statement made here therefore serves all ten wall families at
once. -/

section Supply

open DraismaVargas.LocalCases.A04FourTags
open DraismaVargas.LocalCases.WallProgress

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {wall : coordinate}

/-- **The row calculus on the outgoing-candidate interface.**  For every member of
every wall family with a full-dimensional supply, every stable row of that
member carrying an occurrence of dilation index `≠ 1` has ramification at most
one at each interior vertex and at most one transition.  The single gate is
`hdet`, the member's own `c⁽q⁾ ≠ 0`. -/
theorem rowCalculus_of_supply {input : WallInput degree coordinate wall}
    (supply : FullDimSupply input) (outgoing : Fin input.case.arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation outgoing)).det ≠ 0)
    {memberRow : StablePath (input.family.candidate outgoing).datum}
    {edge : (input.family.candidate outgoing).datum.SourceEdge}
    (hEdge : OnRow (input.family.candidate outgoing).datum memberRow edge)
    (hIndex : (input.family.candidate outgoing).datum.sourceEdgeIndex edge ≠ 1) :
    RowRamificationAtMostOne (input.family.candidate outgoing).datum memberRow ∧
      RowAtMostOneTransition (input.family.candidate outgoing).datum memberRow :=
  rowCalculus_of_index_ne_one (supply.fullDim outgoing hdet) hEdge hIndex

end Supply

/-! ## 4.  `Count.RowRegrowth` §3 with receipt 1 discharged

The upper half of `lemma-edge-deno` (b), transported to an incoming row.  The
statement is `Count.RowRegrowth.forall_index_dvd_of_transport` verbatim, minus
`hNoGlue`, `hEnds`, `hTame` and `hOne`, all four of which §1--§2 derive from
`memberFD` and from `hPartnerIndex` together with `hIndexNeOne`. -/

section Transport

open DraismaVargas.Count.RowRegrowth

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {memberTarget : CFGraph.{0}} {memberDegree : ℕ}
  {member : GluingDatum memberTarget memberDegree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`d₀ ∣ k` on the rectangular incoming matrix, from a member's regrown
transition, with the member's row calculus discharged.**

Compared with `Count.RowRegrowth.forall_index_dvd_of_transport` the hypotheses
`hNoGlue`, `hEnds`, `hTame` and `hOne` are gone: the first two are fields of
`memberFD`, and the last two are §1--§2 applied to the partner occurrence,
which lies on the row and has index `index ≠ 1`. -/
theorem forall_index_dvd_of_transport_of_fullDim
    (memberFD : FullDimensionalSourcePresentation member coordinate)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    {path : StablePath data} {index : ℕ}
    (hPartnerIndex : member.sourceEdgeIndex partner = index) (hIndexNeOne : index ≠ 1)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      data.sourceEdgeIndex edge ∣ index := by
  have hPartnerRow : OnRow member memberRow partner :=
    onRow_partner hTransition hPartnerSurvives hPartnerIncident
  have hPartnerNeOne : member.sourceEdgeIndex partner ≠ 1 := by
    rw [hPartnerIndex]; exact hIndexNeOne
  exact forall_index_dvd_of_transport memberFD.danglingEdgeNoGlue memberFD.pathEnds
    (rowRamificationAtMostOne_of_index_ne_one memberFD hPartnerRow hPartnerNeOne)
    (rowAtMostOneTransition_of_index_ne_one memberFD hPartnerRow hPartnerNeOne)
    hTransition hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident
    hPartnerNe hTerminal hPartnerIndex hTransport

/-- The incoming row denominator form. -/
theorem incomingRowDenominator_dvd_of_transport_of_fullDim
    (memberFD : FullDimensionalSourcePresentation member coordinate)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    {path : StablePath data} {index : ℕ}
    (hPartnerIndex : member.sourceEdgeIndex partner = index) (hIndexNeOne : index ≠ 1)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    TrivalentWeight.incomingRowDenominator data path ∣ index :=
  TrivalentWeight.incomingRowDenominator_dvd_of_forall_index_dvd path
    (forall_index_dvd_of_transport_of_fullDim memberFD hTransition hRegrownSurvives
      hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe hTerminal
      hPartnerIndex hIndexNeOne hTransport)

end Transport

section TransportSupply

open DraismaVargas.Count.RowRegrowth
open DraismaVargas.LocalCases.A04FourTags
open DraismaVargas.LocalCases.WallProgress

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {memberDegree : ℕ} {wall : coordinate}

/-- **The upper half of `lemma-edge-deno` (b) on the outgoing-candidate
interface.**  Everything the member owes is now one inequality, `c⁽q⁾ ≠ 0`; the
remaining hypotheses are the siting of the regrown transition and the transport
`hTransport`, both of which are about the geometry of the wall
crossing and not about the member's row calculus. -/
theorem forall_index_dvd_of_transport_of_supply
    {input : WallInput memberDegree coordinate wall} (supply : FullDimSupply input)
    (outgoing : Fin input.case.arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation outgoing)).det ≠ 0)
    {memberRow : StablePath (input.family.candidate outgoing).datum}
    {regrown partner : (input.family.candidate outgoing).datum.SourceEdge}
    {vertex : (input.family.candidate outgoing).datum.SourceVertex}
    (hTransition : IsRowTransition (input.family.candidate outgoing).datum memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling (input.family.candidate outgoing).datum regrown)
    (hRegrownIncident : Incident (input.family.candidate outgoing).datum regrown vertex)
    (hPartnerSurvives : ¬ IsDangling (input.family.candidate outgoing).datum partner)
    (hPartnerIncident : Incident (input.family.candidate outgoing).datum partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : (input.family.candidate outgoing).datum.SourceVertex,
      Incident (input.family.candidate outgoing).datum regrown u →
      nonDanglingValency (input.family.candidate outgoing).datum u = 2 → u = vertex)
    {path : StablePath data} {index : ℕ}
    (hPartnerIndex : (input.family.candidate outgoing).datum.sourceEdgeIndex partner = index)
    (hIndexNeOne : index ≠ 1)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : (input.family.candidate outgoing).datum.SourceEdge,
        OnRow (input.family.candidate outgoing).datum memberRow image ∧ image ≠ regrown ∧
          (input.family.candidate outgoing).datum.sourceEdgeIndex image =
            data.sourceEdgeIndex edge) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      data.sourceEdgeIndex edge ∣ index :=
  forall_index_dvd_of_transport_of_fullDim (supply.fullDim outgoing hdet) hTransition
    hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe
    hTerminal hPartnerIndex hIndexNeOne hTransport

end TransportSupply

/-! ## 5.  Non-vacuity on the caterpillar of loops

`LocalCases.CaterpillarRows.fullDim` is the full-dimensional presentation of the
caterpillar of loops, and `Count.EdgeDenominator.rowDenominator_cat_pairEdge`
says a pair edge of `T^CL_g` -- a stem or a slope-two spine edge -- carries a
row of constant dilation index `2`.  That is a genuinely ramified witness, so
§1 and §2 apply with nothing assumed. -/

section Witness

open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.Count.Caterpillar

/-- The main occurrence of a pair-edge row of `T^CL_g` has index `2`. -/
theorem sourceEdgeIndex_main_pairEdge (m : ℕ) {i : Fin (6 * m + 3)}
    (hPair : IsPairEdge m i.val) :
    (caterpillarDatum m).sourceEdgeIndex ((caterpillarDatum m).sourceEdge (occ m i) 0) = 2 := by
  rw [CaterpillarStable.sourceEdgeIndex_caterpillar, ite_eq_left ⟨hPair, Or.inl rfl⟩]

/-- **The hypotheses of §1--§2 are inhabited.**  A pair-edge row of `T^CL_g`
avoids leaves, by its own index and nothing else. -/
example (m : ℕ) {i : Fin (6 * m + 3)} (hPair : IsPairEdge m i.val) :
    RowAvoidsLeaves (caterpillarDatum m) ((CaterpillarRows.labelling m).row.symm i) :=
  rowAvoidsLeaves_of_index_ne_one (CaterpillarRows.fullDim m)
    ((mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i _).mp
      (EdgeDenominator.main_mem_rowEdges m i))
    (by rw [sourceEdgeIndex_main_pairEdge m hPair]; norm_num)

/-- **The headline is inhabited.**  The row calculus on a pair-edge row of
`T^CL_g`, with no hypothesis beyond the caterpillar presentation. -/
example (m : ℕ) {i : Fin (6 * m + 3)} (hPair : IsPairEdge m i.val) :
    RowRamificationAtMostOne (caterpillarDatum m)
        ((CaterpillarRows.labelling m).row.symm i) ∧
      RowAtMostOneTransition (caterpillarDatum m)
        ((CaterpillarRows.labelling m).row.symm i) :=
  rowCalculus_of_index_ne_one (CaterpillarRows.fullDim m)
    ((mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i _).mp
      (EdgeDenominator.main_mem_rowEdges m i))
    (by rw [sourceEdgeIndex_main_pairEdge m hPair]; norm_num)

end Witness

end DraismaVargas.Count.OutgoingRowCalculus
