import DraismaVargasCount.RowWalk
import DraismaVargasCount.IncomingSimpleColumn

/-!
# The regrown transition: where a stable row's index constancy actually comes from

**Source.**  Vargas, Part II (arXiv:2609.09109): `proposition-at-most-two-weights`,
`lemma-edge-deno` cases (b) and (c), and the proof of `prop-signed-mult` (1), whose
displayed matrices `A⁽¹⁾, A⁽²⁾, A⁽³⁾` are the input to everything below.  Part I's
case `{w2-r2-nd3-M-1k}` is Figure 33 of Draisma--Vargas Part I (arXiv:1909.12924).

`RowWalk` reduces the upper half `d₀ ∣ k` of `lemma-edge-deno` (b) on the
two distinguished incoming rows of `{w2-r2-nd3-M-1k}` to the single hypothesis
`RowUnramified data (secondRow profile)` (resp. `thirdRow`), which is *not*
implied by row injectivity.  This file answers where that hypothesis comes from,
and the answer is not the wall.

## The finding

**`RowUnramified` on `h₂` and `h₃` is not a consequence of the incoming datum.**
`SecondEquation.W2SourceInput` constrains one target vertex, the wall: its
`equation_c` says `ch(w₀) + val(w₀) - 3 = 1`, and `W2R2SourceProfile` then fixes
the four occurrences at the distinguished block.  `RowUnramified` quantifies
over *every* interior vertex of the row, including vertices arbitrarily far from
the wall, above target vertices the wall interface never mentions.  At a
cycle-preserving codimension-one limit the total dimension correction is `1`
(`W4Bridge.sum_targetExcess_contractDatum`), so away from the wall the datum is
change-minimal, and change-minimality at a **divalent** target vertex `v` reads
`ch(v) = 1`: exactly one block above `v` may carry `r_φ = 1`.  That is a
transition (`Count.RowWalk.IsRowTransition`), it is `lemma-edge-deno` case (c),
and nothing local to the wall forbids it from sitting on `h₂` or on `h₃`.  Part
II exhibits `r_φ = 1` vertices in genuine full-dimensional morphisms (the
bridge-and-loop lemma, `lm:bridge-and-loop`), so case (c) is not empty.

**It is nevertheless true, and the proof runs on the members, not on the limit.**
Read the matrices displayed in Part II's proof of `prop-signed-mult` (1).  Row `h₂` of `A⁽²⁾` is
`(1/(k-1), 1/k, 0, …)` and row `h₃` of `A⁽³⁾` is `(1/(k+1), 0, 1/k, …)`: in
`M⁽²⁾` the row of `e₂` acquires one new occurrence of index `k - 1`, and in
`M⁽³⁾` the row of `e₃` acquires one new occurrence of index `k + 1`.  The
census of `W2M1kStableGraph` says exactly this and says where:

* `W2M1kStableGraph.divided_nonDanglingValency_pair` gives the `t₂`-side
  endpoint over `A₀ ∖ {p}` non-dangling valency **two**, with survivors `e₂`
  (index `k`) and the residual new occurrence (index `k - 1`,
  `ResolutionM1k.secondNewEdge_blockCard_third`, surviving by
  `divided_new_third_survives`), and `divided_new_third_stablePath_eq` puts that
  new occurrence on `e₂`'s row; its far endpoint, the `t₃`-side one over
  `A₀ ∖ {q}`, has non-dangling valency **three**
  (`divided_nonDanglingValency_branch`), so the new occurrence is *terminal* on
  the row;
* `M⁽³⁾`'s `t₃`-side endpoint over `A₀` has non-dangling valency **two**
  (`joined_nonDanglingValency_single`) with survivors `e₃` (index `k`) and the
  new occurrence of index `k + 1` (`ResolutionM1k.thirdResolution_newEdge_blockCard`,
  surviving by `joined_new_survives`), `joined_new_stablePath_eq_third` puts it
  on `e₃`'s row, and the `t₂`-side endpoint over `A₀` has valency three
  (`joined_nonDanglingValency_double`), so that occurrence is terminal too.

So each of the two distinguished rows carries, *in the member that perturbs it*,
a transition at a terminal occurrence.  `Count.RowWalk`'s
`rowAtMostOneTransition_of_simpleTarget` then says the member's row has **no
other** transition, and the limit's row is the member's row minus the terminal
occurrence.  Hence the limit's row is unramified -- and in the sharp form the
count consumes, every index displayed on it equals `k`.

That is the content of this file: the passage from "one transition, at a
terminal occurrence" to "constant index off that occurrence", and the transport
statement that turns a member-side row into the incoming row.

## What is proved

* `localRamification_eq_zero_of_ne_transition` -- with `r ≤ 1` at every interior
  vertex and at most one transition, every interior vertex of the row other than
  the transition is unramified.  No `FullDimensionalSourcePresentation`.
* `sourceEdgeIndex_eq_off_regrown` -- **the engine**: on a row with at most one
  transition, sited at a vertex one of whose two survivors is an occurrence with
  no other interior endpoint, every displayed index off that occurrence equals
  the index of its partner at the transition.  Proved by running
  `Count.RowWalk.chain_const` on the ordered walk with the index function
  corrected at the terminal occurrence, so no list surgery and no square
  labelling is used; `DanglingEdgeNoGlue` and `HasPathEnds` are the only
  structural inputs, and both are available at a codimension-one limit.
* `forall_index_eq_of_transport`, `forall_index_dvd_of_transport` -- the same
  conclusion pushed along an index-preserving transport of the incoming row into
  the member's row, in exactly the shape
  `Count.IncomingSimpleColumn.incomingRowDenominator_secondRow_eq_of_index` asks
  for.
* `forall_index_eq_of_transport_of_rowUnramified`,
  `forall_index_dvd_of_transport_of_rowUnramified` -- the transition-free
  variant, for a member whose row is already unramified.
* `forall_index_dvd_secondRow_of_regrowth`, `forall_index_dvd_thirdRow_of_regrowth`,
  `incomingRowDenominator_secondRow_eq_of_regrowth`,
  `incomingRowDenominator_thirdRow_eq_of_regrowth` -- the `{w2-r2-nd3-M-1k}`
  specialisations, which discharge `Count.RowWalk`'s residue
  `RowUnramified data (secondRow profile)` and its twin *in the form their
  consumers use them*, namely the index hypotheses `hIndex2`, `hIndex3` of
  `Count.IncomingSimpleColumn.sum_signedMult_canonical_eq_zero_of_rows_ne`.

## Explicit inputs here, and their downstream producers

Every statement below about the incoming datum carries, explicitly:

1. **The member's row calculus** -- `RowRamificationAtMostOne member memberRow`
   and `RowAtMostOneTransition member memberRow`.  These are theorems of
   `Count.RowWalk` (`rowRamificationAtMostOne_of_rowAvoidsLeaves`,
   `rowAtMostOneTransition_of_simpleTarget`) as soon as the member carries a
   `FullDimensionalSourcePresentation` and its row avoids leaves. Leaf avoidance
   is automatic from any row occurrence of index different from one, by
   `Count.OutgoingRowCalculus.rowAvoidsLeaves_of_index_ne_one`; the M-1k
   application supplies such an occurrence. Figure 33's member presentations
   are constructed by `Count.W2M1kMemberBalance.memberPresentation` from
   the incoming chart under the relevant nonzero-determinant gate.
   `Count.OutgoingRowCalculus.rowCalculus_of_index_ne_one` then supplies both
   row-calculus inputs without a separate leaf-avoidance receipt.
2. **The transport** `hTransport` -- an index-preserving map from the incoming
   row's occurrences to the member's row occurrences other than the regrown one.
   `Count.W2M1kRowTransport` packages it using the stable-row
   lift and `Candidate.oldSourceEdge`, including the branch-swapped orientation.
   `Count.W2M1kTransitionSiting` supplies the actual terminal transition sites.

These are explicit inputs of this lower-level module because their producers
import it.  `Count.W2M1kIncomingTame.sum_signedMult_eq_zero` assembles all of
them and derives the incoming tame-row bound, which gives the multiplicity
balance of the actual M-1k family (Equation (7) of Part I).

Nothing here is conditional on integrality, on the genus or degree of the
source, on `SimpleTarget`, on `RowTargetInjective`, or on nonsingularity of any
member: those enter only through the two receipts above, and only on the member.

**The dichotomy that makes the receipt harmless.**  If the member `M⁽²⁾` is not
full-rank then `c⁽²⁾ = det A⁽²⁾ = 0` and its term of
`½c⁽¹⁾ + (k-1)c⁽²⁾ + (k+1)c⁽³⁾ = 0` drops out of `Σ_q Mult φ_q` regardless of
`d₀(h₂)`; if it is full-rank then receipt 1 holds for it and `d₀(h₂) = k`
follows.  The same for `M⁽³⁾` and `h₃`, and if both determinants vanish the
identity forces `c⁽¹⁾ = 0` too and all three terms vanish.  This is Part II's
own parenthesis "whenever `c⁽q⁾ ≠ 0`" in the proof of `prop-signed-mult`, and it
is why the count does
not need `RowUnramified` unconditionally -- only on the members that actually
contribute.

## Non-vacuity

No structure is introduced.  §5 instantiates the transition-free transport on
the caterpillar of loops `T^CL_g`, where `Count.RowWalk.rowUnramified_cat`
supplies the member row and the transport is the identity.  The transition-bearing
hypothesis bundle of §2 cannot be inhabited there -- `Count.RowWalk`'s own
docstring records that `IsRowTransition` is deliberately empty on `T^CL_g`, it
being inhabited exactly by `lemma-edge-deno` case (c) -- and the census lemmas
that inhabit it at Figure 33's members are named in "The finding" above.

## Consumers

The residue `RowUnramified`, in the form of the two index hypotheses of
`Count.IncomingSimpleColumn.sum_signedMult_canonical_eq_zero_of_rows_ne`, and the
multiplicity balances at the other walls and at type changes.  §2--§3 are case-independent
and serve all ten trivalent deformation cases; §4 is the `{w2-r2-nd3-M-1k}`
naming of §3.
-/

namespace DraismaVargas.Count.RowRegrowth

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.IndexPattern
open DraismaVargas.Count.RowWalk

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-! ## 1.  Away from the one transition -/

/-- **Every interior vertex of the row other than the transition is
unramified.**  This is `rowUnramified_iff_forall_not_isRowTransition` localised
at a named transition: `RowAtMostOneTransition` makes the transition unique, and
`RowRamificationAtMostOne` leaves no third value for `r_φ`. -/
theorem localRamification_eq_zero_of_ne_transition
    {path : StablePath data} (hTame : RowRamificationAtMostOne data path)
    (hOne : RowAtMostOneTransition data path)
    {vertex other : data.SourceVertex} (hTransition : IsRowTransition data path vertex)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hIncident : Incident data edge other)
    (hValency : nonDanglingValency data other = 2) (hNe : other ≠ vertex) :
    data.localRamification other.1.1 ⟨other.1.2, other.2⟩ = 0 := by
  rcases hTame other edge hEdge hIncident hValency with hZero | hRamified
  · exact hZero
  · exact absurd (hOne other vertex ⟨hValency, hRamified, edge, hEdge, hIncident⟩ hTransition)
      hNe

/-! ## 2.  The engine: constancy off a terminal regrown occurrence -/

/-- **The index is constant off the regrown occurrence.**

`regrown` is an occurrence of the row whose only interior endpoint is the row's
unique transition `vertex`, and `partner` is the other survivor there.  Then
every occurrence of the row other than `regrown` carries the index of `partner`.

The proof runs `Count.RowWalk.chain_const` along the ordered walk with the
*corrected* index function `e ↦ if e = regrown then m(partner) else m(e)`: at
`vertex` the correction is exactly what the transition destroys, and at every
other interior vertex neither survivor is `regrown` (terminality) and the vertex
is unramified (§1).  No sublist of the walk is ever formed, so no square
labelling and no full-dimensionality is used -- only `DanglingEdgeNoGlue` and
`HasPathEnds`, both of which a codimension-one wall datum has. -/
theorem sourceEdgeIndex_eq_off_regrown
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} {regrown partner : data.SourceEdge}
    {vertex : data.SourceVertex}
    (hTame : RowRamificationAtMostOne data path)
    (hOne : RowAtMostOneTransition data path)
    (hTransition : IsRowTransition data path vertex)
    (hRegrownSurvives : ¬ IsDangling data regrown)
    (hRegrownIncident : Incident data regrown vertex)
    (hPartnerSurvives : ¬ IsDangling data partner)
    (hPartnerIncident : Incident data partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : data.SourceVertex, Incident data regrown u →
      nonDanglingValency data u = 2 → u = vertex)
    {first second : data.SourceEdge}
    (hFirst : OnRow data path first) (hFirstNe : first ≠ regrown)
    (hSecond : OnRow data path second) (hSecondNe : second ≠ regrown) :
    data.sourceEdgeIndex first = data.sourceEdgeIndex second := by
  have hStep : ∀ a b : data.SourceEdge, OnRow data path a → OnRow data path b →
      (∃ u : data.SourceVertex, Incident data a u ∧ Incident data b u ∧
        nonDanglingValency data u = 2) →
      (if a = regrown then data.sourceEdgeIndex partner else data.sourceEdgeIndex a) =
        (if b = regrown then data.sourceEdgeIndex partner else data.sourceEdgeIndex b) := by
    rintro a b hA hB ⟨u, haI, hbI, hu⟩
    by_cases hEq : u = vertex
    · subst hEq
      have hA' : a = regrown ∨ a = partner :=
        eq_or_eq_of_nonDanglingValency_two hu hRegrownSurvives hRegrownIncident
          hPartnerSurvives hPartnerIncident (Ne.symm hPartnerNe) hA.survives haI
      have hB' : b = regrown ∨ b = partner :=
        eq_or_eq_of_nonDanglingValency_two hu hRegrownSurvives hRegrownIncident
          hPartnerSurvives hPartnerIncident (Ne.symm hPartnerNe) hB.survives hbI
      rcases hA' with rfl | rfl <;> rcases hB' with rfl | rfl <;> simp [hPartnerNe]
    · have haNe : a ≠ regrown := by
        rintro rfl
        exact hEq (hTerminal u haI hu)
      have hbNe : b ≠ regrown := by
        rintro rfl
        exact hEq (hTerminal u hbI hu)
      rw [if_neg haNe, if_neg hbNe]
      exact sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue hNoGlue hu
        (localRamification_eq_zero_of_ne_transition hTame hOne hTransition hA haI hu hEq)
        hA.survives haI hB.survives hbI
  have hChain := chain_const
    (fun e : data.SourceEdge ↦
      if e = regrown then data.sourceEdgeIndex partner else data.sourceEdgeIndex e)
    (fun a b : data.SourceEdge ↦ ∃ u : data.SourceVertex, Incident data a u ∧
      Incident data b u ∧ nonDanglingValency data u = 2)
    (OnRow data path) hStep (orderedRow hEnds path)
    (fun x hx ↦ (mem_orderedRow_iff hEnds path x).mp hx) (orderedRow_chain hEnds path)
    ((mem_orderedRow_iff hEnds path first).mpr hFirst)
    ((mem_orderedRow_iff hEnds path second).mpr hSecond)
  simpa only [if_neg hFirstNe, if_neg hSecondNe] using hChain

/-- The partner at the transition lies on the row. -/
theorem onRow_partner {path : StablePath data} {partner : data.SourceEdge}
    {vertex : data.SourceVertex} (hTransition : IsRowTransition data path vertex)
    (hPartnerSurvives : ¬ IsDangling data partner)
    (hPartnerIncident : Incident data partner vertex) :
    OnRow data path partner := by
  obtain ⟨hValency, -, edge, hEdge, hIncident⟩ := hTransition
  exact onRow_of_incident hValency hEdge hIncident hPartnerSurvives hPartnerIncident

/-- **Every occurrence of the row off the regrown one has the partner's index.**
The `∀`-form of the engine, on the rectangular row set
`TrivalentWeight.incomingRowEdges`. -/
theorem forall_index_eq_off_regrown
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} {regrown partner : data.SourceEdge}
    {vertex : data.SourceVertex}
    (hTame : RowRamificationAtMostOne data path)
    (hOne : RowAtMostOneTransition data path)
    (hTransition : IsRowTransition data path vertex)
    (hRegrownSurvives : ¬ IsDangling data regrown)
    (hRegrownIncident : Incident data regrown vertex)
    (hPartnerSurvives : ¬ IsDangling data partner)
    (hPartnerIncident : Incident data partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : data.SourceVertex, Incident data regrown u →
      nonDanglingValency data u = 2 → u = vertex) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path, edge ≠ regrown →
      data.sourceEdgeIndex edge = data.sourceEdgeIndex partner := by
  intro edge hEdge hEdgeNe
  exact sourceEdgeIndex_eq_off_regrown hNoGlue hEnds hTame hOne hTransition
    hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe
    hTerminal ((onRow_iff_mem_incomingRowEdges path edge).mpr hEdge) hEdgeNe
    (onRow_partner hTransition hPartnerSurvives hPartnerIncident) hPartnerNe

end DraismaVargas.Count.RowRegrowth

namespace DraismaVargas.Count.RowRegrowth

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.IndexPattern
open DraismaVargas.Count.RowWalk

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {memberTarget : CFGraph} {memberDegree : ℕ}
  {member : GluingDatum memberTarget memberDegree}

/-! ## 3.  Transport: the incoming row inside the member's row

The incoming codimension-one datum and the member live over *different* target
graphs, so the two rows are not the same object and the passage between them is
a hypothesis, named `hTransport`.  It says exactly what the wall-crossing
geometry provides: every occurrence displayed on the incoming row is displayed
on the member's row, with the same dilation index, and is not the regrown
occurrence (which has no counterpart downstairs -- it is the one that contracts).
-/

/-- **The upper half of `lemma-edge-deno` (b), transported.**  Every index
displayed on the incoming row equals the index of the member's partner at the
regrown transition. -/
theorem forall_index_eq_of_transport
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTame : RowRamificationAtMostOne member memberRow)
    (hOne : RowAtMostOneTransition member memberRow)
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    {path : StablePath data}
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      data.sourceEdgeIndex edge = member.sourceEdgeIndex partner := by
  intro edge hEdge
  obtain ⟨image, hImage, hImageNe, hIndex⟩ := hTransport edge hEdge
  rw [← hIndex]
  exact sourceEdgeIndex_eq_off_regrown hNoGlue hEnds hTame hOne hTransition
    hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe
    hTerminal hImage hImageNe
    (onRow_partner hTransition hPartnerSurvives hPartnerIncident) hPartnerNe

/-- The divisibility form, which is what
`Count.IncomingSimpleColumn.incomingRowDenominator_secondRow_eq_of_index` and
`Count.TrivalentWeight.incomingRowDenominator_dvd_of_forall_index_dvd` consume. -/
theorem forall_index_dvd_of_transport
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTame : RowRamificationAtMostOne member memberRow)
    (hOne : RowAtMostOneTransition member memberRow)
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    {path : StablePath data} {index : ℕ}
    (hPartnerIndex : member.sourceEdgeIndex partner = index)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      data.sourceEdgeIndex edge ∣ index := by
  intro edge hEdge
  rw [forall_index_eq_of_transport hNoGlue hEnds hTame hOne hTransition hRegrownSurvives
    hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe hTerminal hTransport
    edge hEdge, hPartnerIndex]

/-- `d₀ ∣ k` on the rectangular incoming matrix, from a regrown transition on the
member. -/
theorem incomingRowDenominator_dvd_of_transport
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTame : RowRamificationAtMostOne member memberRow)
    (hOne : RowAtMostOneTransition member memberRow)
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    {path : StablePath data} {index : ℕ}
    (hPartnerIndex : member.sourceEdgeIndex partner = index)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    TrivalentWeight.incomingRowDenominator data path ∣ index :=
  TrivalentWeight.incomingRowDenominator_dvd_of_forall_index_dvd path
    (forall_index_dvd_of_transport hNoGlue hEnds hTame hOne hTransition hRegrownSurvives
      hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe hTerminal
      hPartnerIndex hTransport)

/-- **The transition-free variant.**  When the member's row carries no
transition at all -- the case of every row that no member perturbs -- the
transport needs no regrown occurrence and no terminality. -/
theorem forall_index_eq_of_transport_of_rowUnramified
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    {memberRow : StablePath member} (hUnram : RowUnramified member memberRow)
    {anchor : member.SourceEdge} (hAnchor : OnRow member memberRow anchor)
    {path : StablePath data}
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      data.sourceEdgeIndex edge = member.sourceEdgeIndex anchor := by
  intro edge hEdge
  obtain ⟨image, hImage, hIndex⟩ := hTransport edge hEdge
  rw [← hIndex]
  exact sourceEdgeIndex_eq_of_rowUnramified hNoGlue hEnds hUnram hImage hAnchor

theorem forall_index_dvd_of_transport_of_rowUnramified
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    {memberRow : StablePath member} (hUnram : RowUnramified member memberRow)
    {anchor : member.SourceEdge} (hAnchor : OnRow member memberRow anchor)
    {path : StablePath data} {index : ℕ}
    (hAnchorIndex : member.sourceEdgeIndex anchor = index)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      data.sourceEdgeIndex edge ∣ index := by
  intro edge hEdge
  rw [forall_index_eq_of_transport_of_rowUnramified hNoGlue hEnds hUnram hAnchor
    hTransport edge hEdge, hAnchorIndex]

end DraismaVargas.Count.RowRegrowth

namespace DraismaVargas.Count.RowRegrowth

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.W2M1kCommonBalance
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2M1kSourceCandidates
open DraismaVargas.Count.RowWalk

/-! ## 4.  The two distinguished rows of `{w2-r2-nd3-M-1k}`

`e₂` and `e₃` have index `k` (`Shape.second_index`, `Shape.third_index`).  In
`M⁽²⁾` the row of `e₂` gains a terminal occurrence of index `k - 1` at a
non-dangling-valency-two endpoint whose other survivor is `e₂`; in `M⁽³⁾` the
row of `e₃` gains a terminal occurrence of index `k + 1` at a
non-dangling-valency-two endpoint whose other survivor is `e₃`.  §3 therefore
applies with `partner` the member's copy of `e₂` (resp. `e₃`) and `index = k`,
and delivers `Count.RowWalk`'s residue in the form its consumers use. -/

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  {memberTarget : CFGraph} {memberDegree : ℕ}
  {member : GluingDatum memberTarget memberDegree}

/-- **The upper half on `h₂`, from `M⁽²⁾`'s regrown transition.**  This is
`Count.RowWalk.forall_index_dvd_secondRow` with its residue
`RowUnramified data (secondRow profile)` replaced by the member-side bundle. -/
theorem forall_index_dvd_secondRow_of_regrowth
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    (shape : Shape profile)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTame : RowRamificationAtMostOne member memberRow)
    (hOne : RowAtMostOneTransition member memberRow)
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    (hPartnerIndex : member.sourceEdgeIndex partner = shape.k)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data (secondRow profile),
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k :=
  forall_index_dvd_of_transport hNoGlue hEnds hTame hOne hTransition hRegrownSurvives
    hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe hTerminal
    hPartnerIndex hTransport

/-- **The upper half on `h₃`, from `M⁽³⁾`'s regrown transition.** -/
theorem forall_index_dvd_thirdRow_of_regrowth
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    (shape : Shape profile)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTame : RowRamificationAtMostOne member memberRow)
    (hOne : RowAtMostOneTransition member memberRow)
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    (hPartnerIndex : member.sourceEdgeIndex partner = shape.k)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data (thirdRow profile),
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k :=
  forall_index_dvd_of_transport hNoGlue hEnds hTame hOne hTransition hRegrownSurvives
    hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe hTerminal
    hPartnerIndex hTransport

/-- **The sharp `d₀(h₂) = k`**: the upper half from `M⁽²⁾`'s regrown transition,
the lower half from the column difference of `IncomingSimpleColumn`.  `hRows` is
`Count.IncomingSimpleColumn`'s own residue and is untouched here. -/
theorem incomingRowDenominator_secondRow_eq_of_regrowth
    (input : W2SourceInput data star) (shape : Shape profile)
    (hRows : secondRow profile ≠ thirdRow profile)
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTame : RowRamificationAtMostOne member memberRow)
    (hOne : RowAtMostOneTransition member memberRow)
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    (hPartnerIndex : member.sourceEdgeIndex partner = shape.k)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data (secondRow profile),
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    TrivalentWeight.incomingRowDenominator data (secondRow profile) = shape.k :=
  IncomingSimpleColumn.incomingRowDenominator_secondRow_eq_of_index profile input shape hRows
    (forall_index_dvd_secondRow_of_regrowth profile hNoGlue hEnds shape hTame hOne
      hTransition hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident
      hPartnerNe hTerminal hPartnerIndex hTransport)

/-- **The sharp `d₀(h₃) = k`.** -/
theorem incomingRowDenominator_thirdRow_eq_of_regrowth
    (input : W2SourceInput data star) (shape : Shape profile)
    (hRows : secondRow profile ≠ thirdRow profile)
    (hNoGlue : DanglingEdgeNoGlue member) (hEnds : HasPathEnds member)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTame : RowRamificationAtMostOne member memberRow)
    (hOne : RowAtMostOneTransition member memberRow)
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    (hPartnerIndex : member.sourceEdgeIndex partner = shape.k)
    (hTransport : ∀ edge ∈ TrivalentWeight.incomingRowEdges data (thirdRow profile),
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    TrivalentWeight.incomingRowDenominator data (thirdRow profile) = shape.k :=
  IncomingSimpleColumn.incomingRowDenominator_thirdRow_eq_of_index profile input shape hRows
    (forall_index_dvd_thirdRow_of_regrowth profile hNoGlue hEnds shape hTame hOne
      hTransition hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident
      hPartnerNe hTerminal hPartnerIndex hTransport)

end DraismaVargas.Count.RowRegrowth

namespace DraismaVargas.Count.RowRegrowth

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.Count.RowWalk

/-! ## 5.  Non-vacuity on the caterpillar of loops

`Count.RowWalk` records that `IsRowTransition` is deliberately empty on
`T^CL_g` -- it is inhabited exactly by `lemma-edge-deno` case (c) -- so §2's
transition-bearing bundle cannot be instantiated there, and the lemmas that do
instantiate it at Figure 33's members are named in the module docstring.  What
`T^CL_g` does inhabit is §3's transport, with the member taken to be the datum
itself, the member's row unramified (`rowUnramified_cat`) and the transport the
identity.  The conclusion is the upper half of `lemma-edge-deno` (b) on the
rectangular incoming interface, which is the shape every consumer of this file
asks for. -/

/-- **The transport is inhabited**, with the identity map on a leaf-free
caterpillar row. -/
theorem transport_cat (m : ℕ) (i : Fin (6 * m + 3)) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges (caterpillarDatum m)
        ((CaterpillarRows.labelling m).row.symm i),
      ∃ image : (caterpillarDatum m).SourceEdge,
        OnRow (caterpillarDatum m) ((CaterpillarRows.labelling m).row.symm i) image ∧
          (caterpillarDatum m).sourceEdgeIndex image =
            (caterpillarDatum m).sourceEdgeIndex edge :=
  fun edge hEdge ↦ ⟨edge, (onRow_iff_mem_incomingRowEdges _ edge).mpr hEdge, rfl⟩

/-- **§3, instantiated**: every index displayed on a leaf-free row of `T^CL_g`
divides the index of that row's main occurrence.
`Count.EdgeDenominator.rowDenominator_cat_pairEdge` evaluates the right-hand
side to `2` on a pair edge and to `1` on a spine edge. -/
example (m : ℕ) {i : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m i) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges (caterpillarDatum m)
        ((CaterpillarRows.labelling m).row.symm i),
      (caterpillarDatum m).sourceEdgeIndex edge ∣
        (caterpillarDatum m).sourceEdgeIndex ((caterpillarDatum m).sourceEdge (occ m i) 0) :=
  forall_index_dvd_of_transport_of_rowUnramified
    (CaterpillarRows.fullDim m).danglingEdgeNoGlue (CaterpillarRows.fullDim m).pathEnds
    (rowUnramified_cat m hNotLeaf)
    ((mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i _).mp
      (EdgeDenominator.main_mem_rowEdges m i))
    rfl (transport_cat m i)

/-- The same read on the incoming row denominator. -/
example (m : ℕ) {i : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m i) :
    TrivalentWeight.incomingRowDenominator (caterpillarDatum m)
        ((CaterpillarRows.labelling m).row.symm i) ∣
      (caterpillarDatum m).sourceEdgeIndex ((caterpillarDatum m).sourceEdge (occ m i) 0) :=
  TrivalentWeight.incomingRowDenominator_dvd_of_forall_index_dvd _
    (forall_index_dvd_of_transport_of_rowUnramified
      (CaterpillarRows.fullDim m).danglingEdgeNoGlue (CaterpillarRows.fullDim m).pathEnds
      (rowUnramified_cat m hNotLeaf)
      ((mem_rowEdges_iff_onRow (CaterpillarRows.labelling m) i _).mp
        (EdgeDenominator.main_mem_rowEdges m i))
      rfl (transport_cat m i))

end DraismaVargas.Count.RowRegrowth
