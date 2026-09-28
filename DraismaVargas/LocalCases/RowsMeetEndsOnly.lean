import DraismaVargas.LocalCases.ForestReceiptGeneral
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-!
# `RowsMeetEndsOnly`, discharged (pure list combinatorics)

**Source.**  `DraismaVargas/LocalCases/ForestReceiptGeneral.lean` §3 and §5.
That file's `RowsMeetEndsOnly strong` (§3) is a receipt of its chain that its
own results do not produce: its §5 closing note shows that three of its four
cases follow from the fields of `TraversalPresentation.StrongPresentation`
(`chain`, `head_isPathEnd`, `getLast_isPathEnd`,
`PresentationDecomposition.Decomposes.nodup`,
`W4StableSource.nonDanglingIncident_eq_pair`), and that the fourth -- an
interior occurrence of a row -- needs one step of a different kind:
`List.IsChain` exposes consecutive pairs of a list, not positions, so
"`edge` is neither the head nor the last entry" has to be turned into
"`edge` has a named predecessor and a named successor in the chain."  This
file supplies exactly that list-combinatorial step and discharges the receipt.
No source proof in the papers is transcribed; §5 of `ForestReceiptGeneral.lean`
is adapted directly (it names the exact case split and the exact contradiction
each half needs).

## What is proved

* §1 **The list-splitting lemma.**  `exists_split_of_ne_head?_getLast?`: a
  list member that is neither the head nor the last entry sits strictly
  between two named neighbours, `l = A ++ a :: edge :: b :: B`.  (If `edge`
  occurs more than once, `List.append_of_mem` picks its *first* occurrence,
  and the two neighbours are read off that occurrence; nothing below needs
  more than the two adjacent relations this particular split gives.)
  `exists_rel_of_mem_of_ne_head?_getLast?` transports an ambient
  `List.IsChain R l` across the split to the two relations `R a edge` and
  `R edge b`, through Mathlib's `List.isChain_append_cons_cons` and
  `List.isChain_cons_cons` (the Mathlib `List.IsChain` API).  Both lemmas are
  stated for a bare `l : List α`
  and used nowhere else in this file except to feed the vertex census below;
  they carry no side conditions of their own.

* §2 **The interior case, closed.**  `rowsMeetEndsOnly_of_strong`: given only
  that every row's two named ends are distinct
  (`∀ row, strong.start row ≠ strong.finish row`), `RowsMeetEndsOnly strong`
  holds outright.  The proof case-splits an occurrence `edge` of a row on
  whether it is the row's head and/or last entry:
  - head and last (a length-one row): its two incidences are `start row` and
    `finish row`, forced distinct by the hypothesis, and `Incident`'s
    two-endpoint shape (`eq_or_eq_of_incident_ne`, private) places any third
    incident vertex at one of them;
  - head only: `List.head?_eq_some_iff` exposes the row as `edge :: y :: ys`,
    `chain` (`List.isChain_cons_cons`) gives the valency-two vertex `m` where
    `edge` meets `y`, and `m ≠ strong.start row` by the valency mismatch, so
    the same two-endpoint argument places any valency-`≠ 2` incidence at
    `strong.start row`;
  - last only: symmetric, through `List.getLast?_eq_some_iff`,
    `List.eq_nil_or_concat'` and `List.isChain_append_cons_cons`;
  - interior (neither): §1's splitting lemma gives the list decomposition
    `A ++ a :: edge :: b :: B`, hence both meeting vertices `m₁` (with `a`)
    and `m₂` (with `b`), *and*, from the same decomposition, that `a`, `edge`,
    `b` are pairwise distinct (`Decomposes.nodup`, read off the suffix
    `a :: edge :: b :: B`).  If `m₁ = m₂`, three distinct surviving
    occurrences sit at one valency-two vertex, contradicting
    `nonDanglingIncident_eq_pair` (which pins the surviving incidence there to
    an unordered *pair*).  So `m₁ ≠ m₂`, both have valency two, and no vertex
    of valency `≠ 2` is incident to `edge` at all -- the goal holds vacuously.

* §3 **`RowsMeetEndsOnly` disappears as a hypothesis.**  `rowsMeetEndsOnly`
  discharges `rowsMeetEndsOnly_of_strong`'s one hypothesis from
  `ForestReceiptGeneral.start_ne_finish` (itself unconditional given a
  faithful core dictionary), and the four downstream headlines of
  `ForestReceiptGeneral` §3-§4 are restated here with the `RowsMeetEndsOnly`
  argument removed, each a one-line call into the theorem there, supplying
  `rowsMeetEndsOnly dict hFaithful` in its place:
  `isForest_sourceZeroSet_of_forest`, `sourceContractionTopology_of_forest`,
  `sourceContractionTopology_of_expansion`,
  `exists_subdivisionPencil_of_transport_of_expansion`.

## Hypotheses left explicit here

This file removes exactly one receipt (`RowsMeetEndsOnly`) from the chain
described in `ForestReceiptGeneral`'s "What is not proved here" section, and
touches none of the others.  Every corollary in §3 takes `dict` (a
`TraversalPresentation.CoreDictionary`), `hFaithful` and `hSpanning`
(`StrongRefinement.Faithful` and `StrongRefinement.Spanning` for it) as explicit
hypotheses; only `hRows` is removed.  The Euler count `N + p = Q + n` is not
implied by `ExpansionData.Conditions`;
`ForestReceiptGeneral.exists_expansionModel_isForest` supplies it
unconditionally for the datum of the stable-model reduction.

## Consumers

Same as `ForestReceiptGeneral` §4: `RetainedIndexProducer`'s producers and
`exists_subdivisionPencil_of_transport` take a `topology`, and this file's §3
theorems are direct, `RowsMeetEndsOnly`-free routes to it, which a caller can
use instead of supplying `RowsMeetEndsOnly strong` by hand.
-/

namespace DraismaVargas.LocalCases.RowsMeetEndsOnly

/-! ## 1.  A generic list-splitting lemma, and the `IsChain` transport across it -/

section ListSplitting

variable {α : Type*}

/-- **An interior list member splits its list into four pieces.**  If `edge`
occurs in `l` and is neither the head nor the last entry, it sits strictly
between two named neighbours: `l = A ++ a :: edge :: b :: B`.  (`edge` may
occur again inside `A`, `B` or as `a`/`b`; `List.append_of_mem` picks its
*first* occurrence, so this is the split at that occurrence -- the only one
this file needs, since it is fed straight into `List.IsChain`, which relates
consecutive list entries regardless of which occurrence is which.) -/
theorem exists_split_of_ne_head?_getLast? {l : List α} {edge : α}
    (hMem : edge ∈ l) (hHead : l.head? ≠ some edge) (hLast : l.getLast? ≠ some edge) :
    ∃ (A : List α) (a : α) (b : α) (B : List α), l = A ++ a :: edge :: b :: B := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hMem
  have hs : s ≠ [] := by
    rintro rfl
    exact hHead (by simp [hst])
  have ht : t ≠ [] := by
    rintro rfl
    exact hLast (by simp [hst])
  rcases List.eq_nil_or_concat' s with hs0 | ⟨A, a, hA⟩
  · exact absurd hs0 hs
  · cases t with
    | nil => exact absurd rfl ht
    | cons b B => exact ⟨A, a, b, B, by rw [hst, hA]; simp⟩

/-- **The chain relation transports across the splitting.**  If `l` is an
`R`-chain and `edge` is an interior occurrence (neither head nor last), `R`
relates `edge` to both of its list-neighbours at that occurrence. -/
theorem exists_rel_of_mem_of_ne_head?_getLast? {R : α → α → Prop} {l : List α} {edge : α}
    (hChain : l.IsChain R) (hMem : edge ∈ l)
    (hHead : l.head? ≠ some edge) (hLast : l.getLast? ≠ some edge) :
    ∃ a b : α, R a edge ∧ R edge b := by
  obtain ⟨A, a, b, B, hEq⟩ := exists_split_of_ne_head?_getLast? hMem hHead hLast
  rw [hEq, List.isChain_append_cons_cons] at hChain
  obtain ⟨-, hab, hChain2⟩ := hChain
  rw [List.isChain_cons_cons] at hChain2
  exact ⟨a, b, hab, hChain2.1⟩

end ListSplitting

/-! ## 2.  `RowsMeetEndsOnly`, discharged -/

section Discharge

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ForestReceiptGeneral
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.PresentationDecomposition
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.W4StableSource
open Utilities.Certificate.SubdivisionGraph

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}

/-- An edge with two named, distinct incident vertices has no third: `Incident`
tests membership in the *two* entries of `data.sourceEnds edge`, so two
distinct witnesses already exhaust them. -/
private theorem eq_or_eq_of_incident_ne
    {edge : candidate.datum.SourceEdge} {v1 v2 u : candidate.datum.SourceVertex}
    (h1 : Incident candidate.datum edge v1) (h2 : Incident candidate.datum edge v2)
    (hne : v1 ≠ v2) (hu : Incident candidate.datum edge u) : u = v1 ∨ u = v2 := by
  unfold Incident at h1 h2 hu
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.symm.trans h2) hne
  · rcases hu with hu | hu
    · exact Or.inl (hu.symm.trans h1)
    · exact Or.inr (hu.symm.trans h2)
  · rcases hu with hu | hu
    · exact Or.inr (hu.symm.trans h2)
    · exact Or.inl (hu.symm.trans h1)
  · exact absurd (h1.symm.trans h2) hne

/-- **The interior case, closed.**  Given only that every row's two named ends
are distinct, `RowsMeetEndsOnly strong` holds outright: this is
`ForestReceiptGeneral`'s §5 case split (head-and-last, head-only, last-only,
interior), with the interior case closed by §1's splitting lemma and the
three-distinct-occurrences contradiction against `nonDanglingIncident_eq_pair`. -/
theorem rowsMeetEndsOnly_of_strong
    {strong : StrongPresentation candidate.datum coordinate}
    (hStartFinish : ∀ row : coordinate, strong.start row ≠ strong.finish row) :
    RowsMeetEndsOnly strong := by
  classical
  intro row edge hedge u hinc hne
  by_cases hHead : (strong.toPresentation.path row).head? = some edge
  · by_cases hLast : (strong.toPresentation.path row).getLast? = some edge
    · -- a length-one row: `edge` sits at both named ends.
      have hS := strong.head_isPathEnd row edge hHead
      have hFi := strong.getLast_isPathEnd row edge hLast
      rcases eq_or_eq_of_incident_ne hS.1 hFi.1 (hStartFinish row) hinc with hEq | hEq
      · exact Or.inl ⟨hEq, hHead⟩
      · exact Or.inr ⟨hEq, hLast⟩
    · -- head only: `chain` names the valency-two vertex `edge` meets next.
      obtain ⟨ys, hEqT⟩ := List.head?_eq_some_iff.mp hHead
      cases ys with
      | nil => exact absurd (by rw [hEqT]; simp) hLast
      | cons y ys' =>
        have hChain := strong.chain row
        rw [hEqT, List.isChain_cons_cons] at hChain
        obtain ⟨hRel, -⟩ := hChain
        obtain ⟨m, hEm, -, hValm⟩ := hRel
        have hS := strong.head_isPathEnd row edge hHead
        have hune : u ≠ m := by
          intro h; apply hne; rw [h]; exact hValm
        have hSm : strong.start row ≠ m := by
          intro h; apply hS.2; rw [h]; exact hValm
        rcases eq_or_eq_of_incident_ne hS.1 hEm hSm hinc with hEq | hEq
        · exact Or.inl ⟨hEq, hHead⟩
        · exact absurd hEq hune
  · by_cases hLast : (strong.toPresentation.path row).getLast? = some edge
    · -- last only: symmetric, through the tail-end of the chain.
      obtain ⟨t, hEqT⟩ := List.getLast?_eq_some_iff.mp hLast
      rcases List.eq_nil_or_concat' t with ht0 | ⟨t', x, htx⟩
      · exact absurd (by rw [hEqT, ht0]; simp) hHead
      · have hChain := strong.chain row
        have hEqL : strong.toPresentation.path row = t' ++ x :: edge :: [] := by
          rw [hEqT, htx]; simp
        rw [hEqL, List.isChain_append_cons_cons] at hChain
        obtain ⟨-, hRel, -⟩ := hChain
        obtain ⟨m, -, hEm, hValm⟩ := hRel
        have hFi := strong.getLast_isPathEnd row edge hLast
        have hune : u ≠ m := by
          intro h; apply hne; rw [h]; exact hValm
        have hFm : strong.finish row ≠ m := by
          intro h; apply hFi.2; rw [h]; exact hValm
        rcases eq_or_eq_of_incident_ne hFi.1 hEm hFm hinc with hEq | hEq
        · exact Or.inr ⟨hEq, hLast⟩
        · exact absurd hEq hune
    · -- interior: §1's splitting lemma, then the three-distinct-edges
      -- contradiction against `nonDanglingIncident_eq_pair`.
      obtain ⟨A, a, b, B, hEq⟩ := exists_split_of_ne_head?_getLast? hedge hHead hLast
      have hChain := strong.chain row
      rw [hEq, List.isChain_append_cons_cons] at hChain
      obtain ⟨-, hRel1, hChain2⟩ := hChain
      rw [List.isChain_cons_cons] at hChain2
      obtain ⟨hRel2, -⟩ := hChain2
      obtain ⟨m1, hAm1, hEm1, hVal1⟩ := hRel1
      obtain ⟨m2, hEm2, hBm2, hVal2⟩ := hRel2
      have hNodup : (a :: edge :: b :: B).Nodup := by
        have hND := strong.decomposes.nodup row
        rw [hEq] at hND
        exact List.Nodup.of_append_right hND
      rw [List.nodup_cons] at hNodup
      have haNeEdge : a ≠ edge := by
        intro h; apply hNodup.1; rw [h]; exact List.mem_cons_self
      have haNeB : a ≠ b := by
        intro h; apply hNodup.1; rw [h]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      have hNodup2 := hNodup.2
      rw [List.nodup_cons] at hNodup2
      have hEdgeNeB : edge ≠ b := by
        intro h; apply hNodup2.1; rw [h]; exact List.mem_cons_self
      have haMemL : a ∈ strong.toPresentation.path row := by rw [hEq]; simp
      have hbMemL : b ∈ strong.toPresentation.path row := by rw [hEq]; simp
      by_cases hm : m1 = m2
      · subst hm
        obtain ⟨other, -, hSet⟩ :=
          nonDanglingIncident_eq_pair candidate.datum hVal1
            (strong.decomposes.not_isDangling_of_mem hedge) hEm1
        have haIn : a ∈ nonDanglingIncident candidate.datum m1 :=
          (mem_nonDanglingIncident candidate.datum m1 a).mpr
            ⟨strong.decomposes.not_isDangling_of_mem haMemL, hAm1⟩
        have hbIn : b ∈ nonDanglingIncident candidate.datum m1 :=
          (mem_nonDanglingIncident candidate.datum m1 b).mpr
            ⟨strong.decomposes.not_isDangling_of_mem hbMemL, hBm2⟩
        rw [hSet] at haIn hbIn
        have haEq : a = other := by
          rcases Finset.mem_insert.mp haIn with h | h
          · exact absurd h haNeEdge
          · exact Finset.mem_singleton.mp h
        have hbEq : b = other := by
          rcases Finset.mem_insert.mp hbIn with h | h
          · exact absurd h hEdgeNeB.symm
          · exact Finset.mem_singleton.mp h
        exact absurd (haEq.trans hbEq.symm) haNeB
      · have huneM1 : u ≠ m1 := by
          intro h; apply hne; rw [h]; exact hVal1
        have huneM2 : u ≠ m2 := by
          intro h; apply hne; rw [h]; exact hVal2
        rcases eq_or_eq_of_incident_ne hEm1 hEm2 hm hinc with hEqU | hEqU
        · exact absurd hEqU huneM1
        · exact absurd hEqU huneM2

/-- **`RowsMeetEndsOnly` disappears as a hypothesis.**  A faithful core
dictionary already supplies distinct row ends (`start_ne_finish`), so
`rowsMeetEndsOnly_of_strong` applies unconditionally. -/
theorem rowsMeetEndsOnly
    {strong : StrongPresentation candidate.datum coordinate}
    {iface : InputInterface spec strong.toPresentation coordinates F}
    (dict : CoreDictionary spec strong iface) (hFaithful : Faithful dict) :
    RowsMeetEndsOnly strong := by
  refine rowsMeetEndsOnly_of_strong (fun row ↦ ?_)
  have h := ForestReceiptGeneral.start_ne_finish dict hFaithful (iface.slot.symm row)
  rwa [Equiv.apply_symm_apply] at h

end Discharge

/-! ## 3.  The downstream headlines, restated without `RowsMeetEndsOnly` -/

section Producer

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.RetainedIndexProducer
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TraversalPresentation
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

variable {tgt : CFGraph.{0}} {degree : ℕ} {data : GluingDatum tgt degree}
  {wall : tgt.V} {candidate : Candidate tgt degree data wall}
  {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}

/-- **`ForestReceiptGeneral.isForest_sourceZeroSet_of_forest`, `RowsMeetEndsOnly`-free.** -/
theorem isForest_sourceZeroSet_of_forest
    (strong : StrongPresentation candidate.datum coordinate)
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (dict : CoreDictionary spec strong iface)
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hForest : IsForest spec.core F) :
    IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet :=
  ForestReceiptGeneral.isForest_sourceZeroSet_of_forest strong iface face dict hFaithful
    hSpanning (rowsMeetEndsOnly dict hFaithful) hForest

/-- **`ForestReceiptGeneral.sourceContractionTopology_of_forest`, `RowsMeetEndsOnly`-free.** -/
theorem sourceContractionTopology_of_forest
    (strong : StrongPresentation candidate.datum coordinate)
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (dict : CoreDictionary spec strong iface)
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hForest : IsForest spec.core F)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    ClearedFace.SourceContractionTopology face :=
  ForestReceiptGeneral.sourceContractionTopology_of_forest strong iface face dict hFaithful
    hSpanning (rowsMeetEndsOnly dict hFaithful) hForest hConnected hGenus

variable {chart : Type} {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}
  {N Q : ℕ} {D : ExpansionData n p N Q} {spec₀ : Spec n p}

/-- **`ForestReceiptGeneral.sourceContractionTopology_of_expansion`,
`RowsMeetEndsOnly`-free.** -/
theorem sourceContractionTopology_of_expansion
    (hCond : D.Conditions spec₀.core) (hEuler : N + p = Q + n)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot)
    (face : ClearedFace candidate strong.toPresentation state.currentFinish)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong
      (terminalExpandedModelInterface hN hL state strong hStrongMatrix slot hBase))
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    ClearedFace.SourceContractionTopology face :=
  ForestReceiptGeneral.sourceContractionTopology_of_expansion hCond hEuler hN hL state strong
    hStrongMatrix slot hBase face dict hFaithful hSpanning (rowsMeetEndsOnly dict hFaithful)
    hConnected hGenus

/-- **`ForestReceiptGeneral.exists_subdivisionPencil_of_transport_of_expansion`,
`RowsMeetEndsOnly`-free.** -/
theorem exists_subdivisionPencil_of_transport_of_expansion
    {n₁ p₁ : ℕ} {request : Spec n₁ p₁}
    (hbn : ∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
      BNExists (spec₀.scale k hk).graph r d ↔ BNExists (request.scale k hk).graph r d)
    (hCond : D.Conditions spec₀.core) (hEuler : N + p = Q + n)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot)
    (face : ClearedFace candidate strong.toPresentation state.currentFinish)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong
      (terminalExpandedModelInterface hN hL state strong hStrongMatrix slot hBase))
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hTargetConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hTargetGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses
      (sourceContractionTopology_of_expansion hCond hEuler hN hL state strong
        hStrongMatrix slot hBase face dict hFaithful hSpanning
        hTargetConnected hTargetGenus)).Nonempty)
    (relabeling : LaplacianEquiv
      (terminalRetainedRefinedSpec hCond hN hL state strong hStrongMatrix slot
        hBase face).graph
      (ClearedFace.SourceContractionTopology.prunedSpec
        (sourceContractionTopology_of_expansion hCond hEuler hN hL state strong
          hStrongMatrix slot hBase face dict hFaithful hSpanning
          hTargetConnected hTargetGenus) hKept).graph)
    (contracted : ClearedFace.ContractedGluing
      (sourceContractionTopology_of_expansion hCond hEuler hN hL state strong
        hStrongMatrix slot hBase face dict hFaithful hSpanning
        hTargetConnected hTargetGenus))
    (hSourceConnected : candidate.datum.Connected) :
    ∃ pencil : DraismaVargas.SubdivisionPencil request degree,
      pencil.scale = face.scale :=
  ForestReceiptGeneral.exists_subdivisionPencil_of_transport_of_expansion hbn hCond hEuler hN hL
    state strong hStrongMatrix slot hBase face dict hFaithful hSpanning
    (rowsMeetEndsOnly dict hFaithful) hTargetConnected hTargetGenus hKept relabeling contracted
    hSourceConnected

end Producer

end DraismaVargas.LocalCases.RowsMeetEndsOnly
