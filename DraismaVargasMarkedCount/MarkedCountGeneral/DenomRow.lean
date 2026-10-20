module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DenomRegrow
public import DraismaVargasCount.SharpRowDenominator

@[expose] public section

/-!
# The denominator step of the drop, part 2: the profile of a marked row

Part II's
`lemma-edge-deno` and `proposition-at-most-two-weights`, read on the **marked** rows of a typed
frame `φ` through its unmarked regrowth (module `DenomRegrow`). For a marked row `P` of `φ`:

* `index_dvd_rowDenominator`: every index occurring on `P` divides the row denominator `d(P)`
  (the simple columns of `SharpRowDenominator.index_dvd_rowDenominator`);
* `rowDenominator_dvd_of_forall`: `d(P)` divides every common multiple of the indices on `P`
  (`EdgeDenominator.rowDenominator_dvd_of_forall_index_dvd`);
* `exists_isJump`: if two indices on `P` differ, `P` has a **jump**: a non-mark vertex of
  surviving valency two where the two occurrences have different indices (the constancy of
  `RowWalk.sourceEdgeIndex_eq_of_rowUnramified`, with the local steps of `RowWalk`);
* `isJump_unique`: `P` has at most one jump (`RowWalk.rowAtMostOneTransition_of_simpleTarget`).

The jump is stated for any datum with marks (`IsJump`), so that it can be compared across the
drop.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.EdgeDenominator
open DraismaVargas.Count.RowWalk
open Utilities.Certificate.ExplicitPotential (Core)

/-- **A jump of the marked row `P`** at `Y`: `Y` is not a mark, has surviving valency two, and
the occurrence of `P` at `Y` and another occurrence at `Y` have different indices. (The other
occurrence is then on `P` too.) -/
def IsJump {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
    (marks : Finset data.SourceVertex) (P : MarkedStablePath data marks)
    (Y : data.SourceVertex) : Prop :=
  Y ∉ marks ∧ nonDanglingValency data Y = 2 ∧
    ∃ F G : NonDanglingEdge data, markedRow marks F = P ∧ Incident data F.1 Y ∧
      Incident data G.1 Y ∧ data.sourceEdgeIndex F.1 ≠ data.sourceEdgeIndex G.1

namespace DenomRegrow

open CatRegrow

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
variable (φ : TypedFrame core mark types degree) (hc : IsMarkedCubic core mark)

local notation "β" => branching φ

/-! ## 1.  The dictionary of the regrowth on a marked row -/

/-- The stable row of the regrowth of the marked row `P`. -/
noncomputable abbrev path (P : MarkedStablePath φ.data (markSet φ.markSource)) :
    StablePath (β).regrowDatum :=
  (β).tagPath (hψ φ) (hT φ) (hT0 φ) (hMark φ) (.inl P)

/-- The stable row of a marked row, through the labelling. -/
theorem labelling_row_symm (P : MarkedStablePath φ.data (markSet φ.markSource)) :
    (labelling φ).row.symm (.inl (φ.fullDim.labelling.row P)) = path φ P := by
  rw [labelling_row_symm_inl, Equiv.symm_apply_apply]

/-- An old occurrence lies on the regrown row of its marked row. -/
theorem onRow_psiSE (F : NonDanglingEdge φ.data) :
    OnRow (β).regrowDatum (path φ (markedRow (markSet φ.markSource) F)) ((β).psiSE F.1) :=
  ⟨((β).oldND (hψ φ) (hT φ) (hT0 φ) (hMark φ) F).2, rfl⟩

/-- Every occurrence of a regrown marked row is old, from that marked row. -/
theorem exists_of_onRow {P : MarkedStablePath φ.data (markSet φ.markSource)}
    {E : (β).regrowDatum.SourceEdge} (h : OnRow (β).regrowDatum (path φ P) E) :
    ∃ F : NonDanglingEdge φ.data, E = (β).psiSE F.1 ∧ markedRow (markSet φ.markSource) F = P := by
  obtain ⟨hS, hP⟩ := h
  rcases (β).nonDanglingEdge_cases (hψ φ) (hT φ) (hT0 φ) (hMark φ) ⟨E, hS⟩ with
    ⟨F, hF⟩ | ⟨t, q, hq, hF⟩
  · refine ⟨F, congrArg Subtype.val hF, ?_⟩
    rw [hF, (β).stablePath_eq_tagPath_iff, (β).rowTag_oldND] at hP
    exact Sum.inl_injective hP
  · rw [hF, (β).stablePath_eq_tagPath_iff, (β).rowTag_tailND] at hP
    exact absurd hP Sum.inr_ne_inl

/-- A vertex of the regrowth at an old occurrence is old. -/
theorem exists_of_incident {F : φ.data.SourceEdge} {X : (β).regrowDatum.SourceVertex}
    (h : Incident (β).regrowDatum ((β).psiSE F) X) :
    ∃ Y : φ.data.SourceVertex, X = (β).psiSV Y ∧ Incident φ.data F Y := by
  rcases (β).sourceVertex_cases X with ⟨Y, rfl⟩ | ⟨v, nn, rfl⟩ | ⟨w, q, rfl⟩
  · exact ⟨Y, rfl, ((β).incident_psiSE_psiSV F Y).mp h⟩
  · exact absurd h ((β).incident_psiSE_newSV F v nn)
  · exact absurd h ((β).incident_psiSE_tailSV F w q)

/-- Membership in the row set of the regrowth's labelling. -/
theorem psiSE_mem_rowEdges (F : NonDanglingEdge φ.data) :
    (β).psiSE F.1 ∈ rowEdges (labelling φ)
      (.inl (φ.fullDim.labelling.row (markedRow (markSet φ.markSource) F))) := by
  rw [mem_rowEdges_iff_onRow, labelling_row_symm]
  exact onRow_psiSE φ F

/-- **The row denominators agree**: the regrowth's matrix is block diagonal. -/
theorem rowDenominator_inl (i : Fin p) :
    Count.rowDenominator (labelling φ).presentation (.inl i) =
      Count.rowDenominator φ.fullDim.labelling.presentation i := by
  unfold Count.rowDenominator
  rw [matrix_labelling]
  apply Nat.dvd_antisymm
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun w _ ↦ ?_
    rcases w with i' | t
    · change (φ.matrix i i').den ∣ _
      exact den_dvd_commonDenominator _ _ (Finset.mem_univ i')
    · change ((0 : Matrix _ _ ℚ) i t).den ∣ _
      simp
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun i' _ ↦ ?_
    exact den_dvd_commonDenominator _ (blockMatrix φ (.inl i)) (Finset.mem_univ (.inl i'))

/-! ## 2.  The two divisibilities -/

include hc in
/-- **Every index on a marked row divides its denominator** (`lemma-edge-deno`, sharp form). -/
theorem index_dvd_rowDenominator (F : NonDanglingEdge φ.data) :
    φ.data.sourceEdgeIndex F.1 ∣ Count.rowDenominator φ.fullDim.labelling.presentation
      (φ.fullDim.labelling.row (markedRow (markSet φ.markSource) F)) := by
  rw [← rowDenominator_inl, ← (β).sourceEdgeIndex_psiSE]
  exact SharpRowDenominator.index_dvd_rowDenominator (fullDim φ hc) (psiSE_mem_rowEdges φ F)

/-- **The denominator of a marked row divides every common multiple of its indices.** -/
theorem rowDenominator_dvd_of_forall (P : MarkedStablePath φ.data (markSet φ.markSource))
    {N : ℕ} (h : ∀ F : NonDanglingEdge φ.data, markedRow (markSet φ.markSource) F = P →
      φ.data.sourceEdgeIndex F.1 ∣ N) :
    Count.rowDenominator φ.fullDim.labelling.presentation (φ.fullDim.labelling.row P) ∣ N := by
  rw [← rowDenominator_inl]
  refine rowDenominator_dvd_of_forall_index_dvd (labelling φ) _ fun e he ↦ ?_
  rw [mem_rowEdges_iff_onRow, labelling_row_symm] at he
  obtain ⟨F, rfl, hF⟩ := exists_of_onRow φ he
  rw [(β).sourceEdgeIndex_psiSE]
  exact h F hF

/-! ## 3.  Jumps -/

include hc in
/-- A row carrying an index other than one avoids the leaves of the regrowth. -/
theorem rowAvoidsLeaves_of_index_ne_one {F : NonDanglingEdge φ.data}
    (hF : φ.data.sourceEdgeIndex F.1 ≠ 1) :
    RowAvoidsLeaves (β).regrowDatum (path φ (markedRow (markSet φ.markSource) F)) := by
  rw [← labelling_row_symm]
  refine (rowAvoidsLeaves_iff_not_passesAboveLeaf (labelling φ) _).mpr ?_
  refine not_passesAboveLeaf_of_index_ne_one (fullDim φ hc) (psiSE_mem_rowEdges φ F) ?_
  rwa [(β).sourceEdgeIndex_psiSE]

/-- Two occurrences at a non-mark vertex of surviving valency two lie on one marked row. -/
theorem markedRow_eq_of_incident {Y : φ.data.SourceVertex} (hY : Y ∉ markSet φ.markSource)
    (hY2 : nonDanglingValency φ.data Y = 2) {F G : NonDanglingEdge φ.data}
    (hF : Incident φ.data F.1 Y) (hG : Incident φ.data G.1 Y) :
    markedRow (markSet φ.markSource) F = markedRow (markSet φ.markSource) G := by
  by_cases h : F = G
  · rw [h]
  · exact markedRow_eq_of_markedConsecutive ⟨h, Y, hF, hG, hY2, hY⟩

include hc in
/-- **A jump is a transition of the regrown row.** -/
theorem isRowTransition_of_isJump {P : MarkedStablePath φ.data (markSet φ.markSource)}
    {Y : φ.data.SourceVertex} (hJ : IsJump φ.data (markSet φ.markSource) P Y) :
    IsRowTransition (β).regrowDatum (path φ P) ((β).psiSV Y) := by
  obtain ⟨hYm, hY2, F, G, rfl, hF, hG, hne⟩ := hJ
  have hX2 : nonDanglingValency (β).regrowDatum ((β).psiSV Y) = 2 :=
    ((β).nonDanglingValency_psiSV_eq_two_iff (hψ φ) (hT φ) (hT0 φ) (hMark φ) Y).mpr ⟨hY2, hYm⟩
  have hFI : Incident (β).regrowDatum ((β).psiSE F.1) ((β).psiSV Y) :=
    ((β).incident_psiSE_psiSV _ _).mpr hF
  have hGI : Incident (β).regrowDatum ((β).psiSE G.1) ((β).psiSV Y) :=
    ((β).incident_psiSE_psiSV _ _).mpr hG
  have hFG := markedRow_eq_of_incident φ hYm hY2 hF hG
  -- the row avoids leaves
  have hAvoid : RowAvoidsLeaves (β).regrowDatum (path φ (markedRow (markSet φ.markSource) F)) := by
    by_cases h1 : φ.data.sourceEdgeIndex F.1 = 1
    · have h1' : φ.data.sourceEdgeIndex G.1 ≠ 1 := fun h ↦ hne (h1.trans h.symm)
      rw [hFG]
      exact rowAvoidsLeaves_of_index_ne_one φ hc h1'
    · exact rowAvoidsLeaves_of_index_ne_one φ hc h1
  refine ⟨hX2, ?_, (β).psiSE F.1, onRow_psiSE φ F, hFI⟩
  rcases rowRamificationAtMostOne_of_rowAvoidsLeaves (fullDim φ hc) hAvoid _ _ (onRow_psiSE φ F)
    hFI hX2 with h0 | h1
  · exfalso
    have hEq := sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue
      (fullDim φ hc).danglingEdgeNoGlue hX2 h0 ((β).oldND (hψ φ) (hT φ) (hT0 φ) (hMark φ) F).2
      hFI ((β).oldND (hψ φ) (hT φ) (hT0 φ) (hMark φ) G).2 hGI
    have hEq' : (β).regrowDatum.sourceEdgeIndex ((β).psiSE F.1) =
        (β).regrowDatum.sourceEdgeIndex ((β).psiSE G.1) := hEq
    rw [(β).sourceEdgeIndex_psiSE, (β).sourceEdgeIndex_psiSE] at hEq'
    exact hne hEq'
  · exact h1

include hc in
/-- **At most one jump on a marked row** (`proposition-at-most-two-weights`: one transition). -/
theorem isJump_unique {P : MarkedStablePath φ.data (markSet φ.markSource)}
    {Y₁ Y₂ : φ.data.SourceVertex} (h₁ : IsJump φ.data (markSet φ.markSource) P Y₁)
    (h₂ : IsJump φ.data (markSet φ.markSource) P Y₂) : Y₁ = Y₂ := by
  have hT₁ := isRowTransition_of_isJump φ hc h₁
  have hT₂ := isRowTransition_of_isJump φ hc h₂
  obtain ⟨hYm, hY2, F, G, rfl, hF, hG, hne⟩ := h₁
  have hFG := markedRow_eq_of_incident φ hYm hY2 hF hG
  have hAvoid : RowAvoidsLeaves (β).regrowDatum (path φ (markedRow (markSet φ.markSource) F)) := by
    by_cases h1 : φ.data.sourceEdgeIndex F.1 = 1
    · have h1' : φ.data.sourceEdgeIndex G.1 ≠ 1 := fun h ↦ hne (h1.trans h.symm)
      rw [hFG]
      exact rowAvoidsLeaves_of_index_ne_one φ hc h1'
    · exact rowAvoidsLeaves_of_index_ne_one φ hc h1
  exact (β).psiSV_injective (rowAtMostOneTransition_of_simpleTarget (fullDim φ hc)
    (OutgoingRowCalculus.simpleTarget_of_fullDim (fullDim φ hc)) hAvoid _ _ hT₁ hT₂)

include hc in
/-- **Two different indices on a marked row force a jump.** -/
theorem exists_isJump {P : MarkedStablePath φ.data (markSet φ.markSource)}
    {F₁ F₂ : NonDanglingEdge φ.data} (h₁ : markedRow (markSet φ.markSource) F₁ = P)
    (h₂ : markedRow (markSet φ.markSource) F₂ = P)
    (hne : φ.data.sourceEdgeIndex F₁.1 ≠ φ.data.sourceEdgeIndex F₂.1) :
    ∃ Y, IsJump φ.data (markSet φ.markSource) P Y := by
  by_contra hNo
  push Not at hNo
  subst h₁
  have hAvoid : RowAvoidsLeaves (β).regrowDatum (path φ (markedRow (markSet φ.markSource) F₁)) := by
    by_cases h1 : φ.data.sourceEdgeIndex F₁.1 = 1
    · have h1' : φ.data.sourceEdgeIndex F₂.1 ≠ 1 := fun h ↦ hne (h1.trans h.symm)
      rw [← h₂]
      exact rowAvoidsLeaves_of_index_ne_one φ hc h1'
    · exact rowAvoidsLeaves_of_index_ne_one φ hc h1
  have hTame := rowRamificationAtMostOne_of_rowAvoidsLeaves (fullDim φ hc) hAvoid
  have hUnram : RowUnramified (β).regrowDatum (path φ (markedRow (markSet φ.markSource) F₁)) := by
    intro X e he hXe hX2
    rcases hTame X e he hXe hX2 with h0 | h1
    · exact h0
    · exfalso
      obtain ⟨a, b, hab, haS, haI, hbS, hbI⟩ := exists_pair_of_nonDanglingValency_two hX2
      have ha := onRow_of_incident hX2 he hXe haS haI
      have hIdx := sourceEdgeIndex_sub_eq_one_of_transition_of_noGlue
        (fullDim φ hc).danglingEdgeNoGlue hX2 h1 haS haI hbS hbI hab
      obtain ⟨Fa, rfl, hFa⟩ := exists_of_onRow φ ha
      have hb := onRow_of_incident hX2 he hXe hbS hbI
      obtain ⟨Fb, rfl, -⟩ := exists_of_onRow φ hb
      obtain ⟨Y, rfl, hYa⟩ := exists_of_incident φ haI
      have hYb : Incident φ.data Fb.1 Y := ((β).incident_psiSE_psiSV _ _).mp hbI
      obtain ⟨hY2, hYm⟩ :=
        ((β).nonDanglingValency_psiSV_eq_two_iff (hψ φ) (hT φ) (hT0 φ) (hMark φ) Y).mp hX2
      rw [(β).sourceEdgeIndex_psiSE, (β).sourceEdgeIndex_psiSE] at hIdx
      exact hNo Y ⟨hYm, hY2, Fa, Fb, hFa, hYa, hYb, by omega⟩
  have hEq := sourceEdgeIndex_eq_of_rowUnramified (fullDim φ hc).danglingEdgeNoGlue
    (fullDim φ hc).pathEnds hUnram (onRow_psiSE φ F₁) (h₂ ▸ onRow_psiSE φ F₂)
  rw [(β).sourceEdgeIndex_psiSE, (β).sourceEdgeIndex_psiSE] at hEq
  exact hne hEq

end DenomRegrow

end DraismaVargas.Count.MarkedCountGeneral
