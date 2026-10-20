module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropContract

@[expose] public section

/-!
# The drop lemma: marked rows, incidences and the matrix under the contraction

Continues
module `DropContract`: a contraction site `S` (a divalent change-zero vertex `x` and an edge `c` at
it) with marks `M` containing one mark `V` over `x` (`Site.MarkHyp`).

* **marked rows** (`Site.rowMap`): the row map `MarkedStablePath data M → MarkedStablePath S.D
  M'` is surjective and identifies exactly the two rows through `V`
  (`rowMap_eq_iff`, `RowRel`);
* **incidences** add over its fibres (`markedIncidenceCount_rowMap`, `_of_ne`, `_fc`), and the
  marked branch vertices of the contraction are those of the datum other than `V`
  (`branchEquiv`);
* **the matrix**: a contracted entry is the sum over the fibre (`markedMatrix_rowMap`, `_of_ne`,
  `_fc`), and the columns `c`, `other` agree except at the two occurrences through `V`
  (`markedMatrix_c_add`);
* **the local data**: `markIndex` and `markRamification` away from `x`, and the leaves of the target,
  are unchanged (`markIndex_vmap`, `markRamification_vmap`, `leafCount_contract`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount

namespace DivalentContraction

section Contraction

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-! ## 3.  Marked rows -/

namespace Site

variable (S : Site data) (M : Finset data.SourceVertex) (V : data.SourceVertex)

/-- **The marks of the contracted datum**: the images of the marks other than `V` (one choice of
the marks `M'` below). -/
noncomputable def marksD : Finset S.D.SourceVertex := (M.erase V).image S.vmap

/-- The marked setting: `V` is a mark over `x` of surviving valency two, no other mark lies over
`x`, and the marks `M'` of the contraction are the images of the others. -/
structure MarkHyp (M' : Finset S.D.SourceVertex) : Prop where
  mem : V ∈ M
  onX : V.1.1 = S.x
  only : ∀ Z ∈ M, Z.1.1 = S.x → Z = V
  valency : nonDanglingValency data V = 2
  marks : ∀ Y : data.SourceVertex, Y.1.1 ≠ S.x → (S.vmap Y ∈ M' ↔ Y ∈ M)

variable {S M V} {M' : Finset S.D.SourceVertex}

/-- `marksD` satisfies the last clause. -/
theorem mem_marksD (hOnly : ∀ Z ∈ M, Z.1.1 = S.x → Z = V) (hV : V.1.1 = S.x)
    {Y : data.SourceVertex} (hY : Y.1.1 ≠ S.x) :
    S.vmap Y ∈ S.marksD M V ↔ Y ∈ M := by
  unfold marksD
  constructor
  · intro h
    obtain ⟨Z, hZ, hZY⟩ := Finset.mem_image.mp h
    obtain ⟨hZV, hZM⟩ := Finset.mem_erase.mp hZ
    have hZx : Z.1.1 ≠ S.x := fun hZx ↦ hZV (hOnly Z hZM hZx)
    rwa [← (S.vmap_inj hZx hY).mp hZY]
  · intro h
    exact Finset.mem_image.mpr ⟨Y, Finset.mem_erase.mpr ⟨fun hYV ↦ hY (hYV ▸ hV), h⟩, rfl⟩

/-- The two surviving occurrences at `V`. -/
theorem nd_c_V (hM : S.MarkHyp M V M') : ¬ IsDangling data (data.sourceEdge S.c V.1.2) := by
  intro hD
  have h := hM.valency
  rw [← card_nonDanglingIncident] at h
  have hSub : nonDanglingIncident data V ⊆ {data.sourceEdge S.other V.1.2} := by
    intro g hg
    obtain ⟨hNd, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hg
    rcases (S.incident_x_iff V hM.onX g).mp hInc with rfl | rfl
    · exact absurd hD hNd
    · exact Finset.mem_singleton_self _
  have := Finset.card_le_card hSub
  rw [h, Finset.card_singleton] at this
  omega

/-- The occurrence over the other edge at `V` survives. -/
theorem nd_other_V (hM : S.MarkHyp M V M') : ¬ IsDangling data (data.sourceEdge S.other V.1.2) := by
  rw [← S.partner_sourceEdge_c, S.isDangling_partner_iff rfl]
  exact S.nd_c_V hM

/-- The occurrence over `c` at `V`. -/
noncomputable def fc (hM : S.MarkHyp M V M') : NonDanglingEdge data :=
  ⟨data.sourceEdge S.c V.1.2, S.nd_c_V hM⟩

/-- The occurrence over the other edge at `V`. -/
noncomputable def fo (hM : S.MarkHyp M V M') : NonDanglingEdge data :=
  ⟨data.sourceEdge S.other V.1.2, S.nd_other_V hM⟩

/-- The occurrence over `c` at `V` meets `V`. -/
theorem incident_fc (hM : S.MarkHyp M V M') : Incident data (S.fc hM).1 V :=
  (S.incident_x_iff V hM.onX _).mpr (Or.inl rfl)

/-- The occurrence over the other edge at `V` meets `V`. -/
theorem incident_fo (hM : S.MarkHyp M V M') : Incident data (S.fo hM).1 V :=
  (S.incident_x_iff V hM.onX _).mpr (Or.inr rfl)

/-- **Marked consecutiveness is carried forwards** (or the two occurrences merge, at a source
vertex over `x` other than `V`). -/
theorem markedConsecutive_ndMap (hM : S.MarkHyp M V M') {e f : NonDanglingEdge data}
    (h : MarkedConsecutive data M e f) :
    S.ndMap e = S.ndMap f ∨ MarkedConsecutive S.D M' (S.ndMap e) (S.ndMap f) := by
  obtain ⟨hne, Y, he, hf, hY2, hYM⟩ := h
  by_cases hYx : Y.1.1 = S.x
  · left
    exact Subtype.ext (S.edgeMap_eq_of_incident_x hYx he hf)
  · right
    refine ⟨fun h ↦ hne (Subtype.ext (S.edgeMap_injOn hYx he hf (congrArg Subtype.val h))),
      S.vmap Y, S.incident_edgeMap hYx he, S.incident_edgeMap hYx hf, ?_, ?_⟩
    · rw [S.nonDanglingValency_vmap hYx]; exact hY2
    · rw [hM.marks Y hYx]; exact hYM

/-- **The row map** `ρ`: a marked row goes to the contracted row of its occurrences. -/
noncomputable def rowMap (hM : S.MarkHyp M V M') :
    MarkedStablePath data M → MarkedStablePath S.D M' :=
  Quot.lift (fun e ↦ markedRow M' (S.ndMap e)) fun _ _ h ↦ by
    rcases S.markedConsecutive_ndMap hM h with h' | h'
    · rw [h']
    · exact markedRow_eq_of_markedConsecutive h'

/-- The row map on a representative. -/
theorem rowMap_markedRow (hM : S.MarkHyp M V M') (e : NonDanglingEdge data) :
    S.rowMap hM (markedRow M e) = markedRow M' (S.ndMap e) := rfl

/-- Every row of the contraction comes from a row. -/
theorem rowMap_surjective (hM : S.MarkHyp M V M') : Function.Surjective (S.rowMap hM) := by
  intro r
  induction r using Quot.ind with
  | mk g =>
    obtain ⟨e, rfl⟩ := S.ndMap_surjective g
    exact ⟨markedRow M e, rfl⟩

/-- The two rows at `V`. -/
def RowRel (hM : S.MarkHyp M V M') (r₁ r₂ : MarkedStablePath data M) : Prop :=
  r₁ = r₂ ∨ ((r₁ = markedRow M (S.fc hM) ∨ r₁ = markedRow M (S.fo hM)) ∧
    (r₂ = markedRow M (S.fc hM) ∨ r₂ = markedRow M (S.fo hM)))

/-- `RowRel` is symmetric. -/
theorem RowRel.symm' {hM : S.MarkHyp M V M'} {r₁ r₂ : MarkedStablePath data M}
    (h : S.RowRel hM r₁ r₂) : S.RowRel hM r₂ r₁ := by
  rcases h with h | ⟨h₁, h₂⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨h₂, h₁⟩

/-- `RowRel` is transitive. -/
theorem RowRel.trans' {hM : S.MarkHyp M V M'} {r₁ r₂ r₃ : MarkedStablePath data M}
    (h₁₂ : S.RowRel hM r₁ r₂) (h₂₃ : S.RowRel hM r₂ r₃) : S.RowRel hM r₁ r₃ := by
  rcases h₁₂ with rfl | ⟨h₁, h₂⟩
  · exact h₂₃
  · rcases h₂₃ with rfl | ⟨-, h₃⟩
    · exact Or.inr ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₁, h₃⟩

/-- Occurrences with the same image lie on related rows. -/
theorem rowRel_of_ndMap_eq (hM : S.MarkHyp M V M') {e f : NonDanglingEdge data}
    (h : S.ndMap e = S.ndMap f) : S.RowRel hM (markedRow M e) (markedRow M f) := by
  rcases S.edgeMap_eq_imp (congrArg Subtype.val h) with h' | ⟨X, hX, he, hf⟩
  · exact Or.inl (by rw [Subtype.ext h'])
  · by_cases hXV : X = V
    · subst hXV
      right
      constructor
      · rcases (S.incident_x_iff X hX e.1).mp he with h₁ | h₁
        · exact Or.inl (by rw [show e = S.fc hM from Subtype.ext h₁])
        · exact Or.inr (by rw [show e = S.fo hM from Subtype.ext h₁])
      · rcases (S.incident_x_iff X hX f.1).mp hf with h₁ | h₁
        · exact Or.inl (by rw [show f = S.fc hM from Subtype.ext h₁])
        · exact Or.inr (by rw [show f = S.fo hM from Subtype.ext h₁])
    · by_cases hef : e = f
      · exact Or.inl (by rw [hef])
      · left
        refine markedRow_eq_of_markedConsecutive ⟨hef, X, he, hf, ?_, ?_⟩
        · exact S.nonDanglingValency_eq_two_of_ne hX hef he hf
        · exact fun hXM ↦ hXV (hM.only X hXM hX)

/-- **The fibres of the row map**: it identifies exactly the two rows at `V`. -/
theorem rowMap_eq_iff (hM : S.MarkHyp M V M') (r₁ r₂ : MarkedStablePath data M) :
    S.rowMap hM r₁ = S.rowMap hM r₂ ↔ S.RowRel hM r₁ r₂ := by
  constructor
  · intro h
    induction r₁ using Quot.ind with
    | mk e₁ =>
      induction r₂ using Quot.ind with
      | mk e₂ =>
        -- the relation, read on contracted occurrences
        let P : NonDanglingEdge S.D → NonDanglingEdge S.D → Prop := fun g₁ g₂ ↦
          ∀ f₁ f₂ : NonDanglingEdge data, S.ndMap f₁ = g₁ → S.ndMap f₂ = g₂ →
            S.RowRel hM (markedRow M f₁) (markedRow M f₂)
        have hGen : ∀ g₁ g₂, Relation.EqvGen (MarkedConsecutive S.D M') g₁ g₂ →
            P g₁ g₂ := by
          intro g₁ g₂ hg
          induction hg with
          | rel g₁ g₂ hc =>
            intro f₁ f₂ hf₁ hf₂
            obtain ⟨hne, Y', hg₁, hg₂, hY2, hYM⟩ := hc
            obtain ⟨Y, hYx, rfl⟩ := S.exists_vmap_eq Y'
            obtain ⟨e₁', he₁', hE₁⟩ := S.exists_incident_edgeMap hYx hg₁
            obtain ⟨e₂', he₂', hE₂⟩ := S.exists_incident_edgeMap hYx hg₂
            let n₁ : NonDanglingEdge data :=
              ⟨e₁', (S.isDangling_edgeMap_iff e₁').not.mp (hE₁ ▸ g₁.2)⟩
            let n₂ : NonDanglingEdge data :=
              ⟨e₂', (S.isDangling_edgeMap_iff e₂').not.mp (hE₂ ▸ g₂.2)⟩
            have hn₁ : S.ndMap n₁ = g₁ := Subtype.ext hE₁
            have hn₂ : S.ndMap n₂ = g₂ := Subtype.ext hE₂
            have hSame : markedRow M n₁ = markedRow M n₂ := by
              refine markedRow_eq_of_markedConsecutive ⟨fun h ↦ hne ?_, Y, he₁', he₂', ?_, ?_⟩
              · rw [← hn₁, ← hn₂, h]
              · rw [← S.nonDanglingValency_vmap hYx]; exact hY2
              · rw [← hM.marks Y hYx]; exact hYM
            have h₁ := S.rowRel_of_ndMap_eq hM (hf₁.trans hn₁.symm)
            have h₂ := S.rowRel_of_ndMap_eq hM (hn₂.trans hf₂.symm)
            rw [hSame] at h₁
            exact h₁.trans' h₂
          | refl g =>
            intro f₁ f₂ hf₁ hf₂
            exact S.rowRel_of_ndMap_eq hM (hf₁.trans hf₂.symm)
          | symm g₁ g₂ _ ih =>
            intro f₁ f₂ hf₁ hf₂
            exact (ih f₂ f₁ hf₂ hf₁).symm'
          | trans g₁ g₂ g₃ _ _ ih₁ ih₂ =>
            intro f₁ f₃ hf₁ hf₃
            obtain ⟨f₂, hf₂⟩ := S.ndMap_surjective g₂
            exact (ih₁ f₁ f₂ hf₁ hf₂).trans' (ih₂ f₂ f₃ hf₂ hf₃)
        exact hGen _ _ (Quot.eqvGen_exact h) e₁ e₂ rfl rfl
  · rintro (rfl | ⟨h₁, h₂⟩)
    · rfl
    · have hV : S.rowMap hM (markedRow M (S.fc hM)) = S.rowMap hM (markedRow M (S.fo hM)) := by
        rw [S.rowMap_markedRow, S.rowMap_markedRow]
        congr 1
        exact Subtype.ext (S.edgeMap_eq_of_incident_x hM.onX (S.incident_fc hM) (S.incident_fo hM))
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · rfl
      · exact hV
      · exact hV.symm
      · rfl

/-! ### Incidences -/

open Classical in
/-- **Incidence counts add over the fibres of the row map**, at the image of a source vertex away
from `x`. -/
theorem markedIncidenceCount_rowMap (hM : S.MarkHyp M V M') {A : data.SourceVertex}
    (hA : A.1.1 ≠ S.x) (r : MarkedStablePath data M) :
    markedIncidenceCount S.D M' (S.vmap A) (S.rowMap hM r) =
      ((StablePathCount.incidentEdges data A).filter fun e ↦
        S.RowRel hM (markedRow M e) r).card := by
  classical
  unfold markedIncidenceCount
  symm
  refine Finset.card_bij (fun e _ ↦ S.ndMap e) ?_ ?_ ?_
  · intro e he
    obtain ⟨hInc, hRel⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [StablePathCount.mem_incidentEdges] at hInc ⊢
      exact S.incident_edgeMap hA hInc
    · rw [← S.rowMap_markedRow]
      exact (S.rowMap_eq_iff hM _ _).mpr hRel
  · intro e he f hf h
    have he' := (StablePathCount.mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp he).1
    have hf' := (StablePathCount.mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hf).1
    exact Subtype.ext (S.edgeMap_injOn hA he' hf' (congrArg Subtype.val h))
  · intro g hg
    obtain ⟨hInc, hRow⟩ := Finset.mem_filter.mp hg
    rw [StablePathCount.mem_incidentEdges] at hInc
    obtain ⟨e, he, hE⟩ := S.exists_incident_edgeMap hA hInc
    let n : NonDanglingEdge data := ⟨e, (S.isDangling_edgeMap_iff e).not.mp (hE ▸ g.2)⟩
    have hn : S.ndMap n = g := Subtype.ext hE
    refine ⟨n, Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr he, ?_⟩, hn⟩
    refine (S.rowMap_eq_iff hM _ _).mp ?_
    rw [S.rowMap_markedRow, hn]
    exact hRow

/-- Away from the two rows at `V`, incidence counts are unchanged. -/
theorem markedIncidenceCount_rowMap_of_ne (hM : S.MarkHyp M V M') {A : data.SourceVertex}
    (hA : A.1.1 ≠ S.x) {r : MarkedStablePath data M} (hc : r ≠ markedRow M (S.fc hM))
    (ho : r ≠ markedRow M (S.fo hM)) :
    markedIncidenceCount S.D M' (S.vmap A) (S.rowMap hM r) =
      markedIncidenceCount data M A r := by
  classical
  rw [S.markedIncidenceCount_rowMap hM hA]
  unfold markedIncidenceCount
  congr 1
  refine Finset.filter_congr fun e _ ↦ ?_
  constructor
  · rintro (h | ⟨-, h | h⟩)
    · exact h
    · exact absurd h hc
    · exact absurd h ho
  · exact Or.inl

/-- At the two rows through `V`, incidence counts add. -/
theorem markedIncidenceCount_rowMap_fc (hM : S.MarkHyp M V M') {A : data.SourceVertex}
    (hA : A.1.1 ≠ S.x) (hne : markedRow M (S.fc hM) ≠ markedRow M (S.fo hM)) :
    markedIncidenceCount S.D M' (S.vmap A) (S.rowMap hM (markedRow M (S.fc hM))) =
      markedIncidenceCount data M A (markedRow M (S.fc hM)) +
        markedIncidenceCount data M A (markedRow M (S.fo hM)) := by
  classical
  rw [S.markedIncidenceCount_rowMap hM hA]
  unfold markedIncidenceCount
  have hSet : ((StablePathCount.incidentEdges data A).filter fun e ↦
      S.RowRel hM (markedRow M e) (markedRow M (S.fc hM))) =
      ((StablePathCount.incidentEdges data A).filter fun e ↦
        markedRow M e = markedRow M (S.fc hM)) ∪
      ((StablePathCount.incidentEdges data A).filter fun e ↦
        markedRow M e = markedRow M (S.fo hM)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_union, RowRel]
    constructor
    · rintro ⟨he, h | ⟨h, -⟩⟩
      · exact Or.inl ⟨he, h⟩
      · rcases h with h | h
        · exact Or.inl ⟨he, h⟩
        · exact Or.inr ⟨he, h⟩
    · rintro (⟨he, h⟩ | ⟨he, h⟩)
      · exact ⟨he, Or.inl h⟩
      · exact ⟨he, Or.inr ⟨Or.inr h, by simp⟩⟩
  rw [hSet, Finset.card_union_of_disjoint]
  · rw [Finset.disjoint_filter]
    intro e _ h₁ h₂
    exact hne (h₁.symm.trans h₂)

/-! ### Marked branch vertices -/

/-- A marked branch vertex other than `V` is not over `x`. -/
theorem not_over_x (hM : S.MarkHyp M V M') (B : MarkedBranchVertex data M) (hB : B.1 ≠ V) :
    B.1.1.1 ≠ S.x := by
  intro hx
  rcases B.2 with h | h
  · have := S.nonDanglingValency_le_two hx; omega
  · exact hB (hM.only _ h hx)

/-- The image of a marked branch vertex other than `V`. -/
noncomputable def branchMap (hM : S.MarkHyp M V M') (B : {B : MarkedBranchVertex data M // B.1 ≠ V}) :
    MarkedBranchVertex S.D M' :=
  ⟨S.vmap B.1.1, by
    rcases B.1.2 with h | h
    · left; rw [S.nonDanglingValency_vmap (S.not_over_x hM B.1 B.2)]; exact h
    · right; rw [hM.marks _ (S.not_over_x hM B.1 B.2)]; exact h⟩

/-- The branch map is a bijection. -/
theorem branchMap_bijective (hM : S.MarkHyp M V M') : Function.Bijective (S.branchMap hM) := by
  constructor
  · intro B₁ B₂ h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext ((S.vmap_inj (S.not_over_x hM B₁.1 B₁.2)
      (S.not_over_x hM B₂.1 B₂.2)).mp h'))
  · intro B'
    obtain ⟨Y, hYx, hY⟩ := S.exists_vmap_eq B'.1
    have hBr : 3 ≤ nonDanglingValency data Y ∨ Y ∈ M := by
      rcases B'.2 with h | h
      · left; rw [← S.nonDanglingValency_vmap hYx, hY]; exact h
      · right; rw [← hM.marks Y hYx, hY]; exact h
    exact ⟨⟨⟨Y, hBr⟩, fun h ↦ hYx (by rw [show Y = V from h]; exact hM.onX)⟩, Subtype.ext hY⟩

/-- **The marked branch vertices of the contraction** are those of the datum other than `V`. -/
noncomputable def branchEquiv (hM : S.MarkHyp M V M') :
    {B : MarkedBranchVertex data M // B.1 ≠ V} ≃ MarkedBranchVertex S.D M' :=
  Equiv.ofBijective _ (S.branchMap_bijective hM)

/-- The branch equivalence, unfolded. -/
theorem branchEquiv_val (hM : S.MarkHyp M V M') (B : {B : MarkedBranchVertex data M // B.1 ≠ V}) :
    (S.branchEquiv hM B).1 = S.vmap B.1.1 := rfl

/-! ### The marked matrix -/

/-- A column of the contraction, from a target edge other than `c`. -/
noncomputable abbrev col (f : {f : target.edges // f ≠ S.c}) : (S.T').edges :=
  foldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne f

/-- The target of the image of an occurrence away from `c`. -/
theorem emap_target (e : {e : data.SourceEdge // e.1.1 ≠ S.c}) :
    (S.emap e).1.1 = S.col ⟨e.1.1.1, e.2⟩ := rfl

/-- The surviving contracted occurrence of a surviving occurrence away from `c`. -/
theorem ndMap_of_ne (e : NonDanglingEdge data) (h : e.1.1.1 ≠ S.c) :
    (S.ndMap e).1 = S.emap ⟨e.1, h⟩ := S.edgeMap_of_ne h

/-- **Membership in a contracted marked row, over a contracted column.** -/
theorem mem_markedOccurrences_emap (hM : S.MarkHyp M V M') (r : MarkedStablePath data M)
    (f : {f : target.edges // f ≠ S.c}) (e : {e : data.SourceEdge // e.1.1 ≠ S.c}) :
    S.emap e ∈ markedOccurrences S.D M' (S.rowMap hM r) (S.col f) ↔
      e.1.1.1 = f.1 ∧ ∃ hNd : ¬ IsDangling data e.1,
        S.RowRel hM (markedRow M (⟨e.1, hNd⟩ : NonDanglingEdge data)) r := by
  rw [mem_markedOccurrences, S.emap_target]
  have hCol : S.col ⟨e.1.1.1, e.2⟩ = S.col f ↔ e.1.1.1 = f.1 :=
    ⟨fun h ↦ congrArg Subtype.val (foldEdge_injective (contracted := S.c) rfl (fst_ne_snd S.c)
      S.hOne h), fun h ↦ by congr 1; exact Subtype.ext h⟩
  rw [hCol]
  constructor
  · rintro ⟨⟨hNdD, hRow⟩, hT⟩
    have hNd : ¬ IsDangling data e.1 := (S.isDangling_emap_iff e).not.mp hNdD
    refine ⟨hT, hNd, (S.rowMap_eq_iff hM _ _).mp ?_⟩
    have hEq : S.ndMap ⟨e.1, hNd⟩ = ⟨S.emap e, hNdD⟩ :=
      Subtype.ext (S.ndMap_of_ne ⟨e.1, hNd⟩ e.2)
    show markedRow M' (S.ndMap ⟨e.1, hNd⟩) = _
    rw [hEq]
    exact hRow
  · rintro ⟨hT, hNd, hRel⟩
    have hNdD : ¬ IsDangling S.D (S.emap e) := (S.isDangling_emap_iff e).not.mpr hNd
    refine ⟨⟨hNdD, ?_⟩, hT⟩
    have hEq : S.ndMap ⟨e.1, hNd⟩ = ⟨S.emap e, hNdD⟩ :=
      Subtype.ext (S.ndMap_of_ne ⟨e.1, hNd⟩ e.2)
    rw [← hEq]
    exact (S.rowMap_eq_iff hM _ _).mpr hRel

open Classical in
/-- **A contracted entry is a sum over the fibre of the row map.** -/
theorem markedMatrix_rowMap (hM : S.MarkHyp M V M') (r : MarkedStablePath data M)
    (f : {f : target.edges // f ≠ S.c}) :
    markedMatrix S.D M' (S.rowMap hM r) (S.col f) =
      ∑ e : data.SourceEdge, if (e.1.1 = f.1 ∧ ∃ hNd : ¬ IsDangling data e,
        S.RowRel hM (markedRow M (⟨e, hNd⟩ : NonDanglingEdge data)) r)
      then (1 : ℚ) / data.sourceEdgeIndex e else 0 := by
  unfold markedMatrix
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun e he ↦ S.emap ⟨e, fun hc ↦
    f.2 (((Finset.mem_filter.mp he).2.1).symm.trans hc)⟩) ?_ ?_ ?_ ?_
  · intro e he
    exact (S.mem_markedOccurrences_emap hM r f _).mpr (Finset.mem_filter.mp he).2
  · intro e₁ he₁ e₂ he₂ h
    exact congrArg Subtype.val (sourceEdgeMap_injective data (contracted := S.c) rfl
      (fst_ne_snd S.c) S.hOne h)
  · intro g hg
    obtain ⟨g₀, rfl⟩ := ContractionFibre.sourceEdgeMap_surjective data (contracted := S.c) rfl
      (fst_ne_snd S.c) S.hOne g
    exact ⟨g₀.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (S.mem_markedOccurrences_emap hM r f g₀).mp hg⟩, rfl⟩
  · intro e he
    have h := ContractionFibre.sourceEdgeIndex_sourceEdgeMap data (contracted := S.c) rfl
      (fst_ne_snd S.c) S.hOne ⟨e, fun hc ↦ f.2 (((Finset.mem_filter.mp he).2.1).symm.trans hc)⟩
    exact congrArg (fun n : ℕ ↦ (1 : ℚ) / n) h.symm

open Classical in
/-- An entry of the marked matrix as a sum over all occurrences. -/
theorem markedMatrix_eq_sum (data : GluingDatum target degree) (M : Finset data.SourceVertex)
    (r : MarkedStablePath data M) (place : target.edges) :
    markedMatrix data M r place =
      ∑ e : data.SourceEdge, if (e.1.1 = place ∧ ∃ hNd : ¬ IsDangling data e,
        markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) = r)
      then (1 : ℚ) / data.sourceEdgeIndex e else 0 := by
  unfold markedMatrix
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext e
  rw [mem_markedOccurrences, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

/-- Away from the two rows at `V`, the contracted entries are the old ones. -/
theorem markedMatrix_rowMap_of_ne (hM : S.MarkHyp M V M') {r : MarkedStablePath data M}
    (hc : r ≠ markedRow M (S.fc hM)) (ho : r ≠ markedRow M (S.fo hM))
    (f : {f : target.edges // f ≠ S.c}) :
    markedMatrix S.D M' (S.rowMap hM r) (S.col f) = markedMatrix data M r f.1 := by
  classical
  rw [S.markedMatrix_rowMap hM r f, markedMatrix_eq_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  congr 1
  apply propext
  refine and_congr Iff.rfl (exists_congr fun hNd ↦ ?_)
  constructor
  · rintro (h | ⟨-, h | h⟩)
    · exact h
    · exact absurd h hc
    · exact absurd h ho
  · exact Or.inl

/-- At the merged row, the contracted entries are the sums of the two old ones. -/
theorem markedMatrix_rowMap_fc (hM : S.MarkHyp M V M')
    (hne : markedRow M (S.fc hM) ≠ markedRow M (S.fo hM)) (f : {f : target.edges // f ≠ S.c}) :
    markedMatrix S.D M' (S.rowMap hM (markedRow M (S.fc hM))) (S.col f) =
      markedMatrix data M (markedRow M (S.fc hM)) f.1 +
        markedMatrix data M (markedRow M (S.fo hM)) f.1 := by
  classical
  rw [S.markedMatrix_rowMap hM _ f, markedMatrix_eq_sum, markedMatrix_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  by_cases hT : e.1.1 = f.1
  swap
  · simp [hT]
  by_cases hNd : IsDangling data e
  · simp [hNd]
  have h1 : (∃ h : ¬ IsDangling data e, S.RowRel hM (markedRow M (⟨e, h⟩ : NonDanglingEdge data))
      (markedRow M (S.fc hM))) ↔ (markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) =
        markedRow M (S.fc hM) ∨ markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) =
          markedRow M (S.fo hM)) := by
    constructor
    · rintro ⟨_, h | ⟨h, -⟩⟩
      · exact Or.inl h
      · exact h
    · rintro (h | h)
      · exact ⟨hNd, Or.inl h⟩
      · exact ⟨hNd, Or.inr ⟨Or.inr h, Or.inl rfl⟩⟩
  have h2 : ∀ t : MarkedStablePath data M,
      (∃ h : ¬ IsDangling data e, markedRow M (⟨e, h⟩ : NonDanglingEdge data) = t) ↔
        markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) = t :=
    fun t ↦ ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hNd, h⟩⟩
  simp only [hT, true_and, h1, h2]
  by_cases hc : markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) = markedRow M (S.fc hM)
  · have ho : markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) ≠ markedRow M (S.fo hM) :=
      fun ho ↦ hne (hc.symm.trans ho)
    simp [hc, hne]
  · simp [hc]

/-- The occurrence over `c` through the sheet of an occurrence. -/
noncomputable def cPartner (e : data.SourceEdge) : data.SourceEdge := data.sourceEdge S.c e.1.2

/-- The `c`-partner of the partner is the occurrence itself. -/
theorem cPartner_partner {e : data.SourceEdge} (h : e.1.1 = S.c) : S.cPartner (S.partner e) = e := by
  unfold cPartner partner
  rw [S.eq_sourceEdge_c h]
  refine (sourceEdge_eq_iff data _ _ _).mpr ?_
  simp only [GluingDatum.sourceEdge_sheet]
  have h1 := (S.other_rel_iff _ _).mp
    ((data.edgePartition S.other).rel_repr_left ((data.edgePartition S.c).repr e.1.2))
  have h2 := (S.c_rel_iff _ _).mp ((data.edgePartition S.c).rel_repr_left e.1.2)
  exact (S.c_rel_iff _ _).mpr (h1.trans h2)

/-- The partner of the `c`-partner is the occurrence itself. -/
theorem partner_cPartner {e : data.SourceEdge} (h : e.1.1 = S.other) :
    S.partner (S.cPartner e) = e := by
  unfold cPartner partner
  conv_rhs => rw [← GluingDatum.sourceEdge_self data e]
  rw [h]
  refine (sourceEdge_eq_iff data _ _ _).mpr ?_
  simp only [GluingDatum.sourceEdge_sheet]
  exact (S.other_rel_iff _ _).mpr ((S.c_rel_iff _ _).mp ((data.edgePartition S.c).rel_repr_left _))

/-- Partners have the same index. -/
theorem sourceEdgeIndex_partner {e : data.SourceEdge} (h : e.1.1 = S.c) :
    data.sourceEdgeIndex (S.partner e) = data.sourceEdgeIndex e := by
  unfold GluingDatum.sourceEdgeIndex partner
  simp only [GluingDatum.sourceEdge_target, GluingDatum.sourceEdge_sheet]
  rw [h]
  rw [blockCard_congr _ ((data.edgePartition S.other).rel_repr_left e.1.2)]
  exact (edge_blockCard_eq S.div S.other_mem S.mem e.1.2)

/-- **Partners away from `V` lie on one marked row.** -/
theorem markedRow_partner (hM : S.MarkHyp M V M') {e : NonDanglingEdge data} (h : e.1.1.1 = S.c)
    (hne : e ≠ S.fc hM) :
    markedRow M (⟨S.partner e.1, (S.isDangling_partner_iff h).not.mpr e.2⟩ : NonDanglingEdge data) =
      markedRow M e := by
  set X := data.sourceEndpoint S.x e.1.1.2 with hXdef
  have hXV : X ≠ V := by
    intro hXV
    apply hne
    apply Subtype.ext
    change e.1 = data.sourceEdge S.c V.1.2
    rw [S.eq_sourceEdge_c h]
    refine (sourceEdge_eq_iff data _ _ _).mpr ((S.c_rel_iff _ _).mpr ?_)
    have h' := (data.sourceEndpoint_eq_iff _ _ _).mp hXV
    exact h'.2
  have hpe : (⟨S.partner e.1, (S.isDangling_partner_iff h).not.mpr e.2⟩ : NonDanglingEdge data) ≠
      e := by
    intro h'
    have := congrArg (fun g : NonDanglingEdge data ↦ g.1.1.1) h'
    simp only [S.partner_target] at this
    exact S.other_ne (this.trans h)
  refine markedRow_eq_of_markedConsecutive ⟨hpe, X, S.incident_partner_x e.1,
    S.incident_c_x h, S.nonDanglingValency_eq_two_of_ne rfl hpe (S.incident_partner_x e.1)
      (S.incident_c_x h), fun hXM ↦ hXV (hM.only X hXM rfl)⟩

open Classical in
/-- **The two columns at `x`**: columns `c` and `other` of the marked matrix agree, except for the
two occurrences at `V`, of index `m`. -/
theorem markedMatrix_c_add (hM : S.MarkHyp M V M') (r : MarkedStablePath data M) :
    markedMatrix data M r S.c +
        (if markedRow M (S.fo hM) = r then (1 : ℚ) / data.sourceEdgeIndex (S.fc hM).1 else 0) =
      markedMatrix data M r S.other +
        (if markedRow M (S.fc hM) = r then (1 : ℚ) / data.sourceEdgeIndex (S.fc hM).1 else 0) := by
  -- the summand of a row over a target edge
  let T : data.SourceEdge → ℚ := fun e ↦ if (∃ hNd : ¬ IsDangling data e,
    markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) = r) then (1 : ℚ) / data.sourceEdgeIndex e else 0
  have hSum : ∀ place : target.edges, markedMatrix data M r place =
      ∑ e ∈ Finset.univ.filter (fun e : data.SourceEdge ↦ e.1.1 = place), T e := by
    intro place
    rw [markedMatrix_eq_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    by_cases h : e.1.1 = place <;> simp [h, T]
  have hc_mem : (S.fc hM).1 ∈ Finset.univ.filter (fun e : data.SourceEdge ↦ e.1.1 = S.c) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  -- reindex the `other` column by partners
  have hOther : ∑ e ∈ Finset.univ.filter (fun e : data.SourceEdge ↦ e.1.1 = S.other), T e =
      ∑ e ∈ Finset.univ.filter (fun e : data.SourceEdge ↦ e.1.1 = S.c), T (S.partner e) := by
    symm
    refine Finset.sum_nbij' S.partner S.cPartner ?_ ?_ ?_ ?_ ?_
    · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · intro e he; exact S.cPartner_partner (Finset.mem_filter.mp he).2
    · intro e he; exact S.partner_cPartner (Finset.mem_filter.mp he).2
    · intro e _; rfl
  rw [hSum, hSum, hOther, ← Finset.add_sum_erase _ _ hc_mem, ← Finset.add_sum_erase _ _ hc_mem]
  -- the terms away from `V` agree
  have hRest : ∑ e ∈ (Finset.univ.filter (fun e : data.SourceEdge ↦ e.1.1 = S.c)).erase (S.fc hM).1,
      T e = ∑ e ∈ (Finset.univ.filter (fun e : data.SourceEdge ↦ e.1.1 = S.c)).erase (S.fc hM).1,
      T (S.partner e) := by
    refine Finset.sum_congr rfl fun e he ↦ ?_
    obtain ⟨hne, he⟩ := Finset.mem_erase.mp he
    have hc : e.1.1 = S.c := (Finset.mem_filter.mp he).2
    have hIdx := S.sourceEdgeIndex_partner hc
    by_cases hNd : IsDangling data e
    · have hNd' : IsDangling data (S.partner e) := (S.isDangling_partner_iff hc).mpr hNd
      simp [T, hNd, hNd']
    · have hRow := S.markedRow_partner hM (e := ⟨e, hNd⟩) hc (fun h ↦ hne (congrArg Subtype.val h))
      have hNd' : ¬ IsDangling data (S.partner e) := (S.isDangling_partner_iff hc).not.mpr hNd
      have hE₁ : (∃ h : ¬ IsDangling data e, markedRow M (⟨e, h⟩ : NonDanglingEdge data) = r) ↔
          markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) = r :=
        ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hNd, h⟩⟩
      have hE₂ : (∃ h : ¬ IsDangling data (S.partner e),
          markedRow M (⟨S.partner e, h⟩ : NonDanglingEdge data) = r) ↔
            markedRow M (⟨e, hNd⟩ : NonDanglingEdge data) = r :=
        ⟨fun ⟨_, h⟩ ↦ hRow ▸ h, fun h ↦ ⟨hNd', hRow ▸ h⟩⟩
      simp only [T, hE₁, hE₂, hIdx]
  rw [hRest]
  -- the terms at `V`
  have hfo : S.partner (S.fc hM).1 = (S.fo hM).1 := S.partner_sourceEdge_c V.1.2
  have hTc : T (S.fc hM).1 = if markedRow M (S.fc hM) = r then
      (1 : ℚ) / data.sourceEdgeIndex (S.fc hM).1 else 0 := by
    simp only [T]
    congr 1
    exact propext ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨(S.fc hM).2, h⟩⟩
  have hTo : T (S.partner (S.fc hM).1) = if markedRow M (S.fo hM) = r then
      (1 : ℚ) / data.sourceEdgeIndex (S.fc hM).1 else 0 := by
    simp only [T, hfo]
    rw [show data.sourceEdgeIndex (S.fo hM).1 = data.sourceEdgeIndex (S.fc hM).1 from
      hfo ▸ S.sourceEdgeIndex_partner (e := (S.fc hM).1) rfl]
    congr 1
    exact propext ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨(S.fo hM).2, h⟩⟩
  rw [hTc, hTo]
  ring

end Site

/-! ## 4.  Local data at the marks, leaves, the target -/

namespace Site

variable (S : Site data)

/-- The target vertex of the image of a source vertex. -/
theorem vmap_target (A : data.SourceVertex) :
    (S.vmap A).1.1 = fold target (fst_ne_snd S.c) A.1.1 := rfl

/-- **The partition above the image of a vertex other than `x` has its blocks.** -/
theorem vp_fold_rel_iff {u : target.V} (hu : u ≠ S.x) (i j : Fin degree) :
    (S.D.vertexPartition (fold target (fst_ne_snd S.c) u)).Rel i j ↔
      (data.vertexPartition u).Rel i j := by
  change (contractVertexPartition data _ _ (fold target (fst_ne_snd S.c) u)).Rel i j ↔ _
  unfold contractVertexPartition
  by_cases hub : u = (S.c : target.V × target.V).2
  · have hfold : ((fold target (fst_ne_snd S.c) u : GraphContraction.Vertex target _) :
        target.V) = (S.c : target.V × target.V).1 := by
      rw [hub, GraphContraction.fold_self]
    rw [ite_eq_left hfold]
    have huw : u = S.w := by
      rcases S.c_ends with h | h
      · rw [hub, h.2]
      · exact absurd (hub.trans h.2) hu
    rw [← mergedPartition, S.merged_rel_iff, huw]
  · rw [GraphContraction.fold_of_ne target (fst_ne_snd S.c) hub]
    by_cases hua : u = (S.c : target.V × target.V).1
    · rw [ite_eq_left hua]
      have huw : u = S.w := by
        rcases S.c_ends with h | h
        · exact absurd (hua.trans h.1) hu
        · rw [hua, h.1]
      rw [← mergedPartition, S.merged_rel_iff, huw]
    · rw [ite_eq_right hua]

/-- Block sizes depend only on the blocks. -/
theorem blockCard_eq_of_rel_iff {P Q : SheetPartition degree} (h : ∀ i j, P.Rel i j ↔ Q.Rel i j)
    (i : Fin degree) : P.blockCard i = Q.blockCard i := by
  unfold SheetPartition.blockCard
  congr 1
  ext j
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact h i j

/-- **The local degree is unchanged away from `x`.** -/
theorem markIndex_vmap {A : data.SourceVertex} (hA : A.1.1 ≠ S.x) :
    markIndex S.D (S.vmap A) = markIndex data A := by
  unfold markIndex
  exact (blockCard_congr _ ((S.D.vertexPartition _).rel_repr_left A.1.2)).trans
    (blockCard_eq_of_rel_iff (S.vp_fold_rel_iff hA) A.1.2)

/-- Over `x`, the local ramifications of the blocks inside a merged block vanish. -/
theorem sum_localRamification_x {u : target.V} (hu : u = S.x)
    (B : (mergedPartition data (S.c : target.V × target.V).1 (S.c : target.V × target.V).2).Blocks) :
    (∑ fb ∈ SheetPartition.blocksWithin (data.vertexPartition u) _ B,
      data.localRamification u fb) = 0 := by
  subst hu
  refine Finset.sum_eq_zero fun fb _ ↦ ?_
  have hfb : fb = (data.vertexPartition S.x).toBlock fb.1 := Subtype.ext fb.2.symm
  rw [hfb]
  exact S.div.2 fb.1

/-- The local ramification at the block of a source vertex. -/
theorem localRamification_toBlock {u : target.V} (A : data.SourceVertex) (hA : A.1.1 = u) :
    data.localRamification u ((data.vertexPartition u).toBlock A.1.2) = markRamification data A := by
  obtain ⟨⟨u', i⟩, hi⟩ := A
  simp only at hA
  subst hA
  unfold markRamification
  congr 1
  exact Subtype.ext hi

/-- Over `w`, a merged block contains the one block of `w` it meets. -/
theorem sum_localRamification_w {u : target.V} (hu : u = S.w) (A : data.SourceVertex)
    (hA : A.1.1 = u) :
    (∑ fb ∈ SheetPartition.blocksWithin (data.vertexPartition u) _
        ((mergedPartition data (S.c : target.V × target.V).1
          (S.c : target.V × target.V).2).toBlock A.1.2),
      data.localRamification u fb) = markRamification data A := by
  subst hu
  have hSet : SheetPartition.blocksWithin (data.vertexPartition S.w)
      (mergedPartition data (S.c : target.V × target.V).1 (S.c : target.V × target.V).2)
      ((mergedPartition data _ _).toBlock A.1.2) = {(data.vertexPartition S.w).toBlock A.1.2} := by
    ext fb
    rw [SheetPartition.mem_blocksWithin, SheetPartition.fineBlockToCoarseBlock_eq_iff_rel,
      Finset.mem_singleton, S.merged_rel_iff]
    have hm : (data.vertexPartition S.w).Rel
        ((mergedPartition data (S.c : target.V × target.V).1
          (S.c : target.V × target.V).2).toBlock A.1.2).1 A.1.2 :=
      (S.merged_rel_iff _ _).mp ((mergedPartition data _ _).rel_repr_left A.1.2)
    constructor
    · intro h
      apply Subtype.ext
      have h' : (data.vertexPartition S.w).repr A.1.2 = (data.vertexPartition S.w).repr fb.1 :=
        hm.symm.trans h
      rw [fb.2] at h'
      exact h'.symm
    · intro h
      rw [h]
      exact hm.trans ((data.vertexPartition S.w).rel_repr_right A.1.2)
  rw [hSet, Finset.sum_singleton]
  exact localRamification_toBlock A hA

/-- `toBlock` of a representative. -/
theorem toBlock_repr (P : SheetPartition degree) (i : Fin degree) : P.toBlock (P.repr i) = P.toBlock i :=
  Subtype.ext (P.repr_idem i)

/-- **The local ramification is unchanged away from `x`.** -/
theorem markRamification_vmap {A : data.SourceVertex} (hA : A.1.1 ≠ S.x) :
    markRamification S.D (S.vmap A) = markRamification data A := by
  by_cases hab : A.1.1 = (S.c : target.V × target.V).1 ∨ A.1.1 = (S.c : target.V × target.V).2
  · have hAw : A.1.1 = S.w := by
      rcases S.eq_x_or_eq_w (u := A.1.1) (by
        rw [mem_incidentEdges_iff]; rcases hab with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm) with h | h
      · exact absurd h hA
      · exact h
    have hfold : fold target (fst_ne_snd S.c) A.1.1 = ⟨(S.c : target.V × target.V).1, fst_ne_snd S.c⟩ := by
      rcases hab with h | h
      · rw [h, GraphContraction.fold_a]
      · rw [h, GraphContraction.fold_self]
    have hv : S.vmap A = S.D.sourceEndpoint ⟨(S.c : target.V × target.V).1, fst_ne_snd S.c⟩ A.1.2 := by
      show S.D.sourceEndpoint (fold target (fst_ne_snd S.c) A.1.1) A.1.2 = _
      rw [hfold]
    rw [hv]
    have hMerge := localRamification_contractDatum_merge data (contracted := S.c) rfl
      (fst_ne_snd S.c) S.hOne S.contractionForest
      ⟨(S.D.vertexPartition ⟨(S.c : target.V × target.V).1, fst_ne_snd S.c⟩).repr A.1.2,
        (S.D.vertexPartition _).repr_idem _⟩
    unfold markRamification
    refine Eq.trans hMerge ?_
    rw [show (mergedPartition data (S.c : target.V × target.V).1 (S.c : target.V × target.V).2).toBlock
        ((S.D.vertexPartition ⟨(S.c : target.V × target.V).1, fst_ne_snd S.c⟩).repr A.1.2) =
        (mergedPartition data _ _).toBlock A.1.2 from by
      rw [show S.D.vertexPartition ⟨(S.c : target.V × target.V).1, fst_ne_snd S.c⟩ =
        mergedPartition data _ _ from contractDatum_vertexPartition_merge data rfl _ S.hOne]
      exact toBlock_repr _ _]
    rcases S.c_ends with h | h
    · rw [S.sum_localRamification_x h.1, S.sum_localRamification_w h.2 A (hAw.trans h.2.symm),
        zero_add]
      rfl
    · rw [S.sum_localRamification_x h.2, S.sum_localRamification_w h.1 A (hAw.trans h.1.symm),
        add_zero]
      rfl
  · push Not at hab
    obtain ⟨hua, hub⟩ := hab
    have hv : S.vmap A = S.D.sourceEndpoint ⟨A.1.1, hub⟩ A.1.2 := by
      show S.D.sourceEndpoint (fold target (fst_ne_snd S.c) A.1.1) A.1.2 = _
      rw [GraphContraction.fold_of_ne target (fst_ne_snd S.c) hub]
    have hvp : S.D.vertexPartition ⟨A.1.1, hub⟩ = data.vertexPartition A.1.1 :=
      contractVertexPartition_of_ne data _ _ (y := ⟨A.1.1, hub⟩) hua
    rw [hv]
    have hSum := sum_blockCountWithin_contract_of_ne data (contracted := S.c) rfl (fst_ne_snd S.c)
      S.hOne hub hua A.1.2
    have hCard := card_incidentEdges_contract_of_ne (contracted := S.c) rfl (fst_ne_snd S.c)
      S.hOne hub hua
    unfold markRamification GluingDatum.localRamification
    have hrep : (data.vertexPartition A.1.1).repr A.1.2 = A.1.2 := A.2
    simp only [GluingDatum.sourceEndpoint]
    rw [hvp, hrep]
    rw [hvp] at hSum
    rw [hSum, hCard]

/-- `x` is not a leaf. -/
theorem not_isLeafVertex_x : ¬ Count.IsLeafVertex target S.x := by
  unfold Count.IsLeafVertex
  rw [S.div.1]
  omega

/-- **Leaves away from `x` correspond.** -/
theorem isLeafVertex_fold_iff {u : target.V} (hu : u ≠ S.x) :
    Count.IsLeafVertex (S.T') (fold target (fst_ne_snd S.c) u) ↔
      Count.IsLeafVertex target u := by
  unfold Count.IsLeafVertex
  by_cases hab : u = (S.c : target.V × target.V).1 ∨ u = (S.c : target.V × target.V).2
  · have huw : u = S.w := by
      rcases S.eq_x_or_eq_w (u := u) (by
        rw [mem_incidentEdges_iff]; rcases hab with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm) with h | h
      · exact absurd h hu
      · exact h
    have hfold : fold target (fst_ne_snd S.c) u = ⟨(S.c : target.V × target.V).1, fst_ne_snd S.c⟩ := by
      rcases hab with h | h
      · rw [h, GraphContraction.fold_a]
      · rw [h, GraphContraction.fold_self]
    rw [hfold]
    have hMerge := card_incidentEdges_merge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne
    have hx := S.div.1
    have hcard : (incidentEdges (target := S.T')
        ⟨(S.c : target.V × target.V).1, fst_ne_snd S.c⟩).card = (incidentEdges u).card := by
      rcases S.c_ends with h | h
      · have h1 : (incidentEdges (S.c : target.V × target.V).1).card = 2 := by rw [h.1]; exact hx
        have h2 : (incidentEdges (S.c : target.V × target.V).2).card = (incidentEdges u).card := by
          rw [h.2, huw]
        exact Nat.add_right_cancel (hMerge.trans (by rw [h1, h2, Nat.add_comm]))
      · have h1 : (incidentEdges (S.c : target.V × target.V).2).card = 2 := by rw [h.2]; exact hx
        have h2 : (incidentEdges (S.c : target.V × target.V).1).card = (incidentEdges u).card := by
          rw [h.1, huw]
        exact Nat.add_right_cancel (hMerge.trans (by rw [h1, h2]))
    rw [hcard]
  · push Not at hab
    obtain ⟨hua, hub⟩ := hab
    rw [GraphContraction.fold_of_ne target (fst_ne_snd S.c) hub]
    have h := card_incidentEdges_contract_of_ne (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne
      hub hua
    exact ⟨fun h' ↦ h.trans h', fun h' ↦ h.symm.trans h'⟩

/-- **The contraction keeps the leaves.** -/
theorem leafCount_contract : Count.leafCount (S.T') = Count.leafCount target := by
  classical
  unfold Count.leafCount
  symm
  refine Finset.card_bij (fun u _ ↦ fold target (fst_ne_snd S.c) u) ?_ ?_ ?_
  · intro u hu
    have hu' := (Count.mem_leafVertices u).mp hu
    have hux : u ≠ S.x := fun h ↦ S.not_isLeafVertex_x (h ▸ hu')
    exact (Count.mem_leafVertices _).mpr ((S.isLeafVertex_fold_iff hux).mpr hu')
  · intro u₁ hu₁ u₂ hu₂ h
    have hu₁' := (Count.mem_leafVertices u₁).mp hu₁
    have hu₂' := (Count.mem_leafVertices u₂).mp hu₂
    have hu₁x : u₁ ≠ S.x := fun h ↦ S.not_isLeafVertex_x (h ▸ hu₁')
    have hu₂x : u₂ ≠ S.x := fun h ↦ S.not_isLeafVertex_x (h ▸ hu₂')
    rcases (GraphContraction.fold_eq_fold_iff target (fst_ne_snd S.c) u₁ u₂).mp h with
      h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact h
    · rcases S.c_ends with h' | h'
      · exact absurd (h₁.trans h'.1) hu₁x
      · exact absurd (h₂.trans h'.2) hu₂x
    · rcases S.c_ends with h' | h'
      · exact absurd (h₂.trans h'.1) hu₂x
      · exact absurd (h₁.trans h'.2) hu₁x
  · intro y hy
    have hy' := (Count.mem_leafVertices y).mp hy
    by_cases hyx : y.1 = S.x
    · -- then `x` is the first end, and `y` is the merged vertex, the image of `w`
      have hxa : S.x = (S.c : target.V × target.V).1 := by
        rcases S.x_eq_or with h | h
        · exact h
        · exact absurd (hyx.trans h) y.2
      have hyw : fold target (fst_ne_snd S.c) S.w = y := by
        have hwb : S.w = (S.c : target.V × target.V).2 := by
          rcases S.c_ends with h | h
          · exact h.2.symm
          · exact absurd (hxa.trans h.1) S.w_ne_x.symm
        rw [hwb, GraphContraction.fold_self]
        exact Subtype.ext (hxa ▸ hyx).symm
      refine ⟨S.w, (Count.mem_leafVertices _).mpr ((S.isLeafVertex_fold_iff S.w_ne_x).mp ?_), hyw⟩
      exact hyw ▸ hy'
    · refine ⟨y.1, (Count.mem_leafVertices _).mpr ((S.isLeafVertex_fold_iff hyx).mp ?_),
        GraphContraction.fold_coe target (fst_ne_snd S.c) y⟩
      exact (GraphContraction.fold_coe target (fst_ne_snd S.c) y).symm ▸ hy'

end Site

end Contraction

end DivalentContraction

end DraismaVargas.Count.MarkedCountGeneral
