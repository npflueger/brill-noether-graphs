module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropRows
public import DraismaVargasMarkedCount.MarkedCountGeneral.DropDet
public import DraismaVargasMarkedCount.MarkedCountGeneral.DropIso
public import DraismaVargasMarkedCount.MarkedCountGeneral.DenomDrop

@[expose] public section

/-!
# The drop lemma: the drop of a typed frame (I1)

Let `κ` be a typed frame over `sub := subdivide core s` whose last mark `v` has type `0`. Its
source vertex `V` lies over a divalent change-zero target vertex `x` with no other mark over it
(`typeZero_image'`). The **drop** contracts the target edge `t'` of the occurrence at `V` on the
row labelled `cs s` (module `DropContract`, `Site`), and reads every field of a typed frame over
`core` off the dictionary of module `DropRows`:

* the marks are the images of the old ones;
* the marked rows are those of `κ` with the two rows through `V` (labelled `cs s` and `last p`)
  joined into the row labelled `s`;
* the columns are the target edges other than `t'`;
* the identification sends the branch vertices other than `V` to their core vertices, and the
  incidences add over the joined rows (`subdivide`'s pieces of `s`);
* (D4′) at the old marks, validity, the dimension count and the determinant
  (`DropDet.abs_det_eq_of_merge`) carry over.

The construction is `dropFrame'`. This module is the request-free part of I1.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction
open GenusSixExistence.Tripod.Gadget (subdivide subdivide_tail_castSucc subdivide_tail_last
  subdivide_head_castSucc subdivide_head_last)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ}

namespace DropSmooth

/-! ## 1.  Incidences of the subdivided core -/

section Incidence

variable (core : Core n p) (s : Fin p)

/-- The new vertex meets only the slot `cs s` among the old slots. -/
theorem coreIncidence_last_castSucc (i : Fin p) :
    coreIncidence (subdivide core s) (Fin.last n) i.castSucc = if i = s then 1 else 0 := by
  unfold coreIncidence
  rw [subdivide_tail_castSucc, subdivide_head_castSucc]
  have hne : ∀ u : Fin n, u.castSucc ≠ Fin.last n := fun u ↦ (Fin.castSucc_lt_last u).ne
  by_cases h : i = s
  · simp [h, hne]
  · simp [h, hne]

/-- The new vertex meets the slot `last p` once. -/
theorem coreIncidence_last_last :
    coreIncidence (subdivide core s) (Fin.last n) (Fin.last p) = 1 := by
  unfold coreIncidence
  rw [subdivide_tail_last, subdivide_head_last]
  have hne : ∀ u : Fin n, u.castSucc ≠ Fin.last n := fun u ↦ (Fin.castSucc_lt_last u).ne
  simp [hne]

/-- Away from `s`, the incidences of the subdivided core are those of the core. -/
theorem coreIncidence_castSucc_castSucc_of_ne (u : Fin n) {i : Fin p} (hi : i ≠ s) :
    coreIncidence (subdivide core s) u.castSucc i.castSucc = coreIncidence core u i := by
  unfold coreIncidence
  rw [subdivide_tail_castSucc, subdivide_head_castSucc, ite_eq_right hi]
  simp only [Fin.castSucc_inj]

/-- The two pieces of `s` share the incidences of `s`. -/
theorem coreIncidence_castSucc_split (u : Fin n) :
    coreIncidence (subdivide core s) u.castSucc s.castSucc +
        coreIncidence (subdivide core s) u.castSucc (Fin.last p) = coreIncidence core u s := by
  unfold coreIncidence
  rw [subdivide_tail_castSucc, subdivide_head_castSucc, subdivide_tail_last, subdivide_head_last,
    ite_eq_left rfl]
  have hne : Fin.last n ≠ u.castSucc := (Fin.castSucc_lt_last u).ne'
  simp only [Fin.castSucc_inj, hne, ite_false]
  ring

end Incidence

/-! ## 2.  The dropped mark and the contraction site -/

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
variable {s : Fin p} (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)

/-- The source vertex of the dropped mark. -/
abbrev V : κ.data.SourceVertex := κ.markSource (Fin.last k)

/-- The last type is `0`. -/
theorem snocType_last : snocType types 0 (Fin.last k) = 0 := by simp [snocType]

/-- The last mark is the new vertex. -/
theorem snocMark_last : snocMark mark (Fin.last k) = Fin.last n := by simp [snocMark]

/-- The old types. -/
theorem snocType_castSucc (j : Fin k) : snocType types 0 j.castSucc = types j := by
  simp [snocType]

/-- The old marks. -/
theorem snocMark_castSucc (j : Fin k) : snocMark mark j.castSucc = (mark j).castSucc := by
  simp [snocMark]

/-- The local structure at the dropped mark (`typeZero_image'`). -/
theorem typeZero (hc : IsMarkedCubic core mark) :
    (incidentEdges (V κ).1.1).card = 2 ∧ κ.data.targetChange (V κ).1.1 = 0 ∧
      (∀ X : κ.data.SourceVertex, X.1.1 = (V κ).1.1 → markRamification κ.data X = 0) ∧
      ∀ i, (κ.markSource i).1.1 = (V κ).1.1 → i = Fin.last k :=
  typeZero_image' (isMarkedCubic_snoc hc s) κ (Fin.last k) (snocType_last)

/-- The marks. -/
abbrev M : Finset κ.data.SourceVertex := markSet κ.markSource

/-- The marked branch vertex of the dropped mark. -/
def VB : MarkedBranchVertex κ.data (M κ) := ⟨V κ, Or.inr (mem_markSet _ _)⟩

/-- The dropped mark is labelled by the new vertex. -/
theorem ident_VB : κ.ident.vertex (VB κ) = Fin.last n := by
  rw [show VB κ = ⟨κ.markSource (Fin.last k), Or.inr (mem_markSet κ.markSource (Fin.last k))⟩
    from rfl, κ.ident.vertex_mark, snocMark_last]

/-- The rows through `V` are those labelled `cs s` and `last p`, each once. -/
theorem count_V (ℓ : Fin (p + 1)) :
    markedIncidenceCount κ.data (M κ) (V κ) (κ.ident.row.symm ℓ) =
      coreIncidence (subdivide core s) (Fin.last n) ℓ := by
  have h := κ.ident.incidence (VB κ) ℓ
  rwa [ident_VB] at h

/-- The row `cs s` meets `V` once. -/
theorem count_V_cs :
    markedIncidenceCount κ.data (M κ) (V κ) (κ.ident.row.symm s.castSucc) = 1 := by
  rw [count_V, coreIncidence_last_castSucc, ite_eq_left rfl]

/-- The row `last p` meets `V` once. -/
theorem count_V_last :
    markedIncidenceCount κ.data (M κ) (V κ) (κ.ident.row.symm (Fin.last p)) = 1 := by
  rw [count_V, coreIncidence_last_last]

/-- The row `cs s` has an occurrence at `V`. -/
theorem exists_fV : ∃ f : NonDanglingEdge κ.data, Incident κ.data f.1 (V κ) ∧
    markedRow (M κ) f = κ.ident.row.symm s.castSucc := by
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp (count_V_cs κ)
  have hMem : f ∈ ((StablePathCount.incidentEdges κ.data (V κ)).filter fun e ↦
      markedRow (M κ) e = κ.ident.row.symm s.castSucc) := by
    rw [hf]
    exact Finset.mem_singleton_self _
  obtain ⟨hInc, hRow⟩ := Finset.mem_filter.mp hMem
  exact ⟨f, (StablePathCount.mem_incidentEdges _ _ _).mp hInc, hRow⟩

/-- **The occurrence at `V` on the row `cs s`.** -/
noncomputable def fV : NonDanglingEdge κ.data := (exists_fV κ).choose

/-- The chosen occurrence at `V` on the row `cs s`. -/
theorem fV_spec : Incident κ.data (fV κ).1 (V κ) ∧
    markedRow (M κ) (fV κ) = κ.ident.row.symm s.castSucc :=
  (exists_fV κ).choose_spec

/-- **The contracted target edge** `t'`. -/
noncomputable abbrev t' : κ.target.edges := (fV κ).1.1.1

/-- The contracted edge is the only edge between its ends (the target is a tree). -/
theorem hOne : num_edges κ.target ((t' κ) : κ.target.V × κ.target.V).1
    ((t' κ) : κ.target.V × κ.target.V).2 = 1 :=
  IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected κ.target
    κ.fullDim.targetConnected κ.fullDim.targetGenus _

/-- The image of the dropped mark is divalent of change zero. -/
theorem divalentZero (hc : IsMarkedCubic core mark) : DivalentZero κ.data (V κ).1.1 := by
  refine ⟨(typeZero κ hc).1, fun sheet ↦ ?_⟩
  exact (typeZero κ hc).2.2.1 (κ.data.sourceEndpoint (V κ).1.1 sheet) rfl

/-- The contracted edge is at the image of the dropped mark. -/
theorem t'_mem : t' κ ∈ incidentEdges (V κ).1.1 :=
  ((incident_iff_target_mem_and_rel κ.data _ _).mp (fV_spec κ).1).1

/-- **The contraction site of the drop.** -/
noncomputable def site (hc : IsMarkedCubic core mark) : Site κ.data where
  x := (V κ).1.1
  c := t' κ
  hOne := hOne κ
  mem := t'_mem κ
  div := divalentZero κ hc

/-- The marks of the drop. -/
noncomputable def markSourceD (hc : IsMarkedCubic core mark) (j : Fin k) : (site κ hc).D.SourceVertex :=
  (site κ hc).vmap (κ.markSource j.castSucc)

/-- The old marks are not over `x`. -/
theorem markSource_castSucc_ne (hc : IsMarkedCubic core mark) (j : Fin k) : (κ.markSource j.castSucc).1.1 ≠ (V κ).1.1 := by
  intro h
  exact (Fin.castSucc_lt_last j).ne ((typeZero κ hc).2.2.2 _ h)

/-- **The marked setting of the drop.** -/
theorem markHyp (hc : IsMarkedCubic core mark) : (site κ hc).MarkHyp (M κ) (V κ) (markSet (markSourceD κ hc)) where
  mem := mem_markSet _ _
  onX := rfl
  only Z hZ hZx := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ
    rw [(typeZero κ hc).2.2.2 i hZx]
  valency := κ.fullDim.markValency _ (mem_markSet _ _)
  marks Y hY := by
    unfold markSet markSourceD
    constructor
    · intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      have hY' := ((site κ hc).vmap_inj (markSource_castSucc_ne κ hc j) hY).mp hj
      exact Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, hY'⟩
    · intro h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      induction i using Fin.lastCases with
      | last => exact absurd rfl hY
      | cast j => exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-! ## 3.  The two rows through `V` -/

variable (hc : IsMarkedCubic core mark)

/-- The occurrence over `t'` at `V` is the chosen one. -/
theorem fc_eq : (site κ hc).fc (markHyp κ hc) = fV κ := by
  apply Subtype.ext
  rcases ((site κ hc).incident_x_iff (V κ) rfl (fV κ).1).mp (fV_spec κ).1 with h | h
  · exact h.symm
  · exfalso
    have := congrArg (fun e : κ.data.SourceEdge ↦ e.1.1) h
    exact (site κ hc).other_ne this.symm

/-- The row of the occurrence over `c` at `V` is labelled `cs s`. -/
theorem row_fc : markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) = κ.ident.row.symm s.castSucc := by
  rw [fc_eq]; exact (fV_spec κ).2

/-- The row of the other occurrence at `V` is labelled `last p`. -/
theorem row_fo : markedRow (M κ) ((site κ hc).fo (markHyp κ hc)) =
    κ.ident.row.symm (Fin.last p) := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp (count_V_last κ)
  have hMem : ∀ e, e ∈ ((StablePathCount.incidentEdges κ.data (V κ)).filter fun e ↦
      markedRow (M κ) e = κ.ident.row.symm (Fin.last p)) ↔ e = g := by
    intro e; rw [hg, Finset.mem_singleton]
  obtain ⟨hgInc, hgRow⟩ := Finset.mem_filter.mp ((hMem g).mpr rfl)
  rw [StablePathCount.mem_incidentEdges] at hgInc
  rcases ((site κ hc).incident_x_iff (V κ) rfl g.1).mp hgInc with h | h
  · exfalso
    have hg' : g = (site κ hc).fc (markHyp κ hc) := Subtype.ext h
    rw [hg', row_fc] at hgRow
    exact (Fin.castSucc_lt_last s).ne (κ.ident.row.symm.injective hgRow)
  · have hg' : g = (site κ hc).fo (markHyp κ hc) := Subtype.ext h
    rw [← hg']
    exact hgRow

/-- The two rows through `V` are distinct. -/
theorem row_fc_ne_fo : markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) ≠
    markedRow (M κ) ((site κ hc).fo (markHyp κ hc)) := by
  rw [row_fc, row_fo]
  intro h
  exact (Fin.castSucc_lt_last s).ne (κ.ident.row.symm.injective h)

/-- A row lies in the pair through `V` exactly when it is labelled by a piece of `s`. -/
theorem mem_pair_iff (ℓ : Fin (p + 1)) :
    (κ.ident.row.symm ℓ = markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) ∨
      κ.ident.row.symm ℓ = markedRow (M κ) ((site κ hc).fo (markHyp κ hc))) ↔
      ℓ = s.castSucc ∨ ℓ = Fin.last p := by
  rw [row_fc, row_fo]
  constructor
  · rintro (h | h)
    · exact Or.inl (κ.ident.row.symm.injective h)
    · exact Or.inr (κ.ident.row.symm.injective h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-! ## 4.  The dictionaries of the drop -/

/-- The contracted marks. -/
noncomputable abbrev MD : Finset (site κ hc).D.SourceVertex := markSet (markSourceD κ hc)

/-- The row of the drop labelled `i`. -/
noncomputable def rowOf (i : Fin p) : MarkedStablePath (site κ hc).D (MD κ hc) :=
  (site κ hc).rowMap (markHyp κ hc) (κ.ident.row.symm i.castSucc)

/-- The rows of the drop are labelled bijectively. -/
theorem rowOf_bijective : Function.Bijective (rowOf κ hc) := by
  constructor
  · intro i j h
    rcases ((site κ hc).rowMap_eq_iff (markHyp κ hc) _ _).mp h with h | ⟨hi, hj⟩
    · exact Fin.castSucc_injective _ (κ.ident.row.symm.injective h)
    · rcases (mem_pair_iff κ hc _).mp hi with hi | hi
      · rcases (mem_pair_iff κ hc _).mp hj with hj | hj
        · exact (Fin.castSucc_injective _ hi).trans (Fin.castSucc_injective _ hj).symm
        · exact absurd hj (Fin.castSucc_lt_last j).ne
      · exact absurd hi (Fin.castSucc_lt_last i).ne
  · intro d
    obtain ⟨r, rfl⟩ := (site κ hc).rowMap_surjective (markHyp κ hc) d
    obtain ⟨ℓ, rfl⟩ := κ.ident.row.symm.surjective r
    induction ℓ using Fin.lastCases with
    | last =>
      refine ⟨s, ((site κ hc).rowMap_eq_iff (markHyp κ hc) _ _).mpr (Or.inr ⟨?_, ?_⟩)⟩
      · exact (mem_pair_iff κ hc _).mpr (Or.inl rfl)
      · exact (mem_pair_iff κ hc _).mpr (Or.inr rfl)
    | cast i => exact ⟨i, rfl⟩

/-- **The rows of the drop**: labelled by the slots of `core`. -/
noncomputable def rowEquiv : MarkedStablePath (site κ hc).D (MD κ hc) ≃ Fin p :=
  (Equiv.ofBijective _ (rowOf_bijective κ hc)).symm

/-- The row of the drop labelled `i`. -/
theorem rowEquiv_symm (i : Fin p) : (rowEquiv κ hc).symm i = rowOf κ hc i := by
  unfold rowEquiv
  rw [Equiv.symm_symm]
  rfl

/-- The old column of the contracted edge. -/
noncomputable abbrev c₀ : Fin (p + 1) := κ.fullDim.labelling.targetEdge.symm (t' κ)

/-- **The columns of the drop**: the target edges other than `t'`. -/
noncomputable def colEquiv : Fin p ≃ (site κ hc).T'.edges :=
  (finSuccAboveEquiv (c₀ κ)).trans
    ((κ.fullDim.labelling.targetEdge.subtypeEquiv fun i ↦ by
      rw [Ne, Ne, Equiv.eq_symm_apply]).trans
      (foldEdgeEquiv (contracted := t' κ) rfl (fst_ne_snd (t' κ)) (hOne κ)))

/-- The columns of the drop, unfolded. -/
theorem colEquiv_apply (j : Fin p) : colEquiv κ hc j = (site κ hc).col
    ⟨κ.fullDim.labelling.targetEdge ((c₀ κ).succAbove j), fun h ↦ (c₀ κ).succAbove_ne j
      ((Equiv.eq_symm_apply _).mpr h)⟩ := rfl

/-- A marked branch vertex is `V` exactly when it is labelled by the new vertex. -/
theorem ident_vertex_eq_last_iff (B : MarkedBranchVertex κ.data (M κ)) :
    κ.ident.vertex B = Fin.last n ↔ B.1 = V κ := by
  constructor
  · intro h
    rw [← ident_VB κ] at h
    exact congrArg Subtype.val (κ.ident.vertex.injective h)
  · intro h
    rw [show B = VB κ from Subtype.ext h]
    exact ident_VB κ

/-- **The marked branch vertices of the drop**: labelled by the vertices of `core`. -/
noncomputable def vertexEquiv : MarkedBranchVertex (site κ hc).D (MD κ hc) ≃ Fin n :=
  ((site κ hc).branchEquiv (markHyp κ hc)).symm.trans
    ((κ.ident.vertex.subtypeEquiv fun B ↦ (ident_vertex_eq_last_iff κ B).not.symm).trans
      (finSuccAboveEquiv (Fin.last n)).symm)

/-- The label of a branch vertex of the drop, read on the old label. -/
theorem vertexEquiv_branchEquiv (B : {B : MarkedBranchVertex κ.data (M κ) // B.1 ≠ V κ}) :
    (vertexEquiv κ hc ((site κ hc).branchEquiv (markHyp κ hc) B)).castSucc = κ.ident.vertex B.1 := by
  unfold vertexEquiv
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  set X : {i : Fin (n + 1) // i ≠ Fin.last n} :=
    κ.ident.vertex.subtypeEquiv (fun B ↦ (ident_vertex_eq_last_iff κ B).not.symm) B
  have h : (Fin.last n).succAbove ((finSuccAboveEquiv (Fin.last n)).symm X) = X.1 :=
    congrArg Subtype.val ((finSuccAboveEquiv (Fin.last n)).apply_symm_apply X)
  rw [Fin.succAbove_last_apply] at h
  exact h

/-- **The incidences of the drop**: those of `core`. -/
theorem incidence (Bd : MarkedBranchVertex (site κ hc).D (MD κ hc)) (i : Fin p) :
    markedIncidenceCount (site κ hc).D (MD κ hc) Bd.1 ((rowEquiv κ hc).symm i) =
      coreIncidence core (vertexEquiv κ hc Bd) i := by
  obtain ⟨B, rfl⟩ := ((site κ hc).branchEquiv (markHyp κ hc)).surjective Bd
  have hBx : B.1.1.1.1 ≠ (site κ hc).x := (site κ hc).not_over_x (markHyp κ hc) B.1 B.2
  have hLabel := vertexEquiv_branchEquiv κ hc B
  rw [rowEquiv_symm, (site κ hc).branchEquiv_val]
  unfold rowOf
  by_cases hi : i = s
  · subst hi
    rw [← row_fc κ hc, (site κ hc).markedIncidenceCount_rowMap_fc (markHyp κ hc) hBx
      (row_fc_ne_fo κ hc), row_fc κ hc, row_fo κ hc, κ.ident.incidence, κ.ident.incidence,
      ← hLabel]
    exact coreIncidence_castSucc_split core i _
  · have hne : κ.ident.row.symm i.castSucc ≠ markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) := by
      rw [row_fc]; exact fun h ↦ hi (Fin.castSucc_injective _ (κ.ident.row.symm.injective h))
    have hne' : κ.ident.row.symm i.castSucc ≠ markedRow (M κ) ((site κ hc).fo (markHyp κ hc)) := by
      rw [row_fo]; exact fun h ↦ (Fin.castSucc_lt_last i).ne (κ.ident.row.symm.injective h)
    rw [(site κ hc).markedIncidenceCount_rowMap_of_ne (markHyp κ hc) hBx hne hne',
      κ.ident.incidence, ← hLabel]
    exact coreIncidence_castSucc_castSucc_of_ne core s _ hi

/-- The marks keep their labels. -/
theorem vertex_mark (j : Fin k) :
    vertexEquiv κ hc ⟨markSourceD κ hc j, Or.inr (mem_markSet _ j)⟩ = mark j := by
  have hB : (⟨markSourceD κ hc j, Or.inr (mem_markSet _ j)⟩ :
      MarkedBranchVertex (site κ hc).D (MD κ hc)) =
      (site κ hc).branchEquiv (markHyp κ hc)
        ⟨⟨κ.markSource j.castSucc, Or.inr (mem_markSet _ _)⟩,
          fun h ↦ markSource_castSucc_ne κ hc j (congrArg (fun X : κ.data.SourceVertex ↦ X.1.1) h)⟩ :=
        Subtype.ext rfl
  rw [hB]
  have h := vertexEquiv_branchEquiv κ hc ⟨⟨κ.markSource j.castSucc, Or.inr (mem_markSet _ _)⟩,
    fun h ↦ markSource_castSucc_ne κ hc j (congrArg (fun X : κ.data.SourceVertex ↦ X.1.1) h)⟩
  rw [κ.ident.vertex_mark, snocMark_castSucc] at h
  exact Fin.castSucc_injective _ h

/-! ## 5.  The labelling and the determinant -/

/-- **The labelling of the drop**: rows by `rowEquiv`, columns by `colEquiv`. -/
noncomputable def labelling : MarkedLabelling (site κ hc).D (MD κ hc) (Fin p) where
  targetEdge := colEquiv κ hc
  row := rowEquiv κ hc

/-- The entries of the drop. -/
theorem matrix_drop (i j : Fin p) :
    GluingDatum.LengthMatrixPresentation.matrix (labelling κ hc).presentation i j =
      markedMatrix (site κ hc).D (MD κ hc) (rowOf κ hc i) (colEquiv κ hc j) := by
  rw [MarkedLabelling.matrix_eq]
  change markedMatrix _ _ ((rowEquiv κ hc).symm i) _ = _
  rw [rowEquiv_symm]
  rfl

/-- The old labelling of rows. -/
abbrev L := κ.fullDim.labelling

/-- The entries of `κ`. -/
theorem matrix_old (r c : Fin (p + 1)) :
    κ.matrix r c = markedMatrix κ.data (M κ) ((L κ).row.symm r) ((L κ).targetEdge c) :=
  MarkedLabelling.matrix_eq _ r c

/-- The old row of the drop's row `i`: the row labelled `cs i`, and for `i = s` the row labelled
`last p`. -/
def oldSlot (s i : Fin p) : Fin (p + 1) := if i = s then Fin.last p else i.castSucc

/-- The old slot of a row of the drop is not `cs s`. -/
theorem oldSlot_ne (s i : Fin p) : oldSlot s i ≠ s.castSucc := by
  unfold oldSlot
  split_ifs with h
  · exact (Fin.castSucc_lt_last s).ne'
  · exact fun h' ↦ h (Fin.castSucc_injective _ h')

/-- The old slots are a bijection onto the slots other than `cs s`. -/
theorem oldSlot_bijective (s : Fin p) : Function.Bijective
    (fun i : Fin p ↦ (⟨oldSlot s i, oldSlot_ne s i⟩ : {ℓ : Fin (p + 1) // ℓ ≠ s.castSucc})) := by
  constructor
  · intro i j h
    have h' : oldSlot s i = oldSlot s j := congrArg Subtype.val h
    unfold oldSlot at h'
    by_cases hi : i = s <;> by_cases hj : j = s
    · rw [hi, hj]
    · rw [ite_eq_left hi, ite_eq_right hj] at h'; exact absurd h' (Fin.castSucc_lt_last j).ne'
    · rw [ite_eq_right hi, ite_eq_left hj] at h'; exact absurd h' (Fin.castSucc_lt_last i).ne
    · rw [ite_eq_right hi, ite_eq_right hj] at h'; exact Fin.castSucc_injective _ h'
  · rintro ⟨ℓ, hℓ⟩
    induction ℓ using Fin.lastCases with
    | last => exact ⟨s, Subtype.ext (by simp [oldSlot])⟩
    | cast i =>
      have hi : i ≠ s := fun h ↦ hℓ (h ▸ rfl)
      exact ⟨i, Subtype.ext (by simp [oldSlot, hi])⟩

/-- The old row of the merged row of the drop. -/
noncomputable abbrev r₁ : Fin (p + 1) := (L κ).row (κ.ident.row.symm s.castSucc)

/-- The old rows of the drop's rows, other than `r₁`. -/
noncomputable def θ : Fin p ≃ {r : Fin (p + 1) // r ≠ r₁ κ} :=
  (Equiv.ofBijective _ (oldSlot_bijective s)).trans
    ((κ.ident.row.symm.trans (L κ).row).subtypeEquiv fun ℓ ↦ by
      simp only [Equiv.trans_apply, r₁, ne_eq, EmbeddingLike.apply_eq_iff_eq])

/-- The value of `θ`. -/
theorem θ_val (i : Fin p) : (θ κ i).1 = (L κ).row (κ.ident.row.symm (oldSlot s i)) := rfl

/-- The index of the edges at `V`. -/
noncomputable abbrev m : ℕ := κ.data.sourceEdgeIndex ((site κ hc).fc (markHyp κ hc)).1

/-- The index at `V` is positive. -/
theorem m_pos : 0 < m κ hc := SheetPartition.blockCard_pos _ _

/-- The old column of the other edge at `x`. -/
noncomputable abbrev c₂ : Fin (p + 1) := (L κ).targetEdge.symm (site κ hc).other

/-- The other old row through `V`. -/
noncomputable abbrev r₂ : Fin (p + 1) := (L κ).row (κ.ident.row.symm (Fin.last p))

/-- The two old rows through `V` are distinct. -/
theorem r₁_ne_r₂ : r₁ κ ≠ r₂ κ := by
  intro h
  exact (Fin.castSucc_lt_last s).ne (κ.ident.row.symm.injective ((L κ).row.injective h))

/-- The two columns at `x` are distinct. -/
theorem c₂_ne_c₀ : c₂ κ hc ≠ c₀ κ := by
  intro h
  exact (site κ hc).other_ne ((L κ).targetEdge.symm.injective h)

/-- The merged row of the drop goes to the row `last p`. -/
theorem θ_s : (θ κ s).1 = r₂ κ := by rw [θ_val]; simp [oldSlot]

/-- **The entries of the drop**: its rows are the old rows, the merged row is the sum of the two
rows through `V`; its columns are the old columns other than `c₀`. -/
theorem matrix_drop_eq (i j : Fin p) :
    GluingDatum.LengthMatrixPresentation.matrix (labelling κ hc).presentation i j =
      κ.matrix (θ κ i).1 ((finSuccAboveEquiv (c₀ κ)) j).1 +
        if i = s then κ.matrix (r₁ κ) ((finSuccAboveEquiv (c₀ κ)) j).1 else 0 := by
  rw [matrix_drop, colEquiv_apply, θ_val, matrix_old, matrix_old, Equiv.symm_apply_apply]
  unfold rowOf
  simp only [finSuccAboveEquiv_apply]
  by_cases hi : i = s
  · subst hi
    rw [ite_eq_left rfl, Equiv.symm_apply_apply]
    rw [← row_fc κ hc, (site κ hc).markedMatrix_rowMap_fc (markHyp κ hc) (row_fc_ne_fo κ hc),
      row_fc κ hc, row_fo κ hc]
    simp only [oldSlot, ite_true]
    ring
  · rw [ite_eq_right hi, add_zero]
    have hne : κ.ident.row.symm i.castSucc ≠ markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) := by
      rw [row_fc]; exact fun h ↦ hi (Fin.castSucc_injective _ (κ.ident.row.symm.injective h))
    have hne' : κ.ident.row.symm i.castSucc ≠
        markedRow (M κ) ((site κ hc).fo (markHyp κ hc)) := by
      rw [row_fo]; exact fun h ↦ (Fin.castSucc_lt_last i).ne (κ.ident.row.symm.injective h)
    rw [(site κ hc).markedMatrix_rowMap_of_ne (markHyp κ hc) hne hne']
    simp only [oldSlot, hi, ite_false]

/-- **The two columns at `x`**: they agree off the rows through `V`, where they differ by `±1/m`. -/
theorem matrix_col (r : Fin (p + 1)) :
    κ.matrix r (c₀ κ) - κ.matrix r (c₂ κ hc) =
      (1 : ℚ) / m κ hc * ((if r = r₁ κ then 1 else 0) - (if r = r₂ κ then 1 else 0)) := by
  have h := (site κ hc).markedMatrix_c_add (markHyp κ hc) ((L κ).row.symm r)
  rw [matrix_old, matrix_old, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hc₁ : markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) = (L κ).row.symm r ↔ r = r₁ κ := by
    rw [row_fc, Equiv.eq_symm_apply, eq_comm]
  have hc₂ : markedRow (M κ) ((site κ hc).fo (markHyp κ hc)) = (L κ).row.symm r ↔ r = r₂ κ := by
    rw [row_fo, Equiv.eq_symm_apply, eq_comm]
  simp only [hc₁, hc₂] at h
  change markedMatrix κ.data (M κ) ((L κ).row.symm r) (site κ hc).c -
    markedMatrix κ.data (M κ) ((L κ).row.symm r) (site κ hc).other = _
  split_ifs at h ⊢ <;> linarith

/-- **The determinant of the drop** (`DropDet.abs_det_eq_of_merge`): `|det A_κ| = |det A_drop| / m`. -/
theorem abs_det : |κ.matrix.det| = |(1 : ℚ) / m κ hc| *
    |(GluingDatum.LengthMatrixPresentation.matrix (labelling κ hc).presentation).det| :=
  abs_det_eq_of_merge κ.matrix _ (r₁_ne_r₂ κ) (c₂_ne_c₀ κ hc) (θ κ) (finSuccAboveEquiv (c₀ κ))
    (i₀ := s) (θ_s κ) _ (matrix_drop_eq κ hc) (matrix_col κ hc)

/-- (D3) for the drop. -/
theorem det_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling κ hc).presentation).det ≠ 0 := by
  intro h
  have h' := abs_det κ hc
  rw [h, abs_zero, mul_zero, abs_eq_zero] at h'
  exact κ.det_ne_zero h'

/-! ## 6.  The remaining fields -/

/-- Adding a mark of type `0` lowers the type excess by one. -/
theorem typeExcess_snoc : typeExcess (snocType types 0) = typeExcess types - 1 := by
  unfold typeExcess
  rw [Fin.sum_univ_castSucc]
  simp only [snocType_castSucc, snocType_last]
  push_cast
  ring

/-- The dimension count of the drop. -/
theorem saturated :
    ((site κ hc).T'.edges.card : ℤ) + typeExcess types =
      2 * genus (site κ hc).D.sourceGraph + 2 * degree - 5 := by
  have hSat := κ.fullDim.saturated
  have hCard := GraphContraction.card_edges_contract κ.target (fst_ne_snd (t' κ)) (hOne κ)
  have hPos : 1 ≤ Multiset.card κ.target.edges :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨_, Multiset.coe_mem (x := t' κ)⟩
  rw [(site κ hc).genus_sourceGraph]
  rw [typeExcess_snoc] at hSat
  change ((Multiset.card (GraphContraction.contract κ.target (fst_ne_snd (t' κ)) (hOne κ)).edges :
    ℕ) : ℤ) + _ = _
  rw [hCard, Nat.cast_sub hPos]
  change ((Multiset.card κ.target.edges : ℕ) : ℤ) + _ = _ at hSat
  push_cast
  linarith

/-- Trivalence of the drop. -/
theorem trivalent (Y' : (site κ hc).D.SourceVertex) : nonDanglingValency (site κ hc).D Y' ≤ 3 := by
  obtain ⟨Y, hYx, rfl⟩ := (site κ hc).exists_vmap_eq Y'
  rw [(site κ hc).nonDanglingValency_vmap hYx]
  exact κ.fullDim.trivalent Y

/-- The marks of the drop have surviving valency two. -/
theorem markValency (Y' : (site κ hc).D.SourceVertex) (hY' : Y' ∈ MD κ hc) :
    nonDanglingValency (site κ hc).D Y' = 2 := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hY'
  unfold markSourceD
  rw [(site κ hc).nonDanglingValency_vmap (markSource_castSucc_ne κ hc j)]
  exact κ.fullDim.markValency _ (mem_markSet _ _)

/-- A slot of the subdivided core has an end other than the new vertex. -/
theorem exists_end_ne_last (ℓ : Fin (p + 1)) :
    ∃ u : Fin n, 1 ≤ coreIncidence (subdivide core s) u.castSucc ℓ := by
  induction ℓ using Fin.lastCases with
  | last =>
    refine ⟨core.head s, ?_⟩
    unfold coreIncidence
    rw [subdivide_head_last]
    simp
  | cast i =>
    refine ⟨core.tail i, ?_⟩
    unfold coreIncidence
    rw [subdivide_tail_castSucc]
    simp

/-- **Path ends of the drop**: every row of the drop has an end at a branch vertex other than
`V`, read off the identification of `κ`. -/
theorem pathEnds : HasMarkedPathEnds (site κ hc).D (MD κ hc) := by
  intro g
  obtain ⟨e, rfl⟩ := (site κ hc).ndMap_surjective g
  obtain ⟨u, hu⟩ := exists_end_ne_last (s := s) (κ.ident.row (markedRow (M κ) e))
  set B := κ.ident.vertex.symm u.castSucc
  have hBV : B.1 ≠ V κ := by
    intro h
    have := (ident_vertex_eq_last_iff κ B).mpr h
    rw [Equiv.apply_symm_apply] at this
    exact (Fin.castSucc_lt_last u).ne this
  have hBx : B.1.1.1 ≠ (site κ hc).x := (site κ hc).not_over_x (markHyp κ hc) B hBV
  have hCount := κ.ident.incidence B (κ.ident.row (markedRow (M κ) e))
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at hCount
  rw [← hCount] at hu
  obtain ⟨e', he'⟩ := Finset.card_pos.mp hu
  obtain ⟨he'Inc, he'Row⟩ := Finset.mem_filter.mp he'
  rw [StablePathCount.mem_incidentEdges] at he'Inc
  refine ⟨(site κ hc).ndMap e', (site κ hc).vmap B.1, ?_, ?_, ?_⟩
  · change (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) e') =
      (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) e)
    rw [he'Row]
  · exact (site κ hc).incident_edgeMap hBx he'Inc
  · rcases B.2 with h | h
    · left
      rw [(site κ hc).nonDanglingValency_vmap hBx]
      omega
    · right
      exact ((markHyp κ hc).marks _ hBx).mpr h

/-- (D4′) at the old marks. -/
theorem typed (j : Fin k) : IsTyped (site κ hc).D (markSourceD κ hc j) (types j) := by
  have h := κ.typed j.castSucc
  rw [snocType_castSucc] at h
  unfold markSourceD
  unfold IsTyped at h ⊢
  rw [(site κ hc).markRamification_vmap (markSource_castSucc_ne κ hc j),
    (site κ hc).markIndex_vmap (markSource_castSucc_ne κ hc j)]
  exact h

end DropSmooth

open DropSmooth in
/-- **The drop of a typed frame** (I1, request-free): see the module docstring. -/
noncomputable def dropFrame' (hc : IsMarkedCubic core mark) {s : Fin p}
    (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree) :
    TypedFrame core mark types degree where
  target := (site κ hc).T'
  data := (site κ hc).D
  markSource := markSourceD κ hc
  fullDim :=
    { valid := (site κ hc).valid κ.fullDim.valid
      targetConnected := GraphContraction.graph_connected_contract κ.target _ (hOne κ)
        κ.fullDim.targetConnected
      targetGenus := (GraphContraction.genus_contract κ.target _ (hOne κ)).trans
        κ.fullDim.targetGenus
      saturated := saturated κ hc
      labelling := labelling κ hc
      det_ne_zero := det_ne_zero κ hc
      trivalent := trivalent κ hc
      markValency := markValency κ hc
      pathEnds := pathEnds κ hc }
  ident :=
    { vertex := vertexEquiv κ hc
      row := rowEquiv κ hc
      incidence := incidence κ hc
      vertex_mark := vertex_mark κ hc }
  typed := typed κ hc


/-! ## 7.  The coordinates of the drop (I3) -/

namespace DropSmooth

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
variable {s : Fin p} (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)
  (hc : IsMarkedCubic core mark)

/-- **The coordinates of the drop**: those of `κ` off the contracted column, with the contracted
coordinate added to the merged column. -/
noncomputable def dropCoords (z : Fin (p + 1) → ℚ) : Fin p → ℚ := fun j ↦
  z ((c₀ κ).succAbove j) + if (c₀ κ).succAbove j = c₂ κ hc then z (c₀ κ) else 0

/-- A row of `κ` against the coordinates of the drop. -/
theorem rowSum (z : Fin (p + 1) → ℚ) (r : Fin (p + 1)) :
    ∑ j, κ.matrix r ((c₀ κ).succAbove j) * dropCoords κ hc z j =
      κ.matrix.mulVec z r - (κ.matrix r (c₀ κ) - κ.matrix r (c₂ κ hc)) * z (c₀ κ) := by
  obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq (c₂_ne_c₀ κ hc)
  have hInj : Function.Injective (c₀ κ).succAbove := Fin.succAbove_right_injective
  have hSingle : ∑ j, κ.matrix r ((c₀ κ).succAbove j) *
      (if (c₀ κ).succAbove j = c₂ κ hc then z (c₀ κ) else 0) =
        κ.matrix r (c₂ κ hc) * z (c₀ κ) := by
    rw [Finset.sum_eq_single j₀]
    · rw [hj₀, ite_eq_left rfl]
    · intro j _ hj
      rw [ite_eq_right (fun h ↦ hj (hInj (h.trans hj₀.symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  unfold dropCoords
  simp only [mul_add, Finset.sum_add_distrib, hSingle]
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succAbove _ (c₀ κ)]
  ring

/-- **The coordinates of the drop at the merged request.** -/
theorem coordsAt_dropFrame' (y : Fin (p + 1) → ℚ) :
    (dropFrame' hc κ).coordsAt (mergeRequest s y) = dropCoords κ hc (κ.coordsAt y) := by
  refine (dropFrame' hc κ).coordsAt_eq_of_mulVec _ _ ?_
  funext i
  have hSlot : (dropFrame' hc κ).slot i = i := by
    change (rowEquiv κ hc) ((rowEquiv κ hc).symm i) = i
    exact Equiv.apply_symm_apply _ _
  rw [hSlot]
  have hAz := κ.mulVec_coordsAt y
  change ∑ j, GluingDatum.LengthMatrixPresentation.matrix (labelling κ hc).presentation i j *
    dropCoords κ hc (κ.coordsAt y) j = _
  simp only [matrix_drop_eq κ hc, finSuccAboveEquiv_apply, add_mul, Finset.sum_add_distrib]
  rw [rowSum κ hc]
  have hθ₁ : (θ κ i).1 ≠ r₁ κ := (θ κ i).2
  have hθ₂ : (θ κ i).1 = r₂ κ ↔ i = s := by
    constructor
    · intro h
      rw [← θ_s κ] at h
      exact (θ κ).injective (Subtype.ext h)
    · rintro rfl; exact θ_s κ
  rw [matrix_col κ hc, hAz]
  have hySlot : ∀ ℓ : Fin (p + 1), (fun row ↦ y (κ.slot row)) ((L κ).row (κ.ident.row.symm ℓ)) =
      y ℓ := by
    intro ℓ
    change y (κ.ident.row ((L κ).row.symm ((L κ).row (κ.ident.row.symm ℓ)))) = y ℓ
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  by_cases hi : i = s
  · subst hi
    have hSum : ∑ j, (if i = i then κ.matrix (r₁ κ) ((c₀ κ).succAbove j) else 0) *
        dropCoords κ hc (κ.coordsAt y) j =
        ∑ j, κ.matrix (r₁ κ) ((c₀ κ).succAbove j) * dropCoords κ hc (κ.coordsAt y) j := by
      simp
    have h22 : (θ κ i).1 = r₂ κ := hθ₂.mpr rfl
    rw [hSum, rowSum κ hc, matrix_col κ hc, hAz, θ_val, hySlot, hySlot]
    rw [θ_val] at hθ₁ h22
    simp only [oldSlot, ite_true] at hθ₁ h22 ⊢
    simp only [hθ₁, r₁_ne_r₂ κ, ite_false]
    unfold mergeRequest
    simp only [ite_true]
    ring
  · have hSum : ∑ j, (if i = s then κ.matrix (r₁ κ) ((c₀ κ).succAbove j) else 0) *
        dropCoords κ hc (κ.coordsAt y) j = 0 := by
      simp [hi]
    have h22 : ¬ (θ κ i).1 = r₂ κ := mt hθ₂.mp hi
    rw [hSum, θ_val, hySlot]
    rw [θ_val] at hθ₁ h22
    simp only [oldSlot, hi, ite_false] at hθ₁ h22 ⊢
    simp only [hθ₁, h22, ite_false]
    unfold mergeRequest
    simp only [hi, ite_false]
    ring

/-- **I3: openness passes to the drop.** -/
theorem openAt_dropFrame' {y : Fin (p + 1) → ℚ} (hOpen : κ.OpenAt y) :
    (dropFrame' hc κ).OpenAt (mergeRequest s y) := by
  intro j
  rw [coordsAt_dropFrame']
  unfold dropCoords
  have h₁ := hOpen ((c₀ κ).succAbove j)
  have h₂ := hOpen (c₀ κ)
  split_ifs <;> linarith

end DropSmooth

/-! ## 8.  The multiplicity of the drop (I4) -/

namespace DropSmooth

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
variable {s : Fin p} (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)
  (hc : IsMarkedCubic core mark)

/-- **The ramified leaf images correspond.** -/
theorem card_ramifiedLeafImages :
    (dropFrame' hc κ).ramifiedLeafImages.card = κ.ramifiedLeafImages.card := by
  classical
  unfold TypedFrame.ramifiedLeafImages
  symm
  refine Finset.card_bij (fun u _ ↦ fold κ.target (fst_ne_snd (t' κ)) u) ?_ ?_ ?_
  · intro u hu
    obtain ⟨hImg, hLeaf⟩ := Finset.mem_filter.mp hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hImg
    have hiPos := (Finset.mem_filter.mp hi).2
    induction i using Fin.lastCases with
    | last => rw [snocType_last] at hiPos; exact absurd hiPos (lt_irrefl 0)
    | cast j =>
      rw [snocType_castSucc] at hiPos
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hiPos⟩, rfl⟩, ?_⟩
      exact ((site κ hc).isLeafVertex_fold_iff (markSource_castSucc_ne κ hc j)).mpr hLeaf
  · intro u₁ hu₁ u₂ hu₂ h
    have hL₁ := (Finset.mem_filter.mp hu₁).2
    have hL₂ := (Finset.mem_filter.mp hu₂).2
    have hu₁x : u₁ ≠ (site κ hc).x := fun h ↦ (site κ hc).not_isLeafVertex_x (h ▸ hL₁)
    have hu₂x : u₂ ≠ (site κ hc).x := fun h ↦ (site κ hc).not_isLeafVertex_x (h ▸ hL₂)
    rcases (GraphContraction.fold_eq_fold_iff κ.target (fst_ne_snd (t' κ)) u₁ u₂).mp h with
      h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact h
    · rcases (site κ hc).c_ends with h' | h'
      · exact absurd (h₁.trans h'.1) hu₁x
      · exact absurd (h₂.trans h'.2) hu₂x
    · rcases (site κ hc).c_ends with h' | h'
      · exact absurd (h₂.trans h'.1) hu₂x
      · exact absurd (h₁.trans h'.2) hu₁x
  · intro y hy
    obtain ⟨hImg, hLeaf⟩ := Finset.mem_filter.mp hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hImg
    have hjPos := (Finset.mem_filter.mp hj).2
    refine ⟨(κ.markSource j.castSucc).1.1, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨j.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [snocType_castSucc]; exact hjPos⟩,
        rfl⟩, ((site κ hc).isLeafVertex_fold_iff (markSource_castSucc_ne κ hc j)).mp hLeaf⟩, rfl⟩

/-- `l*` is unchanged. -/
theorem leafCountStar_eq : (dropFrame' hc κ).leafCountStar = κ.leafCountStar := by
  unfold TypedFrame.leafCountStar
  rw [card_ramifiedLeafImages]
  congr 1
  exact (site κ hc).leafCount_contract

/-- **Away from the merged row, the row denominators agree.** -/
theorem rowDenominator_of_ne {i : Fin p} (hi : i ≠ s) :
    Count.rowDenominator κ.fullDim.labelling.presentation (θ κ i).1 =
      Count.rowDenominator (labelling κ hc).presentation i := by
  have hθ₁ : (θ κ i).1 ≠ r₁ κ := (θ κ i).2
  have hθ₂ : (θ κ i).1 ≠ r₂ κ := by
    intro h
    rw [← θ_s κ] at h
    exact hi ((θ κ).injective (Subtype.ext h))
  obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq (c₂_ne_c₀ κ hc)
  have hB : ∀ j, GluingDatum.LengthMatrixPresentation.matrix (labelling κ hc).presentation i j =
      κ.matrix (θ κ i).1 ((c₀ κ).succAbove j) := by
    intro j
    rw [matrix_drop_eq, ite_eq_right hi, add_zero, finSuccAboveEquiv_apply]
  unfold Count.rowDenominator
  apply Nat.dvd_antisymm
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun c _ ↦ ?_
    by_cases hc₀ : c = c₀ κ
    · have hcol := matrix_col κ hc (θ κ i).1
      rw [ite_eq_right hθ₁, ite_eq_right hθ₂, sub_self, mul_zero, sub_eq_zero] at hcol
      rw [hc₀]
      change (κ.matrix (θ κ i).1 (c₀ κ)).den ∣ _
      rw [hcol, ← hj₀, ← hB]
      exact den_dvd_commonDenominator _ _ (Finset.mem_univ _)
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hc₀
      change (κ.matrix (θ κ i).1 ((c₀ κ).succAbove j)).den ∣ _
      rw [← hB]
      exact den_dvd_commonDenominator _ _ (Finset.mem_univ _)
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun j _ ↦ ?_
    rw [hB]
    exact den_dvd_commonDenominator _ _ (Finset.mem_univ _)

/-! ### The denominator step, through the regrowth (modules `DenomRegrow`, `DenomRow`, `DenomDrop`) -/

/-- The merged row of the drop is the image of the row `cs s` through `V`. -/
theorem rowOf_s_eq : rowOf κ hc s =
    (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) ((site κ hc).fc (markHyp κ hc))) := by
  unfold rowOf
  rw [row_fc]

/-- The merged row of the drop is labelled `s`. -/
theorem labelling_row_rowOf_s : (labelling κ hc).row (rowOf κ hc s) = s := by
  change rowEquiv κ hc (rowOf κ hc s) = s
  rw [← rowEquiv_symm, Equiv.apply_symm_apply]

/-- The old row `r₁` is the row of the occurrence over `t'` at `V`. -/
theorem r₁_eq_row_fc : r₁ κ = (L κ).row (markedRow (M κ) ((site κ hc).fc (markHyp κ hc))) := by
  rw [row_fc]

/-- The old row `r₂` is the row of the other occurrence at `V`. -/
theorem r₂_eq_row_fo : r₂ κ = (L κ).row (markedRow (M κ) ((site κ hc).fo (markHyp κ hc))) := by
  rw [row_fo]

/-- Every index on a row of the drop divides its denominator; at the merged row, the
denominator `d(h)`. -/
theorem index_dvd_rowDenominator_drop (G : NonDanglingEdge (site κ hc).D)
    (hG : markedRow (MD κ hc) G = rowOf κ hc s) :
    (site κ hc).D.sourceEdgeIndex G.1 ∣ Count.rowDenominator (labelling κ hc).presentation s := by
  have h := DenomRegrow.index_dvd_rowDenominator (dropFrame' hc κ) hc G
  change (site κ hc).D.sourceEdgeIndex G.1 ∣ Count.rowDenominator (labelling κ hc).presentation
    ((labelling κ hc).row (markedRow (MD κ hc) G)) at h
  rwa [hG, labelling_row_rowOf_s] at h

/-- The merged row's denominator divides every common multiple of its indices. -/
theorem rowDenominator_drop_dvd {N : ℕ}
    (h : ∀ G : NonDanglingEdge (site κ hc).D, markedRow (MD κ hc) G = rowOf κ hc s →
      (site κ hc).D.sourceEdgeIndex G.1 ∣ N) :
    Count.rowDenominator (labelling κ hc).presentation s ∣ N := by
  have h' := DenomRegrow.rowDenominator_dvd_of_forall (dropFrame' hc κ) (rowOf κ hc s) h
  change Count.rowDenominator (labelling κ hc).presentation ((labelling κ hc).row (rowOf κ hc s)) ∣ N
    at h'
  rwa [labelling_row_rowOf_s] at h'

/-- The occurrences of the two rows through `V` go to the merged row. -/
theorem markedRow_ndMap_of_mem {F : NonDanglingEdge κ.data}
    (hF : markedRow (M κ) F = markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) ∨
      markedRow (M κ) F = markedRow (M κ) ((site κ hc).fo (markHyp κ hc))) :
    markedRow (MD κ hc) ((site κ hc).ndMap F) = rowOf κ hc s := by
  rw [rowOf_s_eq]
  exact ((site κ hc).rowMap_eq_fc_iff (markHyp κ hc) _).mpr hF

/-- Every occurrence of the merged row comes from one of the two rows through `V`. -/
theorem exists_of_markedRow_drop {G : NonDanglingEdge (site κ hc).D}
    (hG : markedRow (MD κ hc) G = rowOf κ hc s) :
    ∃ F : NonDanglingEdge κ.data, (site κ hc).ndMap F = G ∧
      (markedRow (M κ) F = markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) ∨
        markedRow (M κ) F = markedRow (M κ) ((site κ hc).fo (markHyp κ hc))) := by
  obtain ⟨F, rfl⟩ := (site κ hc).ndMap_surjective G
  refine ⟨F, rfl, ((site κ hc).rowMap_eq_fc_iff (markHyp κ hc) _).mp ?_⟩
  rw [← rowOf_s_eq]
  exact hG

/-- The surviving-edge map keeps indices. -/
theorem sourceEdgeIndex_ndMap (F : NonDanglingEdge κ.data) :
    (site κ hc).D.sourceEdgeIndex ((site κ hc).ndMap F).1 = κ.data.sourceEdgeIndex F.1 :=
  (site κ hc).sourceEdgeIndex_edgeMap F.1

/-- **One side constant**: if every index on the row `h'` is `m`, then `d(h') = m` and
`d(h'') = d(h)`; symmetrically for `h''`. Stated for a side `P` through `V` (with occurrence `f`
at `V`) and the other side `Q` (with occurrence `g` at `V`). -/
theorem split_of_constant (f g : NonDanglingEdge κ.data)
    (hf : κ.data.sourceEdgeIndex f.1 = m κ hc) (hg : κ.data.sourceEdgeIndex g.1 = m κ hc)
    (hfg : ∀ F : NonDanglingEdge κ.data,
      (markedRow (M κ) F = markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) ∨
        markedRow (M κ) F = markedRow (M κ) ((site κ hc).fo (markHyp κ hc))) ↔
      (markedRow (M κ) F = markedRow (M κ) f ∨ markedRow (M κ) F = markedRow (M κ) g))
    (hConst : ∀ F : NonDanglingEdge κ.data, markedRow (M κ) F = markedRow (M κ) f →
      κ.data.sourceEdgeIndex F.1 = m κ hc) :
    Count.rowDenominator κ.fullDim.labelling.presentation ((L κ).row (markedRow (M κ) f)) =
        m κ hc ∧
      Count.rowDenominator κ.fullDim.labelling.presentation ((L κ).row (markedRow (M κ) g)) =
        Count.rowDenominator (labelling κ hc).presentation s := by
  have hc' := isMarkedCubic_snoc hc s
  refine ⟨Nat.dvd_antisymm ?_ ?_, Nat.dvd_antisymm ?_ ?_⟩
  · refine DenomRegrow.rowDenominator_dvd_of_forall κ _ fun F hF ↦ ?_
    rw [hConst F hF]
  · rw [← hf]
    exact DenomRegrow.index_dvd_rowDenominator κ hc' f
  · refine DenomRegrow.rowDenominator_dvd_of_forall κ _ fun F hF ↦ ?_
    rw [← sourceEdgeIndex_ndMap κ hc F]
    exact index_dvd_rowDenominator_drop κ hc _
      (markedRow_ndMap_of_mem κ hc ((hfg F).mpr (Or.inr hF)))
  · refine rowDenominator_drop_dvd κ hc fun G hG ↦ ?_
    obtain ⟨F, rfl, hF⟩ := exists_of_markedRow_drop κ hc hG
    rw [sourceEdgeIndex_ndMap]
    rcases (hfg F).mp hF with hF | hF
    · rw [hConst F hF, ← hg]
      exact DenomRegrow.index_dvd_rowDenominator κ hc' g
    · rw [← hF]
      exact DenomRegrow.index_dvd_rowDenominator κ hc' F

/-- **The denominator step**: at the merged row,
`d(h') d(h'') = m · d(h)`, where `h', h''` are the two rows through `V` (old rows `r₁`, `r₂`), `h`
their merged row (row `s` of the drop) and `m` the index of the two edges at `V`.

*Proof sketch.* By Part II `proposition-at-most-two-weights` read on the merged row `h` of the drop:
`h` passes above a leaf (then every index on it is `1`, all three denominators are `1`, and
`m = 1`), or its indices are constant `k` (then `d(h) = d(h') = d(h'') = k = m`, each of `h', h''`
having the simple column of its half of the split edge), or they are `k^μ (k+1)^ν` along the row
with one transition (then the piece of `h` cut at `V` not containing the transition has the single
index `m`, the other piece has both indices, so `{d(h'), d(h'')} = {m, k(k+1)}` and
`d(h) = k(k+1)`).

*Proof.* The profile is read on the marked rows through an unmarked regrowth of each frame
(module `DenomRegrow`: a caterpillar tail at every mark, with `c j = types j + 1`, one ascent, in
degree `degree + k`; the generic `CatRegrow` construction without its degree hypothesis
`IsTailDegree`). There (module `DenomRow`) the row denominator of a marked row is the lcm of its
indices (`index_dvd_rowDenominator`, `rowDenominator_dvd_of_forall`), two different indices on a
row force a jump (`exists_isJump`), and a row has at most one jump (`isJump_unique`). Jumps of `h'`
and of `h''` would be two distinct jumps of `h` (module `DenomDrop`: `isJump_vmap`), so one of
`h'`, `h''` carries the single index `m` (both contain an occurrence at `V`, of index `m`); then
`split_of_constant` gives `d = m` on that side and `d(h)` on the other. -/
theorem rowDenominator_split :
    Count.rowDenominator κ.fullDim.labelling.presentation (r₁ κ) *
        Count.rowDenominator κ.fullDim.labelling.presentation (r₂ κ) =
      m κ hc * Count.rowDenominator (labelling κ hc).presentation s := by
  have hc' := isMarkedCubic_snoc hc s
  have hfc : κ.data.sourceEdgeIndex ((site κ hc).fc (markHyp κ hc)).1 = m κ hc := rfl
  have hfo : κ.data.sourceEdgeIndex ((site κ hc).fo (markHyp κ hc)).1 = m κ hc :=
    (site κ hc).sourceEdgeIndex_fo (markHyp κ hc)
  rw [r₁_eq_row_fc κ hc, r₂_eq_row_fo κ hc]
  by_cases h₁ : ∀ F : NonDanglingEdge κ.data,
      markedRow (M κ) F = markedRow (M κ) ((site κ hc).fc (markHyp κ hc)) →
        κ.data.sourceEdgeIndex F.1 = m κ hc
  · obtain ⟨hd₁, hd₂⟩ := split_of_constant κ hc _ _ hfc hfo (fun _ ↦ Iff.rfl) h₁
    rw [hd₁, hd₂]
  by_cases h₂ : ∀ F : NonDanglingEdge κ.data,
      markedRow (M κ) F = markedRow (M κ) ((site κ hc).fo (markHyp κ hc)) →
        κ.data.sourceEdgeIndex F.1 = m κ hc
  · obtain ⟨hd₂, hd₁⟩ := split_of_constant κ hc _ _ hfo hfc (fun _ ↦ Or.comm) h₂
    rw [hd₁, hd₂, mul_comm]
  exfalso
  push Not at h₁ h₂
  obtain ⟨F₁, hF₁, hne₁⟩ := h₁
  obtain ⟨F₂, hF₂, hne₂⟩ := h₂
  obtain ⟨Y₁, hY₁⟩ := DenomRegrow.exists_isJump κ hc' hF₁ rfl (hfc ▸ hne₁)
  obtain ⟨Y₂, hY₂⟩ := DenomRegrow.exists_isJump κ hc' hF₂ rfl (hfo ▸ hne₂)
  have hJ₁ := (site κ hc).isJump_vmap (markHyp κ hc) hY₁
  have hJ₂ := (site κ hc).isJump_vmap (markHyp κ hc) hY₂
  have hRow : (site κ hc).rowMap (markHyp κ hc)
      (markedRow (M κ) ((site κ hc).fo (markHyp κ hc))) =
      (site κ hc).rowMap (markHyp κ hc) (markedRow (M κ) ((site κ hc).fc (markHyp κ hc))) :=
    ((site κ hc).rowMap_eq_fc_iff (markHyp κ hc) _).mpr (Or.inr rfl)
  rw [hRow] at hJ₂
  have hEq : (site κ hc).vmap Y₁ = (site κ hc).vmap Y₂ :=
    DenomRegrow.isJump_unique (dropFrame' hc κ) hc hJ₁ hJ₂
  have hY : Y₁ = Y₂ := ((site κ hc).vmap_inj ((site κ hc).not_over_x_of_isJump hY₁)
    ((site κ hc).not_over_x_of_isJump hY₂)).mp hEq
  subst hY
  obtain ⟨hYm, hY2, G₁, -, hG₁, hG₁I, -, -⟩ := hY₁
  obtain ⟨-, -, G₂, -, hG₂, hG₂I, -, -⟩ := hY₂
  have h := DenomRegrow.markedRow_eq_of_incident κ hYm hY2 hG₁I hG₂I
  rw [hG₁, hG₂] at h
  exact row_fc_ne_fo κ hc h

/-- **The denominators**: `D_κ = m · D_drop`. -/
theorem denominatorProduct_eq :
    Count.denominatorProduct κ.fullDim.labelling.presentation =
      m κ hc * Count.denominatorProduct (labelling κ hc).presentation := by
  classical
  unfold Count.denominatorProduct
  -- split off `r₁` and reindex the rest by `θ`
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (r₁ κ))]
  have hRest : ∏ r ∈ Finset.univ.erase (r₁ κ),
      Count.rowDenominator κ.fullDim.labelling.presentation r =
        ∏ i, Count.rowDenominator κ.fullDim.labelling.presentation (θ κ i).1 := by
    refine Finset.prod_nbij' (fun r ↦ if h : r = r₁ κ then s else (θ κ).symm ⟨r, h⟩)
      (fun i ↦ (θ κ i).1) ?_ ?_ ?_ ?_ ?_
    · intro r _; exact Finset.mem_univ _
    · intro i _; exact Finset.mem_erase.mpr ⟨(θ κ i).2, Finset.mem_univ _⟩
    · intro r hr
      have hr' := (Finset.mem_erase.mp hr).1
      simp only [hr', dite_false, Equiv.apply_symm_apply]
    · intro i _
      have hi : (θ κ i).1 ≠ r₁ κ := (θ κ i).2
      simp only [hi, dite_false]
      exact (θ κ).symm_apply_apply i
    · intro r hr
      have hr' := (Finset.mem_erase.mp hr).1
      simp only [hr', dite_false, Equiv.apply_symm_apply]
  rw [hRest, ← Finset.prod_erase_mul _ _ (Finset.mem_univ s),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ s)]
  have hOff : ∏ i ∈ Finset.univ.erase s,
      Count.rowDenominator κ.fullDim.labelling.presentation (θ κ i).1 =
        ∏ i ∈ Finset.univ.erase s, Count.rowDenominator (labelling κ hc).presentation i :=
    Finset.prod_congr rfl fun i hi ↦ rowDenominator_of_ne κ hc (Finset.mem_erase.mp hi).1
  rw [hOff, θ_s κ]
  have hSplit := rowDenominator_split κ hc
  calc (∏ i ∈ Finset.univ.erase s, Count.rowDenominator (labelling κ hc).presentation i) *
        Count.rowDenominator κ.fullDim.labelling.presentation (r₂ κ) *
        Count.rowDenominator κ.fullDim.labelling.presentation (r₁ κ)
      = (∏ i ∈ Finset.univ.erase s, Count.rowDenominator (labelling κ hc).presentation i) *
          (Count.rowDenominator κ.fullDim.labelling.presentation (r₁ κ) *
            Count.rowDenominator κ.fullDim.labelling.presentation (r₂ κ)) := by ring
    _ = _ := by rw [hSplit]; ring

/-- **I4: the drop keeps the multiplicity.** -/
theorem typedAbsMult_dropFrame' : (dropFrame' hc κ).typedAbsMult = κ.typedAbsMult := by
  unfold TypedFrame.typedAbsMult TypedFrame.typedSignedMult
  rw [leafCountStar_eq, abs_mul, abs_mul]
  change _ * |(GluingDatum.LengthMatrixPresentation.matrix (labelling κ hc).presentation).det| =
    _ * |κ.matrix.det|
  rw [abs_det κ hc]
  change |((Count.denominatorProduct (labelling κ hc).presentation : ℕ) : ℚ) / _| * _ =
    |((Count.denominatorProduct κ.fullDim.labelling.presentation : ℕ) : ℚ) / _| * _
  rw [denominatorProduct_eq κ hc]
  have hm : (0 : ℚ) < m κ hc := by exact_mod_cast m_pos κ hc
  push_cast
  rw [mul_div_assoc, abs_mul, abs_div (1 : ℚ), abs_one, abs_of_pos hm]
  field_simp

end DropSmooth

end DraismaVargas.Count.MarkedCountGeneral
