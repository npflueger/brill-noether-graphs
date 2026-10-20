module

public import DraismaVargasMarkedCount.MarkedCountGeneral.LiftDatum
public import DraismaVargasMarkedCount.MarkedCountGeneral.LiftWalk

@[expose] public section

/-!
# The drop lemma: the lift of a typed frame at a position (I5)

A typed frame `κ` over `core` and a slot `s`: walk the marked row labelled `s` from the branch
vertex labelled `tail s` (`MarkedWalk`, start `ê₀` at `A₀`). A **position** `P` is an index `i` of
the walk, up to its stop. At a position, subdivide the target edge `t` of the `i`-th occurrence `g`
at its entry end `w` (module `LiftDatum`), and put the new mark `V'` over the new vertex `x'` in the
sheet of `g`; the old marks are lifted to the retained copies (`liftV`).

This module: the marks, the marked setting of module `DropRows` (`markHyp`), the contraction
isomorphism read on marks (`hMarksι`), the transported walk and the **side setup** of module
`DropSide` (`sideSetup`), whence the two rows through `V'` are distinct (`row_fc_ne_fo`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction
open DraismaVargas.Count.MarkedCountGeneral.MarkedWalk
open Utilities.Certificate.ExplicitPotential (Core)

namespace LiftSmooth

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  (s : Fin p) (κ : TypedFrame core mark types degree)

/-! ## 1.  The walk of the row `s` from `tail s` -/

/-- The marks of `κ`. -/
abbrev M : Finset κ.data.SourceVertex := markSet κ.markSource

/-- The branch vertex labelled `tail s`. -/
noncomputable abbrev B₀ : MarkedBranchVertex κ.data (M κ) := κ.ident.vertex.symm (core.tail s)

/-- The row `s` has an occurrence at the branch vertex labelled `tail s`. -/
theorem exists_start : ∃ e : NonDanglingEdge κ.data, Incident κ.data e.1 (B₀ s κ).1 ∧
    markedRow (M κ) e = κ.ident.row.symm s := by
  have h := κ.ident.incidence (B₀ s κ) s
  rw [Equiv.apply_symm_apply] at h
  have hpos : 0 < coreIncidence core (core.tail s) s := by unfold coreIncidence; simp
  rw [← h] at hpos
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  obtain ⟨hInc, hRow⟩ := Finset.mem_filter.mp he
  exact ⟨e, (StablePathCount.mem_incidentEdges _ _ _).mp hInc, hRow⟩

/-- The first occurrence of the walk. -/
noncomputable def f₀ : NonDanglingEdge κ.data := (exists_start s κ).choose

/-- The start vertex. -/
noncomputable abbrev A₀ : κ.data.SourceVertex := (B₀ s κ).1

/-- The first occurrence meets the start vertex. -/
theorem start_incident : Incident κ.data (f₀ s κ).1 (A₀ s κ) := (exists_start s κ).choose_spec.1

/-- The first occurrence is on the row `s`. -/
theorem start_row : markedRow (M κ) (f₀ s κ) = κ.ident.row.symm s := (exists_start s κ).choose_spec.2

/-- The first occurrence survives. -/
theorem start_nd : ¬ IsDangling κ.data (f₀ s κ).1 := (f₀ s κ).2

/-- A marked branch vertex is a vertex where no row continues. -/
theorem not_continues_branch {target : CFGraph} {data : GluingDatum target degree}
    {marks : Finset data.SourceVertex} (B : MarkedBranchVertex data marks) :
    ¬ Continues data marks B.1 := by
  rintro ⟨h₁, h₂⟩
  rcases B.2 with h | h
  · omega
  · exact h₂ h

/-- The row does not continue at the start vertex. -/
theorem start_end : ¬ Continues κ.data (M κ) (A₀ s κ) := not_continues_branch (B₀ s κ)

/-- The stop of the walk. -/
noncomputable abbrev stop₀ : ℕ := stop (start_incident s κ) (start_nd s κ) (start_end s κ)

/-- The occurrences of the walk. -/
noncomputable abbrev Ej (j : ℕ) : κ.data.SourceEdge := E (M := M κ) (f₀ s κ).1 (A₀ s κ) j

/-- The entry vertices of the walk. -/
noncomputable abbrev Aj (j : ℕ) : κ.data.SourceVertex := A (M := M κ) (f₀ s κ).1 (A₀ s κ) j

/-! ## 2.  A position and the subdivision there -/

/-- **A position**: an index of the walk, up to its stop. -/
structure Pos where
  /-- The index. -/
  i : ℕ
  hi : i ≤ stop₀ s κ

variable {s κ} (P : Pos s κ)

/-- The occurrence subdivided. -/
noncomputable abbrev g : κ.data.SourceEdge := Ej s κ P.i

/-- Its entry vertex. -/
noncomputable abbrev entry : κ.data.SourceVertex := Aj s κ P.i

/-- The subdivided occurrence survives. -/
theorem g_nd : ¬ IsDangling κ.data (g P) := not_isDangling_E (start_nd s κ) P.i

/-- The subdivided occurrence meets its entry vertex. -/
theorem g_entry : Incident κ.data (g P) (entry P) := incident_A (start_incident s κ) P.i

/-- The wall: the entry end of `g`. -/
noncomputable abbrev w : κ.target.V := (entry P).1.1

/-- The target edge subdivided. -/
noncomputable abbrev t : κ.target.edges := (g P).1.1

/-- The subdivided target edge is at the wall. -/
theorem hw : t P ∈ incidentEdges (w P) :=
  ((incident_iff_target_mem_and_rel κ.data _ _).mp (g_entry P)).1

/-- **The subdivided datum.** -/
noncomputable abbrev D : GluingDatum (DivalentExpansion.T' (w := w P) (t := t P)) degree :=
  DivalentExpansion.D' κ.data (hw P)

/-- The contraction site. -/
noncomputable abbrev S : Site (D P) :=
  DivalentExpansion.site κ.data (hw P) κ.fullDim.targetConnected κ.fullDim.targetGenus

/-- The contraction isomorphism. -/
noncomputable abbrev ι : GeometricDatumIso (S P).D κ.data :=
  DivalentExpansion.contractIso κ.data (hw P) κ.fullDim.targetConnected κ.fullDim.targetGenus

/-- The lift of an old source vertex. -/
noncomputable abbrev lv (Y : κ.data.SourceVertex) : (D P).SourceVertex :=
  DivalentExpansion.liftV κ.data (hw P) Y

/-- Contracting undoes the lift of an old source vertex. -/
theorem ι_lv (Y : κ.data.SourceVertex) : (ι P).sourceVertexEquiv ((S P).vmap (lv P Y)) = Y :=
  DivalentExpansion.contractIso_vmap_liftV κ.data (hw P) _ _ Y

/-- A lifted vertex is not over `x'`. -/
theorem lv_not_x (Y : κ.data.SourceVertex) : (lv P Y).1.1 ≠ (S P).x := Sum.inl_ne_inr

/-- **The new mark**, over `x'` in the sheet of `g`. -/
noncomputable abbrev V' : (D P).SourceVertex :=
  (D P).sourceEndpoint (freshVertex κ.target) (g P).1.2

/-- The marks of the lift. -/
noncomputable def markSrc : Fin (k + 1) → (D P).SourceVertex :=
  Fin.lastCases (V' P) fun j ↦ lv P (κ.markSource j)

/-- The last mark of the lift is `V'`. -/
theorem markSrc_last : markSrc P (Fin.last k) = V' P := by simp [markSrc]

/-- The other marks of the lift are the lifted old marks. -/
theorem markSrc_castSucc (j : Fin k) : markSrc P j.castSucc = lv P (κ.markSource j) := by
  simp [markSrc]

/-- The marks, as a set. -/
noncomputable abbrev MM : Finset (D P).SourceVertex := markSet (markSrc P)

/-- The marks of the contraction. -/
noncomputable abbrev MD : Finset (S P).D.SourceVertex :=
  markSet fun j ↦ (S P).vmap (lv P (κ.markSource j))

/-- The occurrence over `t` at `V'` is the lift of `g`. -/
theorem sheet_V' : (V' P).1.2 = (g P).1.2 := by
  change ((D P).vertexPartition (freshVertex κ.target)).repr (g P).1.2 = (g P).1.2
  exact (g P).2

/-- The occurrence over the moved `t` at `V'` is the lift of `g`. -/
theorem fo_eq : (D P).sourceEdge (S P).other (V' P).1.2 =
    DivalentExpansion.liftE κ.data (hw P) (g P) := by
  apply Subtype.ext
  apply Prod.ext
  · exact DivalentExpansion.site_other κ.data (hw P) _ _
  · change ((D P).edgePartition (S P).other).repr (V' P).1.2 = (g P).1.2
    rw [sheet_V', DivalentExpansion.site_other]
    change ((D P).edgePartition (occurrenceEquiv κ.target (w P) (DivalentExpansion.place (t P))
      (some (t P)))).repr (g P).1.2 = (g P).1.2
    rw [DivalentExpansion.ep_old]
    exact (g P).2

/-- The lift of `g` contracts to the image of `g`. -/
theorem emap_fo : (S P).emap ⟨DivalentExpansion.liftE κ.data (hw P) (g P),
      DivalentExpansion.liftE_ne κ.data (hw P) _ _ (g P)⟩ =
    (ι P).sourceEdgeEquiv.symm (g P) := by
  rw [Equiv.eq_symm_apply]
  exact DivalentExpansion.contractIso_emap κ.data (hw P) _ _ (g P)

/-- The contracted datum is valid. -/
theorem S_valid : (S P).D.Valid := (S P).valid (DivalentExpansion.valid κ.data (hw P) κ.fullDim.valid)

/-- The subdivided datum is valid. -/
theorem D_valid : (D P).Valid := DivalentExpansion.valid κ.data (hw P) κ.fullDim.valid

/-- The lift of `g` survives. -/
theorem liftE_nd : ¬ IsDangling (D P) (DivalentExpansion.liftE κ.data (hw P) (g P)) := by
  intro h
  have h₁ : IsDangling (S P).D ((ι P).sourceEdgeEquiv.symm (g P)) := by
    rw [← emap_fo]; exact ((S P).isDangling_emap_iff _).mpr h
  have h₂ := ((ι P).isDangling_map_iff (S_valid P).1 _).mpr h₁
  rw [Equiv.apply_symm_apply] at h₂
  exact g_nd P h₂

/-- The occurrence over `c'` at `V'`. -/
noncomputable abbrev fcE : (D P).SourceEdge := (D P).sourceEdge (S P).c (V' P).1.2

/-- The occurrence over `c'` at `V'` survives. -/
theorem fcE_nd : ¬ IsDangling (D P) (fcE P) := by
  intro h
  apply liftE_nd P
  rw [← fo_eq, ← (S P).partner_sourceEdge_c]
  exact ((S P).isDangling_partner_iff rfl).mpr h

/-- The occurrence over the moved `t` at `V'` survives. -/
theorem fo_nd : ¬ IsDangling (D P) ((D P).sourceEdge (S P).other (V' P).1.2) := by
  rw [fo_eq]; exact liftE_nd P

/-- **The marked setting of the lift.** -/
theorem markHyp : (S P).MarkHyp (MM P) (V' P) (MD P) where
  mem := by rw [← markSrc_last]; exact mem_markSet _ _
  onX := rfl
  only Z hZ hZx := by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hZ
    induction j using Fin.lastCases with
    | last => exact markSrc_last P
    | cast j =>
      rw [markSrc_castSucc] at hZx
      exact absurd hZx (lv_not_x P _)
  valency := (S P).nonDanglingValency_eq_two_of_ne (X := V' P) rfl
    (e := ⟨fcE P, fcE_nd P⟩) (f := ⟨_, fo_nd P⟩)
    (fun h ↦ (S P).other_ne (congrArg (fun e : NonDanglingEdge (D P) ↦ e.1.1.1) h).symm)
    (((S P).incident_x_iff (V' P) rfl _).mpr (Or.inl rfl))
    (((S P).incident_x_iff (V' P) rfl _).mpr (Or.inr rfl))
  marks Y hY := by
    constructor
    · intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      have hY' := ((S P).vmap_inj (lv_not_x P _) hY).mp hj
      rw [← hY', ← markSrc_castSucc]
      exact mem_markSet _ _
    · intro h
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
      induction j using Fin.lastCases with
      | last => rw [markSrc_last] at hY; exact absurd rfl hY
      | cast j =>
        rw [markSrc_castSucc]
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- **The contraction isomorphism on marks.** -/
theorem hMarksι (Y : (S P).D.SourceVertex) :
    (ι P).sourceVertexEquiv Y ∈ M κ ↔ Y ∈ MD P := by
  simp only [M, MD, markSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, (ι P).sourceVertexEquiv.injective ?_⟩
    rw [ι_lv, hj]
  · rintro ⟨j, rfl⟩
    exact ⟨j, (ι_lv P _).symm⟩

/-- The inverse contraction isomorphism on marks. -/
theorem hMarksι' (Y : κ.data.SourceVertex) :
    (ι P).symm.sourceVertexEquiv Y ∈ MD P ↔ Y ∈ M κ := by
  rw [← hMarksι, GeometricDatumIso.sourceVertexEquiv_symm', Equiv.apply_symm_apply]

/-! ## 3.  The transported walk and the side setup -/

/-- The start of the transported walk. -/
noncomputable abbrev ê' : (S P).D.SourceEdge := (ι P).symm.sourceEdgeEquiv (f₀ s κ).1

/-- The start vertex of the transported walk. -/
noncomputable abbrev Â' : (S P).D.SourceVertex := (ι P).symm.sourceVertexEquiv (A₀ s κ)

/-- The transported start occurrence meets the transported start vertex. -/
theorem h₀' : Incident (S P).D (ê' P) (Â' P) :=
  ((ι P).symm.incident_map_iff _ _).mpr (start_incident s κ)

/-- The transported start occurrence survives. -/
theorem hNd' : ¬ IsDangling (S P).D (ê' P) :=
  ((ι P).symm.isDangling_map_iff κ.fullDim.valid.1 _).not.mpr (start_nd s κ)

/-- The row does not continue at the transported start vertex. -/
theorem hEnd' : ¬ Continues (S P).D (MD P) (Â' P) :=
  (continues_map (ι P).symm κ.fullDim.valid.1 (hMarksι' P) (A₀ s κ)).not.mpr (start_end s κ)

/-- **The contraction isomorphism carries the walk of `κ` to the transported walk.** -/
theorem walk_map (j : ℕ) :
    (ι P).symm.sourceEdgeEquiv (Ej s κ j) = E (M := MD P) (ê' P) (Â' P) j ∧
      (ι P).symm.sourceVertexEquiv (Aj s κ j) = A (M := MD P) (ê' P) (Â' P) j :=
  seq_map (ι P).symm κ.fullDim.valid.1 (hMarksι' P) (start_incident s κ) (start_nd s κ) j

/-- The transported walk stops where the walk of `κ` stops. -/
theorem stop' : stop (h₀' P) (hNd' P) (hEnd' P) = stop₀ s κ :=
  stop_map (ι P).symm κ.fullDim.valid.1 (hMarksι' P) (start_incident s κ) (start_nd s κ)
    (start_end s κ) (h₀' P) (hNd' P) (hEnd' P)

/-- The edge map at `fc`, as the edge map of `fo`. -/
theorem edgeMap_fc' : (S P).edgeMap ((S P).fc (markHyp P)).1 = (ι P).symm.sourceEdgeEquiv (g P) := by
  have h : (S P).edgeMap ((S P).fc (markHyp P)).1 =
      (S P).emap ⟨((S P).fo (markHyp P)).1, (S P).other_ne⟩ := by
    unfold Site.edgeMap
    rw [(S P).mu_of_eq (e := ((S P).fc (markHyp P)).1) rfl]
    exact congrArg _ (Subtype.ext ((S P).partner_sourceEdge_c _))
  rw [h]
  have h' : (⟨((S P).fo (markHyp P)).1, (S P).other_ne⟩ :
      {e : (D P).SourceEdge // e.1.1 ≠ (S P).c}) =
      ⟨DivalentExpansion.liftE κ.data (hw P) (g P), DivalentExpansion.liftE_ne κ.data (hw P) _ _ (g P)⟩ :=
    Subtype.ext (fo_eq P)
  rw [h', emap_fo]
  rfl

/-- The occurrence over `c'` at `V'` contracts to the `i`-th occurrence of the walk. -/
theorem hg' : (S P).edgeMap ((S P).fc (markHyp P)).1 = E (M := MD P) (ê' P) (Â' P) P.i := by
  rw [edgeMap_fc']; exact (walk_map P P.i).1

/-- The entry of `g` is the source vertex over `w` in the sheet of `g`. -/
theorem entry_eq : entry P = κ.data.sourceEndpoint (w P) (g P).1.2 := by
  have h := ((incident_iff_target_mem_and_rel κ.data _ _).mp (g_entry P)).2
  refine ((κ.data.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, ?_⟩).symm
  exact h.symm

/-- The walk enters the `i`-th occurrence at the far end of the occurrence over `c'`. -/
theorem hOrient' : A (M := MD P) (ê' P) (Â' P) P.i =
    (S P).vmap (Site.far (V' P) ((S P).fc (markHyp P))) := by
  rw [(S P).far_fc (markHyp P), ← (walk_map P P.i).2, GeometricDatumIso.sourceVertexEquiv_symm',
    Equiv.symm_apply_eq]
  rw [DivalentExpansion.contractIso_vmap]
  change entry P = κ.data.sourceEndpoint (contractVertex κ.target (w P) (S P).w)
    (((D P).vertexPartition (S P).w).repr (V' P).1.2)
  rw [DivalentExpansion.site_w, DivalentExpansion.vp_old_w, sheet_V', entry_eq, contract_oldVertex]
  refine ((κ.data.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, ?_⟩).symm
  exact rfl

/-- **The side setup of the lift** (module `DropSide`). -/
noncomputable def sideSetup : (S P).SideSetup (markHyp P) where
  ê₀ := ê' P
  Â₀ := Â' P
  h₀ := h₀' P
  hNd := hNd' P
  hEnd := hEnd' P
  hRow := by
    change markedRow (MD P) ⟨ê' P, hNd' P⟩ = markedRow (MD P) ((S P).ndMap ((S P).fc (markHyp P)))
    have h1 : (S P).ndMap ((S P).fc (markHyp P)) =
        ⟨E (M := MD P) (ê' P) (Â' P) P.i, not_isDangling_E (hNd' P) _⟩ := Subtype.ext (hg' P)
    rw [h1, markedRow_E (h₀' P) (hNd' P)]
  i := P.i
  hi := by rw [stop']; exact P.hi
  hg := hg' P
  fs := (S P).fc (markHyp P)
  hfs := Or.inl rfl
  hOrient := hOrient' P

/-- **The two rows through `V'` are distinct.** -/
theorem row_fc_ne_fo : markedRow (MM P) ((S P).fc (markHyp P)) ≠
    markedRow (MM P) ((S P).fo (markHyp P)) :=
  Site.fc_row_ne_fo_row (sideSetup P)

end LiftSmooth

end DraismaVargas.Count.MarkedCountGeneral
