module

public import DraismaVargasMarkedCount.MarkedCountGeneral.LiftTyped

@[expose] public section

/-!
# The drop lemma: the drop of the lift, its coordinates, and I5

At a position `P` (module `LiftFrame`):

* the drop of the lift is `κ` (`dropIso`): the contraction site of module `DropSmooth` for the lift
  is the one of the subdivision (`t'_lift`), so its contracted datum is `κ.data` through the
  contraction isomorphism of module `LiftDatum`; marks, branch vertices and rows match by
  construction;
* it carries the walk of the drop to the walk of `κ` (`start_map`, `iV_lift`), so the forward
  lemmas of module `DropPos` (`length_cs`, `rowLen_g`) and `coordsAt_dropFrame'` compute the
  coordinates of the lift at `y`: those of `κ` at the merged request, with the column of `t` split
  at `y(cs s) - ℓ_{<i}` (`coords_c₀`, `coords_c₂`, `coords_other`);
* **I5** (`existsLift`): the row `s` has total length `y(cs s) + y(last p)` at the merged request
  (`total_length`), so some position has `ℓ_{<i} ≤ y(cs s) < ℓ_{≤ i}`, and the proviso excludes
  equality on the left.
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
open GenusSixExistence.Tripod.Gadget (subdivide subdivide_tail_castSucc subdivide_head_castSucc)
open Utilities.Certificate.ExplicitPotential (Core)

namespace LiftSmooth

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {s : Fin p} {κ : TypedFrame core mark types degree} (hc : IsMarkedCubic core mark) (P : Pos s κ)

/-! ## 1.  The contraction site of the lift is that of the subdivision -/

/-- The dropped mark of the lift is `V'`. -/
theorem V_lift : DropSmooth.V (liftFrame P) = V' P := markSrc_last P

/-- The divalent vertex of the drop of the lift is `x'`. -/
theorem x_lift : (DropSmooth.site (liftFrame P) hc).x = (S P).x :=
  congrArg (fun X : (D P).SourceVertex ↦ X.1.1) (V_lift P)

/-- The occurrence at the dropped mark on the row `cs s` is the one over `c'`. -/
theorem fV_lift : (DropSmooth.fV (liftFrame P)).1 = fcE P := by
  have hspec := DropSmooth.fV_spec (liftFrame P)
  have hInc : Incident (D P) (DropSmooth.fV (liftFrame P)).1 (V' P) := by
    rw [← V_lift]; exact hspec.1
  rcases ((S P).incident_x_iff (V' P) rfl _).mp hInc with h | h
  · exact h
  · exfalso
    have hfo : DropSmooth.fV (liftFrame P) = (S P).fo (markHyp P) := Subtype.ext h
    have hRow := hspec.2
    rw [hfo] at hRow
    change rfo P = (rowEquiv P).symm s.castSucc at hRow
    rw [rowEquiv_symm_cs] at hRow
    exact row_fc_ne_fo P hRow.symm

/-- **The contracted edge of the drop of the lift is `c'`.** -/
theorem t'_lift : DropSmooth.t' (liftFrame P) = (S P).c :=
  congrArg (fun e : (D P).SourceEdge ↦ e.1.1) (fV_lift P)

/-- **The contracted datum of the lift is `κ.data`.** -/
noncomputable def Φ₀ : GeometricDatumIso (DropSmooth.site (liftFrame P) hc).D (S P).D :=
  Site.contractIso (P₁ := (liftFrame P).data) (P₂ := D P) (GeometricDatumIso.refl (D P))
    (DropSmooth.site (liftFrame P) hc) (S P) (t'_lift P)

/-- **The contracted datum of the lift is `κ.data`.** -/
noncomputable def Φ : GeometricDatumIso (DropSmooth.site (liftFrame P) hc).D κ.data :=
  (Φ₀ hc P).trans (ι P)

/-- `Φ` on the images of source vertices away from `x'`. -/
theorem Φ_vmap {X : (D P).SourceVertex} (hX : X.1.1 ≠ (S P).x) {e : (D P).SourceEdge}
    (he : Incident (D P) e X) :
    (Φ hc P).sourceVertexEquiv ((DropSmooth.site (liftFrame P) hc).vmap X) =
      (ι P).sourceVertexEquiv ((S P).vmap X) :=
  congrArg (ι P).sourceVertexEquiv (contractIso_vmap (P₁ := (liftFrame P).data) (P₂ := D P)
    (GeometricDatumIso.refl (D P)) (DropSmooth.site (liftFrame P) hc) (S P) (t'_lift P)
    (x_lift hc P) (by rw [x_lift]; exact hX) he)

/-- `Φ` on the images of source occurrences. -/
theorem Φ_edgeMap (e : (D P).SourceEdge) :
    (Φ hc P).sourceEdgeEquiv ((DropSmooth.site (liftFrame P) hc).edgeMap e) =
      (ι P).sourceEdgeEquiv ((S P).edgeMap e) := by
  have h := contractIso_edgeMap (P₁ := (liftFrame P).data) (P₂ := D P)
    (GeometricDatumIso.refl (D P)) (DropSmooth.site (liftFrame P) hc) (S P) (t'_lift P)
    (x_lift hc P) e
  have h' : (Φ₀ hc P).sourceEdgeEquiv ((DropSmooth.site (liftFrame P) hc).edgeMap e) =
      (S P).edgeMap e := h
  change (ι P).sourceEdgeEquiv ((Φ₀ hc P).sourceEdgeEquiv ((DropSmooth.site (liftFrame P) hc).edgeMap e)) = _
  rw [h']

/-- A lifted old mark carries an occurrence. -/
theorem incident_lv (Y : κ.data.SourceVertex) (hY : nonDanglingValency κ.data Y = 2) :
    ∃ e : (D P).SourceEdge, Incident (D P) e (lv P Y) :=
  DropSmooth.exists_incident_of_valency (by rw [nd_lv, hY]; omega)

/-- The rows of the drop of the lift are read on `κ`. -/
theorem rowLab_merge (r : MarkedStablePath (D P) (MM P)) :
    κ.ident.row (ρ P (rmap P r)) = DropSmooth.merge s (rowLab P r) := by
  by_cases h₁ : r = rfc P
  · subst h₁
    rw [rowLab_fc, ρ_rfc, Equiv.apply_symm_apply]
    simp [DropSmooth.merge]
  · by_cases h₂ : r = rfo P
    · subst h₂
      rw [rowLab_fo, rmap_rfo, ρ_rfc, Equiv.apply_symm_apply]
      simp [DropSmooth.merge]
    · rw [rowLab_of_ne P h₁ h₂]
      simp [DropSmooth.merge]

/-- **The drop of the lift is `κ`.** -/
noncomputable def dropIso : TypedFrameIso (dropFrame' hc (liftFrame P)) κ where
  datum := Φ hc P
  mark j := by
    change (Φ hc P).sourceVertexEquiv ((DropSmooth.site (liftFrame P) hc).vmap
      (markSrc P j.castSucc)) = κ.markSource j
    have hj := markSrc_castSucc P j
    obtain ⟨e, he⟩ := incident_lv P (κ.markSource j) (κ.fullDim.markValency _ (mem_markSet _ _))
    rw [hj, Φ_vmap hc P (lv_not_x P _) he, ι_lv]
  overCore_vertex Bd hImage := by
    obtain ⟨B, rfl⟩ := ((DropSmooth.site (liftFrame P) hc).branchEquiv
      (DropSmooth.markHyp (liftFrame P) hc)).surjective Bd
    have hB' : B.1.1 ≠ V' P := by rw [← V_lift]; exact B.2
    have h1 := DropSmooth.vertexEquiv_branchEquiv (liftFrame P) hc B
    change _ = vertLab P B.1 at h1
    rw [vertLab_of_ne P hB'] at h1
    change κ.ident.vertex _ = DropSmooth.vertexEquiv (liftFrame P) hc _
    rw [Fin.castSucc_injective _ h1]
    unfold oldLab
    congr 1
    apply Subtype.ext
    change (Φ hc P).sourceVertexEquiv ((DropSmooth.site (liftFrame P) hc).vmap B.1.1) =
      (ι P).sourceVertexEquiv ((S P).vmap B.1.1)
    obtain ⟨e, he⟩ := DropSmooth.exists_incident_branch (liftFrame P).fullDim.markValency B.1
    exact Φ_vmap hc P ((S P).not_over_x (markHyp P) B.1 hB') he
  overCore_row g := by
    obtain ⟨e, rfl⟩ := (DropSmooth.site (liftFrame P) hc).ndMap_surjective g
    change κ.ident.row (markedRow (M κ) _) =
      DropSmooth.rowEquiv (liftFrame P) hc ((DropSmooth.site (liftFrame P) hc).rowMap
        (DropSmooth.markHyp (liftFrame P) hc) (markedRow (MM P) e))
    refine Eq.trans ?_ (DropSmooth.rowEquiv_rowMap (liftFrame P) hc (markedRow (MM P) e)).symm
    change _ = DropSmooth.merge s (rowLab P (markedRow (MM P) e))
    rw [← rowLab_merge]
    have hE : (Φ hc P).nonDanglingEdgeEquiv (dropFrame' hc (liftFrame P)).fullDim.valid.1
        ((DropSmooth.site (liftFrame P) hc).ndMap e) =
        (ι P).nonDanglingEdgeEquiv (S_valid P).1 ((S P).ndMap e) :=
      Subtype.ext (Φ_edgeMap hc P e.1)
    exact congrArg (fun f ↦ κ.ident.row (markedRow (M κ) f)) hE

/-! ## 2.  The walk of the drop of the lift is the walk of `κ` -/

/-- An occurrence of the row `cs s` at a branch vertex other than `V'` maps to the start of the
walk. -/
theorem side_at_branch {B : MarkedBranchVertex (D P) (MM P)} (h : B.1 ≠ V' P)
    {f : NonDanglingEdge (D P)} (hf : Incident (D P) f.1 B.1) (hS : (sideSetup P).Side f) :
    (S P).edgeMap f.1 = ê' P := by
  have hBx : B.1.1.1 ≠ (S P).x := (S P).not_over_x (markHyp P) B h
  have hNC := not_continues_vmap P h
  have hiStop : P.i ≤ stop (h₀' P) (hNd' P) (hEnd' P) := (sideSetup P).hi
  rcases hS with ⟨j, hj, hfj⟩ | hf'
  · have hj' : j < P.i := hj
    have hInc : Incident (S P).D (E (M := MD P) (ê' P) (Â' P) j) ((S P).vmap B.1) :=
      hfj ▸ (S P).incident_edgeMap hBx hf
    have hj0 := (eq_zero_of_incident (h₀' P) (hNd' P) (hEnd' P) (lt_of_lt_of_le hj' hiStop)
      hInc hNC).1
    subst hj0
    exact hfj
  · subst hf'
    have hcN : (S P).vmap ((S P).cNbr (V' P)) = A (M := MD P) (ê' P) (Â' P) P.i :=
      (congrArg (S P).vmap ((S P).far_fc (markHyp P))).symm.trans (hOrient' P).symm
    rcases ((S P).incident_c_iff _ _).mp hf with h' | h'
    · exact absurd (congrArg (fun X : (D P).SourceVertex ↦ X.1.1) h') hBx
    · have hv : (S P).vmap B.1 = A (M := MD P) (ê' P) (Â' P) P.i := by rw [h']; exact hcN
      have hi0 : P.i = 0 := by
        by_contra hne
        exact hNC (hv ▸ continues_A (h₀' P) (hNd' P) (hEnd' P) hiStop hne)
      have : E (M := MD P) (ê' P) (Â' P) P.i = E (M := MD P) (ê' P) (Â' P) 0 := by rw [hi0]
      exact (hg' P).trans this

/-- The branch vertex of the lift labelled `tail s` contracts to the start of the walk. -/
theorem Btail_lift_ne : (DropSmooth.Btail (liftFrame P)).1 ≠ V' P := by
  rw [← V_lift]; exact DropSmooth.Btail_ne (liftFrame P)

/-- The branch vertex of the lift labelled `tail s` contracts to the start of the walk. -/
theorem vmap_Btail : (S P).vmap (DropSmooth.Btail (liftFrame P)).1 = Â' P := by
  refine (vmap_eq_start_iff P (Btail_lift_ne P)).mpr ?_
  have h : vertLab P (DropSmooth.Btail (liftFrame P)) = (core.tail s).castSucc := by
    change vertexEquiv P ((vertexEquiv P).symm (core.tail s).castSucc) = _
    exact Equiv.apply_symm_apply _ _
  rw [vertLab_of_ne P (Btail_lift_ne P)] at h
  exact (Fin.castSucc_injective _ h).symm

/-- The first occurrence of the walk of the drop of the lift contracts to the transported start. -/
theorem edgeMap_ftail : (S P).edgeMap (DropSmooth.ftail (liftFrame P)).1 = ê' P := by
  have hspec := DropSmooth.ftail_spec (liftFrame P)
  have hRow : markedRow (MM P) (DropSmooth.ftail (liftFrame P)) = rfc P :=
    hspec.2.trans (rowEquiv_symm_cs P)
  exact side_at_branch P (Btail_lift_ne P) hspec.1 ((incident_iff_side P _).mp hRow)

/-- `Φ` carries the start occurrence of the drop's walk to that of `κ`. -/
theorem Φ_ê₀ : (Φ hc P).sourceEdgeEquiv (DropSmooth.ê₀ (liftFrame P) hc) = (f₀ s κ).1 :=
  (Φ_edgeMap hc P _).trans ((congrArg (ι P).sourceEdgeEquiv (edgeMap_ftail P)).trans
    (Equiv.apply_symm_apply _ _))

/-- `Φ` carries the start vertex of the drop's walk to that of `κ`. -/
theorem Φ_Â₀ : (Φ hc P).sourceVertexEquiv (DropSmooth.Â₀ (liftFrame P) hc) = A₀ s κ :=
  (Φ_vmap hc P ((S P).not_over_x (markHyp P) _ (Btail_lift_ne P))
    (DropSmooth.ftail_spec (liftFrame P)).1).trans
    ((congrArg (ι P).sourceVertexEquiv (vmap_Btail P)).trans (Equiv.apply_symm_apply _ _))

/-- `Φ` on marks. -/
theorem hMarksΦ (Y : (DropSmooth.site (liftFrame P) hc).D.SourceVertex) :
    (Φ hc P).sourceVertexEquiv Y ∈ M κ ↔ Y ∈ DropSmooth.MD (liftFrame P) hc :=
  (dropIso hc P).mem_markSet_map Y

/-- **The walk of the drop of the lift is the walk of `κ`.** -/
theorem walk_lift (j : ℕ) :
    (Φ hc P).sourceEdgeEquiv (E (M := DropSmooth.MD (liftFrame P) hc)
        (DropSmooth.ê₀ (liftFrame P) hc) (DropSmooth.Â₀ (liftFrame P) hc) j) = Ej s κ j := by
  have h := (seq_map (Φ hc P) (dropFrame' hc (liftFrame P)).fullDim.valid.1 (hMarksΦ hc P)
    (DropSmooth.start_incident (liftFrame P) hc) (DropSmooth.start_nd (liftFrame P) hc) j).1
  rw [h, Φ_ê₀, Φ_Â₀]

/-- Stops do not depend on the proofs. -/
theorem stop_congr {target : CFGraph} {data : GluingDatum target degree}
    {M' : Finset data.SourceVertex} {e₁ e₂ : data.SourceEdge} {A₁ A₂ : data.SourceVertex}
    (he : e₁ = e₂) (hA : A₁ = A₂) (h₁ : Incident data e₁ A₁) (hNd₁ : ¬ IsDangling data e₁)
    (hEnd₁ : ¬ Continues data M' A₁) (h₂ : Incident data e₂ A₂) (hNd₂ : ¬ IsDangling data e₂)
    (hEnd₂ : ¬ Continues data M' A₂) :
    stop h₁ hNd₁ hEnd₁ = stop h₂ hNd₂ hEnd₂ := by
  subst he hA; rfl

/-- The walk of the drop of the lift stops where that of `κ` stops. -/
theorem stop_lift : stop (DropSmooth.start_incident (liftFrame P) hc)
    (DropSmooth.start_nd (liftFrame P) hc) (DropSmooth.start_end (liftFrame P) hc) = stop₀ s κ := by
  have h₀ := ((Φ hc P).incident_map_iff _ _).mpr (DropSmooth.start_incident (liftFrame P) hc)
  have hNd := ((Φ hc P).isDangling_map_iff (dropFrame' hc (liftFrame P)).fullDim.valid.1 _).not.mpr
    (DropSmooth.start_nd (liftFrame P) hc)
  have hEnd := (continues_map (Φ hc P) (dropFrame' hc (liftFrame P)).fullDim.valid.1
    (hMarksΦ hc P) _).not.mpr (DropSmooth.start_end (liftFrame P) hc)
  rw [← stop_map (Φ hc P) (dropFrame' hc (liftFrame P)).fullDim.valid.1 (hMarksΦ hc P)
    (DropSmooth.start_incident (liftFrame P) hc) (DropSmooth.start_nd (liftFrame P) hc)
    (DropSmooth.start_end (liftFrame P) hc) h₀ hNd hEnd]
  exact stop_congr (Φ_ê₀ hc P) (Φ_Â₀ hc P) _ _ _ _ _ _

/-- The occurrence over the contracted edge of the drop of the lift is the one over `c'`. -/
theorem fc_lift : ((DropSmooth.site (liftFrame P) hc).fc (DropSmooth.markHyp (liftFrame P) hc)).1 =
    ((S P).fc (markHyp P)).1 :=
  (congrArg Subtype.val (DropSmooth.fc_eq (liftFrame P) hc)).trans (fV_lift P)

/-- `Φ` carries the occurrence through `V'` to `g`. -/
theorem Φ_g : (Φ hc P).sourceEdgeEquiv ((DropSmooth.site (liftFrame P) hc).edgeMap
    ((DropSmooth.site (liftFrame P) hc).fc (DropSmooth.markHyp (liftFrame P) hc)).1) = g P := by
  refine (Φ_edgeMap hc P _).trans ?_
  have h : (S P).edgeMap ((DropSmooth.site (liftFrame P) hc).fc
      (DropSmooth.markHyp (liftFrame P) hc)).1 = (ι P).sourceEdgeEquiv.symm (g P) := by
    rw [fc_lift]; exact edgeMap_fc' P
  rw [h]
  exact Equiv.apply_symm_apply _ _

/-- **The position of `V'` in the walk of the drop is `P`.** -/
theorem iV_lift : DropSmooth.iV (liftFrame P) hc = P.i := by
  have h := congrArg (Φ hc P).sourceEdgeEquiv (DropSmooth.iV_spec (liftFrame P) hc)
  rw [Φ_g, walk_lift] at h
  have hle := DropSmooth.iV_le (liftFrame P) hc
  rw [stop_lift] at hle
  exact E_injOn (start_incident s κ) (start_nd s κ) (start_end s κ) hle P.hi h.symm

/-- The prefix lengths of the drop of the lift are those of `κ`. -/
theorem pre_lift (y : Fin (p + 1) → ℚ) (j : ℕ) :
    DropSmooth.pre (liftFrame P) hc y j =
      ∑ l ∈ Finset.range j, DropSmooth.rowLen κ (mergeRequest s y) (Ej s κ l) := by
  unfold DropSmooth.pre
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← DropSmooth.rowLen_map (dropIso hc P), ← walk_lift hc P l]
  rfl

/-- The length of the occurrence through `V'` is that of `g`. -/
theorem len_lift (y : Fin (p + 1) → ℚ) :
    DropSmooth.rowLen (dropFrame' hc (liftFrame P)) (mergeRequest s y)
        ((DropSmooth.site (liftFrame P) hc).edgeMap
          ((DropSmooth.site (liftFrame P) hc).fc (DropSmooth.markHyp (liftFrame P) hc)).1) =
      DropSmooth.rowLen κ (mergeRequest s y) (g P) := by
  exact (DropSmooth.rowLen_map (dropIso hc P) _ _).symm.trans
    (congrArg (DropSmooth.rowLen κ (mergeRequest s y)) (Φ_g hc P))

/-! ## 3.  The coordinates of the lift -/

/-- The prefix length of the walk of `κ` at the merged request. -/
noncomputable abbrev preκ (_ : Pos s κ) (y : Fin (p + 1) → ℚ) (j : ℕ) : ℚ :=
  ∑ l ∈ Finset.range j, DropSmooth.rowLen κ (mergeRequest s y) (Ej s κ l)

/-- The occurrence over `c'` at `V'`, in the lift. -/
noncomputable abbrev fcL : NonDanglingEdge (liftFrame P).data :=
  (DropSmooth.site (liftFrame P) hc).fc (DropSmooth.markHyp (liftFrame P) hc)

/-- The other occurrence at `V'`, in the lift. -/
noncomputable abbrev foL : NonDanglingEdge (liftFrame P).data :=
  (DropSmooth.site (liftFrame P) hc).fo (DropSmooth.markHyp (liftFrame P) hc)

/-- **The length of the occurrence over `c'`**: `y(cs s) - ℓ_{<i}` (module `DropPos.length_cs`). -/
theorem fc_len (y : Fin (p + 1) → ℚ) :
    DropSmooth.rowLen (liftFrame P) y (fcL hc P).1 = y s.castSucc - preκ P y P.i := by
  have h := DropSmooth.length_cs (liftFrame P) hc y
  rw [iV_lift, pre_lift] at h
  linarith

/-- The length of the other occurrence at `V'`: the rest of `g` (`DropPos.rowLen_g`). -/
theorem fo_len (y : Fin (p + 1) → ℚ) :
    DropSmooth.rowLen (liftFrame P) y (foL hc P).1 =
      DropSmooth.rowLen κ (mergeRequest s y) (g P) - (y s.castSucc - preκ P y P.i) := by
  have h := DropSmooth.rowLen_g (liftFrame P) hc y
  rw [len_lift, fc_len] at h
  linarith

/-- A coordinate is a length times an index. -/
theorem coords_eq_mul (y : Fin (p + 1) → ℚ) (e : (liftFrame P).data.SourceEdge) :
    (liftFrame P).coordsAt y ((liftFrame P).fullDim.labelling.targetEdge.symm e.1.1) =
      DropSmooth.rowLen (liftFrame P) y e * (liftFrame P).data.sourceEdgeIndex e := by
  unfold DropSmooth.rowLen
  have hIdx : ((liftFrame P).data.sourceEdgeIndex e : ℚ) ≠ 0 := by
    exact_mod_cast (SheetPartition.blockCard_pos _ _).ne'
  field_simp

/-- The coordinate of the lift at the column of `c'`. -/
theorem coords_c₀ (y : Fin (p + 1) → ℚ) :
    (liftFrame P).coordsAt y (DropSmooth.c₀ (liftFrame P)) =
      (y s.castSucc - preκ P y P.i) * (liftFrame P).data.sourceEdgeIndex (fcL hc P).1 := by
  rw [← fc_len hc P y, ← coords_eq_mul P y]
  rfl

/-- The coordinate of the lift at the column of the moved `t`. -/
theorem coords_c₂ (y : Fin (p + 1) → ℚ) :
    (liftFrame P).coordsAt y (DropSmooth.c₂ (liftFrame P) hc) =
      (DropSmooth.rowLen κ (mergeRequest s y) (g P) - (y s.castSucc - preκ P y P.i)) *
        (liftFrame P).data.sourceEdgeIndex (foL hc P).1 := by
  rw [← fo_len hc P y, ← coords_eq_mul P y]
  rfl

include hc in
/-- **The lift is open at `y`** when `y(cs s)` lies strictly inside the interval of `g`. -/
theorem open_lift (y : Fin (p + 1) → ℚ) (hOpen : κ.OpenAt (mergeRequest s y))
    (h₁ : preκ P y P.i < y s.castSucc)
    (h₂ : y s.castSucc < preκ P y P.i + DropSmooth.rowLen κ (mergeRequest s y) (g P)) :
    (liftFrame P).OpenAt y := by
  have hDrop : (dropFrame' hc (liftFrame P)).OpenAt (mergeRequest s y) :=
    ((dropIso hc P).openAt_iff _).mpr hOpen
  have hdc := DropSmooth.coordsAt_dropFrame' (liftFrame P) hc y
  intro col
  by_cases hc₀ : col = DropSmooth.c₀ (liftFrame P)
  · rw [hc₀, coords_c₀ hc]
    have : (0 : ℚ) < (liftFrame P).data.sourceEdgeIndex (fcL hc P).1 := by
      exact_mod_cast SheetPartition.blockCard_pos _ _
    exact mul_pos (by linarith) this
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hc₀
    by_cases hc₂ : (DropSmooth.c₀ (liftFrame P)).succAbove j = DropSmooth.c₂ (liftFrame P) hc
    · rw [hc₂, coords_c₂ hc]
      have : (0 : ℚ) < (liftFrame P).data.sourceEdgeIndex (foL hc P).1 := by
        exact_mod_cast SheetPartition.blockCard_pos _ _
      exact mul_pos (by linarith) this
    · have h := hDrop j
      rw [hdc] at h
      unfold DropSmooth.dropCoords at h
      rw [ite_eq_right hc₂, add_zero] at h
      exact h

include hc in
/-- **At the left end of the interval the lift has a zero coordinate.** -/
theorem zero_lift (y : Fin (p + 1) → ℚ) (h : preκ P y P.i = y s.castSucc) :
    (liftFrame P).coordsAt y (DropSmooth.c₀ (liftFrame P)) = 0 := by
  rw [coords_c₀ hc, h, sub_self, zero_mul]

/-! ## 4.  The total length of the row and the choice of the position -/

omit hc in
open Classical in
/-- **The row `s` has length `y(cs s) + y(last p)`** at the merged request. -/
theorem total_length (s : Fin p) (κ : TypedFrame core mark types degree) (y : Fin (p + 1) → ℚ) :
    ∑ l ∈ Finset.range (stop₀ s κ + 1), DropSmooth.rowLen κ (mergeRequest s y) (Ej s κ l) =
      y s.castSucc + y (Fin.last p) := by
  have hRow := DropSmooth.mulVec_eq_sum κ (κ.coordsAt (mergeRequest s y))
    (κ.fullDim.labelling.row (κ.ident.row.symm s))
  rw [κ.mulVec_coordsAt] at hRow
  have hSlot : κ.slot (κ.fullDim.labelling.row (κ.ident.row.symm s)) = s := by
    change κ.ident.row (κ.fullDim.labelling.row.symm (κ.fullDim.labelling.row (κ.ident.row.symm s))) = s
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  simp only [hSlot, Equiv.symm_apply_apply] at hRow
  have hMerge : mergeRequest s y s = y s.castSucc + y (Fin.last p) := by
    simp [mergeRequest]
  rw [← hMerge, hRow, ← Finset.sum_filter]
  have hSet : (Finset.univ.filter fun f : κ.data.SourceEdge ↦ ∃ hNd : ¬ IsDangling κ.data f,
      markedRow (M κ) (⟨f, hNd⟩ : NonDanglingEdge κ.data) = κ.ident.row.symm s) =
      (Finset.range (stop₀ s κ + 1)).image (Ej s κ) := by
    ext f
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hNd, hR⟩
      obtain ⟨j, hj, hfj⟩ := exists_index (start_incident s κ) (start_nd s κ) (start_end s κ)
        ⟨f, hNd⟩ (hR.trans (start_row s κ).symm)
      exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), hfj.symm⟩
    · rintro ⟨j, -, rfl⟩
      exact ⟨Finset.mem_univ _, not_isDangling_E (start_nd s κ) j,
        (markedRow_E (start_incident s κ) (start_nd s κ) j).trans (start_row s κ)⟩
  rw [hSet, Finset.sum_image]
  · rfl
  · intro i hi j hj h
    exact E_injOn (start_incident s κ) (start_nd s κ) (start_end s κ)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) h

/-- **A point of the total length lies in the interval of one occurrence.** -/
theorem exists_interval (L : ℕ → ℚ) (N : ℕ) (Y : ℚ) (hY0 : 0 ≤ Y)
    (hYN : Y < ∑ l ∈ Finset.range (N + 1), L l) :
    ∃ i ≤ N, ∑ l ∈ Finset.range i, L l ≤ Y ∧ Y < ∑ l ∈ Finset.range i, L l + L i := by
  classical
  have h : ∃ j, Y < ∑ l ∈ Finset.range (j + 1), L l := ⟨N, hYN⟩
  refine ⟨Nat.find h, Nat.find_min' h hYN, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
    · rw [h0, Finset.sum_range_zero]; exact hY0
    · obtain ⟨i', hi'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have := Nat.find_min h (show i' < Nat.find h by omega)
      rw [hi']
      exact not_lt.mp this
  · rw [← Finset.sum_range_succ]
    exact Nat.find_spec h

/-- **I5: the lift.** -/
theorem existsLift (s : Fin p) {y : Fin (p + 1) → ℚ} (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ' : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)
      (col : Fin (p + 1)), κ'.coordsAt y col ≠ 0)
    (κ : TypedFrame core mark types degree) (hOpen : κ.OpenAt (mergeRequest s y)) :
    ∃ κ' : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree,
      κ'.OpenAt y ∧ Nonempty (TypedFrameIso (dropFrame' hc κ') κ) := by
  have hTot := total_length s κ y
  obtain ⟨i, hi, h₁, h₂⟩ := exists_interval _ (stop₀ s κ) (y s.castSucc) (hPositive _).le
    (by rw [hTot]; linarith [hPositive (Fin.last p)])
  let P : Pos s κ := ⟨i, hi⟩
  have hlt : preκ P y P.i < y s.castSucc := by
    rcases h₁.lt_or_eq with h | h
    · exact h
    · exact absurd (zero_lift hc P y h) (hGeneral _ _)
  exact ⟨liftFrame P, open_lift hc P y hOpen hlt h₂, ⟨dropIso hc P⟩⟩

end LiftSmooth

end DraismaVargas.Count.MarkedCountGeneral
