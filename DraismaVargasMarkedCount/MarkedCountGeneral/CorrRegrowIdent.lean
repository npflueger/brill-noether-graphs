module

public import DraismaVargasMarkedCount.MarkedCountGeneral.Regrowth

@[expose] public section

/-!
# The inverse laws, part 5: reading the regrown frame through its label

For `restrictTailed_regrowTailed`: in the regrowth, the tails are the attached ones. Restriction
locates the tails of a frame through its label (`TailRestrict.uSource`, `xSpine`, `xBulb`, `xLeaf`,
`tEdge` are read off `M.ident`). For the regrown frame `regrowTailed T hc hd J κ s` this module
computes the label backwards:

* the core vertex `v` of `T.H` is the old source vertex of `κ.ident.vertex.symm v`
  (`ident_vertex_symm_old`), and the tail vertex `⟨j, w⟩` is the block vertex over the target tail
  vertex `⟨j, w⟩` (`ident_vertex_symm_tail`);
* the core slot `i` is the marked row `κ.ident.row.symm i` (`ident_row_symm_core`), and the tail
  slot `⟨j, s⟩` is the row of the slot `s` (`ident_row_symm_tail`), through its block edge;
* the old part of the datum is `Sheets.extendSheets κ.data σ_B` (`vp_old_eq`,
  `ep_old_eq`), and the slopes of the chains are `s` (`card_P`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) (hd : IsTailDegree n p c degree)
  (J : LowerIndex c) (κ : TypedFrame core mark (lowerType c J) (degree - shed J))
  (s : SlopeData c J)

local notation "F" => regrowTailed T hc hd J κ s
local notation "β" => branching hd J κ s

theorem regrowTailed_target : (F).target = catTarget c κ.target (β).x := rfl
theorem regrowTailed_data : (F).data = (β).regrowDatum := rfl

/-- The old part of the regrown datum is the extension of `κ.data` by the new sheets
(`Sheets.extendSheets`). -/
theorem vp_old_eq (v : κ.target.V) :
    (β).regrowDatum.vertexPartition (oldV c (β).x v) =
      Sheets.extendPartition (κ.data.vertexPartition v) (sheetEquiv hd J).symm := rfl

theorem ep_old_eq (ε : κ.target.edges) :
    (β).regrowDatum.edgePartition (oldE c (β).x ε) =
      Sheets.extendPartition (κ.data.edgePartition ε) (sheetEquiv hd J).symm :=
  CatBranching.ep_oldE _ ε

/-- **The slopes of the regrown chains are `s`.** -/
theorem card_P (j : Fin k) (i : Fin (c j + 1)) : (((β).chain j).P i).card = (s j).1 i :=
  card_windowChain_P (tailSheet_injOn hd J κ s j) (isSlopeSeq J s j) rfl i

/-- **The label, backwards, at a core vertex.** -/
theorem ident_vertex_symm_old (v : Fin n) :
    ((F).ident.vertex.symm (T.vertexEquiv (.inl v))).1 = (β).psiSV (κ.ident.vertex.symm v).1 := by
  have h : (F).ident.vertex (bvEquiv hd J κ s hc (.inl (κ.ident.vertex.symm v))) =
      T.vertexEquiv (.inl v) := by
    change (vertexSum T J κ) ((bvEquiv hd J κ s hc).symm
      (bvEquiv hd J κ s hc (.inl (κ.ident.vertex.symm v)))) = _
    rw [Equiv.symm_apply_apply]
    simp [vertexSum]
  rw [← h]
  exact congrArg Subtype.val (Equiv.symm_apply_apply (F).ident.vertex _)

/-- **The label, backwards, at a tail vertex.** -/
theorem ident_vertex_symm_tail (j : Fin k) (w : CatVertex (c j)) :
    ((F).ident.vertex.symm (T.vertexEquiv (.inr ⟨j, w⟩))).1 = (β).blockSV ⟨j, Sum.inl w⟩ := by
  have h : (F).ident.vertex (bvEquiv hd J κ s hc (.inr ⟨j, w⟩)) =
      T.vertexEquiv (.inr ⟨j, w⟩) := by
    change (vertexSum T J κ) ((bvEquiv hd J κ s hc).symm
      (bvEquiv hd J κ s hc (.inr ⟨j, w⟩))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [← h]
  exact congrArg Subtype.val (Equiv.symm_apply_apply (F).ident.vertex _)

/-- **The label, backwards, at a core slot.** -/
theorem ident_row_symm_core (i : Fin p) :
    (F).ident.row.symm (T.slotEquiv (.inl i)) =
      (β).tagPath (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) (.inl (κ.ident.row.symm i)) := by
  change ((pathEquiv hd J κ s).trans ((identRow J κ).trans T.slotEquiv)).symm _ = _
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rfl

/-- **The label, backwards, at a tail slot**: the row of the slot, through its block edge (or a
loop edge). -/
theorem ident_row_symm_tail (t : TE c) :
    (F).ident.row.symm (T.slotEquiv (.inr t)) =
      ((β).rowND (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) t).stablePath := by
  change ((pathEquiv hd J κ s).trans ((identRow J κ).trans T.slotEquiv)).symm _ = _
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rfl

/-- The row of a surviving edge, through the label. -/
theorem ident_row_stablePath (E : NonDanglingEdge (β).regrowDatum) :
    (F).ident.row E.stablePath =
      T.slotEquiv (identRow J κ ((β).rowTag (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) E)) :=
  rfl

/-- The marks of the regrowth are the old source vertices of the marks of `κ`. -/
theorem ident_vertex_symm_mark (j : Fin k) :
    ((F).ident.vertex.symm (T.oldVertex (mark j))).1 = (β).psiSV (κ.markSource j) := by
  unfold Tailed.oldVertex
  rw [ident_vertex_symm_old]
  congr 1
  rw [← κ.ident.vertex_mark j]
  exact congrArg Subtype.val (Equiv.symm_apply_apply κ.ident.vertex _)

end

end CatRegrow

end DraismaVargas.Count.MarkedCountGeneral
