module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowAssemble
public import DraismaVargasCount.GeometricStableTransport

@[expose] public section

/-!
# Regrowth, part 12: isomorphisms extend over the tails

The class of the regrowth does not depend on the choices. An isomorphism
`iso : TypedFrameIso κ κ'` extends to an isomorphism of the regrown data (`datumIso`):

* over `T`: `iso` itself, lifted to the new sheets by the identity (`liftPerm`, the
  `extendPerm` of module `Sheets`);
* over the tail of mark `j`: **one** sheet permutation `tailPerm j`, the lift of
  `ρ ∘ σ` with `σ` the permutation of `iso` at `x_j` and `ρ` a permutation inside the block `S'`
  of the mark carrying `σ` of the line-up of `κ` to the line-up of `κ'` (`exists_perm_extend`).
  It carries the windows of `κ` to those of `κ'` (`tailPerm_tailSheet`), and it moves sheets only
  inside the block of the mark, so it is compatible with the partitions at `x_j`
  (`rel_markPerm`). This is a permutation of sheets inside one block at one target vertex,
  extended along the far side of that vertex, used once for the choice of `P_1 ⊆ S`; the other
  choices are fixed by the window chain.

The induced dictionaries are computed on the old part and on the block vertices and edges, and
the isomorphism is over the identity of `T.H` (`regrowFrameIso`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Extending a partial bijection inside a block -/

/-- Two injections into a finite set differ by a permutation supported in it. -/
theorem exists_perm_extend {α : Type*} [DecidableEq α] [Fintype α] {m : ℕ} (B : Finset α)
    (f g : Fin m → α) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfB : ∀ r, f r ∈ B) (hgB : ∀ r, g r ∈ B) :
    ∃ ρ : Equiv.Perm α, (∀ r, ρ (f r) = g r) ∧ ∀ x, x ∉ B → ρ x = x := by
  classical
  let f' : Fin m → {x // x ∈ B} := fun r ↦ ⟨f r, hfB r⟩
  let g' : Fin m → {x // x ∈ B} := fun r ↦ ⟨g r, hgB r⟩
  have hf' : Function.Injective f' := fun r r' h ↦ hf (congrArg Subtype.val h)
  have hg' : Function.Injective g' := fun r r' h ↦ hg (congrArg Subtype.val h)
  let e : {y // y ∈ Set.range f'} ≃ {y // y ∈ Set.range g'} :=
    (Equiv.ofInjective f' hf').symm.trans (Equiv.ofInjective g' hg')
  let ρ' : Equiv.Perm {x // x ∈ B} := e.extendSubtype
  refine ⟨Equiv.Perm.ofSubtype ρ', fun r ↦ ?_, fun x hx ↦
    Equiv.Perm.ofSubtype_apply_of_not_mem ρ' hx⟩
  rw [Equiv.Perm.ofSubtype_apply_of_mem ρ' (hfB r)]
  have h : ρ' (f' r) = g' r := by
    change e.extendSubtype (f' r) = g' r
    rw [Equiv.extendSubtype_apply_of_mem e (f' r) ⟨r, rfl⟩]
    simp only [e, Equiv.trans_apply]
    rw [Equiv.ofInjective_symm_apply hf' r]
    rfl
  exact congrArg Subtype.val h

/-- A permutation fixing everything outside a finite set maps the set onto itself. -/
theorem perm_mem_of_mem {α : Type*} {ρ : Equiv.Perm α} {B : Finset α}
    (hρ : ∀ x, x ∉ B → ρ x = x) {x : α} (hx : x ∈ B) : ρ x ∈ B := by
  by_contra h
  have := hρ _ h
  rw [ρ.injective.eq_iff] at this
  exact h (by rw [this]; exact hx)

/-! ## 2.  The permutation over a tail -/

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}

section Perm

variable (hd : IsTailDegree n p c degree) (J : LowerIndex c)
  {κ κ' : TypedFrame core mark (lowerType c J) (degree - shed J)} (iso : TypedFrameIso κ κ')
  (s : SlopeData c J)

theorem iso_x (j : Fin k) :
    iso.datum.targetVertex (κ.markSource j).1.1 = (κ'.markSource j).1.1 := by
  rw [← iso.mark j]; rfl

theorem iso_a (j : Fin k) :
    iso.datum.vertexPerm (κ.markSource j).1.1 (κ.markSource j).1.2 = (κ'.markSource j).1.2 := by
  rw [← iso.mark j]; rfl

/-- The permutation of `iso` carries the block of a mark onto the block of its image. -/
theorem mem_markBlock_map (j : Fin k) {i : Fin (degree - shed J)} (hi : i ∈ markBlock J κ j) :
    iso.datum.vertexPerm (κ.markSource j).1.1 i ∈ markBlock J κ' j := by
  unfold markBlock at hi ⊢
  rw [SheetPartition.mem_block_iff] at hi ⊢
  have hQ := iso.datum.vertexPartition (κ.markSource j).1.1
  rw [iso_x J iso j] at hQ
  rw [hQ, ← iso_a J iso j]
  exact (SheetPartition.relabel_rel_iff _ _ _ _).mpr hi

theorem mem_markBlock_map_iff (j : Fin k) (i : Fin (degree - shed J)) :
    iso.datum.vertexPerm (κ.markSource j).1.1 i ∈ markBlock J κ' j ↔ i ∈ markBlock J κ j := by
  refine ⟨fun h ↦ ?_, mem_markBlock_map J iso j⟩
  unfold markBlock at h ⊢
  rw [SheetPartition.mem_block_iff] at h ⊢
  have hQ := iso.datum.vertexPartition (κ.markSource j).1.1
  rw [iso_x J iso j] at hQ
  rw [hQ, ← iso_a J iso j] at h
  exact (SheetPartition.relabel_rel_iff _ _ _ _).mp h

theorem exists_markPerm (j : Fin k) :
    ∃ ρ : Equiv.Perm (Fin (degree - shed J)),
      (∀ r, ρ (iso.datum.vertexPerm (κ.markSource j).1.1 (lineUp J κ s j r)) = lineUp J κ' s j r) ∧
        ∀ x, x ∉ markBlock J κ' j → ρ x = x :=
  exists_perm_extend (markBlock J κ' j) _ _
    ((iso.datum.vertexPerm _).injective.comp (lineUp_injective J κ s j))
    (lineUp_injective J κ' s j) (fun r ↦ mem_markBlock_map J iso j (lineUp_mem J κ s j r))
    (lineUp_mem J κ' s j)

/-- **The permutation at mark `j`**: `iso` at `x_j`, then inside the block of the mark. -/
def markPerm (j : Fin k) : Equiv.Perm (Fin (degree - shed J)) :=
  (iso.datum.vertexPerm (κ.markSource j).1.1).trans (exists_markPerm J iso s j).choose

theorem markPerm_lineUp (j : Fin k) (r : Fin (firstSlope J s j)) :
    markPerm J iso s j (lineUp J κ s j r) = lineUp J κ' s j r :=
  (exists_markPerm J iso s j).choose_spec.1 r

/-- **The permutation at mark `j` moves sheets only inside the block of the mark.** -/
theorem rel_markPerm (j : Fin k) (i : Fin (degree - shed J)) :
    (κ.data.vertexPartition (κ.markSource j).1.1).Rel
      ((iso.datum.vertexPerm (κ.markSource j).1.1).symm (markPerm J iso s j i)) i := by
  set σ := iso.datum.vertexPerm (κ.markSource j).1.1
  set ρ := (exists_markPerm J iso s j).choose
  have hρ := (exists_markPerm J iso s j).choose_spec.2
  change (κ.data.vertexPartition (κ.markSource j).1.1).Rel (σ.symm (ρ (σ i))) i
  by_cases hi : σ i ∈ markBlock J κ' j
  · have h1 : ρ (σ i) ∈ markBlock J κ' j := perm_mem_of_mem hρ hi
    have h2 : σ.symm (ρ (σ i)) ∈ markBlock J κ j := by
      rw [← mem_markBlock_map_iff J iso j, Equiv.apply_symm_apply]; exact h1
    have h3 : i ∈ markBlock J κ j := (mem_markBlock_map_iff J iso j i).mp hi
    unfold markBlock at h2 h3
    rw [SheetPartition.mem_block_iff] at h2 h3
    exact h2.symm.trans h3
  · rw [hρ _ hi, Equiv.symm_apply_apply]
    rfl

/-- **The sheet permutation over the tail of mark `j`.** -/
def tailPerm (j : Fin k) : Equiv.Perm (Fin degree) :=
  liftPerm (sheetEquiv hd J) (markPerm J iso s j)

theorem tailPerm_tailSheet (j : Fin k) {r : ℕ} (hr : r < firstSlope J s j + J j) :
    tailPerm hd J iso s j (tailSheet hd J κ s j r) = tailSheet hd J κ' s j r := by
  unfold tailPerm
  by_cases h : r < firstSlope J s j
  · rw [tailSheet_lt hd J κ s h, tailSheet_lt hd J κ' s h, liftPerm_old, markPerm_lineUp]
  · rw [tailSheet_ge hd J κ s (by omega) (by omega), tailSheet_ge hd J κ' s (by omega) (by omega),
      liftPerm_new]

theorem tailPerm_window (j : Fin k) {lo len : ℕ} (h : lo + len ≤ firstSlope J s j + J j) :
    (window (tailSheet hd J κ s j) lo len).map (tailPerm hd J iso s j).toEmbedding =
      window (tailSheet hd J κ' s j) lo len := by
  unfold window
  rw [Finset.map_eq_image, Finset.image_image]
  refine Finset.image_congr fun r hr ↦ ?_
  simp only [Finset.coe_Ico, Set.mem_Ico] at hr
  exact tailPerm_tailSheet hd J iso s j (by omega)

/-- The permutation carries the chain of `κ` onto the chain of `κ'`. -/
theorem tailPerm_P (j : Fin k) (i : Fin (c j + 1)) :
    ((chain hd J κ s j).P i).map (tailPerm hd J iso s j).toEmbedding = (chain hd J κ' s j).P i :=
  tailPerm_window hd J iso s j (chain_P_bound J s j i)

theorem tailPerm_Q (j : Fin k) (i : Fin (c j)) :
    ((chain hd J κ s j).Q i).map (tailPerm hd J iso s j).toEmbedding = (chain hd J κ' s j).Q i :=
  tailPerm_window hd J iso s j (winQ_le_M (isSlopeSeq J s j) rfl i)

theorem tailPerm_tailSheet_lo (j : Fin k) (i : Fin (c j + 1)) :
    tailPerm hd J iso s j (tailSheet hd J κ s j (winLo (s j).1 i)) =
      tailSheet hd J κ' s j (winLo (s j).1 i) := by
  refine tailPerm_tailSheet hd J iso s j ?_
  have h := chain_P_bound J s j i
  have := (isSlopeSeq J s j).1 i
  omega

theorem tailPerm_eB (j : Fin k) (t : CatSlot (c j)) :
    ((chain hd J κ s j).eB t).map (tailPerm hd J iso s j).toEmbedding = (chain hd J κ' s j).eB t := by
  rcases slot_cases t with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact tailPerm_P hd J iso s j i
  · exact tailPerm_Q hd J iso s j i
  · rfl

theorem tailPerm_R (j : Fin k) (i : Fin (c j + 1)) :
    ((chain hd J κ s j).R i).map (tailPerm hd J iso s j).toEmbedding = (chain hd J κ' s j).R i :=
  tailPerm_eB hd J iso s j _

theorem tailPerm_vB (j : Fin k) (w : TailV (c j)) :
    ((chain hd J κ s j).vB w).map (tailPerm hd J iso s j).toEmbedding = (chain hd J κ' s j).vB w := by
  rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · change ((chain hd J κ s j).P i.castSucc ∪ (chain hd J κ s j).P i.succ).map _ =
      (chain hd J κ' s j).P i.castSucc ∪ (chain hd J κ' s j).P i.succ
    rw [Finset.map_union, tailPerm_P, tailPerm_P]
  · exact tailPerm_R hd J iso s j i
  · exact tailPerm_R hd J iso s j i

theorem tailPerm_vA (j : Fin k) (w : TailV (c j)) :
    tailPerm hd J iso s j ((chain hd J κ s j).vA w) = (chain hd J κ' s j).vA w := by
  rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact tailPerm_tailSheet_lo hd J iso s j i.castSucc
  · exact tailPerm_tailSheet_lo hd J iso s j i
  · exact tailPerm_tailSheet_lo hd J iso s j i

theorem tailPerm_eA (j : Fin k) (t : CatSlot (c j)) :
    tailPerm hd J iso s j ((chain hd J κ s j).eA t) = (chain hd J κ' s j).eA t := by
  rcases slot_cases t with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact tailPerm_tailSheet_lo hd J iso s j i
  · exact tailPerm_tailSheet_lo hd J iso s j i.castSucc
  · change tailPerm hd J iso s j (tailSheet hd J κ s j 0) = tailSheet hd J κ' s j 0
    refine tailPerm_tailSheet hd J iso s j ?_
    rw [firstSlope_eq]; omega

theorem tailPerm_rowSet (j : Fin k) (t : CatSlot (c j)) :
    ((chain hd J κ s j).rowSet t).map (tailPerm hd J iso s j).toEmbedding =
      (chain hd J κ' s j).rowSet t := by
  rcases slot_cases t with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact tailPerm_P hd J iso s j i
  · exact tailPerm_Q hd J iso s j i
  · exact tailPerm_R hd J iso s j i

end Perm

/-! ## 3.  The isomorphism of regrown data -/

section DatumIso

variable (hd : IsTailDegree n p c degree) (J : LowerIndex c)
  {κ κ' : TypedFrame core mark (lowerType c J) (degree - shed J)} (iso : TypedFrameIso κ κ')
  (s : SlopeData c J)

local notation "β" => branching hd J κ s
local notation "β'" => branching hd J κ' s

/-- The target vertex dictionary: `iso` on the old vertices, the identity on the tails. -/
def tvIso : (catTarget c κ.target (β).x).V ≃ (catTarget c κ'.target (β').x).V :=
  Equiv.sumCongr iso.datum.targetVertex (Equiv.refl _)

/-- The target edge dictionary: `iso` on the old edges, the identity on the tails. -/
def teIso : (catTarget c κ.target (β).x).edges ≃ (catTarget c κ'.target (β').x).edges :=
  (occEquiv c (β).x).symm.trans
    ((Equiv.sumCongr iso.datum.targetEdge (Equiv.refl _)).trans (occEquiv c (β').x))

@[simp] theorem tvIso_oldV (v : κ.target.V) :
    tvIso hd J iso s (oldV c (β).x v) = oldV c (β').x (iso.datum.targetVertex v) := rfl
@[simp] theorem tvIso_tailV (w : TV c) : tvIso hd J iso s (tailV c (β).x w) = tailV c (β').x w :=
  rfl

@[simp] theorem teIso_oldE (ε : κ.target.edges) :
    teIso hd J iso s (oldE c (β).x ε) = oldE c (β').x (iso.datum.targetEdge ε) := by
  simp [teIso, oldE]
@[simp] theorem teIso_tailE (t : TE c) : teIso hd J iso s (tailE c (β).x t) = tailE c (β').x t := by
  simp [teIso, tailE]

theorem tvIso_tailEnd (t : TE c) :
    tvIso hd J iso s (tailEnd c (β).x t) = tailEnd c (β').x t := by
  obtain ⟨j, s'⟩ := t
  rw [tailEnd_eq_attach, tailEnd_eq_attach]
  cases lTail s' with
  | none =>
    rw [attach_none, attach_none, tvIso_oldV]
    exact congrArg _ (iso_x J iso j)
  | some w => rfl

/-- The vertex sheet permutations. -/
def vpIso : (catTarget c κ.target (β).x).V → Equiv.Perm (Fin degree) :=
  Sum.elim (fun v ↦ liftPerm (sheetEquiv hd J) (iso.datum.vertexPerm v))
    (fun w ↦ tailPerm hd J iso s w.1)

/-- The occurrence sheet permutations. -/
def occPerm : Occ c κ.target → Equiv.Perm (Fin degree) :=
  Sum.elim (fun ε ↦ liftPerm (sheetEquiv hd J) (iso.datum.edgePerm ε))
    (fun t ↦ tailPerm hd J iso s t.1)

/-- The edge sheet permutations. -/
def epIso (e : (catTarget c κ.target (β).x).edges) : Equiv.Perm (Fin degree) :=
  occPerm hd J iso s ((occEquiv c (β).x).symm e)

@[simp] theorem vpIso_oldV (v : κ.target.V) :
    vpIso hd J iso s (oldV c (β).x v) = liftPerm (sheetEquiv hd J) (iso.datum.vertexPerm v) := rfl
@[simp] theorem vpIso_tailV (w : TV c) :
    vpIso hd J iso s (tailV c (β).x w) = tailPerm hd J iso s w.1 := rfl
@[simp] theorem epIso_oldE (ε : κ.target.edges) :
    epIso hd J iso s (oldE c (β).x ε) = liftPerm (sheetEquiv hd J) (iso.datum.edgePerm ε) := by
  simp [epIso, oldE, occPerm]
@[simp] theorem epIso_tailE (t : TE c) :
    epIso hd J iso s (tailE c (β).x t) = tailPerm hd J iso s t.1 := by
  simp [epIso, tailE, occPerm]

theorem blockPart_vB_relabel (w : TV c) :
    blockPart ((β').vB w) ((β').vA w) =
      (blockPart ((β).vB w) ((β).vA w)).relabel (tailPerm hd J iso s w.1) := by
  rw [blockPart_relabel]
  exact congrArg₂ blockPart (tailPerm_vB hd J iso s w.1 w.2).symm (tailPerm_vA hd J iso s w.1 w.2).symm

theorem blockPart_eB_relabel (t : TE c) :
    blockPart ((β').eB t) ((β').eA t) =
      (blockPart ((β).eB t) ((β).eA t)).relabel (tailPerm hd J iso s t.1) := by
  rw [blockPart_relabel]
  exact congrArg₂ blockPart (tailPerm_eB hd J iso s t.1 t.2).symm (tailPerm_eA hd J iso s t.1 t.2).symm

/-- A lifted permutation that moves old sheets inside their blocks moves every sheet inside its
block. -/
theorem rel_liftPerm {d' d₀ : ℕ} {N : Type} (e : Fin d' ⊕ N ≃ Fin d₀) (P : SheetPartition d')
    (α₁ α₂ : Equiv.Perm (Fin d')) (h : ∀ i, P.Rel (α₂.symm (α₁ i)) i) (q : Fin d₀) :
    (liftPart e P).Rel ((liftPerm e α₂).symm (liftPerm e α₁ q)) q := by
  rcases sheet_cases (e := e) q with ⟨i, rfl⟩ | ⟨n, rfl⟩
  · rw [liftPerm_old, liftPerm_symm_old, liftPart_rel_old_old]
    exact h i
  · rw [liftPerm_new, liftPerm_symm_new]
    rfl

/-- **The isomorphism of the regrown data** induced by an isomorphism of typed frames. -/
def datumIso : GeometricDatumIso (β).regrowDatum (β').regrowDatum where
  targetVertex := tvIso hd J iso s
  targetEdge := teIso hd J iso s
  ends e := by
    rcases edge_cases c (β).x e with ⟨f, rfl⟩ | ⟨t, rfl⟩
    · rw [teIso_oldE, oldE_ends, oldE_ends]
      rcases iso.datum.ends f with h | h
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; rfl)
    · rw [teIso_tailE, tailE_ends, tailE_ends]
      exact Or.inl (Prod.ext (tvIso_tailEnd hd J iso s t).symm rfl)
  vertexPerm := vpIso hd J iso s
  edgePerm := epIso hd J iso s
  vertexPartition v := by
    rcases vertex_cases c (β).x v with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · change liftPart _ (κ'.data.vertexPartition (iso.datum.targetVertex w)) =
        (liftPart _ (κ.data.vertexPartition w)).relabel (liftPerm _ (iso.datum.vertexPerm w))
      rw [iso.datum.vertexPartition w]
      exact (liftPart_relabel (e := sheetEquiv hd J) _ _).symm
    · exact blockPart_vB_relabel hd J iso s w
  edgePartition e := by
    rcases edge_cases c (β).x e with ⟨f, rfl⟩ | ⟨t, rfl⟩
    · rw [teIso_oldE, CatBranching.ep_oldE, CatBranching.ep_oldE, epIso_oldE,
        iso.datum.edgePartition f]
      exact (liftPart_relabel (e := sheetEquiv hd J) _ _).symm
    · rw [teIso_tailE, CatBranching.ep_tailE, CatBranching.ep_tailE, epIso_tailE]
      exact blockPart_eB_relabel hd J iso s t
  compatible e v hv q := by
    rcases edge_cases c (β).x e with ⟨f, rfl⟩ | ⟨t, rfl⟩
    · rw [oldE_ends] at hv
      rw [epIso_oldE]
      rcases vertex_cases c (β).x v with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · simp only [oldV_inj] at hv
        rw [vpIso_oldV, CatBranching.vp_oldV]
        exact rel_liftPerm _ _ _ _ (iso.datum.compatible f w hv) q
      · simp at hv
    · rw [tailE_ends] at hv
      rw [epIso_tailE]
      rcases vertex_cases c (β).x v with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · have hv' : tailEnd c (β).x t = oldV c (β).x w := by
          rcases hv with h | h
          · exact h
          · exact absurd h (headEnd_ne_oldV c (β).x t w)
        obtain ⟨-, hx⟩ := (tailEnd_eq_oldV_iff c (β).x t w).mp hv'
        subst hx
        rw [vpIso_oldV, CatBranching.vp_oldV]
        exact rel_liftPerm _ _ _ _ (rel_markPerm J iso s t.1) q
      · obtain ⟨j', w'⟩ := w
        have hj : t.1 = j' := tail_incident_mark c (β).x hv
        rw [vpIso_tailV]
        change (blockPart _ _).Rel ((tailPerm hd J iso s j').symm (tailPerm hd J iso s t.1 q)) q
        rw [hj, Equiv.symm_apply_apply]
        rfl

/-! ### The induced dictionaries -/

theorem sourceVertexEquiv_psiSV (Y : κ.data.SourceVertex) :
    (datumIso hd J iso s).sourceVertexEquiv ((β).psiSV Y) =
      (β').psiSV (iso.datum.sourceVertexEquiv Y) := by
  apply Subtype.ext
  change (tvIso hd J iso s (oldV c (β).x Y.1.1),
    liftPerm (sheetEquiv hd J) (iso.datum.vertexPerm Y.1.1) (old (sheetEquiv hd J) Y.1.2)) = _
  rw [tvIso_oldV, liftPerm_old]
  rfl

theorem sourceVertexEquiv_blockSV (w : TV c) :
    (datumIso hd J iso s).sourceVertexEquiv ((β).blockSV w) = (β').blockSV w := by
  apply Subtype.ext
  change (tvIso hd J iso s (tailV c (β).x w),
    tailPerm hd J iso s w.1 ((blockPart ((β).vB w) ((β).vA w)).repr ((β).vA w))) =
      (tailV c (β').x w, (blockPart ((β').vB w) ((β').vA w)).repr ((β').vA w))
  rw [tvIso_tailV, blockPart_repr_of_mem ((β).vA_mem w), blockPart_repr_of_mem ((β').vA_mem w)]
  exact Prod.ext rfl (tailPerm_vA hd J iso s w.1 w.2)

theorem sourceEdgeEquiv_psiSE (F : κ.data.SourceEdge) :
    (datumIso hd J iso s).sourceEdgeEquiv ((β).psiSE F) =
      (β').psiSE (iso.datum.sourceEdgeEquiv F) := by
  apply Subtype.ext
  change (teIso hd J iso s (oldE c (β).x F.1.1),
    epIso hd J iso s (oldE c (β).x F.1.1) (old (sheetEquiv hd J) F.1.2)) = _
  rw [teIso_oldE, epIso_oldE, liftPerm_old]
  rfl

theorem sourceEdgeEquiv_tailSE (t : TE c) (q : Fin degree) :
    (datumIso hd J iso s).sourceEdgeEquiv ((β).tailSE t q) =
      (β').tailSE t (tailPerm hd J iso s t.1 q) := by
  apply Subtype.ext
  change (teIso hd J iso s (tailE c (β).x t),
    epIso hd J iso s (tailE c (β).x t) (((β).regrowDatum.edgePartition (tailE c (β).x t)).repr q)) =
      (tailE c (β').x t,
        ((β').regrowDatum.edgePartition (tailE c (β').x t)).repr (tailPerm hd J iso s t.1 q))
  rw [teIso_tailE, epIso_tailE, CatBranching.ep_tailE, CatBranching.ep_tailE,
    blockPart_eB_relabel hd J iso s t]
  refine Prod.ext rfl ?_
  change _ = tailPerm hd J iso s t.1 ((blockPart ((β).eB t) ((β).eA t)).repr
    ((tailPerm hd J iso s t.1).symm (tailPerm hd J iso s t.1 q)))
  rw [Equiv.symm_apply_apply]

/-! ### Over the identity of the tailed core -/

variable (T : Tailed core mark c) (hc : IsMarkedCubic core mark)

theorem nonDanglingEdgeEquiv_oldND (hR : (β).regrowDatum.Connected) (F : NonDanglingEdge κ.data) :
    (datumIso hd J iso s).nonDanglingEdgeEquiv hR
        ((β).oldND (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) F) =
      (β').oldND (hψ J κ') (hT J κ') (hT0 J κ') (hMark hd J κ' s)
        (iso.datum.nonDanglingEdgeEquiv (hψ J κ) F) :=
  Subtype.ext (sourceEdgeEquiv_psiSE hd J iso s F.1)

theorem nonDanglingEdgeEquiv_rowND (hR : (β).regrowDatum.Connected) (t : TE c) :
    ∃ hq : tailPerm hd J iso s t.1 ((β).rowAnchor t) ∈ (β').rowSet t,
      (datumIso hd J iso s).nonDanglingEdgeEquiv hR
          ((β).rowND (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) t) =
        (β').tailND (hψ J κ') (hT J κ') (hT0 J κ') (hMark hd J κ' s) t hq := by
  have hmem : (β).rowAnchor t ∈ (β).rowSet t := (β).rowIdx_sub_rowSet t ((β).rowAnchor_mem t)
  refine ⟨?_, Subtype.ext (sourceEdgeEquiv_tailSE hd J iso s t _)⟩
  change _ ∈ (chain hd J κ' s t.1).rowSet t.2
  rw [← tailPerm_rowSet hd J iso s t.1 t.2]
  exact Finset.mem_map_of_mem _ hmem

/-- **The isomorphism is over the identity of `T.H`, on vertices.** -/
theorem overCore_vertex (hR : (β).regrowDatum.Connected) (branch : BranchVertex (β).regrowDatum) :
    (ident T hd J κ' s hc).vertex ((datumIso hd J iso s).branchVertexEquiv hR branch) =
      (ident T hd J κ s hc).vertex branch := by
  obtain ⟨z, rfl⟩ := (bvEquiv hd J κ s hc).surjective branch
  have hL : (ident T hd J κ s hc).vertex (bvEquiv hd J κ s hc z) = vertexSum T J κ z := by
    simp [ident]
  rw [hL]
  rcases z with Y | ⟨j, w⟩
  · have hY' : 3 ≤ nonDanglingValency κ'.data (iso.datum.sourceVertexEquiv Y.1) ∨
        iso.datum.sourceVertexEquiv Y.1 ∈ markSet κ'.markSource := by
      rw [iso.datum.nonDanglingValency_map (hψ J κ), iso.mem_markSet_map]
      exact Y.2
    have hImg : (datumIso hd J iso s).branchVertexEquiv hR (bvEquiv hd J κ s hc (.inl Y)) =
        bvEquiv hd J κ' s hc (.inl ⟨_, hY'⟩) :=
      Subtype.ext (sourceVertexEquiv_psiSV hd J iso s Y.1)
    rw [hImg]
    simp only [ident, Equiv.trans_apply, Equiv.symm_apply_apply]
    change T.vertexEquiv (.inl (κ'.ident.vertex ⟨_, hY'⟩)) = T.vertexEquiv (.inl (κ.ident.vertex Y))
    rw [iso.overCore_vertex Y hY']
  · have hImg : (datumIso hd J iso s).branchVertexEquiv hR (bvEquiv hd J κ s hc (.inr ⟨j, w⟩)) =
        bvEquiv hd J κ' s hc (.inr ⟨j, w⟩) :=
      Subtype.ext (sourceVertexEquiv_blockSV hd J iso s ⟨j, Sum.inl w⟩)
    rw [hImg]
    simp only [ident, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl

/-- **The isomorphism is over the identity of `T.H`, on rows.** -/
theorem overCore_row (hR : (β).regrowDatum.Connected) (path : StablePath (β).regrowDatum) :
    (ident T hd J κ' s hc).row ((datumIso hd J iso s).stablePathEquiv hR path) =
      (ident T hd J κ s hc).row path := by
  obtain ⟨t, rfl⟩ := (pathEquiv hd J κ s).symm.surjective path
  have hL : (ident T hd J κ s hc).row ((pathEquiv hd J κ s).symm t) =
      T.slotEquiv (identRow J κ t) := by
    simp [ident]
  rw [hL]
  rcases t with P | t₀
  · induction P using Quot.ind with
    | mk F =>
      change (ident T hd J κ' s hc).row ((datumIso hd J iso s).stablePathEquiv hR
        ((β).oldND (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) F).stablePath) = _
      rw [Count.GeometricDatumIso.stablePathEquiv_mk, nonDanglingEdgeEquiv_oldND]
      change T.slotEquiv (identRow J κ' ((β').rowTag (hψ J κ') (hT J κ') (hT0 J κ')
        (hMark hd J κ' s) ((β').oldND (hψ J κ') (hT J κ') (hT0 J κ') (hMark hd J κ' s) _))) = _
      rw [CatBranching.rowTag_oldND]
      exact congrArg (fun z ↦ T.slotEquiv (Sum.inl z)) (iso.overCore_row F)
  · change (ident T hd J κ' s hc).row ((datumIso hd J iso s).stablePathEquiv hR
      ((β).rowND (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) t₀).stablePath) = _
    obtain ⟨hq, h⟩ := nonDanglingEdgeEquiv_rowND hd J iso s hR t₀
    rw [Count.GeometricDatumIso.stablePathEquiv_mk, h]
    change T.slotEquiv (identRow J κ' ((β').rowTag (hψ J κ') (hT J κ') (hT0 J κ')
      (hMark hd J κ' s) ((β').tailND (hψ J κ') (hT J κ') (hT0 J κ') (hMark hd J κ' s) t₀ hq))) = _
    rw [CatBranching.rowTag_tailND]
    rfl

end DatumIso

end

end CatRegrow

end DraismaVargas.Count.MarkedCountGeneral
