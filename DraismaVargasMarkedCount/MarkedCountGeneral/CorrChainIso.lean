module

public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrTailMatch

@[expose] public section

/-!
# The inverse laws, part 4: two regrowths with the same slopes are isomorphic

For the decomposition theorem (module `Correspondence`): the fibre over the
tail is determined by the core map. Two caterpillar branchings `β₁, β₂` over the same datum `ψ`,
with the same marks and the same slopes (`|P¹_i| = |P²_i|` at every mark), whatever their sheet
decompositions `e` and their chains, have isomorphic regrowths (`chainIso`), over the identity of
the regrown target:

* over `T`: the sheet permutation `oldPerm` (old sheets to old sheets, the new sheet entering at an
  ascent of `β₁` to the new sheet entering at that ascent of `β₂`, `CorrAlloc.newMatch`);
* over the tail of mark `j`: the level-by-level permutations of `CorrTailMatch` (`tailMatch j`).

It carries the old source vertices and edges to their namesakes (`chainIso_psiSV`,
`chainIso_psiSE`), every block vertex to its namesake (`chainIso_blockSV`), and the surviving
edges over every tail slot to surviving edges over that slot (`chainIso_tailSE`,
`TailMatch.eP_rowSet`). This is the comparison needed for `regrowTailed_restrictTailed`
(the regrowth of a restriction against the frame it came from, once the frame is written as a
regrowth of its own chains), and it holds for any number of marks.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)

variable {T : CFGraph.{0}} {d' d k : ℕ} {N N' : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β₁ : CatBranching ψ N d c) (β₂ : CatBranching ψ N' d c) (hmark : β₁.mark = β₂.mark)
  (hcard : ∀ j i, ((β₁.chain j).P i).card = ((β₂.chain j).P i).card)

/-! ## 1.  Over the old target -/

/-- **The sheet permutation over `T`.** -/
def oldPerm : Equiv.Perm (Fin d) :=
  β₁.e.symm.trans ((Equiv.sumCongr (Equiv.refl _) (newMatch β₁ β₂ hcard)).trans β₂.e)

@[simp] theorem oldPerm_old (i : Fin d') : oldPerm β₁ β₂ hcard (old β₁.e i) = old β₂.e i := by
  simp [oldPerm]

@[simp] theorem oldPerm_new (n : N) :
    oldPerm β₁ β₂ hcard (new β₁.e n) = new β₂.e (newMatch β₁ β₂ hcard n) := by
  simp [oldPerm]

theorem oldPerm_symm_old (i : Fin d') : (oldPerm β₁ β₂ hcard).symm (old β₂.e i) = old β₁.e i := by
  rw [Equiv.symm_apply_eq, oldPerm_old]

theorem oldPerm_symm_new (n : N') :
    (oldPerm β₁ β₂ hcard).symm (new β₂.e n) = new β₁.e ((newMatch β₁ β₂ hcard).symm n) := by
  rw [Equiv.symm_apply_eq, oldPerm_new, Equiv.apply_symm_apply]

theorem liftPart_oldPerm (P : SheetPartition d') :
    liftPart β₂.e P = (liftPart β₁.e P).relabel (oldPerm β₁ β₂ hcard) := by
  apply SheetPartition.ext_repr
  funext q
  change _ = oldPerm β₁ β₂ hcard ((liftPart β₁.e P).repr ((oldPerm β₁ β₂ hcard).symm q))
  rcases sheet_cases (e := β₂.e) q with ⟨i, rfl⟩ | ⟨n, rfl⟩
  · rw [oldPerm_symm_old, liftPart_repr_old, liftPart_repr_old, oldPerm_old]
  · rw [oldPerm_symm_new, liftPart_repr_new, liftPart_repr_new, oldPerm_new,
      Equiv.apply_symm_apply]

/-! ## 2.  Over the tails -/

include hmark in
theorem x_eq (j : Fin k) : β₂.x j = β₁.x j := by unfold CatBranching.x; rw [hmark]

include hmark in
theorem a_eq (j : Fin k) : β₂.a j = β₁.a j := by unfold CatBranching.a; rw [hmark]

/-- The block of the mark at the attaching vertex. -/
def attachBlock (β : CatBranching ψ N d c) (j : Fin k) : Finset (Fin d) :=
  (liftPart β.e (ψ.vertexPartition (β.x j))).block (old β.e (β.a j))

theorem mem_attachBlock_iff (β : CatBranching ψ N d c) (j : Fin k) (q : Fin d) :
    q ∈ attachBlock β j ↔ ∃ i, q = old β.e i ∧ (ψ.vertexPartition (β.x j)).Rel (β.a j) i := by
  unfold attachBlock
  rw [liftPart_block_old, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, rfl, ((ψ.vertexPartition _).mem_block_iff _ _).mp hi⟩
  · rintro ⟨i, rfl, hi⟩
    exact ⟨i, ((ψ.vertexPartition _).mem_block_iff _ _).mpr hi, rfl⟩

theorem P0_sub_attachBlock (β : CatBranching ψ N d c) (j : Fin k) :
    (β.chain j).P 0 ⊆ attachBlock β j := fun q hq ↦
  (mem_attachBlock_iff β j q).mpr (β.P0_sub j q hq)

include hmark in
theorem attachBlock_map (j : Fin k) :
    (attachBlock β₁ j).map (oldPerm β₁ β₂ hcard).toEmbedding = attachBlock β₂ j := by
  unfold attachBlock
  rw [liftPart_block_old, liftPart_block_old, Finset.map_map, x_eq β₁ β₂ hmark,
    a_eq β₁ β₂ hmark]
  congr 1
  ext i
  simp

theorem enters_new {j : Fin k} {q : Fin d} {i : Fin (c j)} (β : CatBranching ψ N d c)
    (h : (β.chain j).Enters q i) : ∃ n, q = new β.e n ∧ β.EntersAt n j i := by
  obtain ⟨n, rfl⟩ := β.fresh j i.succ q h.1 ((β.valid j).not_mem_zero_of_enters h)
  exact ⟨n, rfl, h⟩

include hmark in
/-- **The matching data at mark `j`.** -/
def tailMatch (j : Fin k) : TailMatch d (c j) where
  ch₁ := β₁.chain j
  ch₂ := β₂.chain j
  B₁ := attachBlock β₁ j
  B₂ := attachBlock β₂ j
  θ := oldPerm β₁ β₂ hcard
  valid₁ := β₁.valid j
  valid₂ := β₂.valid j
  card := hcard j
  P0₁ := P0_sub_attachBlock β₁ j
  P0₂ := P0_sub_attachBlock β₂ j
  θB := attachBlock_map β₁ β₂ hmark hcard j
  θenter q i h := by
    obtain ⟨n, rfl, hn⟩ := enters_new β₁ h
    rw [oldPerm_new]
    have h1 := β₂.entersAt_entry (newMatch β₁ β₂ hcard n)
    rw [entry_newMatch, β₁.entry_eq hn] at h1
    exact h1
  enter_notB q i h := by
    obtain ⟨n, rfl, -⟩ := enters_new β₁ h
    intro hmem
    obtain ⟨i', h', -⟩ := (mem_attachBlock_iff β₁ j _).mp hmem
    exact new_ne_old _ _ h'

@[simp] theorem tailMatch_ch₁ (j : Fin k) : (tailMatch β₁ β₂ hmark hcard j).ch₁ = β₁.chain j := rfl
@[simp] theorem tailMatch_ch₂ (j : Fin k) : (tailMatch β₁ β₂ hmark hcard j).ch₂ = β₂.chain j := rfl
@[simp] theorem tailMatch_θ (j : Fin k) :
    (tailMatch β₁ β₂ hmark hcard j).θ = oldPerm β₁ β₂ hcard := rfl

/-! ## 3.  The isomorphism -/

/-- The target edge dictionary (the identity, read through the two occurrence dictionaries). -/
def chainTE : (catTarget c T β₁.x).edges ≃ (catTarget c T β₂.x).edges :=
  (occEquiv c β₁.x).symm.trans (occEquiv c β₂.x)

@[simp] theorem chainTE_oldE (ε : T.edges) : chainTE β₁ β₂ (oldE c β₁.x ε) = oldE c β₂.x ε := by
  simp [chainTE, oldE]
@[simp] theorem chainTE_tailE (t : TE c) : chainTE β₁ β₂ (tailE c β₁.x t) = tailE c β₂.x t := by
  simp [chainTE, tailE]

/-- The vertex sheet permutations. -/
def chainVP : (catTarget c T β₁.x).V → Equiv.Perm (Fin d) :=
  Sum.elim (fun _ ↦ oldPerm β₁ β₂ hcard) (fun w ↦ (tailMatch β₁ β₂ hmark hcard w.1).vP w.2)

/-- The occurrence sheet permutations. -/
def chainOccP : Occ c T → Equiv.Perm (Fin d) :=
  Sum.elim (fun _ ↦ oldPerm β₁ β₂ hcard) (fun t ↦ (tailMatch β₁ β₂ hmark hcard t.1).eP t.2)

/-- The edge sheet permutations. -/
def chainEP (e : (catTarget c T β₁.x).edges) : Equiv.Perm (Fin d) :=
  chainOccP β₁ β₂ hmark hcard ((occEquiv c β₁.x).symm e)

@[simp] theorem chainVP_oldV (v : T.V) :
    chainVP β₁ β₂ hmark hcard (oldV c β₁.x v) = oldPerm β₁ β₂ hcard := rfl
@[simp] theorem chainVP_tailV (w : TV c) :
    chainVP β₁ β₂ hmark hcard (tailV c β₁.x w) = (tailMatch β₁ β₂ hmark hcard w.1).vP w.2 := rfl
@[simp] theorem chainEP_oldE (ε : T.edges) :
    chainEP β₁ β₂ hmark hcard (oldE c β₁.x ε) = oldPerm β₁ β₂ hcard := by
  simp [chainEP, oldE, chainOccP]
@[simp] theorem chainEP_tailE (t : TE c) :
    chainEP β₁ β₂ hmark hcard (tailE c β₁.x t) = (tailMatch β₁ β₂ hmark hcard t.1).eP t.2 := by
  simp [chainEP, tailE, chainOccP]

include hmark in
theorem tailEnd_eq (t : TE c) : tailEnd c β₂.x t = tailEnd c β₁.x t := by
  unfold tailEnd
  rw [show β₂.x = β₁.x from funext (x_eq β₁ β₂ hmark)]

theorem blockPart_empty_eq (a b : Fin d) : blockPart (∅ : Finset (Fin d)) a = blockPart ∅ b := by
  rw [blockPart_empty, blockPart_empty]

/-- **Two regrowths with the same marks and slopes are isomorphic** (over the identity of the
regrown target). -/
def chainIso : GeometricDatumIso β₁.regrowDatum β₂.regrowDatum where
  targetVertex := Equiv.refl _
  targetEdge := chainTE β₁ β₂
  ends e := by
    rcases edge_cases c β₁.x e with ⟨f, rfl⟩ | ⟨t, rfl⟩
    · rw [chainTE_oldE, oldE_ends, oldE_ends]
      exact Or.inl rfl
    · rw [chainTE_tailE, tailE_ends, tailE_ends, tailEnd_eq β₁ β₂ hmark]
      exact Or.inl rfl
  vertexPerm := chainVP β₁ β₂ hmark hcard
  edgePerm := chainEP β₁ β₂ hmark hcard
  vertexPartition v := by
    rcases vertex_cases c β₁.x v with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact liftPart_oldPerm β₁ β₂ hcard (ψ.vertexPartition w)
    · change blockPart (β₂.vB w) (β₂.vA w) =
        (blockPart (β₁.vB w) (β₁.vA w)).relabel ((tailMatch β₁ β₂ hmark hcard w.1).vP w.2)
      rw [blockPart_relabel]
      exact congrArg₂ blockPart ((tailMatch β₁ β₂ hmark hcard w.1).vP_map w.2).symm
        ((tailMatch β₁ β₂ hmark hcard w.1).vP_anchor w.2).symm
  edgePartition e := by
    rcases edge_cases c β₁.x e with ⟨f, rfl⟩ | ⟨t, rfl⟩
    · rw [chainTE_oldE, CatBranching.ep_oldE, CatBranching.ep_oldE, chainEP_oldE]
      exact liftPart_oldPerm β₁ β₂ hcard (ψ.edgePartition f)
    · rw [chainTE_tailE, CatBranching.ep_tailE, CatBranching.ep_tailE, chainEP_tailE,
        blockPart_relabel]
      obtain ⟨j, s⟩ := t
      by_cases hs : ∃ i, s = loop i
      · obtain ⟨i, rfl⟩ := hs
        change blockPart ∅ _ = blockPart ((∅ : Finset (Fin d)).map _) _
        rw [Finset.map_empty]
        exact blockPart_empty_eq _ _
      · push Not at hs
        exact congrArg₂ blockPart ((tailMatch β₁ β₂ hmark hcard j).eP_map s).symm
          ((tailMatch β₁ β₂ hmark hcard j).eP_anchor hs).symm
  compatible e v hv q := by
    rcases edge_cases c β₁.x e with ⟨f, rfl⟩ | ⟨t, rfl⟩
    · rw [chainEP_oldE]
      rcases vertex_cases c β₁.x v with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · rw [chainVP_oldV, Equiv.symm_apply_apply]
        rfl
      · rw [oldE_ends] at hv
        simp at hv
    · rw [tailE_ends] at hv
      rw [chainEP_tailE]
      rcases vertex_cases c β₁.x v with ⟨w, rfl⟩ | ⟨⟨j', w⟩, rfl⟩
      · have hv' : tailEnd c β₁.x t = oldV c β₁.x w := by
          rcases hv with h | h
          · exact h
          · exact absurd h (headEnd_ne_oldV c β₁.x t w)
        obtain ⟨h0, hx⟩ := (tailEnd_eq_oldV_iff c β₁.x t w).mp hv'
        rw [lTail_eq_none_iff] at h0
        obtain ⟨j, s⟩ := t
        simp only at h0 hx
        subst hx
        change (β₁.regrowDatum.vertexPartition (oldV c β₁.x (β₁.x j))).Rel
          ((chainVP β₁ β₂ hmark hcard (oldV c β₁.x (β₁.x j))).symm
            ((tailMatch β₁ β₂ hmark hcard j).eP s q)) q
        rw [h0, chainVP_oldV]
        refine (tailMatch β₁ β₂ hmark hcard j).compat_attach _ (fun q hq q' ↦ ?_) q
        change q ∈ attachBlock β₁ j at hq
        change _ ↔ q' ∈ attachBlock β₁ j
        unfold attachBlock at hq ⊢
        rw [SheetPartition.mem_block_iff] at hq ⊢
        exact ⟨fun h ↦ hq.trans h, fun h ↦ hq.symm.trans h⟩
      · obtain ⟨j, s⟩ := t
        obtain rfl := tail_incident_mark c β₁.x hv
        rw [chainVP_tailV]
        exact (tailMatch β₁ β₂ hmark hcard j).compat_tail w
          ((tail_incident_iff c β₁.x j s w).mp hv) q

/-! ## 4.  The induced dictionaries -/

theorem chainIso_psiSV (Y : ψ.SourceVertex) :
    (chainIso β₁ β₂ hmark hcard).sourceVertexEquiv (β₁.psiSV Y) = β₂.psiSV Y := by
  apply Subtype.ext
  change (oldV c β₁.x Y.1.1, oldPerm β₁ β₂ hcard (old β₁.e Y.1.2)) = _
  rw [oldPerm_old]
  rfl

theorem chainIso_blockSV (w : TV c) :
    (chainIso β₁ β₂ hmark hcard).sourceVertexEquiv (β₁.blockSV w) = β₂.blockSV w := by
  apply Subtype.ext
  change (tailV c β₁.x w, (tailMatch β₁ β₂ hmark hcard w.1).vP w.2
    ((blockPart (β₁.vB w) (β₁.vA w)).repr (β₁.vA w))) =
      (tailV c β₂.x w, (blockPart (β₂.vB w) (β₂.vA w)).repr (β₂.vA w))
  rw [blockPart_repr_of_mem (β₁.vA_mem w), blockPart_repr_of_mem (β₂.vA_mem w)]
  exact Prod.ext rfl ((tailMatch β₁ β₂ hmark hcard w.1).vP_anchor w.2)

theorem chainIso_psiSE (F : ψ.SourceEdge) :
    (chainIso β₁ β₂ hmark hcard).sourceEdgeEquiv (β₁.psiSE F) = β₂.psiSE F := by
  apply Subtype.ext
  change (chainTE β₁ β₂ (oldE c β₁.x F.1.1),
    chainEP β₁ β₂ hmark hcard (oldE c β₁.x F.1.1) (old β₁.e F.1.2)) = _
  rw [chainTE_oldE, chainEP_oldE, oldPerm_old]
  rfl

theorem chainIso_tailSE (t : TE c) (q : Fin d) :
    (chainIso β₁ β₂ hmark hcard).sourceEdgeEquiv (β₁.tailSE t q) =
      β₂.tailSE t ((tailMatch β₁ β₂ hmark hcard t.1).eP t.2 q) := by
  apply Subtype.ext
  change (chainTE β₁ β₂ (tailE c β₁.x t), chainEP β₁ β₂ hmark hcard (tailE c β₁.x t)
      ((β₁.regrowDatum.edgePartition (tailE c β₁.x t)).repr q)) =
    (tailE c β₂.x t, (β₂.regrowDatum.edgePartition (tailE c β₂.x t)).repr
      ((tailMatch β₁ β₂ hmark hcard t.1).eP t.2 q))
  rw [chainTE_tailE, chainEP_tailE]
  refine Prod.ext rfl ?_
  have h := (chainIso β₁ β₂ hmark hcard).edgePartition (tailE c β₁.x t)
  change β₂.regrowDatum.edgePartition (chainTE β₁ β₂ (tailE c β₁.x t)) =
    (β₁.regrowDatum.edgePartition (tailE c β₁.x t)).relabel
      (chainEP β₁ β₂ hmark hcard (tailE c β₁.x t)) at h
  rw [chainTE_tailE, chainEP_tailE] at h
  change _ = (β₂.regrowDatum.edgePartition (tailE c β₂.x t)).repr _
  rw [h]
  change _ = (tailMatch β₁ β₂ hmark hcard t.1).eP t.2
    ((β₁.regrowDatum.edgePartition (tailE c β₁.x t)).repr
      (((tailMatch β₁ β₂ hmark hcard t.1).eP t.2).symm ((tailMatch β₁ β₂ hmark hcard t.1).eP t.2 q)))
  rw [Equiv.symm_apply_apply]

theorem chainIso_newSE (ε : T.edges) (n : N) :
    (chainIso β₁ β₂ hmark hcard).sourceEdgeEquiv (β₁.newSE ε n) =
      β₂.newSE ε (newMatch β₁ β₂ hcard n) := by
  apply Subtype.ext
  change (chainTE β₁ β₂ (oldE c β₁.x ε), chainEP β₁ β₂ hmark hcard (oldE c β₁.x ε)
    (new β₁.e n)) = _
  rw [chainTE_oldE, chainEP_oldE, oldPerm_new]
  rfl

end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
