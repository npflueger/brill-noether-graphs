module

public import DiagonalSecant.CMDictionary
public import DraismaVargasCount.PendantRetraction

@[expose] public section

/-!
# The pendant retraction of a regrowth without new sheets

The chip coefficients
of the typed placement are pendant-retraction fibres (`PendantRetraction.retractedFibre`), so
transporting the public hairpin receipt from the regrown frame needs the retraction classes of
the regrowth over an old target vertex to be those of `κ`.

When the regrowth adds no new sheet (`[IsEmpty N]`: the lower index is `0`, the case of the
diagonal secant theorem) every tail block lies in the first block `P_1` of its chain
(`mem_P_zero_of_mem_vB`), so a sheet outside `P_1` is a singleton over the whole tail and its
tail copy is a pendant tree hanging at the old vertex carrying that sheet over the mark's
image. The **anchor** of a source vertex of the regrowth records that old vertex (`none` for the
block vertices of the tails and their pendant pieces, which never meet an old vertex through a
dangling occurrence). Every dangling occurrence joins vertices whose anchors are retraction-
equivalent (`anchorRel_sourceEnds`), so the retraction classes of two old vertices agree in the
regrowth and in `ψ` (`retractVertex_psiSV_iff`), and the retracted fibre over an old vertex is
unchanged (`retractedFibre_psiSV`).
-/

namespace DiagonalSecant.CM

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.CatRegrow
open DraismaVargas.Count.PendantRetraction
open DraismaVargas.Count.MarkedCountGeneral.CatSlot DraismaVargas.Count.MarkedCountGeneral.CatRegrow.TailV

section Anchor

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c) [IsEmpty N]

/-! ## 1.  No new sheets -/

/-- The old sheet of a sheet of the regrowth, when there are no new sheets. -/
def oldInv (q : Fin d) : Fin d' := (β.e.symm q).elim id fun n ↦ isEmptyElim n

theorem old_oldInv (q : Fin d) : old β.e (oldInv β q) = q := by
  unfold oldInv old
  rcases h : β.e.symm q with i | n
  · simp only [Sum.elim_inl, id]
    rw [← h, Equiv.apply_symm_apply]
  · exact isEmptyElim n

theorem oldInv_old (i : Fin d') : oldInv β (old β.e i) = i := by
  unfold oldInv old
  rw [Equiv.symm_apply_apply]
  rfl

/-- Every sheet is old. -/
theorem exists_old (q : Fin d) : ∃ i, q = old β.e i := ⟨oldInv β q, (old_oldInv β q).symm⟩

/-- Every sheet of a tail block is in the first block of its chain. -/
theorem mem_P_zero_of_mem_P {j : Fin k} {i : Fin (c j + 1)} {q : Fin d}
    (hq : q ∈ (β.chain j).P i) : q ∈ (β.chain j).P 0 := by
  by_contra h0
  obtain ⟨n, -⟩ := β.fresh j i q hq h0
  exact isEmptyElim n

theorem mem_P_zero_of_mem_vB {j : Fin k} {w : TailV (c j)} {q : Fin d}
    (hq : q ∈ β.vB ⟨j, w⟩) : q ∈ (β.chain j).P 0 := by
  obtain ⟨i, hi, -, -⟩ := (β.valid j).exists_P_of_mem_vB hq
  exact mem_P_zero_of_mem_P β hi

/-! ## 2.  The anchor -/

/-- **The anchor** of a source vertex of the regrowth: an old vertex is its own anchor; a vertex
over a tail vertex of mark `j` carrying a sheet outside `P_1` is anchored at the old vertex of
that sheet over the mark's image; the block vertices of the tails (and their pendant pieces,
which carry sheets of `P_1`) have no anchor. -/
noncomputable def anchor (X : β.regrowDatum.SourceVertex) : Option ψ.SourceVertex :=
  Sum.elim (fun v ↦ some (ψ.sourceEndpoint v (oldInv β X.1.2)))
    (fun w ↦ if X.1.2 ∈ (β.chain w.1).P 0 then none
      else some (ψ.sourceEndpoint (β.x w.1) (oldInv β X.1.2))) X.1.1

theorem anchor_psiSV (Y : ψ.SourceVertex) : anchor β (β.psiSV Y) = some Y := by
  show some (ψ.sourceEndpoint Y.1.1 (oldInv β (old β.e Y.1.2))) = some Y
  rw [oldInv_old, GluingDatum.sourceEndpoint_self]

theorem anchor_tailSV (j : Fin k) (w : TailV (c j)) (q : Fin d) :
    anchor β (β.tailSV ⟨j, w⟩ q) =
      if q ∈ (β.chain j).P 0 then none else some (ψ.sourceEndpoint (β.x j) (oldInv β q)) := by
  have hX : (β.tailSV ⟨j, w⟩ q).1.2 = (blockPart (β.vB ⟨j, w⟩) (β.vA ⟨j, w⟩)).repr q := rfl
  show (if (β.tailSV ⟨j, w⟩ q).1.2 ∈ (β.chain j).P 0 then none
    else some (ψ.sourceEndpoint (β.x j) (oldInv β (β.tailSV ⟨j, w⟩ q).1.2))) = _
  rw [hX]
  by_cases hq : q ∈ β.vB ⟨j, w⟩
  · rw [blockPart_repr_of_mem hq]
    have h1 : β.vA ⟨j, w⟩ ∈ (β.chain j).P 0 := mem_P_zero_of_mem_vB β (β.vA_mem ⟨j, w⟩)
    have h2 : q ∈ (β.chain j).P 0 := mem_P_zero_of_mem_vB β hq
    rw [ite_eq_left h1, ite_eq_left h2]
  · rw [blockPart_repr_of_not_mem hq]

/-- Retraction-equivalence of anchors. -/
def AnchorRel : Option ψ.SourceVertex → Option ψ.SourceVertex → Prop
  | none, none => True
  | some a, some b => retractVertex a = retractVertex b
  | some _, none => False
  | none, some _ => False

theorem anchorRel_refl (o : Option ψ.SourceVertex) : AnchorRel o o := by
  cases o
  · trivial
  · exact rfl

theorem anchorRel_symm {o o' : Option ψ.SourceVertex} (h : AnchorRel o o') : AnchorRel o' o := by
  cases o <;> cases o'
  · trivial
  · exact h.elim
  · exact h.elim
  · exact (h : retractVertex _ = retractVertex _).symm

theorem anchorRel_trans {o o' o'' : Option ψ.SourceVertex} (h : AnchorRel o o')
    (h' : AnchorRel o' o'') : AnchorRel o o'' := by
  cases o <;> cases o' <;> cases o'' <;>
    first
    | trivial
    | exact (h : retractVertex _ = retractVertex _).trans h'

/-! ## 3.  Dangling occurrences relate anchors -/

variable (hψ : ψ.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
  (hMark : ∀ j, nonDanglingValency ψ (β.mark j) ≠ 0)

include hψ hT hT0 hMark

omit [IsEmpty N] in
theorem not_mem_rowSet_of_isDangling_tailSE {t : TE c} {q : Fin d}
    (h : IsDangling β.regrowDatum (β.tailSE t q)) : q ∉ β.rowSet t := fun hq ↦
  (β.not_isDangling_iff hψ hT hT0 hMark _).mpr (Or.inr ⟨t, q, hq, rfl⟩) h

/-- **The ends of a dangling occurrence of the regrowth have related anchors.** -/
theorem anchorRel_sourceEnds {E : β.regrowDatum.SourceEdge} (hE : IsDangling β.regrowDatum E) :
    AnchorRel (anchor β (β.regrowDatum.sourceEnds E).1)
      (anchor β (β.regrowDatum.sourceEnds E).2) := by
  rcases β.sourceEdge_cases E with ⟨F, rfl⟩ | ⟨ε, n, -⟩ | ⟨t, q, rfl⟩
  · rw [β.sourceEnds_psiSE]
    simp only [anchor_psiSV]
    show retractVertex _ = retractVertex _
    exact Quotient.sound (Relation.ReflTransGen.single
      ⟨F, (β.isDangling_psiSE_iff hψ hT hT0 hMark F).mp hE, Or.inl rfl⟩)
  · exact isEmptyElim n
  · have hq := not_mem_rowSet_of_isDangling_tailSE β hψ hT hT0 hMark hE
    obtain ⟨j, s⟩ := t
    rw [β.sourceEnds_tailSE]
    simp only
    rw [anchor_tailSV, tailEnd_eq_attach]
    cases h : lTail s with
    | none =>
      rw [lTail_eq_none_iff] at h
      subst h
      have hq0 : q ∉ (β.chain j).P 0 := by
        intro h0
        apply hq
        change q ∈ (β.chain j).rowSet (path 0)
        rw [TailChain.rowSet_of_not_loop _ (fun i h ↦ by simp [DraismaVargas.Count.MarkedCountGeneral.CatSlot.path, DraismaVargas.Count.MarkedCountGeneral.CatSlot.loop] at h),
          TailChain.eB_path]
        exact h0
      rw [ite_eq_right hq0]
      obtain ⟨i, rfl⟩ := exists_old β q
      rw [attach_none, β.sourceEndpoint_oldV_old, anchor_psiSV, oldInv_old]
      exact anchorRel_refl _
    | some w' =>
      rw [attach_some]
      change AnchorRel (anchor β (β.tailSV ⟨j, w'⟩ q)) _
      rw [anchor_tailSV]
      exact anchorRel_refl _

theorem anchorRel_of_danglingStep {X X' : β.regrowDatum.SourceVertex}
    (h : DanglingStep X X') : AnchorRel (anchor β X) (anchor β X') := by
  obtain ⟨E, hE, hEnds⟩ := h
  have this := anchorRel_sourceEnds β hψ hT hT0 hMark hE
  rcases hEnds with hEnds | hEnds <;> rw [hEnds] at this
  · exact this
  · exact anchorRel_symm this

theorem anchorRel_of_reflTransGen {X X' : β.regrowDatum.SourceVertex}
    (h : Relation.ReflTransGen DanglingStep X X') : AnchorRel (anchor β X) (anchor β X') := by
  induction h with
  | refl => exact anchorRel_refl _
  | tail _ hStep ih => exact anchorRel_trans ih (anchorRel_of_danglingStep β hψ hT hT0 hMark hStep)

/-! ## 4.  The retraction classes and fibres of old vertices -/

/-- **Two old vertices are retraction-equivalent in the regrowth iff they are in `ψ`.** -/
theorem retractVertex_psiSV_iff (v w : ψ.SourceVertex) :
    retractVertex (β.psiSV v) = retractVertex (β.psiSV w) ↔
      retractVertex v = retractVertex w := by
  constructor
  · intro h
    have this := anchorRel_of_reflTransGen β hψ hT hT0 hMark (Quotient.exact h)
    rw [anchor_psiSV, anchor_psiSV] at this
    exact this
  · intro h
    apply Quotient.sound
    refine Relation.ReflTransGen.lift β.psiSV (fun a b hab ↦ ?_) _ _ (Quotient.exact h)
    obtain ⟨F, hF, hEnds⟩ := hab
    refine ⟨β.psiSE F, (β.isDangling_psiSE_iff hψ hT hT0 hMark F).mpr hF, ?_⟩
    rw [β.sourceEnds_psiSE]
    rcases hEnds with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **The retracted fibre over an old vertex is unchanged by the regrowth.** -/
theorem retractedFibre_psiSV (x : T.V) (v : ψ.SourceVertex) :
    retractedFibre (data := β.regrowDatum) (oldV c β.x x) (retractVertex (β.psiSV v)) =
      retractedFibre (data := ψ) x (retractVertex v) := by
  classical
  unfold retractedFibre
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image β.psiSV)) ?_]
  · rw [Finset.sum_image (fun _ _ _ _ h ↦ β.psiSV_injective h)]
    refine Finset.sum_congr rfl fun Y _ ↦ ?_
    have hcard : (β.regrowDatum.vertexPartition (β.psiSV Y).1.1).blockCard (β.psiSV Y).1.2 =
        (ψ.vertexPartition Y.1.1).blockCard Y.1.2 := by
      change (liftPart β.e (ψ.vertexPartition Y.1.1)).blockCard (old β.e Y.1.2) = _
      exact liftPart_blockCard_old _ _
    rw [hcard]
    have hiff : (retractVertex (β.psiSV Y) = retractVertex (β.psiSV v) ∧
        (β.psiSV Y).1.1 = oldV c β.x x) ↔ (retractVertex Y = retractVertex v ∧ Y.1.1 = x) := by
      rw [retractVertex_psiSV_iff β hψ hT hT0 hMark, CatBranching.psiSV_target, oldV_inj]
    exact if_congr hiff rfl rfl
  · intro X _ hX
    rcases β.sourceVertex_cases X with ⟨Y, rfl⟩ | ⟨v', n, -⟩ | ⟨w, q, rfl⟩
    · exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ Y)) hX
    · exact isEmptyElim n
    · split_ifs with h
      · exact absurd h.2 (tailV_ne_oldV c β.x x w)
      · rfl

end Anchor

end DiagonalSecant.CM
