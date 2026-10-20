module

public import DiagonalSecant.CMDictionary
public import DiagonalSecant.TypedMoments

@[expose] public section

/-!
# The mark's image is an admissible root (tailed form)

The root over which the typed fibre is pushed may be a leaf of the target. The statement that
the image of a mark is an admissible root (`TypedMoments.AdmissibleRoot`) cannot be had for
every typed frame by the public argument: its leaf case ("over the image of a mark that is a
leaf of the target, every surviving source vertex is a mark") is the
leaf dichotomy of `LeafFibre`, which the public side derives from change-minimality and
dangling-no-glue, neither of which a typed frame has at the image of a mark (the type excess sits
there). This module proves it for the typed frames the theorem uses, those of a lower type over
a marked-cubic core with a tailed core at the headline degree, **through the regrowth**:

* on the regrown frame `f` the image `oldV x` of the mark has valency at least two (the tail
  hangs there), and `f` is change-minimal (`FullDimensionalSourcePresentation.targetExcess_eq_zero`),
  so the change at `oldV x` is at most `1`;
* a surviving non-mark source vertex `v` over the leaf `x` has at least two source occurrences
  over the leaf edge `t`, so at least two blocks over `t` (`two_le_blockCountWithin`); its block
  is disjoint from the tail's first block `P_1` (that block lies in the mark's), so over the tail
  edge it splits into singletons; its local ramification on `f` is then
  `k_t + m − 2 ≥ 2` (`localRamification_psiSV_of_leaf`), which exceeds the change.

The model instance is `admissibleRoot_mark_of_model`. The assembly of the diagonal secant
theorem does not use it: the hairpin receipt (`CMHairpin.lean`) subsumes the root condition.
-/

namespace DiagonalSecant.CM

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.MarkedCountGeneral.CatRegrow
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open DiagonalSecant.TypedMoments (AdmissibleRoot)

/-! ## 1.  Blocks over the leaf edge, on any datum -/

section Datum

variable {target : CFGraph.{0}} {degree : ℕ} (data : GluingDatum target degree)

/-- An incident source occurrence lies over an incident target occurrence, and its sheet is in
the vertex's block. -/
theorem mem_incidentEdges_of_incident {e : data.SourceEdge} {v : data.SourceVertex}
    (h : Incident data e v) :
    e.1.1 ∈ incidentEdges v.1.1 ∧ (data.vertexPartition v.1.1).Rel v.1.2 e.1.2 := by
  unfold Incident GluingDatum.sourceEnds at h
  rw [GluingDatum.incidentEdges, Finset.mem_filter]
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := (data.sourceEndpoint_eq_iff _ _ _).mp h
    refine ⟨⟨Finset.mem_univ _, Or.inl h1⟩, ?_⟩
    rw [← h1]
    unfold SheetPartition.Rel at h2 ⊢
    exact h2.symm
  · obtain ⟨h1, h2⟩ := (data.sourceEndpoint_eq_iff _ _ _).mp h
    refine ⟨⟨Finset.mem_univ _, Or.inr h1⟩, ?_⟩
    rw [← h1]
    unfold SheetPartition.Rel at h2 ⊢
    exact h2.symm

/-- Two distinct source occurrences over one target occurrence have distinct sheets. -/
theorem sheet_ne_of_ne {e e' : data.SourceEdge} (hne : e ≠ e') (ht : e.1.1 = e'.1.1) :
    e.1.2 ≠ e'.1.2 := by
  intro h
  exact hne (Subtype.ext (Prod.ext ht h))

/-- **At least two blocks over the leaf edge** at a source vertex of surviving valency at least
two over a leaf: its two surviving occurrences both lie over the leaf edge. -/
theorem two_le_blockCountWithin {v : data.SourceVertex} {t : target.edges}
    (ht : incidentEdges v.1.1 = {t}) (hnd : 2 ≤ nonDanglingValency data v) :
    2 ≤ (data.edgePartition t).blockCountWithin (data.vertexPartition v.1.1) v.1.2 := by
  classical
  rw [← card_nonDanglingIncident] at hnd
  obtain ⟨e, he, e', he', hne⟩ := Finset.one_lt_card.mp hnd
  rw [mem_nonDanglingIncident] at he he'
  obtain ⟨hte, hre⟩ := mem_incidentEdges_of_incident data he.2
  obtain ⟨hte', hre'⟩ := mem_incidentEdges_of_incident data he'.2
  rw [ht, Finset.mem_singleton] at hte hte'
  have hsheet : e.1.2 ≠ e'.1.2 := sheet_ne_of_ne data hne (hte.trans hte'.symm)
  unfold SheetPartition.blockCountWithin
  have hsub : ({e.1.2, e'.1.2} : Finset (Fin degree)) ⊆
      ((data.vertexPartition v.1.1).block v.1.2).image (data.edgePartition t).repr := by
    intro q hq
    rw [Finset.mem_insert, Finset.mem_singleton] at hq
    rw [Finset.mem_image]
    rcases hq with rfl | rfl
    · refine ⟨e.1.2, ?_, ?_⟩
      · rw [SheetPartition.mem_block_iff]; exact hre
      · rw [← hte]; exact e.2
    · refine ⟨e'.1.2, ?_, ?_⟩
      · rw [SheetPartition.mem_block_iff]; exact hre'
      · rw [← hte']; exact e'.2
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hsheet] at this

/-- The block count over an incident occurrence is at most the block size. -/
theorem blockCountWithin_le_blockCard_of_mem {x : target.V} {t : target.edges}
    (ht : t ∈ incidentEdges x) (q : Fin degree)
    (hq : (data.vertexPartition x).repr q = q) :
    (data.edgePartition t).blockCountWithin (data.vertexPartition x) q ≤
      (data.vertexPartition x).blockCard q := by
  have hRefines : (data.edgePartition t).Refines (data.vertexPartition x) := by
    rw [GluingDatum.incidentEdges, Finset.mem_filter] at ht
    rcases ht.2 with h | h
    · simpa [h] using data.refines_left t
    · simpa [h] using data.refines_right t
  exact SheetPartition.blockCountWithin_le_blockCard _ _ hRefines ⟨q, hq⟩

end Datum

/-! ## 2.  The local ramification of an old non-mark vertex over a leaf, on the regrowth -/

section Branching

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c)

open CatSlot TailV

/-- The first tail block at a mark over `v.1.1` is disjoint from the (lifted) block of a
non-mark `v`. -/
theorem disjoint_eB_path_zero {v : ψ.SourceVertex} {j : Fin k} (hx : β.x j = v.1.1)
    (hvm : β.mark j ≠ v) :
    Disjoint (β.eB ⟨j, path 0⟩) ((liftPart β.e (ψ.vertexPartition v.1.1)).block (old β.e v.1.2)) := by
  rw [Finset.disjoint_left]
  intro a ha hmem
  have ha' : a ∈ (β.chain j).P 0 := by
    change a ∈ (β.chain j).eB (path 0) at ha
    rwa [TailChain.eB_path] at ha
  obtain ⟨i, rfl, hi⟩ := β.P0_sub j a ha'
  rw [SheetPartition.mem_block_iff, liftPart_rel_old_old] at hmem
  apply hvm
  rw [β.mark_eq j]
  apply (ψ.sourceEndpoint_eq_iff _ _ _).mpr
  refine ⟨hx, ?_⟩
  change (ψ.vertexPartition (β.x j)).Rel (β.a j) i at hi
  rw [hx] at hi ⊢
  unfold SheetPartition.Rel at hi hmem ⊢
  exact hi.trans hmem.symm

/-- **The local ramification of a non-mark old vertex over a leaf, on the regrowth**:
`k_t(v) + m(v) − 2`, where `t` is the leaf edge, because every tail occurrence at the leaf
splits `v`'s block into singletons. -/
theorem localRamification_psiSV_of_leaf {v : ψ.SourceVertex} {t : T.edges}
    (ht : incidentEdges v.1.1 = {t}) (hvm : ∀ j, β.x j = v.1.1 → β.mark j ≠ v) :
    β.regrowDatum.localRamification (oldV c β.x v.1.1) ⟨old β.e v.1.2, (β.psiSV v).2⟩ =
      ((ψ.edgePartition t).blockCountWithin (ψ.vertexPartition v.1.1) v.1.2 : ℤ) +
        ((ψ.vertexPartition v.1.1).blockCard v.1.2 : ℤ) - 2 := by
  classical
  unfold GluingDatum.localRamification
  rw [sum_incidentEdges_oldV, card_incidentEdges_oldV, ht, Finset.sum_singleton,
    Finset.card_singleton]
  simp only [CatBranching.vp_oldV, CatBranching.ep_oldE, CatBranching.ep_tailE,
    liftPart_blockCountWithin_old, liftPart_blockCard_old]
  have htail : ∀ j ∈ Finset.univ.filter (fun j ↦ β.x j = v.1.1),
      ((blockPart (β.eB ⟨j, path 0⟩) (β.eA ⟨j, path 0⟩)).blockCountWithin
        (liftPart β.e (ψ.vertexPartition v.1.1)) (old β.e v.1.2) : ℤ) =
      ((ψ.vertexPartition v.1.1).blockCard v.1.2 : ℤ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [blockCountWithin_blockPart_of_disjoint (disjoint_eB_path_zero β hj.2 (hvm j hj.2)),
      liftPart_blockCard_old]
  rw [Finset.sum_congr rfl htail, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

end Branching

/-! ## 3.  The admissible root, for typed frames of a tailed core -/

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) (hd : IsTailDegree n p c degree)
  (J : LowerIndex c) (κ : TypedFrame core mark (lowerType c J) (degree - shed J))
  (s : SlopeData c J)

include T hc hd s in
/-- **No surviving non-mark source vertex over the image of a mark that is a leaf**, for a typed
frame that regrows: the change of the regrown frame at that image is at most `1`, and such a
vertex would contribute at least `2`. -/
theorem not_survives_of_leaf (j : Fin k) (hLeaf : IsLeafVertex κ.target (κ.markSource j).1.1)
    (v : κ.data.SourceVertex) (hv : v.1.1 = (κ.markSource j).1.1)
    (hpos : 0 < nonDanglingValency κ.data v) (hvm : v ∉ markSet κ.markSource) : False := by
  classical
  set β := CatRegrow.branching hd J κ s with hβ
  set f := regrowTailed T hc hd J κ s with hf
  have hdata : f.data = β.regrowDatum := rfl
  -- the leaf edge
  have hLeaf' : IsLeafVertex κ.target v.1.1 := by rw [hv]; exact hLeaf
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hLeaf'
  -- the regrown frame is change-minimal at the image, which has valency at least two there
  have hExcess := f.fullDim.targetExcess_eq_zero (oldV c β.x v.1.1)
  unfold GluingDatum.targetExcess at hExcess
  have hCard := card_incidentEdges_oldV c β.x v.1.1
  rw [ht, Finset.card_singleton] at hCard
  have hMarks : 1 ≤ (Finset.univ.filter (fun j' ↦ β.x j' = v.1.1)).card :=
    Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hβ, CatRegrow.branching_x, hv]⟩⟩
  -- the local ramification of `v` on the regrowth is at least two
  have hvm' : ∀ j', β.x j' = v.1.1 → β.mark j' ≠ v := fun j' _ h ↦
    hvm (h ▸ mem_markSet κ.markSource j')
  have hRam := localRamification_psiSV_of_leaf β ht hvm'
  have hnd : 2 ≤ nonDanglingValency κ.data v := by
    have := NonDanglingValency.nonDanglingValency_ne_one κ.data κ.fullDim.valid.1 v
    omega
  have hTwo := two_le_blockCountWithin κ.data ht hnd
  have hLe := blockCountWithin_le_blockCard_of_mem κ.data
    (x := v.1.1) (t := t) (by rw [ht]; exact Finset.mem_singleton_self t) v.1.2 v.2
  -- the change is at least the local ramification of `v`
  have hChange : β.regrowDatum.localRamification (oldV c β.x v.1.1)
      ⟨old β.e v.1.2, (β.psiSV v).2⟩ ≤ β.regrowDatum.targetChange (oldV c β.x v.1.1) := by
    unfold GluingDatum.targetChange
    exact Finset.single_le_sum (fun B _ ↦ β.regrowDatum.localRamification_nonneg _
      (f.fullDim.valid.2 _) B) (Finset.mem_univ _)
  rw [hRam] at hChange
  change β.regrowDatum.targetChange (oldV c β.x v.1.1) +
    ((incidentEdges (oldV c β.x v.1.1)).card : ℤ) - 3 = 0 at hExcess
  rw [hCard] at hExcess
  push_cast at hExcess
  omega

include T hc hd s in
/-- **The mark's image is an admissible root**, for a typed frame that regrows. -/
theorem admissibleRoot_mark_of_tailed (j : Fin k) :
    AdmissibleRoot κ.data (markSet κ.markSource) (κ.markSource j).1.1 := by
  by_cases hLeaf : IsLeafVertex κ.target (κ.markSource j).1.1
  · right
    intro v hv hpos
    by_contra hvm
    exact not_survives_of_leaf T hc hd J κ s j hLeaf v hv hpos hvm
  · left
    exact hLeaf

/-! ## 4.  The model instance -/

section Model

open DiagonalSecant
open GenusSixExistence.Tripod.Gadget (subdivide)

variable {g : ℕ} {G : CFGraph.{0}} {u : (UnitSubdivisionPresentation.spec G).graph.V}

/-- The leaf-or-root predicate is invariant under the cast of a typed frame. -/
theorem admissibleRoot_cast_iff {n p k : ℕ} {core : Core n p} {mark : Fin k → Fin n}
    {types types' : Fin k → ℕ} {d d' : ℕ} (ht : types = types') (hd : d = d')
    (κ : TypedFrame core mark types d) (j : Fin k) :
    AdmissibleRoot (TypedFrame.cast ht hd κ).data (markSet (TypedFrame.cast ht hd κ).markSource)
      ((TypedFrame.cast ht hd κ).markSource j).1.1 ↔
    AdmissibleRoot κ.data (markSet κ.markSource) (κ.markSource j).1.1 := by
  subst ht hd
  rfl

/-- **The mark's image is an admissible root** for the typed member of the diagonal secant
theorem, at its mark. -/
theorem admissibleRoot_mark_of_model (M : OnceMarkedModel g G u) (hg5 : 5 ≤ g)
    (κ : TypedFrame M.markedCore (onceMark M.N) ![g - 4] (g - 1)) (j : Fin 1) :
    AdmissibleRoot κ.data (markSet κ.markSource) (κ.markSource j).1.1 := by
  have ha : 1 ≤ g - 4 := by omega
  have hd : IsTailDegree (M.N + 1) (M.Q + 1) (tailType (g - 4)) (g - 1) :=
    tailed_isTailDegree M.genus_eq ha (by omega)
  have hShed : (g - 1) - shed (c := tailType (g - 4)) (fun _ ↦ 0) = g - 1 := by
    rw [show shed (c := tailType (g - 4)) (fun _ ↦ 0) = 0 from Finset.sum_eq_zero fun _ _ ↦ rfl,
      Nat.sub_zero]
  have h := admissibleRoot_mark_of_tailed (tailed M.core M.slot (g - 4))
    (tailed_markedCubic M.cubic M.slot) hd (fun _ ↦ 0)
    (TypedFrame.cast (lowerType_tailType_zero ha).symm hShed.symm κ)
    (fun _ ↦ CM.zeroSlope _ rfl) j
  exact (admissibleRoot_cast_iff _ _ κ j).mp h

end Model

end DiagonalSecant.CM
