module

public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrRegrowIdent

@[expose] public section

/-!
# The inverse laws, part 6: restriction after regrowth

For the decomposition theorem (restriction
after regrowth is the identity). For the regrown frame `F = regrowTailed T hc hd J κ s`, the
restriction (`TailRestrict`, read at `M = F.member 0`) finds exactly what regrowth attached:

* the tail vertices it deletes are the regrown ones (`xSpine_regrow`, `xBulb_regrow`,
  `xLeaf_regrow`), so the kept vertices are the old ones (`mem_Keep_regrow`);
* its lone path edges are the block edges, so its slopes are `s` (`sPath_regrow`) and its lower
  index is `J` (`lowerNat_regrow`);
* its lone sheets are the new sheets (`isLone_iff_regrow`).

This module builds the target dictionary (`tv`, `te`) and the comparison of the restricted datum
with `κ.data` extended by the new sheets (`extIso`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) (hd : IsTailDegree n p c degree)
  (J : LowerIndex c) (κ : TypedFrame core mark (lowerType c J) (degree - shed J))
  (s : SlopeData c J)

local notation "F" => regrowTailed T hc hd J κ s
local notation "β" => branching hd J κ s
local notation "M" => DraismaVargas.Count.SegmentWalls.Frame.member (regrowTailed T hc hd J κ s) 0

/-! ## 1.  The tails of the regrowth, as restriction finds them -/

/-- The source vertex restriction names at a tail vertex of `H` is the regrown block vertex. -/
theorem vSource_regrow_tail (j : Fin k) (w : CatVertex (c j)) :
    TailAt.vSource M (T.vertexEquiv (.inr ⟨j, w⟩)) = (β).blockSV ⟨j, Sum.inl w⟩ :=
  ident_vertex_symm_tail T hc hd J κ s j w

/-- The source vertex restriction names at a mark is the old source vertex of the mark. -/
theorem uSource_regrow (j : Fin k) :
    TailRestrict.uSource T M j = (β).psiSV (κ.markSource j) :=
  ident_vertex_symm_mark T hc hd J κ s j

theorem xMark_regrow (j : Fin k) : TailRestrict.xMark T M j = oldV c (β).x ((β).x j) := by
  unfold TailRestrict.xMark
  rw [uSource_regrow]
  rfl

theorem xSpine_regrow (j : Fin k) (i : Fin (c j)) :
    TailRestrict.xSpine T M j i = tailV c (β).x ⟨j, spine i⟩ := by
  unfold TailRestrict.xSpine
  rw [TailAt.spineV, TailRestrict.cat_vertex, vSource_regrow_tail]
  rfl

theorem xBulb_regrow (j : Fin k) (i : Fin (c j + 1)) :
    TailRestrict.xBulb T M j i = tailV c (β).x ⟨j, bulb i⟩ := by
  rw [TailRestrict.xBulb_eq, TailRestrict.cat_vertex, vSource_regrow_tail]
  rfl

/-- An edge at a tail vertex is a tail edge at one of its slots. -/
theorem exists_slot_of_mem_tailV {Tg : CFGraph.{0}} {x : Fin k → Tg.V} {j : Fin k}
    {w : TailV (c j)} {e : (catTarget c Tg x).edges}
    (he : e ∈ GluingDatum.incidentEdges (tailV c x ⟨j, w⟩)) :
    ∃ s ∈ incSlots w, e = tailE c x ⟨j, s⟩ := by
  rw [incidentEdges_tailV, Finset.mem_map] at he
  obtain ⟨s, hs, rfl⟩ := he
  exact ⟨s, hs, rfl⟩

theorem xLeaf_regrow (j : Fin k) (i : Fin (c j + 1)) :
    TailRestrict.xLeaf T M j i = tailV c (β).x ⟨j, tip i⟩ := by
  have hL : TailRestrict.tEdge T hc M j (Sum.inr (Sum.inr i)) ∈
      GluingDatum.incidentEdges (TailRestrict.xLeaf T M j i) := by
    rw [TailRestrict.incidentEdges_xLeaf T hc M]; exact Finset.mem_singleton_self _
  have hB : TailRestrict.tEdge T hc M j (Sum.inr (Sum.inr i)) ∈
      GluingDatum.incidentEdges (TailRestrict.xBulb T M j i) := by
    rw [TailRestrict.incidentEdges_xBulb T hc M]; simp
  rw [xBulb_regrow T hc hd J κ s] at hB
  obtain ⟨s₀, hs₀, he⟩ := exists_slot_of_mem_tailV hB
  rw [he] at hL
  rcases vertex_cases c (β).x (TailRestrict.xLeaf T M j i) with ⟨v, hv⟩ | ⟨⟨j', w⟩, hw⟩
  · exfalso
    rw [hv] at hL
    have hEnd := (TailRestrict.mem_incidentEdges_iff_end T M).mp hL
    rw [tailE_ends] at hEnd
    rcases hEnd with h | h
    · obtain ⟨-, hx⟩ := (tailEnd_eq_oldV_iff c (β).x _ v).mp h
      apply TailRestrict.xMark_ne_xLeaf T M j j i
      rw [hv, xMark_regrow T hc hd J κ s, ← hx]
    · exact headEnd_ne_oldV c (β).x _ v h
  · rw [hw] at hL ⊢
    obtain ⟨s₁, hs₁, he₁⟩ := exists_slot_of_mem_tailV hL
    have h₁ := tailE_injective c (β).x he₁
    rcases Sigma.mk.inj_iff.mp h₁ with ⟨rfl, h₂⟩
    obtain rfl := eq_of_heq h₂
    rcases TailV.cases w with ⟨i', rfl⟩ | ⟨i', rfl⟩ | ⟨i', rfl⟩
    · exact absurd ((xSpine_regrow T hc hd J κ s j i').trans hw.symm)
        (TailRestrict.xSpine_ne_xLeaf T hc M j i' j i)
    · exact absurd ((xBulb_regrow T hc hd J κ s j i').trans hw.symm)
        (TailRestrict.xBulb_ne_xLeaf T M j i' j i)
    · rw [incSlots_tip, Finset.mem_singleton] at hs₁
      subst hs₁
      rw [incSlots_bulb] at hs₀
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs₀
      rcases hs₀ with h | h
      · exact absurd h.symm (inBridge_ne_loop _ _)
      · rw [loop_inj] at h
        rw [h]

/-! ## 2.  The slopes and the lower index -/

/-- **The lone path edge restriction finds is the block edge** of the path slot. -/
theorem pathE_regrow (j : Fin k) (i : Fin (c j + 1)) :
    TailAt.pathE (TailRestrict.cat T j) M (T.cubic hc) i =
      (β).rowND (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s) ⟨j, path i⟩ := by
  symm
  refine ((TailAt.lone_pathE (TailRestrict.cat T j) M (T.cubic hc) i).1 _).mp ?_
  unfold TailAt.row
  rw [TailRestrict.cat_slot]
  exact (ident_row_symm_tail T hc hd J κ s ⟨j, path i⟩).symm

/-- **The slopes of the regrowth are `s`.** -/
theorem sPath_regrow (j : Fin k) (i : Fin (c j + 1)) :
    TailRestrict.sPath T hc M j i = (s j).1 i := by
  unfold TailRestrict.sPath
  rw [pathE_regrow]
  change (β).regrowDatum.sourceEdgeIndex ((β).tailSE ⟨j, path i⟩ ((β).rowAnchor ⟨j, path i⟩)) = _
  rw [CatBranching.sourceEdgeIndex_tailSE]
  have hmem : (β).rowAnchor ⟨j, path i⟩ ∈ (β).eB ⟨j, path i⟩ :=
    ((β).valid j).eA_mem (s := path i) fun i' ↦ path_ne_loop i i'
  rw [ite_eq_left hmem]
  exact card_P hd J κ s j i

/-- **The lower index of the regrowth is `J`.** -/
theorem lowerNat_regrow (j : Fin k) : TailRestrict.lowerNat T hc F j = J j := by
  unfold TailRestrict.lowerNat
  rw [sPath_regrow]
  have h := slope_first (s j).2
  omega

/-! ## 3.  The kept vertices are the old ones -/

/-- The restriction's names of the deleted vertices, in the regrown target. -/
def tvOf : (Σ j, TailRestrict.TailV (c j)) → TV c
  | ⟨j, Sum.inl i⟩ => ⟨j, spine i⟩
  | ⟨j, Sum.inr (Sum.inl i)⟩ => ⟨j, bulb i⟩
  | ⟨j, Sum.inr (Sum.inr i)⟩ => ⟨j, tip i⟩

theorem tailVertex_regrow (q : Σ j, TailRestrict.TailV (c j)) :
    TailRestrict.tailVertex T M q = tailV c (β).x (tvOf q) := by
  obtain ⟨j, i | i | i⟩ := q
  · exact xSpine_regrow T hc hd J κ s j i
  · exact xBulb_regrow T hc hd J κ s j i
  · exact xLeaf_regrow T hc hd J κ s j i

theorem mem_Keep_regrow (v : (M).target.V) :
    v ∈ TailRestrict.Keep T M ↔ ∃ w, v = oldV c (β).x w := by
  rw [TailRestrict.mem_Keep]
  constructor
  · intro h
    rcases vertex_cases c (β).x v with ⟨w, rfl⟩ | ⟨⟨j, w⟩, rfl⟩
    · exact ⟨w, rfl⟩
    · exfalso
      rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact h ⟨j, Sum.inl i⟩ (tailVertex_regrow T hc hd J κ s _)
      · exact h ⟨j, Sum.inr (Sum.inl i)⟩ (tailVertex_regrow T hc hd J κ s _)
      · exact h ⟨j, Sum.inr (Sum.inr i)⟩ (tailVertex_regrow T hc hd J κ s _)
  · rintro ⟨w, rfl⟩ q hq
    rw [tailVertex_regrow] at hq
    exact tailV_ne_oldV c (β).x w _ hq

theorem oldV_mem_Keep (w : κ.target.V) : oldV c (β).x w ∈ TailRestrict.Keep T M :=
  (mem_Keep_regrow T hc hd J κ s _).mpr ⟨w, rfl⟩

theorem tailV_notMem_Keep (w : TV c) : tailV c (β).x w ∉ TailRestrict.Keep T M := by
  intro h
  obtain ⟨v, hv⟩ := (mem_Keep_regrow T hc hd J κ s _).mp h
  exact tailV_ne_oldV c (β).x v w hv

/-! ## 4.  The target dictionary -/

/-- The restricted target vertex of an old vertex. -/
def keepV (w : κ.target.V) : (TailRestrict.rTarget T hc M).V :=
  vRestrict (oldV c (β).x w) (oldV_mem_Keep T hc hd J κ s w)

theorem keepV_bijective : Function.Bijective (keepV T hc hd J κ s) := by
  constructor
  · intro w w' h
    exact oldV_injective c (β).x (congrArg vIncl h)
  · intro v
    obtain ⟨w, hw⟩ := (mem_Keep_regrow T hc hd J κ s (vIncl v)).mp (vIncl_mem v)
    exact ⟨w, vIncl_injective hw.symm⟩

/-- **The target vertex dictionary**: restriction of the regrowth to `κ`. -/
def tv : (TailRestrict.rTarget T hc M).V ≃ κ.target.V :=
  (Equiv.ofBijective _ (keepV_bijective T hc hd J κ s)).symm

theorem oldV_tv (v : (TailRestrict.rTarget T hc M).V) :
    oldV c (β).x (tv T hc hd J κ s v) = vIncl v := by
  have h : keepV T hc hd J κ s (tv T hc hd J κ s v) = v :=
    (Equiv.ofBijective _ (keepV_bijective T hc hd J κ s)).apply_symm_apply v
  exact congrArg vIncl h

theorem keptEdge_oldE (e : κ.target.edges) :
    KeptEdge (TailRestrict.Keep T M) (oldE c (β).x e) := by
  unfold KeptEdge
  rw [oldE_ends]
  exact ⟨oldV_mem_Keep T hc hd J κ s _, oldV_mem_Keep T hc hd J κ s _⟩

/-- An old edge, as a kept edge. -/
def keepE (e : κ.target.edges) :
    {e : (M).target.edges // KeptEdge (TailRestrict.Keep T M) e} :=
  ⟨oldE c (β).x e, keptEdge_oldE T hc hd J κ s e⟩

theorem keepE_bijective : Function.Bijective (keepE T hc hd J κ s) := by
  constructor
  · intro e e' h
    exact oldE_injective c (β).x (congrArg Subtype.val h)
  · rintro ⟨e, he⟩
    rcases edge_cases c (β).x e with ⟨f, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨f, rfl⟩
    · exfalso
      have h := he.2
      rw [tailE_ends] at h
      exact tailV_notMem_Keep T hc hd J κ s _ h

/-- **The target edge dictionary.** -/
def te : (TailRestrict.rTarget T hc M).edges ≃ κ.target.edges :=
  (edgeEquiv (Keep := TailRestrict.Keep T M)
    (hKeep := TailRestrict.Keep_nonempty T hc M)).trans
    (Equiv.ofBijective _ (keepE_bijective T hc hd J κ s)).symm

theorem oldE_te (e : (TailRestrict.rTarget T hc M).edges) :
    oldE c (β).x (te T hc hd J κ s e) = edgeIncl e := by
  have h : keepE T hc hd J κ s (te T hc hd J κ s e) = ⟨edgeIncl e, keptEdge_edgeIncl e⟩ :=
    (Equiv.ofBijective _ (keepE_bijective T hc hd J κ s)).apply_symm_apply _
  exact congrArg Subtype.val h

/-! ## 5.  The restricted datum is `κ.data` with the new sheets -/

/-- `κ.data` with the new sheets of the regrowth, as a sheet extension. -/
abbrev extData : GluingDatum κ.target degree := Sheets.extendSheets κ.data (sheetEquiv hd J).symm

theorem rData_vp (v : (TailRestrict.rTarget T hc M).V) :
    (TailRestrict.rData T hc M).vertexPartition v =
      liftPart (β).e (κ.data.vertexPartition (tv T hc hd J κ s v)) := by
  exact (congrArg (fun w ↦ (β).regrowDatum.vertexPartition w) (oldV_tv T hc hd J κ s v)).symm

theorem rData_ep (e : (TailRestrict.rTarget T hc M).edges) :
    (TailRestrict.rData T hc M).edgePartition e =
      liftPart (β).e (κ.data.edgePartition (te T hc hd J κ s e)) := by
  exact (congrArg (fun w ↦ (β).regrowDatum.edgePartition w) (oldE_te T hc hd J κ s e)).symm.trans
    (CatBranching.ep_oldE _ _)

/-- **The restricted datum of the regrowth is `κ.data` with the new sheets**, over the target
dictionary, with identity sheet permutations. -/
def extIso : GeometricDatumIso (TailRestrict.rData T hc M) (extData hd J κ) where
  targetVertex := tv T hc hd J κ s
  targetEdge := te T hc hd J κ s
  ends e := by
    left
    have h := oldE_ends c (β).x (te T hc hd J κ s e)
    rw [oldE_te] at h
    apply Prod.ext <;> apply oldV_injective c (β).x
    · rw [oldV_tv]
      exact (congrArg Prod.fst h).symm.trans (edgeIncl_fst e)
    · rw [oldV_tv]
      exact (congrArg Prod.snd h).symm.trans (edgeIncl_snd e)
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition v := by
    rw [Transport.DatumIso.relabel_refl, rData_vp]
    rfl
  edgePartition e := by
    rw [Transport.DatumIso.relabel_refl, rData_ep]
    rfl
  compatible _ _ _ _ := by
    simp only [Equiv.refl_apply, Equiv.refl_symm]
    rfl

/-! ## 6.  The lone sheets are the new sheets -/

theorem isLone_new (n : Fin (shed J)) :
    Sheets.IsLone (TailRestrict.rData T hc M) (new (β).e n) := by
  intro v q h
  rw [rData_vp] at h
  exact (liftPart_rel_new_iff _ n q).mp h

theorem isLone_iff_regrow (i : Fin degree) :
    Sheets.IsLone (TailRestrict.rData T hc M) i ↔ ∃ n, new (β).e n = i := by
  classical
  constructor
  · intro hi
    have hSub : Finset.univ.image (new (β).e) ⊆ TailRestrict.loneSet T hc M := by
      intro q hq
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hq
      exact (TailRestrict.mem_loneSet T hc M).mpr (isLone_new T hc hd J κ s n)
    have hCard : (TailRestrict.loneSet T hc M).card ≤ (Finset.univ.image (new (β).e)).card := by
      rw [Finset.card_image_of_injective _ new_injective, Finset.card_univ, Fintype.card_fin]
      have h := TailRestrict.sum_lowerNat T hc F
      have h2 : ∑ j, (J j : ℕ) = ∑ j, (TailRestrict.lowerIdx T hc F j : ℕ) :=
        Finset.sum_congr rfl fun j _ ↦ (lowerNat_regrow T hc hd J κ s j).symm
      exact le_of_eq (h.symm.trans h2.symm)
    have hEq := Finset.eq_of_subset_of_card_le hSub hCard
    have hi' := (TailRestrict.mem_loneSet T hc M).mpr hi
    rw [← hEq] at hi'
    obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hi'
    exact ⟨n, hn⟩
  · rintro ⟨n, rfl⟩
    exact isLone_new T hc hd J κ s n

/-! ## 7.  The isomorphism of typed frames -/

theorem isNew_iff_regrow (m : ℕ) (hm : m + TailRestrict.nShed T hc M = degree) (i : Fin degree) :
    Sheets.IsNew (sheetEquiv hd J).symm i ↔ Sheets.IsNew (TailRestrict.split T hc M m hm) i := by
  rw [TailRestrict.isNew_split_iff, isLone_iff_regrow, Sheets.isNew_iff, Equiv.symm_symm]
  rfl

theorem hJreg (j : Fin k) : (J j : ℕ) = TailRestrict.lowerNat T hc F j :=
  (lowerNat_regrow T hc hd J κ s j).symm

/-- The restriction of the regrowth, as a typed frame at the lower index `J`. -/
abbrev resFrame : TypedFrame core mark (lowerType c J) (degree - shed J) :=
  TailRestrict.typedFrameAt T hc F J (hJreg T hc hd J κ s)

/-- A literal equality of data, as an isomorphism. -/
def isoOfEq {Tg : CFGraph.{0}} {d : ℕ} {D₁ D₂ : GluingDatum Tg d} (h : D₁ = D₂) :
    GeometricDatumIso D₁ D₂ where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends _ := Or.inl rfl
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition v := by subst h; exact (Transport.DatumIso.relabel_refl _).symm
  edgePartition e := by subst h; exact (Transport.DatumIso.relabel_refl _).symm
  compatible _ _ _ _ := by
    subst h
    simp only [Equiv.refl_apply, Equiv.refl_symm]
    rfl

/-- **The datum of the restriction of the regrowth is `κ.data`**: `extIso`, with the new sheets
deleted on both sides. -/
def datIso : GeometricDatumIso (resFrame T hc hd J κ s).data κ.data :=
  (Sheets.restrictSheetsIso (h₂ := Sheets.isLone_extendSheets κ.data (sheetEquiv hd J).symm)
      (hm₂ := κ.data.degree_pos) (extIso T hc hd J κ s)
      (fun _ i ↦ isNew_iff_regrow T hc hd J κ s _ _ i)
      (fun _ i ↦ isNew_iff_regrow T hc hd J κ s _ _ i)).trans
    (isoOfEq (Sheets.restrictSheets_extendSheets κ.data (sheetEquiv hd J).symm))

theorem psiSV_datIso (X : (resFrame T hc hd J κ s).data.SourceVertex) :
    (β).psiSV ((datIso T hc hd J κ s).sourceVertexEquiv X) =
      TailRestrict.cSV T hc M _ (TailRestrict.mDegAt_add T hc F J (hJreg T hc hd J κ s)) X := by
  have h := congrArg Subtype.val (Sheets.inclSV_restrictSheetsIso
    (h₂ := Sheets.isLone_extendSheets κ.data (sheetEquiv hd J).symm)
    (hm₂ := κ.data.degree_pos) (extIso T hc hd J κ s)
    (fun _ i ↦ isNew_iff_regrow T hc hd J κ s _ _ i)
    (fun _ i ↦ isNew_iff_regrow T hc hd J κ s _ _ i) X)
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (oldV c (β).x) (congrArg Prod.fst h)).trans (oldV_tv T hc hd J κ s _)
  · have h2 := congrArg Prod.snd h
    exact h2

theorem psiSE_datIso (E : (resFrame T hc hd J κ s).data.SourceEdge) :
    (β).psiSE ((datIso T hc hd J κ s).sourceEdgeEquiv E) =
      TailRestrict.cSE T hc M _ (TailRestrict.mDegAt_add T hc F J (hJreg T hc hd J κ s)) E := by
  have h := congrArg Subtype.val (Sheets.inclSE_restrictSheetsIso
    (h₂ := Sheets.isLone_extendSheets κ.data (sheetEquiv hd J).symm)
    (hm₂ := κ.data.degree_pos) (extIso T hc hd J κ s)
    (fun _ i ↦ isNew_iff_regrow T hc hd J κ s _ _ i)
    (fun _ i ↦ isNew_iff_regrow T hc hd J κ s _ _ i) E)
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (oldE c (β).x) (congrArg Prod.fst h)).trans (oldE_te T hc hd J κ s _)
  · have h2 := congrArg Prod.snd h
    exact h2

/-- **Restriction after regrowth is `κ`**, up to isomorphism of typed frames. -/
def resIso : TypedFrameIso (resFrame T hc hd J κ s) κ where
  datum := datIso T hc hd J κ s
  mark j := by
    apply (β).psiSV_injective
    rw [psiSV_datIso]
    exact (TailRestrict.cSV_markSrc T hc M _ _ j).trans (uSource_regrow T hc hd J κ s j)
  overCore_vertex vertex hImage := by
    apply TailRestrict.oldVertex_injective T
    refine Eq.trans ?_ (TailRestrict.oldVertex_vertexEquiv T hc M _ _ vertex).symm
    have key : (F).ident.vertex.symm (T.oldVertex (κ.ident.vertex ⟨_, hImage⟩)) =
        TailRestrict.branchOf T hc M _ _ vertex := by
      apply Subtype.ext
      refine (ident_vertex_symm_old T hc hd J κ s _).trans ?_
      have hY := Equiv.symm_apply_apply κ.ident.vertex ⟨_, hImage⟩
      exact (congrArg (fun Z ↦ (β).psiSV Z.1) hY).trans (psiSV_datIso T hc hd J κ s vertex.1)
    rw [← key]
    exact (Equiv.apply_symm_apply (F).ident.vertex _).symm
  overCore_row edge := by
    apply T.coreSlot_injective
    refine Eq.trans ?_ (TailRestrict.coreSlot_rowEquiv T hc M _ _ edge).symm
    have hE : TailRestrict.ndInc T hc M _ _ edge =
        (β).oldND (hψ J κ) (hT J κ) (hT0 J κ) (hMark hd J κ s)
          ((datIso T hc hd J κ s).nonDanglingEdgeEquiv
            (resFrame T hc hd J κ s).fullDim.valid.1 edge) :=
      Subtype.ext (psiSE_datIso T hc hd J κ s edge.1).symm
    rw [hE]
    refine Eq.trans ?_ (ident_row_stablePath T hc hd J κ s _).symm
    rw [CatBranching.rowTag_oldND]
    rfl

/-- **Restriction after regrowth is the identity** on lower classes (the decomposition theorem). -/
theorem restrictTailed_regrowTailed_eq :
    (restrictTailed T hc F).toClass = ⟨J, TypedFrameClass.mk κ, s⟩ := by
  have key : ∀ (J' : LowerIndex c) (h : ∀ j, (J' j : ℕ) = TailRestrict.lowerNat T hc F j),
      J' = TailRestrict.lowerIdx T hc F →
      (restrictTailed T hc F).toClass =
        ⟨J', TypedFrameClass.mk (TailRestrict.typedFrameAt T hc F J' h),
          TailRestrict.slopeSeqAt T hc F J' h⟩ := by
    rintro J' h rfl
    rfl
  have hJ : J = TailRestrict.lowerIdx T hc F := funext fun j ↦ Fin.ext (hJreg T hc hd J κ s j)
  rw [key J (hJreg T hc hd J κ s) hJ]
  have hs : TailRestrict.slopeSeqAt T hc F J (hJreg T hc hd J κ s) = s :=
    funext fun j ↦ Subtype.ext (funext fun i ↦ sPath_regrow T hc hd J κ s j i)
  rw [hs, TypedFrameClass.mk_eq_mk_of_iso ⟨resIso T hc hd J κ s⟩]

end

end CatRegrow

end DraismaVargas.Count.MarkedCountGeneral
