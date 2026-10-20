module

public import DiagonalSecant.CMWalk
public import DiagonalSecant.CMRetract
public import DiagonalSecant.CMRoot
public import DraismaVargasCount.RowHairpinPosition

@[expose] public section

/-!
# The hairpin receipt on marked rows, through the regrowth

The statement is the hairpin receipt (`TypedMoments.HairpinReceipt`, the typed form of
`RowHairpinPosition.weighted_prefix_mem`) for the typed frames that regrow: a typed frame
`κ` of lower index `0` over a marked-cubic core `(core, mark)` with a tailed core `T` at the
headline degree. (For a general `MarkedFullDim … excess`, which has no regrowth, the receipt is
not available; see the module docstring of `TypedMoments`.)

The generic form `weighted_prefix_mem_generic` is stated on a caterpillar branching `β` without
new sheets, for a typed presentation `fd` of `ψ` and any full-dimensional presentation `fdD` of
the regrown datum whose columns over the old edges carry `fd`'s coordinates. It transports
`RowHairpinPosition.weighted_prefix_mem` from `fdD`:

* `fdD`'s row of `κ`'s marked row `path` is `tagPath (inl path)`; its public ordered row starts at
  a path end that is an old edge at an old vertex (`nonDanglingEdge_cases`), which is a marked
  path end of `path`, so the public ordered row is the image under `psiSE` of the typed ordered
  row or of its reverse (`markedPathEnd_cases`, `markedTraverse_finish`, `traverse_psiSE`);
* the walk vertices, prefix positions and chip coefficients correspond term by term
  (`walkVertex_psiSE`, `walkVertex_reverse`, the column hypothesis, the index dictionary
  `sourceEdgeIndex_psiSE`, and `retractedFibre_psiSV`); in the reversed case the public
  position is the row's total length (an integer, `prefixPosition_full`) minus the typed one.

`weighted_prefix_mem_of_regrow` instantiates it at the regrown frame of a typed frame, where the
root is internal in the regrown target when it is internal in `κ.target` or the image of a mark
(`not_isLeafVertex_oldV`); `weighted_prefix_mem_of_model` is the instance at the once-marked
model, at the root `x_u`: it supplies the hairpin-receipt hypothesis of the generic chain
`collisionCoefficient_mem → … → exists_placedFibre_of_bigCore` in
`TypedRealisation.exists_placedFibre`.
-/

namespace DiagonalSecant.CM

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.OrientedTraversal (walkVertex)
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.MarkedCountGeneral.CatRegrow
open DraismaVargas.Count.PendantRetraction
open DraismaVargas.Count.SlotMoment (oddDenominatorSubring mem_oddDenominatorSubring)
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)

/-! ## 1.  The generic transport, on a branching without new sheets -/

section Generic

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c) [IsEmpty N]
  (hψ : ψ.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
  (hMark : ∀ j, nonDanglingValency ψ (β.mark j) ≠ 0)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate] {excess : ℤ}
  (fd : MarkedFullDim ψ β.marks coordinate excess)
  {coordD : Type*} [Fintype coordD] [DecidableEq coordD]
  (fdD : FullDimensionalSource.FullDimensionalSourcePresentation β.regrowDatum coordD)

include hψ hT hT0 hMark in
/-- **The hairpin receipt on a marked row of `ψ`, transported from the regrowth.** -/
theorem weighted_prefix_mem_generic (z : coordinate → ℚ) (yZ : coordinate → ℤ)
    (hSys : (LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec z =
      fun row ↦ (yZ row : ℚ))
    (zD : coordD → ℚ) (yD : coordD → ℤ)
    (hSysD : (LengthMatrixPresentation.matrix fdD.labelling.presentation).mulVec zD =
      fun row ↦ (yD row : ℚ))
    (hOddD : Odd (fdAbsMultNat fdD))
    (hcol : ∀ ε : T.edges, zD (fdD.labelling.targetEdge.symm (oldE c β.x ε)) =
      z (fd.labelling.targetEdge.symm ε))
    (path : MarkedStablePath ψ β.marks) {root : T.V}
    (hInternal : ¬ IsLeafVertex (catTarget c T β.x) (oldV c β.x root))
    {i : ℕ} (hi : i + 1 < (TypedRows.orderedRow fd.pathEnds path).length) :
    (retractedFibre root (retractVertex (TypedRows.rowVertex fd.pathEnds path (i + 1))) : ℚ) *
      TypedRows.prefixPosition fd z path (i + 1) ∈ oddDenominatorSubring := by
  classical
  set W := TypedRows.orderedRow fd.pathEnds path with hW
  have hLW : (TypedRows.orderedRow fd.pathEnds path).length = W.length := rfl
  set P' : StablePath β.regrowDatum := β.tagPath hψ hT hT0 hMark (Sum.inl path) with hP'
  -- the public start of the row of the regrowth
  set E₀ := RowWalk.startEdge fdD.pathEnds P' with hE₀def
  set X₀ := RowWalk.startVertex fdD.pathEnds P' with hX₀def
  have hE₀ : E₀.stablePath = P' := RowWalk.startEdge_stablePath _ _
  have hEnd₀ : IsPathEnd β.regrowDatum E₀.1 X₀ := RowWalk.startEdge_isPathEnd _ _
  -- it is an old occurrence of `path`, at an old vertex
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : NonDanglingEdge ψ, E₀ = β.oldND hψ hT hT0 hMark F₀ := by
    rcases β.nonDanglingEdge_cases hψ hT hT0 hMark E₀ with h | ⟨t, q, hq, h⟩
    · exact h
    · exfalso
      rw [h, β.stablePath_tailND hψ hT hT0 hMark, ← β.tagPath_inr hψ hT hT0 hMark, hP',
        ← β.stablePathEquiv_symm_apply, ← β.stablePathEquiv_symm_apply] at hE₀
      exact Sum.inr_ne_inl ((β.stablePathEquiv hψ hT hT0 hMark).symm.injective hE₀)
  have hrow : markedRow β.marks F₀ = path := by
    rw [hF₀] at hE₀
    rw [show (β.oldND hψ hT hT0 hMark F₀).stablePath =
        β.tagPath hψ hT hT0 hMark (Sum.inl (markedRow β.marks F₀)) from rfl, hP',
      ← β.stablePathEquiv_symm_apply, ← β.stablePathEquiv_symm_apply] at hE₀
    exact Sum.inl_injective ((β.stablePathEquiv hψ hT hT0 hMark).symm.injective hE₀)
  obtain ⟨Y₀, hY₀inc, hX₀⟩ : ∃ Y₀, Incident ψ F₀.1 Y₀ ∧ X₀ = β.psiSV Y₀ := by
    have hInc : Incident β.regrowDatum (β.psiSE F₀.1) X₀ := by
      have h := hEnd₀.1
      rw [hF₀] at h
      exact h
    unfold Incident at hInc
    rw [β.sourceEnds_psiSE] at hInc
    rcases hInc with h | h
    · exact ⟨_, incident_left ψ F₀.1, h.symm⟩
    · exact ⟨_, incident_right ψ F₀.1, h.symm⟩
  have hEnd : IsMarkedPathEnd ψ β.marks F₀.1 Y₀ := by
    refine ⟨hY₀inc, ?_⟩
    have h2 := hEnd₀.2
    rw [hX₀] at h2
    by_contra hcon
    push Not at hcon
    exact h2 ((β.nonDanglingValency_psiSV_eq_two_iff hψ hT hT0 hMark Y₀).mpr hcon)
  -- the public ordered row is the image of the marked traversal from that end
  have hOrd : RowWalk.orderedRow fdD.pathEnds P' =
      (TypedRows.markedTraverse ψ β.marks ∅ F₀.1 Y₀).map β.psiSE := by
    show traverse β.regrowDatum ∅ E₀.1 X₀ = _
    rw [hF₀, hX₀]
    have h := traverse_psiSE β hψ hT hT0 hMark ∅ F₀.1 Y₀ F₀.2
    rw [Finset.map_empty] at h
    exact h
  -- the term-by-term dictionary of positions
  have hterm : ∀ e : ψ.SourceEdge,
      zD (fdD.labelling.targetEdge.symm (β.psiSE e).1.1) /
          (β.regrowDatum.sourceEdgeIndex (β.psiSE e) : ℚ) =
        z (fd.labelling.targetEdge.symm e.1.1) / (ψ.sourceEdgeIndex e : ℚ) := by
    intro e
    rw [CatBranching.psiSE_target, β.sourceEdgeIndex_psiSE, hcol]
  have hpos : ∀ (l : List ψ.SourceEdge) (m : ℕ),
      (((l.map β.psiSE).take m).map fun edge ↦
        zD (fdD.labelling.targetEdge.symm edge.1.1) /
          (β.regrowDatum.sourceEdgeIndex edge : ℚ)).sum =
      ((l.take m).map fun e ↦ z (fd.labelling.targetEdge.symm e.1.1) /
          (ψ.sourceEdgeIndex e : ℚ)).sum := by
    intro l m
    rw [← List.map_take, List.map_map]
    congr 1
    exact List.map_congr_left fun e _ ↦ hterm e
  rcases markedPathEnd_cases fd.pathEnds path hrow hEnd with ⟨hF0, hY0⟩ | ⟨hFL, hYL⟩
  · -- the same orientation
    have hOrd' : RowWalk.orderedRow fdD.pathEnds P' = W.map β.psiSE := by
      rw [hOrd, hF0, hY0, TypedRows.orderedRow_getElem_zero, TypedRows.rowVertex_zero]
      rfl
    have hi' : i + 1 < (RowWalk.orderedRow fdD.pathEnds P').length := by
      rw [hOrd', List.length_map]; exact hi
    have hPub := RowHairpinPosition.weighted_prefix_mem fdD yD zD hSysD hOddD P' hInternal hi'
    have hVert : RowPosition.rowVertex fdD P' (i + 1) =
        β.psiSV (TypedRows.rowVertex fd.pathEnds path (i + 1)) := by
      unfold RowPosition.rowVertex
      rw [hOrd', show RowWalk.startVertex fdD.pathEnds P' = X₀ from rfl, hX₀, hY0,
        TypedRows.rowVertex_zero, walkVertex_psiSE β _ _ _ (by omega)]
      rfl
    have hPos : RowPosition.prefixPosition fdD zD P' (i + 1) =
        TypedRows.prefixPosition fd z path (i + 1) := by
      unfold RowPosition.prefixPosition TypedRows.prefixPosition
      rw [hOrd']
      exact hpos W (i + 1)
    rw [hVert, retractedFibre_psiSV β hψ hT hT0 hMark, hPos] at hPub
    exact hPub
  · -- the reverse orientation: the public walk runs from the finish
    have hOrd' : RowWalk.orderedRow fdD.pathEnds P' = W.reverse.map β.psiSE := by
      rw [hOrd, hFL, hYL, markedTraverse_finish]
    have hLen : (RowWalk.orderedRow fdD.pathEnds P').length = W.length := by
      rw [hOrd', List.length_map, List.length_reverse]
    have hi' : W.length - 2 - i + 1 < (RowWalk.orderedRow fdD.pathEnds P').length := by
      rw [hLen]; omega
    have hPub := RowHairpinPosition.weighted_prefix_mem fdD yD zD hSysD hOddD P' hInternal hi'
    have hidx : W.length - (W.length - 2 - i + 1) = i + 1 := by omega
    have hVert : RowPosition.rowVertex fdD P' (W.length - 2 - i + 1) =
        β.psiSV (TypedRows.rowVertex fd.pathEnds path (i + 1)) := by
      unfold RowPosition.rowVertex
      rw [hOrd', show RowWalk.startVertex fdD.pathEnds P' = X₀ from rfl, hX₀, hYL,
        walkVertex_psiSE β _ _ _ (by rw [List.length_reverse]; omega),
        walkVertex_reverse fd.pathEnds path _ (by omega), hidx]
    -- the public position is the total length minus the typed position
    set total := TypedRows.prefixPosition fd z path W.length with htotal
    have hPos : RowPosition.prefixPosition fdD zD P' (W.length - 2 - i + 1) =
        total - TypedRows.prefixPosition fd z path (i + 1) := by
      unfold RowPosition.prefixPosition
      rw [hOrd', hpos W.reverse, List.take_reverse, List.map_reverse, List.sum_reverse, hidx,
        htotal]
      unfold TypedRows.prefixPosition
      rw [List.take_length]
      conv_rhs => rw [← List.take_append_drop (i + 1) W, List.map_append, List.sum_append]
      ring
    have hTotal : total ∈ oddDenominatorSubring := by
      rw [htotal, hW, TypedRows.prefixPosition_full, hSys]
      exact intCast_mem _ _
    rw [hVert, retractedFibre_psiSV β hψ hT hT0 hMark, hPos] at hPub
    have hprod := oddDenominatorSubring.sub_mem
      (oddDenominatorSubring.mul_mem (intCast_mem oddDenominatorSubring
        (retractedFibre root (retractVertex (TypedRows.rowVertex fd.pathEnds path (i + 1)))))
        hTotal) hPub
    convert hprod using 1
    ring

end Generic

/-! ## 2.  The instance at the regrown frame of a typed frame -/

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}

section Frame

variable (T : Tailed core mark c) (hc : IsMarkedCubic core mark) (hd : IsTailDegree n p c degree)
  (J : LowerIndex c) (κ : TypedFrame core mark (lowerType c J) (degree - shed J))
  (s : SlopeData c J)

/-- The column of `f` over an old target edge is the core slot of `κ`'s column. -/
theorem targetEdge_symm_oldE (ε : κ.target.edges) :
    (regrowTailed T hc hd J κ s).fullDim.labelling.targetEdge.symm
        (oldE c (CatRegrow.branching hd J κ s).x ε) =
      T.coreSlot (κ.fullDim.labelling.targetEdge.symm ε) := by
  apply (Equiv.symm_apply_eq _).mpr
  rw [targetEdge_coreSlot, Equiv.apply_symm_apply]

/-- The image of a mark has an incident target edge. -/
theorem incidentEdges_card_pos_mark (j : Fin k) :
    0 < (incidentEdges (κ.markSource j).1.1).card := by
  classical
  have h2 := κ.fullDim.markValency _ (MarkedCount.mem_markSet κ.markSource j)
  rw [← card_nonDanglingIncident] at h2
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by rw [h2]; exact two_pos)
  rw [mem_nonDanglingIncident] at he
  exact Finset.card_pos.mpr ⟨_, (mem_incidentEdges_of_incident κ.data he.2).1⟩

/-- **An internal vertex of `κ.target`, or the image of a mark, is internal in the regrown
target.** -/
theorem not_isLeafVertex_oldV {root : κ.target.V}
    (hRoot : ¬ IsLeafVertex κ.target root ∨ ∃ j, (κ.markSource j).1.1 = root) :
    ¬ IsLeafVertex (catTarget c κ.target (CatRegrow.branching hd J κ s).x)
      (oldV c (CatRegrow.branching hd J κ s).x root) := by
  classical
  intro hLeaf
  unfold IsLeafVertex at hLeaf
  rw [card_incidentEdges_oldV] at hLeaf
  have hmarks : ∀ j, (CatRegrow.branching hd J κ s).x j = root →
      0 < (incidentEdges root).card := fun j hj ↦ by
    have := incidentEdges_card_pos_mark J κ j
    rwa [show (κ.markSource j).1.1 = root from hj] at this
  rcases hRoot with hR | ⟨j, hj⟩
  · unfold IsLeafVertex at hR
    have hpos : 0 < (Finset.univ.filter fun j ↦ (CatRegrow.branching hd J κ s).x j = root).card := by
      omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hj
    have := hmarks j hj.2
    omega
  · have h1 := hmarks j hj
    have h2 : 0 < (Finset.univ.filter fun j ↦ (CatRegrow.branching hd J κ s).x j = root).card :=
      Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    omega

end Frame

/-- **Every interior chip term along a marked row has odd denominator** at an internal root or
at the image of a mark, for a typed frame of lower index `0` over a marked-cubic core with a
tailed core at the headline degree, at an integral request, when the typed multiplicity is odd
(`RowHairpinPosition.weighted_prefix_mem` on the regrowth). -/
theorem weighted_prefix_mem_of_regrow (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree)
    (κ : TypedFrame core mark (lowerType c fun _ ↦ 0) (degree - shed (c := c) fun _ ↦ 0))
    (s : SlopeData c fun _ ↦ 0) (y : Fin p → ℚ) (yZ : Fin p → ℤ) (hy : ∀ i, y i = yZ i)
    (hOdd : ∃ m : ℕ, Odd m ∧ κ.typedAbsMult = m)
    (path : MarkedStablePath κ.data (markSet κ.markSource)) {root : κ.target.V}
    (hRoot : ¬ IsLeafVertex κ.target root ∨ ∃ j, (κ.markSource j).1.1 = root)
    {i : ℕ} (hi : i + 1 < (TypedRows.orderedRow κ.fullDim.pathEnds path).length) :
    (retractedFibre root (retractVertex (TypedRows.rowVertex κ.fullDim.pathEnds path (i + 1))) : ℚ) *
      TypedRows.prefixPosition κ.fullDim (κ.coordsAt y) path (i + 1) ∈ oddDenominatorSubring := by
  have : IsEmpty (Fin (shed (c := c) fun _ ↦ 0)) := by
    rw [show shed (c := c) (fun _ ↦ 0) = 0 from Finset.sum_eq_zero fun _ _ ↦ rfl]
    infer_instance
  refine weighted_prefix_mem_generic (CatRegrow.branching hd (fun _ ↦ 0) κ s)
    (CatRegrow.hψ _ κ) (CatRegrow.hT _ κ) (CatRegrow.hT0 _ κ) (CatRegrow.hMark hd _ κ s)
    κ.fullDim (regrowTailed T hc hd (fun _ ↦ 0) κ s).fullDim (κ.coordsAt y)
    (fun row ↦ yZ (κ.slot row)) ?_ (regrowCoords T hd _ κ s y) (regrowRequestInt T _ κ yZ)
    (mulVec_regrowCoords_int T hc hd _ κ s y yZ hy) (odd_fdAbsMultNat T hc hd _ κ s hOdd) ?_
    path (not_isLeafVertex_oldV hd _ κ s hRoot) hi
  · funext row
    show κ.matrix.mulVec (κ.coordsAt y) row = _
    rw [κ.mulVec_coordsAt y]
    exact hy _
  · intro ε
    exact (congrArg (regrowCoords T hd _ κ s y) (targetEdge_symm_oldE T hc hd _ κ s ε)).trans
      (regrowCoords_coreSlot T hd _ κ s y _)

/-! ## 3.  The model instance -/

section Model

open DiagonalSecant
open GenusSixExistence.Tripod.Gadget (subdivide)

variable {g : ℕ} {G : CFGraph.{0}} {u : (UnitSubdivisionPresentation.spec G).graph.V}

/-- **The hairpin receipt at the mark's image, for the typed member of the diagonal secant
theorem**: the typed form of `RowHairpinPosition.weighted_prefix_mem` that the generic chain of
`TypedMoments` needs at the root `x_u`. -/
theorem weighted_prefix_mem_of_model (M : OnceMarkedModel g G u) (hg5 : 5 ≤ g)
    (κ : TypedFrame M.markedCore (onceMark M.N) ![g - 4] (g - 1))
    (hOdd : ∃ m : ℕ, Odd m ∧ κ.typedAbsMult = m)
    (path : MarkedStablePath κ.data (markSet κ.markSource)) (j : Fin 1)
    {i : ℕ} (hi : i + 1 < (TypedRows.orderedRow κ.fullDim.pathEnds path).length) :
    (retractedFibre (κ.markSource j).1.1
        (retractVertex (TypedRows.rowVertex κ.fullDim.pathEnds path (i + 1))) : ℚ) *
      TypedRows.prefixPosition κ.fullDim (κ.coordsAt M.request) path (i + 1) ∈
        oddDenominatorSubring := by
  have ha : 1 ≤ g - 4 := by omega
  have hd : IsTailDegree (M.N + 1) (M.Q + 1) (tailType (g - 4)) (g - 1) :=
    tailed_isTailDegree M.genus_eq ha (by omega)
  have hShed : (g - 1) - shed (c := tailType (g - 4)) (fun _ ↦ 0) = g - 1 := by
    rw [show shed (c := tailType (g - 4)) (fun _ ↦ 0) = 0 from Finset.sum_eq_zero fun _ _ ↦ rfl,
      Nat.sub_zero]
  have key : ∀ (types' : Fin 1 → ℕ) (d' : ℕ) (ht : lowerType (tailType (g - 4)) (fun _ ↦ 0) = types')
      (hd' : (g - 1) - shed (c := tailType (g - 4)) (fun _ ↦ 0) = d')
      (κ' : TypedFrame M.markedCore (onceMark M.N) types' d')
      (path' : MarkedStablePath κ'.data (markSet κ'.markSource)),
      (∃ m : ℕ, Odd m ∧ κ'.typedAbsMult = m) →
      ∀ {i : ℕ}, i + 1 < (TypedRows.orderedRow κ'.fullDim.pathEnds path').length →
      (retractedFibre (κ'.markSource j).1.1
          (retractVertex (TypedRows.rowVertex κ'.fullDim.pathEnds path' (i + 1))) : ℚ) *
        TypedRows.prefixPosition κ'.fullDim (κ'.coordsAt M.request) path' (i + 1) ∈
          oddDenominatorSubring := by
    rintro types' d' rfl rfl κ' path' hOdd' i hi'
    exact weighted_prefix_mem_of_regrow (tailed M.core M.slot (g - 4))
      (tailed_markedCubic M.cubic M.slot) hd κ' (fun _ ↦ CM.zeroSlope _ rfl) M.request
      (fun e ↦ (degenerateLength M.expansion M.small e : ℤ))
      (fun e ↦ by simp [OnceMarkedModel.request]) hOdd' path' (Or.inr ⟨j, rfl⟩) hi'
  exact key _ _ (lowerType_tailType_zero ha) hShed κ path hOdd hi

end Model

end DiagonalSecant.CM
