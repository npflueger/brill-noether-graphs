import DraismaVargasCount.SpineRowLength

/-!
# The edge budget at the caterpillar of loops: the `2g` lollipop edges, and the residue

Companion of `SpineRowLength`, carrying its member-level statements
to `catCore m` and assembling Part II's edge budget
(`SpinePath.catCore_spine_edge_budget`) out of them.  This is the counting step
of the proof of `lm:combinatorial-structure-caterpillar-of-loops` in Vargas,
Part II (arXiv:2609.09109), together with its consequence that every row lies
over a single column (`SpineOffDiagonal.RowSingleColumn`).

Several statements carry the loop-leaf adjacency hypothesis
`hAdj : ∀ slot hLoop, LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop`,
Part I's pass-once condition at the lollipop; it is proved unconditionally as
`PassOnceLollipopWitness.loopLeafAdjacent`.

## What is proved

* §1 `loopLeafMap_bijective`, `exists_loopSlot_of_isLeafVertex`,
  `exists_loopSlot_of_passesAboveLeaf` --- **every leaf of the target of a
  caterpillar member is the leaf of a loop row**, so every row that passes
  above a leaf *is* a loop row and every other row is leaf-avoiding.  The
  counts match (`LollipopLeafRow.card_catCore_loopSlots` and
  `LollipopDivalent.leafCount_eq_catCore`), so the injection
  `LollipopLeafRow.loopLeafMap_injective` is a bijection.  **No hypothesis.**
* §2 `catCore_not_loop_to_loop` --- **no slot of `catCore m` joins the branch
  vertices of two distinct self-loops**, for `m ≥ 1`.  `m = 0` is genuinely
  excluded, not an artefact: `H^CL_2` is two loops joined by one bridge, and
  the configuration is realised there.
* §3 `loopBridgeEdge_inj`, `loopLeafEdge_ne_loopBridgeEdge` --- the `2g`
  lollipop **edges** are distinct, under `hAdj`.
* §4 `lollipopEdges`, `mem_lollipopEdges_iff`, `lollipopEdges_card` --- **the
  `2g`-element set of lollipop edges**, under `hAdj` and `m ≥ 1`.  This is the set
  `SpinePath.catCore_spine_edge_budget` asks for.
* §5 `FreeRow`, `notMem_lollipopEdges_of_meets`, `spineColumns_card_le` ---
  Part II's `|φ(P)| ≤ g - 3`: a set of columns each met by a row that is
  neither a loop row nor a bridge row has at most `g - 3` elements.
* §6 `FreeColumnsSeparated`, `meets_row_unique_of_free`,
  `exists_rowSingleColumn_of_free`,
  `card_rowEdges_eq_one_of_not_passesAboveLeaf`,
  `exists_perm_member_matrix_diagonal_of_free` --- **the residue, named**, and
  what it buys: `RowSingleColumn` for every row, the spine bound `¬ PassesAboveLeaf → card =
  1`, and `A_φ` monomial.
* §7 `bridgeRow`, `loopRowIndex`, `bridgeRow_ne_loopRowIndex`, `bridgeRow_inj`,
  `lollipopRows`, `lollipopRows_card`, `freeRow_iff_notMem_lollipopRows`,
  `freeRows_card` --- **the `2g` lollipop rows and the `g - 3` free rows, with
  `hAdj`**, only `m ≥ 1`.  The *row* side of Part II's `2g` count is
  unconditional; only the *column* side needs `hAdj`.

## What is NOT proved (every hypothesis, explicitly)

* **`hAdj` is a hypothesis of §3--§6.**  It enters through exactly one theorem,
  `LollipopBridgeFibre.eq_bridge_of_surviving_of_leafAdjacent`.  §1, §2 and §7
  are unconditional.
* **The free-column hypothesis `FreeColumnsSeparated` is not proved here, for no
  column.**  It is Part II's *"the image `φ(P)` is disjoint from all
  `φ(N(L(A_i)))` … `φ` is injective on `P`"*, and the injectivity half needs
  the **concatenated** source spine path: each row's own occurrences have
  distinct target images (`RowGeodesic.rowTargetInjective_of_genusZero`), but
  this file does not join two consecutive rows into one non-backtracking target
  walk.  §6 is stated so that it is the only remaining hypothesis.  (The base
  count obtains the single-column property by another route,
  `SpineSingleColumn` with `TrivalentFibreUnique.leafAvoidingSeparated`.)
* **Counting alone cannot close it.**  §5 and §7 give `g - 3` free rows with
  nonempty supports confined to at most `g - 3` free columns, and expanding
  `det A_φ` along the `2g` lollipop columns leaves a nonsingular
  `(g-3) × (g-3)` minor --- but a nonsingular square matrix need not be
  monomial, so no argument from cardinalities and `fd.det_ne_zero` can finish.
* No spine path is constructed, in the source or in the target.  Nothing below
  mentions a walk, `Neigh`, a slope or a ballot sequence.
* Nothing below mentions `Open`, `HasOddMult`, `GeometricFibre`,
  `openOddCount`, `BallotFamily` or genericity of the request; every statement
  is about an arbitrary `FibreMember (catCore m) request (m + 2)`.
-/

namespace DraismaVargas.Count.SpineRowLengthWitness

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.EdgeDenominator
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.RowWalk
open DraismaVargas.Count.SpineOffDiagonal
open DraismaVargas.Count.SpineRowLength

/-! ## 1.  Every leaf of the target is a loop row's leaf -/

section Leaves

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- **The injection of self-loop slots into leaves is a bijection.**  `2m + 2`
self-loop slots, `2m + 2` leaves (`LollipopDivalent.leafCount_eq_catCore`,
unconditional), and the map between them is injective. -/
theorem loopLeafMap_bijective (member : FibreMember (catCore m) request (m + 2)) :
    Function.Bijective (LollipopLeafRow.loopLeafMap member) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨LollipopLeafRow.loopLeafMap_injective member, ?_⟩
  rw [LollipopLeafRow.card_catCore_loopSlots m]
  have hcard : Fintype.card {vertex : member.target.V // IsLeafVertex member.target vertex}
      = leafCount member.target := by
    simp [leafCount, leafVertices, Fintype.card_subtype]
  rw [hcard, LollipopDivalent.leafCount_eq_catCore m member]

/-- **Every leaf of the target of a caterpillar member is the leaf that some
loop row passes above.** -/
theorem exists_loopSlot_of_isLeafVertex (member : FibreMember (catCore m) request (m + 2))
    {vertex : member.target.V} (hLeaf : IsLeafVertex member.target vertex) :
    ∃ (slot : Fin (6 * m + 3)) (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopLeafRow.loopLeaf member hLoop = vertex := by
  obtain ⟨loopSlot, hEq⟩ := (loopLeafMap_bijective member).2 ⟨vertex, hLeaf⟩
  exact ⟨loopSlot.1, loopSlot.2, congrArg Subtype.val hEq⟩

/-- **A row that passes above a leaf is a loop row.**  Consequently every
non-loop row of a caterpillar member is leaf-avoiding, which is what makes
`SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf` available on
it. -/
theorem exists_loopSlot_of_passesAboveLeaf (member : FibreMember (catCore m) request (m + 2))
    {sourceRow : Fin (6 * m + 3)}
    (hPasses : PassesAboveLeaf member.fullDim.labelling sourceRow) :
    ∃ (slot : Fin (6 * m + 3)) (_ : (catCore m).tail slot = (catCore m).head slot),
      sourceRow = member.fullDim.labelling.row (member.ident.row.symm slot) := by
  obtain ⟨vertex, hLeaf, hRow⟩ :=
    exists_eq_leafRow_of_passesAboveLeaf member.fullDim hPasses
  obtain ⟨slot, hLoop, hVertex⟩ := exists_loopSlot_of_isLeafVertex member hLeaf
  subst hVertex
  exact ⟨slot, hLoop, hRow.trans (LollipopLeafRow.leafRow_loopLeaf member hLoop)⟩

end Leaves

/-! ## 2.  No slot of `catCore m` joins two lollipops -/

section Arithmetic

private theorem tail_eq_tail_iff (m : ℕ) (s t : Fin (6 * m + 3)) :
    (catCore m).tail s = (catCore m).tail t ↔ catTailVal m s = catTailVal m t := by
  rw [Fin.ext_iff]
  show branchIdx (catTailVal m s) = branchIdx (catTailVal m t) ↔ _
  exact branchIdx_inj (catTailVal_mod m s) (catTailVal_mod m t)

private theorem head_eq_tail_iff (m : ℕ) (s t : Fin (6 * m + 3)) :
    (catCore m).head s = (catCore m).tail t ↔ catHeadVal m s = catTailVal m t := by
  rw [Fin.ext_iff]
  show branchIdx (catHeadVal m s) = branchIdx (catTailVal m t) ↔ _
  exact branchIdx_inj (catHeadVal_mod m s) (catTailVal_mod m t)

/-- **`catCore m` has no slot joining the branch vertices of two distinct
self-loops**, as soon as `m ≥ 1`.  In `H^CL_g` the bridges join a lollipop
vertex `A_i` to a spine vertex `B_j`; the excluded `m = 0` case is `H^CL_2`,
which is two loops joined by a single bridge. -/
theorem catCore_not_loop_to_loop (m : ℕ) (hm : 1 ≤ m) {t first second : Fin (6 * m + 3)}
    (hFirst : (catCore m).tail first = (catCore m).head first)
    (hSecond : (catCore m).tail second = (catCore m).head second)
    (hNe : first ≠ second)
    (hT1 : (catCore m).tail t = (catCore m).tail first ∨
      (catCore m).head t = (catCore m).tail first)
    (hT2 : (catCore m).tail t = (catCore m).tail second ∨
      (catCore m).head t = (catCore m).tail second) : False := by
  rw [LollipopLeafRow.catCore_tail_eq_head_iff] at hFirst hSecond
  have hFV : catTailVal m first = first.val :=
    LollipopDivalent.catTailVal_eq_of_isLeafEdge m hFirst
  have hSV : catTailVal m second = second.val :=
    LollipopDivalent.catTailVal_eq_of_isLeafEdge m hSecond
  have hNeVal : first.val ≠ second.val := fun h ↦ hNe (Fin.ext h)
  have hFirstLt := first.isLt
  have hSecondLt := second.isLt
  have hTLt := t.isLt
  have hLeafFirst : first.val % 3 = 0 ∨ first.val = 6 * m + 2 := hFirst
  have hLeafSecond : second.val % 3 = 0 ∨ second.val = 6 * m + 2 := hSecond
  have hTail : catTailVal m t = parentIndex (t.val + 1) := rfl
  have hHead : catHeadVal m t = if IsLeafEdge m t then parentIndex (t.val + 1) else t.val + 1 :=
    rfl
  have hParent : parentIndex (t.val + 1) =
      if (t.val + 1) % 3 = 2 then t.val + 1 - 3 else t.val + 1 - 1 := rfl
  rw [tail_eq_tail_iff, head_eq_tail_iff, hFV] at hT1
  rw [tail_eq_tail_iff, head_eq_tail_iff, hSV] at hT2
  by_cases hLeafT : IsLeafEdge m t
  · have hLeafTVal : t.val % 3 = 0 ∨ t.val = 6 * m + 2 := hLeafT
    rw [hHead, if_pos hLeafT, ← hTail] at hT1 hT2
    rcases hT1 with h1 | h1 <;> rcases hT2 with h2 | h2 <;> exact hNeVal (h1.symm.trans h2)
  · have hNotLeafTVal : ¬ (t.val % 3 = 0 ∨ t.val = 6 * m + 2) := hLeafT
    rw [hHead, if_neg hLeafT] at hT1 hT2
    rw [hTail, hParent] at hT1 hT2
    rcases hT1 with h1 | h1 <;> rcases hT2 with h2 | h2
    · exact hNeVal (h1.symm.trans h2)
    · split_ifs at h1 h2 <;> omega
    · split_ifs at h1 h2 <;> omega
    · exact hNeVal (h1.symm.trans h2)

end Arithmetic

/-! ## 3.  Distinct lollipops have distinct bridge edges -/

section Bridges

/-- The core incidence of the stable row through a surviving occurrence at the
branch vertex of a self-loop slot. -/
private theorem core_incidence_of_incident {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    {slot : Fin (6 * m + 3)} (hLoop : (catCore m).tail slot = (catCore m).head slot)
    {edge : member.data.SourceEdge} (hSurvives : ¬ IsDangling member.data edge)
    (hIncident : Incident member.data edge (LollipopDivalent.loopBranch member hLoop)) :
    (catCore m).tail (member.ident.row (NonDanglingEdge.stablePath
          (⟨edge, hSurvives⟩ : NonDanglingEdge member.data))) = (catCore m).tail slot ∨
      (catCore m).head (member.ident.row (NonDanglingEdge.stablePath
          (⟨edge, hSurvives⟩ : NonDanglingEdge member.data))) = (catCore m).tail slot := by
  set path := NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge member.data)
    with hpath
  have hPos : 0 < StablePathCount.incidenceCount member.data
      (LollipopDivalent.loopBranch member hLoop) path :=
    (StablePathCount.incidenceCount_pos_iff _ _ _).mpr
      ⟨⟨edge, hSurvives⟩, hIncident, rfl⟩
  have hIdent := member.ident.incidence (member.ident.vertex.symm ((catCore m).tail slot))
    (member.ident.row path)
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at hIdent
  have hPos' : 0 < coreIncidence (catCore m) ((catCore m).tail slot)
      (member.ident.row path) := by
    rw [← hIdent]; exact hPos
  clear hPos
  unfold coreIncidence at hPos'
  split_ifs at hPos' with h1 h2 h2
  · exact Or.inl h1
  · exact Or.inl h1
  · exact Or.inr h2
  · omega

/-- **Distinct lollipops have distinct bridge edges**, under `hAdj` and for
`m ≥ 1`.  If the two bridge edges agreed then the fibre clause above the bridge
(`LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch`) would identify
the two bridge *occurrences*, and the resulting stable row would join the two
lollipop branch vertices --- which §2 forbids in `catCore m`. -/
theorem loopBridgeEdge_inj (m : ℕ) (hm : 1 ≤ m) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    {first second : Fin (6 * m + 3)}
    (hFirst : (catCore m).tail first = (catCore m).head first)
    (hSecond : (catCore m).tail second = (catCore m).head second)
    (hEdge : loopBridgeEdge member hFirst = loopBridgeEdge member hSecond) :
    first = second := by
  by_contra hNe
  obtain ⟨hSurvFirst, hIncFirst, hOffFirst, -⟩ := loopBridge_spec member hFirst
  obtain ⟨hSurvSecond, hIncSecond, -, -⟩ := loopBridge_spec member hSecond
  have hBridgeEq : loopBridge member hSecond = loopBridge member hFirst :=
    LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch member hFirst
      (hAdj first hFirst) hSurvFirst hIncFirst hOffFirst hSurvSecond hEdge.symm
  have hIncSecond' : Incident member.data (loopBridge member hFirst)
      (LollipopDivalent.loopBranch member hSecond) := by
    rw [← hBridgeEq]; exact hIncSecond
  exact catCore_not_loop_to_loop m hm hFirst hSecond hNe
    (core_incidence_of_incident member hFirst hSurvFirst hIncFirst)
    (core_incidence_of_incident member hSecond hSurvFirst hIncSecond')

/-- A lollipop's leaf vertex is not another lollipop's divalent vertex. -/
private theorem loopLeaf_ne_loopImage {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    {first second : Fin (6 * m + 3)}
    (hFirst : (catCore m).tail first = (catCore m).head first)
    (hSecond : (catCore m).tail second = (catCore m).head second) :
    LollipopLeafRow.loopLeaf member hFirst ≠ LollipopDivalent.loopImage member hSecond := by
  intro hEq
  have hOne : (GluingDatum.incidentEdges
      (LollipopLeafRow.loopLeaf member hFirst)).card = 1 :=
    LollipopLeafRow.loopLeaf_isLeafVertex member hFirst
  rw [hEq, LollipopDivalent.loopImage_divalent member hSecond] at hOne
  omega

/-- **A lollipop's leaf edge is never another lollipop's bridge edge.**  Under
`hAdj` the leaf edge `t_{v_i}` joins the leaf `v_i` to the divalent vertex
`φ(A_i)`; if it were `φ(e_b^j)` then `φ(A_j)` would be one of those two ends,
and it is divalent, so `φ(A_j) = φ(A_i)` and `i = j` --- which
`loopBridgeEdge_ne_loopLeafEdge` excludes. -/
theorem loopLeafEdge_ne_loopBridgeEdge (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    {first second : Fin (6 * m + 3)}
    (hFirst : (catCore m).tail first = (catCore m).head first)
    (hSecond : (catCore m).tail second = (catCore m).head second) :
    loopLeafEdge member hFirst ≠ loopBridgeEdge member hSecond := by
  intro hEq
  by_cases hSlot : first = second
  · subst hSlot
    exact loopBridgeEdge_ne_loopLeafEdge member hFirst hEq.symm
  have hLeafMem := leafEdge_mem (LollipopLeafRow.loopLeaf_isLeafVertex member hFirst)
  have hImageMem : loopLeafEdge member hFirst ∈
      GluingDatum.incidentEdges (LollipopDivalent.loopImage member hFirst) := hAdj first hFirst
  have hSecondMem : loopLeafEdge member hFirst ∈
      GluingDatum.incidentEdges (LollipopDivalent.loopImage member hSecond) := by
    rw [hEq]; exact loopBridgeEdge_mem_incidentEdges member hSecond
  have hLeaf := fst_eq_or_snd_eq_of_mem_incidentEdges hLeafMem
  have hImage := fst_eq_or_snd_eq_of_mem_incidentEdges hImageMem
  have hOther := fst_eq_or_snd_eq_of_mem_incidentEdges hSecondMem
  have hNeOne := loopLeaf_ne_loopImage member hFirst hFirst
  have hNeTwo := loopLeaf_ne_loopImage member hFirst hSecond
  have hSame : LollipopDivalent.loopImage member hSecond =
      LollipopDivalent.loopImage member hFirst := by
    rcases hLeaf with hLeaf | hLeaf <;> rcases hImage with hImage | hImage <;>
      rcases hOther with hOther | hOther <;>
      first
        | exact absurd (hLeaf.symm.trans hImage) hNeOne
        | exact absurd (hLeaf.symm.trans hOther) hNeTwo
        | exact hOther.symm.trans hImage
  exact hSlot (LollipopDivalent.catCore_tail_inj_of_loop m second first hSecond hFirst
    (LollipopDivalent.loopImage_inj member hSecond hFirst hSame)).symm

end Bridges

/-! ## 4.  The `2g` lollipop edges -/

section EdgeSet

/-- **The `2g` lollipop edges**: for each self-loop slot of `catCore m`, the
leaf edge `t_{v_i}` and the bridge edge `φ(e_b^i)`.  Part II's *"these paths
account for `2g` distinct edges of `T`"*. -/
noncomputable def lollipopEdges (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) : Finset member.target.edges := by
  classical
  exact Finset.image
    (fun x : {slot : Fin (6 * m + 3) //
        (catCore m).tail slot = (catCore m).head slot} × Bool =>
      if x.2 then loopBridgeEdge member x.1.2 else loopLeafEdge member x.1.2)
    Finset.univ

theorem mem_lollipopEdges_iff (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) (edge : member.target.edges) :
    edge ∈ lollipopEdges m member ↔
      ∃ (slot : Fin (6 * m + 3))
        (hLoop : (catCore m).tail slot = (catCore m).head slot),
        edge = loopLeafEdge member hLoop ∨ edge = loopBridgeEdge member hLoop := by
  classical
  unfold lollipopEdges
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.1.1, x.1.2, ?_⟩
    by_cases hb : x.2 = true
    · rw [if_pos hb] at hx; exact Or.inr hx.symm
    · rw [if_neg hb] at hx; exact Or.inl hx.symm
  · rintro ⟨slot, hLoop, hEq | hEq⟩
    · exact ⟨(⟨slot, hLoop⟩, false), by simpa using hEq.symm⟩
    · exact ⟨(⟨slot, hLoop⟩, true), by simpa using hEq.symm⟩

private theorem lollipopEdge_injective (m : ℕ) (hm : 1 ≤ m)
    {request : Fin (6 * m + 3) → ℚ} (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop) :
    Function.Injective
      (fun x : {slot : Fin (6 * m + 3) //
          (catCore m).tail slot = (catCore m).head slot} × Bool =>
        if x.2 then loopBridgeEdge member x.1.2 else loopLeafEdge member x.1.2) := by
  rintro ⟨⟨i, hi⟩, bi⟩ ⟨⟨j, hj⟩, bj⟩ hEq
  simp only at hEq
  cases bi <;> cases bj <;> simp only [Bool.false_eq_true, if_false, if_true] at hEq
  · have hij : i = j := loopLeafEdge_inj member hi hj hEq
    subst hij; rfl
  · exact absurd hEq (loopLeafEdge_ne_loopBridgeEdge m member hAdj hi hj)
  · exact absurd hEq.symm (loopLeafEdge_ne_loopBridgeEdge m member hAdj hj hi)
  · have hij : i = j := loopBridgeEdge_inj m hm member hAdj hi hj hEq
    subst hij; rfl

/-- **The lollipop edge set has `2g` elements**, under `hAdj` and for `m ≥ 1`.
This is the set `SpinePath.catCore_spine_edge_budget` asks for. -/
theorem lollipopEdges_card (m : ℕ) (hm : 1 ≤ m) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop) :
    (lollipopEdges m member).card = 2 * (2 * m + 2) := by
  classical
  unfold lollipopEdges
  rw [Finset.card_image_of_injective _ (lollipopEdge_injective m hm member hAdj),
    Finset.card_univ, Fintype.card_prod, LollipopLeafRow.card_catCore_loopSlots m,
    Fintype.card_bool]
  omega

end EdgeSet

/-! ## 5.  Part II's edge budget for the spine rows -/

section Budget

/-- The rows this section calls *free*: neither a loop row nor the row of a
lollipop bridge. -/
def FreeRow {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (sourceRow : Fin (6 * m + 3)) : Prop :=
  (∀ (slot : Fin (6 * m + 3)) (_ : (catCore m).tail slot = (catCore m).head slot),
      sourceRow ≠ member.fullDim.labelling.row (member.ident.row.symm slot)) ∧
    (∀ (slot : Fin (6 * m + 3)) (hLoop : (catCore m).tail slot = (catCore m).head slot),
      sourceRow ≠ member.fullDim.labelling.row (NonDanglingEdge.stablePath
        (⟨loopBridge member hLoop, (loopBridge_spec member hLoop).1⟩ :
          NonDanglingEdge member.data)))

/-- **A column met by a free row is not a lollipop edge.**  This is Part II's
*"the image `φ(P)` is disjoint from all `φ(N(L(A_i)))`"*, and it comes from the
fibre clauses of `lm:bridge-and-loop`, not from the valency census. -/
theorem notMem_lollipopEdges_of_meets (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    {sourceRow column : Fin (6 * m + 3)} (hFree : FreeRow member sourceRow)
    (hMeets : Meets member.fullDim.labelling sourceRow column) :
    member.fullDim.labelling.targetEdge column ∉ lollipopEdges m member := by
  intro hMem
  obtain ⟨slot, hLoop, hEq | hEq⟩ := (mem_lollipopEdges_iff m member _).mp hMem
  · exact hFree.1 slot hLoop (eq_loopRow_of_meets_loopLeafEdge member hLoop hEq hMeets)
  · exact hFree.2 slot hLoop
      (eq_bridgeRow_of_meets_loopBridgeEdge member hLoop (hAdj slot hLoop) hEq hMeets)

/-- **Part II's `|φ(P)| ≤ g - 3`.**  Any set of columns each of which some free
row meets has at most `g - 3` elements, `g = 2m + 2`. -/
theorem spineColumns_card_le (m : ℕ) (hm : 1 ≤ m) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    (columns : Finset (Fin (6 * m + 3)))
    (hColumns : ∀ column ∈ columns, ∃ sourceRow, FreeRow member sourceRow ∧
      Meets member.fullDim.labelling sourceRow column) :
    columns.card + 3 ≤ 2 * m + 2 := by
  classical
  have hCard : (columns.image
      (fun column ↦ member.fullDim.labelling.targetEdge column)).card = columns.card :=
    Finset.card_image_of_injective _ member.fullDim.labelling.targetEdge.injective
  have hDisj : Disjoint (lollipopEdges m member)
      (columns.image fun column ↦ member.fullDim.labelling.targetEdge column) := by
    rw [Finset.disjoint_right]
    intro edge hEdge hLolli
    obtain ⟨column, hColumn, hEq⟩ := Finset.mem_image.mp hEdge
    obtain ⟨sourceRow, hFree, hMeets⟩ := hColumns column hColumn
    exact notMem_lollipopEdges_of_meets m member hAdj hFree hMeets (hEq ▸ hLolli)
  have hBudget := SpinePath.catCore_spine_edge_budget m member (lollipopEdges m member)
    (columns.image fun column ↦ member.fullDim.labelling.targetEdge column)
    (lollipopEdges_card m hm member hAdj) hDisj
  omega

end Budget

/-! ## 6.  The residue, and what it buys -/

section Residue

/-- **The residue.**  Distinct rows never meet a
common *non-lollipop* column.  Part II gets it by concatenating the spine rows
into the single path `P` from `L(B_2)` to `L(B_{g-1})` and observing that `φ`
is injective on `P` because `T` is a tree and consecutive edges of `P` have
distinct images; here only the injectivity of each row's own walk
(`RowGeodesic.rowTargetInjective_of_genusZero`) is available, with no
concatenation. -/
def FreeColumnsSeparated (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) : Prop :=
  ∀ sourceRow sourceRow' column : Fin (6 * m + 3),
    (∀ (slot : Fin (6 * m + 3)) (hLoop : (catCore m).tail slot = (catCore m).head slot),
      member.fullDim.labelling.targetEdge column ≠ loopLeafEdge member hLoop) →
    (∀ (slot : Fin (6 * m + 3)) (hLoop : (catCore m).tail slot = (catCore m).head slot),
      member.fullDim.labelling.targetEdge column ≠ loopBridgeEdge member hLoop) →
    Meets member.fullDim.labelling sourceRow column →
    Meets member.fullDim.labelling sourceRow' column →
    sourceRow = sourceRow'

/-- **`hOff` on every column**, from `hAdj` and the residue: the lollipop columns
are §4's, the rest are the hypothesis. -/
theorem meets_row_unique_of_free (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    (hFree : FreeColumnsSeparated m member)
    (sourceRow sourceRow' column : Fin (6 * m + 3))
    (hMeets : Meets member.fullDim.labelling sourceRow column)
    (hMeets' : Meets member.fullDim.labelling sourceRow' column) :
    sourceRow = sourceRow' := by
  by_cases hLeafColumn : ∃ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      member.fullDim.labelling.targetEdge column = loopLeafEdge member hLoop
  · obtain ⟨slot, hLoop, hEq⟩ := hLeafColumn
    exact meets_row_unique_loopLeafEdge member hLoop hEq hMeets hMeets'
  by_cases hBridgeColumn : ∃ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      member.fullDim.labelling.targetEdge column = loopBridgeEdge member hLoop
  · obtain ⟨slot, hLoop, hEq⟩ := hBridgeColumn
    exact meets_row_unique_loopBridgeEdge member hLoop (hAdj slot hLoop) hEq hMeets hMeets'
  · exact hFree sourceRow sourceRow' column
      (fun slot hLoop hEq ↦ hLeafColumn ⟨slot, hLoop, hEq⟩)
      (fun slot hLoop hEq ↦ hBridgeColumn ⟨slot, hLoop, hEq⟩) hMeets hMeets'

/-- **`RowSingleColumn` at a caterpillar member**, from `hAdj` and the residue. -/
theorem exists_rowSingleColumn_of_free (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    (hFree : FreeColumnsSeparated m member) :
    ∃ σ : Fin (6 * m + 3) → Fin (6 * m + 3), Function.Bijective σ ∧
      ∀ sourceRow, RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow) :=
  SpineOffDiagonal.member_rowSingleColumn_of_meets_row_unique member
    (meets_row_unique_of_free m member hAdj hFree)

/-- **The spine bound.**  A leaf-avoiding row of a caterpillar member displays
exactly one surviving occurrence --- Part II's *"each path edge `h_i` contains a
single edge of `G`"*.  By §1 the leaf-avoiding rows are exactly the non-loop
rows. -/
theorem card_rowEdges_eq_one_of_not_passesAboveLeaf (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    (hFree : FreeColumnsSeparated m member) {sourceRow : Fin (6 * m + 3)}
    (hAvoid : ¬ PassesAboveLeaf member.fullDim.labelling sourceRow) :
    (rowEdges member.fullDim.labelling sourceRow).card = 1 := by
  obtain ⟨σ, -, hSingle⟩ := exists_rowSingleColumn_of_free m member hAdj hFree
  exact RowSingleColumnProof.card_rowEdges_eq_one_of_rowSingleColumn_of_not_passesAboveLeaf
    member.fullDim hAvoid (hSingle sourceRow)

/-- **`A_φ` is a monomial matrix at an arbitrary caterpillar member**, from `hAdj`
and the residue.  This is the diagonality input of the exhaustion in
`CaterpillarBallotCount`. -/
theorem exists_perm_member_matrix_diagonal_of_free (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hAdj : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      LollipopBridgeFibreWitness.LoopLeafAdjacent member hLoop)
    (hFree : FreeColumnsSeparated m member) :
    ∃ e : Equiv.Perm (Fin (6 * m + 3)),
      (∀ sourceRow column : Fin (6 * m + 3), column ≠ e sourceRow →
        member.matrix sourceRow column = 0) ∧
      (∀ sourceRow : Fin (6 * m + 3), member.matrix sourceRow (e sourceRow) ≠ 0) := by
  obtain ⟨σ, -, hSingle⟩ := exists_rowSingleColumn_of_free m member hAdj hFree
  exact SpineOffDiagonal.exists_perm_member_matrix_diagonal member hSingle

end Residue

/-! ## 7.  The `2g` lollipop rows --- no `hAdj` needed -/

section Rows

/-- The stable row of the bridge at a self-loop slot: Part II's `h_b`. -/
noncomputable def bridgeRow {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) {slot : Fin (6 * m + 3)}
    (hLoop : (catCore m).tail slot = (catCore m).head slot) : Fin (6 * m + 3) :=
  member.fullDim.labelling.row (NonDanglingEdge.stablePath
    (⟨loopBridge member hLoop, (loopBridge_spec member hLoop).1⟩ :
      NonDanglingEdge member.data))

/-- The stable row of a self-loop slot: Part II's `h_l`. -/
noncomputable def loopRowIndex {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) (slot : Fin (6 * m + 3)) :
    Fin (6 * m + 3) :=
  member.fullDim.labelling.row (member.ident.row.symm slot)

/-- **A bridge row is never a loop row.**  For one lollipop this is the
defining property of the bridge; across two it is that a branch vertex cannot
be interior to a stable row, so the loop row of `second` would have an end at
`A_first`. -/
theorem bridgeRow_ne_loopRowIndex (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) {first second : Fin (6 * m + 3)}
    (hFirst : (catCore m).tail first = (catCore m).head first)
    (hSecond : (catCore m).tail second = (catCore m).head second) :
    bridgeRow member hFirst ≠ loopRowIndex member second := by
  intro hEq
  obtain ⟨hSurv, hInc, hOffRow, -⟩ := loopBridge_spec member hFirst
  have hPath : NonDanglingEdge.stablePath
      (⟨loopBridge member hFirst, hSurv⟩ : NonDanglingEdge member.data)
      = member.ident.row.symm second := member.fullDim.labelling.row.injective hEq
  have hCore := core_incidence_of_incident member hFirst hSurv hInc
  rw [hPath, Equiv.apply_symm_apply] at hCore
  have hTails : (catCore m).tail second = (catCore m).tail first := by
    rcases hCore with hCore | hCore
    · exact hCore
    · exact hSecond.trans hCore
  have hSlot : second = first :=
    LollipopDivalent.catCore_tail_inj_of_loop m second first hSecond hFirst hTails
  subst hSlot
  exact hOffRow ⟨hSurv, hPath⟩

/-- **Distinct lollipops have distinct bridge rows**, for `m ≥ 1` and **with no
`hAdj`**: a common bridge row would have an end at each of the two lollipop branch
vertices, which §2 forbids in `catCore m`. -/
theorem bridgeRow_inj (m : ℕ) (hm : 1 ≤ m) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) {first second : Fin (6 * m + 3)}
    (hFirst : (catCore m).tail first = (catCore m).head first)
    (hSecond : (catCore m).tail second = (catCore m).head second)
    (hEq : bridgeRow member hFirst = bridgeRow member hSecond) : first = second := by
  by_contra hNe
  obtain ⟨hSurvFirst, hIncFirst, -, -⟩ := loopBridge_spec member hFirst
  obtain ⟨hSurvSecond, hIncSecond, -, -⟩ := loopBridge_spec member hSecond
  have hPath : NonDanglingEdge.stablePath
      (⟨loopBridge member hFirst, hSurvFirst⟩ : NonDanglingEdge member.data)
      = NonDanglingEdge.stablePath
        (⟨loopBridge member hSecond, hSurvSecond⟩ : NonDanglingEdge member.data) :=
    member.fullDim.labelling.row.injective hEq
  have hOne := core_incidence_of_incident member hFirst hSurvFirst hIncFirst
  have hTwo := core_incidence_of_incident member hSecond hSurvSecond hIncSecond
  rw [← hPath] at hTwo
  exact catCore_not_loop_to_loop m hm hFirst hSecond hNe hOne hTwo

/-- **The `2g` lollipop rows**: the `g` loop rows and the `g` bridge rows. -/
noncomputable def lollipopRows (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) : Finset (Fin (6 * m + 3)) := by
  classical
  exact Finset.image
    (fun x : {slot : Fin (6 * m + 3) //
        (catCore m).tail slot = (catCore m).head slot} × Bool =>
      if x.2 then bridgeRow member x.1.2 else loopRowIndex member x.1.1)
    Finset.univ

theorem mem_lollipopRows_iff (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) (sourceRow : Fin (6 * m + 3)) :
    sourceRow ∈ lollipopRows m member ↔
      ∃ (slot : Fin (6 * m + 3))
        (hLoop : (catCore m).tail slot = (catCore m).head slot),
        sourceRow = loopRowIndex member slot ∨ sourceRow = bridgeRow member hLoop := by
  classical
  unfold lollipopRows
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.1.1, x.1.2, ?_⟩
    by_cases hb : x.2 = true
    · rw [if_pos hb] at hx; exact Or.inr hx.symm
    · rw [if_neg hb] at hx; exact Or.inl hx.symm
  · rintro ⟨slot, hLoop, hEq | hEq⟩
    · exact ⟨(⟨slot, hLoop⟩, false), by simpa using hEq.symm⟩
    · exact ⟨(⟨slot, hLoop⟩, true), by simpa using hEq.symm⟩

/-- **A row is free exactly when it is not a lollipop row.** -/
theorem freeRow_iff_notMem_lollipopRows (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) (sourceRow : Fin (6 * m + 3)) :
    FreeRow member sourceRow ↔ sourceRow ∉ lollipopRows m member := by
  constructor
  · intro hFree hMem
    obtain ⟨slot, hLoop, hEq | hEq⟩ := (mem_lollipopRows_iff m member sourceRow).mp hMem
    · exact hFree.1 slot hLoop hEq
    · exact hFree.2 slot hLoop hEq
  · intro hMem
    exact ⟨fun slot hLoop hEq ↦ hMem
        ((mem_lollipopRows_iff m member sourceRow).mpr ⟨slot, hLoop, Or.inl hEq⟩),
      fun slot hLoop hEq ↦ hMem
        ((mem_lollipopRows_iff m member sourceRow).mpr ⟨slot, hLoop, Or.inr hEq⟩)⟩

/-- **There are exactly `2g` lollipop rows**, for `m ≥ 1` and **with no `hAdj`**. -/
theorem lollipopRows_card (m : ℕ) (hm : 1 ≤ m) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) :
    (lollipopRows m member).card = 2 * (2 * m + 2) := by
  classical
  have hInj : Function.Injective
      (fun x : {slot : Fin (6 * m + 3) //
          (catCore m).tail slot = (catCore m).head slot} × Bool =>
        if x.2 then bridgeRow member x.1.2 else loopRowIndex member x.1.1) := by
    rintro ⟨⟨i, hi⟩, bi⟩ ⟨⟨j, hj⟩, bj⟩ hEq
    simp only at hEq
    cases bi <;> cases bj <;> simp only [Bool.false_eq_true, if_false, if_true] at hEq
    · have hij : i = j := member.ident.row.symm.injective
        (member.fullDim.labelling.row.injective hEq)
      subst hij; rfl
    · exact absurd hEq.symm (bridgeRow_ne_loopRowIndex m member hj hi)
    · exact absurd hEq (bridgeRow_ne_loopRowIndex m member hi hj)
    · have hij : i = j := bridgeRow_inj m hm member hi hj hEq
      subst hij; rfl
  unfold lollipopRows
  rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_prod,
    LollipopLeafRow.card_catCore_loopSlots m, Fintype.card_bool]
  omega

/-- **There are exactly `g - 3` free rows**, for `m ≥ 1` and with no `hAdj` ---
Part II's `g - 3` interior edges of the path `P`.  Together with
`spineColumns_card_le` this is the whole of Part II's count: `g - 3` rows whose
supports are nonempty (`SpineOffDiagonal.rowSupport_nonempty`) and confined to
at most `g - 3` columns. -/
theorem freeRows_card (m : ℕ) (hm : 1 ≤ m) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2)) :
    (lollipopRows m member)ᶜ.card + 3 = 2 * m + 2 := by
  classical
  rw [Finset.card_compl, lollipopRows_card m hm member, Fintype.card_fin]
  omega

end Rows

end DraismaVargas.Count.SpineRowLengthWitness
