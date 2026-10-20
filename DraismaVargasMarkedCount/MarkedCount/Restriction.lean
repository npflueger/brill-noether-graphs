module

public import DraismaVargasMarkedCount.MarkedCount.Lollipop
public import DraismaVargasMarkedCount.MarkedCount.RestrictIso

@[expose] public section

/-!
# Restriction

**Restriction** deletes the branch `B_j = (t_b, u', t_l, v_C)` of the lollipop at every mark from a
frame over the lollipop core, keeping the marks as source vertices. On gluing data it is the
restriction to the kept target vertices, all branches at once (`Restrict.restrictDatum`, module
`RestrictDatum`): the target is the induced subgraph on the complement of `{φ(w_j)} ∪ {φ(C_j)}`,
with the same partitions. Two `contractDatum` steps per lollipop would give the same datum
(contracting a leaf edge deletes its leaf, and the joins are the old partitions); one step for all
`k` lollipops avoids an induction over intermediate targets. The helper modules are `RestrictDatum`
(generic), `LoopAt`, `RestrictLollipop`, `RestrictBridge`, `RestrictBranch` (the lollipop
package at a member), `RestrictFrame` (the fields of the marked frame) and `RestrictIso`
(functoriality).

**The bridge-and-loop lemma** (Draisma--Vargas Part I, arXiv:1909.12924, `lemma-loop-bridge`;
Vargas, Part II, arXiv:2609.09109, `lm:bridge-and-loop`) is what makes the branches visible: at a
trivalent vertex `w` of the stable graph incident to a bridge `h_b` and a loop `h_l`, the bridge
is a single source edge `e_b` of index two from `w` to the mark `u`, the loop is two edges
`e_1, e_2` of index one from `w` to a vertex `C` over a leaf `v_C`, `u' = φ(w)` is divalent, and
`e_b, w, e_1, e_2, C` are the only non-dangling elements over the branch `(t_b, u', t_l, v_C)`
(the *fibre clause*).

The map is request-free. Its properties, all request-free too:

* `restrictFrame_respects`: it descends to classes (an isomorphism of lollipop frames carries the
  branches to the branches and restricts, `Restrict.restrictIso`);
* `coordsAt_restrictFrame`: the block structure `A_φ = A_{φ'} ⊕ diag(1/2, 2)` per lollipop, read
  on coordinates: `z = (A_{φ'}⁻¹ y, 2β, λ/2)`, so the tails do not enter the other coordinates;
* `markRamification_restrictFrame`: `r_{φ'}(u) = r_φ(u) + 1`;
* `abs_det_restrictFrame`, `denominatorProduct_restrictFrame`, `leafCount_restrictFrame`: the
  three numbers of the multiplicity;

and from them, **proved here**: `markRamification_restrictFrame_eq_one_or_two` (with the
dichotomy at a mark: a fold, `r_φ(u) = 1`, or a transition, `r_φ(u) = 0`) and the multiplicity
identity **`markedAbsMult_restrictFrame`**, `|Mult_H| = r(u) · |naive|` (the multiplicity part of
the lollipop lemma).

Everything here holds for any number `k` of marks. One clause of the bridge-and-loop lemma that the
public lollipop package lacks, `h_b = ⟨w, e_b, u⟩` (the bridge is a single source edge), is proved
in `LoopAt` and `RestrictBridge` by Part I's column-dependence argument.
-/

namespace DraismaVargas.Count.MarkedCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}

/-- **Restriction**: delete the branch of every lollipop.

*Construction.* For a frame `f` over `attachLollipops core mark`: by the lollipop package (the
bridge-and-loop lemma: `LollipopLeafRow.exists_leafRow_of_core_loop`,
`LollipopDivalent.blockCard_and_bridge_index`,
`LollipopBridgeFibreWitness.eq_bridge_of_surviving_loopBranch`,
`PassOnceLollipopWitness.loopLeafAdjacent`, applied to the loop slot `loopSlot p j`, a core loop by
`attachLollipops_loop_isLoop`), the loop row of lollipop `j` is the leaf row of a leaf `v_C` whose
neighbour `u'` is divalent, the bridge `e_b` is the only surviving occurrence over `t_b = u' x`, and
everything else over `t_b, u', t_l, v_C` is dangling; the far end of `e_b` is the mark
(`Lollipops.farEnd_eq_markV`). Delete the vertices `u', v_C` of every branch at once
(`Lollipops.rData`, the restriction `Restrict.restrictDatum` to `Lollipops.Keep`). The result is
valid with the same index map away from the branches; its surviving part is that of `f` minus
`e_b, w, e_1, e_2, C` (this gives (D1) and (D2) of `MarkedFrame`); `markSource j` is the image of
`lollipopMarkSource f j`; the marked rows are the stable paths of `f` other than the bridge and loop
rows, cut at the marks, i.e. the core slots: `ident.row` is `f.ident.row` restricted to `coreSlot`;
`ident.vertex` sends the surviving branch vertices and the marks to `oldVertex`. `saturated`:
`|E(T)|` drops by `2k` and `g(G)` by `k`. `det_ne_zero` from the block decomposition. `ramified`
from `markRamification_restrictFrame` and `markRamification_lollipopMark_nonneg`. -/
noncomputable def restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) : MarkedFrame core mark degree :=
  let M := f.member 0
  { target := Lollipops.rTarget M
    data := Lollipops.rData M
    markSource := Lollipops.markSource M
    fullDim :=
      { valid := Lollipops.rData_valid M
        targetConnected := Lollipops.rTarget_connected M
        targetGenus := Lollipops.rTarget_genus M
        saturated := Lollipops.rData_saturated M
        labelling := Lollipops.labelling M hc
        det_ne_zero := Lollipops.det_labelling_ne_zero M hc
        trivalent := fun X ↦ (Lollipops.nonDanglingValency_rData_le M hc X).trans
          (M.fullDim.trivalent _)
        markValency := fun X hX ↦ by
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hX
          exact Lollipops.nonDanglingValency_markSource M hc j
        pathEnds := Lollipops.rData_pathEnds M hc }
    ident :=
      { vertex := Lollipops.vertexEquiv M hc
        row := Lollipops.rowEquiv M hc
        incidence := Lollipops.markedIncidenceCount_eq M hc
        vertex_mark := fun j ↦ Lollipops.vertexEquiv_markSource M hc j _ }
    ramified := fun j ↦ by
      have h := Lollipops.localRamification_markSource M hc j
      have h0 : 0 ≤ M.data.localRamification (Lollipops.markV M j).1.1
          ⟨(Lollipops.markV M j).1.2, (Lollipops.markV M j).2⟩ :=
        markRamification_lollipopMark_nonneg f j
      unfold markRamification
      rw [h]
      omega }

/-- **Restriction descends to classes.**

*Why true.* An isomorphism of lollipop frames over the identity of the lollipop core preserves
the bridge and loop rows (it is over the identity on rows), hence the branches, and induces an
isomorphism of the contracted data (`GeometricContraction.contractDatumIso`) carrying marks to
marks (`overCore_vertex` at `oldVertex (mark j)`), over the identity of the marked core. -/
theorem restrictFrame_respects (hc : IsMarkedCubic core mark)
    {f f' : Frame (attachLollipops core mark) degree} (iso : FrameIso f f') :
    Nonempty (MarkedFrameIso (restrictFrame hc f) (restrictFrame hc f')) :=
  ⟨{ datum := Lollipops.restrictFrameIso iso
     mark := fun j ↦ Lollipops.restrictFrameIso_markSource iso j
     overCore_vertex := fun X hImage ↦
       Lollipops.vertexEquiv_restrictFrameIso iso hc X ⟨_, hImage⟩ rfl
     overCore_row := fun E ↦ Lollipops.rowEquiv_restrictFrameIso iso hc E _ rfl }⟩

/-- **The block structure, on coordinates.**

Every column of a lollipop frame is a column of its restriction, a bridge column or a loop
column; at every request `y` with tails `(β, λ)` the coordinates are `(A_{φ'}⁻¹ y, 2β, λ/2)`.
No positivity is assumed: this is linear algebra on the matrix.

*Why true.* Row `h_b` is the single occurrence `e_b` of index `2` over `t_b`, entry `1/2`; row `h_l`
is `e_1, e_2` of index `1` over `t_l`, entry `2`; columns `t_b, t_l` vanish off these rows by the
fibre clause of the bridge-and-loop lemma; the remaining block is the marked matrix of the
restriction, by construction of `restrictFrame`. Then `A z = y_H` splits. -/
theorem coordsAt_restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) :
    ∃ (col : Fin p → Fin (p + (k + k))) (bridgeCol loopCol : Fin k → Fin (p + (k + k))),
      (∀ c, (∃ i, col i = c) ∨ (∃ j, bridgeCol j = c) ∨ (∃ j, loopCol j = c)) ∧
      ∀ (y : Fin p → ℚ) (bridge loop : Fin k → ℚ),
        (∀ i, f.coordsAt (lollipopRequest y bridge loop) (col i) =
          (restrictFrame hc f).coordsAt y i) ∧
        (∀ j, f.coordsAt (lollipopRequest y bridge loop) (bridgeCol j) = 2 * bridge j) ∧
        (∀ j, f.coordsAt (lollipopRequest y bridge loop) (loopCol j) = loop j / 2) := by
  set M := f.member 0
  refine ⟨Lollipops.colIncl M, fun j ↦ f.fullDim.labelling.targetEdge.symm (Lollipops.tb M j),
    fun j ↦ f.fullDim.labelling.targetEdge.symm (Lollipops.tl M j), ?_, ?_⟩
  · intro c
    obtain ⟨s, rfl⟩ := (Lollipops.colBlocks M).surjective c
    rcases s with i | j | j
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨j, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, rfl⟩)
  · intro y bridge loop
    obtain ⟨h1, h2, h3⟩ := Lollipops.coords_blocks M hc (lollipopRequest y bridge loop)
      (f.coordsAt (lollipopRequest y bridge loop)) (f.mulVec_coordsAt _)
    refine ⟨fun i ↦ ?_, fun j ↦ ?_, fun j ↦ ?_⟩
    · have hR : (restrictFrame hc f).coordsAt y =
          fun i ↦ f.coordsAt (lollipopRequest y bridge loop) (Lollipops.colIncl M i) := by
        have hSlot : (fun row ↦ y ((restrictFrame hc f).slot row)) = y := by
          funext row
          change y ((Lollipops.rowEquiv M hc) ((Lollipops.rowEquiv M hc).symm row)) = y row
          rw [Equiv.apply_symm_apply]
        rw [MarkedFrame.coordsAt, hSlot]
        have h1' : (restrictFrame hc f).matrix.mulVec
            (fun i ↦ f.coordsAt (lollipopRequest y bridge loop) (Lollipops.colIncl M i)) = y := by
          rw [show (restrictFrame hc f).matrix =
            GluingDatum.LengthMatrixPresentation.matrix (Lollipops.labelling M hc).presentation
            from rfl, h1]
          funext i
          exact lollipopRequest_core y bridge loop i
        refine (congrArg (fun w ↦ (restrictFrame hc f).matrix⁻¹.mulVec w) h1'.symm).trans ?_
        rw [Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (restrictFrame hc f).det_ne_zero),
          Matrix.one_mulVec]
      rw [hR]
    · exact (h2 j).trans (by rw [lollipopRequest_bridge])
    · exact (h3 j).trans (by rw [lollipopRequest_loop])

/-- **`r_{φ'}(u) = r_φ(u) + 1`**.

*Why true.* At `u` the deleted edges are `e_b` and the `m(u) - 2` dangling edges over `t_b`
(all other edges at `u` over `t_b` dangle), `m(u) - 1` in all, and `val φ(u)` drops by one:
`r' = (val u - (m - 1) - 2) - m (val x - 3) = r + 1`. In sheet coordinates: one incident target
edge fewer at `φ(u)`, and over `t_b` the block of `u` held `m(u) - 1` edge blocks
(`blockCountWithin`). -/
theorem markRamification_restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) (j : Fin k) :
    markRamification (restrictFrame hc f).data ((restrictFrame hc f).markSource j) =
      markRamification f.data (lollipopMarkSource f j) + 1 :=
  Lollipops.localRamification_markSource (f.member 0) hc j

/-- **`|det A_φ| = |det A_{φ'}|`**.

*Why true.* `A_φ` is block diagonal `A_{φ'} ⊕ diag(1/2, 2) ⊕ ⋯` after reindexing rows and
columns (`Matrix.det_fromBlocks_zero₂₁`, `Matrix.det_diagonal`; reindexing changes only the
sign), and `(1/2) · 2 = 1`. -/
theorem abs_det_restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) :
    |(restrictFrame hc f).matrix.det| = |f.matrix.det| :=
  Lollipops.abs_det_labelling (f.member 0) hc

/-- **`D_φ = 2^k D_{φ'}`**.

*Why true.* Row `h_b` has the single entry `1/2` (denominator `2`), row `h_l` the single entry `2`
(denominator `1`, `EdgeDenominator.rowDenominator_eq_one_of_leafRow`), and the other rows are the
rows of the restriction. -/
theorem denominatorProduct_restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) :
    Count.denominatorProduct f.fullDim.labelling.presentation =
      2 ^ k * Count.denominatorProduct (restrictFrame hc f).fullDim.labelling.presentation :=
  Lollipops.denominatorProduct_labelling (f.member 0) hc

/-- **The leaf count**: `l(T) = l(T') + k - #{folds}`, where a
mark is a fold exactly when its image is a leaf of `T'`, i.e. when `r_{φ'} = 2`.

*Why true.* The leaves of `T` are those of `T'`, plus `v_C` per lollipop, minus `φ(u)` when it is a
leaf of `T'` (in `T` it is divalent). `φ(u)` is a leaf of `T'` iff `val_T φ(u) = 2` iff (fold or
transition) `φ` folds at `u` iff `r_φ(u) = 1` iff `r_{φ'}(u) = 2`. The branches are disjoint
(`RestrictBranch`), so the counts add. -/
theorem leafCount_restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) :
    Count.leafCount f.target +
        (Finset.univ.filter fun j ↦
          markRamification (restrictFrame hc f).data ((restrictFrame hc f).markSource j) = 2).card =
      Count.leafCount (restrictFrame hc f).target + k :=
  Lollipops.leafCount_restrict (f.member 0) hc

/-! ## Proved from the above -/

/-- **A restricted mark has `r ∈ {1, 2}`**: `r' = r + 1`
with `0 ≤ r ≤ 1`. -/
theorem markRamification_restrictFrame_eq_one_or_two (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) (j : Fin k) :
    markRamification (restrictFrame hc f).data ((restrictFrame hc f).markSource j) = 1 ∨
      markRamification (restrictFrame hc f).data ((restrictFrame hc f).markSource j) = 2 := by
  have h := markRamification_restrictFrame hc f j
  have h0 := markRamification_lollipopMark_nonneg f j
  have h1 := markRamification_lollipopMark_le_one f j
  omega

/-- The ramification factor of a restriction is `2^{#folds}`. -/
theorem ramificationFactor_restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) :
    (restrictFrame hc f).ramificationFactor =
      2 ^ (Finset.univ.filter fun j ↦
        markRamification (restrictFrame hc f).data ((restrictFrame hc f).markSource j) = 2).card := by
  have hpoint : ∀ j, markRamification (restrictFrame hc f).data
      ((restrictFrame hc f).markSource j) =
      if markRamification (restrictFrame hc f).data ((restrictFrame hc f).markSource j) = 2
        then 2 else 1 := by
    intro j
    rcases markRamification_restrictFrame_eq_one_or_two hc f j with h | h <;> rw [h] <;> rfl
  unfold MarkedFrame.ramificationFactor
  rw [Finset.prod_congr rfl fun j _ ↦ hpoint j, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one]

/-- **The multiplicity identity** (the lollipop lemma): the marked multiplicity of the restriction
is Part II's multiplicity of the lollipop frame, `|Mult_H(φ)| = |Mult(φ'; marks)|`. Per lollipop:
`D_φ = 2 D_{φ'}`, `l(T) = l(T') + 1 - [fold]`, `|det|` equal, and `r_{φ'}(u) = 2^{[fold]}`. -/
theorem markedAbsMult_restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) :
    (restrictFrame hc f).markedAbsMult = f.absMult := by
  have hprod := ramificationFactor_restrictFrame hc f
  have hD := denominatorProduct_restrictFrame hc f
  have hL := leafCount_restrictFrame hc f
  have hdet := abs_det_restrictFrame hc f
  set R := restrictFrame hc f
  set F := (Finset.univ.filter fun j ↦ markRamification R.data (R.markSource j) = 2).card
  unfold MarkedFrame.markedAbsMult MarkedFrame.markedSignedMult
  change _ = |Count.signedMult f.fullDim.labelling.presentation|
  unfold Count.signedMult
  rw [hprod, hD]
  change |((2 ^ F : ℤ) : ℚ) * (_ / _ * R.matrix.det)| = |_ / _ * f.matrix.det|
  rw [abs_mul, abs_mul, abs_mul, abs_div, abs_div, hdet.symm]
  push_cast
  rw [abs_of_pos (by positivity : (0 : ℚ) < 2 ^ F),
    abs_of_nonneg (by positivity : (0 : ℚ) ≤ 2 ^ k * _),
    abs_of_nonneg (by positivity : (0 : ℚ) ≤ (Count.denominatorProduct R.fullDim.labelling.presentation : ℚ)),
    abs_of_pos (by positivity : (0 : ℚ) < 2 ^ Count.leafCount R.target),
    abs_of_pos (by positivity : (0 : ℚ) < 2 ^ Count.leafCount f.target)]
  have h2 : (2 : ℚ) ^ F * 2 ^ Count.leafCount f.target = 2 ^ k * 2 ^ Count.leafCount R.target := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  field_simp
  linear_combination (↑(Count.denominatorProduct R.fullDim.labelling.presentation) *
    |R.matrix.det|) * h2

end DraismaVargas.Count.MarkedCount
