import GenusSixExistence.BrillNoetherRank.Tripod.ClawDefs
import Utilities.IntegralGeometry.DeterminantExpansion

/-!
# The Cools--Draisma tripod gluing, and the gluing bijection

The gluing bijection `Classification.exists_gluing`, proved here as `exists_gluing` with the same
binders and conclusion. The construction is the gluing of a tripod of Cools–Draisma, *On metric
graphs with prescribed gonality*, arXiv:1602.05542. Prose proof:
`Research/genus-six-brill-noether-rank.md`, §3.3 (Glued members), §5.1 (The construction), §5.2
(Positivity and change-minimality), §5.3 (The determinant), §5.4 (Denominators and multiplicity)
and §5.5 (The bijection); section and statement numbers in this file refer to that note. The
four class-level statements (d), (e), (f′) and `exists_gluedIdent` of the table below are proved
in `GluingClasses.lean` and the modules it imports.

## The construction (step (a), data)

For a gluing datum `D` of degree `d` over a target tree `T` and a `Placement` of the three marks
(the target edge under each mark, read after the previous subdivisions, and a sheet of the
source edge carrying it), `glueDatum D π` is the Cools–Draisma tripod gluing, of degree `d + 1`:

* subdivide `T` at the three mark images (`subdivTarget`, `refineDatum`: the new vertex and both
  halves carry the partition of the old edge);
* add a new sheet `Fin.last d`, a copy of the subdivided target (`extendDatum`);
* attach an arm at each mark image (`leafTarget`, `leafDatum`): the arm is discrete, and at its
  tip the new sheet is glued to the sheet of the mark.

All three target operations are `TargetExpansion.graph`, so connectedness, genus and edge counts
come from upstream. Shown about it: the target is a connected tree with six more edges
(`Placement.T₆_connected`, `T₆_genus`, `T₆_edge_card`), each tip is a leaf
(`vertex_degree_tipTarget`) and `l(T') = l(T) + 3` (`leafCount_T₆`, §5.4); the source
has genus two more (`genus_glueDatum`), so the dimension count is saturated
(`glueDatum_saturated`); and Riemann--Hurwitz is preserved by each stage
(`glueDatum_riemannHurwitz`).

## The relation, and why it is this one

`IsGluingOf s ψ φ`: up to a `GeometricDatumIso`, the datum of `φ` is `glueDatum ψ.data π` at a
placement of the marks on the core of `ψ` (`Placement.NonDangling`), and the core identification
of `φ` carries the glued labels (`GluedLabels`): old branch vertices, the marks, the centre (the
branch vertex of the new sheet), the old stable paths (as pieces of their own slot of `G̃`,
`mergeSlot`) and the legs. The vertex clauses are equations, so every vertex label is pinned;
this is what makes injectivity and well-definedness true statements.

## The decomposition

| step | declaration | content | prose | where, and from what |
|---|---|---|---|---|
| (a) | `glueDatum`, `Placement` | the Cools–Draisma gluing as a gluing datum | §5.1; Theorem 5.1 | here |
| (a) | `glueDatum_connected` | the glued source is connected | §5.1 | here (`refineDatum_connected`, walks through the new sheet and a tip) |
| (a) | `glueDatum_riemannHurwitz` | Riemann--Hurwitz at every target vertex | §5.2 | here, stage by stage |
| (a) | `glueDatum_saturated` | `\|E(T')\| = 2 g' + 2 (d+1) - 5` | §5.1, the genus count | here |
| (a) | dangling dictionary | which glued source edges dangle; the valency at every vertex | §5.2 | here (`Refine.isDangling_iff`, `isDangling_liftSE_iff`, `nonDanglingValency_oldVertex₃`, `nonDanglingValency_newVertex`) |
| (a) | `card_stablePath_glueDatum` (S1) | `p + 6` stable paths | §5.3 | here (`card_stablePath_glue`: three marks and one median) |
| (a) | `nonDanglingValency_glueDatum_le_three` (S2) | trivalent | §5.2 | here (`nonDanglingValency_glue_le_three`) |
| (a) | `hasPathEnds_glueDatum` (S3) | path ends | Theorem 5.1 | here (`hasPathEnds_glue`) |
| (a) | `hairpin_not_isDangling` | the two arms of each hairpin survive (they lie on a cycle) | §3.3 | here |
| (a) | `isDangling_armSheetEdge`, `stablePath_hairpin`, `matrix_armColumn` | the other arms dangle; the hairpin is one stable path; its column is `2 e_leg` | §5.3 | here |
| (a) | `hairpinPath_injective` (S4) | the three hairpins are three stable paths | §5.3 | here (`hairpinPath_ne_glue`) |
| (a) | `exists_armColumns_glueDatum` | the arm columns, in every labelling | §5.3 | here, from S4 |
| (a) | `exists_stableLabelling_glueDatum` | stable labelling, `det ≠ 0`, trivalent, path ends | §5.3 | here, from S1--S5 |
| (a) | `nonempty_fullDim_glueDatum` | the full-dimensional presentation | Theorem 5.1 | here, from the above |
| (a) | `exists_gluedIdent` | the core identification with the glued labels, open at `y` | §5.2; §(g) below | `GluingClasses.lean` |
| (a) | `exists_open_isGluingOf` | every open `ψ` has an open gluing | Theorem 5.1 | here, from the above |
| (b) | `memberIsGlued_of_isGluingOf` | a gluing is glued | §3.3 | here |
| (c) | `abs_det_eq_of_doubled_columns`, `abs_det_refine` | expanding along the arm columns; one refinement step | §5.3 | `Utilities.DeterminantExpansion` (linear algebra) |
| (c) | `abs_det_clsMatrix_refine` | one refinement of a class matrix: `\|det\|` times `1/a` | §5.3 | here, from `abs_det_refine` |
| (c) | `exists_refinementChain_glueDatum` (S5a) | the non-leg rows are the stable paths of `ψ` cut at the marks, one mark at a time | §5.3 | here (`CutPaths.exists_cutLabels`: the separations are counted, `CutPaths.card_image_gluedPath`) |
| (c) | `abs_det_residual_glueDatum` (S5) | `\|det A'\| · ∏ a_k = \|det A_ψ\|` for the residual block | §5.3 | here, from S5a |
| (c) | `abs_det_glueDatum_labelling`, `abs_det_glueDatum` | `\|det A_N\| · ∏ a_k = 8 \|det A_ψ\|` | §5.3 | here, from S4, S5 |
| (c) | `prod_rowDenominator_residual_glueDatum` (S6) | the non-leg rows have `∏ d_i = D_ψ · ∏ a_k` | §5.4 | here (`d` is the lcm of the row's indices, `rowDenominator_eq_lcm`; one merge per mark, `LcmMerge.prod_lcm_merge`; monotone profile, `CutPaths.gluedPath_eq_of_twoValued`) |
| (c) | `rowDenominator_legRow`, `denominatorProduct_glueDatum` | the leg rows have `d = 1`; `D_N = D_ψ · ∏ a_k` | Part II `lemma-edge-deno` (a) | here, from S4, S6 |
| (c) | `fdAbsMult_glueDatum`, `oddMult_eq_of_isGluingOf` | `\|Mult\|` is preserved | §5.4 | here, from the above and `leafCount_T₆` |
| (d) | `nonempty_iso_of_isGluingOf_iso` | injective on classes | §5.5, injectivity | `GluingClasses.lean` |
| (f′) | `nonempty_iso_of_isGluingOf` | well defined on classes | §5.5 | `GluingClasses.lean` |
| (e) | `exists_isGluingOf_of_memberIsGlued` | onto the open glued classes | §5.5 | `GluingClasses.lean` |
| (f) | `exists_gluingEquiv` | the bijection on `GeometricFibre` subtypes, preserving `multNat` | §5.5 | here, from the above |
| (g) | `exists_gluing` | the statement of `Classification.exists_gluing`, with `B = ∅` | §(g) below | here |

S1--S4 rest on the **dangling dictionary** of the glued datum (sections "The dangling dictionary"
to "The dangling dictionary of the glued datum"), which comes from two facts about an arbitrary
datum: an edge property without a vertex of valency one has no dangling edge
(`not_isDangling_of_witness`), and the non-dangling edges of a connected datum are such a
property (`NonDanglingValency.nonDanglingValency_ne_one`). With them: a refinement has the
dangling edges of the datum it refines (`Refine.isDangling_iff`); the old edges of the glued
datum keep their status (`isDangling_liftSE_iff`); and the surviving new-sheet edges form an edge
set of the tree `T₃` without valency one off the mark images, so it is the tree spanned by them,
with one branch point, the median (`tCount_add_le`, `card_branch_eq_one`). S5 follows from
one combinatorial statement, S5a (the non-leg rows are the stable paths of `ψ` cut at the marks,
`exists_refinementChain_glueDatum`), and the one-step determinant identity
`abs_det_clsMatrix_refine`; S5a is proved in section "The cut paths" by counting ends, and S6
(the denominators) from the same cut paths, see its docstring.

## (g): the family `B` is empty

Condition (iv) of §6.3, the mark condition, asks that the marks avoid the source points
over target vertices of every member over `G̃`, with distinct images. It is **implied by (ii)**,
the generality of `y` for the frames of `Γ̃` in degree five, so `B = ∅` suffices and (iv) costs
nothing. Suppose a mark of `y` sits over a target vertex of an open member `ψ`, or two marks
have one image. Place the marks at their actual positions, putting a mark at a vertex on an
adjacent edge at offset `0` and ordering coincident images along their edge. The glued frame at
this placement is a frame of `Γ̃` in degree five (`nonempty_fullDim_glueDatum` holds at every
placement on the core), and its coordinates at `y` are the geometric lengths, one of which is the
zero-length piece. That is a zero coordinate of a frame of `Γ̃`, which (ii) excludes. The arms are
positive by long legs (§5.2). This argument is inside `exists_gluedIdent`.

## What is not used

`Dichotomy` is not imported: surjectivity starts from `MemberIsGlued`, and its content is the
onto step of §5.5, with the facts at the inner ends of the detour leaf edges from §4.8, not the
parameter count of `Dichotomy.isGlued_of_lost_eq_detours`.
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count (IsLeafVertex leafVertices leafCount)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open Utilities.DeterminantExpansion

namespace SheetOps

variable {d : ℕ}

/-- Add a new sheet `Fin.last d`, as a singleton block. -/
def extendNew (P : SheetPartition d) : SheetPartition (d + 1) where
  repr x := if h : (x : ℕ) < d then (P.repr ⟨x, h⟩).castSucc else Fin.last d
  repr_idem x := by
    by_cases h : (x : ℕ) < d
    · simp [h, P.repr_idem]
    · simp [h]

@[simp] theorem extendNew_repr_castSucc (P : SheetPartition d) (i : Fin d) :
    (extendNew P).repr i.castSucc = (P.repr i).castSucc := by
  simp [extendNew]

@[simp] theorem extendNew_repr_last (P : SheetPartition d) :
    (extendNew P).repr (Fin.last d) = Fin.last d := by
  simp [extendNew]

theorem extendNew_refines {P Q : SheetPartition d} (h : P.Refines Q) :
    (extendNew P).Refines (extendNew Q) := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast j =>
      exfalso
      simp only [SheetPartition.rel_iff, extendNew_repr_last, extendNew_repr_castSucc] at hxy
      exact (Fin.castSucc_lt_last _).ne hxy.symm
  | cast i =>
    induction y using Fin.lastCases with
    | last =>
      exfalso
      simp only [SheetPartition.rel_iff, extendNew_repr_last, extendNew_repr_castSucc] at hxy
      exact (Fin.castSucc_lt_last _).ne hxy
    | cast j =>
      simp only [SheetPartition.rel_iff, extendNew_repr_castSucc, Fin.castSucc_inj] at hxy ⊢
      exact h i j hxy

/-- The partition whose only non-singleton block is `{a, b}`. -/
def pair (a b : Fin d) : SheetPartition d where
  repr x := if x = b then a else x
  repr_idem x := by
    by_cases hx : x = b
    · by_cases hab : a = b <;> simp [hx, hab]
    · simp [hx]

end SheetOps

open TargetExpansion

/-- The edges moved to the fresh vertex by the subdivision of `t`: `t` alone. -/
def subdivRight (T : CFGraph) (t : T.edges) : T.edges → Bool :=
  fun e ↦ @decide (e = t) (Classical.propDecidable _)

/-- **Subdivide the target edge `t`** at a fresh vertex `Sum.inr ()`: the expansion of `t.2`
that moves only `t` (`TargetExpansion.graph`). `t` becomes `(t.1, fresh)`, the new edge is
`(t.2, fresh)`. -/
def subdivTarget (T : CFGraph) (t : T.edges) : CFGraph :=
  TargetExpansion.graph T (t : T.V × T.V).2 (subdivRight T t)

/-- **Attach a leaf** `Sum.inr ()` at the target vertex `u`: the expansion of `u` that moves no
edge. -/
def leafTarget (T : CFGraph) (u : T.V) : CFGraph :=
  TargetExpansion.graph T u fun _ ↦ false

variable {T : CFGraph} {d : ℕ}

/-- An old vertex of a subdivided target. -/
def subdivOld (T : CFGraph) (t : T.edges) (v : T.V) : (subdivTarget T t).V := Sum.inl v

/-- The fresh vertex of a subdivided target. -/
def subdivFresh (T : CFGraph) (t : T.edges) : (subdivTarget T t).V := Sum.inr ()

/-- An old vertex of a target with a leaf attached. -/
def leafOld (T : CFGraph) (u : T.V) (v : T.V) : (leafTarget T u).V := Sum.inl v

/-- The attached leaf. -/
def leafTip (T : CFGraph) (u : T.V) : (leafTarget T u).V := Sum.inr ()

theorem leafTip_ne_leafOld (T : CFGraph) (u v : T.V) : leafTip T u ≠ leafOld T u v :=
  Sum.inr_ne_inl

theorem leafOld_injective (T : CFGraph) (u : T.V) : Function.Injective (leafOld T u) :=
  Sum.inl_injective

/-- The occurrence dictionary of a subdivision: `none` is the new edge `(t.2, fresh)`. -/
def subdivOcc (T : CFGraph) (t : T.edges) : Option T.edges ≃ (subdivTarget T t).edges :=
  TargetExpansion.occurrenceEquiv T _ _

/-- The occurrence dictionary of a leaf attachment: `none` is the leaf edge. -/
def leafOcc (T : CFGraph) (u : T.V) : Option T.edges ≃ (leafTarget T u).edges :=
  TargetExpansion.occurrenceEquiv T _ _

theorem subdivOcc_none (T : CFGraph) (t : T.edges) :
    ((subdivOcc T t none : (subdivTarget T t).edges) :
      (subdivTarget T t).V × (subdivTarget T t).V) =
        (subdivOld T t (t : T.V × T.V).2, subdivFresh T t) :=
  occurrenceEquiv_none _ _ _

theorem subdivOcc_some (T : CFGraph) (t e : T.edges) :
    ((subdivOcc T t (some e) : (subdivTarget T t).edges) :
      (subdivTarget T t).V × (subdivTarget T t).V) =
        oldEnds T (t : T.V × T.V).2 (subdivRight T t) e :=
  occurrenceEquiv_some _ _ _ _

theorem subdivOcc_some_self (T : CFGraph) (t : T.edges) :
    ((subdivOcc T t (some t) : (subdivTarget T t).edges) :
      (subdivTarget T t).V × (subdivTarget T t).V) =
        (subdivOld T t (t : T.V × T.V).1, subdivFresh T t) := by
  rw [subdivOcc_some]
  have hne : (t : T.V × T.V).1 ≠ (t : T.V × T.V).2 := fun h ↦
    T.loopless (t : T.V × T.V).1 (by
      rw [show ((t : T.V × T.V).1, (t : T.V × T.V).1) = (t : T.V × T.V) from Prod.ext rfl h]
      exact Multiset.coe_mem)
  simp only [oldEnds, expandedEndpoint, subdivRight, decide_true, if_true, if_neg hne]
  rfl

theorem subdivOcc_some_of_ne (T : CFGraph) {t e : T.edges} (h : e ≠ t) :
    ((subdivOcc T t (some e) : (subdivTarget T t).edges) :
      (subdivTarget T t).V × (subdivTarget T t).V) =
        (subdivOld T t (e : T.V × T.V).1, subdivOld T t (e : T.V × T.V).2) := by
  rw [subdivOcc_some]
  simp only [oldEnds, expandedEndpoint, subdivRight, h, decide_false, Bool.false_eq_true,
    if_false]
  rfl

theorem leafOcc_none (T : CFGraph) (u : T.V) :
    ((leafOcc T u none : (leafTarget T u).edges) : (leafTarget T u).V × (leafTarget T u).V) =
      (leafOld T u u, leafTip T u) :=
  occurrenceEquiv_none _ _ _

theorem leafOcc_some (T : CFGraph) (u : T.V) (e : T.edges) :
    ((leafOcc T u (some e) : (leafTarget T u).edges) : (leafTarget T u).V × (leafTarget T u).V) =
      (leafOld T u (e : T.V × T.V).1, leafOld T u (e : T.V × T.V).2) :=
  occurrenceEquiv_some _ _ _ _

/-! ### Valencies in an expanded target -/

theorem card_filter_expandedEdges (T : CFGraph) (w : T.V) (r : T.edges → Bool)
    (p : Vertex T × Vertex T → Prop) [DecidablePred p] :
    Multiset.card ((expandedEdges T w r).filter p) =
      (if p (newEnds T w) then 1 else 0) +
        Multiset.card ((enumeratedEdges T).filter fun e ↦ p (oldEnds T w r e)) := by
  rw [expandedEdges, Multiset.filter_cons, Multiset.filter_map]
  split_ifs <;> simp [add_comm]

theorem card_filter_incident_eq_vertex_degree (T : CFGraph) (w : T.V) :
    (Multiset.card ((enumeratedEdges T).filter fun e : T.edges ↦
      (e : T.V × T.V).1 = w ∨ (e : T.V × T.V).2 = w) : ℤ) = vertex_degree T w := by
  rw [PendantDeletion.vertex_degree_eq_card_filter_incident]
  congr 1
  conv_rhs => rw [← Multiset.map_univ_coe T.edges]
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- Attaching a leaf at `u` raises the valency of `u` by one and keeps the others. -/
theorem vertex_degree_leafOld (T : CFGraph) (u w : T.V) :
    vertex_degree (leafTarget T u) (leafOld T u w) =
      vertex_degree T w + if w = u then 1 else 0 := by
  refine (PendantDeletion.vertex_degree_eq_card_filter_incident (leafTarget T u) _).trans ?_
  change (Multiset.card ((expandedEdges T u fun _ ↦ false).filter
    fun e : Vertex T × Vertex T ↦ e.1 = Sum.inl w ∨ e.2 = Sum.inl w) : ℤ) = _
  rw [card_filter_expandedEdges, ← card_filter_incident_eq_vertex_degree, add_comm]
  push_cast
  congr 1
  · congr 2
    apply Multiset.filter_congr
    intro e _
    simp [oldEnds, expandedEndpoint, oldVertex]
  · by_cases h : w = u
    · subst h; simp [newEnds, oldVertex]
    · simp [newEnds, oldVertex, freshVertex, h, Ne.symm h]

theorem vertex_degree_leafOld_of_ne (T : CFGraph) {u w : T.V} (h : w ≠ u) :
    vertex_degree (leafTarget T u) (leafOld T u w) = vertex_degree T w := by
  rw [vertex_degree_leafOld, if_neg h, add_zero]

/-- The attached leaf has valency one. -/
theorem vertex_degree_leafTip (T : CFGraph) (u : T.V) :
    vertex_degree (leafTarget T u) (leafTip T u) = 1 := by
  refine (PendantDeletion.vertex_degree_eq_card_filter_incident (leafTarget T u) _).trans ?_
  change (Multiset.card ((expandedEdges T u fun _ ↦ false).filter
    fun e : Vertex T × Vertex T ↦ e.1 = Sum.inr () ∨ e.2 = Sum.inr ()) : ℤ) = _
  rw [card_filter_expandedEdges]
  simp [newEnds, oldEnds, expandedEndpoint, oldVertex, freshVertex]

/-- The partition of the edge `e₀` refines the refined vertex partition at either remapped end
of `e₀`. -/
theorem refines_expanded (D : GluingDatum T d) (t e₀ : T.edges) (v : T.V)
    (hv : (e₀ : T.V × T.V).1 = v ∨ (e₀ : T.V × T.V).2 = v) :
    (D.edgePartition e₀).Refines
      ((Sum.elim D.vertexPartition fun _ ↦ D.edgePartition t : Vertex T → SheetPartition d)
        (expandedEndpoint T (t : T.V × T.V).2
          (subdivRight T t) e₀ v)) := by
  have hold : (D.edgePartition e₀).Refines (D.vertexPartition v) := by
    rcases hv with h | h
    · rw [← h]; exact D.refines_left e₀
    · rw [← h]; exact D.refines_right e₀
  unfold expandedEndpoint
  by_cases he : e₀ = t
  · subst he
    simp only [subdivRight, decide_true, if_true]
    by_cases hw : v = (e₀ : T.V × T.V).2
    · rw [if_pos hw]
      exact SheetPartition.Refines.refl _
    · rw [if_neg hw]
      exact hold
  · simp only [subdivRight, he, decide_false, Bool.false_eq_true, if_false]
    exact hold

/-- **Refine a datum at a target edge.** The fresh vertex and both halves carry the partition
of the old edge. -/
def refineDatum (D : GluingDatum T d) (t : T.edges) : GluingDatum (subdivTarget T t) d where
  degree_pos := D.degree_pos
  vertexPartition := Sum.elim D.vertexPartition fun _ ↦ D.edgePartition t
  edgePartition e := Option.elim ((subdivOcc T t).symm e) (D.edgePartition t) D.edgePartition
  refines_left e := by
    obtain ⟨x, rfl⟩ := (subdivOcc T t).surjective e
    rw [Equiv.symm_apply_apply]
    cases x with
    | none =>
      rw [subdivOcc_none]
      exact D.refines_right t
    | some e₀ =>
      rw [subdivOcc_some]
      exact refines_expanded D t e₀ _ (Or.inl rfl)
  refines_right e := by
    obtain ⟨x, rfl⟩ := (subdivOcc T t).surjective e
    rw [Equiv.symm_apply_apply]
    cases x with
    | none =>
      rw [subdivOcc_none]
      exact SheetPartition.Refines.refl _
    | some e₀ =>
      rw [subdivOcc_some]
      exact refines_expanded D t e₀ _ (Or.inr rfl)

/-- **Add the new sheet** `Fin.last d`, a disjoint copy of the target. -/
def extendDatum (D : GluingDatum T d) : GluingDatum T (d + 1) where
  degree_pos := Nat.succ_pos d
  vertexPartition v := SheetOps.extendNew (D.vertexPartition v)
  edgePartition e := SheetOps.extendNew (D.edgePartition e)
  refines_left e := SheetOps.extendNew_refines (D.refines_left e)
  refines_right e := SheetOps.extendNew_refines (D.refines_right e)

/-- **Attach an arm at `u`.** The leaf edge has the discrete partition; at its tip the sheets
`a` and `b` are glued. -/
def leafDatum (D : GluingDatum T d) (u : T.V) (a b : Fin d) : GluingDatum (leafTarget T u) d where
  degree_pos := D.degree_pos
  vertexPartition := Sum.elim D.vertexPartition fun _ ↦ SheetOps.pair a b
  edgePartition e := Option.elim ((leafOcc T u).symm e) (SheetPartition.discrete d)
    D.edgePartition
  refines_left e := by
    obtain ⟨x, rfl⟩ := (leafOcc T u).surjective e
    rw [Equiv.symm_apply_apply]
    cases x with
    | none => exact SheetPartition.discrete_refines _
    | some e₀ =>
      rw [leafOcc_some]
      exact D.refines_left e₀
  refines_right e := by
    obtain ⟨x, rfl⟩ := (leafOcc T u).surjective e
    rw [Equiv.symm_apply_apply]
    cases x with
    | none => exact SheetPartition.discrete_refines _
    | some e₀ =>
      rw [leafOcc_some]
      exact D.refines_right e₀

/-! ## Placements and the glued datum -/

/-- **A placement of the three marks** on a datum over `T`: the target edge under mark `0`; the
edge, after subdividing at mark `0`, under mark `1`; the edge, after the second subdivision,
under mark `2`; and for each mark a sheet of the source edge carrying it. -/
structure Placement (T : CFGraph) (d : ℕ) where
  edge₀ : T.edges
  edge₁ : (subdivTarget T edge₀).edges
  edge₂ : (subdivTarget (subdivTarget T edge₀) edge₁).edges
  sheet : Fin 3 → Fin d

namespace Placement

variable (π : Placement T d)

abbrev T₁ : CFGraph := subdivTarget T π.edge₀
abbrev T₂ : CFGraph := subdivTarget π.T₁ π.edge₁
abbrev T₃ : CFGraph := subdivTarget π.T₂ π.edge₂

/-- The three subdivision vertices, in `T₃`. -/
def markVertex₃ : Fin 3 → π.T₃.V
  | 0 => subdivOld _ _ (subdivOld _ _ (subdivFresh T π.edge₀))
  | 1 => subdivOld _ _ (subdivFresh π.T₁ π.edge₁)
  | 2 => subdivFresh π.T₂ π.edge₂

abbrev T₄ : CFGraph := leafTarget π.T₃ (π.markVertex₃ 0)
abbrev T₅ : CFGraph := leafTarget π.T₄ (leafOld π.T₃ _ (π.markVertex₃ 1))
abbrev T₆ : CFGraph :=
  leafTarget π.T₅ (leafOld π.T₄ _ (leafOld π.T₃ _ (π.markVertex₃ 2)))

/-- A vertex of `T₃` in the glued target. -/
def lift₃ (v : π.T₃.V) : π.T₆.V := leafOld π.T₅ _ (leafOld π.T₄ _ (leafOld π.T₃ _ v))

/-- An old target vertex in the glued target. -/
def liftV (v : T.V) : π.T₆.V :=
  π.lift₃ (subdivOld π.T₂ _ (subdivOld π.T₁ _ (subdivOld T π.edge₀ v)))

/-- The image of mark `k` in the glued target. -/
def markTarget (k : Fin 3) : π.T₆.V := π.lift₃ (π.markVertex₃ k)

/-- The tip of the arm at mark `k`. -/
def tipTarget : Fin 3 → π.T₆.V
  | 0 => leafOld π.T₅ _ (leafOld π.T₄ _ (leafTip π.T₃ _))
  | 1 => leafOld π.T₅ _ (leafTip π.T₄ _)
  | 2 => leafTip π.T₅ _

/-- An old target edge in the glued target (its first half, if it is subdivided). -/
def liftE (e : T.edges) : π.T₆.edges :=
  leafOcc _ _ (some (leafOcc _ _ (some (leafOcc _ _ (some (subdivOcc _ _ (some
    (subdivOcc _ _ (some (subdivOcc _ _ (some e)))))))))))

/-- The arm at mark `k`, from the mark to the tip. -/
def armEdge : Fin 3 → π.T₆.edges
  | 0 => leafOcc _ _ (some (leafOcc _ _ (some (leafOcc _ _ none))))
  | 1 => leafOcc _ _ (some (leafOcc _ _ none))
  | 2 => leafOcc _ _ none

/-- The old target edge under mark `k`. -/
def parentEdge : Fin 3 → T.edges
  | 0 => π.edge₀
  | 1 => Option.elim ((subdivOcc T π.edge₀).symm π.edge₁) π.edge₀ id
  | 2 => Option.elim ((subdivOcc T π.edge₀).symm
      (Option.elim ((subdivOcc π.T₁ π.edge₁).symm π.edge₂) π.edge₁ id)) π.edge₀ id

end Placement

/-- **The Cools--Draisma tripod gluing**, as a gluing datum of degree `d + 1`
(Cools–Draisma; §5.1 and Theorem 5.1). Subdivide the target
at the three mark images; add a new sheet `Fin.last d`, a copy of the subdivided target; attach
an arm at each mark image, discrete along the arm and gluing the new sheet to the mark's sheet
at the tip. -/
def glueDatum (D : GluingDatum T d) (π : Placement T d) : GluingDatum π.T₆ (d + 1) :=
  leafDatum (leafDatum (leafDatum
    (extendDatum (refineDatum (refineDatum (refineDatum D π.edge₀) π.edge₁) π.edge₂))
    (π.markVertex₃ 0) (π.sheet 0).castSucc (Fin.last d))
    (leafOld π.T₃ _ (π.markVertex₃ 1)) (π.sheet 1).castSucc (Fin.last d))
    (leafOld π.T₄ _ (leafOld π.T₃ _ (π.markVertex₃ 2))) (π.sheet 2).castSucc (Fin.last d)

namespace Placement

variable (D : GluingDatum T d) (π : Placement T d)

/-- An old source vertex, in the glued source. -/
def oldSourceVertex (x : D.SourceVertex) : (glueDatum D π).SourceVertex :=
  (glueDatum D π).sourceEndpoint (π.liftV x.1.1) x.1.2.castSucc

/-- An old source edge, in the glued source (its first half, if its target is subdivided). -/
def oldSourceEdge (x : D.SourceEdge) : (glueDatum D π).SourceEdge :=
  (glueDatum D π).sourceEdge (π.liftE x.1.1) x.1.2.castSucc

/-- Mark `k`, as a source vertex of the glued datum. -/
def markSourceVertex (k : Fin 3) : (glueDatum D π).SourceVertex :=
  (glueDatum D π).sourceEndpoint (π.markTarget k) (π.sheet k).castSucc

/-- The arm of leg `k` in the sheet of mark `k`: the first edge of the hairpin. -/
def armSourceEdge (k : Fin 3) : (glueDatum D π).SourceEdge :=
  (glueDatum D π).sourceEdge (π.armEdge k) (π.sheet k).castSucc

/-- `a_k`: the index of the old source edge carrying mark `k`. -/
def markIndex (k : Fin 3) : ℕ := D.sourceEdgeIndex (D.sourceEdge (π.parentEdge k) (π.sheet k))

/-- The marks lie on the core: the old source edge under each mark is not dangling. -/
def NonDangling : Prop :=
  ∀ k, ¬ DraismaVargas.LocalCases.W4StableSource.IsDangling D
    (D.sourceEdge (π.parentEdge k) (π.sheet k))

end Placement

/-! ### The arms of the glued target -/

namespace Placement

variable (π : Placement T d)

/-- The arm at mark `k` runs from the mark image to the tip. -/
theorem armEdge_ends (k : Fin 3) :
    ((π.armEdge k : π.T₆.edges) : π.T₆.V × π.T₆.V) = (π.markTarget k, π.tipTarget k) := by
  match k with
  | 0 =>
    show ((leafOcc _ _ (some (leafOcc _ _ (some (leafOcc _ _ none)))) : π.T₆.edges) :
      π.T₆.V × π.T₆.V) = _
    rw [leafOcc_some, leafOcc_some, leafOcc_none]
    rfl
  | 1 =>
    show ((leafOcc _ _ (some (leafOcc _ _ none)) : π.T₆.edges) : π.T₆.V × π.T₆.V) = _
    rw [leafOcc_some, leafOcc_none]
    rfl
  | 2 =>
    show ((leafOcc _ _ none : π.T₆.edges) : π.T₆.V × π.T₆.V) = _
    rw [leafOcc_none]
    rfl

/-- The tip of each arm is a leaf of the glued target. -/
theorem vertex_degree_tipTarget (k : Fin 3) : vertex_degree π.T₆ (π.tipTarget k) = 1 := by
  match k with
  | 0 =>
    exact (vertex_degree_leafOld_of_ne π.T₅
      fun h ↦ leafTip_ne_leafOld _ _ _ (leafOld_injective _ _ h)).trans
      ((vertex_degree_leafOld_of_ne π.T₄ (leafTip_ne_leafOld _ _ _)).trans
        (vertex_degree_leafTip _ _))
  | 1 =>
    exact (vertex_degree_leafOld_of_ne π.T₅ (leafTip_ne_leafOld _ _ _)).trans
      (vertex_degree_leafTip _ _)
  | 2 => exact vertex_degree_leafTip _ _

end Placement

/-! ### Connectedness, genus, valencies and leaves of the glued target -/

theorem subdivTarget_connected (t : T.edges) (h : graph_connected T) :
    graph_connected (subdivTarget T t) := TargetExpansion.graph_connected _ _ _ h

theorem leafTarget_connected (u : T.V) (h : graph_connected T) :
    graph_connected (leafTarget T u) := TargetExpansion.graph_connected _ _ _ h

theorem subdivTarget_genus (t : T.edges) : genus (subdivTarget T t) = genus T :=
  TargetExpansion.graph_genus _ _ _

theorem leafTarget_genus (u : T.V) : genus (leafTarget T u) = genus T :=
  TargetExpansion.graph_genus _ _ _

theorem subdivTarget_edge_card (t : T.edges) :
    (subdivTarget T t).edges.card = T.edges.card + 1 := TargetExpansion.graph_edge_card _ _ _

theorem leafTarget_edge_card (u : T.V) :
    (leafTarget T u).edges.card = T.edges.card + 1 := TargetExpansion.graph_edge_card _ _ _

namespace Placement

variable (π : Placement T d)

theorem T₆_connected (h : graph_connected T) : graph_connected π.T₆ :=
  leafTarget_connected _ (leafTarget_connected _ (leafTarget_connected _
    (subdivTarget_connected _ (subdivTarget_connected _ (subdivTarget_connected _ h)))))

theorem T₆_genus : genus π.T₆ = genus T := by
  show genus (leafTarget _ _) = _
  rw [leafTarget_genus, leafTarget_genus, leafTarget_genus, subdivTarget_genus,
    subdivTarget_genus, subdivTarget_genus]

theorem T₆_edge_card : π.T₆.edges.card = T.edges.card + 6 := by
  show (leafTarget _ _).edges.card = _
  rw [leafTarget_edge_card, leafTarget_edge_card, leafTarget_edge_card, subdivTarget_edge_card,
    subdivTarget_edge_card, subdivTarget_edge_card]

end Placement

/-! ### Valencies after a subdivision -/

theorem vertex_degree_graph_old (w : T.V) (r : T.edges → Bool) {v : T.V} (hne : v ≠ w) :
    vertex_degree (TargetExpansion.graph T w r) (oldVertex T v) = vertex_degree T v := by
  refine (PendantDeletion.vertex_degree_eq_card_filter_incident _ _).trans ?_
  change (Multiset.card ((expandedEdges T w r).filter
    fun e : Vertex T × Vertex T ↦ e.1 = oldVertex T v ∨ e.2 = oldVertex T v) : ℤ) = _
  rw [card_filter_expandedEdges, ← card_filter_incident_eq_vertex_degree]
  have hnew : ¬ ((newEnds T w).1 = oldVertex T v ∨ (newEnds T w).2 = oldVertex T v) := by
    simp [newEnds, oldVertex, freshVertex, Ne.symm hne]
  rw [if_neg hnew, zero_add]
  congr 2
  apply Multiset.filter_congr
  intro e _
  simp only [oldEnds]
  rw [expandedEndpoint_eq_oldVertex_iff_of_ne _ _ _ _ _ _ hne,
    expandedEndpoint_eq_oldVertex_iff_of_ne _ _ _ _ _ _ hne]

theorem vertex_degree_subdivOld_of_ne (t : T.edges) {v : T.V} (hne : v ≠ (t : T.V × T.V).2) :
    vertex_degree (subdivTarget T t) (subdivOld T t v) = vertex_degree T v :=
  vertex_degree_graph_old _ _ hne


theorem fst_ne_snd (t : T.edges) : (t : T.V × T.V).1 ≠ (t : T.V × T.V).2 := fun h ↦
  T.loopless (t : T.V × T.V).1 (by
    rw [show ((t : T.V × T.V).1, (t : T.V × T.V).1) = (t : T.V × T.V) from Prod.ext rfl h]
    exact Multiset.coe_mem)

/-- Exactly one old occurrence is `t`. -/
theorem card_filter_eq_self (t : T.edges) (q : T.edges → Prop) [DecidablePred q]
    (hq : ∀ e, q e ↔ e = t) : Multiset.card ((enumeratedEdges T).filter q) = 1 := by
  rw [show (enumeratedEdges T).filter q =
      ((Finset.univ : Finset T.edges).filter q).val from rfl, Finset.card_val,
    Finset.card_eq_one]
  refine ⟨t, ?_⟩
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hq]

/-- Removing `t` from the occurrences at one of its ends lowers their number by one. -/
theorem card_filter_succ (t : T.edges) (q r : T.edges → Prop) [DecidablePred q]
    [DecidablePred r] (hq : q t) (hr : ∀ e, r e ↔ q e ∧ e ≠ t) :
    Multiset.card ((enumeratedEdges T).filter r) + 1 =
      Multiset.card ((enumeratedEdges T).filter q) := by
  classical
  have hsplit := Multiset.filter_add_not (fun e ↦ e = t) ((enumeratedEdges T).filter q)
  rw [Multiset.filter_filter, Multiset.filter_filter] at hsplit
  rw [← hsplit, Multiset.card_add, add_comm]
  congr 1
  · symm
    apply card_filter_eq_self t
    intro e
    constructor
    · intro h
      tauto
    · rintro rfl
      tauto
  · congr 1
    apply Multiset.filter_congr
    intro e _
    rw [hr]
    tauto

theorem vertex_degree_subdivOld_wall (t : T.edges) :
    vertex_degree (subdivTarget T t) (subdivOld T t (t : T.V × T.V).2) =
      vertex_degree T (t : T.V × T.V).2 := by
  classical
  refine (PendantDeletion.vertex_degree_eq_card_filter_incident _ _).trans ?_
  change (Multiset.card ((expandedEdges T _ (subdivRight T t)).filter
    fun e : Vertex T × Vertex T ↦ e.1 = oldVertex T (t : T.V × T.V).2 ∨
      e.2 = oldVertex T (t : T.V × T.V).2) : ℤ) = _
  rw [card_filter_expandedEdges, ← card_filter_incident_eq_vertex_degree,
    if_pos (show (newEnds T (t : T.V × T.V).2).1 = oldVertex T (t : T.V × T.V).2 ∨
      (newEnds T (t : T.V × T.V).2).2 = oldVertex T (t : T.V × T.V).2 from Or.inl rfl)]
  rw [← card_filter_succ t (fun e : T.edges ↦ (e : T.V × T.V).1 = (t : T.V × T.V).2 ∨
    (e : T.V × T.V).2 = (t : T.V × T.V).2)
    (fun e ↦ (oldEnds T _ (subdivRight T t) e).1 = oldVertex T (t : T.V × T.V).2 ∨
      (oldEnds T _ (subdivRight T t) e).2 = oldVertex T (t : T.V × T.V).2) (Or.inr rfl)
    fun e ↦ ?_]
  · push_cast
    ring
  · by_cases he : e = t
    · subst he
      simp [oldEnds, expandedEndpoint, subdivRight, oldVertex, freshVertex, fst_ne_snd]
    · simp [oldEnds, expandedEndpoint, subdivRight, he, oldVertex]

theorem vertex_degree_subdivFresh (t : T.edges) :
    vertex_degree (subdivTarget T t) (subdivFresh T t) = 2 := by
  classical
  refine (PendantDeletion.vertex_degree_eq_card_filter_incident _ _).trans ?_
  change (Multiset.card ((expandedEdges T _ (subdivRight T t)).filter
    fun e : Vertex T × Vertex T ↦ e.1 = freshVertex T ∨ e.2 = freshVertex T) : ℤ) = _
  rw [card_filter_expandedEdges,
    if_pos (show (newEnds T (t : T.V × T.V).2).1 = freshVertex T ∨
      (newEnds T (t : T.V × T.V).2).2 = freshVertex T from Or.inr rfl),
    card_filter_eq_self t _ fun e ↦ ?_]
  · rfl
  · by_cases he : e = t
    · subst he
      simp [oldEnds, expandedEndpoint, subdivRight, oldVertex, freshVertex, fst_ne_snd]
    · simp [oldEnds, expandedEndpoint, subdivRight, he, oldVertex, freshVertex]

theorem vertex_degree_subdivOld (t : T.edges) (v : T.V) :
    vertex_degree (subdivTarget T t) (subdivOld T t v) = vertex_degree T v := by
  by_cases h : v = (t : T.V × T.V).2
  · rw [h]
    exact vertex_degree_subdivOld_wall t
  · exact vertex_degree_subdivOld_of_ne t h

theorem subdivOld_injective (T : CFGraph) (t : T.edges) : Function.Injective (subdivOld T t) :=
  Sum.inl_injective

theorem subdivFresh_ne_subdivOld (T : CFGraph) (t : T.edges) (v : T.V) :
    subdivFresh T t ≠ subdivOld T t v :=
  Sum.inr_ne_inl

theorem isLeafVertex_iff (G : CFGraph) (v : G.V) : IsLeafVertex G v ↔ vertex_degree G v = 1 := by
  rw [← card_filter_incident_eq_vertex_degree]
  unfold IsLeafVertex GluingDatum.incidentEdges
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

theorem leafCount_eq_sum (G : CFGraph) :
    leafCount G = ∑ v : G.V, if IsLeafVertex G v then 1 else 0 := by
  rw [leafCount, leafVertices, Finset.card_filter]

theorem leafCount_subdivTarget (t : T.edges) : leafCount (subdivTarget T t) = leafCount T := by
  rw [leafCount_eq_sum, leafCount_eq_sum]
  refine (TargetExpansion.sum_vertices T _ (subdivRight T t)
    (fun v : (subdivTarget T t).V ↦ if IsLeafVertex (subdivTarget T t) v then 1 else 0)).trans ?_
  have hfresh : ¬ IsLeafVertex (subdivTarget T t) (subdivFresh T t) := by
    rw [isLeafVertex_iff, vertex_degree_subdivFresh]
    norm_num
  rw [show freshVertex T = subdivFresh T t from rfl, if_neg hfresh, add_zero]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [show oldVertex T v = subdivOld T t v from rfl]
  refine if_congr ?_ rfl rfl
  rw [isLeafVertex_iff, isLeafVertex_iff, vertex_degree_subdivOld]

theorem leafCount_leafTarget (u : T.V) (hu : vertex_degree T u = 2) :
    leafCount (leafTarget T u) = leafCount T + 1 := by
  rw [leafCount_eq_sum, leafCount_eq_sum]
  refine (TargetExpansion.sum_vertices T u (fun _ ↦ false)
    (fun v : (leafTarget T u).V ↦ if IsLeafVertex (leafTarget T u) v then 1 else 0)).trans ?_
  have htip : IsLeafVertex (leafTarget T u) (leafTip T u) := by
    rw [isLeafVertex_iff, vertex_degree_leafTip]
  rw [show freshVertex T = leafTip T u from rfl, if_pos htip]
  congr 1
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [show oldVertex T v = leafOld T u v from rfl]
  refine if_congr ?_ rfl rfl
  rw [isLeafVertex_iff, isLeafVertex_iff, vertex_degree_leafOld]
  by_cases h : v = u
  · subst h
    simp [hu]
  · simp [h]

namespace Placement

variable (π : Placement T d)

/-- Each mark image is a divalent vertex of `T₃`: it subdivides an edge. -/
theorem vertex_degree_markVertex₃ (k : Fin 3) : vertex_degree π.T₃ (π.markVertex₃ k) = 2 := by
  match k with
  | 0 => exact (vertex_degree_subdivOld _ _).trans ((vertex_degree_subdivOld _ _).trans
      (vertex_degree_subdivFresh _))
  | 1 => exact (vertex_degree_subdivOld _ _).trans (vertex_degree_subdivFresh _)
  | 2 => exact vertex_degree_subdivFresh _

theorem markVertex₃_one_ne_zero : π.markVertex₃ 1 ≠ π.markVertex₃ 0 := fun h ↦
  subdivFresh_ne_subdivOld _ _ _ (subdivOld_injective _ _ h)

theorem markVertex₃_two_ne_zero : π.markVertex₃ 2 ≠ π.markVertex₃ 0 :=
  subdivFresh_ne_subdivOld _ _ _

theorem markVertex₃_two_ne_one : π.markVertex₃ 2 ≠ π.markVertex₃ 1 :=
  subdivFresh_ne_subdivOld _ _ _

/-- **`l(T') = l(T) + 3`** (§5.4): subdividing keeps the leaves, and each arm adds
one, at a divalent vertex. -/
theorem leafCount_T₆ : leafCount π.T₆ = leafCount T + 3 := by
  have h4 : vertex_degree π.T₃ (π.markVertex₃ 0) = 2 := π.vertex_degree_markVertex₃ 0
  have h5 : vertex_degree π.T₄ (leafOld π.T₃ _ (π.markVertex₃ 1)) = 2 :=
    (vertex_degree_leafOld_of_ne _ π.markVertex₃_one_ne_zero).trans
      (π.vertex_degree_markVertex₃ 1)
  have h6 : vertex_degree π.T₅ (leafOld π.T₄ _ (leafOld π.T₃ _ (π.markVertex₃ 2))) = 2 :=
    (vertex_degree_leafOld_of_ne _ fun h ↦ π.markVertex₃_two_ne_one
      (leafOld_injective _ _ h)).trans ((vertex_degree_leafOld_of_ne _
        π.markVertex₃_two_ne_zero).trans (π.vertex_degree_markVertex₃ 2))
  have e6 : leafCount π.T₆ = leafCount π.T₅ + 1 := leafCount_leafTarget _ h6
  have e5 : leafCount π.T₅ = leafCount π.T₄ + 1 := leafCount_leafTarget _ h5
  have e4 : leafCount π.T₄ = leafCount π.T₃ + 1 := leafCount_leafTarget _ h4
  have e3 : leafCount π.T₃ = leafCount π.T₂ := leafCount_subdivTarget _
  have e2 : leafCount π.T₂ = leafCount π.T₁ := leafCount_subdivTarget _
  have e1 : leafCount π.T₁ = leafCount T := leafCount_subdivTarget _
  omega

end Placement

/-- The first end of the canonical source edge through a sheet is the canonical source vertex
through that sheet. -/
theorem sourceEnds_sourceEdge_fst {d' : ℕ} (D : GluingDatum T d') (e : T.edges) (i : Fin d') :
    (D.sourceEnds (D.sourceEdge e i)).1 = D.sourceEndpoint (e : T.V × T.V).1 i := by
  apply Subtype.ext
  show ((e : T.V × T.V).1,
      (D.vertexPartition (e : T.V × T.V).1).repr ((D.edgePartition e).repr i)) =
    ((e : T.V × T.V).1, (D.vertexPartition (e : T.V × T.V).1).repr i)
  rw [(D.refines_left e) _ _ ((D.edgePartition e).rel_repr_left i)]

/-! ### The genus of the glued source -/

/-- The number of blocks of a sheet partition. -/
def numBlocks (P : SheetPartition d) : ℕ := (Finset.univ.filter fun i ↦ P.repr i = i).card

theorem card_sourceVertex (D : GluingDatum T d) :
    Fintype.card D.SourceVertex = ∑ v, numBlocks (D.vertexPartition v) := by
  classical
  have h' : Fintype.card D.SourceVertex = Fintype.card {item : T.V × Fin d //
      (D.vertexPartition item.1).repr item.2 = item.2} := Fintype.card_congr (Equiv.refl _)
  rw [h', Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [numBlocks, Finset.card_filter]

theorem card_sourceEdge (D : GluingDatum T d) :
    Fintype.card D.SourceEdge = ∑ e, numBlocks (D.edgePartition e) := by
  classical
  have h' : Fintype.card D.SourceEdge = Fintype.card {item : T.edges × Fin d //
      (D.edgePartition item.1).repr item.2 = item.2} := Fintype.card_congr (Equiv.refl _)
  rw [h', Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [numBlocks, Finset.card_filter]

theorem genus_sourceGraph (D : GluingDatum T d) :
    genus D.sourceGraph =
      ((∑ e, numBlocks (D.edgePartition e) : ℕ) : ℤ) -
        ((∑ v, numBlocks (D.vertexPartition v) : ℕ) : ℤ) + 1 := by
  unfold genus
  rw [show Multiset.card D.sourceGraph.edges = Fintype.card D.SourceEdge by
      simp [GluingDatum.sourceGraph],
    show Fintype.card D.sourceGraph.V = Fintype.card D.SourceVertex from rfl,
    card_sourceVertex, card_sourceEdge]

theorem numBlocks_extendNew (P : SheetPartition d) :
    numBlocks (SheetOps.extendNew P) = numBlocks P + 1 := by
  unfold numBlocks
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [SheetOps.extendNew_repr_castSucc, SheetOps.extendNew_repr_last, Fin.castSucc_inj,
    if_true]

theorem numBlocks_discrete (d : ℕ) : numBlocks (SheetPartition.discrete d) = d := by
  simp [numBlocks, SheetPartition.discrete]

theorem numBlocks_pair {a b : Fin d} (hab : a ≠ b) : numBlocks (SheetOps.pair a b) = d - 1 := by
  unfold numBlocks
  rw [show (Finset.univ.filter fun i ↦ (SheetOps.pair a b).repr i = i) = Finset.univ.erase b by
    ext i
    by_cases hi : i = b
    · subst hi; simp [SheetOps.pair, hab]
    · simp [SheetOps.pair, hi]]
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]


theorem genus_refineDatum (D : GluingDatum T d) (t : T.edges) :
    genus (refineDatum D t).sourceGraph = genus D.sourceGraph := by
  rw [genus_sourceGraph, genus_sourceGraph]
  have hE : (∑ e, numBlocks ((refineDatum D t).edgePartition e)) =
      numBlocks (D.edgePartition t) + ∑ e, numBlocks (D.edgePartition e) := by
    rw [← (subdivOcc T t).sum_comp, Fintype.sum_option]
    simp only [refineDatum, Equiv.symm_apply_apply, Option.elim]
  have hV : (∑ v, numBlocks ((refineDatum D t).vertexPartition v)) =
      (∑ v, numBlocks (D.vertexPartition v)) + numBlocks (D.edgePartition t) :=
    TargetExpansion.sum_vertices T _ (subdivRight T t)
      (fun v : (subdivTarget T t).V ↦ numBlocks ((refineDatum D t).vertexPartition v))
  rw [hE, hV]
  push_cast
  ring

theorem genus_extendDatum (D : GluingDatum T d) :
    genus (extendDatum D).sourceGraph =
      genus D.sourceGraph + genus T - 1 := by
  rw [genus_sourceGraph, genus_sourceGraph]
  simp only [extendDatum, numBlocks_extendNew, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]
  unfold genus
  rw [Multiset.card_coe]
  push_cast
  ring

theorem genus_leafDatum (D : GluingDatum T d) (u : T.V) {a b : Fin d} (hab : a ≠ b) :
    genus (leafDatum D u a b).sourceGraph = genus D.sourceGraph + 1 := by
  rw [genus_sourceGraph, genus_sourceGraph]
  have hE : (∑ e, numBlocks ((leafDatum D u a b).edgePartition e)) =
      d + ∑ e, numBlocks (D.edgePartition e) := by
    rw [← (leafOcc T u).sum_comp, Fintype.sum_option]
    simp only [leafDatum, Equiv.symm_apply_apply, Option.elim, numBlocks_discrete]
  have hV : (∑ v, numBlocks ((leafDatum D u a b).vertexPartition v)) =
      (∑ v, numBlocks (D.vertexPartition v)) + (d - 1) := by
    refine (TargetExpansion.sum_vertices T u (fun _ ↦ false)
      (fun v : (leafTarget T u).V ↦ numBlocks ((leafDatum D u a b).vertexPartition v))).trans ?_
    exact congrArg (_ + ·) (numBlocks_pair hab)
  rw [hE, hV]
  have hd : 1 ≤ d := D.degree_pos
  push_cast [Nat.cast_sub hd]
  ring

/-- **The glued source has genus two more** (the genus count of Cools–Draisma): subdividing keeps
the genus, the new sheet is a disjoint tree (`-1`), and each arm closes a cycle (`+1`). -/
theorem genus_glueDatum (D : GluingDatum T d) (π : Placement T d) (hT : genus T = 0) :
    genus (glueDatum D π).sourceGraph = genus D.sourceGraph + 2 := by
  have hne : ∀ k, (π.sheet k).castSucc ≠ Fin.last d := fun k ↦ (Fin.castSucc_lt_last _).ne
  have h3 : genus π.T₃ = 0 := by
    show genus (subdivTarget _ _) = 0
    rw [subdivTarget_genus, subdivTarget_genus, subdivTarget_genus, hT]
  unfold glueDatum
  rw [genus_leafDatum _ _ (hne 2), genus_leafDatum _ _ (hne 1), genus_leafDatum _ _ (hne 0),
    genus_extendDatum, h3, genus_refineDatum, genus_refineDatum, genus_refineDatum]
  ring

/-! ### Riemann--Hurwitz, stage by stage -/

theorem leafTarget_cases (u : T.V) (x : (leafTarget T u).V) :
    (∃ w, x = leafOld T u w) ∨ x = leafTip T u := by
  rcases x with w | ⟨⟩
  · exact Or.inl ⟨w, rfl⟩
  · exact Or.inr rfl

theorem sum_incidentEdges_leafTarget (u : T.V) (x : (leafTarget T u).V)
    (f : (leafTarget T u).edges → ℤ) :
    ∑ e ∈ GluingDatum.incidentEdges x, f e =
      (if leafOld T u u = x ∨ leafTip T u = x then f (leafOcc T u none) else 0) +
        ∑ e : T.edges, if leafOld T u (e : T.V × T.V).1 = x ∨ leafOld T u (e : T.V × T.V).2 = x
          then f (leafOcc T u (some e)) else 0 := by
  classical
  rw [GluingDatum.incidentEdges, Finset.sum_filter, ← (leafOcc T u).sum_comp, Fintype.sum_option]
  simp only [leafOcc_none, leafOcc_some]


theorem blockCountWithin_discrete (P : SheetPartition d) (i : Fin d) :
    (SheetPartition.discrete d).blockCountWithin P i = P.blockCard i := by
  simp [SheetPartition.blockCountWithin, SheetPartition.discrete, SheetPartition.blockCard]

theorem leafDatum_vertexPartition_leafOld (D : GluingDatum T d) (u : T.V) (a b : Fin d)
    (w : T.V) : (leafDatum D u a b).vertexPartition (leafOld T u w) = D.vertexPartition w := rfl

theorem leafDatum_vertexPartition_leafTip (D : GluingDatum T d) (u : T.V) (a b : Fin d) :
    (leafDatum D u a b).vertexPartition (leafTip T u) = SheetOps.pair a b := rfl

theorem leafDatum_edgePartition_none (D : GluingDatum T d) (u : T.V) (a b : Fin d) :
    (leafDatum D u a b).edgePartition (leafOcc T u none) = SheetPartition.discrete d := by
  simp [leafDatum]

theorem leafDatum_edgePartition_some (D : GluingDatum T d) (u : T.V) (a b : Fin d)
    (e : T.edges) :
    (leafDatum D u a b).edgePartition (leafOcc T u (some e)) = D.edgePartition e := by
  simp [leafDatum]

theorem sum_incidentEdges_eq (v : T.V) (f : T.edges → ℤ) :
    ∑ e ∈ GluingDatum.incidentEdges v, f e =
      ∑ e : T.edges, if (e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v then f e else 0 := by
  rw [GluingDatum.incidentEdges, Finset.sum_filter]

theorem card_incidentEdges_eq_sum {G : CFGraph} (v : G.V) :
    ((GluingDatum.incidentEdges v).card : ℤ) = ∑ _e ∈ GluingDatum.incidentEdges v, (1 : ℤ) := by
  simp

theorem riemannHurwitz_leafDatum (D : GluingDatum T d) (hD : D.RiemannHurwitz) (u : T.V)
    (a b : Fin d) : (leafDatum D u a b).RiemannHurwitz := by
  intro x sheet
  rw [card_incidentEdges_eq_sum, sum_incidentEdges_leafTarget, sum_incidentEdges_leafTarget]
  simp only [leafDatum_edgePartition_none, leafDatum_edgePartition_some, blockCountWithin_discrete]
  rcases leafTarget_cases u x with ⟨w, rfl⟩ | rfl
  · have hw := hD w sheet
    rw [card_incidentEdges_eq_sum, sum_incidentEdges_eq, sum_incidentEdges_eq] at hw
    simp only [leafDatum_vertexPartition_leafOld, (leafOld_injective T u).eq_iff,
      leafTip_ne_leafOld, or_false]
    have hb : (0 : ℤ) ≤ (D.vertexPartition w).blockCard sheet := by positivity
    by_cases huw : u = w
    · simp only [huw, if_true]
      nlinarith
    · simp only [huw, if_false]
      linarith
  · simp only [leafDatum_vertexPartition_leafTip, Ne.symm (leafTip_ne_leafOld _ _ _),
      or_true, if_true, false_or, if_false, Finset.sum_const_zero, add_zero]
    have hb : (1 : ℤ) ≤ (SheetOps.pair a b).blockCard sheet := by
      exact_mod_cast (SheetOps.pair a b).blockCard_pos sheet
    push_cast
    linarith


namespace SheetOps

theorem block_extendNew_castSucc (P : SheetPartition d) (i : Fin d) :
    (extendNew P).block i.castSucc = (P.block i).map Fin.castSuccEmb := by
  ext j
  induction j using Fin.lastCases with
  | last =>
    simp only [SheetPartition.mem_block_iff, SheetPartition.rel_iff, extendNew_repr_castSucc,
      extendNew_repr_last, Finset.mem_map, Fin.coe_castSuccEmb]
    constructor
    · intro h
      exact absurd h (Fin.castSucc_lt_last _).ne
    · rintro ⟨j, -, hj⟩
      exact absurd hj (Fin.castSucc_lt_last _).ne
  | cast j =>
    simp only [SheetPartition.mem_block_iff, SheetPartition.rel_iff, extendNew_repr_castSucc,
      Fin.castSucc_inj, Finset.mem_map, Fin.coe_castSuccEmb]
    constructor
    · intro h
      exact ⟨j, h, rfl⟩
    · rintro ⟨j', hj', rfl⟩
      exact hj'

theorem block_extendNew_last (P : SheetPartition d) :
    (extendNew P).block (Fin.last d) = {Fin.last d} := by
  ext j
  induction j using Fin.lastCases with
  | last => simp
  | cast j =>
    simp only [SheetPartition.mem_block_iff, SheetPartition.rel_iff, extendNew_repr_castSucc,
      extendNew_repr_last, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd h.symm (Fin.castSucc_lt_last _).ne
    · intro h
      exact absurd h (Fin.castSucc_lt_last _).ne

theorem blockCard_extendNew_castSucc (P : SheetPartition d) (i : Fin d) :
    (extendNew P).blockCard i.castSucc = P.blockCard i := by
  rw [SheetPartition.blockCard, block_extendNew_castSucc, Finset.card_map]
  rfl

theorem blockCard_extendNew_last (P : SheetPartition d) :
    (extendNew P).blockCard (Fin.last d) = 1 := by
  rw [SheetPartition.blockCard, block_extendNew_last, Finset.card_singleton]

theorem blockCountWithin_extendNew_castSucc (E P : SheetPartition d) (i : Fin d) :
    (extendNew E).blockCountWithin (extendNew P) i.castSucc = E.blockCountWithin P i := by
  rw [SheetPartition.blockCountWithin, SheetPartition.blockCountWithin, block_extendNew_castSucc,
    Finset.map_eq_image, Finset.image_image]
  have : ((extendNew E).repr ∘ Fin.castSuccEmb) = Fin.castSucc ∘ E.repr := by
    funext j
    simp
  rw [this, ← Finset.image_image, Finset.card_image_of_injective _ (Fin.castSucc_injective _)]

theorem blockCountWithin_extendNew_last (E P : SheetPartition d) :
    (extendNew E).blockCountWithin (extendNew P) (Fin.last d) = 1 := by
  rw [SheetPartition.blockCountWithin, block_extendNew_last, Finset.image_singleton,
    Finset.card_singleton]

end SheetOps

theorem riemannHurwitz_extendDatum (D : GluingDatum T d) (hD : D.RiemannHurwitz) :
    (extendDatum D).RiemannHurwitz := by
  intro v x
  induction x using Fin.lastCases with
  | last =>
    show (∑ e ∈ GluingDatum.incidentEdges v,
        ((SheetOps.extendNew (D.edgePartition e)).blockCountWithin
          (SheetOps.extendNew (D.vertexPartition v)) (Fin.last d) : ℤ)) - 2 ≥
      ((SheetOps.extendNew (D.vertexPartition v)).blockCard (Fin.last d) : ℤ) *
        (((GluingDatum.incidentEdges v).card : ℤ) - 2)
    simp only [SheetOps.blockCountWithin_extendNew_last, SheetOps.blockCard_extendNew_last]
    rw [card_incidentEdges_eq_sum]
    push_cast
    linarith
  | cast i =>
    show (∑ e ∈ GluingDatum.incidentEdges v,
        ((SheetOps.extendNew (D.edgePartition e)).blockCountWithin
          (SheetOps.extendNew (D.vertexPartition v)) i.castSucc : ℤ)) - 2 ≥
      ((SheetOps.extendNew (D.vertexPartition v)).blockCard i.castSucc : ℤ) *
        (((GluingDatum.incidentEdges v).card : ℤ) - 2)
    simp only [SheetOps.blockCountWithin_extendNew_castSucc, SheetOps.blockCard_extendNew_castSucc]
    exact hD v i


theorem subdivTarget_cases (t : T.edges) (x : (subdivTarget T t).V) :
    (∃ w, x = subdivOld T t w) ∨ x = subdivFresh T t := by
  rcases x with w | ⟨⟩
  · exact Or.inl ⟨w, rfl⟩
  · exact Or.inr rfl

theorem sum_incidentEdges_subdivTarget (t : T.edges) (x : (subdivTarget T t).V)
    (f : (subdivTarget T t).edges → ℤ) :
    ∑ e ∈ GluingDatum.incidentEdges x, f e =
      (if subdivOld T t (t : T.V × T.V).2 = x ∨ subdivFresh T t = x then
        f (subdivOcc T t none) else 0) +
        ∑ e : T.edges, if ((subdivOcc T t (some e) : (subdivTarget T t).edges) :
            (subdivTarget T t).V × (subdivTarget T t).V).1 = x ∨
          ((subdivOcc T t (some e) : (subdivTarget T t).edges) :
            (subdivTarget T t).V × (subdivTarget T t).V).2 = x
          then f (subdivOcc T t (some e)) else 0 := by
  classical
  rw [GluingDatum.incidentEdges, Finset.sum_filter, ← (subdivOcc T t).sum_comp,
    Fintype.sum_option]
  simp only [subdivOcc_none]

theorem sum_incidentEdges_subdivOld (t : T.edges) (w : T.V) (g : T.edges → ℤ)
    (f : (subdivTarget T t).edges → ℤ) (hf : ∀ e, f (subdivOcc T t (some e)) = g e)
    (hnone : f (subdivOcc T t none) = g t) :
    ∑ e ∈ GluingDatum.incidentEdges (subdivOld T t w), f e =
      ∑ e ∈ GluingDatum.incidentEdges w, g e := by
  classical
  rw [sum_incidentEdges_subdivTarget, sum_incidentEdges_eq, hnone]
  simp only [hf]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ t),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ t)]
  have herase : (∑ e ∈ Finset.univ.erase t,
      if ((subdivOcc T t (some e) : (subdivTarget T t).edges) :
          (subdivTarget T t).V × (subdivTarget T t).V).1 = subdivOld T t w ∨
        ((subdivOcc T t (some e) : (subdivTarget T t).edges) :
          (subdivTarget T t).V × (subdivTarget T t).V).2 = subdivOld T t w
        then g e else 0) =
      ∑ e ∈ Finset.univ.erase t,
        if (e : T.V × T.V).1 = w ∨ (e : T.V × T.V).2 = w then g e else 0 := by
    refine Finset.sum_congr rfl fun e he ↦ ?_
    simp only [subdivOcc_some_of_ne T (Finset.ne_of_mem_erase he),
      (subdivOld_injective T t).eq_iff]
  rw [herase]
  simp only [subdivOcc_some_self, (subdivOld_injective T t).eq_iff, subdivFresh_ne_subdivOld,
    or_false]
  have hne := fst_ne_snd t
  by_cases h1 : (t : T.V × T.V).1 = w <;> by_cases h2 : (t : T.V × T.V).2 = w
  · exact absurd (h1.trans h2.symm) hne
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

theorem sum_incidentEdges_subdivFresh (t : T.edges) (f : (subdivTarget T t).edges → ℤ) :
    ∑ e ∈ GluingDatum.incidentEdges (subdivFresh T t), f e =
      f (subdivOcc T t none) + f (subdivOcc T t (some t)) := by
  classical
  rw [sum_incidentEdges_subdivTarget, ← Finset.sum_erase_add _ _ (Finset.mem_univ t)]
  have herase : (∑ e ∈ Finset.univ.erase t,
      if ((subdivOcc T t (some e) : (subdivTarget T t).edges) :
          (subdivTarget T t).V × (subdivTarget T t).V).1 = subdivFresh T t ∨
        ((subdivOcc T t (some e) : (subdivTarget T t).edges) :
          (subdivTarget T t).V × (subdivTarget T t).V).2 = subdivFresh T t
        then f (subdivOcc T t (some e)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun e he ↦ ?_
    simp only [subdivOcc_some_of_ne T (Finset.ne_of_mem_erase he),
      Ne.symm (subdivFresh_ne_subdivOld T t _), or_self, if_false]
  rw [herase]
  simp [subdivOcc_some_self]

theorem refineDatum_edgePartition_none (D : GluingDatum T d) (t : T.edges) :
    (refineDatum D t).edgePartition (subdivOcc T t none) = D.edgePartition t := by
  simp [refineDatum]

theorem refineDatum_edgePartition_some (D : GluingDatum T d) (t e : T.edges) :
    (refineDatum D t).edgePartition (subdivOcc T t (some e)) = D.edgePartition e := by
  simp [refineDatum]

theorem blockCountWithin_self (E : SheetPartition d) (i : Fin d) : E.blockCountWithin E i = 1 := by
  rw [SheetPartition.blockCountWithin, Finset.card_eq_one]
  refine ⟨E.repr i, ?_⟩
  ext j
  simp only [Finset.mem_image, SheetPartition.mem_block_iff, SheetPartition.rel_iff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk.symm
  · rintro rfl
    exact ⟨i, rfl, rfl⟩

theorem riemannHurwitz_refineDatum (D : GluingDatum T d) (hD : D.RiemannHurwitz) (t : T.edges) :
    (refineDatum D t).RiemannHurwitz := by
  intro x sheet
  rcases subdivTarget_cases t x with ⟨w, rfl⟩ | rfl
  · have hw := hD w sheet
    rw [card_incidentEdges_eq_sum, sum_incidentEdges_subdivOld t w (fun _ ↦ (1 : ℤ))
      (fun _ ↦ (1 : ℤ)) (fun _ ↦ rfl) rfl,
      ← card_incidentEdges_eq_sum,
      sum_incidentEdges_subdivOld t w
        (fun e ↦ ((D.edgePartition e).blockCountWithin (D.vertexPartition w) sheet : ℤ)) _
        (fun e ↦ by rw [refineDatum_edgePartition_some]; rfl)
        (by rw [refineDatum_edgePartition_none]; rfl)]
    exact hw
  · rw [card_incidentEdges_eq_sum, sum_incidentEdges_subdivFresh, sum_incidentEdges_subdivFresh,
      refineDatum_edgePartition_none, refineDatum_edgePartition_some]
    show (((D.edgePartition t).blockCountWithin (D.edgePartition t) sheet : ℕ) : ℤ) +
        (((D.edgePartition t).blockCountWithin (D.edgePartition t) sheet : ℕ) : ℤ) - 2 ≥
      (((D.edgePartition t).blockCard sheet : ℕ) : ℤ) * ((1 : ℤ) + 1 - 2)
    rw [blockCountWithin_self]
    norm_num

/-! ### Connectedness of the glued source -/

section Connectivity

/-- The underlying simple graph of the source of a datum. -/
abbrev srcGraph {S : CFGraph} {k : ℕ} (E : GluingDatum S k) : SimpleGraph E.SourceVertex :=
  Utilities.underlyingSimpleGraph E.sourceGraph

theorem sourceEnds_sourceEdge_snd {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (e : S.edges)
    (i : Fin k) : (E.sourceEnds (E.sourceEdge e i)).2 = E.sourceEndpoint (e : S.V × S.V).2 i := by
  apply Subtype.ext
  show ((e : S.V × S.V).2,
      (E.vertexPartition (e : S.V × S.V).2).repr ((E.edgePartition e).repr i)) =
    ((e : S.V × S.V).2, (E.vertexPartition (e : S.V × S.V).2).repr i)
  rw [(E.refines_right e) _ _ ((E.edgePartition e).rel_repr_left i)]

/-- Every target edge and sheet give an adjacency of the source. -/
theorem adj_sourceEndpoint {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (e : S.edges)
    (i : Fin k) :
    (srcGraph E).Adj (E.sourceEndpoint (e : S.V × S.V).1 i)
      (E.sourceEndpoint (e : S.V × S.V).2 i) := by
  have hmem : E.sourceEnds (E.sourceEdge e i) ∈ E.sourceGraph.edges :=
    Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ _))
  rw [← sourceEnds_sourceEdge_fst, ← sourceEnds_sourceEdge_snd]
  exact GraphContraction.num_edges_pos_of_mem_edges E.sourceGraph _ _ hmem

/-- Every adjacency of the source comes from a target edge and a sheet. -/
theorem exists_of_adj {S : CFGraph} {k : ℕ} (E : GluingDatum S k) {a b : E.SourceVertex}
    (h : (srcGraph E).Adj a b) :
    ∃ (e : S.edges) (i : Fin k),
      (a = E.sourceEndpoint (e : S.V × S.V).1 i ∧ b = E.sourceEndpoint (e : S.V × S.V).2 i) ∨
        (b = E.sourceEndpoint (e : S.V × S.V).1 i ∧
          a = E.sourceEndpoint (e : S.V × S.V).2 i) := by
  obtain ⟨pair, hmem, hpair⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos E.sourceGraph a b h
  obtain ⟨x, -, hx⟩ := Multiset.mem_map.mp hmem
  refine ⟨x.1.1, x.1.2, ?_⟩
  rcases hpair with rfl | rfl
  · exact Or.inl ⟨(congrArg Prod.fst hx).symm, (congrArg Prod.snd hx).symm⟩
  · exact Or.inr ⟨(congrArg Prod.fst hx).symm, (congrArg Prod.snd hx).symm⟩

theorem reachable_map {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} (f : α → β)
    (hf : ∀ a b, G.Adj a b → H.Reachable (f a) (f b)) (hG : G.Preconnected) (a b : α) :
    H.Reachable (f a) (f b) := by
  obtain ⟨w⟩ := hG a b
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h _ ih => exact (hf _ _ h).trans ih

/-- A map out of a connected source that sends each source edge to a reachable pair sends any
two vertices to a reachable pair. -/
theorem reachable_of_sourceEdges {S : CFGraph} {k : ℕ} {β : Type*} (E : GluingDatum S k)
    (H : SimpleGraph β) (f : E.SourceVertex → β)
    (hf : ∀ (e : S.edges) (i : Fin k),
      H.Reachable (f (E.sourceEndpoint (e : S.V × S.V).1 i))
        (f (E.sourceEndpoint (e : S.V × S.V).2 i)))
    (hE : E.Connected) (a b : E.SourceVertex) : H.Reachable (f a) (f b) := by
  have hc := (Utilities.graph_connected_iff_underlyingSimpleGraph_connected _).mp hE
  refine reachable_map f (fun a b h ↦ ?_) hc.preconnected a b
  obtain ⟨e, i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_of_adj E h
  · exact hf e i
  · exact (hf e i).symm

/-- A map out of a connected target graph that sends each edge to a reachable pair. -/
theorem reachable_of_targetEdges {S : CFGraph} {β : Type*} (H : SimpleGraph β) (f : S.V → β)
    (hf : ∀ e : S.edges, H.Reachable (f (e : S.V × S.V).1) (f (e : S.V × S.V).2))
    (hS : graph_connected S) (a b : S.V) : H.Reachable (f a) (f b) := by
  have hc := (Utilities.graph_connected_iff_underlyingSimpleGraph_connected _).mp hS
  refine reachable_map f (fun a b h ↦ ?_) hc.preconnected a b
  obtain ⟨pair, hmem, hpair⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos _ a b h
  obtain ⟨e, he⟩ := exists_occurrence_of_mem_edges hmem
  have h := hf e
  rw [he] at h
  rcases hpair with rfl | rfl
  · exact h
  · exact h.symm

theorem connected_of_reachable {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (x₀ : E.SourceVertex)
    (h : ∀ x, (srcGraph E).Reachable x₀ x) : E.Connected := by
  unfold GluingDatum.Connected
  rw [Utilities.graph_connected_iff_underlyingSimpleGraph_connected,
    SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨x₀, h⟩

/-- **Refining at a target edge keeps the source connected**: the old source edges over `t`
become paths of length two through the fresh vertex. -/
theorem refineDatum_connected (D : GluingDatum T d) (t : T.edges) (hD : D.Connected) :
    (refineDatum D t).Connected := by
  let f : D.SourceVertex → (refineDatum D t).SourceVertex := fun x ↦
    (refineDatum D t).sourceEndpoint (subdivOld T t x.1.1) x.1.2
  have hf_end : ∀ w i, f (D.sourceEndpoint w i) =
      (refineDatum D t).sourceEndpoint (subdivOld T t w) i := by
    intro w i
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show (D.vertexPartition w).repr ((D.vertexPartition w).repr i) = (D.vertexPartition w).repr i
    exact (D.vertexPartition w).repr_idem i
  have hold : ∀ (e : T.edges) (i : Fin d),
      (srcGraph (refineDatum D t)).Reachable
        ((refineDatum D t).sourceEndpoint (subdivOld T t (e : T.V × T.V).1) i)
        ((refineDatum D t).sourceEndpoint (subdivOld T t (e : T.V × T.V).2) i) := by
    intro e i
    by_cases he : e = t
    · subst he
      have h1 := adj_sourceEndpoint (refineDatum D e) (subdivOcc T e (some e)) i
      rw [subdivOcc_some_self] at h1
      have h2 := adj_sourceEndpoint (refineDatum D e) (subdivOcc T e none) i
      rw [subdivOcc_none] at h2
      exact h1.reachable.trans h2.reachable.symm
    · have h := adj_sourceEndpoint (refineDatum D t) (subdivOcc T t (some e)) i
      rw [subdivOcc_some_of_ne T he] at h
      exact h.reachable
  have hreach : ∀ a b : D.SourceVertex, (srcGraph (refineDatum D t)).Reachable (f a) (f b) :=
    reachable_of_sourceEdges D _ f (fun e i ↦ by rw [hf_end, hf_end]; exact hold e i) hD
  let i₀ : Fin d := ⟨0, D.degree_pos⟩
  let a₀ := D.sourceEndpoint (t : T.V × T.V).2 i₀
  refine connected_of_reachable _ (f a₀) fun x ↦ ?_
  obtain ⟨⟨v, i⟩, hx⟩ := x
  rcases v with w | ⟨⟩
  · have hx' : f ⟨(w, i), hx⟩ = ⟨(Sum.inl w, i), hx⟩ :=
      (refineDatum D t).sourceEndpoint_self ⟨(Sum.inl w, i), hx⟩
    rw [← hx']
    exact hreach a₀ ⟨(w, i), hx⟩
  · have hadj := adj_sourceEndpoint (refineDatum D t) (subdivOcc T t none) i
    rw [subdivOcc_none, ← hf_end] at hadj
    have hx' : (refineDatum D t).sourceEndpoint (subdivFresh T t) i = ⟨(Sum.inr (), i), hx⟩ :=
      (refineDatum D t).sourceEndpoint_self ⟨(Sum.inr (), i), hx⟩
    rw [← hx']
    exact (hreach a₀ _).trans hadj.reachable


namespace Placement

variable (π : Placement T d)

/-- An edge of `T₃` in the glued target. -/
def liftE₃ (e : π.T₃.edges) : π.T₆.edges :=
  leafOcc _ _ (some (leafOcc _ _ (some (leafOcc _ _ (some e)))))

theorem liftE₃_ends (e : π.T₃.edges) :
    ((π.liftE₃ e : π.T₆.edges) : π.T₆.V × π.T₆.V) =
      (π.lift₃ (e : π.T₃.V × π.T₃.V).1, π.lift₃ (e : π.T₃.V × π.T₃.V).2) := by
  show ((leafOcc _ _ (some (leafOcc _ _ (some (leafOcc _ _ (some e))))) : π.T₆.edges) :
    π.T₆.V × π.T₆.V) = _
  rw [leafOcc_some, leafOcc_some, leafOcc_some]
  rfl

theorem T₃_connected (h : graph_connected T) : graph_connected π.T₃ :=
  subdivTarget_connected _ (subdivTarget_connected _ (subdivTarget_connected _ h))

end Placement

/-- **The glued source is connected** (Cools–Draisma). The old sheets over `T₃` are connected
(`refineDatum_connected`, three times), the new sheet is a copy of the connected `T₃`, the tip of
the first arm joins the two, and every tip hangs off its mark image by an arm. -/
theorem glueDatum_connected (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected)
    (hT : graph_connected T) : (glueDatum D π).Connected := by
  let D₃ := refineDatum (refineDatum (refineDatum D π.edge₀) π.edge₁) π.edge₂
  have hD₃ : D₃.Connected :=
    refineDatum_connected _ _ (refineDatum_connected _ _ (refineDatum_connected _ _ hD))
  let G := glueDatum D π
  -- the old sheets, over `T₃`
  let O : D₃.SourceVertex → G.SourceVertex := fun x ↦
    G.sourceEndpoint (π.lift₃ x.1.1) x.1.2.castSucc
  have hO_end : ∀ w i, O (D₃.sourceEndpoint w i) = G.sourceEndpoint (π.lift₃ w) i.castSucc := by
    intro w i
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show (SheetOps.extendNew (D₃.vertexPartition w)).repr ((D₃.vertexPartition w).repr i).castSucc =
      (SheetOps.extendNew (D₃.vertexPartition w)).repr i.castSucc
    simp only [SheetOps.extendNew_repr_castSucc, SheetPartition.repr_idem]
  have hliftAdj : ∀ (e : π.T₃.edges) (j : Fin (d + 1)),
      (srcGraph G).Adj (G.sourceEndpoint (π.lift₃ (e : π.T₃.V × π.T₃.V).1) j)
        (G.sourceEndpoint (π.lift₃ (e : π.T₃.V × π.T₃.V).2) j) := by
    intro e j
    have h := adj_sourceEndpoint G (π.liftE₃ e) j
    rw [π.liftE₃_ends] at h
    exact h
  have harmAdj : ∀ (k : Fin 3) (j : Fin (d + 1)),
      (srcGraph G).Adj (G.sourceEndpoint (π.lift₃ (π.markVertex₃ k)) j)
        (G.sourceEndpoint (π.tipTarget k) j) := by
    intro k j
    have h := adj_sourceEndpoint G (π.armEdge k) j
    rw [π.armEdge_ends] at h
    exact h
  have hO : ∀ a b, (srcGraph G).Reachable (O a) (O b) :=
    reachable_of_sourceEdges D₃ _ O
      (fun e i ↦ by rw [hO_end, hO_end]; exact (hliftAdj e i.castSucc).reachable) hD₃
  -- the new sheet, a copy of `T₃`
  let N : π.T₃.V → G.SourceVertex := fun v ↦ G.sourceEndpoint (π.lift₃ v) (Fin.last d)
  have hN : ∀ a b, (srcGraph G).Reachable (N a) (N b) :=
    reachable_of_targetEdges _ N (fun e ↦ (hliftAdj e (Fin.last d)).reachable)
      (π.T₃_connected hT)
  -- the tip of the first arm joins the new sheet to the sheet of the first mark
  have htip : G.sourceEndpoint (π.tipTarget 0) (Fin.last d) =
      G.sourceEndpoint (π.tipTarget 0) (π.sheet 0).castSucc := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show (SheetOps.pair (π.sheet 0).castSucc (Fin.last d)).repr (Fin.last d) =
      (SheetOps.pair (π.sheet 0).castSucc (Fin.last d)).repr (π.sheet 0).castSucc
    simp [SheetOps.pair, (Fin.castSucc_lt_last (π.sheet 0)).ne]
  let x₀ := N (π.markVertex₃ 0)
  have hlink : (srcGraph G).Reachable x₀ (O (D₃.sourceEndpoint (π.markVertex₃ 0) (π.sheet 0))) := by
    have h1 := (harmAdj 0 (Fin.last d)).reachable
    rw [htip] at h1
    rw [hO_end]
    exact h1.trans (harmAdj 0 (π.sheet 0).castSucc).reachable.symm
  have hlift : ∀ v j, (srcGraph G).Reachable x₀ (G.sourceEndpoint (π.lift₃ v) j) := by
    intro v j
    induction j using Fin.lastCases with
    | last => exact hN _ v
    | cast i =>
      rw [← hO_end]
      exact hlink.trans (hO _ _)
  have htips : ∀ k j, (srcGraph G).Reachable x₀ (G.sourceEndpoint (π.tipTarget k) j) :=
    fun k j ↦ (hlift (π.markVertex₃ k) j).trans (harmAdj k j).reachable
  refine connected_of_reachable G x₀ fun x ↦ ?_
  rw [← G.sourceEndpoint_self x]
  obtain ⟨⟨v, j⟩, hx⟩ := x
  rcases v with ((v | ⟨⟩) | ⟨⟩) | ⟨⟩
  · exact hlift v j
  · exact htips 0 j
  · exact htips 1 j
  · exact htips 2 j

end Connectivity

/-! ### The arms of the glued source

The hairpin of each leg, read off the glued datum: off the hairpin an arm ends at a source
vertex of valency one, so it dangles (`isDangling_armSheetEdge`); the two arms of the hairpin meet
at the tip, a passage once they survive (`nonDanglingValency_tip`, `stablePath_hairpin`); and the
column of an arm in any labelling is `2` in the row of the hairpin (`matrix_armColumn`). -/

section Arms

open DraismaVargas.Count
open DraismaVargas.LocalCases.W4StableSource

namespace Placement

variable (π : Placement T d)

theorem markTarget_ne_tipTarget (k : Fin 3) : π.markTarget k ≠ π.tipTarget k := by
  match k with
  | 0 => exact fun h ↦ leafTip_ne_leafOld _ _ _ (leafOld_injective _ _ (leafOld_injective _ _ h)).symm
  | 1 => exact fun h ↦ leafTip_ne_leafOld _ _ _ (leafOld_injective _ _ h).symm
  | 2 => exact fun h ↦ leafTip_ne_leafOld _ _ _ h.symm

/-- The only target edge at the tip of an arm is the arm. -/
theorem incidentEdges_tipTarget (k : Fin 3) :
    GluingDatum.incidentEdges (π.tipTarget k) = {π.armEdge k} := by
  have hcard : (GluingDatum.incidentEdges (π.tipTarget k)).card = 1 :=
    (isLeafVertex_iff _ _).mpr (π.vertex_degree_tipTarget k)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hmem : π.armEdge k ∈ GluingDatum.incidentEdges (π.tipTarget k) := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr (congrArg Prod.snd (π.armEdge_ends k))
  rw [ha] at hmem ⊢
  rw [Finset.mem_singleton.mp hmem]

end Placement

variable (D : GluingDatum T d) (π : Placement T d)

theorem glueDatum_edgePartition_armEdge (k : Fin 3) :
    (glueDatum D π).edgePartition (π.armEdge k) = SheetPartition.discrete (d + 1) := by
  match k with
  | 0 =>
    show (glueDatum D π).edgePartition
      (leafOcc _ _ (some (leafOcc _ _ (some (leafOcc _ _ none))))) = _
    unfold glueDatum
    rw [leafDatum_edgePartition_some, leafDatum_edgePartition_some, leafDatum_edgePartition_none]
  | 1 =>
    show (glueDatum D π).edgePartition (leafOcc _ _ (some (leafOcc _ _ none))) = _
    unfold glueDatum
    rw [leafDatum_edgePartition_some, leafDatum_edgePartition_none]
  | 2 =>
    show (glueDatum D π).edgePartition (leafOcc _ _ none) = _
    unfold glueDatum
    rw [leafDatum_edgePartition_none]

theorem glueDatum_vertexPartition_tipTarget (k : Fin 3) :
    (glueDatum D π).vertexPartition (π.tipTarget k) =
      SheetOps.pair (π.sheet k).castSucc (Fin.last d) := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- The arm at `k` in the sheet `j`. -/
def armSheetEdge (k : Fin 3) (j : Fin (d + 1)) : (glueDatum D π).SourceEdge :=
  (glueDatum D π).sourceEdge (π.armEdge k) j

theorem armSheetEdge_sheet (k : Fin 3) (j : Fin (d + 1)) : (armSheetEdge D π k j).1.2 = j := by
  show ((glueDatum D π).edgePartition (π.armEdge k)).repr j = j
  rw [glueDatum_edgePartition_armEdge]
  rfl

theorem eq_armSheetEdge {k : Fin 3} (x : (glueDatum D π).SourceEdge) (hx : x.1.1 = π.armEdge k) :
    x = armSheetEdge D π k x.1.2 := by
  obtain ⟨⟨ε, j⟩, hj⟩ := x
  simp only at hx
  subst hx
  apply Subtype.ext
  exact Prod.ext rfl hj.symm

theorem pair_rel_iff (a b x y : Fin d) :
    (SheetOps.pair a b).Rel x y ↔ (if x = b then a else x) = (if y = b then a else y) := by
  rw [SheetPartition.rel_iff]
  rfl

/-- **The source edges at a source vertex over the tip of an arm** are the arms in the sheets of
its block. -/
theorem incident_tip_iff (k : Fin 3) (j : Fin (d + 1)) (x : (glueDatum D π).SourceEdge) :
    Incident (glueDatum D π) x ((glueDatum D π).sourceEndpoint (π.tipTarget k) j) ↔
      x.1.1 = π.armEdge k ∧
        (SheetOps.pair (π.sheet k).castSucc (Fin.last d)).Rel x.1.2 j := by
  have hEnds : ∀ w i, (glueDatum D π).sourceEndpoint w i =
      (glueDatum D π).sourceEndpoint (π.tipTarget k) j ↔
        w = π.tipTarget k ∧ ((glueDatum D π).vertexPartition w).Rel i j := by
    intro w i
    rw [GluingDatum.sourceEndpoint_eq_iff]
    constructor
    · rintro ⟨hw, hrel⟩
      have hw' : w = π.tipTarget k := hw
      subst hw'
      refine ⟨rfl, ?_⟩
      rw [SheetPartition.rel_iff] at hrel ⊢
      exact hrel.trans (SheetPartition.repr_idem _ j)
    · rintro ⟨rfl, hrel⟩
      refine ⟨rfl, ?_⟩
      rw [SheetPartition.rel_iff] at hrel ⊢
      exact hrel.trans (SheetPartition.repr_idem _ j).symm
  constructor
  · intro h
    have hinc : ∀ w, (w = ((x.1.1 : π.T₆.edges) : π.T₆.V × π.T₆.V).1 ∨
        w = ((x.1.1 : π.T₆.edges) : π.T₆.V × π.T₆.V).2) → w = π.tipTarget k →
        x.1.1 = π.armEdge k := by
      rintro w hw rfl
      have hmem : x.1.1 ∈ GluingDatum.incidentEdges (π.tipTarget k) := by
        simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hw with hw | hw
        · exact Or.inl hw.symm
        · exact Or.inr hw.symm
      rw [π.incidentEdges_tipTarget] at hmem
      exact Finset.mem_singleton.mp hmem
    rcases h with h | h
    · obtain ⟨hw, -⟩ := (hEnds _ _).mp h
      have hx := hinc _ (Or.inl rfl) hw
      exfalso
      rw [hx, π.armEdge_ends] at hw
      exact π.markTarget_ne_tipTarget k hw
    · obtain ⟨hw, hrel⟩ := (hEnds _ _).mp h
      have hx := hinc _ (Or.inr rfl) hw
      refine ⟨hx, ?_⟩
      rw [hw, glueDatum_vertexPartition_tipTarget] at hrel
      exact hrel
  · rintro ⟨hx, hrel⟩
    right
    apply (hEnds _ _).mpr
    have hw : ((x.1.1 : π.T₆.edges) : π.T₆.V × π.T₆.V).2 = π.tipTarget k := by
      rw [hx, π.armEdge_ends]
    refine ⟨hw, ?_⟩
    rw [hw, glueDatum_vertexPartition_tipTarget]
    exact hrel


theorem pair_rel_last (k : Fin 3) :
    (SheetOps.pair (π.sheet k).castSucc (Fin.last d)).Rel (Fin.last d) (π.sheet k).castSucc := by
  rw [pair_rel_iff, if_pos rfl, if_neg (Fin.castSucc_lt_last _).ne]

/-- **The arms off the hairpin dangle**: in a sheet other than the mark's and the new one, the
arm ends at a source vertex of valency one. -/
theorem isDangling_armSheetEdge (hconn : (glueDatum D π).Connected) (k : Fin 3)
    (j : Fin (d + 1)) (hK : j ≠ (π.sheet k).castSucc) (hΛ : j ≠ Fin.last d) :
    IsDangling (glueDatum D π) (armSheetEdge D π k j) := by
  apply isDangling_of_sourceEnds_snd_degree_eq_one _ hconn
  have hend : ((glueDatum D π).sourceEnds (armSheetEdge D π k j)).2 =
      (glueDatum D π).sourceEndpoint (π.tipTarget k) j := by
    rw [armSheetEdge, sourceEnds_sourceEdge_snd, π.armEdge_ends]
  rw [hend, vertex_degree_sourceGraph_eq_card_incidentSourceEdge, Nat.cast_eq_one,
    Fintype.card_eq_one_iff]
  refine ⟨⟨armSheetEdge D π k j, (incident_tip_iff D π k j _).mpr ⟨rfl, ?_⟩⟩, ?_⟩
  · rw [armSheetEdge_sheet]
    exact (SheetPartition.rel_iff _ _ _).mpr rfl
  · rintro ⟨x, hx⟩
    obtain ⟨hx1, hrel⟩ := (incident_tip_iff D π k j x).mp hx
    apply Subtype.ext
    show x = armSheetEdge D π k j
    rw [eq_armSheetEdge D π x hx1]
    congr 1
    rw [pair_rel_iff, if_neg hΛ] at hrel
    split_ifs at hrel with h
    · exact absurd hrel.symm hK
    · exact hrel

theorem armSheetEdge_ne (k : Fin 3) {i j : Fin (d + 1)} (h : i ≠ j) :
    armSheetEdge D π k i ≠ armSheetEdge D π k j := fun he ↦ h (by
  have := congrArg (fun x : (glueDatum D π).SourceEdge ↦ x.1.2) he
  simpa only [armSheetEdge_sheet] using this)

/-- **The tip of a hairpin is a passage**: when the two arms of the hairpin survive, they are the
only surviving source edges at the tip. -/
theorem nonDanglingValency_tip (hconn : (glueDatum D π).Connected) (k : Fin 3)
    (hK : ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (π.sheet k).castSucc))
    (hΛ : ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (Fin.last d))) :
    nonDanglingValency (glueDatum D π)
      ((glueDatum D π).sourceEndpoint (π.tipTarget k) (π.sheet k).castSucc) = 2 := by
  have hKΛ : (π.sheet k).castSucc ≠ Fin.last d := (Fin.castSucc_lt_last _).ne
  unfold nonDanglingValency
  rw [Finset.card_eq_two]
  refine ⟨armSheetEdge D π k (π.sheet k).castSucc, armSheetEdge D π k (Fin.last d),
    armSheetEdge_ne D π k hKΛ, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hnd, hinc⟩
    obtain ⟨hx1, -⟩ := (incident_tip_iff D π k _ x).mp hinc
    rw [eq_armSheetEdge D π x hx1] at hnd ⊢
    by_cases h1 : x.1.2 = (π.sheet k).castSucc
    · left; rw [h1]
    by_cases h2 : x.1.2 = Fin.last d
    · right; rw [h2]
    exact absurd (isDangling_armSheetEdge D π hconn k _ h1 h2) hnd
  · rintro (rfl | rfl)
    · refine ⟨hK, (incident_tip_iff D π k _ _).mpr ⟨rfl, ?_⟩⟩
      rw [armSheetEdge_sheet]
      exact (SheetPartition.rel_iff _ _ _).mpr rfl
    · refine ⟨hΛ, (incident_tip_iff D π k _ _).mpr ⟨rfl, ?_⟩⟩
      rw [armSheetEdge_sheet]
      exact pair_rel_last π k

/-- The two arms of a hairpin lie on one stable path. -/
theorem stablePath_hairpin (hconn : (glueDatum D π).Connected) (k : Fin 3)
    (hK : ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (π.sheet k).castSucc))
    (hΛ : ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (Fin.last d))) :
    NonDanglingEdge.stablePath (⟨_, hK⟩ : NonDanglingEdge (glueDatum D π)) =
      NonDanglingEdge.stablePath (⟨_, hΛ⟩ : NonDanglingEdge (glueDatum D π)) := by
  refine stablePath_eq_of_consecutive ⟨fun h ↦ armSheetEdge_ne D π k
    (Fin.castSucc_lt_last (π.sheet k)).ne (congrArg Subtype.val h), _, ?_, ?_,
    nonDanglingValency_tip D π hconn k hK hΛ⟩
  · exact (incident_tip_iff D π k _ _).mpr ⟨rfl, by
      rw [armSheetEdge_sheet]; exact (SheetPartition.rel_iff _ _ _).mpr rfl⟩
  · exact (incident_tip_iff D π k _ _).mpr ⟨rfl, by
      rw [armSheetEdge_sheet]; exact pair_rel_last π k⟩

theorem sourceEdgeIndex_armSheetEdge (k : Fin 3) (j : Fin (d + 1)) :
    (glueDatum D π).sourceEdgeIndex (armSheetEdge D π k j) = 1 := by
  rw [armSheetEdge, GluingDatum.sourceEdgeIndex_sourceEdge, glueDatum_edgePartition_armEdge]
  simp [SheetPartition.blockCard, SheetPartition.block, SheetPartition.discrete, Finset.filter_eq]

/-- **The column of an arm** in any labelling: `2` in the row of the hairpin, `0` elsewhere. -/
theorem matrix_armColumn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StableLengthMatrixLabelling (glueDatum D π) ι) (hconn : (glueDatum D π).Connected)
    (k : Fin 3)
    (hK : ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (π.sheet k).castSucc))
    (hΛ : ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (Fin.last d))) (r : ι) :
    GluingDatum.LengthMatrixPresentation.matrix L.presentation r (L.targetEdge.symm (π.armEdge k)) =
      if r = L.row (NonDanglingEdge.stablePath (⟨_, hK⟩ : NonDanglingEdge (glueDatum D π))) then 2 else 0 := by
  classical
  have hKΛ : (π.sheet k).castSucc ≠ Fin.last d := (Fin.castSucc_lt_last _).ne
  have hmem : ∀ x, x ∈ LeafFibre.rowFibre L r (π.armEdge k) ↔
      (x = armSheetEdge D π k (π.sheet k).castSucc ∨ x = armSheetEdge D π k (Fin.last d)) ∧
        r = L.row (NonDanglingEdge.stablePath (⟨_, hK⟩ : NonDanglingEdge (glueDatum D π))) := by
    intro x
    rw [LeafFibre.mem_rowFibre]
    constructor
    · rintro ⟨⟨hnd, hrow⟩, hx1⟩
      have hx := eq_armSheetEdge D π x hx1
      by_cases h1 : x.1.2 = (π.sheet k).castSucc
      · rw [h1] at hx
        subst hx
        exact ⟨Or.inl rfl, hrow.symm⟩
      by_cases h2 : x.1.2 = Fin.last d
      · rw [h2] at hx
        subst hx
        refine ⟨Or.inr rfl, ?_⟩
        rw [stablePath_hairpin D π hconn k hK hΛ]
        exact hrow.symm
      exact absurd (hx ▸ isDangling_armSheetEdge D π hconn k _ h1 h2) hnd
    · rintro ⟨rfl | rfl, rfl⟩
      · exact ⟨⟨hK, rfl⟩, rfl⟩
      · refine ⟨⟨hΛ, ?_⟩, rfl⟩
        rw [stablePath_hairpin D π hconn k hK hΛ]
  rw [LeafFibre.matrix_eq_sum_fibre]
  split_ifs with hr
  · have hset : LeafFibre.rowFibre L r (π.armEdge k) =
        {armSheetEdge D π k (π.sheet k).castSucc, armSheetEdge D π k (Fin.last d)} := by
      ext x
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hr⟩⟩
    rw [hset, Finset.sum_pair (armSheetEdge_ne D π k hKΛ), sourceEdgeIndex_armSheetEdge,
      sourceEdgeIndex_armSheetEdge]
    norm_num
  · refine Finset.sum_eq_zero fun x hx ↦ absurd ((hmem x).mp hx).2 hr

end Arms

/-! ### The hairpins lie on cycles -/

section Hairpin

open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingSideStructure (ReachP mem_side_of_reachP)

/-- **An edge on a cycle is not dangling.** If each end of `x` can be reached from the other end
without stepping onto it, arriving through a neighbour other than the start, then no cut has `x`
as its only crossing edge (`DanglingSideStructure.mem_side_of_reachP`). -/
theorem not_isDangling_of_returns {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (x : E.SourceEdge)
    {u' v' : E.SourceVertex}
    (hu : 0 < num_edges E.sourceGraph u' (E.sourceEnds x).2) (hune : u' ≠ (E.sourceEnds x).1)
    (hur : ReachP E.sourceGraph (fun z ↦ z ≠ (E.sourceEnds x).2) (E.sourceEnds x).1 u')
    (hv : 0 < num_edges E.sourceGraph v' (E.sourceEnds x).1) (hvne : v' ≠ (E.sourceEnds x).2)
    (hvr : ReachP E.sourceGraph (fun z ↦ z ≠ (E.sourceEnds x).1) (E.sourceEnds x).2 v') :
    ¬ IsDangling E x := by
  intro h
  unfold IsDangling at h
  rcases h with h | h <;> obtain ⟨cut⟩ := h
  · have hmem := mem_side_of_reachP cut cut.left_mem hur
    have hc := cut.cross_num_edges u' _ hmem cut.right_not_mem
    rw [if_neg (fun h ↦ hune h.1)] at hc
    omega
  · have hmem := mem_side_of_reachP cut cut.left_mem hvr
    have hc := cut.cross_num_edges v' _ hmem cut.right_not_mem
    rw [if_neg (fun h ↦ hvne h.1)] at hc
    omega

theorem rtg_of_walk {V W : Type*} {H : SimpleGraph V} (R : W → W → Prop) (f : V → W)
    (hf : ∀ a b, H.Adj a b → R (f a) (f b)) {a b : V} (w : H.Walk a b) :
    Relation.ReflTransGen R (f a) (f b) := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons h _ ih => exact Relation.ReflTransGen.head (hf _ _ h) ih

theorem exists_adj_reach_avoid_aux {V : Type*} {H : SimpleGraph V} {a : V} :
    ∀ {u b : V} (_ : H.Walk u b), u ≠ b →
      Relation.ReflTransGen (fun u v ↦ H.Adj u v ∧ v ≠ b) a u →
      ∃ b', H.Adj b' b ∧ Relation.ReflTransGen (fun u v ↦ H.Adj u v ∧ v ≠ b) a b' := by
  intro u b w
  induction w with
  | nil => intro hne; exact absurd rfl hne
  | @cons u v c huv p ih =>
    intro _ hr
    by_cases hv : v = c
    · subst hv
      exact ⟨u, huv, hr⟩
    · exact ih hv (Relation.ReflTransGen.tail hr ⟨huv, hv⟩)

/-- **The first arrival at `b`**: a walk from `a ≠ b` to `b` reaches a neighbour of `b` without
stepping onto `b`. -/
theorem exists_adj_reach_avoid {V : Type*} {H : SimpleGraph V} {a b : V} (w : H.Walk a b)
    (hab : a ≠ b) :
    ∃ b', H.Adj b' b ∧ Relation.ReflTransGen (fun u v ↦ H.Adj u v ∧ v ≠ b) a b' :=
  exists_adj_reach_avoid_aux w hab Relation.ReflTransGen.refl

theorem reachP_of_walk {V : Type*} {H : SimpleGraph V} {X : CFGraph} (f : V → X.V)
    (P : X.V → Prop) (hadj : ∀ u v, H.Adj u v → 0 < num_edges X (f u) (f v))
    (hP : ∀ v, P (f v)) {a c : V} (w : H.Walk a c) : ReachP X P (f a) (f c) :=
  rtg_of_walk _ f (fun u v h ↦ ⟨hadj u v h, hP v⟩) w

theorem reachP_of_rtg_avoid {V : Type*} {H : SimpleGraph V} {X : CFGraph} (f : V → X.V)
    {b : V} (hadj : ∀ u v, H.Adj u v → 0 < num_edges X (f u) (f v))
    (hinj : ∀ v, v ≠ b → f v ≠ f b) {a c : V}
    (h : Relation.ReflTransGen (fun u v ↦ H.Adj u v ∧ v ≠ b) a c) :
    ReachP X (fun z ↦ z ≠ f b) (f a) (f c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.tail ih ⟨hadj _ _ hst.1, hinj _ hst.2⟩

theorem reachP_single {X : CFGraph} {P : X.V → Prop} {a b : X.V} (h : 0 < num_edges X a b)
    (hb : P b) : ReachP X P a b :=
  Relation.ReflTransGen.single ⟨h, hb⟩

theorem num_edges_pos_symm {X : CFGraph} {a b : X.V} (h : 0 < num_edges X a b) :
    0 < num_edges X b a := by
  rwa [num_edges_symmetric]

namespace Placement

variable (π : Placement T d)

theorem lift₃_injective : Function.Injective π.lift₃ := fun _ _ h ↦
  leafOld_injective _ _ (leafOld_injective _ _ (leafOld_injective _ _ h))

theorem lift₃_ne_tipTarget (v : π.T₃.V) (k : Fin 3) : π.lift₃ v ≠ π.tipTarget k := by
  match k with
  | 0 => exact fun h ↦ leafTip_ne_leafOld _ _ _ (leafOld_injective _ _ (leafOld_injective _ _ h)).symm
  | 1 => exact fun h ↦ leafTip_ne_leafOld _ _ _ (leafOld_injective _ _ h).symm
  | 2 => exact fun h ↦ leafTip_ne_leafOld _ _ _ h.symm

theorem tipTarget_injective : Function.Injective π.tipTarget := by
  intro a b h
  fin_cases a <;> fin_cases b
  all_goals first
    | rfl
    | exfalso
      simp only [Placement.tipTarget, leafOld, leafTip] at h
      cases h

theorem markVertex₃_injective : Function.Injective π.markVertex₃ := by
  intro a b h
  fin_cases a <;> fin_cases b
  all_goals first
    | rfl
    | exfalso
      simp only [Placement.markVertex₃, subdivOld, subdivFresh] at h
      cases h

end Placement

variable (D : GluingDatum T d) (π : Placement T d)

/-- `D` refined at the three marks. -/
abbrev refine₃ : GluingDatum π.T₃ d :=
  refineDatum (refineDatum (refineDatum D π.edge₀) π.edge₁) π.edge₂

/-- A source vertex of the refined datum, in an old sheet of the glued source. -/
def oldVertex₃ (x : (refine₃ D π).SourceVertex) : (glueDatum D π).SourceVertex :=
  (glueDatum D π).sourceEndpoint (π.lift₃ x.1.1) x.1.2.castSucc

/-- A target vertex of `T₃`, in the new sheet of the glued source. -/
def newVertex (v : π.T₃.V) : (glueDatum D π).SourceVertex :=
  (glueDatum D π).sourceEndpoint (π.lift₃ v) (Fin.last d)

theorem oldVertex₃_sourceEndpoint (w : π.T₃.V) (i : Fin d) :
    oldVertex₃ D π ((refine₃ D π).sourceEndpoint w i) =
      (glueDatum D π).sourceEndpoint (π.lift₃ w) i.castSucc := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show (SheetOps.extendNew ((refine₃ D π).vertexPartition w)).repr
      ((((refine₃ D π).vertexPartition w).repr i).castSucc) =
    (SheetOps.extendNew ((refine₃ D π).vertexPartition w)).repr i.castSucc
  simp only [SheetOps.extendNew_repr_castSucc, SheetPartition.repr_idem]

theorem adj_lift₃ (e : π.T₃.edges) (j : Fin (d + 1)) :
    (srcGraph (glueDatum D π)).Adj
      ((glueDatum D π).sourceEndpoint (π.lift₃ (e : π.T₃.V × π.T₃.V).1) j)
      ((glueDatum D π).sourceEndpoint (π.lift₃ (e : π.T₃.V × π.T₃.V).2) j) := by
  have h := adj_sourceEndpoint (glueDatum D π) (π.liftE₃ e) j
  rw [π.liftE₃_ends] at h
  exact h

theorem adj_arm (k : Fin 3) (j : Fin (d + 1)) :
    (srcGraph (glueDatum D π)).Adj
      ((glueDatum D π).sourceEndpoint (π.lift₃ (π.markVertex₃ k)) j)
      ((glueDatum D π).sourceEndpoint (π.tipTarget k) j) := by
  have h := adj_sourceEndpoint (glueDatum D π) (π.armEdge k) j
  rw [π.armEdge_ends] at h
  exact h

theorem adj_oldVertex₃ {a b : (refine₃ D π).SourceVertex} (h : (srcGraph (refine₃ D π)).Adj a b) :
    (srcGraph (glueDatum D π)).Adj (oldVertex₃ D π a) (oldVertex₃ D π b) := by
  obtain ⟨e, i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_of_adj _ h
  · rw [oldVertex₃_sourceEndpoint, oldVertex₃_sourceEndpoint]
    exact adj_lift₃ D π e _
  · rw [oldVertex₃_sourceEndpoint, oldVertex₃_sourceEndpoint]
    exact (adj_lift₃ D π e _).symm

theorem adj_newVertex {v w : π.T₃.V} (h : (Utilities.underlyingSimpleGraph π.T₃).Adj v w) :
    (srcGraph (glueDatum D π)).Adj (newVertex D π v) (newVertex D π w) := by
  obtain ⟨pair, hmem, hpair⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos _ v w h
  obtain ⟨e, he⟩ := exists_occurrence_of_mem_edges hmem
  have h' := adj_lift₃ D π e (Fin.last d)
  rw [he] at h'
  rcases hpair with rfl | rfl
  · exact h'
  · exact h'.symm

theorem tip_last_eq (k : Fin 3) :
    (glueDatum D π).sourceEndpoint (π.tipTarget k) (Fin.last d) =
      (glueDatum D π).sourceEndpoint (π.tipTarget k) (π.sheet k).castSucc := by
  apply GluingDatum.sourceEndpoint_congr
  rw [glueDatum_vertexPartition_tipTarget]
  exact pair_rel_last π k

theorem oldVertex₃_injective : Function.Injective (oldVertex₃ D π) := by
  rintro ⟨⟨v, i⟩, hi⟩ ⟨⟨w, j⟩, hj⟩ h
  have h1 : π.lift₃ v = π.lift₃ w := congrArg (fun z ↦ z.1.1) h
  obtain rfl := π.lift₃_injective h1
  have h2 := congrArg (fun z : (glueDatum D π).SourceVertex ↦ z.1.2) h
  change (SheetOps.extendNew ((refine₃ D π).vertexPartition v)).repr i.castSucc =
    (SheetOps.extendNew ((refine₃ D π).vertexPartition v)).repr j.castSucc at h2
  simp only [SheetOps.extendNew_repr_castSucc, Fin.castSucc_inj] at h2
  have hij : i = j := hi.symm.trans (h2.trans hj)
  subst hij
  rfl

theorem newVertex_injective : Function.Injective (newVertex D π) := fun _ _ h ↦
  π.lift₃_injective (congrArg (fun z : (glueDatum D π).SourceVertex ↦ z.1.1) h)

theorem oldVertex₃_ne_newVertex (x : (refine₃ D π).SourceVertex) (v : π.T₃.V) :
    oldVertex₃ D π x ≠ newVertex D π v := by
  intro h
  have h2 := congrArg (fun z : (glueDatum D π).SourceVertex ↦ z.1.2) h
  change (SheetOps.extendNew ((refine₃ D π).vertexPartition x.1.1)).repr x.1.2.castSucc =
    (SheetOps.extendNew ((refine₃ D π).vertexPartition v)).repr (Fin.last d) at h2
  simp only [SheetOps.extendNew_repr_castSucc, SheetOps.extendNew_repr_last] at h2
  exact (Fin.castSucc_lt_last _).ne h2

theorem oldVertex₃_ne_tip (x : (refine₃ D π).SourceVertex) (k : Fin 3) (j : Fin (d + 1)) :
    oldVertex₃ D π x ≠ (glueDatum D π).sourceEndpoint (π.tipTarget k) j := fun h ↦
  π.lift₃_ne_tipTarget _ k (congrArg (fun z : (glueDatum D π).SourceVertex ↦ z.1.1) h)

theorem newVertex_ne_tip (v : π.T₃.V) (k : Fin 3) (j : Fin (d + 1)) :
    newVertex D π v ≠ (glueDatum D π).sourceEndpoint (π.tipTarget k) j := fun h ↦
  π.lift₃_ne_tipTarget _ k (congrArg (fun z : (glueDatum D π).SourceVertex ↦ z.1.1) h)

theorem tip_ne_tip {j k : Fin 3} (hjk : j ≠ k) (a b : Fin (d + 1)) :
    (glueDatum D π).sourceEndpoint (π.tipTarget j) a ≠
      (glueDatum D π).sourceEndpoint (π.tipTarget k) b := fun h ↦
  hjk (π.tipTarget_injective (congrArg (fun z : (glueDatum D π).SourceVertex ↦ z.1.1) h))

/-- **The hairpin survives** (§3.3): the arm at mark `k`, in the sheet of the mark and in
the new sheet, lies on a cycle of the glued source (up the hairpin at `k`, along the new sheet to
another mark `j`, down the hairpin there and back along the old sheets), so it is not dangling. -/
theorem hairpin_not_isDangling (hD : D.Connected) (hT : graph_connected T) (k : Fin 3) :
    ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (π.sheet k).castSucc) ∧
      ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (Fin.last d)) := by
  classical
  let G := glueDatum D π
  -- another mark
  obtain ⟨j, hjk⟩ : ∃ j : Fin 3, j ≠ k := ⟨if k = 0 then 1 else 0, by split_ifs <;> omega⟩
  have hD₃ : (refine₃ D π).Connected :=
    refineDatum_connected _ _ (refineDatum_connected _ _ (refineDatum_connected _ _ hD))
  have hD₃c := (Utilities.graph_connected_iff_underlyingSimpleGraph_connected _).mp hD₃
  have hT₃c := (Utilities.graph_connected_iff_underlyingSimpleGraph_connected _).mp
    (π.T₃_connected hT)
  let m₃ := (refine₃ D π).sourceEndpoint (π.markVertex₃ k) (π.sheet k)
  let mj₃ := (refine₃ D π).sourceEndpoint (π.markVertex₃ j) (π.sheet j)
  let m := oldVertex₃ D π m₃
  let mj := oldVertex₃ D π mj₃
  let τ := G.sourceEndpoint (π.tipTarget k) (π.sheet k).castSucc
  let τj := G.sourceEndpoint (π.tipTarget j) (π.sheet j).castSucc
  let n := newVertex D π (π.markVertex₃ k)
  let nj := newVertex D π (π.markVertex₃ j)
  have hm : m = G.sourceEndpoint (π.lift₃ (π.markVertex₃ k)) (π.sheet k).castSucc :=
    oldVertex₃_sourceEndpoint D π _ _
  have hmj : mj = G.sourceEndpoint (π.lift₃ (π.markVertex₃ j)) (π.sheet j).castSucc :=
    oldVertex₃_sourceEndpoint D π _ _
  -- the four arms
  have A1 : 0 < num_edges G.sourceGraph m τ := by rw [hm]; exact adj_arm D π k _
  have A2 : 0 < num_edges G.sourceGraph n τ := by
    have h := adj_arm D π k (Fin.last d)
    rw [tip_last_eq] at h
    exact h
  have A3 : 0 < num_edges G.sourceGraph mj τj := by rw [hmj]; exact adj_arm D π j _
  have A4 : 0 < num_edges G.sourceGraph nj τj := by
    have h := adj_arm D π j (Fin.last d)
    rw [tip_last_eq] at h
    exact h
  have hm₃ : mj₃ ≠ m₃ := fun h ↦ hjk (π.markVertex₃_injective
    (congrArg (fun z : (refine₃ D π).SourceVertex ↦ z.1.1) h))
  have hmv : π.markVertex₃ j ≠ π.markVertex₃ k := fun h ↦ hjk (π.markVertex₃_injective h)
  -- walks in the old sheets and in the new sheet
  have WO : ∀ (z : G.SourceVertex), (∀ x, oldVertex₃ D π x ≠ z) → ∀ a b,
      ReachP G.sourceGraph (fun w ↦ w ≠ z) (oldVertex₃ D π a) (oldVertex₃ D π b) := by
    intro z hz a b
    obtain ⟨w⟩ := hD₃c.preconnected a b
    exact reachP_of_walk _ _ (fun u v h ↦ adj_oldVertex₃ D π h) hz w
  have WN : ∀ (z : G.SourceVertex), (∀ v, newVertex D π v ≠ z) → ∀ a b,
      ReachP G.sourceGraph (fun w ↦ w ≠ z) (newVertex D π a) (newVertex D π b) := by
    intro z hz a b
    obtain ⟨w⟩ := hT₃c.preconnected a b
    exact reachP_of_walk _ _ (fun u v h ↦ adj_newVertex D π h) hz w
  -- the two arms of the hairpin
  have hendsK : G.sourceEnds (armSheetEdge D π k (π.sheet k).castSucc) = (m, τ) := by
    refine Prod.ext ?_ ?_
    · rw [armSheetEdge, sourceEnds_sourceEdge_fst, π.armEdge_ends, hm]; rfl
    · rw [armSheetEdge, sourceEnds_sourceEdge_snd, π.armEdge_ends]
  have hendsΛ : G.sourceEnds (armSheetEdge D π k (Fin.last d)) = (n, τ) := by
    refine Prod.ext ?_ ?_
    · rw [armSheetEdge, sourceEnds_sourceEdge_fst, π.armEdge_ends]; rfl
    · rw [armSheetEdge, sourceEnds_sourceEdge_snd, π.armEdge_ends, tip_last_eq]
  have hnm : n ≠ m := (oldVertex₃_ne_newVertex D π _ _).symm
  constructor
  · -- the arm in the sheet of the mark: ends `m`, `τ`
    obtain ⟨m₃', hadj', hreach'⟩ := exists_adj_reach_avoid
      (Classical.choice (hD₃c.preconnected mj₃ m₃)) hm₃
    refine not_isDangling_of_returns G _ (u' := n) (v' := oldVertex₃ D π m₃') ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [hendsK]
    · exact A2
    · exact hnm
    · -- `m ⇝ mj → τj → nj ⇝ n`, avoiding `τ`
      refine ((WO τ (fun x ↦ oldVertex₃_ne_tip D π x k _) m₃ mj₃).trans
        (reachP_single A3 (tip_ne_tip D π hjk _ _))).trans ?_
      refine (reachP_single (num_edges_pos_symm A4) (newVertex_ne_tip D π _ k _)).trans ?_
      exact WN τ (fun v ↦ newVertex_ne_tip D π v k _) (π.markVertex₃ j) (π.markVertex₃ k)
    · exact adj_oldVertex₃ D π hadj'
    · exact oldVertex₃_ne_tip D π _ k _
    · -- `τ → n ⇝ nj → τj → mj ⇝ m₃'`, avoiding `m`
      refine (reachP_single (num_edges_pos_symm A2) hnm).trans ?_
      refine (WN m (fun v ↦ (oldVertex₃_ne_newVertex D π _ v).symm) (π.markVertex₃ k)
        (π.markVertex₃ j)).trans ?_
      refine (reachP_single A4 (oldVertex₃_ne_tip D π _ j _).symm).trans ?_
      refine (reachP_single (num_edges_pos_symm A3)
        (fun h ↦ hm₃ (oldVertex₃_injective D π h))).trans ?_
      exact reachP_of_rtg_avoid _ (fun u v h ↦ adj_oldVertex₃ D π h)
        (fun v hv h ↦ hv (oldVertex₃_injective D π h)) hreach'
  · -- the arm in the new sheet: ends `n`, `τ`
    obtain ⟨w', hadj', hreach'⟩ := exists_adj_reach_avoid
      (Classical.choice (hT₃c.preconnected (π.markVertex₃ j) (π.markVertex₃ k))) hmv
    refine not_isDangling_of_returns G _ (u' := m) (v' := newVertex D π w') ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [hendsΛ]
    · exact A1
    · exact hnm.symm
    · -- `n ⇝ nj → τj → mj ⇝ m`, avoiding `τ`
      refine ((WN τ (fun v ↦ newVertex_ne_tip D π v k _) (π.markVertex₃ k) (π.markVertex₃ j)).trans
        (reachP_single A4 (tip_ne_tip D π hjk _ _))).trans ?_
      refine (reachP_single (num_edges_pos_symm A3) (oldVertex₃_ne_tip D π _ k _)).trans ?_
      exact WO τ (fun x ↦ oldVertex₃_ne_tip D π x k _) mj₃ m₃
    · exact adj_newVertex D π hadj'
    · exact newVertex_ne_tip D π _ k _
    · -- `τ → m ⇝ mj → τj → nj ⇝ w'`, avoiding `n`
      refine (reachP_single (num_edges_pos_symm A1) hnm.symm).trans ?_
      refine (WO n (fun x ↦ oldVertex₃_ne_newVertex D π x _) m₃ mj₃).trans ?_
      refine (reachP_single A3 (newVertex_ne_tip D π _ j _).symm).trans ?_
      refine (reachP_single (num_edges_pos_symm A4)
        (fun h ↦ hmv (newVertex_injective D π h))).trans ?_
      exact reachP_of_rtg_avoid _ (fun u v h ↦ adj_newVertex D π h)
        (fun v hv h ↦ hv (newVertex_injective D π h)) hreach'

end Hairpin

/-! ## The dangling dictionary

Which source edges of a datum are dangling is decided by two facts, both about an arbitrary
datum `E`:

* **the witness lemma** (`not_isDangling_of_witness`): if a property `W` of source edges is such
  that no source vertex has exactly one incident `W`-edge, then no `W`-edge is dangling. A
  dangling `W`-edge has a genus-zero side; at its inner end another `W`-edge leaves, and it is
  dangling along a strictly smaller side (`DanglingDescent.danglingSideDescent`); the sides
  cannot shrink for ever.
* **maximality** (`NonDanglingValency.nonDanglingValency_ne_one`): the non-dangling edges of a
  connected datum are themselves such a property.

So the non-dangling edges are the largest edge set without a vertex of valency one, and the
dictionary of a construction is proved by exhibiting a witness on one side and reading the
non-dangling edges of the other side as a witness. -/

section DanglingDictionary

open DraismaVargas.LocalCases.W4StableSource

/-- The number of source edges with property `W` at a source vertex. -/
noncomputable def wCount {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (W : E.SourceEdge → Prop)
    (v : E.SourceVertex) : ℕ := by
  classical
  exact (Finset.univ.filter fun e ↦ W e ∧ Incident E e v).card

theorem nonDanglingValency_eq_wCount {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    (v : E.SourceVertex) :
    nonDanglingValency E v = wCount E (fun e ↦ ¬ IsDangling E e) v := by
  classical
  unfold nonDanglingValency wCount
  congr 1
  ext e
  simp

theorem wCount_congr {S : CFGraph} {k : ℕ} (E : GluingDatum S k) {W W' : E.SourceEdge → Prop}
    (v : E.SourceVertex) (h : ∀ e, Incident E e v → (W e ↔ W' e)) :
    wCount E W v = wCount E W' v := by
  classical
  unfold wCount
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨hw, hi⟩ ↦ ⟨(h e hi).mp hw, hi⟩, fun ⟨hw, hi⟩ ↦ ⟨(h e hi).mpr hw, hi⟩⟩

theorem wCount_le_of_imp {S : CFGraph} {k : ℕ} (E : GluingDatum S k) {W W' : E.SourceEdge → Prop}
    (v : E.SourceVertex) (h : ∀ e, Incident E e v → W e → W' e) :
    wCount E W v ≤ wCount E W' v := by
  classical
  unfold wCount
  refine Finset.card_le_card fun e he ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨h e he.2 he.1, he.2⟩

/-- **The witness lemma.** No edge of a property without a vertex of valency one is dangling. -/
theorem not_isDangling_of_witness {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    (W : E.SourceEdge → Prop) (hW : ∀ v, wCount E W v ≠ 1) {e : E.SourceEdge} (he : W e) :
    ¬ IsDangling E e := by
  classical
  have key : ∀ (n : ℕ) (inner outer : E.SourceVertex)
      (cut : DanglingSide E.sourceGraph inner outer), cut.side.card = n →
      ∀ e, W e → (E.sourceEnds e = (inner, outer) ∨ E.sourceEnds e = (outer, inner)) → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro inner outer cut hn e he hEnds
      have hInc : Incident E e inner := by
        rcases hEnds with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      obtain ⟨f, hfW, hfInc, hfe⟩ : ∃ f, W f ∧ Incident E f inner ∧ f ≠ e := by
        by_contra hno
        push Not at hno
        apply hW inner
        unfold wCount
        rw [Finset.card_eq_one]
        refine ⟨e, ?_⟩
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h ↦ hno f h.1 h.2, fun h ↦ h ▸ ⟨he, hInc⟩⟩
      obtain ⟨first, second, smaller, hfEnds, hlt⟩ :=
        DraismaVargas.LocalCases.DanglingDescent.danglingSideDescent E inner outer cut e f hEnds
          hfInc hfe
      exact ih _ (hn ▸ hlt) first second smaller rfl f hfW hfEnds
  intro hD
  rcases hD with ⟨⟨cut⟩⟩ | ⟨⟨cut⟩⟩
  · exact key _ _ _ cut rfl e he (Or.inl rfl)
  · exact key _ _ _ cut rfl e he (Or.inr rfl)

/-- Maximality, in the form of the witness lemma: in a connected datum no vertex has exactly one
non-dangling edge. -/
theorem wCount_nonDangling_ne_one {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    (hE : E.Connected) (v : E.SourceVertex) :
    wCount E (fun e ↦ ¬ IsDangling E e) v ≠ 1 := by
  rw [← nonDanglingValency_eq_wCount]
  exact DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one E hE v

/-! ### A refinement has the dangling edges of the datum it refines

`refineDatum D t` subdivides every source edge over `t` at a fresh source vertex of the same
block. Its source edges have parents in `D` (`parentSE`), its old source vertices are those of
`D` (`oldSV`) and its fresh ones are the blocks of `t` (`freshSV`). The incident edges at an old
vertex are, through `parentSE`, those of `D` (`wCount_oldSV`); a fresh vertex has exactly the
two halves (`incident_freshSV_iff`). So a source edge is dangling exactly when its parent is
(`isDangling_refineDatum_iff`): the witnesses `¬ IsDangling D ∘ parentSE` and "some piece
survives" go both ways. -/

/-- The old target edge under a target edge of the subdivision at `t`. -/
def parentT (t : T.edges) (ε : (subdivTarget T t).edges) : T.edges :=
  Option.elim ((subdivOcc T t).symm ε) t id

@[simp] theorem parentT_none (t : T.edges) : parentT t (subdivOcc T t none) = t := by
  simp [parentT]

@[simp] theorem parentT_some (t e : T.edges) : parentT t (subdivOcc T t (some e)) = e := by
  simp [parentT]

theorem parentT_eq_iff (t : T.edges) (ε : (subdivTarget T t).edges) (e : T.edges) :
    parentT t ε = e ↔ ε = subdivOcc T t (some e) ∨ (e = t ∧ ε = subdivOcc T t none) := by
  obtain ⟨o, rfl⟩ := (subdivOcc T t).surjective ε
  cases o with
  | none =>
    rw [parentT_none]
    constructor
    · rintro rfl; exact Or.inr ⟨rfl, rfl⟩
    · rintro (h | ⟨rfl, -⟩)
      · exact absurd ((subdivOcc T t).injective h) (by simp)
      · rfl
  | some e' =>
    rw [parentT_some]
    constructor
    · rintro rfl; exact Or.inl rfl
    · rintro (h | ⟨-, h⟩)
      · exact Option.some_injective _ ((subdivOcc T t).injective h)
      · exact absurd ((subdivOcc T t).injective h) (by simp)

theorem refineDatum_edgePartition (D : GluingDatum T d) (t : T.edges)
    (ε : (subdivTarget T t).edges) :
    (refineDatum D t).edgePartition ε = D.edgePartition (parentT t ε) := by
  obtain ⟨o, rfl⟩ := (subdivOcc T t).surjective ε
  cases o with
  | none => rw [refineDatum_edgePartition_none, parentT_none]
  | some e => rw [refineDatum_edgePartition_some, parentT_some]

/-- The piece of the old target edge `e` at the old vertex `w`: the second half of `t` if
`w` is its second end, and the (first half of the) edge itself otherwise. -/
noncomputable def pieceT (t : T.edges) (w : T.V) (e : T.edges) : (subdivTarget T t).edges := by
  classical
  exact if e = t ∧ (t : T.V × T.V).2 = w then subdivOcc T t none else subdivOcc T t (some e)

@[simp] theorem parentT_pieceT (t : T.edges) (w : T.V) (e : T.edges) :
    parentT t (pieceT t w e) = e := by
  unfold pieceT
  split_ifs with h
  · rw [parentT_none, h.1]
  · rw [parentT_some]

theorem subdivOld_eq_iff (t : T.edges) (v w : T.V) : subdivOld T t v = subdivOld T t w ↔ v = w :=
  (subdivOld_injective T t).eq_iff

/-- **The target edges at an old vertex** of a subdivision are the pieces, at that vertex, of
the old edges there. -/
theorem mem_incidentEdges_subdivOld (t : T.edges) (w : T.V) (ε : (subdivTarget T t).edges) :
    ε ∈ GluingDatum.incidentEdges (subdivOld T t w) ↔
      parentT t ε ∈ GluingDatum.incidentEdges w ∧ ε = pieceT t w (parentT t ε) := by
  classical
  have hne := fst_ne_snd t
  obtain ⟨o, rfl⟩ := (subdivOcc T t).surjective ε
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  cases o with
  | none =>
    rw [subdivOcc_none, parentT_none]
    simp only [pieceT, true_and, subdivOld_eq_iff]
    constructor
    · rintro (h | h)
      · exact ⟨Or.inr h, by rw [if_pos h]⟩
      · exact absurd h (subdivFresh_ne_subdivOld T t w)
    · rintro ⟨-, h⟩
      by_cases h2 : (t : T.V × T.V).2 = w
      · exact Or.inl h2
      · rw [if_neg h2] at h
        exact absurd ((subdivOcc T t).injective h) (by simp)
  | some e =>
    rw [parentT_some]
    by_cases het : e = t
    · subst het
      rw [subdivOcc_some_self]
      simp only [pieceT, true_and, subdivOld_eq_iff]
      constructor
      · rintro (h | h)
        · have h2 : (e : T.V × T.V).2 ≠ w := fun h2 ↦ hne (h.trans h2.symm)
          exact ⟨Or.inl h, by rw [if_neg h2]⟩
        · exact absurd h (subdivFresh_ne_subdivOld T e w)
      · rintro ⟨h1, h⟩
        by_cases h2 : (e : T.V × T.V).2 = w
        · rw [if_pos h2] at h
          exact absurd ((subdivOcc T e).injective h) (by simp)
        · exact Or.inl (h1.resolve_right h2)
    · rw [subdivOcc_some_of_ne T het]
      simp only [pieceT, het, false_and, if_false, subdivOld_eq_iff, and_true]

/-- The target edges at the fresh vertex are the two halves of `t`. -/
theorem mem_incidentEdges_subdivFresh (t : T.edges) (ε : (subdivTarget T t).edges) :
    ε ∈ GluingDatum.incidentEdges (subdivFresh T t) ↔ parentT t ε = t := by
  classical
  obtain ⟨o, rfl⟩ := (subdivOcc T t).surjective ε
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  cases o with
  | none =>
    rw [subdivOcc_none, parentT_none]
    simp
  | some e =>
    rw [parentT_some]
    by_cases het : e = t
    · subst het
      rw [subdivOcc_some_self]
      simp
    · rw [subdivOcc_some_of_ne T het]
      simp only [het, iff_false]
      rintro (h | h) <;> exact subdivFresh_ne_subdivOld T t _ h.symm

namespace Refine

variable (D : GluingDatum T d) (t : T.edges)

/-- The old source edge under a source edge of the refinement. -/
def parentSE (y : (refineDatum D t).SourceEdge) : D.SourceEdge :=
  ⟨(parentT t y.1.1, y.1.2), by
    have h := y.2
    rw [refineDatum_edgePartition] at h
    exact h⟩

theorem parentSE_sourceEdge (ε : (subdivTarget T t).edges) (j : Fin d) :
    parentSE D t ((refineDatum D t).sourceEdge ε j) = D.sourceEdge (parentT t ε) j := by
  apply Subtype.ext
  show (parentT t ε, ((refineDatum D t).edgePartition ε).repr j) =
    (parentT t ε, (D.edgePartition (parentT t ε)).repr j)
  rw [refineDatum_edgePartition]

/-- An old source vertex, in the refinement. -/
def oldSV (x : D.SourceVertex) : (refineDatum D t).SourceVertex :=
  ⟨(subdivOld T t x.1.1, x.1.2), x.2⟩

/-- A fresh source vertex of the refinement: a block of `t`. -/
def freshSV (i : Fin d) (hi : (D.edgePartition t).repr i = i) :
    (refineDatum D t).SourceVertex :=
  ⟨(subdivFresh T t, i), hi⟩

theorem sourceEndpoint_subdivOld (w : T.V) (j : Fin d) :
    (refineDatum D t).sourceEndpoint (subdivOld T t w) j = oldSV D t (D.sourceEndpoint w j) :=
  rfl

theorem sourceEndpoint_subdivFresh (j : Fin d) :
    (refineDatum D t).sourceEndpoint (subdivFresh T t) j =
      freshSV D t ((D.edgePartition t).repr j) ((D.edgePartition t).repr_idem j) :=
  rfl

theorem oldSV_injective : Function.Injective (oldSV D t) := by
  rintro ⟨⟨v, i⟩, hi⟩ ⟨⟨w, j⟩, hj⟩ h
  have h1 := congrArg (fun z : (refineDatum D t).SourceVertex ↦ z.1.1) h
  have h2 := congrArg (fun z : (refineDatum D t).SourceVertex ↦ z.1.2) h
  simp only [oldSV] at h1 h2
  obtain rfl := subdivOld_injective T t h1
  subst h2
  rfl

theorem oldSV_ne_freshSV (x : D.SourceVertex) (i : Fin d) (hi) :
    oldSV D t x ≠ freshSV D t i hi := fun h ↦
  subdivFresh_ne_subdivOld T t _
    (congrArg (fun z : (refineDatum D t).SourceVertex ↦ z.1.1) h).symm

theorem sourceVertex_cases (z : (refineDatum D t).SourceVertex) :
    (∃ x, z = oldSV D t x) ∨ ∃ i hi, z = freshSV D t i hi := by
  obtain ⟨⟨v, i⟩, hi⟩ := z
  rcases v with w | ⟨⟩
  · exact Or.inl ⟨⟨(w, i), hi⟩, rfl⟩
  · exact Or.inr ⟨i, hi, rfl⟩

theorem incident_oldSV_iff (y : (refineDatum D t).SourceEdge) (x : D.SourceVertex) :
    Incident (refineDatum D t) y (oldSV D t x) ↔
      Incident D (parentSE D t y) x ∧ y.1.1 = pieceT t x.1.1 (parentT t y.1.1) := by
  rw [incident_iff_target_mem_and_rel, incident_iff_target_mem_and_rel]
  show y.1.1 ∈ GluingDatum.incidentEdges (subdivOld T t x.1.1) ∧
      (D.vertexPartition x.1.1).Rel x.1.2 y.1.2 ↔
    (parentT t y.1.1 ∈ GluingDatum.incidentEdges x.1.1 ∧
      (D.vertexPartition x.1.1).Rel x.1.2 y.1.2) ∧ _
  rw [mem_incidentEdges_subdivOld]
  tauto

/-- **The count at an old vertex** is the count in `D`, through `parentSE`. -/
theorem wCount_oldSV (Q : D.SourceEdge → Prop) (x : D.SourceVertex) :
    wCount (refineDatum D t) (fun y ↦ Q (parentSE D t y)) (oldSV D t x) = wCount D Q x := by
  classical
  unfold wCount
  refine Finset.card_bij (fun y _ ↦ parentSE D t y) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨hy.1, ((incident_oldSV_iff D t y x).mp hy.2).1⟩
  · intro y₁ hy₁ y₂ hy₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
    have h1 := ((incident_oldSV_iff D t y₁ x).mp hy₁.2).2
    have h2 := ((incident_oldSV_iff D t y₂ x).mp hy₂.2).2
    have hT : parentT t y₁.1.1 = parentT t y₂.1.1 :=
      congrArg (fun f : D.SourceEdge ↦ f.1.1) h
    have hS : y₁.1.2 = y₂.1.2 := congrArg (fun f : D.SourceEdge ↦ f.1.2) h
    apply Subtype.ext
    exact Prod.ext (by rw [h1, h2, hT]) hS
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    let y : (refineDatum D t).SourceEdge := ⟨(pieceT t x.1.1 f.1.1, f.1.2), by
      rw [refineDatum_edgePartition, parentT_pieceT]; exact f.2⟩
    have hy : parentSE D t y = f := Subtype.ext (Prod.ext (parentT_pieceT _ _ _) rfl)
    refine ⟨y, ?_, hy⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hy ▸ hf.1, (incident_oldSV_iff D t y x).mpr ⟨hy ▸ hf.2, ?_⟩⟩
    show pieceT t x.1.1 f.1.1 = pieceT t x.1.1 (parentT t (pieceT t x.1.1 f.1.1))
    rw [parentT_pieceT]

/-- The half of the source edge `(t, i)` at the old second end of `t`. -/
def halfNone (i : Fin d) (hi : (D.edgePartition t).repr i = i) :
    (refineDatum D t).SourceEdge :=
  ⟨(subdivOcc T t none, i), by rw [refineDatum_edgePartition_none]; exact hi⟩

/-- The half of the source edge `(t, i)` at the old first end of `t`. -/
def halfSome (i : Fin d) (hi : (D.edgePartition t).repr i = i) :
    (refineDatum D t).SourceEdge :=
  ⟨(subdivOcc T t (some t), i), by rw [refineDatum_edgePartition_some]; exact hi⟩

theorem halfNone_ne_halfSome (i : Fin d) (hi) : halfNone D t i hi ≠ halfSome D t i hi :=
  fun h ↦ absurd ((subdivOcc T t).injective
    (congrArg (fun y : (refineDatum D t).SourceEdge ↦ y.1.1) h)) (by simp)

theorem parentSE_halfNone (i : Fin d) (hi) : parentSE D t (halfNone D t i hi) = ⟨(t, i), hi⟩ :=
  Subtype.ext (Prod.ext (parentT_none t) rfl)

theorem parentSE_halfSome (i : Fin d) (hi) : parentSE D t (halfSome D t i hi) = ⟨(t, i), hi⟩ :=
  Subtype.ext (Prod.ext (parentT_some t t) rfl)

theorem incident_freshSV_iff (i : Fin d) (hi) (y : (refineDatum D t).SourceEdge) :
    Incident (refineDatum D t) y (freshSV D t i hi) ↔
      y = halfNone D t i hi ∨ y = halfSome D t i hi := by
  rw [incident_iff_target_mem_and_rel]
  show y.1.1 ∈ GluingDatum.incidentEdges (subdivFresh T t) ∧
    (D.edgePartition t).Rel i y.1.2 ↔ _
  rw [mem_incidentEdges_subdivFresh]
  have hy := y.2
  rw [refineDatum_edgePartition] at hy
  constructor
  · rintro ⟨hp, hrel⟩
    have hsheet : y.1.2 = i := by
      rw [SheetPartition.rel_iff] at hrel
      rw [hp] at hy
      rw [← hy, ← hrel, hi]
    rcases (parentT_eq_iff t y.1.1 t).mp hp with h | ⟨-, h⟩
    · right; exact Subtype.ext (Prod.ext h hsheet)
    · left; exact Subtype.ext (Prod.ext h hsheet)
  · rintro (rfl | rfl)
    · exact ⟨parentT_none t, (SheetPartition.rel_iff _ _ _).mpr rfl⟩
    · exact ⟨parentT_some t t, (SheetPartition.rel_iff _ _ _).mpr rfl⟩

open Classical in
/-- **The count at a fresh vertex**: the two halves. -/
theorem wCount_freshSV (W : (refineDatum D t).SourceEdge → Prop) (i : Fin d) (hi) :
    wCount (refineDatum D t) W (freshSV D t i hi) =
      (if W (halfNone D t i hi) then 1 else 0) + (if W (halfSome D t i hi) then 1 else 0) := by
  unfold wCount
  have hset : (Finset.univ.filter fun y ↦ W y ∧ Incident (refineDatum D t) y (freshSV D t i hi)) =
      ({halfNone D t i hi, halfSome D t i hi} : Finset _).filter W := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, incident_freshSV_iff]
    tauto
  rw [hset]
  have hne := halfNone_ne_halfSome D t i hi
  by_cases h1 : W (halfNone D t i hi) <;> by_cases h2 : W (halfSome D t i hi) <;>
    simp [Finset.filter_insert, Finset.filter_singleton, h1, h2, Finset.card_pair hne]

/-- Two source edges with the same parent are equal, or are the two halves at a fresh vertex. -/
theorem eq_or_halves_of_parentSE_eq {y y' : (refineDatum D t).SourceEdge}
    (h : parentSE D t y = parentSE D t y') (hne : y ≠ y') :
    ∃ i hi, (y = halfNone D t i hi ∧ y' = halfSome D t i hi) ∨
      (y = halfSome D t i hi ∧ y' = halfNone D t i hi) := by
  have hT : parentT t y.1.1 = parentT t y'.1.1 := congrArg (fun f : D.SourceEdge ↦ f.1.1) h
  have hS : y.1.2 = y'.1.2 := congrArg (fun f : D.SourceEdge ↦ f.1.2) h
  have hy0 := y.2
  rw [refineDatum_edgePartition] at hy0
  generalize he : parentT t y.1.1 = e at hT hy0
  rcases (parentT_eq_iff t y.1.1 e).mp he with h1 | ⟨h1t, h1⟩ <;>
    rcases (parentT_eq_iff t y'.1.1 e).mp hT.symm with h2 | ⟨h2t, h2⟩
  · exact absurd (Subtype.ext (Prod.ext (h1.trans h2.symm) hS)) hne
  · rw [h2t] at h1 hy0
    exact ⟨y.1.2, hy0, Or.inr ⟨Subtype.ext (Prod.ext h1 rfl),
      Subtype.ext (Prod.ext h2 hS.symm)⟩⟩
  · rw [h1t] at h2 hy0
    exact ⟨y.1.2, hy0, Or.inl ⟨Subtype.ext (Prod.ext h1 rfl),
      Subtype.ext (Prod.ext h2 hS.symm)⟩⟩
  · exact absurd (Subtype.ext (Prod.ext (h1.trans h2.symm) hS)) hne

/-- **A refinement has the dangling edges of `D`** (Theorem 5.1; subdividing changes nothing). -/
theorem isDangling_iff (hD : D.Connected) (y : (refineDatum D t).SourceEdge) :
    IsDangling (refineDatum D t) y ↔ IsDangling D (parentSE D t y) := by
  classical
  have hR : (refineDatum D t).Connected := refineDatum_connected D t hD
  -- the two halves at a fresh vertex have one status
  have hhalves : ∀ i hi, (¬ IsDangling (refineDatum D t) (halfNone D t i hi) ↔
      ¬ IsDangling (refineDatum D t) (halfSome D t i hi)) := by
    intro i hi
    have h := wCount_nonDangling_ne_one _ hR (freshSV D t i hi)
    rw [wCount_freshSV] at h
    split_ifs at h with h1 h2 h2 <;> simp_all
  have hW : ∀ x : D.SourceVertex,
      wCount D (fun f ↦ ∃ y, parentSE D t y = f ∧ ¬ IsDangling (refineDatum D t) y) x ≠ 1 := by
    intro x
    rw [← wCount_oldSV D t]
    rw [wCount_congr _ _ (W' := fun y ↦ ¬ IsDangling (refineDatum D t) y)]
    · exact wCount_nonDangling_ne_one _ hR _
    · intro y _
      constructor
      · rintro ⟨y', hy', hnd⟩
        by_cases hyy : y = y'
        · exact hyy ▸ hnd
        · obtain ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
            eq_or_halves_of_parentSE_eq D t hy'.symm hyy
          · exact (hhalves i hi).mpr hnd
          · exact (hhalves i hi).mp hnd
      · intro hnd
        exact ⟨y, rfl, hnd⟩
  rw [← not_iff_not]
  constructor
  · intro hnd
    exact not_isDangling_of_witness D _ hW ⟨y, rfl, hnd⟩
  · intro hnd
    refine not_isDangling_of_witness _ (fun y ↦ ¬ IsDangling D (parentSE D t y)) (fun z ↦ ?_) hnd
    rcases sourceVertex_cases D t z with ⟨x, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [wCount_oldSV D t (fun f ↦ ¬ IsDangling D f)]; exact wCount_nonDangling_ne_one D hD x
    · rw [wCount_freshSV, parentSE_halfNone, parentSE_halfSome]
      split_ifs <;> omega

theorem isDangling_sourceEdge (hD : D.Connected) (ε : (subdivTarget T t).edges) (j : Fin d) :
    IsDangling (refineDatum D t) ((refineDatum D t).sourceEdge ε j) ↔
      IsDangling D (D.sourceEdge (parentT t ε) j) := by
  rw [isDangling_iff D t hD, parentSE_sourceEdge]

/-- **The valency at an old vertex** is that of `D`. -/
theorem nonDanglingValency_oldSV (hD : D.Connected) (x : D.SourceVertex) :
    nonDanglingValency (refineDatum D t) (oldSV D t x) = nonDanglingValency D x := by
  rw [nonDanglingValency_eq_wCount, nonDanglingValency_eq_wCount,
    ← wCount_oldSV D t (fun f ↦ ¬ IsDangling D f)]
  apply wCount_congr
  intro y _
  rw [isDangling_iff D t hD]

open Classical in
/-- **The valency at a fresh vertex** is two, or zero if its edge dangles. -/
theorem nonDanglingValency_freshSV (hD : D.Connected) (i : Fin d) (hi) :
    nonDanglingValency (refineDatum D t) (freshSV D t i hi) =
      if IsDangling D ⟨(t, i), hi⟩ then 0 else 2 := by
  rw [nonDanglingValency_eq_wCount, wCount_freshSV]
  simp only [isDangling_iff D t hD, parentSE_halfNone, parentSE_halfSome]
  by_cases h : IsDangling D ⟨(t, i), hi⟩ <;> simp [h]

open Classical in
theorem nonDanglingValency_sourceEndpoint_fresh (hD : D.Connected) (j : Fin d) :
    nonDanglingValency (refineDatum D t) ((refineDatum D t).sourceEndpoint (subdivFresh T t) j) =
      if IsDangling D (D.sourceEdge t j) then 0 else 2 := by
  rw [sourceEndpoint_subdivFresh]
  exact nonDanglingValency_freshSV D t hD _ _

theorem nonDanglingValency_sourceEndpoint_old (hD : D.Connected) (w : T.V) (j : Fin d) :
    nonDanglingValency (refineDatum D t) ((refineDatum D t).sourceEndpoint (subdivOld T t w) j) =
      nonDanglingValency D (D.sourceEndpoint w j) := by
  rw [sourceEndpoint_subdivOld]
  exact nonDanglingValency_oldSV D t hD _

/-- Trivalence passes to the refinement. -/
theorem nonDanglingValency_le_three (hD : D.Connected)
    (h : ∀ x, nonDanglingValency D x ≤ 3) (z : (refineDatum D t).SourceVertex) :
    nonDanglingValency (refineDatum D t) z ≤ 3 := by
  classical
  rcases sourceVertex_cases D t z with ⟨x, rfl⟩ | ⟨i, hi, rfl⟩
  · rw [nonDanglingValency_oldSV D t hD]; exact h x
  · rw [nonDanglingValency_freshSV D t hD]; split_ifs <;> omega

/-- The piece of the old source edge `f` at the old source vertex `x`. -/
noncomputable def piece (x : D.SourceVertex) (f : D.SourceEdge) : (refineDatum D t).SourceEdge :=
  ⟨(pieceT t x.1.1 f.1.1, f.1.2), by rw [refineDatum_edgePartition, parentT_pieceT]; exact f.2⟩

theorem parentSE_piece (x : D.SourceVertex) (f : D.SourceEdge) :
    parentSE D t (piece D t x f) = f :=
  Subtype.ext (Prod.ext (parentT_pieceT _ _ _) rfl)

theorem incident_piece {x : D.SourceVertex} {f : D.SourceEdge} (h : Incident D f x) :
    Incident (refineDatum D t) (piece D t x f) (oldSV D t x) := by
  rw [incident_oldSV_iff, parentSE_piece]
  refine ⟨h, ?_⟩
  show pieceT t x.1.1 f.1.1 = pieceT t x.1.1 (parentT t (pieceT t x.1.1 f.1.1))
  rw [parentT_pieceT]

/-- Two surviving edges with one parent lie on one stable path. -/
theorem stablePath_eq_of_parentSE_eq (hD : D.Connected)
    {y y' : NonDanglingEdge (refineDatum D t)} (h : parentSE D t y.1 = parentSE D t y'.1) :
    y.stablePath = y'.stablePath := by
  classical
  by_cases hyy : y.1 = y'.1
  · rw [Subtype.ext hyy]
  have hpar : ¬ IsDangling D (parentSE D t y.1) := (isDangling_iff D t hD y.1).not.mp y.2
  obtain ⟨i, hi, hcase⟩ := eq_or_halves_of_parentSE_eq D t h hyy
  have hval : nonDanglingValency (refineDatum D t) (freshSV D t i hi) = 2 := by
    rw [nonDanglingValency_freshSV D t hD, if_neg]
    rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
    · rwa [h1, parentSE_halfNone] at hpar
    · rwa [h1, parentSE_halfSome] at hpar
  apply stablePath_eq_of_consecutive
  refine ⟨fun h' ↦ hyy (congrArg Subtype.val h'), freshSV D t i hi, ?_, ?_, hval⟩
  · rw [incident_freshSV_iff]
    rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rw [incident_freshSV_iff]
    rcases hcase with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2

/-- **Path ends pass to the refinement**: a path end of `D` is a path end of the piece at it. -/
theorem hasPathEnds (hD : D.Connected) (hEnds : HasPathEnds D) :
    HasPathEnds (refineDatum D t) := by
  classical
  intro y
  have hpy : ¬ IsDangling D (parentSE D t y.1) := (isDangling_iff D t hD y.1).not.mp y.2
  obtain ⟨f', x, hf', hend⟩ := hEnds ⟨_, hpy⟩
  let Q : NonDanglingEdge D → Prop := fun f ↦ ∀ y'' : NonDanglingEdge (refineDatum D t),
    parentSE D t y''.1 = f.1 → y''.stablePath = y.stablePath
  have hQ0 : Q ⟨_, hpy⟩ := fun y'' h ↦ stablePath_eq_of_parentSE_eq D t hD h
  have hsurv : ∀ (x : D.SourceVertex) (f : NonDanglingEdge D),
      ¬ IsDangling (refineDatum D t) (piece D t x f.1) := fun x f ↦
    (isDangling_iff D t hD _).not.mpr (by rw [parentSE_piece]; exact f.2)
  have hclosed : ∀ a b : NonDanglingEdge D, Consecutive D a b → Q a → Q b := by
    rintro a b ⟨hab, x, ha, hb, hx⟩ hQa y'' hy''
    have hcons : Consecutive (refineDatum D t) ⟨_, hsurv x a⟩ ⟨_, hsurv x b⟩ := by
      refine ⟨fun h ↦ hab ?_, oldSV D t x, incident_piece D t ha, incident_piece D t hb, ?_⟩
      · have := congrArg (fun z : NonDanglingEdge (refineDatum D t) ↦ parentSE D t z.1) h
        simp only [parentSE_piece] at this
        exact Subtype.ext this
      · rw [nonDanglingValency_oldSV D t hD]; exact hx
    rw [stablePath_eq_of_parentSE_eq D t hD (y' := ⟨_, hsurv x b⟩) (by rw [hy'', parentSE_piece]),
      ← stablePath_eq_of_consecutive hcons]
    exact hQa _ (parentSE_piece D t x a.1)
  have hQf' : Q f' := (eqvGen_iff_of_closed hclosed ((stablePath_eq_iff _ _).mp hf')).mpr hQ0
  refine ⟨⟨_, hsurv x f'⟩, oldSV D t x, hQf' _ (parentSE_piece D t x f'.1), ?_, ?_⟩
  · exact incident_piece D t hend.1
  · rw [nonDanglingValency_oldSV D t hD]; exact hend.2

end Refine

/-! ### The three refinements at the marks -/

namespace Placement

variable (D : GluingDatum T d) (π : Placement T d)

theorem refine₃_connected (hD : D.Connected) : (refine₃ D π).Connected :=
  refineDatum_connected _ _ (refineDatum_connected _ _ (refineDatum_connected _ _ hD))

theorem refine₁_connected (hD : D.Connected) : (refineDatum D π.edge₀).Connected :=
  refineDatum_connected _ _ hD

theorem refine₂_connected (hD : D.Connected) :
    (refineDatum (refineDatum D π.edge₀) π.edge₁).Connected :=
  refineDatum_connected _ _ (refineDatum_connected _ _ hD)

theorem refine₃_trivalent (hD : D.Connected) (h : ∀ x, nonDanglingValency D x ≤ 3) :
    ∀ z, nonDanglingValency (refine₃ D π) z ≤ 3 :=
  Refine.nonDanglingValency_le_three _ _ (π.refine₂_connected D hD)
    (Refine.nonDanglingValency_le_three _ _ (π.refine₁_connected D hD)
      (Refine.nonDanglingValency_le_three _ _ hD h))

theorem refine₃_hasPathEnds (hD : D.Connected) (h : HasPathEnds D) : HasPathEnds (refine₃ D π) :=
  Refine.hasPathEnds _ _ (π.refine₂_connected D hD)
    (Refine.hasPathEnds _ _ (π.refine₁_connected D hD) (Refine.hasPathEnds _ _ hD h))

/-- **Each mark has valency two in `refine₃ D π`**: it subdivides a surviving edge. -/
theorem nonDanglingValency_markR₃ (hD : D.Connected) (hπ : π.NonDangling D) (k : Fin 3) :
    nonDanglingValency (refine₃ D π) ((refine₃ D π).sourceEndpoint (π.markVertex₃ k) (π.sheet k))
      = 2 := by
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  match k with
  | 0 =>
    show nonDanglingValency (refine₃ D π) ((refine₃ D π).sourceEndpoint
      (subdivOld _ _ (subdivOld _ _ (subdivFresh T π.edge₀))) (π.sheet 0)) = 2
    rw [Refine.nonDanglingValency_sourceEndpoint_old _ _ h₂,
      Refine.nonDanglingValency_sourceEndpoint_old _ _ h₁,
      Refine.nonDanglingValency_sourceEndpoint_fresh _ _ hD,
      if_neg (show ¬ IsDangling D (D.sourceEdge π.edge₀ (π.sheet 0)) from hπ 0)]
  | 1 =>
    show nonDanglingValency (refine₃ D π) ((refine₃ D π).sourceEndpoint
      (subdivOld _ _ (subdivFresh π.T₁ π.edge₁)) (π.sheet 1)) = 2
    rw [Refine.nonDanglingValency_sourceEndpoint_old _ _ h₂,
      Refine.nonDanglingValency_sourceEndpoint_fresh _ _ h₁, if_neg]
    rw [Refine.isDangling_sourceEdge _ _ hD]
    exact hπ 1
  | 2 =>
    show nonDanglingValency (refine₃ D π) ((refine₃ D π).sourceEndpoint
      (subdivFresh π.T₂ π.edge₂) (π.sheet 2)) = 2
    rw [Refine.nonDanglingValency_sourceEndpoint_fresh _ _ h₂, if_neg]
    rw [Refine.isDangling_sourceEdge _ _ h₁, Refine.isDangling_sourceEdge _ _ hD]
    exact hπ 2

end Placement

end DanglingDictionary

/-! ### The pieces of the glued source

The glued source has three kinds of source edges: the old ones (`liftSE`, an edge of
`refine₃ D π` in its old sheet), the new-sheet ones (`newSE`, a target edge of `T₃` in the sheet
`Fin.last d`) and the arms (`armSheetEdge`); and three kinds of source vertices: `oldVertex₃`,
`newVertex` and the vertices over the tips. Incidence among them is decided at the target, by
`incident_iff_target_mem_and_rel`. -/

section GlueStructure

open DraismaVargas.LocalCases.W4StableSource

namespace Placement

variable (π : Placement T d)

/-- The three arms are distinct target edges. -/
theorem armEdge_injective : Function.Injective π.armEdge := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp [Placement.armEdge] at h)

theorem T₆_edge_cases (ε : π.T₆.edges) : (∃ e, ε = π.liftE₃ e) ∨ ∃ k, ε = π.armEdge k := by
  obtain ⟨o₂, rfl⟩ := (leafOcc π.T₅ _).surjective ε
  rcases o₂ with _ | ε₅
  · exact Or.inr ⟨2, rfl⟩
  obtain ⟨o₁, rfl⟩ := (leafOcc π.T₄ _).surjective ε₅
  rcases o₁ with _ | ε₄
  · exact Or.inr ⟨1, rfl⟩
  obtain ⟨o₀, rfl⟩ := (leafOcc π.T₃ _).surjective ε₄
  rcases o₀ with _ | e
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inl ⟨e, rfl⟩

theorem liftE₃_injective : Function.Injective π.liftE₃ := by
  intro a b h
  unfold liftE₃ at h
  simpa using h

theorem liftE₃_ne_armEdge (e : π.T₃.edges) (k : Fin 3) : π.liftE₃ e ≠ π.armEdge k := by
  intro h
  match k with
  | 0 =>
    unfold liftE₃ armEdge at h
    simp at h
  | 1 =>
    unfold liftE₃ armEdge at h
    simp at h
  | 2 =>
    unfold liftE₃ armEdge at h
    simp at h

theorem T₆_vertex_cases (v : π.T₆.V) : (∃ w, v = π.lift₃ w) ∨ ∃ k, v = π.tipTarget k := by
  rcases v with ((w | ⟨⟩) | ⟨⟩) | ⟨⟩
  · exact Or.inl ⟨w, rfl⟩
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨1, rfl⟩
  · exact Or.inr ⟨2, rfl⟩

theorem markTarget_eq_lift₃ (k : Fin 3) : π.markTarget k = π.lift₃ (π.markVertex₃ k) := rfl

/-- **The target edges at an old vertex** of the glued target: the old ones, and the arm if it
is a mark image. -/
theorem mem_incidentEdges_lift₃ (v : π.T₃.V) (ε : π.T₆.edges) :
    ε ∈ GluingDatum.incidentEdges (π.lift₃ v) ↔
      (∃ e ∈ GluingDatum.incidentEdges v, ε = π.liftE₃ e) ∨
        ∃ k, π.markVertex₃ k = v ∧ ε = π.armEdge k := by
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases π.T₆_edge_cases ε with ⟨e, rfl⟩ | ⟨k, rfl⟩
  · rw [π.liftE₃_ends, (π.lift₃_injective).eq_iff, (π.lift₃_injective).eq_iff]
    constructor
    · intro h
      exact Or.inl ⟨e, h, rfl⟩
    · rintro (⟨e', h, he⟩ | ⟨k, -, hk⟩)
      · rw [π.liftE₃_injective he]; exact h
      · exact absurd hk (π.liftE₃_ne_armEdge e k)
  · rw [π.armEdge_ends, markTarget_eq_lift₃, (π.lift₃_injective).eq_iff]
    constructor
    · rintro (h | h)
      · exact Or.inr ⟨k, h, rfl⟩
      · exact absurd h (π.lift₃_ne_tipTarget v k).symm
    · rintro (⟨e', -, he⟩ | ⟨k', h, hk⟩)
      · exact absurd he.symm (π.liftE₃_ne_armEdge e' k)
      · rw [π.armEdge_injective hk]; exact Or.inl h

end Placement

variable (D : GluingDatum T d) (π : Placement T d)

theorem glueDatum_edgePartition_liftE₃ (ε : π.T₃.edges) :
    (glueDatum D π).edgePartition (π.liftE₃ ε) =
      SheetOps.extendNew ((refine₃ D π).edgePartition ε) := by
  show (glueDatum D π).edgePartition
    (leafOcc _ _ (some (leafOcc _ _ (some (leafOcc _ _ (some ε)))))) = _
  unfold glueDatum
  rw [leafDatum_edgePartition_some, leafDatum_edgePartition_some, leafDatum_edgePartition_some]
  rfl

theorem glueDatum_vertexPartition_lift₃ (v : π.T₃.V) :
    (glueDatum D π).vertexPartition (π.lift₃ v) =
      SheetOps.extendNew ((refine₃ D π).vertexPartition v) := rfl

/-- An old source edge of the glued datum: an edge of `refine₃ D π`, in its old sheet. -/
def liftSE (x : (refine₃ D π).SourceEdge) : (glueDatum D π).SourceEdge :=
  ⟨(π.liftE₃ x.1.1, x.1.2.castSucc), by
    rw [glueDatum_edgePartition_liftE₃, SheetOps.extendNew_repr_castSucc, x.2]⟩

/-- A new-sheet source edge of the glued datum. -/
def newSE (ε : π.T₃.edges) : (glueDatum D π).SourceEdge :=
  ⟨(π.liftE₃ ε, Fin.last d), by
    rw [glueDatum_edgePartition_liftE₃, SheetOps.extendNew_repr_last]⟩

theorem oldVertex₃_val (x : (refine₃ D π).SourceVertex) :
    (oldVertex₃ D π x).1 = (π.lift₃ x.1.1, x.1.2.castSucc) := by
  show (π.lift₃ x.1.1, (SheetOps.extendNew ((refine₃ D π).vertexPartition x.1.1)).repr
    x.1.2.castSucc) = _
  rw [SheetOps.extendNew_repr_castSucc, x.2]

theorem newVertex_val (v : π.T₃.V) : (newVertex D π v).1 = (π.lift₃ v, Fin.last d) := by
  show (π.lift₃ v, (SheetOps.extendNew ((refine₃ D π).vertexPartition v)).repr (Fin.last d)) = _
  rw [SheetOps.extendNew_repr_last]

theorem armSheetEdge_val (k : Fin 3) (j : Fin (d + 1)) :
    (armSheetEdge D π k j).1 = (π.armEdge k, j) :=
  Prod.ext rfl (armSheetEdge_sheet D π k j)

theorem liftSE_injective : Function.Injective (liftSE D π) := by
  intro a b h
  have h1 := congrArg (fun y : (glueDatum D π).SourceEdge ↦ y.1.1) h
  have h2 := congrArg (fun y : (glueDatum D π).SourceEdge ↦ y.1.2) h
  simp only [liftSE] at h1 h2
  exact Subtype.ext (Prod.ext (π.liftE₃_injective h1) (Fin.castSucc_injective _ h2))

theorem newSE_injective : Function.Injective (newSE D π) := by
  intro a b h
  exact π.liftE₃_injective (congrArg (fun y : (glueDatum D π).SourceEdge ↦ y.1.1) h)

theorem liftSE_ne_newSE (x : (refine₃ D π).SourceEdge) (ε : π.T₃.edges) :
    liftSE D π x ≠ newSE D π ε := fun h ↦
  (Fin.castSucc_lt_last x.1.2).ne (congrArg (fun y : (glueDatum D π).SourceEdge ↦ y.1.2) h)

theorem liftSE_ne_arm (x : (refine₃ D π).SourceEdge) (k : Fin 3) (j : Fin (d + 1)) :
    liftSE D π x ≠ armSheetEdge D π k j := fun h ↦
  π.liftE₃_ne_armEdge _ k (by
    have := congrArg (fun y : (glueDatum D π).SourceEdge ↦ y.1.1) h
    simpa [liftSE, armSheetEdge_val] using this)

theorem newSE_ne_arm (ε : π.T₃.edges) (k : Fin 3) (j : Fin (d + 1)) :
    newSE D π ε ≠ armSheetEdge D π k j := fun h ↦
  π.liftE₃_ne_armEdge _ k (by
    have := congrArg (fun y : (glueDatum D π).SourceEdge ↦ y.1.1) h
    simpa [newSE, armSheetEdge_val] using this)

theorem arm_injective : Function.Injective fun kj : Fin 3 × Fin (d + 1) ↦
    armSheetEdge D π kj.1 kj.2 := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  have h' := congrArg (fun y : (glueDatum D π).SourceEdge ↦ y.1) h
  simp only [armSheetEdge_val, Prod.mk.injEq] at h'
  exact Prod.ext (π.armEdge_injective h'.1) h'.2

/-- **Every source edge of the glued datum** is old, new-sheet, or an arm. -/
theorem sourceEdge_cases_glue (y : (glueDatum D π).SourceEdge) :
    (∃ x, y = liftSE D π x) ∨ (∃ ε, y = newSE D π ε) ∨
      ∃ k j, y = armSheetEdge D π k j := by
  obtain ⟨⟨ε, j⟩, hj⟩ := y
  rcases π.T₆_edge_cases ε with ⟨e, rfl⟩ | ⟨k, rfl⟩
  · rw [glueDatum_edgePartition_liftE₃] at hj
    induction j using Fin.lastCases with
    | last => exact Or.inr (Or.inl ⟨e, rfl⟩)
    | cast i =>
      rw [SheetOps.extendNew_repr_castSucc, Fin.castSucc_inj] at hj
      exact Or.inl ⟨⟨(e, i), hj⟩, rfl⟩
  · exact Or.inr (Or.inr ⟨k, j, eq_armSheetEdge D π _ rfl⟩)

/-- **Every source vertex of the glued datum** is old, new-sheet, or over a tip. -/
theorem sourceVertex_cases_glue (z : (glueDatum D π).SourceVertex) :
    (∃ x, z = oldVertex₃ D π x) ∨ (∃ v, z = newVertex D π v) ∨
      ∃ k j, z = (glueDatum D π).sourceEndpoint (π.tipTarget k) j := by
  obtain ⟨⟨w, j⟩, hj⟩ := z
  rcases π.T₆_vertex_cases w with ⟨v, rfl⟩ | ⟨k, rfl⟩
  · rw [glueDatum_vertexPartition_lift₃] at hj
    induction j using Fin.lastCases with
    | last => exact Or.inr (Or.inl ⟨v, Subtype.ext (newVertex_val D π v).symm⟩)
    | cast i =>
      rw [SheetOps.extendNew_repr_castSucc, Fin.castSucc_inj] at hj
      exact Or.inl ⟨⟨(v, i), hj⟩, Subtype.ext (oldVertex₃_val D π ⟨(v, i), hj⟩).symm⟩
  · exact Or.inr (Or.inr ⟨k, j, ((glueDatum D π).sourceEndpoint_self ⟨(π.tipTarget k, j), hj⟩).symm⟩)

theorem extendNew_rel_castSucc_iff (P : SheetPartition d) (i : Fin d) (j : Fin (d + 1)) :
    (SheetOps.extendNew P).Rel i.castSucc j ↔ ∃ i', j = i'.castSucc ∧ P.Rel i i' := by
  rw [SheetPartition.rel_iff]
  induction j using Fin.lastCases with
  | last =>
    simp only [SheetOps.extendNew_repr_castSucc, SheetOps.extendNew_repr_last]
    constructor
    · intro h
      exact absurd h (Fin.castSucc_lt_last _).ne
    · rintro ⟨i', h, -⟩
      exact absurd h (Fin.castSucc_lt_last _).ne'
  | cast j =>
    simp only [SheetOps.extendNew_repr_castSucc, Fin.castSucc_inj, SheetPartition.rel_iff]
    constructor
    · intro h; exact ⟨j, rfl, h⟩
    · rintro ⟨i', h, hrel⟩
      have h' : j = i' := by simpa using h
      subst h'
      exact hrel

theorem extendNew_rel_last_iff (P : SheetPartition d) (j : Fin (d + 1)) :
    (SheetOps.extendNew P).Rel (Fin.last d) j ↔ j = Fin.last d := by
  rw [SheetPartition.rel_iff]
  induction j using Fin.lastCases with
  | last => simp
  | cast j =>
    simp only [SheetOps.extendNew_repr_castSucc, SheetOps.extendNew_repr_last]
    constructor
    · intro h
      exact absurd h (Fin.castSucc_lt_last _).ne'
    · intro h
      exact absurd h (Fin.castSucc_lt_last _).ne

/-! #### Incidence -/

theorem incident_oldVertex₃_iff (y : (glueDatum D π).SourceEdge)
    (x : (refine₃ D π).SourceVertex) :
    Incident (glueDatum D π) y (oldVertex₃ D π x) ↔
      y.1.1 ∈ GluingDatum.incidentEdges (π.lift₃ x.1.1) ∧
        (SheetOps.extendNew ((refine₃ D π).vertexPartition x.1.1)).Rel x.1.2.castSucc y.1.2 := by
  rw [incident_iff_target_mem_and_rel, oldVertex₃_val]
  exact Iff.rfl

theorem incident_newVertex_iff (y : (glueDatum D π).SourceEdge) (v : π.T₃.V) :
    Incident (glueDatum D π) y (newVertex D π v) ↔
      y.1.1 ∈ GluingDatum.incidentEdges (π.lift₃ v) ∧ y.1.2 = Fin.last d := by
  rw [incident_iff_target_mem_and_rel, newVertex_val]
  show _ ∧ (SheetOps.extendNew ((refine₃ D π).vertexPartition v)).Rel (Fin.last d) y.1.2 ↔ _
  rw [extendNew_rel_last_iff]

theorem incident_liftSE_oldVertex₃ (x' : (refine₃ D π).SourceEdge)
    (x : (refine₃ D π).SourceVertex) :
    Incident (glueDatum D π) (liftSE D π x') (oldVertex₃ D π x) ↔ Incident (refine₃ D π) x' x := by
  rw [incident_oldVertex₃_iff, incident_iff_target_mem_and_rel]
  show π.liftE₃ x'.1.1 ∈ _ ∧ (SheetOps.extendNew _).Rel _ x'.1.2.castSucc ↔ _
  rw [π.mem_incidentEdges_lift₃, extendNew_rel_castSucc_iff]
  constructor
  · rintro ⟨⟨e, he, h⟩ | ⟨k, -, h⟩, i', hi', hrel⟩
    · refine ⟨?_, ?_⟩
      · rw [π.liftE₃_injective h]; exact he
      · rw [Fin.castSucc_injective _ hi']; exact hrel
    · exact absurd h (π.liftE₃_ne_armEdge _ k)
  · rintro ⟨he, hrel⟩
    exact ⟨Or.inl ⟨_, he, rfl⟩, _, rfl, hrel⟩

theorem not_incident_newSE_oldVertex₃ (ε : π.T₃.edges) (x : (refine₃ D π).SourceVertex) :
    ¬ Incident (glueDatum D π) (newSE D π ε) (oldVertex₃ D π x) := by
  rw [incident_oldVertex₃_iff]
  rintro ⟨-, h⟩
  obtain ⟨i', h', -⟩ := (extendNew_rel_castSucc_iff _ _ _).mp h
  exact (Fin.castSucc_lt_last i').ne h'.symm

theorem incident_arm_oldVertex₃_iff (k : Fin 3) (j : Fin (d + 1))
    (x : (refine₃ D π).SourceVertex) :
    Incident (glueDatum D π) (armSheetEdge D π k j) (oldVertex₃ D π x) ↔
      π.markVertex₃ k = x.1.1 ∧ ∃ i', j = i'.castSucc ∧
        ((refine₃ D π).vertexPartition x.1.1).Rel x.1.2 i' := by
  rw [incident_oldVertex₃_iff, armSheetEdge_val, π.mem_incidentEdges_lift₃,
    extendNew_rel_castSucc_iff]
  constructor
  · rintro ⟨⟨e, -, h⟩ | ⟨k', hk', h⟩, hrel⟩
    · exact absurd h.symm (π.liftE₃_ne_armEdge e k)
    · have hkk := π.armEdge_injective h
      subst hkk
      exact ⟨hk', hrel⟩
  · rintro ⟨hk, hrel⟩
    exact ⟨Or.inr ⟨k, hk, rfl⟩, hrel⟩

theorem not_incident_liftSE_newVertex (x : (refine₃ D π).SourceEdge) (v : π.T₃.V) :
    ¬ Incident (glueDatum D π) (liftSE D π x) (newVertex D π v) := by
  rw [incident_newVertex_iff]
  rintro ⟨-, h⟩
  exact (Fin.castSucc_lt_last x.1.2).ne h

theorem incident_newSE_newVertex (ε : π.T₃.edges) (v : π.T₃.V) :
    Incident (glueDatum D π) (newSE D π ε) (newVertex D π v) ↔
      ε ∈ GluingDatum.incidentEdges v := by
  rw [incident_newVertex_iff]
  show π.liftE₃ ε ∈ _ ∧ Fin.last d = Fin.last d ↔ _
  rw [π.mem_incidentEdges_lift₃]
  constructor
  · rintro ⟨⟨e, he, h⟩ | ⟨k, -, h⟩, -⟩
    · rw [π.liftE₃_injective h]; exact he
    · exact absurd h (π.liftE₃_ne_armEdge _ k)
  · intro h
    exact ⟨Or.inl ⟨ε, h, rfl⟩, rfl⟩

theorem incident_arm_newVertex_iff (k : Fin 3) (j : Fin (d + 1)) (v : π.T₃.V) :
    Incident (glueDatum D π) (armSheetEdge D π k j) (newVertex D π v) ↔
      π.markVertex₃ k = v ∧ j = Fin.last d := by
  rw [incident_newVertex_iff, armSheetEdge_val, π.mem_incidentEdges_lift₃]
  constructor
  · rintro ⟨⟨e, -, h⟩ | ⟨k', hk', h⟩, hj⟩
    · exact absurd h.symm (π.liftE₃_ne_armEdge e k)
    · have hkk := π.armEdge_injective h
      subst hkk
      exact ⟨hk', hj⟩
  · rintro ⟨hk, hj⟩
    exact ⟨Or.inr ⟨k, hk, rfl⟩, hj⟩

theorem not_incident_liftSE_tip (x : (refine₃ D π).SourceEdge) (k : Fin 3) (j : Fin (d + 1)) :
    ¬ Incident (glueDatum D π) (liftSE D π x)
      ((glueDatum D π).sourceEndpoint (π.tipTarget k) j) := by
  rw [incident_tip_iff]
  rintro ⟨h, -⟩
  exact π.liftE₃_ne_armEdge _ k h

theorem not_incident_newSE_tip (ε : π.T₃.edges) (k : Fin 3) (j : Fin (d + 1)) :
    ¬ Incident (glueDatum D π) (newSE D π ε)
      ((glueDatum D π).sourceEndpoint (π.tipTarget k) j) := by
  rw [incident_tip_iff]
  rintro ⟨h, -⟩
  exact π.liftE₃_ne_armEdge _ k h

/-! #### Counting the edges at a vertex, by kind -/

/-- The source edges of the glued datum, by kind. -/
noncomputable def glueEdgeEquiv :
    (refine₃ D π).SourceEdge ⊕ π.T₃.edges ⊕ (Fin 3 × Fin (d + 1)) ≃
      (glueDatum D π).SourceEdge :=
  Equiv.ofBijective
    (Sum.elim (liftSE D π) (Sum.elim (newSE D π)
      fun kj : Fin 3 × Fin (d + 1) ↦ armSheetEdge D π kj.1 kj.2)) (by
    constructor
    · rintro (a | b | c) (a' | b' | c') h
      all_goals simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [liftSE_injective D π h]
      · exact absurd h (liftSE_ne_newSE D π _ _)
      · exact absurd h (liftSE_ne_arm D π _ _ _)
      · exact absurd h.symm (liftSE_ne_newSE D π _ _)
      · rw [newSE_injective D π h]
      · exact absurd h (newSE_ne_arm D π _ _ _)
      · exact absurd h.symm (liftSE_ne_arm D π _ _ _)
      · exact absurd h.symm (newSE_ne_arm D π _ _ _)
      · rw [arm_injective D π h]
    · intro y
      rcases sourceEdge_cases_glue D π y with ⟨x, rfl⟩ | ⟨ε, rfl⟩ | ⟨k, j, rfl⟩
      · exact ⟨Sum.inl x, rfl⟩
      · exact ⟨Sum.inr (Sum.inl ε), rfl⟩
      · exact ⟨Sum.inr (Sum.inr (k, j)), rfl⟩)

theorem glueEdgeEquiv_apply
    (s : (refine₃ D π).SourceEdge ⊕ π.T₃.edges ⊕ (Fin 3 × Fin (d + 1))) :
    glueEdgeEquiv D π s = Sum.elim (liftSE D π) (Sum.elim (newSE D π)
      fun kj : Fin 3 × Fin (d + 1) ↦ armSheetEdge D π kj.1 kj.2) s := rfl

end GlueStructure

section GlueCount

open DraismaVargas.LocalCases.W4StableSource

open Classical in
theorem wCount_eq_sum {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (W : E.SourceEdge → Prop)
    (v : E.SourceVertex) :
    wCount E W v = ∑ e, if W e ∧ Incident E e v then 1 else 0 := by
  unfold wCount
  rw [Finset.card_filter]

/-- The number of target edges with property `X` at a target vertex. -/
noncomputable def tCount {S : CFGraph} (X : S.edges → Prop) (v : S.V) : ℕ := by
  classical
  exact (Finset.univ.filter fun ε ↦ X ε ∧ ε ∈ GluingDatum.incidentEdges v).card

open Classical in
theorem tCount_eq_sum {S : CFGraph} (X : S.edges → Prop) (v : S.V) :
    tCount X v = ∑ ε, if X ε ∧ ε ∈ GluingDatum.incidentEdges v then 1 else 0 := by
  unfold tCount
  rw [Finset.card_filter]

variable (D : GluingDatum T d) (π : Placement T d)

open Classical in
theorem wCount_glue_eq (W : (glueDatum D π).SourceEdge → Prop)
    (z : (glueDatum D π).SourceVertex) :
    wCount (glueDatum D π) W z =
      (∑ x, if W (liftSE D π x) ∧ Incident _ (liftSE D π x) z then 1 else 0) +
      ((∑ ε, if W (newSE D π ε) ∧ Incident _ (newSE D π ε) z then 1 else 0) +
      ∑ k, ∑ j, if W (armSheetEdge D π k j) ∧ Incident _ (armSheetEdge D π k j) z then 1 else 0) := by
  rw [wCount_eq_sum, ← (glueEdgeEquiv D π).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp only [glueEdgeEquiv_apply, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- The mark `k`, as a source vertex of `refine₃ D π`. -/
def markR₃ (k : Fin 3) : (refine₃ D π).SourceVertex :=
  (refine₃ D π).sourceEndpoint (π.markVertex₃ k) (π.sheet k)

theorem markR₃_injective : Function.Injective (markR₃ D π) := fun _ _ h ↦
  π.markVertex₃_injective (congrArg (fun z : (refine₃ D π).SourceVertex ↦ z.1.1) h)

/-- An edge property is **hairpin-shaped** when it holds of exactly the two arms of each
hairpin. -/
def HairpinShaped (W : (glueDatum D π).SourceEdge → Prop) : Prop :=
  ∀ k j, W (armSheetEdge D π k j) ↔ j = (π.sheet k).castSucc ∨ j = Fin.last d

theorem eq_markR₃_iff (x : (refine₃ D π).SourceVertex) (k : Fin 3) :
    x = markR₃ D π k ↔ π.markVertex₃ k = x.1.1 ∧
      ((refine₃ D π).vertexPartition x.1.1).Rel x.1.2 (π.sheet k) := by
  rw [markR₃]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := ((refine₃ D π).sourceEndpoint_eq_iff _ _ x).mp h.symm
    refine ⟨h1, ?_⟩
    rw [← h1]
    exact (SheetPartition.rel_iff _ _ _).mpr ((SheetPartition.rel_iff _ _ _).mp h2).symm
  · rintro ⟨h1, h2⟩
    refine (((refine₃ D π).sourceEndpoint_eq_iff _ _ x).mpr ⟨h1, ?_⟩).symm
    rw [h1]
    exact (SheetPartition.rel_iff _ _ _).mpr ((SheetPartition.rel_iff _ _ _).mp h2).symm

open Classical in
theorem sum_arm_oldVertex₃ {W : (glueDatum D π).SourceEdge → Prop} (hW : HairpinShaped D π W)
    (x : (refine₃ D π).SourceVertex) :
    (∑ k, ∑ j, if W (armSheetEdge D π k j) ∧
        Incident _ (armSheetEdge D π k j) (oldVertex₃ D π x) then 1 else 0) =
      ∑ k, if x = markR₃ D π k then 1 else 0 := by
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_eq_single (π.sheet k).castSucc]
  · refine if_congr ?_ rfl rfl
    rw [hW, incident_arm_oldVertex₃_iff, eq_markR₃_iff]
    constructor
    · rintro ⟨-, hk, i', hi', hrel⟩
      rw [Fin.castSucc_injective _ hi']
      exact ⟨hk, hrel⟩
    · rintro ⟨hk, hrel⟩
      exact ⟨Or.inl rfl, hk, _, rfl, hrel⟩
  · intro j _ hj
    rw [if_neg]
    rintro ⟨hWj, hinc⟩
    rcases (hW k j).mp hWj with h | h
    · exact hj h
    · obtain ⟨-, i', hi', -⟩ := (incident_arm_oldVertex₃_iff D π k j x).mp hinc
      rw [h] at hi'
      exact (Fin.castSucc_lt_last i').ne hi'.symm
  · intro h; exact absurd (Finset.mem_univ _) h

open Classical in
/-- **The count at an old vertex** of the glued datum, for a hairpin-shaped property: the count
in `refine₃ D π`, plus one at a mark. -/
theorem wCount_glue_oldVertex₃ {W : (glueDatum D π).SourceEdge → Prop} (hW : HairpinShaped D π W)
    (x : (refine₃ D π).SourceVertex) :
    wCount (glueDatum D π) W (oldVertex₃ D π x) =
      wCount (refine₃ D π) (fun x' ↦ W (liftSE D π x')) x +
        ∑ k, if x = markR₃ D π k then 1 else 0 := by
  rw [wCount_glue_eq, sum_arm_oldVertex₃ D π hW, wCount_eq_sum]
  have hnew : (∑ ε, if W (newSE D π ε) ∧ Incident _ (newSE D π ε) (oldVertex₃ D π x)
      then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun ε _ ↦ if_neg fun h ↦ not_incident_newSE_oldVertex₃ D π ε x h.2
  rw [hnew, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun x' _ ↦ if_congr ?_ rfl rfl
  rw [incident_liftSE_oldVertex₃]

open Classical in
theorem sum_mark_le_one (x : (refine₃ D π).SourceVertex) :
    (∑ k, if x = markR₃ D π k then 1 else 0) ≤ 1 := by
  by_cases h : ∃ k, x = markR₃ D π k
  · obtain ⟨k, rfl⟩ := h
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h'
      exact hb (markR₃_injective D π h').symm
    · simp
  · push Not at h
    simp [h]

open Classical in
theorem sum_mark_eq_one (k : Fin 3) :
    (∑ k', if markR₃ D π k = markR₃ D π k' then 1 else 0) = 1 := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h'
    exact hb (markR₃_injective D π h').symm
  · simp

open Classical in
theorem sum_mark_eq_zero {x : (refine₃ D π).SourceVertex} (h : ∀ k, x ≠ markR₃ D π k) :
    (∑ k, if x = markR₃ D π k then 1 else 0) = 0 :=
  Finset.sum_eq_zero fun k _ ↦ if_neg (h k)

open Classical in
/-- **The count at a new-sheet vertex**, for a hairpin-shaped property. -/
theorem wCount_glue_newVertex {W : (glueDatum D π).SourceEdge → Prop} (hW : HairpinShaped D π W)
    (v : π.T₃.V) :
    wCount (glueDatum D π) W (newVertex D π v) =
      tCount (fun ε ↦ W (newSE D π ε)) v + ∑ k, if π.markVertex₃ k = v then 1 else 0 := by
  rw [wCount_glue_eq, tCount_eq_sum]
  have hold : (∑ x, if W (liftSE D π x) ∧ Incident _ (liftSE D π x) (newVertex D π v)
      then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ if_neg fun h ↦ not_incident_liftSE_newVertex D π x v h.2
  rw [hold, zero_add]
  congr 1
  · refine Finset.sum_congr rfl fun ε _ ↦ if_congr ?_ rfl rfl
    rw [incident_newSE_newVertex]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_eq_single (Fin.last d)]
    · refine if_congr ?_ rfl rfl
      rw [hW, incident_arm_newVertex_iff]
      simp
    · intro j _ hj
      rw [if_neg]
      rintro ⟨-, hinc⟩
      exact hj ((incident_arm_newVertex_iff D π k j v).mp hinc).2
    · intro h; exact absurd (Finset.mem_univ _) h

theorem incident_tip_arm_only (k : Fin 3) (j : Fin (d + 1)) (y : (glueDatum D π).SourceEdge)
    (h : Incident (glueDatum D π) y ((glueDatum D π).sourceEndpoint (π.tipTarget k) j)) :
    y = armSheetEdge D π k y.1.2 :=
  eq_armSheetEdge D π y ((incident_tip_iff D π k j y).mp h).1

end GlueCount

/-! ### Trees

The new sheet of the glued source is a copy of the tree `T₃`, so the new-sheet half of the
dangling dictionary is a statement about edge sets in a tree. A connected graph of genus zero has
a tree as underlying simple graph and no parallel edges (`isTree_of_genus_zero`,
`num_edges_le_one_of_genus_zero`). In an acyclic graph a path can be walked on, through vertices
of degree other than one, until it reaches a prescribed set `M` (`exists_path_to_mem`), and two
such walks from one vertex reach different points of `M` when they start differently. So a
vertex has at most `|M ∖ {v}|` edges of an edge set without valency one off `M`
(`tCount_add_le`). -/

section Trees

open Utilities

theorem num_edges_eq_card_univ_filter (S : CFGraph) (u w : S.V) :
    num_edges S u w = (Finset.univ.filter fun ε : S.edges ↦
      (ε : S.V × S.V) = (u, w) ∨ (ε : S.V × S.V) = (w, u)).card := by
  classical
  unfold num_edges
  conv_lhs => rw [← Multiset.map_univ_coe S.edges]
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- **A connected graph of genus zero is a tree**, after forgetting multiplicities. -/
theorem isTree_of_genus_zero {S : CFGraph} (hS : graph_connected S) (hg : genus S = 0) :
    (underlyingSimpleGraph S).IsTree := by
  classical
  have hc : (underlyingSimpleGraph S).Connected :=
    (graph_connected_iff_underlyingSimpleGraph_connected S).mp hS
  have hlow : Fintype.card S.V ≤ (underlyingSimpleGraph S).edgeFinset.card + 1 := by
    have := hc.card_vert_le_card_edgeSet_add_one
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using this
  have hup := underlyingSimpleGraph_edgeFinset_card_le S
  have hE : (Multiset.card S.edges : ℤ) + 1 = Fintype.card S.V := by
    unfold genus at hg; omega
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc, ?_⟩
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega

/-- **A connected graph of genus zero has no parallel edges.** -/
theorem num_edges_le_one_of_genus_zero {S : CFGraph} (hS : graph_connected S)
    (hg : genus S = 0) (u w : S.V) : num_edges S u w ≤ 1 := by
  classical
  have hc : (underlyingSimpleGraph S).Connected :=
    (graph_connected_iff_underlyingSimpleGraph_connected S).mp hS
  have hlow : Fintype.card S.V ≤ (underlyingSimpleGraph S).edgeFinset.card + 1 := by
    have := hc.card_vert_le_card_edgeSet_add_one
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using this
  have hsub : (underlyingSimpleGraph S).edgeFinset.card ≤
      (S.edges.map fun e ↦ s(e.1, e.2)).toFinset.card := by
    apply Finset.card_le_card
    intro e he
    rw [Multiset.mem_toFinset]
    rw [SimpleGraph.mem_edgeFinset] at he
    refine Sym2.ind ?_ e he
    intro x y hxy
    change num_edges S x y > 0 at hxy
    change 0 < (S.edges.filter (fun edge => edge = (x, y) ∨ edge = (y, x))).card at hxy
    rw [Multiset.card_pos_iff_exists_mem] at hxy
    obtain ⟨edge, hedge⟩ := hxy
    rw [Multiset.mem_filter] at hedge
    rcases hedge with ⟨hEdge, hEdgeEndpoints⟩
    refine Multiset.mem_map.mpr ⟨edge, hEdge, ?_⟩
    rcases hEdgeEndpoints with hEdgeEndpoints | hEdgeEndpoints
    · simp [hEdgeEndpoints]
    · simp [hEdgeEndpoints, Sym2.eq_swap]
  have hE : (Multiset.card S.edges : ℤ) + 1 = Fintype.card S.V := by
    unfold genus at hg; omega
  have hnodup : (S.edges.map fun e ↦ s(e.1, e.2)).Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    have := Multiset.toFinset_card_le (S.edges.map fun e ↦ s(e.1, e.2))
    rw [Multiset.card_map] at this ⊢
    omega
  unfold num_edges
  calc Multiset.card (S.edges.filter fun e ↦ e = (u, w) ∨ e = (w, u))
      ≤ Multiset.card (S.edges.filter fun e ↦ s(u, w) = s(e.1, e.2)) := by
        apply Multiset.card_le_card
        apply Multiset.monotone_filter_right
        intro e he
        rcases he with rfl | rfl
        · rfl
        · exact Sym2.eq_swap
    _ = Multiset.count s(u, w) (S.edges.map fun e ↦ s(e.1, e.2)) :=
        (Multiset.count_map _ _ _).symm
    _ ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnodup _

/-- **Walking out along a forest.** In an acyclic graph in which every vertex off `M` with a
neighbour has a second one, a path can be continued until it ends in `M`. -/
theorem exists_path_to_mem {V : Type*} [Fintype V] {H : SimpleGraph V} (hH : H.IsAcyclic)
    (M : Set V) (hdeg : ∀ u ∉ M, ∀ w, H.Adj u w → ∃ w', H.Adj u w' ∧ w' ≠ w) {v w : V}
    (hvw : H.Adj v w) {u : V} (q : H.Walk w u) (hq : (SimpleGraph.Walk.cons hvw q).IsPath) :
    ∃ (m : V) (q' : H.Walk w m), (SimpleGraph.Walk.cons hvw q').IsPath ∧ m ∈ M := by
  suffices key : ∀ n, ∀ {u : V} (q : H.Walk w u), (SimpleGraph.Walk.cons hvw q).IsPath →
      Fintype.card V - q.length = n →
      ∃ (m : V) (q' : H.Walk w m), (SimpleGraph.Walk.cons hvw q').IsPath ∧ m ∈ M from
    key _ q hq rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u q hq hn
    by_cases hu : u ∈ M
    · exact ⟨u, q, hq, hu⟩
    · have hnil : ¬ (SimpleGraph.Walk.cons hvw q).Nil := SimpleGraph.Walk.not_nil_cons
      have hpen := (SimpleGraph.Walk.adj_penultimate hnil).symm
      obtain ⟨w', hw', hne⟩ := hdeg u hu _ hpen
      have hnot : w' ∉ (SimpleGraph.Walk.cons hvw q).support := fun hm ↦
        hne (hH.eq_penultimate_of_adj_end hq hw' hm)
      have hp' : (SimpleGraph.Walk.cons hvw (q.concat hw')).IsPath := hq.concat hnot hw'
      have hlt := hp'.length_lt
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat] at hlt
      refine ih (Fintype.card V - (q.concat hw').length) ?_ (q.concat hw') hp' rfl
      rw [SimpleGraph.Walk.length_concat]
      omega

/-- Two paths from `v` to one point that start differently do not exist in an acyclic graph. -/
theorem snd_eq_of_isAcyclic {V : Type*} {H : SimpleGraph V} (hH : H.IsAcyclic) {v w w' m : V}
    (hvw : H.Adj v w) (hvw' : H.Adj v w') (q : H.Walk w m) (q' : H.Walk w' m)
    (hq : (SimpleGraph.Walk.cons hvw q).IsPath) (hq' : (SimpleGraph.Walk.cons hvw' q').IsPath) :
    w = w' := by
  have h := (hH.subsingleton_path v m).elim ⟨_, hq⟩ ⟨_, hq'⟩
  have := congrArg (fun p : H.Path v m ↦ p.1.snd) h
  simpa using this

/-- **At most `|M ∖ {v}|` directions.** -/
theorem card_adj_le_card_erase {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] (hH : H.IsAcyclic) (M : Finset V)
    (hdeg : ∀ u ∉ M, ∀ w, H.Adj u w → ∃ w', H.Adj u w' ∧ w' ≠ w) (v : V) :
    (Finset.univ.filter (H.Adj v)).card ≤ (M.erase v).card := by
  classical
  have hex : ∀ w (h : H.Adj v w), ∃ m, m ∈ M ∧ ∃ q : H.Walk w m,
      (SimpleGraph.Walk.cons h q).IsPath := by
    intro w h
    have h0 : (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by simpa using h.ne⟩
    obtain ⟨m, q, hq, hm⟩ := exists_path_to_mem hH (↑M) (fun u hu w hw ↦ hdeg u hu w hw) h _ h0
    exact ⟨m, hm, q, hq⟩
  let f : V → V := fun w ↦ if h : H.Adj v w then Classical.choose (hex w h) else v
  have hf : ∀ w (h : H.Adj v w), f w ∈ M ∧ ∃ q : H.Walk w (f w),
      (SimpleGraph.Walk.cons h q).IsPath := by
    intro w h
    have hfw : f w = Classical.choose (hex w h) := dif_pos h
    rw [hfw]
    exact Classical.choose_spec (hex w h)
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro w hw
    have hw' : H.Adj v w := (Finset.mem_filter.mp hw).2
    obtain ⟨hm, q, hq⟩ := hf w hw'
    refine Finset.mem_erase.mpr ⟨?_, hm⟩
    intro hfv
    have hv : v ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hq).2
    exact hv (hfv ▸ q.end_mem_support)
  · intro w₁ hw₁ w₂ hw₂ heq
    have h₁ : H.Adj v w₁ := (Finset.mem_filter.mp hw₁).2
    have h₂ : H.Adj v w₂ := (Finset.mem_filter.mp hw₂).2
    obtain ⟨-, q₁, hq₁⟩ := hf w₁ h₁
    obtain ⟨-, q₂, hq₂⟩ := hf w₂ h₂
    revert q₁ hq₁
    rw [heq]
    intro q₁ hq₁
    exact snd_eq_of_isAcyclic hH h₁ h₂ q₁ q₂ hq₁ hq₂

variable {S : CFGraph}

/-- The graph of the edges with property `X`. -/
def edgeGraph (S : CFGraph) (X : S.edges → Prop) : SimpleGraph S.V :=
  SimpleGraph.fromRel fun u w ↦ ∃ ε : S.edges, X ε ∧ (ε : S.V × S.V) = (u, w)

theorem edgeGraph_adj (X : S.edges → Prop) (u w : S.V) :
    (edgeGraph S X).Adj u w ↔ ∃ ε : S.edges, X ε ∧
      ((ε : S.V × S.V) = (u, w) ∨ (ε : S.V × S.V) = (w, u)) := by
  rw [edgeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨ε, hX, h⟩ | ⟨ε, hX, h⟩⟩
    · exact ⟨ε, hX, Or.inl h⟩
    · exact ⟨ε, hX, Or.inr h⟩
  · rintro ⟨ε, hX, h | h⟩
    · refine ⟨fun huw ↦ ?_, Or.inl ⟨ε, hX, h⟩⟩
      subst huw
      exact S.loopless u (h ▸ Multiset.coe_mem)
    · refine ⟨fun huw ↦ ?_, Or.inr ⟨ε, hX, h⟩⟩
      subst huw
      exact S.loopless u (h ▸ Multiset.coe_mem)

theorem edgeGraph_le (X : S.edges → Prop) : edgeGraph S X ≤ underlyingSimpleGraph S := by
  classical
  intro u w h
  obtain ⟨ε, -, hε⟩ := (edgeGraph_adj X u w).mp h
  change num_edges S u w > 0
  rw [num_edges_eq_card_univ_filter]
  exact Finset.card_pos.mpr ⟨ε, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hε⟩⟩

/-- The other end of a target edge at `v`. -/
def otherEnd (v : S.V) (ε : S.edges) : S.V :=
  if (ε : S.V × S.V).1 = v then (ε : S.V × S.V).2 else (ε : S.V × S.V).1

/-- **The `X`-edges at `v` are its `X`-neighbours**, when there are no parallel edges. -/
theorem tCount_eq_card_adj (hpar : ∀ u w : S.V, num_edges S u w ≤ 1) (X : S.edges → Prop)
    (v : S.V) [DecidableRel (edgeGraph S X).Adj] :
    tCount X v = (Finset.univ.filter ((edgeGraph S X).Adj v)).card := by
  classical
  unfold tCount
  refine Finset.card_bij (fun ε _ ↦ otherEnd v ε) ?_ ?_ ?_
  · intro ε hε
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, GluingDatum.incidentEdges] at hε ⊢
    rw [edgeGraph_adj]
    refine ⟨ε, hε.1, ?_⟩
    unfold otherEnd
    rcases hε.2 with h | h
    · rw [if_pos h]; left; exact Prod.ext h rfl
    · by_cases h1 : (ε : S.V × S.V).1 = v
      · rw [if_pos h1]; left; exact Prod.ext h1 rfl
      · rw [if_neg h1]; right; exact Prod.ext rfl h
  · intro ε₁ h₁ ε₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, GluingDatum.incidentEdges] at h₁ h₂
    have hends : ∀ ε : S.edges, ((ε : S.V × S.V).1 = v ∨ (ε : S.V × S.V).2 = v) →
        ((ε : S.V × S.V) = (v, otherEnd v ε) ∨ (ε : S.V × S.V) = (otherEnd v ε, v)) := by
      intro ε h
      unfold otherEnd
      by_cases h1 : (ε : S.V × S.V).1 = v
      · rw [if_pos h1]; left; exact Prod.ext h1 rfl
      · rw [if_neg h1]; right; exact Prod.ext rfl (h.resolve_left h1)
    have hle := hpar v (otherEnd v ε₁)
    rw [num_edges_eq_card_univ_filter] at hle
    have hm₁ : ε₁ ∈ Finset.univ.filter fun ε : S.edges ↦
        (ε : S.V × S.V) = (v, otherEnd v ε₁) ∨ (ε : S.V × S.V) = (otherEnd v ε₁, v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hends ε₁ h₁.2⟩
    have hm₂ : ε₂ ∈ Finset.univ.filter fun ε : S.edges ↦
        (ε : S.V × S.V) = (v, otherEnd v ε₁) ∨ (ε : S.V × S.V) = (otherEnd v ε₁, v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have := hends ε₂ h₂.2
        rw [← heq] at this
        exact this⟩
    exact Finset.card_le_one.mp hle _ hm₁ _ hm₂
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨ε, hX, h⟩ := (edgeGraph_adj X v w).mp hw
    have hvw : v ≠ w := hw.ne
    refine ⟨ε, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, GluingDatum.incidentEdges]
      rcases h with h | h
      · exact ⟨hX, Or.inl (by rw [h])⟩
      · exact ⟨hX, Or.inr (by rw [h])⟩
    · unfold otherEnd
      rcases h with h | h
      · rw [h]; simp
      · rw [h]; simp [Ne.symm hvw]

/-- **The degree bound in a tree** (§5.2): an edge set of a tree without
valency one off `M` has at most `|M|` edges at a vertex, `|M| - 1` at a point of `M`. -/
theorem tCount_add_le (hS : graph_connected S) (hg : genus S = 0) (M : Finset S.V)
    (X : S.edges → Prop) (hX : ∀ u ∉ M, tCount X u ≠ 1) (v : S.V) :
    tCount X v + (if v ∈ M then 1 else 0) ≤ M.card := by
  classical
  have hpar := num_edges_le_one_of_genus_zero hS hg
  have hac : (edgeGraph S X).IsAcyclic :=
    (isTree_of_genus_zero hS hg).isAcyclic.anti (edgeGraph_le X)
  have hdeg : ∀ u ∉ M, ∀ w, (edgeGraph S X).Adj u w → ∃ w', (edgeGraph S X).Adj u w' ∧ w' ≠ w := by
    intro u hu w hw
    have hpos : 1 < (Finset.univ.filter ((edgeGraph S X).Adj u)).card := by
      have h1 := hX u hu
      rw [tCount_eq_card_adj hpar] at h1
      have h0 : 0 < (Finset.univ.filter ((edgeGraph S X).Adj u)).card :=
        Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_cases haw : a = w
    · exact ⟨b, hb, fun hbw ↦ hab (haw.trans hbw.symm)⟩
    · exact ⟨a, ha, haw⟩
  have h := card_adj_le_card_erase hac M hdeg v
  rw [← tCount_eq_card_adj hpar] at h
  by_cases hv : v ∈ M
  · rw [if_pos hv]
    have := Finset.card_erase_add_one hv
    omega
  · rw [if_neg hv, Finset.erase_eq_of_notMem hv] at *
    omega

/-- **A forest has a leaf**: an edge set of a tree with no vertex of valency one is empty. -/
theorem not_of_tCount_ne_one (hS : graph_connected S) (hg : genus S = 0) (X : S.edges → Prop)
    (hX : ∀ u, tCount X u ≠ 1) (ε : S.edges) : ¬ X ε := by
  classical
  intro hε
  have h := tCount_add_le hS hg ∅ X (fun u _ ↦ hX u) (ε : S.V × S.V).1
  simp only [Finset.notMem_empty, if_false, add_zero, Finset.card_empty] at h
  have hpos : 0 < tCount X (ε : S.V × S.V).1 := by
    unfold tCount
    exact Finset.card_pos.mpr ⟨ε, by simp [GluingDatum.incidentEdges, hε]⟩
  omega

theorem reachable_induce_of_walk {V : Type*} {H : SimpleGraph V} (s : Set V)
    (hs : ∀ u w, H.Adj u w → u ∈ s) :
    ∀ {a b : V} (_ : H.Walk a b) (ha : a ∈ s), ∃ hb : b ∈ s,
      (H.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩
  | _, _, .nil, ha => ⟨ha, SimpleGraph.Reachable.refl _⟩
  | _, _, .cons h p, ha => by
    obtain ⟨hb, hr⟩ := reachable_induce_of_walk s hs p (hs _ _ h.symm)
    refine ⟨hb, SimpleGraph.Reachable.trans ?_ hr⟩
    exact SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.mpr h)

/-- **One branch point** (§3.3). An edge set of a tree without valency one off
three points, with an edge at each of them, is a tree with its leaves among the three points, so
exactly one vertex has `tCount X v + [v ∈ M] = 3`. -/
theorem card_branch_eq_one (hS : graph_connected S) (hg : genus S = 0) (M : Finset S.V)
    (hM : M.card = 3) (X : S.edges → Prop) (hX : ∀ u ∉ M, tCount X u ≠ 1)
    (hXM : ∀ u ∈ M, tCount X u ≠ 0) :
    (Finset.univ.filter fun v ↦ 3 ≤ tCount X v + (if v ∈ M then 1 else 0)).card = 1 := by
  classical
  have hpar := num_edges_le_one_of_genus_zero hS hg
  set H := edgeGraph S X with hHdef
  have hac : H.IsAcyclic := (isTree_of_genus_zero hS hg).isAcyclic.anti (edgeGraph_le X)
  have hdegH : ∀ v, tCount X v = (Finset.univ.filter (H.Adj v)).card :=
    fun v ↦ tCount_eq_card_adj hpar X v
  have hdeg : ∀ u ∉ M, ∀ w, H.Adj u w → ∃ w', H.Adj u w' ∧ w' ≠ w := by
    intro u hu w hw
    have hpos : 1 < (Finset.univ.filter (H.Adj u)).card := by
      have h1 := hX u hu
      rw [hdegH] at h1
      have h0 : 0 < (Finset.univ.filter (H.Adj u)).card :=
        Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_cases haw : a = w
    · exact ⟨b, hb, fun hbw ↦ hab (haw.trans hbw.symm)⟩
    · exact ⟨a, ha, haw⟩
  have hpath1 : ∀ {v w : S.V} (h : H.Adj v w), (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil).IsPath :=
    fun h ↦ by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by simpa using h.ne⟩
  -- the support of `X`, with `M`
  set V' : Finset S.V := Finset.univ.filter fun v ↦ 0 < tCount X v ∨ v ∈ M with hV'def
  have hmemV' : ∀ v, v ∈ V' ↔ 0 < tCount X v ∨ v ∈ M := fun v ↦ by simp [V']
  have hadjV : ∀ u w, H.Adj u w → u ∈ (V' : Set S.V) := by
    intro u w h
    rw [Finset.mem_coe, hmemV', hdegH]
    exact Or.inl (Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)
  have hreachM : ∀ v ∈ V', ∃ m ∈ M, H.Reachable v m := by
    intro v hv
    rcases (hmemV' v).mp hv with h | h
    · rw [hdegH] at h
      obtain ⟨w, hw⟩ := Finset.card_pos.mp h
      have hw' : H.Adj v w := (Finset.mem_filter.mp hw).2
      obtain ⟨m, q, -, hm⟩ := exists_path_to_mem hac M hdeg hw' _ (hpath1 hw')
      exact ⟨m, hm, ⟨SimpleGraph.Walk.cons hw' q⟩⟩
    · exact ⟨v, h, SimpleGraph.Reachable.refl _⟩
  have hMM : ∀ m ∈ M, ∃ m' ∈ M, m' ≠ m ∧ H.Reachable m m' := by
    intro m hm
    have h := hXM m hm
    rw [hdegH] at h
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    have hw' : H.Adj m w := (Finset.mem_filter.mp hw).2
    obtain ⟨m', q, hq, hm'⟩ := exists_path_to_mem hac M hdeg hw' _ (hpath1 hw')
    refine ⟨m', hm', ?_, ⟨SimpleGraph.Walk.cons hw' q⟩⟩
    rintro rfl
    exact ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hq).2 q.end_mem_support
  obtain ⟨a, b, c, hab, hac', hbc, hMabc⟩ := Finset.card_eq_three.mp hM
  have hmemM : ∀ m, m ∈ M ↔ m = a ∨ m = b ∨ m = c := fun m ↦ by simp [hMabc]
  have haM : a ∈ M := (hmemM a).mpr (Or.inl rfl)
  have hbM : b ∈ M := (hmemM b).mpr (Or.inr (Or.inl rfl))
  have hcM : c ∈ M := (hmemM c).mpr (Or.inr (Or.inr rfl))
  have hallM : ∀ m ∈ M, H.Reachable a m := by
    obtain ⟨m₁, hm₁, hne₁, hr₁⟩ := hMM a haM
    have hb' : H.Reachable a b ∧ H.Reachable a c := by
      rcases (hmemM m₁).mp hm₁ with rfl | rfl | rfl
      · exact absurd rfl hne₁
      · obtain ⟨m₂, hm₂, hne₂, hr₂⟩ := hMM c hcM
        refine ⟨hr₁, ?_⟩
        rcases (hmemM m₂).mp hm₂ with rfl | rfl | rfl
        · exact hr₂.symm
        · exact hr₁.trans hr₂.symm
        · exact absurd rfl hne₂
      · obtain ⟨m₂, hm₂, hne₂, hr₂⟩ := hMM b hbM
        refine ⟨?_, hr₁⟩
        rcases (hmemM m₂).mp hm₂ with rfl | rfl | rfl
        · exact hr₂.symm
        · exact absurd rfl hne₂
        · exact hr₁.trans hr₂.symm
    intro m hm
    rcases (hmemM m).mp hm with rfl | rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hb'.1
    · exact hb'.2
  -- the induced graph on the support is a tree
  have haV : a ∈ (V' : Set S.V) := by rw [Finset.mem_coe, hmemV']; exact Or.inr haM
  have htree : (H.induce (V' : Set S.V)).IsTree := by
    refine ⟨?_, hac.induce _⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨a, haV⟩, fun ⟨v, hv⟩ ↦ ?_⟩
    obtain ⟨m, hm, hr⟩ := hreachM v hv
    obtain ⟨p⟩ := (hallM m hm).trans hr.symm
    obtain ⟨hb, hr'⟩ := reachable_induce_of_walk _ hadjV p haV
    exact hr'
  have hsum := (H.induce (V' : Set S.V)).sum_degrees_eq_twice_card_edges
  have hcard := htree.card_edgeFinset
  have hdegI : ∀ v : (V' : Set S.V), (H.induce (V' : Set S.V)).degree v = tCount X v.1 := by
    intro v
    rw [hdegH, ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    refine Finset.card_bij (fun w _ ↦ w.1) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact SimpleGraph.induce_adj.mp hw
    · intro w₁ _ w₂ _ h
      exact Subtype.ext h
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact ⟨⟨w, hadjV w v.1 hw.symm⟩, by simpa [SimpleGraph.induce_adj] using hw, rfl⟩
  simp only [hdegI] at hsum
  rw [← Finset.sum_subtype V' (p := fun x ↦ x ∈ (V' : Set S.V)) (fun x ↦ Finset.mem_coe.symm)
    (fun v ↦ tCount X v)] at hsum
  have hcardV : Fintype.card (V' : Set S.V) = V'.card := by simp
  rw [hcardV] at hcard
  -- the valencies on the support are two or three
  set val : S.V → ℕ := fun v ↦ tCount X v + (if v ∈ M then 1 else 0) with hval
  have hval_le : ∀ v, val v ≤ 3 := fun v ↦ hM ▸ tCount_add_le hS hg M X hX v
  have hval_ge : ∀ v ∈ V', 2 ≤ val v := by
    intro v hv
    simp only [val]
    by_cases hvM : v ∈ M
    · rw [if_pos hvM]; have := hXM v hvM; omega
    · rw [if_neg hvM]
      have h1 := hX v hvM
      rcases (hmemV' v).mp hv with h | h
      · omega
      · exact absurd h hvM
  have hMV : M ⊆ V' := fun m hm ↦ (hmemV' m).mpr (Or.inr hm)
  have hsumval : ∑ v ∈ V', val v = 2 * V'.card + 1 := by
    simp only [val, Finset.sum_add_distrib]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hMV, Finset.sum_const, hM]
    simp only [smul_eq_mul, mul_one]
    omega
  have hfilter : (Finset.univ.filter fun v ↦ 3 ≤ val v) = V'.filter fun v ↦ 3 ≤ val v := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨(hmemV' v).mpr ?_, h⟩
      by_contra hn
      push Not at hn
      have : val v = 0 := by simp only [val]; rw [if_neg hn.2]; omega
      omega
    · exact fun h ↦ h.2
  show (Finset.univ.filter fun v ↦ 3 ≤ val v).card = 1
  rw [hfilter, Finset.card_filter]
  have hpt : ∀ v ∈ V', (if 3 ≤ val v then 1 else 0) = val v - 2 := by
    intro v hv
    have h1 := hval_le v
    have h2 := hval_ge v hv
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hpt]
  have hsub : ∑ v ∈ V', (val v - 2) + ∑ _v ∈ V', 2 = ∑ v ∈ V', val v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v hv ↦ by have := hval_ge v hv; omega
  rw [Finset.sum_const, smul_eq_mul, hsumval] at hsub
  omega

end Trees

/-! ### The dangling dictionary of the glued datum

The old edges keep their status (`isDangling_liftSE_iff`): the survivors of `refine₃ D π`, the
hairpins and the surviving new-sheet edges form a witness, and conversely the survivors of the
glued datum among the old edges form a witness in `refine₃ D π`, the marks being harmless since
each has two old survivors there (`Placement.nonDanglingValency_markR₃`). So the valency at an old
vertex is that of `refine₃ D π`, plus one at a mark; at a new-sheet vertex it is the number of
surviving new-sheet edges, plus one at a mark image; and over a tip it is at most two. -/

section GlueDangling

open DraismaVargas.LocalCases.W4StableSource

variable (D : GluingDatum T d) (π : Placement T d)

theorem hairpinShaped_nonDangling (hD : D.Connected) (hT : graph_connected T) :
    HairpinShaped D π (fun y ↦ ¬ IsDangling (glueDatum D π) y) := by
  intro k j
  have hconn := glueDatum_connected D π hD hT
  constructor
  · intro h
    by_contra hj
    push Not at hj
    exact h (isDangling_armSheetEdge D π hconn k j hj.1 hj.2)
  · rintro (rfl | rfl)
    · exact (hairpin_not_isDangling D π hD hT k).1
    · exact (hairpin_not_isDangling D π hD hT k).2

/-- **The old edges keep their status in the glued datum** (§5.2). -/
theorem isDangling_liftSE_iff (hD : D.Connected) (hT : graph_connected T) (hπ : π.NonDangling D)
    (x : (refine₃ D π).SourceEdge) :
    IsDangling (glueDatum D π) (liftSE D π x) ↔ IsDangling (refine₃ D π) x := by
  classical
  have hG := glueDatum_connected D π hD hT
  have hR := π.refine₃_connected D hD
  have hND := hairpinShaped_nonDangling D π hD hT
  -- (1) a survivor of `refine₃ D π` survives
  have h1 : ∀ x, ¬ IsDangling (refine₃ D π) x → ¬ IsDangling (glueDatum D π) (liftSE D π x) := by
    intro x hx
    let W : (glueDatum D π).SourceEdge → Prop := fun y ↦
      (∃ x', y = liftSE D π x' ∧ ¬ IsDangling (refine₃ D π) x') ∨
        ((∃ k j, y = armSheetEdge D π k j) ∨ (∃ ε, y = newSE D π ε)) ∧
          ¬ IsDangling (glueDatum D π) y
    have hWnl : ∀ y, (∀ x', y ≠ liftSE D π x') → (W y ↔ ¬ IsDangling (glueDatum D π) y) := by
      intro y hy
      constructor
      · rintro (⟨x', h, -⟩ | ⟨-, h⟩)
        · exact absurd h (hy x')
        · exact h
      · intro h
        refine Or.inr ⟨?_, h⟩
        rcases sourceEdge_cases_glue D π y with ⟨x', rfl⟩ | ⟨ε, rfl⟩ | ⟨k, j, rfl⟩
        · exact absurd rfl (hy x')
        · exact Or.inr ⟨ε, rfl⟩
        · exact Or.inl ⟨k, j, rfl⟩
    have hWshape : HairpinShaped D π W := by
      intro k j
      rw [hWnl _ fun x' h ↦ liftSE_ne_arm D π x' k j h.symm]
      exact hND k j
    refine not_isDangling_of_witness _ W (fun z ↦ ?_) (Or.inl ⟨x, rfl, hx⟩)
    rcases sourceVertex_cases_glue D π z with ⟨x₀, rfl⟩ | ⟨v, rfl⟩ | ⟨k, j, rfl⟩
    · rw [wCount_glue_oldVertex₃ D π hWshape]
      have hlift : wCount (refine₃ D π) (fun x' ↦ W (liftSE D π x')) x₀ =
          nonDanglingValency (refine₃ D π) x₀ := by
        rw [nonDanglingValency_eq_wCount]
        apply wCount_congr
        intro x' _
        constructor
        · intro hW
          rcases hW with ⟨x'', h, hnd⟩ | ⟨hkind, -⟩
          · rw [liftSE_injective D π h]; exact hnd
          · rcases hkind with ⟨k, j, h⟩ | ⟨ε, h⟩
            · exact absurd h (liftSE_ne_arm D π _ _ _)
            · exact absurd h (liftSE_ne_newSE D π _ _)
        · intro h; exact Or.inl ⟨x', rfl, h⟩
      rw [hlift]
      by_cases hm : ∃ k, x₀ = markR₃ D π k
      · obtain ⟨k, rfl⟩ := hm
        rw [sum_mark_eq_one, markR₃, π.nonDanglingValency_markR₃ D hD hπ k]
        omega
      · push Not at hm
        rw [sum_mark_eq_zero D π hm, add_zero]
        exact DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hR x₀
    · rw [wCount_congr _ _ (W' := fun y ↦ ¬ IsDangling (glueDatum D π) y)]
      · exact wCount_nonDangling_ne_one _ hG _
      · intro y hy
        exact hWnl y fun x' h ↦ not_incident_liftSE_newVertex D π x' v (h ▸ hy)
    · rw [wCount_congr _ _ (W' := fun y ↦ ¬ IsDangling (glueDatum D π) y)]
      · exact wCount_nonDangling_ne_one _ hG _
      · intro y hy
        exact hWnl y fun x' h ↦ not_incident_liftSE_tip D π x' k j (h ▸ hy)
  -- (2) a survivor of the glued datum among the old edges survives in `refine₃ D π`
  have h2 : ∀ x, ¬ IsDangling (glueDatum D π) (liftSE D π x) → ¬ IsDangling (refine₃ D π) x := by
    intro x hx
    refine not_isDangling_of_witness _
      (fun x' ↦ ¬ IsDangling (glueDatum D π) (liftSE D π x')) (fun x₀ ↦ ?_) hx
    have hc := wCount_glue_oldVertex₃ D π hND x₀
    have hne := wCount_nonDangling_ne_one _ hG (oldVertex₃ D π x₀)
    by_cases hm : ∃ k, x₀ = markR₃ D π k
    · obtain ⟨k, rfl⟩ := hm
      rw [sum_mark_eq_one] at hc
      have hge : nonDanglingValency (refine₃ D π) (markR₃ D π k) ≤
          wCount (refine₃ D π) (fun x' ↦ ¬ IsDangling (glueDatum D π) (liftSE D π x'))
            (markR₃ D π k) := by
        rw [nonDanglingValency_eq_wCount]
        exact wCount_le_of_imp _ _ fun x' _ h ↦ h1 x' h
      have h2' : nonDanglingValency (refine₃ D π) (markR₃ D π k) = 2 :=
        π.nonDanglingValency_markR₃ D hD hπ k
      omega
    · push Not at hm
      rw [sum_mark_eq_zero D π hm, add_zero] at hc
      rw [← hc]
      exact hne
  rw [← not_iff_not]
  exact ⟨h2 x, h1 x⟩

/-- **The valency at an old vertex** of the glued datum: that of `refine₃ D π`, plus one at a
mark. -/
theorem nonDanglingValency_oldVertex₃ (hD : D.Connected) (hT : graph_connected T)
    (hπ : π.NonDangling D) (x : (refine₃ D π).SourceVertex) :
    nonDanglingValency (glueDatum D π) (oldVertex₃ D π x) =
      nonDanglingValency (refine₃ D π) x + ∑ k, if x = markR₃ D π k then 1 else 0 := by
  rw [nonDanglingValency_eq_wCount, wCount_glue_oldVertex₃ D π (hairpinShaped_nonDangling D π hD hT),
    nonDanglingValency_eq_wCount]
  congr 1
  apply wCount_congr
  intro x' _
  rw [isDangling_liftSE_iff D π hD hT hπ]

/-- The surviving new-sheet edges, as target edges of `T₃`. -/
def NewSurvives (ε : π.T₃.edges) : Prop := ¬ IsDangling (glueDatum D π) (newSE D π ε)

/-- **The valency at a new-sheet vertex**: the surviving new-sheet edges, plus one at a mark
image. -/
theorem nonDanglingValency_newVertex (hD : D.Connected) (hT : graph_connected T) (v : π.T₃.V) :
    nonDanglingValency (glueDatum D π) (newVertex D π v) =
      tCount (NewSurvives D π) v + ∑ k, if π.markVertex₃ k = v then 1 else 0 := by
  rw [nonDanglingValency_eq_wCount, wCount_glue_newVertex D π (hairpinShaped_nonDangling D π hD hT)]
  rfl

theorem wCount_le_card_filter {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (W : E.SourceEdge → Prop)
    (v : E.SourceVertex) [DecidablePred W] : wCount E W v ≤ (Finset.univ.filter W).card := by
  classical
  unfold wCount
  refine Finset.card_le_card fun e he ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact he.1

/-- **The valency over a tip** is at most two. -/
theorem nonDanglingValency_tip_le (hD : D.Connected) (hT : graph_connected T) (k : Fin 3)
    (j : Fin (d + 1)) :
    nonDanglingValency (glueDatum D π) ((glueDatum D π).sourceEndpoint (π.tipTarget k) j) ≤ 2 := by
  classical
  have hND := hairpinShaped_nonDangling D π hD hT
  rw [nonDanglingValency_eq_wCount]
  refine (wCount_le_of_imp _ (W' := fun y ↦ y = armSheetEdge D π k (π.sheet k).castSucc ∨
    y = armSheetEdge D π k (Fin.last d)) _ fun y hy hnd ↦ ?_).trans ?_
  · have hy' := incident_tip_arm_only D π k j y hy
    rw [hy'] at hnd ⊢
    rcases (hND k _).mp hnd with h | h
    · left; rw [h]
    · right; rw [h]
  · refine (wCount_le_card_filter _ _ _).trans ?_
    calc (Finset.univ.filter fun y ↦ y = armSheetEdge D π k (π.sheet k).castSucc ∨
          y = armSheetEdge D π k (Fin.last d)).card
        ≤ ({armSheetEdge D π k (π.sheet k).castSucc, armSheetEdge D π k (Fin.last d)} :
            Finset _).card := Finset.card_le_card fun y hy ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hy
      _ ≤ 2 := Finset.card_le_two

namespace Placement

variable (π : Placement T d)

/-- The three mark images, as a finset of vertices of `T₃`. -/
def markSet : Finset π.T₃.V := Finset.univ.image π.markVertex₃

theorem card_markSet : π.markSet.card = 3 := by
  rw [markSet, Finset.card_image_of_injective _ π.markVertex₃_injective]
  rfl

open Classical in
theorem sum_markVertex_eq (v : π.T₃.V) :
    (∑ k, if π.markVertex₃ k = v then 1 else 0) = if v ∈ π.markSet then 1 else 0 := by
  by_cases hv : v ∈ π.markSet
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    rw [if_pos hv, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (π.markVertex₃_injective h)
    · simp
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun k _ ↦ if_neg fun h ↦ hv ?_
    rw [← h]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem T₃_genus (hT0 : genus T = 0) : genus π.T₃ = 0 := by
  show genus (subdivTarget _ _) = 0
  rw [subdivTarget_genus, subdivTarget_genus, subdivTarget_genus, hT0]

end Placement

open Classical in
/-- **The new sheet is trivalent**: at most three survivors at a new-sheet vertex. -/
theorem nonDanglingValency_newVertex_le_three (hD : D.Connected) (hT : graph_connected T)
    (hT0 : genus T = 0) (v : π.T₃.V) :
    nonDanglingValency (glueDatum D π) (newVertex D π v) ≤ 3 := by
  have hG := glueDatum_connected D π hD hT
  rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq, ← π.card_markSet]
  refine tCount_add_le (π.T₃_connected hT) (π.T₃_genus hT0) π.markSet _ (fun u hu ↦ ?_) v
  have h := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
    (newVertex D π u)
  rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq, if_neg hu, add_zero] at h
  exact h

/-- **The glued datum is trivalent** (S2 in its general form). -/
theorem nonDanglingValency_glue_le_three (hD : D.Connected) (hT : graph_connected T)
    (hT0 : genus T = 0) (hπ : π.NonDangling D) (h3 : ∀ x, nonDanglingValency D x ≤ 3)
    (z : (glueDatum D π).SourceVertex) : nonDanglingValency (glueDatum D π) z ≤ 3 := by
  rcases sourceVertex_cases_glue D π z with ⟨x, rfl⟩ | ⟨v, rfl⟩ | ⟨k, j, rfl⟩
  · rw [nonDanglingValency_oldVertex₃ D π hD hT hπ]
    by_cases hm : ∃ k, x = markR₃ D π k
    · obtain ⟨k, rfl⟩ := hm
      rw [sum_mark_eq_one, markR₃, π.nonDanglingValency_markR₃ D hD hπ k]
    · push Not at hm
      rw [sum_mark_eq_zero D π hm, add_zero]
      exact π.refine₃_trivalent D hD h3 x
  · exact nonDanglingValency_newVertex_le_three D π hD hT hT0 v
  · exact (nonDanglingValency_tip_le D π hD hT k j).trans (by norm_num)

theorem tCount_eq_one_iff {S : CFGraph} (X : S.edges → Prop) (v : S.V) :
    tCount X v = 1 ↔ ∃ ε, X ε ∧ ε ∈ GluingDatum.incidentEdges v ∧
      ∀ ε', X ε' → ε' ∈ GluingDatum.incidentEdges v → ε' = ε := by
  classical
  unfold tCount
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩
    rw [Finset.eq_singleton_iff_unique_mem, Finset.mem_filter] at ha
    exact ⟨a, ha.1.2.1, ha.1.2.2,
      fun ε' h1 h2 ↦ ha.2 ε' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)⟩
  · rintro ⟨a, h1, h2, h3⟩
    refine ⟨a, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩, fun ε' hε' ↦ ?_⟩⟩
    rw [Finset.mem_filter] at hε'
    exact h3 ε' hε'.2.1 hε'.2.2

/-- At a vertex of valency two, a survivor has exactly one other survivor. -/
theorem exists_other_survivor {S : CFGraph} {k : ℕ} (E : GluingDatum S k) {v : E.SourceVertex}
    (hv : nonDanglingValency E v = 2) {e : E.SourceEdge} (he : ¬ IsDangling E e)
    (hinc : Incident E e v) :
    ∃ z, (¬ IsDangling E z ∧ Incident E z v) ∧ z ≠ e := by
  classical
  unfold nonDanglingValency at hv
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hv
  have hmem : ∀ z, (¬ IsDangling E z ∧ Incident E z v) ↔ z = a ∨ z = b := by
    intro z
    have := congrArg (z ∈ ·) hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, eq_iff_iff] at this
    exact this
  rcases (hmem e).mp ⟨he, hinc⟩ with rfl | rfl
  · exact ⟨b, (hmem b).mpr (Or.inr rfl), fun h ↦ hab h.symm⟩
  · exact ⟨a, (hmem a).mpr (Or.inl rfl), hab⟩

/-- **No stable path of the glued datum is a cycle** (S3 in its general form). An old stable
path runs, through old vertices of valency two (none of them a mark), along a stable path of
`refine₃ D π`, and so reaches an end of it; a hairpin ends at its mark; and a new-sheet stable
path without an end would be an edge set of the tree `T₃` without a vertex of valency one. -/
theorem hasPathEnds_glue (hD : D.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
    (hπ : π.NonDangling D) (hEnds : HasPathEnds D) : HasPathEnds (glueDatum D π) := by
  classical
  have hG := glueDatum_connected D π hD hT
  have hND := hairpinShaped_nonDangling D π hD hT
  have hhair := fun k ↦ (hairpin_not_isDangling D π hD hT k).1
  have hmarkEnd : ∀ k, IsPathEnd (glueDatum D π) (armSheetEdge D π k (π.sheet k).castSucc)
      (oldVertex₃ D π (markR₃ D π k)) := by
    intro k
    refine ⟨(incident_arm_oldVertex₃_iff D π k _ _).mpr
      ⟨rfl, π.sheet k, rfl, SheetPartition.rel_repr_left _ _⟩, ?_⟩
    rw [nonDanglingValency_oldVertex₃ D π hD hT hπ, sum_mark_eq_one, markR₃,
      π.nonDanglingValency_markR₃ D hD hπ k]
    omega
  intro y
  by_contra hno
  push Not at hno
  have htouch : ∀ (f : NonDanglingEdge (glueDatum D π)) (v), f.stablePath = y.stablePath →
      Incident (glueDatum D π) f.1 v → nonDanglingValency (glueDatum D π) v = 2 := by
    intro f v hf hinc
    by_contra hne
    exact hno f v hf ⟨hinc, hne⟩
  have hnoHair : ∀ k, NonDanglingEdge.stablePath (⟨_, hhair k⟩ : NonDanglingEdge (glueDatum D π)) ≠
      y.stablePath := fun k hk ↦ hno _ _ hk (hmarkEnd k)
  rcases sourceEdge_cases_glue D π y.1 with ⟨x, hx⟩ | ⟨ε, hε⟩ | ⟨k, j, hkj⟩
  · -- an old stable path
    have hx_nd : ¬ IsDangling (refine₃ D π) x :=
      (isDangling_liftSE_iff D π hD hT hπ x).not.mp (by rw [← hx]; exact y.2)
    obtain ⟨x', u, hx', hend⟩ := (π.refine₃_hasPathEnds D hD hEnds) ⟨x, hx_nd⟩
    let Q : NonDanglingEdge (refine₃ D π) → Prop := fun x'' ↦
      ∃ h : ¬ IsDangling (glueDatum D π) (liftSE D π x''.1),
        NonDanglingEdge.stablePath (⟨_, h⟩ : NonDanglingEdge (glueDatum D π)) = y.stablePath
    have hQ0 : Q ⟨x, hx_nd⟩ := by
      refine ⟨by rw [← hx]; exact y.2, ?_⟩
      have : (⟨liftSE D π x, by rw [← hx]; exact y.2⟩ : NonDanglingEdge (glueDatum D π)) = y :=
        Subtype.ext hx.symm
      rw [this]
    have hclosed : ∀ a b, Consecutive (refine₃ D π) a b → Q a → Q b := by
      rintro a b ⟨hab, u, ha, hb, -⟩ ⟨ha', hpa⟩
      have hb' : ¬ IsDangling (glueDatum D π) (liftSE D π b.1) :=
        (isDangling_liftSE_iff D π hD hT hπ b.1).not.mpr b.2
      have hinca := (incident_liftSE_oldVertex₃ D π a.1 u).mpr ha
      have hincb := (incident_liftSE_oldVertex₃ D π b.1 u).mpr hb
      have hval := htouch ⟨_, ha'⟩ _ hpa hinca
      refine ⟨hb', ?_⟩
      rw [← hpa]
      symm
      apply stablePath_eq_of_consecutive
      exact ⟨fun h ↦ hab (Subtype.ext (liftSE_injective D π (congrArg Subtype.val h))), _,
        hinca, hincb, hval⟩
    obtain ⟨h', hp'⟩ := (eqvGen_iff_of_closed hclosed ((stablePath_eq_iff _ _).mp hx')).mpr hQ0
    apply hno ⟨_, h'⟩ (oldVertex₃ D π u) hp'
    refine ⟨(incident_liftSE_oldVertex₃ D π x'.1 u).mpr hend.1, ?_⟩
    rw [nonDanglingValency_oldVertex₃ D π hD hT hπ]
    by_cases hm : ∃ k, u = markR₃ D π k
    · obtain ⟨k, rfl⟩ := hm
      rw [sum_mark_eq_one, markR₃, π.nonDanglingValency_markR₃ D hD hπ k]
      omega
    · push Not at hm
      rw [sum_mark_eq_zero D π hm, add_zero]
      exact hend.2
  · -- a new-sheet stable path
    let Y : π.T₃.edges → Prop := fun ε' ↦ ∃ h : NewSurvives D π ε',
      NonDanglingEdge.stablePath (⟨newSE D π ε', h⟩ : NonDanglingEdge (glueDatum D π)) = y.stablePath
    have hYε : Y ε := by
      refine ⟨by show ¬ _; rw [← hε]; exact y.2, ?_⟩
      have : (⟨newSE D π ε, by rw [← hε]; exact y.2⟩ : NonDanglingEdge (glueDatum D π)) = y :=
        Subtype.ext hε.symm
      rw [this]
    refine not_of_tCount_ne_one (π.T₃_connected hT) (π.T₃_genus hT0) Y (fun u hu ↦ ?_) ε hYε
    obtain ⟨ε', ⟨hs', hpath'⟩, hε'inc, huniq⟩ := (tCount_eq_one_iff Y u).mp hu
    have hinc' := (incident_newSE_newVertex D π ε' u).mpr hε'inc
    have hval := htouch ⟨_, hs'⟩ _ hpath' hinc'
    obtain ⟨z, hz, hzne⟩ := exists_other_survivor _ hval hs' hinc'
    have hcons : Consecutive (glueDatum D π) ⟨_, hs'⟩ ⟨z, hz.1⟩ :=
      ⟨fun h ↦ hzne (congrArg Subtype.val h).symm, _, hinc', hz.2, hval⟩
    have hzpath : NonDanglingEdge.stablePath (⟨z, hz.1⟩ : NonDanglingEdge (glueDatum D π)) = y.stablePath :=
      (stablePath_eq_of_consecutive hcons).symm.trans hpath'
    rcases sourceEdge_cases_glue D π z with ⟨x, rfl⟩ | ⟨ε'', rfl⟩ | ⟨k, j, rfl⟩
    · exact not_incident_liftSE_newVertex D π x u hz.2
    · exact hzne (by
        rw [huniq ε'' ⟨hz.1, hzpath⟩ ((incident_newSE_newVertex D π ε'' u).mp hz.2)])
    · obtain ⟨-, rfl⟩ := (incident_arm_newVertex_iff D π k j u).mp hz.2
      apply hnoHair k
      rw [stablePath_hairpin D π hG k (hhair k) ((hairpin_not_isDangling D π hD hT k).2)]
      exact hzpath
  · -- a hairpin
    have hy : ¬ IsDangling (glueDatum D π) (armSheetEdge D π k j) := by rw [← hkj]; exact y.2
    rcases (hND k j).mp hy with rfl | rfl
    · apply hnoHair k
      have : (⟨_, hhair k⟩ : NonDanglingEdge (glueDatum D π)) = y := Subtype.ext hkj.symm
      rw [this]
    · apply hnoHair k
      rw [stablePath_hairpin D π hG k (hhair k) hy]
      have : (⟨_, hy⟩ : NonDanglingEdge (glueDatum D π)) = y := Subtype.ext hkj.symm
      rw [this]

theorem tCount_congr {S : CFGraph} {X X' : S.edges → Prop} {v : S.V}
    (h : ∀ ε ∈ GluingDatum.incidentEdges v, (X ε ↔ X' ε)) : tCount X v = tCount X' v := by
  classical
  unfold tCount
  congr 1
  ext ε
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨a, b⟩ ↦ ⟨(h ε b).mp a, b⟩, fun ⟨a, b⟩ ↦ ⟨(h ε b).mpr a, b⟩⟩

theorem tCount_eq_zero {S : CFGraph} {X : S.edges → Prop} {v : S.V}
    (h : ∀ ε ∈ GluingDatum.incidentEdges v, ¬ X ε) : tCount X v = 0 := by
  classical
  unfold tCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ε - ⟨hX, hε⟩
  exact h ε hε hX

open DraismaVargas.LocalCases.StablePathCount (endCount incidenceCount incidenceCount_pos_iff) in
/-- With exactly two ends, a stable path meets no third vertex of valency other than two. -/
theorem incidenceCount_eq_zero_of_two_ends {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    {C : StablePath E} (h2 : endCount E C = 2) {a b : E.SourceVertex} (hab : a ≠ b)
    (ha : nonDanglingValency E a ≠ 2) (hb : nonDanglingValency E b ≠ 2)
    (hia : 0 < incidenceCount E a C) (hib : 0 < incidenceCount E b C)
    {w : E.SourceVertex} (hw : nonDanglingValency E w ≠ 2) (hwa : w ≠ a) (hwb : w ≠ b) :
    incidenceCount E w C = 0 := by
  classical
  by_contra hne
  have hiw : 0 < incidenceCount E w C := Nat.pos_of_ne_zero hne
  unfold endCount at h2
  rw [Finset.sum_filter] at h2
  have hle := Finset.sum_le_sum_of_subset (Finset.subset_univ ({a, b, w} : Finset E.SourceVertex))
    (f := fun v ↦ if ¬ nonDanglingValency E v = 2 then incidenceCount E v C else 0)
  rw [Finset.sum_insert (by simp [hab, Ne.symm hwa]), Finset.sum_insert (by simp [Ne.symm hwb]),
    Finset.sum_singleton, if_pos ha, if_pos hb, if_pos hw] at hle
  omega

theorem fin3_third : ∀ k j : Fin 3, k ≠ j → ∃ l, l ≠ k ∧ l ≠ j := by decide

theorem fin3_cases : ∀ i k j l : Fin 3, k ≠ j → l ≠ k → l ≠ j → i ≠ l → i = k ∨ i = j := by
  decide

open DraismaVargas.LocalCases.StablePathCount (endCount incidenceCount incidenceCount_pos_iff
  endCount_eq_two) in
/-- **The three hairpins lie on three stable paths** (S4 in its general form). A stable path
has exactly two ends; one through two hairpins has them at the two marks, so it continues
through every other vertex it meets, and its new-sheet edges take up every surviving
new-sheet edge at the vertices they meet. It misses the third mark image, so the other surviving
new-sheet edges form an edge set of `T₃` without valency one off the third mark image, yet with
an edge there: impossible in a tree (`tCount_add_le`). -/
theorem hairpinPath_ne_glue (hD : D.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
    (hπ : π.NonDangling D) (hEnds : HasPathEnds D) {k j : Fin 3} (hkj : k ≠ j) :
    NonDanglingEdge.stablePath (⟨_, (hairpin_not_isDangling D π hD hT k).1⟩ :
        NonDanglingEdge (glueDatum D π)) ≠
      NonDanglingEdge.stablePath (⟨_, (hairpin_not_isDangling D π hD hT j).1⟩ :
        NonDanglingEdge (glueDatum D π)) := by
  classical
  intro hC
  have hG := glueDatum_connected D π hD hT
  have hEndsG := hasPathEnds_glue D π hD hT hT0 hπ hEnds
  have hhair := fun i ↦ (hairpin_not_isDangling D π hD hT i).1
  have hhairL := fun i ↦ (hairpin_not_isDangling D π hD hT i).2
  have hpathL : ∀ i, NonDanglingEdge.stablePath (⟨_, hhairL i⟩ : NonDanglingEdge (glueDatum D π)) =
      NonDanglingEdge.stablePath (⟨_, hhair i⟩ : NonDanglingEdge (glueDatum D π)) := fun i ↦
    (stablePath_hairpin D π hG i (hhair i) (hhairL i)).symm
  have hmarkVal : ∀ i, nonDanglingValency (glueDatum D π) (oldVertex₃ D π (markR₃ D π i)) = 3 := by
    intro i
    rw [nonDanglingValency_oldVertex₃ D π hD hT hπ, sum_mark_eq_one, markR₃,
      π.nonDanglingValency_markR₃ D hD hπ i]
  have hmarkInc : ∀ i, Incident (glueDatum D π) (armSheetEdge D π i (π.sheet i).castSucc)
      (oldVertex₃ D π (markR₃ D π i)) := fun i ↦
    (incident_arm_oldVertex₃_iff D π i _ _).mpr ⟨rfl, π.sheet i, rfl, SheetPartition.rel_repr_left _ _⟩
  set C := NonDanglingEdge.stablePath (⟨_, hhair k⟩ : NonDanglingEdge (glueDatum D π)) with hCdef
  have h2 := endCount_eq_two _ (DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one
    _ hG) hEndsG C
  have hab : oldVertex₃ D π (markR₃ D π k) ≠ oldVertex₃ D π (markR₃ D π j) := fun h ↦
    hkj (markR₃_injective D π (oldVertex₃_injective D π h))
  have hia : 0 < incidenceCount (glueDatum D π) (oldVertex₃ D π (markR₃ D π k)) C :=
    (incidenceCount_pos_iff _ _ _).mpr ⟨⟨_, hhair k⟩, hmarkInc k, rfl⟩
  have hib : 0 < incidenceCount (glueDatum D π) (oldVertex₃ D π (markR₃ D π j)) C :=
    (incidenceCount_pos_iff _ _ _).mpr ⟨⟨_, hhair j⟩, hmarkInc j, hC.symm⟩
  have hnoThird : ∀ w, nonDanglingValency (glueDatum D π) w ≠ 2 →
      w ≠ oldVertex₃ D π (markR₃ D π k) → w ≠ oldVertex₃ D π (markR₃ D π j) →
      ∀ e : NonDanglingEdge (glueDatum D π), e.stablePath = C → ¬ Incident (glueDatum D π) e.1 w := by
    intro w hw hwa hwb e he hinc
    have h0 := incidenceCount_eq_zero_of_two_ends _ h2 hab (by rw [hmarkVal]; omega)
      (by rw [hmarkVal]; omega) hia hib hw hwa hwb
    have hpos : 0 < incidenceCount (glueDatum D π) w C :=
      (incidenceCount_pos_iff _ _ _).mpr ⟨e, hinc, he⟩
    omega
  have hclos : ∀ v (e : NonDanglingEdge (glueDatum D π)), e.stablePath = C →
      Incident (glueDatum D π) e.1 v → v ≠ oldVertex₃ D π (markR₃ D π k) →
      v ≠ oldVertex₃ D π (markR₃ D π j) → ∀ z : NonDanglingEdge (glueDatum D π),
      Incident (glueDatum D π) z.1 v → z.stablePath = C := by
    intro v e he hinc hva hvb z hz
    have hv2 : nonDanglingValency (glueDatum D π) v = 2 := by
      by_contra hne
      exact hnoThird v hne hva hvb e he hinc
    by_cases hze : z = e
    · rw [hze, he]
    · rw [← he]
      symm
      exact stablePath_eq_of_consecutive ⟨fun h ↦ hze h.symm, v, hinc, hz, hv2⟩
  have hna : ∀ u i, newVertex D π u ≠ oldVertex₃ D π (markR₃ D π i) := fun u i h ↦
    oldVertex₃_ne_newVertex D π _ _ h.symm
  let Y : π.T₃.edges → Prop := fun ε ↦ ∃ h : NewSurvives D π ε,
    NonDanglingEdge.stablePath (⟨newSE D π ε, h⟩ : NonDanglingEdge (glueDatum D π)) = C
  let Touched : π.T₃.V → Prop := fun u ↦ ∃ e : NonDanglingEdge (glueDatum D π), e.stablePath = C ∧
    Incident (glueDatum D π) e.1 (newVertex D π u)
  have hall : ∀ u, Touched u → ∀ ε, NewSurvives D π ε → ε ∈ GluingDatum.incidentEdges u → Y ε := by
    rintro u ⟨e, he, hinc⟩ ε hX hε
    exact ⟨hX, hclos _ e he hinc (hna u k) (hna u j) ⟨_, hX⟩
      ((incident_newSE_newVertex D π ε u).mpr hε)⟩
  have htouchMark : ∀ i, (i = k ∨ i = j) → Touched (π.markVertex₃ i) := by
    rintro i hi
    refine ⟨⟨_, hhairL i⟩, ?_, (incident_arm_newVertex_iff D π i _ _).mpr ⟨rfl, rfl⟩⟩
    rcases hi with rfl | rfl
    · exact hpathL i
    · exact (hpathL i).trans hC.symm
  obtain ⟨l, hlk, hlj⟩ := fin3_third k j hkj
  have hnl : ∀ ε, Y ε → ε ∉ GluingDatum.incidentEdges (π.markVertex₃ l) := by
    rintro ε ⟨hX, hY⟩ hε
    have h1 := hclos _ ⟨_, hX⟩ hY ((incident_newSE_newVertex D π ε _).mpr hε) (hna _ k) (hna _ j)
      ⟨_, hhairL l⟩ ((incident_arm_newVertex_iff D π l _ _).mpr ⟨rfl, rfl⟩)
    rw [hpathL l] at h1
    refine hnoThird _ (by rw [hmarkVal]; omega) ?_ ?_ ⟨_, hhair l⟩ h1 (hmarkInc l)
    · intro h; exact hlk (markR₃_injective D π (oldVertex₃_injective D π h))
    · intro h; exact hlj (markR₃_injective D π (oldVertex₃_injective D π h))
  let Z : π.T₃.edges → Prop := fun ε ↦ NewSurvives D π ε ∧ ¬ Y ε
  have hZ : ∀ u ∉ ({π.markVertex₃ l} : Finset π.T₃.V), tCount Z u ≠ 1 := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    by_cases ht : Touched u
    · rw [tCount_eq_zero fun ε hε hZε ↦ hZε.2 (hall u ht ε hZε.1 hε)]
      omega
    · have huM : u ∉ π.markSet := by
        intro hm
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
        exact ht (htouchMark i (fin3_cases i k j l hkj hlk hlj (fun h ↦ hu (h ▸ rfl))))
      have hZX : tCount Z u = tCount (NewSurvives D π) u := tCount_congr fun ε hε ↦
        ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun hY ↦ ht ⟨⟨_, hY.1⟩, hY.2,
          (incident_newSE_newVertex D π ε u).mpr hε⟩⟩⟩
      rw [hZX]
      have := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
        (newVertex D π u)
      rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq, if_neg huM, add_zero] at this
      exact this
  have hle := tCount_add_le (π.T₃_connected hT) (π.T₃_genus hT0) {π.markVertex₃ l} Z hZ
    (π.markVertex₃ l)
  rw [if_pos (Finset.mem_singleton_self _), Finset.card_singleton] at hle
  have hZl : tCount Z (π.markVertex₃ l) = tCount (NewSurvives D π) (π.markVertex₃ l) :=
    tCount_congr fun ε hε ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun hY ↦ hnl ε hY hε⟩⟩
  have hXl := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
    (newVertex D π (π.markVertex₃ l))
  rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq,
    if_pos (show π.markVertex₃ l ∈ π.markSet from
      Finset.mem_image_of_mem _ (Finset.mem_univ _))] at hXl
  omega

/-! #### The number of stable paths -/

open DraismaVargas.LocalCases.Trivalence (stableVertices mem_stableVertices) in
/-- **The stable-path count of a trivalent datum**: `2 · #paths = 3 · #branch vertices`. -/
theorem two_mul_card_stablePath_eq {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    (hE : E.Connected) (hEnds : HasPathEnds E) (h3 : ∀ v, nonDanglingValency E v ≤ 3) :
    2 * Fintype.card (StablePath E) = 3 * (stableVertices E).card := by
  rw [← DraismaVargas.LocalCases.StablePathCount.sum_stableValency_eq_two_mul_card_stablePath E
    (DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one E hE) hEnds]
  rw [Finset.sum_congr rfl fun v hv ↦
    (le_antisymm (h3 v) ((mem_stableVertices E v).mp hv) : nonDanglingValency E v = 3)]
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

open DraismaVargas.LocalCases.Trivalence (stableVertices mem_stableVertices) in
/-- A refinement has the branch vertices of `D`. -/
theorem Refine.card_stableVertices (D : GluingDatum T d) (t : T.edges) (hD : D.Connected) :
    (stableVertices (refineDatum D t)).card = (stableVertices D).card := by
  classical
  have h : stableVertices (refineDatum D t) =
      (stableVertices D).map ⟨Refine.oldSV D t, Refine.oldSV_injective D t⟩ := by
    ext z
    rw [mem_stableVertices, Finset.mem_map]
    constructor
    · intro hz
      rcases Refine.sourceVertex_cases D t z with ⟨x, rfl⟩ | ⟨i, hi, rfl⟩
      · rw [Refine.nonDanglingValency_oldSV D t hD] at hz
        exact ⟨x, (mem_stableVertices D x).mpr hz, rfl⟩
      · rw [Refine.nonDanglingValency_freshSV D t hD] at hz
        split_ifs at hz <;> omega
    · rintro ⟨x, hx, rfl⟩
      rw [Function.Embedding.coeFn_mk, Refine.nonDanglingValency_oldSV D t hD]
      exact (mem_stableVertices D x).mp hx
  rw [h, Finset.card_map]

open DraismaVargas.LocalCases.Trivalence (stableVertices mem_stableVertices) in
theorem Placement.card_stableVertices_refine₃ (hD : D.Connected) :
    (stableVertices (refine₃ D π)).card = (stableVertices D).card := by
  rw [Refine.card_stableVertices _ _ (π.refine₂_connected D hD),
    Refine.card_stableVertices _ _ (π.refine₁_connected D hD), Refine.card_stableVertices _ _ hD]

open Classical in
open DraismaVargas.LocalCases.Trivalence (stableVertices mem_stableVertices) in
/-- **The branch vertices of the glued datum**: those of `D`, the three marks and the median. -/
theorem card_stableVertices_glue (hD : D.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
    (hπ : π.NonDangling D) :
    (stableVertices (glueDatum D π)).card = (stableVertices D).card + 4 := by
  have hG := glueDatum_connected D π hD hT
  -- branch vertices are old or new
  have hsplit : stableVertices (glueDatum D π) =
      ((Finset.univ.filter fun x ↦ 3 ≤ nonDanglingValency (glueDatum D π) (oldVertex₃ D π x)).map
        ⟨oldVertex₃ D π, oldVertex₃_injective D π⟩) ∪
      ((Finset.univ.filter fun v ↦ 3 ≤ nonDanglingValency (glueDatum D π) (newVertex D π v)).map
        ⟨newVertex D π, newVertex_injective D π⟩) := by
    ext z
    simp only [mem_stableVertices, Finset.mem_union, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · intro hz
      rcases sourceVertex_cases_glue D π z with ⟨x, rfl⟩ | ⟨v, rfl⟩ | ⟨k, j, rfl⟩
      · exact Or.inl ⟨x, hz, rfl⟩
      · exact Or.inr ⟨v, hz, rfl⟩
      · have := nonDanglingValency_tip_le D π hD hT k j
        omega
    · rintro (⟨x, hx, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact hx
      · exact hv
  have hdisj : Disjoint
      ((Finset.univ.filter fun x ↦ 3 ≤ nonDanglingValency (glueDatum D π) (oldVertex₃ D π x)).map
        ⟨oldVertex₃ D π, oldVertex₃_injective D π⟩)
      ((Finset.univ.filter fun v ↦ 3 ≤ nonDanglingValency (glueDatum D π) (newVertex D π v)).map
        ⟨newVertex D π, newVertex_injective D π⟩) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hz'
    exact oldVertex₃_ne_newVertex D π x v hv.symm
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
  -- the old branch vertices: those of `refine₃ D π`, and the three marks
  have hold : (Finset.univ.filter fun x ↦
      3 ≤ nonDanglingValency (glueDatum D π) (oldVertex₃ D π x)).card =
        (stableVertices (refine₃ D π)).card + 3 := by
    rw [Finset.card_filter, stableVertices, Finset.card_filter]
    have hpt : ∀ x : (refine₃ D π).SourceVertex,
        (if 3 ≤ nonDanglingValency (glueDatum D π) (oldVertex₃ D π x) then 1 else 0) =
          (if 3 ≤ nonDanglingValency (refine₃ D π) x then 1 else 0) +
            ∑ k, if x = markR₃ D π k then 1 else 0 := by
      intro x
      rw [nonDanglingValency_oldVertex₃ D π hD hT hπ]
      by_cases hm : ∃ k, x = markR₃ D π k
      · obtain ⟨k, rfl⟩ := hm
        rw [sum_mark_eq_one, markR₃, π.nonDanglingValency_markR₃ D hD hπ k]
        simp
      · push Not at hm
        rw [sum_mark_eq_zero D π hm, add_zero, add_zero]
    rw [Finset.sum_congr rfl fun x _ ↦ hpt x, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    rw [Finset.sum_congr rfl fun k _ ↦ Finset.sum_ite_eq' Finset.univ (markR₃ D π k) fun _ ↦ 1]
    simp
  -- the new branch vertex: the median
  have hnew : (Finset.univ.filter fun v ↦
      3 ≤ nonDanglingValency (glueDatum D π) (newVertex D π v)).card = 1 := by
    have hX : ∀ u ∉ π.markSet, tCount (NewSurvives D π) u ≠ 1 := by
      intro u hu
      have h := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
        (newVertex D π u)
      rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq, if_neg hu, add_zero] at h
      exact h
    have hXM : ∀ u ∈ π.markSet, tCount (NewSurvives D π) u ≠ 0 := by
      intro u hu
      have h := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
        (newVertex D π u)
      rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq, if_pos hu] at h
      omega
    have h := card_branch_eq_one (π.T₃_connected hT) (π.T₃_genus hT0) π.markSet π.card_markSet
      (NewSurvives D π) hX hXM
    refine Eq.trans ?_ h
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq]
  rw [hold, hnew, π.card_stableVertices_refine₃ D hD]

/-- **The glued datum has `#paths(D) + 6` stable paths** (S1 in its general form). -/
theorem card_stablePath_glue (hD : D.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
    (hπ : π.NonDangling D) (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D) :
    Fintype.card (StablePath (glueDatum D π)) = Fintype.card (StablePath D) + 6 := by
  have hG := glueDatum_connected D π hD hT
  have h1 := two_mul_card_stablePath_eq (glueDatum D π) hG (hasPathEnds_glue D π hD hT hT0 hπ hEnds)
    (nonDanglingValency_glue_le_three D π hD hT hT0 hπ h3)
  have h2 := two_mul_card_stablePath_eq D hD hEnds h3
  rw [card_stableVertices_glue D π hD hT hT0 hπ] at h1
  omega

end GlueDangling


/-! ### Toward S5: one refinement of a class matrix

The determinant induction of §5.3 runs one mark at a time. `clsMatrix` is the length
matrix of an arbitrary labelling `cls` of the surviving edges of a datum by an index type (for a
stable labelling, the stable path of each edge). Refining at a target edge `t` and labelling the
refinement by `Option ι` so that one class `h = cls f` is split in two at a surviving source edge
`f` over `t`, and nothing else changes (`SplitsAt`), multiplies `|det|` by `1 / a`, with `a` the
index of `f` (`abs_det_clsMatrix_refine`, from `abs_det_refine`). -/

section ClassMatrix

open DraismaVargas.LocalCases.W4StableSource

open Classical in
/-- The length matrix of a labelling of the surviving edges by classes. -/
noncomputable def clsMatrix (E : GluingDatum T d) {ι : Type*} [DecidableEq ι]
    (cls : NonDanglingEdge E → ι) (col : ι ≃ T.edges) : Matrix ι ι ℚ := fun r c ↦
  ∑ x : NonDanglingEdge E, if cls x = r ∧ x.1.1.1 = col c then (1 : ℚ) / E.sourceEdgeIndex x.1
    else 0

namespace Refine

variable (D : GluingDatum T d) (t : T.edges)

theorem sourceEdgeIndex_eq (y : (refineDatum D t).SourceEdge) :
    (refineDatum D t).sourceEdgeIndex y = D.sourceEdgeIndex (parentSE D t y) := by
  unfold GluingDatum.sourceEdgeIndex
  rw [refineDatum_edgePartition]
  rfl

/-- The surviving parent of a surviving edge of the refinement. -/
def parentND (hD : D.Connected) (y : NonDanglingEdge (refineDatum D t)) : NonDanglingEdge D :=
  ⟨parentSE D t y.1, (isDangling_iff D t hD y.1).not.mp y.2⟩

/-- The piece of a source edge over the occurrence `some`. -/
def someHalf (x : D.SourceEdge) : (refineDatum D t).SourceEdge :=
  ⟨(subdivOcc T t (some x.1.1), x.1.2), by rw [refineDatum_edgePartition_some]; exact x.2⟩

/-- The half over the new occurrence `none` of a source edge over `t`. -/
def noneHalf (x : D.SourceEdge) : (refineDatum D t).SourceEdge :=
  ⟨(subdivOcc T t none, (D.edgePartition t).repr x.1.2), by
    rw [refineDatum_edgePartition_none]; exact SheetPartition.repr_idem _ _⟩

theorem parentSE_someHalf (x : D.SourceEdge) : parentSE D t (someHalf D t x) = x :=
  Subtype.ext (Prod.ext (parentT_some _ _) rfl)

theorem parentSE_noneHalf {x : D.SourceEdge} (hx : x.1.1 = t) :
    parentSE D t (noneHalf D t x) = x := by
  have h2 := x.2
  rw [hx] at h2
  exact Subtype.ext (Prod.ext ((parentT_none t).trans hx.symm) h2)

theorem not_isDangling_someHalf (hD : D.Connected) (x : NonDanglingEdge D) :
    ¬ IsDangling (refineDatum D t) (someHalf D t x.1) :=
  (isDangling_iff D t hD _).not.mpr (by rw [parentSE_someHalf]; exact x.2)

theorem not_isDangling_noneHalf (hD : D.Connected) {x : NonDanglingEdge D} (hx : x.1.1.1 = t) :
    ¬ IsDangling (refineDatum D t) (noneHalf D t x.1) :=
  (isDangling_iff D t hD _).not.mpr (by rw [parentSE_noneHalf D t hx]; exact x.2)

/-- The surviving `some`-piece of a surviving edge. -/
def someHalfND (hD : D.Connected) (x : NonDanglingEdge D) : NonDanglingEdge (refineDatum D t) :=
  ⟨_, not_isDangling_someHalf D t hD x⟩

/-- The surviving `none`-half of a surviving edge, made total by the half of its sheet over `t`. -/
noncomputable def noneHalfND (hD : D.Connected) (x : NonDanglingEdge D) :
    NonDanglingEdge (refineDatum D t) := by
  classical
  exact if hx : x.1.1.1 = t then ⟨_, not_isDangling_noneHalf D t hD hx⟩ else someHalfND D t hD x

theorem noneHalfND_val (hD : D.Connected) {x : NonDanglingEdge D} (hx : x.1.1.1 = t) :
    (noneHalfND D t hD x).1 = noneHalf D t x.1 := by
  simp [noneHalfND, hx]

open Classical in
/-- **Sums over the `some`-pieces** are sums over the surviving edges of `D`. -/
theorem sum_over_some (hD : D.Connected) (c : T.edges)
    (g : NonDanglingEdge (refineDatum D t) → ℚ) :
    (∑ y : NonDanglingEdge (refineDatum D t), if y.1.1.1 = subdivOcc T t (some c) then g y else 0) =
      ∑ x : NonDanglingEdge D, if x.1.1.1 = c then g (someHalfND D t hD x) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (parentND D t hD) (someHalfND D t hD) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    show parentT t y.1.1.1 = c
    rw [hy, parentT_some]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    show subdivOcc T t (some x.1.1.1) = _
    rw [hx]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    apply Subtype.ext
    apply Subtype.ext
    show (subdivOcc T t (some (parentT t y.1.1.1)), y.1.1.2) = y.1.1
    rw [hy, parentT_some]
    exact Prod.ext hy.symm rfl
  · intro x _
    apply Subtype.ext
    exact parentSE_someHalf D t x.1
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    show y.1.1 = (subdivOcc T t (some (parentT t y.1.1.1)), y.1.1.2)
    rw [hy, parentT_some]
    exact Prod.ext hy rfl

open Classical in
/-- **Sums over the new halves** are sums over the surviving edges of `D` over `t`. -/
theorem sum_over_none (hD : D.Connected) (g : NonDanglingEdge (refineDatum D t) → ℚ) :
    (∑ y : NonDanglingEdge (refineDatum D t), if y.1.1.1 = subdivOcc T t none then g y else 0) =
      ∑ x : NonDanglingEdge D, if x.1.1.1 = t then g (noneHalfND D t hD x) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (parentND D t hD) (noneHalfND D t hD) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    show parentT t y.1.1.1 = t
    rw [hy, parentT_none]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [noneHalfND_val D t hD hx]
    rfl
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hp : (parentND D t hD y).1.1.1 = t := by
      show parentT t y.1.1.1 = t
      rw [hy, parentT_none]
    apply Subtype.ext
    rw [noneHalfND_val D t hD hp]
    apply Subtype.ext
    have hyy := y.1.2
    rw [refineDatum_edgePartition, hy, parentT_none] at hyy
    show (subdivOcc T t none, (D.edgePartition t).repr y.1.1.2) = y.1.1
    rw [hyy, ← hy]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply Subtype.ext
    show parentSE D t (noneHalfND D t hD x).1 = x.1
    rw [noneHalfND_val D t hD hx, parentSE_noneHalf D t hx]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hp : (parentND D t hD y).1.1.1 = t := by
      show parentT t y.1.1.1 = t
      rw [hy, parentT_none]
    congr 1
    apply Subtype.ext
    rw [noneHalfND_val D t hD hp]
    apply Subtype.ext
    have hyy := y.1.2
    rw [refineDatum_edgePartition, hy, parentT_none] at hyy
    show y.1.1 = (subdivOcc T t none, (D.edgePartition t).repr y.1.1.2)
    rw [hyy, ← hy]

end Refine

/-- **A refined labelling that splits one class at `f`** and changes nothing else: every
surviving edge keeps the class of its parent, except that some edges of the class `cls f` move to
the new class `none`; the two halves of `f` are on different sides; and the two halves of every
other surviving edge over `t` stay together. -/
structure SplitsAt (D : GluingDatum T d) (t : T.edges) (hD : D.Connected) {ι : Type*}
    (cls : NonDanglingEdge D → ι) (cls' : NonDanglingEdge (refineDatum D t) → Option ι)
    (f : NonDanglingEdge D) : Prop where
  over_t : f.1.1.1 = t
  parent : ∀ y, cls' y = some (cls (Refine.parentND D t hD y)) ∨
    (cls (Refine.parentND D t hD y) = cls f ∧ cls' y = none)
  split : cls' (Refine.someHalfND D t hD f) ≠ cls' (Refine.noneHalfND D t hD f)
  others : ∀ f' : NonDanglingEdge D, f'.1.1.1 = t → f' ≠ f →
    cls' (Refine.someHalfND D t hD f') = cls' (Refine.noneHalfND D t hD f')

open Classical in
/-- **One refinement of a class matrix** (§5.3): splitting the class
`cls f` at the surviving edge `f` over `t` multiplies `|det|` by `1 / a`, `a` the index of `f`.
Every other class passes over the two halves of `t` alike, the two pieces of `cls f` together
are the old row, and they differ on the halves only through the halves of `f`
(`abs_det_refine`). -/
theorem abs_det_clsMatrix_refine (D : GluingDatum T d) (t : T.edges) (hD : D.Connected)
    {ι : Type} [Fintype ι] [DecidableEq ι] (cls : NonDanglingEdge D → ι) (col : ι ≃ T.edges)
    (cls' : NonDanglingEdge (refineDatum D t) → Option ι) (f : NonDanglingEdge D)
    (hs : SplitsAt D t hD cls cls' f) :
    |(clsMatrix (refineDatum D t) cls' ((Equiv.optionCongr col).trans (subdivOcc T t))).det| *
        D.sourceEdgeIndex f.1 = |(clsMatrix D cls col).det| := by
  set col' := (Equiv.optionCongr col).trans (subdivOcc T t) with hcol'
  set M := clsMatrix (refineDatum D t) cls' col' with hMdef
  set B := clsMatrix D cls col with hBdef
  set w : NonDanglingEdge D → ℚ := fun x ↦ (1 : ℚ) / D.sourceEdgeIndex x.1 with hw
  set sH := Refine.someHalfND D t hD with hsH
  set nH := Refine.noneHalfND D t hD with hnH
  have hpar_s : ∀ x, Refine.parentND D t hD (sH x) = x := fun x ↦
    Subtype.ext (Refine.parentSE_someHalf D t x.1)
  have hpar_n : ∀ x : NonDanglingEdge D, x.1.1.1 = t → Refine.parentND D t hD (nH x) = x := by
    intro x hx
    apply Subtype.ext
    show Refine.parentSE D t (nH x).1 = x.1
    rw [hnH, Refine.noneHalfND_val D t hD hx, Refine.parentSE_noneHalf D t hx]
  have hidx_s : ∀ x, (refineDatum D t).sourceEdgeIndex (sH x).1 = D.sourceEdgeIndex x.1 := by
    intro x
    rw [Refine.sourceEdgeIndex_eq]
    exact congrArg D.sourceEdgeIndex (Refine.parentSE_someHalf D t x.1)
  have hidx_n : ∀ x : NonDanglingEdge D, x.1.1.1 = t →
      (refineDatum D t).sourceEdgeIndex (nH x).1 = D.sourceEdgeIndex x.1 := by
    intro x hx
    rw [Refine.sourceEdgeIndex_eq, hnH, Refine.noneHalfND_val D t hD hx,
      Refine.parentSE_noneHalf D t hx]
  -- the entries of `M`, as sums over the surviving edges of `D`
  have hM_some : ∀ r' c, M r' (some c) = ∑ x : NonDanglingEdge D,
      if x.1.1.1 = col c then (if cls' (sH x) = r' then w x else 0) else 0 := by
    intro r' c
    show (∑ y : NonDanglingEdge (refineDatum D t), if cls' y = r' ∧ y.1.1.1 = col' (some c) then
      (1 : ℚ) / (refineDatum D t).sourceEdgeIndex y.1 else 0) = _
    have hc : col' (some c) = subdivOcc T t (some (col c)) := rfl
    rw [hc]
    have hsplit : ∀ y : NonDanglingEdge (refineDatum D t),
        (if cls' y = r' ∧ y.1.1.1 = subdivOcc T t (some (col c)) then
          (1 : ℚ) / (refineDatum D t).sourceEdgeIndex y.1 else 0) =
        if y.1.1.1 = subdivOcc T t (some (col c)) then
          (if cls' y = r' then (1 : ℚ) / (refineDatum D t).sourceEdgeIndex y.1 else 0) else 0 := by
      intro y
      by_cases h1 : cls' y = r' <;> by_cases h2 : y.1.1.1 = subdivOcc T t (some (col c)) <;>
        simp [h1, h2]
    rw [Finset.sum_congr rfl fun y _ ↦ hsplit y, Refine.sum_over_some D t hD]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [hidx_s]
  have hM_none : ∀ r', M r' none = ∑ x : NonDanglingEdge D,
      if x.1.1.1 = t then (if cls' (nH x) = r' then w x else 0) else 0 := by
    intro r'
    show (∑ y : NonDanglingEdge (refineDatum D t), if cls' y = r' ∧ y.1.1.1 = col' none then
      (1 : ℚ) / (refineDatum D t).sourceEdgeIndex y.1 else 0) = _
    have hc : col' none = subdivOcc T t none := rfl
    rw [hc]
    have hsplit : ∀ y : NonDanglingEdge (refineDatum D t),
        (if cls' y = r' ∧ y.1.1.1 = subdivOcc T t none then
          (1 : ℚ) / (refineDatum D t).sourceEdgeIndex y.1 else 0) =
        if y.1.1.1 = subdivOcc T t none then
          (if cls' y = r' then (1 : ℚ) / (refineDatum D t).sourceEdgeIndex y.1 else 0) else 0 := by
      intro y
      by_cases h1 : cls' y = r' <;> by_cases h2 : y.1.1.1 = subdivOcc T t none <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun y _ ↦ hsplit y, Refine.sum_over_none D t hD]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : x.1.1.1 = t
    · rw [if_pos hx, if_pos hx, hidx_n x hx]
    · rw [if_neg hx, if_neg hx]
  have hBe : ∀ r c, B r c = ∑ x : NonDanglingEdge D,
      if x.1.1.1 = col c then (if cls x = r then w x else 0) else 0 := by
    intro r c
    show (∑ x : NonDanglingEdge D, if cls x = r ∧ x.1.1.1 = col c then
      (1 : ℚ) / D.sourceEdgeIndex x.1 else 0) = _
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h1 : cls x = r <;> by_cases h2 : x.1.1.1 = col c <;> simp [h1, h2, w]
  -- the classes of the halves
  have hs_s : ∀ x, cls' (sH x) = some (cls x) ∨ (cls x = cls f ∧ cls' (sH x) = none) := by
    intro x
    have := hs.parent (sH x)
    rw [hpar_s x] at this
    exact this
  have hs_n : ∀ x : NonDanglingEdge D, x.1.1.1 = t →
      cls' (nH x) = some (cls x) ∨ (cls x = cls f ∧ cls' (nH x) = none) := by
    intro x hx
    have := hs.parent (nH x)
    rw [hpar_n x hx] at this
    exact this
  have e1 : ∀ (v : ι) (o : Option ι) (r : ι), r ≠ cls f →
      (o = some v ∨ (v = cls f ∧ o = none)) → (o = some r ↔ v = r) := by
    intro v o r hr ho
    rcases ho with ho | ⟨hv, ho⟩
    · rw [ho]; exact ⟨fun h ↦ Option.some_injective _ h, fun h ↦ by rw [h]⟩
    · rw [ho]; exact ⟨fun h ↦ absurd h (by simp), fun h ↦ absurd (h ▸ hv) hr⟩
  have e2 : ∀ (v : ι) (o : Option ι) (u : ℚ), (o = some v ∨ (v = cls f ∧ o = none)) →
      (if o = some (cls f) then u else 0) + (if o = none then u else 0) =
        if v = cls f then u else 0 := by
    intro v o u ho
    rcases ho with rfl | ⟨rfl, rfl⟩
    · by_cases hv : v = cls f
      · simp [hv]
      · simp [hv]
    · simp
  have htc : col (col.symm t) = t := col.apply_symm_apply t
  -- the four hypotheses of `abs_det_refine`
  have hother : ∀ r, r ≠ cls f → M (some r) (some (col.symm t)) = M (some r) none := by
    intro r hr
    rw [hM_some, hM_none, htc]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : x.1.1.1 = t
    · rw [if_pos hx, if_pos hx]
      have h1 := e1 _ _ r hr (hs_s x)
      have h2 := e1 _ _ r hr (hs_n x hx)
      by_cases hc : cls x = r
      · rw [if_pos (h1.mpr hc), if_pos (h2.mpr hc)]
      · rw [if_neg (fun h ↦ hc (h1.mp h)), if_neg (fun h ↦ hc (h2.mp h))]
    · rw [if_neg hx, if_neg hx]
  have hsum : M (some (cls f)) (some (col.symm t)) + M none (some (col.symm t)) =
      M (some (cls f)) none + M none none := by
    rw [hM_some, hM_some, hM_none, hM_none, htc, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : x.1.1.1 = t
    · rw [if_pos hx, if_pos hx, if_pos hx, if_pos hx, e2 _ _ _ (hs_s x), e2 _ _ _ (hs_n x hx)]
    · rw [if_neg hx, if_neg hx, if_neg hx, if_neg hx]
  have hrow : ∀ c, B (cls f) c = M (some (cls f)) (some c) + M none (some c) := by
    intro c
    rw [hBe, hM_some, hM_some, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : x.1.1.1 = col c
    · rw [if_pos hx, if_pos hx, if_pos hx, e2 _ _ _ (hs_s x)]
    · rw [if_neg hx, if_neg hx, if_neg hx, add_zero]
  have hB' : ∀ r, r ≠ cls f → ∀ c, B r c = M (some r) (some c) := by
    intro r hr c
    rw [hBe, hM_some]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : x.1.1.1 = col c
    · rw [if_pos hx, if_pos hx]
      have h1 := e1 _ _ r hr (hs_s x)
      by_cases hc : cls x = r
      · rw [if_pos hc, if_pos (h1.mpr hc)]
      · rw [if_neg hc, if_neg (fun h ↦ hc (h1.mp h))]
    · rw [if_neg hx, if_neg hx]
  rw [abs_det_refine B M (cls f) (col.symm t) hother hsum hrow hB']
  -- the entry `δ`: only the halves of `f` differ
  have hδ : M (some (cls f)) (some (col.symm t)) - M (some (cls f)) none =
      (if cls' (sH f) = some (cls f) then w f else 0) -
        (if cls' (nH f) = some (cls f) then w f else 0) := by
    rw [hM_some, hM_none, htc, ← Finset.sum_sub_distrib, Finset.sum_eq_single f]
    · rw [if_pos hs.over_t, if_pos hs.over_t]
    · intro x _ hxf
      by_cases hx : x.1.1.1 = t
      · rw [if_pos hx, if_pos hx, hs.others x hx hxf, sub_self]
      · rw [if_neg hx, if_neg hx, sub_self]
    · intro h; exact absurd (Finset.mem_univ f) h
  have hapos : (0 : ℚ) < D.sourceEdgeIndex f.1 := by
    have := (D.edgePartition f.1.1.1).blockCard_pos f.1.1.2
    unfold GluingDatum.sourceEdgeIndex
    exact_mod_cast this
  have habs : |(if cls' (sH f) = some (cls f) then w f else 0) -
      (if cls' (nH f) = some (cls f) then w f else 0)| = w f := by
    have hwpos : 0 ≤ w f := by simp only [w]; positivity
    have hs1 := hs_s f
    have hn1 := hs_n f hs.over_t
    have hne := hs.split
    rcases hs1 with h1 | ⟨-, h1⟩ <;> rcases hn1 with h2 | ⟨-, h2⟩
    · exact absurd (h1.trans h2.symm) hne
    · rw [if_pos h1, if_neg (by rw [h2]; simp), sub_zero, abs_of_nonneg hwpos]
    · rw [if_neg (by rw [h1]; simp), if_pos h2, zero_sub, abs_neg, abs_of_nonneg hwpos]
    · exact absurd (h1.trans h2.symm) hne
  rw [hδ, habs]
  simp only [w]
  field_simp

open Classical in
/-- **The matrix of a stable labelling is a class matrix**: classes are the stable paths. -/
theorem matrix_eq_clsMatrix {E : GluingDatum T d} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StableLengthMatrixLabelling E ι) :
    GluingDatum.LengthMatrixPresentation.matrix L.presentation =
      clsMatrix E (fun x ↦ L.row x.stablePath) L.targetEdge := by
  ext r c
  have h := DraismaVargas.Count.LeafFibre.matrix_eq_sum_fibre L r (L.targetEdge c)
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  show _ = ∑ x : NonDanglingEdge E, if L.row x.stablePath = r ∧ x.1.1.1 = L.targetEdge c then
    (1 : ℚ) / E.sourceEdgeIndex x.1 else 0
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun edge hedge ↦ (⟨edge,
      ((DraismaVargas.Count.LeafFibre.mem_rowFibre L r _ edge).mp hedge).1.1⟩ :
        NonDanglingEdge E)) (fun x _ ↦ x.1) ?_ ?_ ?_ ?_ ?_
  · intro edge hedge
    obtain ⟨⟨hS, hrow⟩, hover⟩ := (DraismaVargas.Count.LeafFibre.mem_rowFibre L r _ edge).mp hedge
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow, hover⟩
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    exact (DraismaVargas.Count.LeafFibre.mem_rowFibre L r _ x.1).mpr ⟨⟨x.2, hx'.1⟩, hx'.2⟩
  · intro edge _
    rfl
  · intro x _
    rfl
  · intro edge _
    rfl

/-- The column labelling of a refinement: the new half is `none`. -/
noncomputable abbrev refineCol {ι : Type*} (t : T.edges) (col : ι ≃ T.edges) :
    Option ι ≃ (subdivTarget T t).edges :=
  (Equiv.optionCongr col).trans (subdivOcc T t)

end ClassMatrix

/-! ## The labels of a glued member -/

section Labels

open DraismaVargas.Count
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)
open GenusSixExistence.Tripod.Gadget

variable {n p : ℕ} {core : Core n p}

/-- A vertex of `G̃` as a vertex of the gadget. -/
def oldLabel (v : Fin n) : Fin (n + 1 + 1 + 1 + 1) := v.castSucc.castSucc.castSucc.castSucc

/-- Merge the two pieces of a subdivided slot (`subdivide`): `castSucc i ↦ i`, `last ↦ e`. -/
def mergeOne {q : ℕ} (e : Fin q) (j : Fin (q + 1)) : Fin q :=
  if h : (j : ℕ) < q then ⟨j, h⟩ else e

/-- The slot of `G̃` that a slot of the gadget comes from: G-slots merge back through the three
subdivisions, legs come from none. -/
def mergeSlot (s : MarkSlots p) (j : Fin (p + 1 + 1 + 1 + 3)) : Option (Fin p) :=
  if h : (j : ℕ) < p + 1 + 1 + 1 then
    some (mergeOne s.first (mergeOne s.second (mergeOne s.third ⟨j, h⟩)))
  else none

/-- **The labels of a glued member** (§3.3, §5.5). A core
identification `ident'` of a datum `data'`, read through an isomorphism `iso` from the glued datum
of `ψ` at `π`, labels

* each branch vertex of `ψ` as itself, in the old vertices of `Γ̃`;
* mark `k` as `tripodMark n k`;
* the centre as the branch vertex of the new sheet;
* each old stable path as a piece of its own slot of `G̃`;
* the arm of leg `k`, in the sheet of mark `k`, as part of leg `k`.

The vertex clauses are equations, so they pin every vertex label. -/
structure GluedLabels (s : MarkSlots p) {d : ℕ} {yG : Fin p → ℚ} (ψ : FibreMember core yG d)
    (π : Placement ψ.target d) {target' : CFGraph.{0}} {data' : GluingDatum target' (d + 1)}
    (ident' : CoreIdentification (tripodCore core s) data')
    (iso : GeometricDatumIso (glueDatum ψ.data π) data') : Prop where
  old : ∀ b : BranchVertex ψ.data, (ident'.vertex.symm (oldLabel (ψ.ident.vertex b))).1 =
    iso.sourceVertexEquiv (π.oldSourceVertex ψ.data b.1)
  mark : ∀ k, (ident'.vertex.symm (tripodMark n k)).1 =
    iso.sourceVertexEquiv (π.markSourceVertex ψ.data k)
  centre : (iso.sourceVertexEquiv.symm (ident'.vertex.symm (centre n)).1).1.2 = Fin.last d
  row : ∀ e : NonDanglingEdge ψ.data, ∃ e' : NonDanglingEdge data',
    e'.1 = iso.sourceEdgeEquiv (π.oldSourceEdge ψ.data e.1) ∧
      mergeSlot s (ident'.row e'.stablePath) = some (ψ.ident.row e.stablePath)
  leg : ∀ k, ∃ e' : NonDanglingEdge data',
    e'.1 = iso.sourceEdgeEquiv (π.armSourceEdge ψ.data k) ∧ ident'.row e'.stablePath = legSlot p k

/-- **`φ` is the Cools--Draisma tripod gluing of `ψ`**: up to an isomorphism of gluing data,
`φ` is `glueDatum ψ.data π` at a placement of the marks on the core of `ψ`, with the glued
labels. -/
def IsGluingOf (s : MarkSlots p) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (ψ : FibreMember core (baseRequest s y) (2 + 2))
    (φ : FibreMember (tripodCore core s) y (3 + 2)) : Prop :=
  ∃ π : Placement ψ.target (2 + 2), π.NonDangling ψ.data ∧
    ∃ iso : GeometricDatumIso (glueDatum ψ.data π) φ.data, GluedLabels s ψ π φ.ident iso

end Labels


section Bijection

open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph} {d : ℕ}

/-! ## (a) The glued member -/

/-- **Riemann--Hurwitz holds for the glued datum** whenever it holds for `D` (§5.2,
change-minimality, whose three local checks are RH with equality): it is preserved by each stage,
`riemannHurwitz_refineDatum`, `riemannHurwitz_extendDatum` and `riemannHurwitz_leafDatum`. -/
theorem glueDatum_riemannHurwitz (D : GluingDatum T d) (π : Placement T d)
    (hD : D.RiemannHurwitz) : (glueDatum D π).RiemannHurwitz := by
  unfold glueDatum
  exact riemannHurwitz_leafDatum _ (riemannHurwitz_leafDatum _ (riemannHurwitz_leafDatum _
    (riemannHurwitz_extendDatum _ (riemannHurwitz_refineDatum _ (riemannHurwitz_refineDatum _
      (riemannHurwitz_refineDatum _ hD _) _) _)) _ _ _) _ _ _) _ _ _

/-- **The dimension count is saturated** for the glued datum: six more target edges, two more
in the source genus, one more sheet. -/
theorem glueDatum_saturated {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) :
    (π.T₆.edges.card : ℤ) = 2 * genus (glueDatum ψ.data π).sourceGraph + 2 * (2 + 2 + 1) - 5 := by
  have h := ψ.fullDim.saturated
  rw [genus_glueDatum _ _ ψ.fullDim.targetGenus, π.T₆_edge_card]
  push_cast at h ⊢
  linarith

/-! ### The stable graph and the length matrix of the glued datum

`exists_stableLabelling_glueDatum`, `abs_det_glueDatum` and `denominatorProduct_glueDatum` are
proved from six statements about the stable graph of `glueDatum ψ.data π` (S1--S6 below), the
arm lemmas above (`hairpin_not_isDangling`, `matrix_armColumn`), the arm expansion
`abs_det_eq_of_doubled_columns` and Part II `lemma-edge-deno` (a). S1--S4 come from the
dangling dictionary (§5.2), shown above: a glued source edge is
non-dangling exactly when it is

* an old source edge, or a piece of one, that is non-dangling for `ψ`
  (`isDangling_liftSE_iff`, `Refine.isDangling_iff`);
* the arm of mark `k` in the sheet of mark `k`, or in the new sheet `Fin.last`
  (`hairpin_not_isDangling`, `isDangling_armSheetEdge`);
* an edge of the new sheet on the subtree of `T₃` spanned by the three mark images
  (`NewSurvives`; that it is a tree with leaves among the mark images and one branch point is
  `tCount_add_le` and `card_branch_eq_one`).

S5 follows from S5a (`exists_refinementChain_glueDatum`, from `CutPaths`), and S6
(`prod_rowDenominator_residual_glueDatum`) from `CutPaths` and `LcmMerge`. -/

/-- **The arm columns** of a labelling of the glued datum: the column of the arm at mark `k` is
`2 e_{legRow k}`. Only the hairpin of leg `k` passes over the arm, once in the sheet of the mark
and once in the new sheet, each with index one (§5.3). -/
def ArmColumns {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2)) (π : Placement ψ.target (2 + 2))
    (L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) : Prop :=
  ∀ r k, GluingDatum.LengthMatrixPresentation.matrix L.presentation r
      (L.targetEdge.symm (π.armEdge k)) = if r = legRow k then 2 else 0

/-- **(S1) The glued datum has `p + 6` stable paths**: the `p` old ones, three of them split at a
mark, and the three legs. True by the row list of §5.3: by the dangling
dictionary the non-dangling edges are the old ones (halved over the subdivided target edges),
the two arms of each hairpin, and the new sheet over the subtree spanned by the marks; the
branch vertices are the old ones, the three marks (two halves and the arm, `hπ`) and the median
of the three mark images in the new sheet. A mark splits the old stable path through it once,
also when two marks lie on one path, and each leg is the hairpin followed by the new-sheet path
to the median. Proof (`card_stablePath_glue`): by counting rather than by listing the
classes: `2 · #paths = 3 · #branch vertices` for a trivalent datum with path ends
(`two_mul_card_stablePath_eq`), and the branch vertices of the glued datum are those of `ψ`, the
three marks and the median (`card_stableVertices_glue`). -/
theorem card_stablePath_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data) :
    Fintype.card (StablePath (glueDatum ψ.data π)) = p + 1 + 1 + 1 + 3 := by
  rw [card_stablePath_glue ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected
    ψ.fullDim.targetGenus hπ ψ.fullDim.trivalent ψ.fullDim.pathEnds,
    Fintype.card_congr ψ.fullDim.labelling.row, Fintype.card_fin]

/-- **(S2) The glued datum is trivalent** (§5.2). Old source vertices keep
their non-dangling valency (everything new meets the old sheets at the marks, on the core, so
the old dangling trees stay dangling) and `ψ` is trivalent (`ψ.fullDim.trivalent`); a mark has
the two halves of its edge and its arm; in the new sheet only the median of the three mark images
has valency three; every other new vertex has valency at most two. Proof:
`nonDanglingValency_glue_le_three`. -/
theorem nonDanglingValency_glueDatum_le_three {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data) :
    ∀ v, nonDanglingValency (glueDatum ψ.data π) v ≤ 3 :=
  nonDanglingValency_glue_le_three ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected
    ψ.fullDim.targetGenus hπ ψ.fullDim.trivalent

/-- **(S3) No stable path of the glued datum is a cycle.** Each old piece ends at an old branch
vertex or at a mark, and each leg runs from its mark to the median. True because `ψ` has path
ends (`ψ.fullDim.pathEnds`) and every new branch vertex (the marks and the median) has
non-dangling valency three. Proof: `hasPathEnds_glue`. -/
theorem hasPathEnds_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data) :
    HasPathEnds (glueDatum ψ.data π) :=
  hasPathEnds_glue ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected ψ.fullDim.targetGenus hπ
    ψ.fullDim.pathEnds

/-- **The hairpin survives** (§3.3, §5.2): `hairpin_not_isDangling`,
since the source and the target of `ψ` are connected. -/
theorem hairpin_not_isDangling_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (k : Fin 3) :
    ¬ IsDangling (glueDatum ψ.data π) (armSheetEdge ψ.data π k (π.sheet k).castSucc) ∧
      ¬ IsDangling (glueDatum ψ.data π) (armSheetEdge ψ.data π k (Fin.last _)) :=
  hairpin_not_isDangling ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected k

/-- **(S4) The three hairpins lie on three different stable paths** (§5.3,
the leg rows). True because a stable path runs through passages only, and each leg is bounded
by branch vertices: on one side by its mark (non-dangling valency three: the two halves of the
old edge and the arm, `hπ`), on the other by the median of the three mark images in the new
sheet. Two hairpins on one stable path would make the path pass through a mark. Proof
(`hairpinPath_ne_glue`): a stable path has exactly two ends, and one through two hairpins would
leave the surviving new-sheet edges at the third mark image as an edge set of the tree `T₃`
without valency one elsewhere. -/
theorem hairpinPath_injective {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (h : ∀ k, ¬ IsDangling (glueDatum ψ.data π) (armSheetEdge ψ.data π k (π.sheet k).castSucc)) :
    Function.Injective fun k ↦
      NonDanglingEdge.stablePath (⟨_, h k⟩ : NonDanglingEdge (glueDatum ψ.data π)) := by
  intro k j hkj
  by_contra hne
  exact hairpinPath_ne_glue ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected
    ψ.fullDim.targetGenus hπ ψ.fullDim.pathEnds hne hkj

/-- **The arm columns** (§5.3, Part I `prop-adm-matrix` (a)): in every labelling of the
glued datum, the column of the arm at mark `k` is `2 e_{legRow k}` for three distinct rows, the
rows of the hairpins. From `hairpin_not_isDangling`, S4 and `matrix_armColumn`. -/
theorem exists_armColumns_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3))) :
    ∃ legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3), Function.Injective legRow ∧
      ArmColumns ψ π L legRow := by
  have hconn := glueDatum_connected ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected
  have hsurv := hairpin_not_isDangling_glueDatum ψ π
  refine ⟨fun k ↦ L.row (NonDanglingEdge.stablePath
      (⟨_, (hsurv k).1⟩ : NonDanglingEdge (glueDatum ψ.data π))),
    L.row.injective.comp (hairpinPath_injective ψ π hπ fun k ↦ (hsurv k).1), fun r k ↦ ?_⟩
  exact matrix_armColumn ψ.data π L hconn k (hsurv k).1 (hsurv k).2 r

namespace Placement

variable (D : GluingDatum T d) (π : Placement T d)

/-- Mark `0`, as a surviving source edge of `D`. -/
def markEdge₀ (hπ : π.NonDangling D) : NonDanglingEdge D :=
  ⟨D.sourceEdge π.edge₀ (π.sheet 0), hπ 0⟩

/-- Mark `1`, as a surviving source edge of `D` refined at mark `0`. -/
def markEdge₁ (hD : D.Connected) (hπ : π.NonDangling D) :
    NonDanglingEdge (refineDatum D π.edge₀) :=
  ⟨(refineDatum D π.edge₀).sourceEdge π.edge₁ (π.sheet 1),
    (Refine.isDangling_sourceEdge _ _ hD _ _).not.mpr (hπ 1)⟩

/-- Mark `2`, as a surviving source edge of `D` refined at marks `0` and `1`. -/
def markEdge₂ (hD : D.Connected) (hπ : π.NonDangling D) :
    NonDanglingEdge (refineDatum (refineDatum D π.edge₀) π.edge₁) :=
  ⟨(refineDatum (refineDatum D π.edge₀) π.edge₁).sourceEdge π.edge₂ (π.sheet 2),
    (Refine.isDangling_sourceEdge _ _ (π.refine₁_connected D hD) _ _).not.mpr
      ((Refine.isDangling_sourceEdge _ _ hD _ _).not.mpr (hπ 2))⟩

theorem sourceEdgeIndex_markEdge₀ (hπ : π.NonDangling D) :
    D.sourceEdgeIndex (π.markEdge₀ D hπ).1 = π.markIndex D 0 := rfl

theorem sourceEdgeIndex_markEdge₁ (hD : D.Connected) (hπ : π.NonDangling D) :
    (refineDatum D π.edge₀).sourceEdgeIndex (π.markEdge₁ D hD hπ).1 = π.markIndex D 1 := by
  rw [markEdge₁, Refine.sourceEdgeIndex_eq, Refine.parentSE_sourceEdge]
  rfl

theorem sourceEdgeIndex_markEdge₂ (hD : D.Connected) (hπ : π.NonDangling D) :
    (refineDatum (refineDatum D π.edge₀) π.edge₁).sourceEdgeIndex (π.markEdge₂ D hD hπ).1 =
      π.markIndex D 2 := by
  rw [markEdge₂, Refine.sourceEdgeIndex_eq, Refine.parentSE_sourceEdge, Refine.sourceEdgeIndex_eq,
    Refine.parentSE_sourceEdge]
  rfl

end Placement

/-! ### The cut paths (toward S5a)

The non-leg rows of the glued matrix are the glued stable paths through old edges
(`CutPaths.gluedPath`; old edges continue into old edges, `CutPaths.isOld_of_consecutive`).
Merging them back one mark at a time (`Merge.merged`; `CutPaths.cut₂`, `cut₁`, `cut₀`) splits one
class per mark, and merged back at all three marks they are unions of stable paths of `D`
(`CutPaths.cut₀_eq_of_consecutive`). That each mark really separates is **counted, not walked**:
merging back at a mark loses one class exactly when the mark separates
(`Merge.card_image_merged`), the glued paths through old edges have two ends each and so number
`#paths(D) + 3` (`CutPaths.card_image_gluedPath`), and `#paths(D)` classes remain at the end. -/

namespace Refine

variable (D : GluingDatum T d) (t : T.edges)

/-- Every surviving edge of a refinement is the `some`-piece of its parent, or the `none`-half
of a parent over `t`. -/
theorem eq_someHalfND_or_noneHalfND (hD : D.Connected) (z : NonDanglingEdge (refineDatum D t)) :
    z = someHalfND D t hD (parentND D t hD z) ∨
      ((parentND D t hD z).1.1.1 = t ∧ z = noneHalfND D t hD (parentND D t hD z)) := by
  obtain ⟨o, ho⟩ := (subdivOcc T t).surjective z.1.1.1
  cases o with
  | some e =>
    left
    apply Subtype.ext
    apply Subtype.ext
    show z.1.1 = (subdivOcc T t (some (parentT t z.1.1.1)), z.1.1.2)
    rw [← ho, parentT_some]
    exact Prod.ext ho.symm rfl
  | none =>
    have hp : (parentND D t hD z).1.1.1 = t := by
      show parentT t z.1.1.1 = t
      rw [← ho, parentT_none]
    right
    refine ⟨hp, ?_⟩
    apply Subtype.ext
    rw [noneHalfND_val D t hD hp]
    apply Subtype.ext
    have hzz := z.1.2
    rw [refineDatum_edgePartition, ← ho, parentT_none] at hzz
    show z.1.1 = (subdivOcc T t none, (D.edgePartition t).repr z.1.1.2)
    rw [hzz]
    exact Prod.ext ho.symm rfl

theorem parentND_someHalfND (hD : D.Connected) (x : NonDanglingEdge D) :
    parentND D t hD (someHalfND D t hD x) = x :=
  Subtype.ext (parentSE_someHalf D t x.1)

theorem parentND_noneHalfND (hD : D.Connected) {x : NonDanglingEdge D} (hx : x.1.1.1 = t) :
    parentND D t hD (noneHalfND D t hD x) = x := by
  apply Subtype.ext
  show parentSE D t (noneHalfND D t hD x).1 = x.1
  rw [noneHalfND_val D t hD hx, parentSE_noneHalf D t hx]

theorem parentND_surjective (hD : D.Connected) : Function.Surjective (parentND D t hD) :=
  fun x ↦ ⟨_, parentND_someHalfND D t hD x⟩

theorem someHalfND_ne_noneHalfND (hD : D.Connected) {x : NonDanglingEdge D} (hx : x.1.1.1 = t) :
    someHalfND D t hD x ≠ noneHalfND D t hD x := by
  intro h
  have h' := congrArg (fun y : NonDanglingEdge (refineDatum D t) ↦ y.1.1.1) h
  rw [noneHalfND_val D t hD hx] at h'
  change subdivOcc T t (some x.1.1.1) = subdivOcc T t none at h'
  exact absurd ((subdivOcc T t).injective h') (by simp)

theorem repr_of_over {x : D.SourceEdge} (hx : x.1.1 = t) :
    (D.edgePartition t).repr x.1.2 = x.1.2 := by
  have h := x.2
  rw [hx] at h
  exact h

/-- The fresh vertex subdividing a source edge over `t`. -/
def freshOf (x : D.SourceEdge) (hx : x.1.1 = t) : (refineDatum D t).SourceVertex :=
  freshSV D t x.1.2 (repr_of_over D t hx)

theorem freshOf_inj {x y : D.SourceEdge} (hx : x.1.1 = t) (hy : y.1.1 = t)
    (h : freshOf D t x hx = freshOf D t y hy) : x = y :=
  Subtype.ext (Prod.ext (hx.trans hy.symm)
    (congrArg (fun z : (refineDatum D t).SourceVertex ↦ z.1.2) h))

theorem incident_halves (hD : D.Connected) {x : NonDanglingEdge D} (hx : x.1.1.1 = t) :
    Incident _ (someHalfND D t hD x).1 (freshOf D t x.1 hx) ∧
      Incident _ (noneHalfND D t hD x).1 (freshOf D t x.1 hx) := by
  constructor
  · rw [freshOf, incident_freshSV_iff]
    right
    exact Subtype.ext (Prod.ext (congrArg (fun e ↦ subdivOcc T t (some e)) hx) rfl)
  · rw [freshOf, incident_freshSV_iff, noneHalfND_val D t hD hx]
    left
    exact Subtype.ext (Prod.ext rfl (repr_of_over D t hx))

theorem nonDanglingValency_freshOf (hD : D.Connected) (x : NonDanglingEdge D)
    (hx : x.1.1.1 = t) : nonDanglingValency (refineDatum D t) (freshOf D t x.1 hx) = 2 := by
  rw [freshOf, nonDanglingValency_freshSV D t hD, if_neg]
  have h : (⟨(t, x.1.1.2), repr_of_over D t hx⟩ : D.SourceEdge) = x.1 :=
    Subtype.ext (Prod.ext hx.symm rfl)
  rw [h]
  exact x.2

/-- The surviving piece of a surviving edge at an old vertex. -/
def pieceND (hD : D.Connected) (u : D.SourceVertex) (y : NonDanglingEdge D) :
    NonDanglingEdge (refineDatum D t) :=
  ⟨piece D t u y.1, (isDangling_iff D t hD _).not.mpr (by rw [parentSE_piece]; exact y.2)⟩

theorem parentND_pieceND (hD : D.Connected) (u : D.SourceVertex) (y : NonDanglingEdge D) :
    parentND D t hD (pieceND D t hD u y) = y :=
  Subtype.ext (parentSE_piece D t u y.1)

/-- **Two edges at an old vertex** have two different pieces at it. -/
theorem pieceND_pair (hD : D.Connected) {y y' : NonDanglingEdge D} {u : D.SourceVertex}
    (hne : y ≠ y') (hy : Incident D y.1 u) (hy' : Incident D y'.1 u) :
    pieceND D t hD u y ≠ pieceND D t hD u y' ∧
      Incident _ (pieceND D t hD u y).1 (oldSV D t u) ∧
        Incident _ (pieceND D t hD u y').1 (oldSV D t u) :=
  ⟨fun h ↦ hne (by rw [← parentND_pieceND D t hD u y, h, parentND_pieceND]),
    incident_piece D t hy, incident_piece D t hy'⟩

/-- **Two edges of different index at a vertex of a refinement** meet at an old vertex: the two
edges at a fresh vertex are the halves of one edge. -/
theorem exists_oldSV_of_incident_ne {y y' : (refineDatum D t).SourceEdge}
    {x : (refineDatum D t).SourceVertex} (hy : Incident _ y x) (hy' : Incident _ y' x)
    (hne : D.sourceEdgeIndex (parentSE D t y) ≠ D.sourceEdgeIndex (parentSE D t y')) :
    ∃ u, x = oldSV D t u ∧ Incident D (parentSE D t y) u ∧ Incident D (parentSE D t y') u := by
  rcases sourceVertex_cases D t x with ⟨u, rfl⟩ | ⟨i, hi, rfl⟩
  · exact ⟨u, rfl, ((incident_oldSV_iff D t y u).mp hy).1, ((incident_oldSV_iff D t y' u).mp hy').1⟩
  · exfalso
    apply hne
    have hp : ∀ w, Incident _ w (freshSV D t i hi) → parentSE D t w = ⟨(t, i), hi⟩ := by
      intro w hw
      rcases (incident_freshSV_iff D t i hi w).mp hw with rfl | rfl
      · exact parentSE_halfNone D t i hi
      · exact parentSE_halfSome D t i hi
    rw [hp y hy, hp y' hy']

theorem sourceEdgeIndex_someHalfND (hD : D.Connected) (x : NonDanglingEdge D) :
    (refineDatum D t).sourceEdgeIndex (someHalfND D t hD x).1 = D.sourceEdgeIndex x.1 := by
  rw [sourceEdgeIndex_eq]
  exact congrArg (fun y : NonDanglingEdge D ↦ D.sourceEdgeIndex y.1) (parentND_someHalfND D t hD x)

theorem sourceEdgeIndex_noneHalfND (hD : D.Connected) {x : NonDanglingEdge D} (hx : x.1.1.1 = t) :
    (refineDatum D t).sourceEdgeIndex (noneHalfND D t hD x).1 = D.sourceEdgeIndex x.1 := by
  rw [sourceEdgeIndex_eq]
  exact congrArg (fun y : NonDanglingEdge D ↦ D.sourceEdgeIndex y.1)
    (parentND_noneHalfND D t hD hx)

end Refine

/-! ### Merging back at one mark -/

namespace Merge

variable (D : GluingDatum T d) (t : T.edges) (hD : D.Connected) {α : Type*} [DecidableEq α]

/-- Identify `N` with `S`. -/
def mergeFn (S N : α) (P : α) : α := if P = N then S else P

/-- **The labelling merged back at `f`**: the class of the `some`-piece, with the class of the
`none`-half of `f` identified with that of its `some`-half. -/
def merged (f : NonDanglingEdge D) (c : NonDanglingEdge (refineDatum D t) → α) :
    NonDanglingEdge D → α := fun x ↦
  mergeFn (c (Refine.someHalfND D t hD f)) (c (Refine.noneHalfND D t hD f))
    (c (Refine.someHalfND D t hD x))

/-- The two halves of every edge over `t` other than `f` have one class. -/
def Others (f : NonDanglingEdge D) (c : NonDanglingEdge (refineDatum D t) → α) : Prop :=
  ∀ f' : NonDanglingEdge D, f'.1.1.1 = t → f' ≠ f →
    c (Refine.someHalfND D t hD f') = c (Refine.noneHalfND D t hD f')

variable {D t hD}

theorem mergeFn_self (S N : α) : mergeFn S N S = S := by
  unfold mergeFn; split_ifs with h <;> rfl

/-- **The merged class of the parent** is the merged class of the child. -/
theorem merged_parentND {f : NonDanglingEdge D} {c : NonDanglingEdge (refineDatum D t) → α}
    (hc : Others D t hD f c) (z : NonDanglingEdge (refineDatum D t)) :
    merged D t hD f c (Refine.parentND D t hD z) =
      mergeFn (c (Refine.someHalfND D t hD f)) (c (Refine.noneHalfND D t hD f)) (c z) := by
  rcases Refine.eq_someHalfND_or_noneHalfND D t hD z with h | ⟨hp, h⟩
  · conv_rhs => rw [h]
    rfl
  · by_cases hpf : Refine.parentND D t hD z = f
    · conv_rhs => rw [h, hpf]
      unfold merged mergeFn
      rw [hpf]
      simp only [if_true]
      split_ifs <;> rfl
    · conv_rhs => rw [h, ← hc _ hp hpf]
      rfl

theorem image_merged {f : NonDanglingEdge D} {c : NonDanglingEdge (refineDatum D t) → α}
    (hc : Others D t hD f c) :
    Finset.univ.image (merged D t hD f c) =
      (Finset.univ.image c).image
        (mergeFn (c (Refine.someHalfND D t hD f)) (c (Refine.noneHalfND D t hD f))) := by
  ext P
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨c (Refine.someHalfND D t hD x), ⟨_, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨_, merged_parentND hc z⟩

/-- **Merging back loses one class**, exactly when the two halves of `f` are separated. -/
theorem card_image_merged {f : NonDanglingEdge D} {c : NonDanglingEdge (refineDatum D t) → α}
    (hc : Others D t hD f c) :
    (Finset.univ.image (merged D t hD f c)).card +
        (if c (Refine.someHalfND D t hD f) = c (Refine.noneHalfND D t hD f) then 0 else 1) =
      (Finset.univ.image c).card := by
  rw [image_merged hc]
  set S := c (Refine.someHalfND D t hD f)
  set N := c (Refine.noneHalfND D t hD f)
  by_cases hSN : S = N
  · rw [if_pos hSN, add_zero]
    have hid : mergeFn S N = id := by
      funext P; unfold mergeFn; split_ifs with h <;> simp [h, hSN]
    rw [hid, Finset.image_id]
  · rw [if_neg hSN]
    have hN : N ∈ Finset.univ.image c := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have heq : (Finset.univ.image c).image (mergeFn S N) = (Finset.univ.image c).erase N := by
      ext P
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        unfold mergeFn
        split_ifs with h
        · exact ⟨hSN, _, rfl⟩
        · exact ⟨h, z, rfl⟩
      · rintro ⟨hP, z, rfl⟩
        exact ⟨_, ⟨z, rfl⟩, by unfold mergeFn; rw [if_neg hP]⟩
    rw [heq, Finset.card_erase_of_mem hN]
    have : 0 < (Finset.univ.image c).card := Finset.card_pos.mpr ⟨N, hN⟩
    omega

/-- The labels after a split: the `none`-half's class gets the new label. -/
def liftLabel {ι : Type*} (N : α) (lab : α → ι) : α → Option ι := fun P ↦
  if P = N then none else some (lab P)

/-- **A separating labelling splits one class**: merging back and relabelling gives `SplitsAt`. -/
theorem splitsAt_of_separated {ι : Type*} {f : NonDanglingEdge D}
    {c : NonDanglingEdge (refineDatum D t) → α} (hf : f.1.1.1 = t) (hc : Others D t hD f c)
    (hsep : c (Refine.someHalfND D t hD f) ≠ c (Refine.noneHalfND D t hD f))
    (lab : α → ι) (cls : NonDanglingEdge D → ι) (hcls : ∀ x, cls x = lab (merged D t hD f c x)) :
    SplitsAt D t hD cls (fun y ↦ liftLabel (c (Refine.noneHalfND D t hD f)) lab (c y)) f := by
  set S := c (Refine.someHalfND D t hD f)
  set N := c (Refine.noneHalfND D t hD f)
  have hmf : merged D t hD f c f = S := by
    show mergeFn S N S = S
    exact mergeFn_self S N
  refine ⟨hf, fun y ↦ ?_, ?_, fun f' hf' hne ↦ ?_⟩
  · rw [hcls, hcls, merged_parentND hc, hmf]
    unfold liftLabel mergeFn
    by_cases hy : c y = N
    · right
      exact ⟨by rw [if_pos hy], by rw [if_pos hy]⟩
    · left
      rw [if_neg hy, if_neg hy]
  · unfold liftLabel
    rw [if_neg hsep, if_pos rfl]
    simp
  · show liftLabel N lab (c (Refine.someHalfND D t hD f')) =
      liftLabel N lab (c (Refine.noneHalfND D t hD f'))
    rw [hc f' hf' hne]

/-- **Splitting one class keeps every label in use.** -/
theorem surjective_of_splitsAt {ι : Type*} {f : NonDanglingEdge D} {cls : NonDanglingEdge D → ι}
    {cls' : NonDanglingEdge (refineDatum D t) → Option ι} (hs : SplitsAt D t hD cls cls' f)
    (hsurj : Function.Surjective cls) : Function.Surjective cls' := by
  have hhalf : ∀ x, x.1.1.1 = t → ∀ y, y = Refine.someHalfND D t hD x ∨
      y = Refine.noneHalfND D t hD x → cls' y = some (cls x) ∨ (cls x = cls f ∧ cls' y = none) := by
    rintro x hx y (rfl | rfl)
    · have := hs.parent (Refine.someHalfND D t hD x)
      rwa [Refine.parentND_someHalfND] at this
    · have := hs.parent (Refine.noneHalfND D t hD x)
      rwa [Refine.parentND_noneHalfND D t hD hx] at this
  have hf := hs.over_t
  have hS := hhalf f hf _ (Or.inl rfl)
  have hN := hhalf f hf _ (Or.inr rfl)
  have hsplit := hs.split
  have hboth : (cls' (Refine.someHalfND D t hD f) = none ∨
      cls' (Refine.noneHalfND D t hD f) = none) ∧
      (cls' (Refine.someHalfND D t hD f) = some (cls f) ∨
        cls' (Refine.noneHalfND D t hD f) = some (cls f)) := by
    rcases hS with h1 | ⟨-, h1⟩ <;> rcases hN with h2 | ⟨-, h2⟩
    · exact absurd (h1.trans h2.symm) hsplit
    · exact ⟨Or.inr h2, Or.inl h1⟩
    · exact ⟨Or.inl h1, Or.inr h2⟩
    · exact absurd (h1.trans h2.symm) hsplit
  intro o
  cases o with
  | none =>
    rcases hboth.1 with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  | some v =>
    obtain ⟨x, rfl⟩ := hsurj v
    have := hs.parent (Refine.someHalfND D t hD x)
    rw [Refine.parentND_someHalfND] at this
    rcases this with h | ⟨hx, -⟩
    · exact ⟨_, h⟩
    · rw [hx]
      rcases hboth.2 with h | h
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩

end Merge

/-! ### Toward S6: the lcm of the indices, class by class -/

namespace LcmMerge

variable {X α : Type*} [Fintype X] [DecidableEq α] (idx : X → ℕ)

/-- The indices occurring in the class `Q` of a labelling `F`. -/
def idxSet (F : X → α) (Q : α) : Finset ℕ := (Finset.univ.filter fun x ↦ F x = Q).image idx

theorem mem_idxSet {F : X → α} {Q : α} {n : ℕ} :
    n ∈ idxSet idx F Q ↔ ∃ x, F x = Q ∧ idx x = n := by
  simp [idxSet]

theorem mergeFn_eq_mergeFn {S N P P' : α} (h : Merge.mergeFn S N P = Merge.mergeFn S N P')
    (hne : P ≠ P') : (P = N ∧ P' = S) ∨ (P = S ∧ P' = N) := by
  unfold Merge.mergeFn at h
  by_cases hP : P = N <;> by_cases hP' : P' = N
  · exact absurd (hP.trans hP'.symm) hne
  · rw [if_pos hP, if_neg hP'] at h; exact Or.inl ⟨hP, h.symm⟩
  · rw [if_neg hP, if_pos hP'] at h; exact Or.inr ⟨h, hP'⟩
  · rw [if_neg hP, if_neg hP'] at h; exact absurd h hne

/-- **Merging two classes divides the product of the lcms by the merge defect.** -/
theorem prod_lcm_merge (F G : X → α) {S N : α} (hG : ∀ x, G x = Merge.mergeFn S N (F x))
    {x₁ x₂ : X} (h₁ : F x₁ = S) (h₂ : F x₂ = N) (hSN : S ≠ N) {a : ℕ}
    (hC : (idxSet idx F S).lcm id * (idxSet idx F N).lcm id =
      (idxSet idx F S ∪ idxSet idx F N).lcm id * a) :
    ∏ Q ∈ Finset.univ.image F, (idxSet idx F Q).lcm id =
      (∏ Q ∈ Finset.univ.image G, (idxSet idx G Q).lcm id) * a := by
  have hGfun : G = fun x ↦ Merge.mergeFn S N (F x) := funext hG
  subst hGfun
  set m := Merge.mergeFn S N
  have hS : S ∈ Finset.univ.image F := h₁ ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hN : N ∈ Finset.univ.image F := h₂ ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hSe : S ∈ (Finset.univ.image F).erase N := Finset.mem_erase.mpr ⟨hSN, hS⟩
  have himg : Finset.univ.image (fun x ↦ m (F x)) = (Finset.univ.image F).erase N := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨x, rfl⟩
      simp only [m, Merge.mergeFn]
      split_ifs with h
      · exact ⟨hSN, x₁, h₁⟩
      · exact ⟨h, x, rfl⟩
    · rintro ⟨hP, x, rfl⟩
      exact ⟨x, by simp only [m, Merge.mergeFn, if_neg hP]⟩
  have hother : ∀ Q, Q ≠ S → Q ≠ N →
      idxSet idx (fun x ↦ m (F x)) Q = idxSet idx F Q := by
    intro Q hQS hQN
    ext n
    simp only [mem_idxSet]
    refine exists_congr fun x ↦ and_congr_left fun _ ↦ ?_
    simp only [m, Merge.mergeFn]
    split_ifs with h
    · exact ⟨fun h' ↦ absurd h'.symm hQS, fun h' ↦ absurd (h'.symm.trans h) hQN⟩
    · exact Iff.rfl
  have hSS : idxSet idx (fun x ↦ m (F x)) S = idxSet idx F S ∪ idxSet idx F N := by
    ext n
    simp only [mem_idxSet, Finset.mem_union]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [m, Merge.mergeFn] at hx
      split_ifs at hx with h
      · exact Or.inr ⟨x, h, rfl⟩
      · exact Or.inl ⟨x, hx, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨x, by simp only [m, Merge.mergeFn, hx, if_neg hSN], rfl⟩
      · exact ⟨x, by simp only [m, Merge.mergeFn, hx, if_true], rfl⟩
  rw [himg, ← Finset.mul_prod_erase _ _ hN, ← Finset.mul_prod_erase _ _ hSe,
    ← Finset.mul_prod_erase _ _ hSe, hSS]
  have hrest : ∏ Q ∈ ((Finset.univ.image F).erase N).erase S,
      (idxSet idx (fun x ↦ m (F x)) Q).lcm id =
      ∏ Q ∈ ((Finset.univ.image F).erase N).erase S, (idxSet idx F Q).lcm id := by
    refine Finset.prod_congr rfl fun Q hQ ↦ ?_
    have hQS := Finset.ne_of_mem_erase hQ
    have hQN := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hQ)
    rw [hother Q hQS hQN]
  rw [hrest]
  calc _ = ((idxSet idx F S).lcm id * (idxSet idx F N).lcm id) *
        ∏ Q ∈ ((Finset.univ.image F).erase N).erase S, (idxSet idx F Q).lcm id := by ring
    _ = _ := by rw [hC]; ring

/-- **A two-valued merged class comes from a two-valued class**, when the merged classes share
an index. -/
theorem exists_twoValued_of_merge (F G : X → α) {S N : α}
    (hG : ∀ x, G x = Merge.mergeFn S N (F x)) {a : ℕ}
    (haS : a ∈ idxSet idx F S) (haN : a ∈ idxSet idx F N) {Q : α}
    (hQ : 2 ≤ (idxSet idx G Q).card) :
    ∃ x, G x = Q ∧ 2 ≤ (idxSet idx F (F x)).card := by
  have hGfun : G = fun x ↦ Merge.mergeFn S N (F x) := funext hG
  subst hGfun
  by_contra hno
  push Not at hno
  have hle : (idxSet idx (fun x ↦ Merge.mergeFn S N (F x)) Q).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro n hn n' hn'
    obtain ⟨x, hx, rfl⟩ := (mem_idxSet idx).mp hn
    obtain ⟨x', hx', rfl⟩ := (mem_idxSet idx).mp hn'
    have hc : ∀ y, Merge.mergeFn S N (F y) = Q → ∀ b b', b ∈ idxSet idx F (F y) →
        b' ∈ idxSet idx F (F y) → b = b' := fun y hy b b' hb hb' ↦
      Finset.card_le_one.mp (Nat.lt_succ_iff.mp (hno y hy)) b hb b' hb'
    have hm : ∀ y, idx y ∈ idxSet idx F (F y) := fun y ↦ (mem_idxSet idx).mpr ⟨y, rfl, rfl⟩
    by_cases hxx : F x = F x'
    · exact hc x hx _ _ (hm x) ((mem_idxSet idx).mpr ⟨x', hxx.symm, rfl⟩)
    · rcases mergeFn_eq_mergeFn (hx.trans hx'.symm) hxx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 := hc x hx _ a (hm x) (h1 ▸ haN)
        have e2 := hc x' hx' _ a (hm x') (h2 ▸ haS)
        rw [e1, e2]
      · have e1 := hc x hx _ a (hm x) (h1 ▸ haS)
        have e2 := hc x' hx' _ a (hm x') (h2 ▸ haN)
        rw [e1, e2]
  omega

/-- The lcm identity at a split, when one side has the single index `a`. -/
theorem lcm_mul_lcm_of_eq_singleton {A B : Finset ℕ} {a : ℕ} (hA : A = {a}) (hB : a ∈ B) :
    A.lcm id * B.lcm id = (A ∪ B).lcm id * a := by
  rw [hA, Finset.lcm_singleton, Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr hB)]
  simp [mul_comm]

/-- **The condition at a split**: if not both sides carry two indices, and both carry `a`, the
lcm identity holds. -/
theorem lcm_split {A B : Finset ℕ} {a : ℕ} (hA : a ∈ A) (hB : a ∈ B)
    (hnot : ¬ (2 ≤ A.card ∧ 2 ≤ B.card)) :
    A.lcm id * B.lcm id = (A ∪ B).lcm id * a := by
  have hone : ∀ C : Finset ℕ, a ∈ C → ¬ 2 ≤ C.card → C = {a} := fun C hC h2 ↦
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hC, fun b hb ↦
      Finset.card_le_one.mp (by omega) b hb a hC⟩
  by_cases h2A : 2 ≤ A.card
  · have hBa := hone B hB fun h ↦ hnot ⟨h2A, h⟩
    rw [mul_comm, Finset.union_comm]
    exact lcm_mul_lcm_of_eq_singleton hBa hA
  · exact lcm_mul_lcm_of_eq_singleton (hone A hA h2A) hB

end LcmMerge

open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation) in
/-- **On a full-dimensional row, `d` is the lcm of the indices displayed on it** (Part II
`lemma-edge-deno`): every index divides `d` (`SharpRowDenominator.index_dvd_rowDenominator`), and
their lcm clears the row (`EdgeDenominator.rowDenominator_dvd_of_forall_index_dvd`). -/
theorem rowDenominator_eq_lcm {S : CFGraph.{0}} {k : ℕ} {E : GluingDatum S k} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (fd : FullDimensionalSourcePresentation E ι) (r : ι) :
    DraismaVargas.Count.rowDenominator fd.labelling.presentation r =
      ((DraismaVargas.Count.EdgeDenominator.rowEdges fd.labelling r).image
        E.sourceEdgeIndex).lcm id := by
  apply Nat.dvd_antisymm
  · exact DraismaVargas.Count.EdgeDenominator.rowDenominator_dvd_of_forall_index_dvd _ _
      fun e he ↦ Finset.dvd_lcm (Finset.mem_image_of_mem _ he)
  · refine Finset.lcm_dvd fun n hn ↦ ?_
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
    exact DraismaVargas.Count.SharpRowDenominator.index_dvd_rowDenominator fd he

/-! ### Counting the stable paths through a closed set of edges -/

open DraismaVargas.LocalCases.StablePathCount (endCount incidenceCount incidentEdges
  mem_incidentEdges endCount_eq_two) in
open Classical in
/-- **Two ends each**: a set of stable paths has twice as many ends as there are incidences of
its edges at vertices of valency other than two. -/
theorem two_mul_card_paths {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    (hNeOne : ∀ v, nonDanglingValency E v ≠ 1) (hEnds : HasPathEnds E)
    (Sp : Finset (StablePath E)) :
    2 * Sp.card =
      ∑ v ∈ Finset.univ.filter (fun v ↦ ¬ nonDanglingValency E v = 2),
        (Finset.univ.filter fun e : NonDanglingEdge E ↦
          e.stablePath ∈ Sp ∧ Incident E e.1 v).card := by
  have hv : ∀ v, ∑ P ∈ Sp, incidenceCount E v P =
      (Finset.univ.filter fun e : NonDanglingEdge E ↦ e.stablePath ∈ Sp ∧ Incident E e.1 v).card := by
    intro v
    have hfib := Finset.card_eq_sum_card_fiberwise (f := fun e : NonDanglingEdge E ↦ e.stablePath)
      (s := (incidentEdges E v).filter fun e ↦ e.stablePath ∈ Sp) (t := Sp)
      (fun e he ↦ (Finset.mem_filter.mp he).2)
    have hset : (incidentEdges E v).filter (fun e ↦ e.stablePath ∈ Sp) =
        Finset.univ.filter fun e : NonDanglingEdge E ↦ e.stablePath ∈ Sp ∧ Incident E e.1 v := by
      ext e
      simp only [Finset.mem_filter, mem_incidentEdges, Finset.mem_univ, true_and]
      tauto
    rw [← hset, hfib]
    refine Finset.sum_congr rfl fun P hP ↦ ?_
    unfold incidenceCount
    congr 1
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hP⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  calc 2 * Sp.card = ∑ P ∈ Sp, endCount E P := by
        rw [Finset.sum_congr rfl fun P _ ↦ endCount_eq_two E hNeOne hEnds P, Finset.sum_const,
          smul_eq_mul, mul_comm]
    _ = ∑ v ∈ Finset.univ.filter (fun v ↦ ¬ nonDanglingValency E v = 2),
          ∑ P ∈ Sp, incidenceCount E v P := by
        unfold endCount
        rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl fun v _ ↦ hv v

open DraismaVargas.LocalCases.StablePathCount (endCount incidenceCount endCount_eq_two
  sum_incidenceCount_vertex) in
open Classical in
/-- **The stable-path count, as ends**: twice the number of stable paths is the total valency
at the vertices of valency other than two. -/
theorem two_mul_card_stablePath_eq_sum {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    (hNeOne : ∀ v, nonDanglingValency E v ≠ 1) (hEnds : HasPathEnds E) :
    2 * Fintype.card (StablePath E) =
      ∑ v ∈ Finset.univ.filter (fun v ↦ ¬ nonDanglingValency E v = 2),
        nonDanglingValency E v := by
  calc 2 * Fintype.card (StablePath E) = ∑ P : StablePath E, endCount E P := by
        rw [Finset.sum_congr rfl fun P _ ↦ endCount_eq_two E hNeOne hEnds P, Finset.sum_const,
          Finset.card_univ, smul_eq_mul, mul_comm]
    _ = ∑ v ∈ Finset.univ.filter (fun v ↦ ¬ nonDanglingValency E v = 2),
          ∑ P : StablePath E, incidenceCount E v P := by
        unfold endCount
        rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl fun v _ ↦ sum_incidenceCount_vertex E v

open DraismaVargas.LocalCases.Trivalence (stableVertices) in
/-- Refining at the marks keeps the number of stable paths. -/
theorem card_stablePath_refine₃ (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected)
    (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D) :
    Fintype.card (StablePath (refine₃ D π)) = Fintype.card (StablePath D) := by
  have h1 := two_mul_card_stablePath_eq (refine₃ D π) (π.refine₃_connected D hD)
    (π.refine₃_hasPathEnds D hD hEnds) (π.refine₃_trivalent D hD h3)
  have h2 := two_mul_card_stablePath_eq D hD hEnds h3
  rw [π.card_stableVertices_refine₃ D hD] at h1
  omega

/-! ### The glued stable paths through old edges -/

namespace CutPaths

section Defs

variable (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D)

/-- The glued copy of a surviving edge of `refine₃ D π` (`isDangling_liftSE_iff`). -/
def liftND (z : NonDanglingEdge (refine₃ D π)) : NonDanglingEdge (glueDatum D π) :=
  ⟨liftSE D π z.1, (isDangling_liftSE_iff D π hD hT hπ z.1).not.mpr z.2⟩

theorem liftND_injective (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected)
    (hT : graph_connected T) (hπ : π.NonDangling D) : Function.Injective (liftND D π hD hT hπ) :=
  fun _ _ h ↦ Subtype.ext (liftSE_injective D π (congrArg Subtype.val h))

/-- **The glued stable path through an old surviving edge.** -/
def gluedPath (z : NonDanglingEdge (refine₃ D π)) : StablePath (glueDatum D π) :=
  (liftND D π hD hT hπ z).stablePath

/-- A surviving glued edge is **old** when it is the copy of an edge of `refine₃ D π`. -/
def IsOld (x : NonDanglingEdge (glueDatum D π)) : Prop := ∃ z, x.1 = liftSE D π z

end Defs

variable {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D)
include hD hT hπ

theorem isOld_liftND (z : NonDanglingEdge (refine₃ D π)) : IsOld D π (liftND D π hD hT hπ z) :=
  ⟨z.1, rfl⟩

theorem eq_liftND_of_isOld {x : NonDanglingEdge (glueDatum D π)} (h : IsOld D π x) :
    ∃ z, x = liftND D π hD hT hπ z := by
  obtain ⟨z, hz⟩ := h
  refine ⟨⟨z, fun hdz ↦ x.2 ?_⟩, Subtype.ext hz⟩
  rw [hz]
  exact (isDangling_liftSE_iff D π hD hT hπ z).mpr hdz

/-- **Old edges continue into old edges**: at a valency-two vertex of an old edge, the other
surviving edge is old. The only new edges at an old vertex are arms, at a mark, where the
valency is three. -/
theorem isOld_of_consecutive {a b : NonDanglingEdge (glueDatum D π)}
    (h : Consecutive (glueDatum D π) a b) (ha : IsOld D π a) : IsOld D π b := by
  obtain ⟨-, v, hav, hbv, hval⟩ := h
  obtain ⟨z, hz⟩ := ha
  rw [hz] at hav
  rcases sourceVertex_cases_glue D π v with ⟨x, rfl⟩ | ⟨u, rfl⟩ | ⟨k, j, rfl⟩
  · rcases sourceEdge_cases_glue D π b.1 with ⟨z', hz'⟩ | ⟨ε, hε⟩ | ⟨k, j, hkj⟩
    · exact ⟨z', hz'⟩
    · rw [hε] at hbv
      exact absurd hbv (not_incident_newSE_oldVertex₃ D π ε x)
    · exfalso
      have hnd := b.2
      rw [hkj] at hnd hbv
      obtain ⟨hk, i', hi', hrel⟩ := (incident_arm_oldVertex₃_iff D π k j x).mp hbv
      rcases ((hairpinShaped_nonDangling D π hD hT) k j).mp hnd with hj | hj
      · rw [hj] at hi'
        have hii : i' = π.sheet k := (Fin.castSucc_injective _ hi').symm
        rw [hii] at hrel
        have hx : x = markR₃ D π k := (eq_markR₃_iff D π x k).mpr ⟨hk, hrel⟩
        rw [hx, nonDanglingValency_oldVertex₃ D π hD hT hπ, sum_mark_eq_one, markR₃,
          π.nonDanglingValency_markR₃ D hD hπ k] at hval
        omega
      · rw [hj] at hi'
        exact (Fin.castSucc_lt_last i').ne hi'.symm
  · exact absurd hav (not_incident_liftSE_newVertex D π z u)
  · exact absurd hav (not_incident_liftSE_tip D π z k j)

theorem isOld_iff_of_stablePath_eq {a b : NonDanglingEdge (glueDatum D π)}
    (h : a.stablePath = b.stablePath) : IsOld D π a ↔ IsOld D π b :=
  eqvGen_iff_of_closed (fun _ _ hc ha ↦ isOld_of_consecutive hD hT hπ hc ha)
    ((stablePath_eq_iff _ _).mp h)

/-- **Two old edges through a passage of `refine₃ D π` off the marks** lie on one glued path. -/
theorem gluedPath_eq_of_incident {z z' : NonDanglingEdge (refine₃ D π)}
    {x : (refine₃ D π).SourceVertex} (hne : z ≠ z') (hz : Incident _ z.1 x)
    (hz' : Incident _ z'.1 x) (hval : nonDanglingValency (refine₃ D π) x = 2)
    (hm : ∀ k, x ≠ markR₃ D π k) :
    gluedPath D π hD hT hπ z = gluedPath D π hD hT hπ z' := by
  apply stablePath_eq_of_consecutive
  refine ⟨fun h ↦ hne (liftND_injective D π hD hT hπ h), oldVertex₃ D π x,
    (incident_liftSE_oldVertex₃ D π _ x).mpr hz, (incident_liftSE_oldVertex₃ D π _ x).mpr hz', ?_⟩
  rw [nonDanglingValency_oldVertex₃ D π hD hT hπ, sum_mark_eq_zero D π hm, add_zero]
  exact hval

theorem mem_image_gluedPath_iff (e : NonDanglingEdge (glueDatum D π)) :
    e.stablePath ∈ Finset.univ.image (gluedPath D π hD hT hπ) ↔ IsOld D π e := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, hz⟩
    exact (isOld_iff_of_stablePath_eq hD hT hπ hz).mp (isOld_liftND hD hT hπ z)
  · intro he
    obtain ⟨z, rfl⟩ := eq_liftND_of_isOld hD hT hπ he
    exact ⟨z, rfl⟩

open Classical in
/-- The old surviving edges at an old vertex are the copies of those of `refine₃ D π`. -/
theorem card_old_incident (x : (refine₃ D π).SourceVertex) :
    (Finset.univ.filter fun e : NonDanglingEdge (glueDatum D π) ↦
        e.stablePath ∈ Finset.univ.image (gluedPath D π hD hT hπ) ∧
          Incident _ e.1 (oldVertex₃ D π x)).card =
      nonDanglingValency (refine₃ D π) x := by
  simp only [mem_image_gluedPath_iff hD hT hπ]
  rw [← DraismaVargas.LocalCases.StablePathCount.card_incidentEdges]
  symm
  refine Finset.card_bij (fun z _ ↦ liftND D π hD hT hπ z) ?_ ?_ ?_
  · intro z hz
    rw [DraismaVargas.LocalCases.StablePathCount.mem_incidentEdges] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨isOld_liftND hD hT hπ z, (incident_liftSE_oldVertex₃ D π _ x).mpr hz⟩
  · intro z₁ _ z₂ _ h
    exact liftND_injective D π hD hT hπ h
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨z, rfl⟩ := eq_liftND_of_isOld hD hT hπ he.1
    refine ⟨z, ?_, rfl⟩
    rw [DraismaVargas.LocalCases.StablePathCount.mem_incidentEdges]
    exact (incident_liftSE_oldVertex₃ D π _ x).mp he.2

open Classical in
theorem card_old_incident_eq_zero {v : (glueDatum D π).SourceVertex}
    (hv : ∀ x, v ≠ oldVertex₃ D π x) :
    (Finset.univ.filter fun e : NonDanglingEdge (glueDatum D π) ↦
        e.stablePath ∈ Finset.univ.image (gluedPath D π hD hT hπ) ∧ Incident _ e.1 v).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro e - ⟨hold, hinc⟩
  obtain ⟨z, hz⟩ := (mem_image_gluedPath_iff hD hT hπ e).mp hold
  rw [hz] at hinc
  rcases sourceVertex_cases_glue D π v with ⟨x, rfl⟩ | ⟨u, rfl⟩ | ⟨k, j, rfl⟩
  · exact hv x rfl
  · exact not_incident_liftSE_newVertex D π z u hinc
  · exact not_incident_liftSE_tip D π z k j hinc

open Classical in
/-- **The count of the glued paths through old edges** (two ends each): `#paths(D) + 3`. The
ends of these paths are the old incidences at the old vertices of valency other than two, which
are the branch vertices of `refine₃ D π` and the three marks (two old incidences each). -/
theorem card_image_gluedPath (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3)
    (hEnds : HasPathEnds D) :
    (Finset.univ.image (gluedPath D π hD hT hπ)).card = Fintype.card (StablePath D) + 3 := by
  have hG := glueDatum_connected D π hD hT
  have hR := π.refine₃_connected D hD
  have hcount := two_mul_card_paths (glueDatum D π)
    (DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG)
    (hasPathEnds_glue D π hD hT hT0 hπ hEnds) (Finset.univ.image (gluedPath D π hD hT hπ))
  set A := Finset.univ.filter fun x : (refine₃ D π).SourceVertex ↦
    ¬ nonDanglingValency (glueDatum D π) (oldVertex₃ D π x) = 2 with hA
  have hsum : ∑ v ∈ Finset.univ.filter
        (fun v ↦ ¬ nonDanglingValency (glueDatum D π) v = 2),
      (Finset.univ.filter fun e : NonDanglingEdge (glueDatum D π) ↦
        e.stablePath ∈ Finset.univ.image (gluedPath D π hD hT hπ) ∧ Incident _ e.1 v).card =
      ∑ x ∈ A, nonDanglingValency (refine₃ D π) x := by
    symm
    calc ∑ x ∈ A, nonDanglingValency (refine₃ D π) x =
          ∑ x ∈ A, (Finset.univ.filter fun e : NonDanglingEdge (glueDatum D π) ↦
            e.stablePath ∈ Finset.univ.image (gluedPath D π hD hT hπ) ∧
              Incident _ e.1 (oldVertex₃ D π x)).card :=
          Finset.sum_congr rfl fun x _ ↦ (card_old_incident hD hT hπ x).symm
      _ = ∑ v ∈ A.map ⟨oldVertex₃ D π, oldVertex₃_injective D π⟩,
            (Finset.univ.filter fun e : NonDanglingEdge (glueDatum D π) ↦
              e.stablePath ∈ Finset.univ.image (gluedPath D π hD hT hπ) ∧
                Incident _ e.1 v).card := by
          rw [Finset.sum_map]
          rfl
      _ = _ := by
          refine Finset.sum_subset ?_ ?_
          · intro v hv
            obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv
            simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hx
          · intro v hv hnot
            apply card_old_incident_eq_zero hD hT hπ
            rintro x rfl
            apply hnot
            refine Finset.mem_map.mpr ⟨x, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
            simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hv
  have hpt : ∀ x : (refine₃ D π).SourceVertex,
      (if ¬ nonDanglingValency (glueDatum D π) (oldVertex₃ D π x) = 2 then
        nonDanglingValency (refine₃ D π) x else 0) =
      (if ¬ nonDanglingValency (refine₃ D π) x = 2 then nonDanglingValency (refine₃ D π) x
        else 0) + 2 * ∑ k, if x = markR₃ D π k then 1 else 0 := by
    intro x
    rw [nonDanglingValency_oldVertex₃ D π hD hT hπ]
    by_cases hm : ∃ k, x = markR₃ D π k
    · obtain ⟨k, rfl⟩ := hm
      rw [sum_mark_eq_one, show nonDanglingValency (refine₃ D π) (markR₃ D π k) = 2 from
        π.nonDanglingValency_markR₃ D hD hπ k]
      simp
    · push Not at hm
      rw [sum_mark_eq_zero D π hm]
      simp
  have hmarks : (∑ x : (refine₃ D π).SourceVertex, ∑ k : Fin 3,
      if x = markR₃ D π k then 1 else 0) = 3 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun k _ ↦ Finset.sum_ite_eq' Finset.univ (markR₃ D π k) fun _ ↦ 1]
    simp
  have hR3 := two_mul_card_stablePath_eq_sum (refine₃ D π)
    (DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hR)
    (π.refine₃_hasPathEnds D hD hEnds)
  have hAsum : ∑ x ∈ A, nonDanglingValency (refine₃ D π) x =
      2 * Fintype.card (StablePath (refine₃ D π)) + 6 := by
    rw [hA, Finset.sum_filter, Finset.sum_congr rfl fun x _ ↦ hpt x, Finset.sum_add_distrib,
      ← Finset.mul_sum, hmarks, hR3, Finset.sum_filter]
    omega
  have hcard := card_stablePath_refine₃ D π hD h3 hEnds
  omega

end CutPaths

/-! ### The three marks in `refine₃ D π` -/

namespace Placement

variable (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected) (hπ : π.NonDangling D)

theorem markR₃_zero_eq : markR₃ D π 0 =
    Refine.oldSV _ π.edge₂ (Refine.oldSV _ π.edge₁ (Refine.freshOf D π.edge₀ (π.markEdge₀ D hπ).1 rfl)) :=
  rfl

theorem markR₃_one_eq : markR₃ D π 1 =
    Refine.oldSV _ π.edge₂ (Refine.freshOf _ π.edge₁ (π.markEdge₁ D hD hπ).1 rfl) :=
  rfl

theorem markR₃_two_eq : markR₃ D π 2 = Refine.freshOf _ π.edge₂ (π.markEdge₂ D hD hπ).1 rfl :=
  rfl

end Placement

namespace CutPaths

section Defs

variable (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D)

/-- The glued paths merged back at mark `2`: a labelling of the surviving edges of `D` refined at
marks `0`, `1`. -/
def cut₂ : NonDanglingEdge (refineDatum (refineDatum D π.edge₀) π.edge₁) →
    StablePath (glueDatum D π) :=
  Merge.merged _ π.edge₂ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ) (gluedPath D π hD hT hπ)

/-- Merged back at marks `2`, `1`. -/
def cut₁ : NonDanglingEdge (refineDatum D π.edge₀) → StablePath (glueDatum D π) :=
  Merge.merged _ π.edge₁ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ) (cut₂ D π hD hT hπ)

/-- Merged back at all three marks. -/
def cut₀ : NonDanglingEdge D → StablePath (glueDatum D π) :=
  Merge.merged D π.edge₀ hD (π.markEdge₀ D hπ) (cut₁ D π hD hT hπ)

end Defs

variable {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D)
include hD hT hπ

/-- **Mark `2` is the only cut over `edge₂`.** -/
theorem others₃ : Merge.Others _ π.edge₂ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ)
    (gluedPath D π hD hT hπ) := by
  intro f' hf' hne
  have h₂ := π.refine₂_connected D hD
  obtain ⟨hs, hn⟩ := Refine.incident_halves _ π.edge₂ h₂ hf'
  refine gluedPath_eq_of_incident hD hT hπ (Refine.someHalfND_ne_noneHalfND _ _ h₂ hf') hs hn
    (Refine.nonDanglingValency_freshOf _ _ h₂ f' hf') fun k ↦ ?_
  match k with
  | 0 => exact fun h ↦ Refine.oldSV_ne_freshSV _ _ _ _ _ (h.trans (π.markR₃_zero_eq D hπ)).symm
  | 1 => exact fun h ↦ Refine.oldSV_ne_freshSV _ _ _ _ _ (h.trans (π.markR₃_one_eq D hD hπ)).symm
  | 2 => exact fun h ↦ hne (Subtype.ext (Refine.freshOf_inj _ _ hf' rfl
      (h.trans (π.markR₃_two_eq D hD hπ))))

theorem cut₂_parentND (z : NonDanglingEdge (refine₃ D π)) :
    cut₂ D π hD hT hπ (Refine.parentND _ π.edge₂ (π.refine₂_connected D hD) z) =
      Merge.mergeFn (gluedPath D π hD hT hπ
          (Refine.someHalfND _ _ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ)))
        (gluedPath D π hD hT hπ
          (Refine.noneHalfND _ _ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ)))
        (gluedPath D π hD hT hπ z) :=
  Merge.merged_parentND (others₃ hD hT hπ) z

/-- **Mark `1` is the only cut over `edge₁`.** -/
theorem others₂ : Merge.Others _ π.edge₁ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ)
    (cut₂ D π hD hT hπ) := by
  intro f' hf' hne
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  obtain ⟨hs, hn⟩ := Refine.incident_halves _ π.edge₁ h₁ hf'
  obtain ⟨hzz, hz, hz'⟩ := Refine.pieceND_pair _ π.edge₂ h₂
    (Refine.someHalfND_ne_noneHalfND _ _ h₁ hf') hs hn
  set u := Refine.freshOf _ π.edge₁ f'.1 hf'
  have e1 := cut₂_parentND hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u (Refine.someHalfND _ _ h₁ f'))
  have e2 := cut₂_parentND hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u (Refine.noneHalfND _ _ h₁ f'))
  rw [Refine.parentND_pieceND] at e1 e2
  rw [e1, e2]
  suffices hg : gluedPath D π hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u (Refine.someHalfND _ _ h₁ f')) =
      gluedPath D π hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u (Refine.noneHalfND _ _ h₁ f')) by
    rw [hg]
  refine gluedPath_eq_of_incident hD hT hπ hzz hz hz' ?_ fun k ↦ ?_
  · rw [Refine.nonDanglingValency_oldSV _ _ h₂]
    exact Refine.nonDanglingValency_freshOf _ _ h₁ f' hf'
  match k with
  | 0 =>
    intro h
    have h' := Refine.oldSV_injective _ _ (h.trans (π.markR₃_zero_eq D hπ))
    exact Refine.oldSV_ne_freshSV _ _ _ _ _ h'.symm
  | 1 =>
    intro h
    have h' := Refine.oldSV_injective _ _ (h.trans (π.markR₃_one_eq D hD hπ))
    exact hne (Subtype.ext (Refine.freshOf_inj _ _ hf' rfl h'))
  | 2 => exact fun h ↦ Refine.oldSV_ne_freshSV _ _ _ _ _ (h.trans (π.markR₃_two_eq D hD hπ))

theorem cut₁_parentND (w : NonDanglingEdge (refineDatum (refineDatum D π.edge₀) π.edge₁)) :
    cut₁ D π hD hT hπ (Refine.parentND _ π.edge₁ (π.refine₁_connected D hD) w) =
      Merge.mergeFn (cut₂ D π hD hT hπ
          (Refine.someHalfND _ _ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ)))
        (cut₂ D π hD hT hπ
          (Refine.noneHalfND _ _ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ)))
        (cut₂ D π hD hT hπ w) :=
  Merge.merged_parentND (others₂ hD hT hπ) w

/-- **Mark `0` is the only cut over `edge₀`.** -/
theorem others₁ : Merge.Others D π.edge₀ hD (π.markEdge₀ D hπ) (cut₁ D π hD hT hπ) := by
  intro f' hf' hne
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  obtain ⟨hs, hn⟩ := Refine.incident_halves D π.edge₀ hD hf'
  obtain ⟨hww, hw, hw'⟩ := Refine.pieceND_pair _ π.edge₁ h₁
    (Refine.someHalfND_ne_noneHalfND _ _ hD hf') hs hn
  obtain ⟨hzz, hz, hz'⟩ := Refine.pieceND_pair _ π.edge₂ h₂ hww hw hw'
  set u := Refine.freshOf D π.edge₀ f'.1 hf'
  set u' := Refine.oldSV _ π.edge₁ u
  have e1 := cut₁_parentND hD hT hπ (Refine.pieceND _ π.edge₁ h₁ u (Refine.someHalfND _ _ hD f'))
  have e2 := cut₁_parentND hD hT hπ (Refine.pieceND _ π.edge₁ h₁ u (Refine.noneHalfND _ _ hD f'))
  rw [Refine.parentND_pieceND] at e1 e2
  have e3 := cut₂_parentND hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u'
    (Refine.pieceND _ π.edge₁ h₁ u (Refine.someHalfND _ _ hD f')))
  have e4 := cut₂_parentND hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u'
    (Refine.pieceND _ π.edge₁ h₁ u (Refine.noneHalfND _ _ hD f')))
  rw [Refine.parentND_pieceND] at e3 e4
  rw [e1, e2, e3, e4]
  suffices hg : gluedPath D π hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u'
      (Refine.pieceND _ π.edge₁ h₁ u (Refine.someHalfND _ _ hD f'))) =
      gluedPath D π hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u'
        (Refine.pieceND _ π.edge₁ h₁ u (Refine.noneHalfND _ _ hD f'))) by
    rw [hg]
  refine gluedPath_eq_of_incident hD hT hπ hzz hz hz' ?_ fun k ↦ ?_
  · rw [Refine.nonDanglingValency_oldSV _ _ h₂, Refine.nonDanglingValency_oldSV _ _ h₁]
    exact Refine.nonDanglingValency_freshOf _ _ hD f' hf'
  match k with
  | 0 =>
    intro h
    have h' := Refine.oldSV_injective _ _ (Refine.oldSV_injective _ _
      (h.trans (π.markR₃_zero_eq D hπ)))
    exact hne (Subtype.ext (Refine.freshOf_inj _ _ hf' rfl h'))
  | 1 =>
    intro h
    have h' := Refine.oldSV_injective _ _ (h.trans (π.markR₃_one_eq D hD hπ))
    exact Refine.oldSV_ne_freshSV _ _ _ _ _ h'
  | 2 => exact fun h ↦ Refine.oldSV_ne_freshSV _ _ _ _ _ (h.trans (π.markR₃_two_eq D hD hπ))

theorem cut₀_parentND (y : NonDanglingEdge (refineDatum D π.edge₀)) :
    cut₀ D π hD hT hπ (Refine.parentND D π.edge₀ hD y) =
      Merge.mergeFn (cut₁ D π hD hT hπ (Refine.someHalfND _ _ hD (π.markEdge₀ D hπ)))
        (cut₁ D π hD hT hπ (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ)))
        (cut₁ D π hD hT hπ y) :=
  Merge.merged_parentND (others₁ hD hT hπ) y

/-- **Merged back at all three marks, the classes are unions of stable paths of `D`.** -/
theorem cut₀_eq_of_consecutive {x x' : NonDanglingEdge D} (h : Consecutive D x x') :
    cut₀ D π hD hT hπ x = cut₀ D π hD hT hπ x' := by
  obtain ⟨hne, v, hx, hx', hval⟩ := h
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  obtain ⟨hyy, hy, hy'⟩ := Refine.pieceND_pair D π.edge₀ hD hne hx hx'
  obtain ⟨hww, hw, hw'⟩ := Refine.pieceND_pair _ π.edge₁ h₁ hyy hy hy'
  obtain ⟨hzz, hz, hz'⟩ := Refine.pieceND_pair _ π.edge₂ h₂ hww hw hw'
  have e1 := cut₀_parentND hD hT hπ (Refine.pieceND D π.edge₀ hD v x)
  have e2 := cut₀_parentND hD hT hπ (Refine.pieceND D π.edge₀ hD v x')
  rw [Refine.parentND_pieceND] at e1 e2
  set v₁ := Refine.oldSV D π.edge₀ v
  set v₂ := Refine.oldSV _ π.edge₁ v₁
  have e3 := cut₁_parentND hD hT hπ (Refine.pieceND _ π.edge₁ h₁ v₁ (Refine.pieceND D π.edge₀ hD v x))
  have e4 := cut₁_parentND hD hT hπ
    (Refine.pieceND _ π.edge₁ h₁ v₁ (Refine.pieceND D π.edge₀ hD v x'))
  rw [Refine.parentND_pieceND] at e3 e4
  have e5 := cut₂_parentND hD hT hπ (Refine.pieceND _ π.edge₂ h₂ v₂
    (Refine.pieceND _ π.edge₁ h₁ v₁ (Refine.pieceND D π.edge₀ hD v x)))
  have e6 := cut₂_parentND hD hT hπ (Refine.pieceND _ π.edge₂ h₂ v₂
    (Refine.pieceND _ π.edge₁ h₁ v₁ (Refine.pieceND D π.edge₀ hD v x')))
  rw [Refine.parentND_pieceND] at e5 e6
  rw [e1, e2, e3, e4, e5, e6]
  suffices hg : gluedPath D π hD hT hπ (Refine.pieceND _ π.edge₂ h₂ v₂
      (Refine.pieceND _ π.edge₁ h₁ v₁ (Refine.pieceND D π.edge₀ hD v x))) =
      gluedPath D π hD hT hπ (Refine.pieceND _ π.edge₂ h₂ v₂
        (Refine.pieceND _ π.edge₁ h₁ v₁ (Refine.pieceND D π.edge₀ hD v x'))) by
    rw [hg]
  refine gluedPath_eq_of_incident hD hT hπ hzz hz hz' ?_ fun k ↦ ?_
  · rw [Refine.nonDanglingValency_oldSV _ _ h₂, Refine.nonDanglingValency_oldSV _ _ h₁,
      Refine.nonDanglingValency_oldSV _ _ hD]
    exact hval
  match k with
  | 0 =>
    intro h
    have h' := Refine.oldSV_injective _ _ (Refine.oldSV_injective _ _
      (h.trans (π.markR₃_zero_eq D hπ)))
    exact Refine.oldSV_ne_freshSV _ _ _ _ _ h'
  | 1 =>
    intro h
    have h' := Refine.oldSV_injective _ _ (h.trans (π.markR₃_one_eq D hD hπ))
    exact Refine.oldSV_ne_freshSV _ _ _ _ _ h'
  | 2 => exact fun h ↦ Refine.oldSV_ne_freshSV _ _ _ _ _ (h.trans (π.markR₃_two_eq D hD hπ))

open Classical in
/-- **The cut-path labels** (§5.3). Label the glued paths through old edges
so that, merged back one mark at a time, each stage splits one class at its mark and the first
stage is the stable labelling of `D`. The separations at the marks are not shown separately:
merging back at a mark loses one class exactly when the mark separates
(`Merge.card_image_merged`), there are `#paths(D) + 3` glued paths through old edges
(`card_image_gluedPath`), and after the three merges at most `#paths(D)` classes remain
(`cut₀_eq_of_consecutive`). -/
theorem exists_cutLabels (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3)
    (hEnds : HasPathEnds D) {ι : Type*} [Fintype ι] [DecidableEq ι] (rowLab : StablePath D ≃ ι) :
    ∃ (cls₁ : NonDanglingEdge (refineDatum D π.edge₀) → Option ι)
      (cls₂ : NonDanglingEdge (refineDatum (refineDatum D π.edge₀) π.edge₁) → Option (Option ι))
      (lab : StablePath (glueDatum D π) → Option (Option (Option ι))),
      SplitsAt D π.edge₀ hD (fun x ↦ rowLab x.stablePath) cls₁ (π.markEdge₀ D hπ) ∧
      SplitsAt _ π.edge₁ (π.refine₁_connected D hD) cls₁ cls₂ (π.markEdge₁ D hD hπ) ∧
      SplitsAt _ π.edge₂ (π.refine₂_connected D hD) cls₂
        (fun z ↦ lab (gluedPath D π hD hT hπ z)) (π.markEdge₂ D hD hπ) ∧
      Set.InjOn lab (Finset.univ.image (gluedPath D π hD hT hπ) : Set _) ∧
      Function.Surjective (fun z ↦ lab (gluedPath D π hD hT hπ z)) := by
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  -- the cardinality chain
  have hc₂ := Merge.card_image_merged (others₃ hD hT hπ)
  have hc₁ := Merge.card_image_merged (others₂ hD hT hπ)
  have hc₀ := Merge.card_image_merged (others₁ hD hT hπ)
  have hg := card_image_gluedPath hD hT hπ hT0 h3 hEnds
  obtain ⟨κ, hκ⟩ : ∃ κ : StablePath D → StablePath (glueDatum D π),
      ∀ x : NonDanglingEdge D, κ x.stablePath = cut₀ D π hD hT hπ x :=
    ⟨Quot.lift (cut₀ D π hD hT hπ) fun _ _ h ↦ cut₀_eq_of_consecutive hD hT hπ h, fun _ ↦ rfl⟩
  have himκ : Finset.univ.image (cut₀ D π hD hT hπ) = Finset.univ.image κ := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.stablePath, hκ x⟩
    · rintro ⟨C, rfl⟩
      obtain ⟨x, rfl⟩ := Quot.exists_rep C
      exact ⟨x, (hκ x).symm⟩
  have hκle : (Finset.univ.image κ).card ≤ Fintype.card (StablePath D) :=
    Finset.card_image_le.trans (by rw [Finset.card_univ])
  change (Finset.univ.image (cut₀ D π hD hT hπ)).card + _ = _ at hc₀
  rw [himκ] at hc₀
  change (Finset.univ.image (cut₂ D π hD hT hπ)).card + _ = _ at hc₂
  change (Finset.univ.image (cut₁ D π hD hT hπ)).card + _ = _ at hc₁
  -- the separations
  have hs₃ : gluedPath D π hD hT hπ (Refine.someHalfND _ _ h₂ (π.markEdge₂ D hD hπ)) ≠
      gluedPath D π hD hT hπ (Refine.noneHalfND _ _ h₂ (π.markEdge₂ D hD hπ)) := by
    intro h
    rw [if_pos h] at hc₂
    split_ifs at hc₁ hc₀ <;> omega
  have hs₂ : cut₂ D π hD hT hπ (Refine.someHalfND _ _ h₁ (π.markEdge₁ D hD hπ)) ≠
      cut₂ D π hD hT hπ (Refine.noneHalfND _ _ h₁ (π.markEdge₁ D hD hπ)) := by
    intro h
    rw [if_pos h] at hc₁
    split_ifs at hc₂ hc₀ <;> omega
  have hs₁ : cut₁ D π hD hT hπ (Refine.someHalfND _ _ hD (π.markEdge₀ D hπ)) ≠
      cut₁ D π hD hT hπ (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ)) := by
    intro h
    rw [if_pos h] at hc₀
    split_ifs at hc₂ hc₁ <;> omega
  have hκcard : (Finset.univ.image κ).card = (Finset.univ : Finset (StablePath D)).card := by
    rw [if_neg hs₃] at hc₂
    rw [if_neg hs₂] at hc₁
    rw [if_neg hs₁] at hc₀
    rw [Finset.card_univ]
    omega
  have hκinj : Function.Injective κ := by
    have := Finset.card_image_iff.mp hκcard
    exact fun a b h ↦ this (Finset.mem_coe.mpr (Finset.mem_univ a))
      (Finset.mem_coe.mpr (Finset.mem_univ b)) h
  -- the labels
  have : Nonempty (StablePath D) := ⟨(π.markEdge₀ D hπ).stablePath⟩
  obtain ⟨lab₀, hlab₀⟩ : ∃ lab₀ : StablePath (glueDatum D π) → ι,
      ∀ x : NonDanglingEdge D, rowLab x.stablePath = lab₀ (cut₀ D π hD hT hπ x) := by
    refine ⟨fun P ↦ rowLab (Function.invFun κ P), fun x ↦ ?_⟩
    show rowLab x.stablePath = rowLab (Function.invFun κ (cut₀ D π hD hT hπ x))
    rw [← hκ, Function.leftInverse_invFun hκinj]
  let lab₁ := Merge.liftLabel (cut₁ D π hD hT hπ (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ))) lab₀
  let lab₂ := Merge.liftLabel
    (cut₂ D π hD hT hπ (Refine.noneHalfND _ _ h₁ (π.markEdge₁ D hD hπ))) lab₁
  let lab₃ := Merge.liftLabel
    (gluedPath D π hD hT hπ (Refine.noneHalfND _ _ h₂ (π.markEdge₂ D hD hπ))) lab₂
  have hf₀ : (π.markEdge₀ D hπ).1.1.1 = π.edge₀ := rfl
  have ho₁ := others₁ hD hT hπ
  have s₁ := Merge.splitsAt_of_separated hf₀ ho₁ hs₁ lab₀ _ hlab₀
  have hf₁ : (π.markEdge₁ D hD hπ).1.1.1 = π.edge₁ := rfl
  have ho₂ := others₂ hD hT hπ
  have s₂ := Merge.splitsAt_of_separated hf₁ ho₂ hs₂ lab₁
    (fun y ↦ lab₁ (cut₁ D π hD hT hπ y)) fun _ ↦ rfl
  have hf₂ : (π.markEdge₂ D hD hπ).1.1.1 = π.edge₂ := rfl
  have ho₃ := others₃ hD hT hπ
  have s₃ := Merge.splitsAt_of_separated hf₂ ho₃ hs₃ lab₂
    (fun y ↦ lab₂ (cut₂ D π hD hT hπ y)) fun _ ↦ rfl
  have hsurj₀ : Function.Surjective fun x : NonDanglingEdge D ↦ rowLab x.stablePath := by
    intro i
    obtain ⟨x, hx⟩ := Quot.exists_rep (rowLab.symm i)
    refine ⟨x, ?_⟩
    show rowLab x.stablePath = i
    rw [show x.stablePath = rowLab.symm i from hx, Equiv.apply_symm_apply]
  have hsurj : Function.Surjective fun z ↦ lab₃ (gluedPath D π hD hT hπ z) :=
    Merge.surjective_of_splitsAt s₃ (Merge.surjective_of_splitsAt s₂
      (Merge.surjective_of_splitsAt s₁ hsurj₀))
  refine ⟨_, _, lab₃, s₁, s₂, s₃, ?_, hsurj⟩
  have himg : (Finset.univ.image (gluedPath D π hD hT hπ)).image lab₃ = Finset.univ := by
    rw [Finset.image_image]
    exact Finset.image_univ_of_surjective hsurj
  apply Finset.card_image_iff.mp
  rw [himg, hg, Finset.card_univ, Fintype.card_option, Fintype.card_option, Fintype.card_option,
    Fintype.card_congr rowLab]

omit hD hT hπ in
/-- The index of an old edge is its index in `refine₃ D π`. -/
theorem sourceEdgeIndex_liftSE (z : (refine₃ D π).SourceEdge) :
    (glueDatum D π).sourceEdgeIndex (liftSE D π z) = (refine₃ D π).sourceEdgeIndex z := by
  unfold GluingDatum.sourceEdgeIndex
  show ((glueDatum D π).edgePartition (π.liftE₃ z.1.1)).blockCard z.1.2.castSucc = _
  rw [glueDatum_edgePartition_liftE₃, SheetOps.blockCard_extendNew_castSucc]

/-- **Sums over the surviving glued edges** of a function vanishing off the old ones are sums
over the surviving edges of `refine₃ D π`. -/
theorem sum_eq_sum_liftND (F : NonDanglingEdge (glueDatum D π) → ℚ)
    (hF : ∀ x, ¬ IsOld D π x → F x = 0) :
    ∑ x, F x = ∑ z, F (liftND D π hD hT hπ z) := by
  classical
  rw [← Finset.sum_image (fun a _ b _ h ↦ liftND_injective D π hD hT hπ h)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx ↦ hF x fun hold ↦ hx ?_).symm
  obtain ⟨z, rfl⟩ := eq_liftND_of_isOld hD hT hπ hold
  exact Finset.mem_image_of_mem _ (Finset.mem_univ z)

/-- **The glued path through an old edge is not a hairpin.** -/
theorem gluedPath_ne_hairpin (z : NonDanglingEdge (refine₃ D π)) (k : Fin 3) :
    gluedPath D π hD hT hπ z ≠
      NonDanglingEdge.stablePath (⟨_, (hairpin_not_isDangling D π hD hT k).1⟩ :
        NonDanglingEdge (glueDatum D π)) := by
  intro h
  obtain ⟨z', hz'⟩ := (isOld_iff_of_stablePath_eq hD hT hπ h).mp (isOld_liftND hD hT hπ z)
  exact liftSE_ne_arm D π z' k _ hz'.symm

end CutPaths

/-! ### Toward S6: stages, separations, and the ramified passages -/

namespace CutPaths

section Defs

variable (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected)

/-- The ancestor in `D` of a surviving edge of `refine₃ D π`. -/
def anc (z : NonDanglingEdge (refine₃ D π)) : NonDanglingEdge D :=
  Refine.parentND D π.edge₀ hD (Refine.parentND _ π.edge₁ (π.refine₁_connected D hD)
    (Refine.parentND _ π.edge₂ (π.refine₂_connected D hD) z))

/-- The index of a surviving edge of `refine₃ D π`. -/
def idx (z : NonDanglingEdge (refine₃ D π)) : ℕ := (refine₃ D π).sourceEdgeIndex z.1

/-- `refine₃ D π`, refined at mark `0`, then the vertex `v` of `D` in it. -/
def lift₃V (v : D.SourceVertex) : (refine₃ D π).SourceVertex :=
  Refine.oldSV _ π.edge₂ (Refine.oldSV _ π.edge₁ (Refine.oldSV D π.edge₀ v))

end Defs

section Stages

variable (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D)

/-- The glued paths merged back at mark `2`, on the edges of `refine₃ D π`. -/
def stage₂ (z : NonDanglingEdge (refine₃ D π)) : StablePath (glueDatum D π) :=
  Merge.mergeFn
    (gluedPath D π hD hT hπ (Refine.someHalfND _ _ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ)))
    (gluedPath D π hD hT hπ (Refine.noneHalfND _ _ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ)))
    (gluedPath D π hD hT hπ z)

/-- Merged back at marks `2`, `1`. -/
def stage₁ (z : NonDanglingEdge (refine₃ D π)) : StablePath (glueDatum D π) :=
  Merge.mergeFn
    (cut₂ D π hD hT hπ (Refine.someHalfND _ _ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ)))
    (cut₂ D π hD hT hπ (Refine.noneHalfND _ _ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ)))
    (stage₂ D π hD hT hπ z)

/-- Merged back at all three marks. -/
def stage₀ (z : NonDanglingEdge (refine₃ D π)) : StablePath (glueDatum D π) :=
  Merge.mergeFn
    (cut₁ D π hD hT hπ (Refine.someHalfND _ _ hD (π.markEdge₀ D hπ)))
    (cut₁ D π hD hT hπ (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ)))
    (stage₁ D π hD hT hπ z)

end Stages

variable {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D)
include hD hT hπ

theorem cut₂_parent (z : NonDanglingEdge (refine₃ D π)) :
    cut₂ D π hD hT hπ (Refine.parentND _ π.edge₂ (π.refine₂_connected D hD) z) =
      stage₂ D π hD hT hπ z :=
  cut₂_parentND hD hT hπ z

theorem cut₁_parent (z : NonDanglingEdge (refine₃ D π)) :
    cut₁ D π hD hT hπ (Refine.parentND _ π.edge₁ (π.refine₁_connected D hD)
      (Refine.parentND _ π.edge₂ (π.refine₂_connected D hD) z)) = stage₁ D π hD hT hπ z := by
  rw [cut₁_parentND hD hT hπ, cut₂_parent hD hT hπ]
  rfl

theorem cut₀_anc (z : NonDanglingEdge (refine₃ D π)) :
    cut₀ D π hD hT hπ (anc D π hD z) = stage₀ D π hD hT hπ z := by
  rw [anc, cut₀_parentND hD hT hπ, cut₁_parent hD hT hπ]
  rfl

omit hT hπ in
theorem idx_eq_anc (z : NonDanglingEdge (refine₃ D π)) :
    idx D π z = D.sourceEdgeIndex (anc D π hD z).1 := by
  rw [idx, Refine.sourceEdgeIndex_eq, Refine.sourceEdgeIndex_eq, Refine.sourceEdgeIndex_eq]
  rfl

/-- **The separations at the marks and the stable paths of `D`** (the chain of
`exists_cutLabels`). -/
theorem separations (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3)
    (hEnds : HasPathEnds D) :
    gluedPath D π hD hT hπ (Refine.someHalfND _ _ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ)) ≠
        gluedPath D π hD hT hπ
          (Refine.noneHalfND _ _ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ)) ∧
      cut₂ D π hD hT hπ (Refine.someHalfND _ _ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ)) ≠
        cut₂ D π hD hT hπ
          (Refine.noneHalfND _ _ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ)) ∧
      cut₁ D π hD hT hπ (Refine.someHalfND _ _ hD (π.markEdge₀ D hπ)) ≠
        cut₁ D π hD hT hπ (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ)) ∧
      ∀ x x' : NonDanglingEdge D, cut₀ D π hD hT hπ x = cut₀ D π hD hT hπ x' →
        x.stablePath = x'.stablePath := by
  classical
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  have hc₂ := Merge.card_image_merged (others₃ hD hT hπ)
  have hc₁ := Merge.card_image_merged (others₂ hD hT hπ)
  have hc₀ := Merge.card_image_merged (others₁ hD hT hπ)
  have hg := card_image_gluedPath hD hT hπ hT0 h3 hEnds
  obtain ⟨κ, hκ⟩ : ∃ κ : StablePath D → StablePath (glueDatum D π),
      ∀ x : NonDanglingEdge D, κ x.stablePath = cut₀ D π hD hT hπ x :=
    ⟨Quot.lift (cut₀ D π hD hT hπ) fun _ _ h ↦ cut₀_eq_of_consecutive hD hT hπ h, fun _ ↦ rfl⟩
  have himκ : Finset.univ.image (cut₀ D π hD hT hπ) = Finset.univ.image κ := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.stablePath, hκ x⟩
    · rintro ⟨C, rfl⟩
      obtain ⟨x, rfl⟩ := Quot.exists_rep C
      exact ⟨x, (hκ x).symm⟩
  have hκle : (Finset.univ.image κ).card ≤ Fintype.card (StablePath D) :=
    Finset.card_image_le.trans (by rw [Finset.card_univ])
  change (Finset.univ.image (cut₀ D π hD hT hπ)).card + _ = _ at hc₀
  rw [himκ] at hc₀
  change (Finset.univ.image (cut₂ D π hD hT hπ)).card + _ = _ at hc₂
  change (Finset.univ.image (cut₁ D π hD hT hπ)).card + _ = _ at hc₁
  have hs₃ : gluedPath D π hD hT hπ (Refine.someHalfND _ _ h₂ (π.markEdge₂ D hD hπ)) ≠
      gluedPath D π hD hT hπ (Refine.noneHalfND _ _ h₂ (π.markEdge₂ D hD hπ)) := by
    intro h
    rw [if_pos h] at hc₂
    split_ifs at hc₁ hc₀ <;> omega
  have hs₂ : cut₂ D π hD hT hπ (Refine.someHalfND _ _ h₁ (π.markEdge₁ D hD hπ)) ≠
      cut₂ D π hD hT hπ (Refine.noneHalfND _ _ h₁ (π.markEdge₁ D hD hπ)) := by
    intro h
    rw [if_pos h] at hc₁
    split_ifs at hc₂ hc₀ <;> omega
  have hs₁ : cut₁ D π hD hT hπ (Refine.someHalfND _ _ hD (π.markEdge₀ D hπ)) ≠
      cut₁ D π hD hT hπ (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ)) := by
    intro h
    rw [if_pos h] at hc₀
    split_ifs at hc₂ hc₁ <;> omega
  refine ⟨hs₃, hs₂, hs₁, fun x x' h ↦ ?_⟩
  have hκcard : (Finset.univ.image κ).card = (Finset.univ : Finset (StablePath D)).card := by
    rw [if_neg hs₃] at hc₂
    rw [if_neg hs₂] at hc₁
    rw [if_neg hs₁] at hc₀
    rw [Finset.card_univ]
    omega
  have hκinj := Finset.card_image_iff.mp hκcard
  exact hκinj (Finset.mem_coe.mpr (Finset.mem_univ _)) (Finset.mem_coe.mpr (Finset.mem_univ _))
    (by rw [hκ, hκ, h])

omit hT in
theorem lift₃V_ne_markR₃ (v : D.SourceVertex) (k : Fin 3) : lift₃V D π v ≠ markR₃ D π k := by
  match k with
  | 0 =>
    intro h
    have h' := Refine.oldSV_injective _ _ (Refine.oldSV_injective _ _
      (h.trans (π.markR₃_zero_eq D hπ)))
    exact Refine.oldSV_ne_freshSV _ _ _ _ _ h'
  | 1 =>
    intro h
    have h' := Refine.oldSV_injective _ _ (h.trans (π.markR₃_one_eq D hD hπ))
    exact Refine.oldSV_ne_freshSV _ _ _ _ _ h'
  | 2 => exact fun h ↦ Refine.oldSV_ne_freshSV _ _ _ _ _ (h.trans (π.markR₃_two_eq D hD hπ))

omit hT hπ in
theorem nonDanglingValency_lift₃V (v : D.SourceVertex) :
    nonDanglingValency (refine₃ D π) (lift₃V D π v) = nonDanglingValency D v := by
  rw [lift₃V, Refine.nonDanglingValency_oldSV _ _ (π.refine₂_connected D hD),
    Refine.nonDanglingValency_oldSV _ _ (π.refine₁_connected D hD),
    Refine.nonDanglingValency_oldSV _ _ hD]

/-- **Glued paths lie in stable paths of `D`.** -/
theorem stablePath_anc_eq (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3)
    (hEnds : HasPathEnds D) {z z' : NonDanglingEdge (refine₃ D π)}
    (h : stage₀ D π hD hT hπ z = stage₀ D π hD hT hπ z') :
    (anc D π hD z).stablePath = (anc D π hD z').stablePath :=
  (separations hD hT hπ hT0 h3 hEnds).2.2.2 _ _ (by rw [cut₀_anc, cut₀_anc, h])

theorem stage₀_eq_of_gluedPath_eq {z z' : NonDanglingEdge (refine₃ D π)}
    (h : gluedPath D π hD hT hπ z = gluedPath D π hD hT hπ z') :
    stage₀ D π hD hT hπ z = stage₀ D π hD hT hπ z' := by
  simp only [stage₀, stage₁, stage₂, h]

open Classical in
/-- **A glued path carrying two indices passes a ramified passage of `D`**: walking along it
(`eqvGen_iff_of_closed`) some two consecutive edges have different indices; they meet at an old
vertex of valency two, which is not fresh at any stage, since the two edges at a fresh vertex
are the halves of one edge (`Refine.exists_oldSV_of_incident_ne`). -/
theorem exists_ramified_of_twoValued {z : NonDanglingEdge (refine₃ D π)}
    (h2 : 2 ≤ (LcmMerge.idxSet (idx D π) (gluedPath D π hD hT hπ)
      (gluedPath D π hD hT hπ z)).card) :
    ∃ (v : D.SourceVertex) (za : NonDanglingEdge (refine₃ D π)) (xb : NonDanglingEdge D),
      gluedPath D π hD hT hπ za = gluedPath D π hD hT hπ z ∧
      Incident _ za.1 (lift₃V D π v) ∧ Incident D (anc D π hD za).1 v ∧ Incident D xb.1 v ∧
      D.sourceEdgeIndex (anc D π hD za).1 ≠ D.sourceEdgeIndex xb.1 ∧
      nonDanglingValency D v = 2 := by
  set g := gluedPath D π hD hT hπ with hg
  obtain ⟨n₁, hn₁, n₂, hn₂, hne⟩ := Finset.one_lt_card.mp h2
  obtain ⟨z₁, hz₁, rfl⟩ := (LcmMerge.mem_idxSet _).mp hn₁
  obtain ⟨z₂, hz₂, rfl⟩ := (LcmMerge.mem_idxSet _).mp hn₂
  obtain ⟨a, b, hab, ha, hidx⟩ : ∃ a b : NonDanglingEdge (glueDatum D π), Consecutive _ a b ∧
      a.stablePath = g z ∧
        (glueDatum D π).sourceEdgeIndex a.1 ≠ (glueDatum D π).sourceEdgeIndex b.1 := by
    by_contra hno
    push Not at hno
    have hclosed : ∀ a b : NonDanglingEdge (glueDatum D π), Consecutive _ a b →
        (a.stablePath = g z → (glueDatum D π).sourceEdgeIndex a.1 = idx D π z₁) →
        (b.stablePath = g z → (glueDatum D π).sourceEdgeIndex b.1 = idx D π z₁) := by
      intro a b hc ha hb
      have hab' : a.stablePath = g z := (stablePath_eq_of_consecutive hc).trans hb
      rw [← hno a b hc hab', ha hab']
    have h12 : Relation.EqvGen (Consecutive _) (liftND D π hD hT hπ z₁)
        (liftND D π hD hT hπ z₂) := (stablePath_eq_iff _ _).mp (hz₁.trans hz₂.symm)
    have h21 := (eqvGen_iff_of_closed hclosed h12).mp (fun _ ↦ sourceEdgeIndex_liftSE z₁.1) hz₂
    exact hne (h21.symm.trans (sourceEdgeIndex_liftSE z₂.1))
  have haOld : IsOld D π a :=
    (isOld_iff_of_stablePath_eq hD hT hπ (ha : a.stablePath = (liftND D π hD hT hπ z).stablePath)).mpr
      (isOld_liftND hD hT hπ z)
  have hbOld := isOld_of_consecutive hD hT hπ hab haOld
  obtain ⟨za, rfl⟩ := eq_liftND_of_isOld hD hT hπ haOld
  obtain ⟨zb, rfl⟩ := eq_liftND_of_isOld hD hT hπ hbOld
  obtain ⟨-, w, haw, hbw, hval⟩ := hab
  change (glueDatum D π).sourceEdgeIndex (liftSE D π za.1) ≠
    (glueDatum D π).sourceEdgeIndex (liftSE D π zb.1) at hidx
  rw [sourceEdgeIndex_liftSE, sourceEdgeIndex_liftSE] at hidx
  rcases sourceVertex_cases_glue D π w with ⟨x, rfl⟩ | ⟨u, rfl⟩ | ⟨k, j, rfl⟩
  · have hza := (incident_liftSE_oldVertex₃ D π za.1 x).mp haw
    have hzb := (incident_liftSE_oldVertex₃ D π zb.1 x).mp hbw
    have hvalx : nonDanglingValency (refine₃ D π) x = 2 := by
      rw [nonDanglingValency_oldVertex₃ D π hD hT hπ] at hval
      by_cases hm : ∃ k, x = markR₃ D π k
      · obtain ⟨k, rfl⟩ := hm
        rw [sum_mark_eq_one, markR₃, π.nonDanglingValency_markR₃ D hD hπ k] at hval
        omega
      · push Not at hm
        rw [sum_mark_eq_zero D π hm, add_zero] at hval
        exact hval
    obtain ⟨x₂, rfl, h2a, h2b⟩ := Refine.exists_oldSV_of_incident_ne _ π.edge₂ hza hzb
      (by simpa only [← Refine.sourceEdgeIndex_eq] using hidx)
    obtain ⟨x₁, rfl, h1a, h1b⟩ := Refine.exists_oldSV_of_incident_ne _ π.edge₁ h2a h2b
      (by simpa only [← Refine.sourceEdgeIndex_eq] using hidx)
    obtain ⟨v, rfl, h0a, h0b⟩ := Refine.exists_oldSV_of_incident_ne D π.edge₀ h1a h1b
      (by simpa only [← Refine.sourceEdgeIndex_eq] using hidx)
    refine ⟨v, za, anc D π hD zb, ha, hza, h0a, h0b, ?_, ?_⟩
    · rw [← idx_eq_anc hD, ← idx_eq_anc hD]
      exact hidx
    · rw [← nonDanglingValency_lift₃V hD]
      exact hvalx
  · exact absurd haw (not_incident_liftSE_newVertex D π za.1 u)
  · exact absurd haw (not_incident_liftSE_tip D π za.1 k j)

open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation) in
open DraismaVargas.Count.RowWalk in
open DraismaVargas.Count.EdgeDenominator (PassesAboveLeaf sourceEdgeIndex_eq_one_of_passesAboveLeaf
  mem_rowEdges) in
open Classical in
/-- **At most one two-valued glued path over each stable path of `D`.** Each passes a ramified
passage of `D` on that path (`exists_ramified_of_twoValued`); on a leaf-avoiding row that is a
transition, and there is at most one (`rowAtMostOneTransition_of_simpleTarget`, with the
target simple, `OutgoingRowCalculus.simpleTarget_of_fullDim`); the two edges
at it lie on one glued path. On a leaf-passing row every index is one. -/
theorem gluedPath_eq_of_twoValued (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3)
    (hEnds : HasPathEnds D) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fd : FullDimensionalSourcePresentation D ι) (hSimple : SimpleTarget T)
    {z z' : NonDanglingEdge (refine₃ D π)}
    (hpath : (anc D π hD z).stablePath = (anc D π hD z').stablePath)
    (h2 : 2 ≤ (LcmMerge.idxSet (idx D π) (gluedPath D π hD hT hπ)
      (gluedPath D π hD hT hπ z)).card)
    (h2' : 2 ≤ (LcmMerge.idxSet (idx D π) (gluedPath D π hD hT hπ)
      (gluedPath D π hD hT hπ z')).card) :
    gluedPath D π hD hT hπ z = gluedPath D π hD hT hπ z' := by
  obtain ⟨v, za, xb, hza, hinc, hxa, hxb, hidx, hval⟩ := exists_ramified_of_twoValued hD hT hπ h2
  obtain ⟨v', za', xb', hza', hinc', hxa', hxb', hidx', hval'⟩ :=
    exists_ramified_of_twoValued hD hT hπ h2'
  set h := (anc D π hD z).stablePath with hh
  have hpa : (anc D π hD za).stablePath = h :=
    stablePath_anc_eq hD hT hπ hT0 h3 hEnds (stage₀_eq_of_gluedPath_eq hD hT hπ hza)
  have hpa' : (anc D π hD za').stablePath = h :=
    (stablePath_anc_eq hD hT hπ hT0 h3 hEnds (stage₀_eq_of_gluedPath_eq hD hT hπ hza')).trans
      hpath.symm
  have hother : ∀ {w : D.SourceVertex} {xa xb' : NonDanglingEdge D}, Incident D xa.1 w →
      Incident D xb'.1 w → nonDanglingValency D w = 2 →
      D.sourceEdgeIndex xa.1 ≠ D.sourceEdgeIndex xb'.1 → xb'.stablePath = xa.stablePath := by
    intro w xa xb' hi hi' hv hne
    exact (stablePath_eq_of_consecutive ⟨fun he ↦ hne (by rw [he]), w, hi, hi', hv⟩).symm
  by_cases hpass : PassesAboveLeaf fd.labelling (fd.labelling.row h)
  · exfalso
    have hone : ∀ x : NonDanglingEdge D, x.stablePath = h → D.sourceEdgeIndex x.1 = 1 :=
      fun x hx ↦ sourceEdgeIndex_eq_one_of_passesAboveLeaf fd hpass
        ((mem_rowEdges _ _ _).mpr ⟨x.2, by rw [← hx]; rfl⟩)
    exact hidx ((hone _ hpa).trans (hone _ ((hother hxa hxb hval hidx).trans hpa)).symm)
  have hAvoid : RowAvoidsLeaves D h := by
    have := (rowAvoidsLeaves_iff_not_passesAboveLeaf fd.labelling (fd.labelling.row h)).mpr hpass
    rwa [Equiv.symm_apply_apply] at this
  have htame := rowRamificationAtMostOne_of_rowAvoidsLeaves fd hAvoid
  have htrans : ∀ {w : D.SourceVertex} {xa xb' : NonDanglingEdge D}, xa.stablePath = h →
      Incident D xa.1 w → Incident D xb'.1 w → nonDanglingValency D w = 2 →
      D.sourceEdgeIndex xa.1 ≠ D.sourceEdgeIndex xb'.1 → IsRowTransition D h w := by
    intro w xa xb' hxh hi hi' hv hne
    have hon : OnRow D h xa.1 := ⟨xa.2, hxh⟩
    refine ⟨hv, ?_, xa.1, hon, hi⟩
    rcases htame w xa.1 hon hi hv with h0 | h1
    · exact absurd (sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue
        fd.danglingEdgeNoGlue hv h0 xa.2 hi xb'.2 hi') hne
    · exact h1
  have hvv := rowAtMostOneTransition_of_simpleTarget fd hSimple hAvoid v v'
    (htrans hpa hxa hxb hval hidx) (htrans hpa' hxa' hxb' hval' hidx')
  subst hvv
  rw [← hza, ← hza']
  by_cases heq : za = za'
  · rw [heq]
  · exact gluedPath_eq_of_incident hD hT hπ heq hinc hinc'
      (by rw [nonDanglingValency_lift₃V hD]; exact hval) (lift₃V_ne_markR₃ hD hπ v)

end CutPaths


/-- **The non-leg rows are the rows of the old glued paths.** -/
theorem nonleg_cover {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) (hleg : Function.Injective legRow)
    (harm : ArmColumns ψ π L legRow) :
    (∀ z, L.row (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) ∉
        Set.range legRow) ∧
      ∀ i ∉ Set.range legRow, ∃ z,
        L.row (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) = i := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hG := glueDatum_connected ψ.data π hD hT
  set g := CutPaths.gluedPath ψ.data π hD hT hπ with hgdef
  have hgcard := CutPaths.card_image_gluedPath hD hT hπ ψ.fullDim.targetGenus ψ.fullDim.trivalent
    ψ.fullDim.pathEnds
  rw [← hgdef] at hgcard
  have hp : Fintype.card (StablePath ψ.data) = p := by
    rw [Fintype.card_congr ψ.fullDim.labelling.row, Fintype.card_fin]
  have hlegRow : ∀ k, legRow k = L.row (NonDanglingEdge.stablePath
      (⟨_, (hairpin_not_isDangling ψ.data π hD hT k).1⟩ : NonDanglingEdge (glueDatum ψ.data π))) := by
    intro k
    have h := matrix_armColumn ψ.data π L hG k (hairpin_not_isDangling ψ.data π hD hT k).1
      (hairpin_not_isDangling ψ.data π hD hT k).2 (legRow k)
    rw [harm, if_pos rfl] at h
    by_contra hne
    rw [if_neg hne] at h
    norm_num at h
  have hnl : ∀ z, L.row (g z) ∉ Set.range legRow := by
    rintro z ⟨k, hk⟩
    rw [hlegRow k] at hk
    exact CutPaths.gluedPath_ne_hairpin hD hT hπ z k (L.row.injective hk).symm
  refine ⟨hnl, ?_⟩
  have hcardNL : Fintype.card {i // i ∉ Set.range legRow} = p + 3 := by
    have h := card_compl_range_add_three legRow hleg
    rw [Fintype.card_fin] at h
    omega
  classical
  intro i hi
  have hsub : Finset.univ.image (fun z ↦ L.row (g z)) ⊆
      Finset.univ.filter fun i ↦ i ∉ Set.range legRow := by
    intro j hj
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl z⟩
  have hc1 : (Finset.univ.image (fun z ↦ L.row (g z))).card = p + 3 := by
    have : Finset.univ.image (fun z ↦ L.row (g z)) = (Finset.univ.image g).image L.row := by
      rw [Finset.image_image]
      rfl
    rw [this, Finset.card_image_of_injective _ L.row.injective, hgcard, hp]
  have hc2 : (Finset.univ.filter fun i ↦ i ∉ Set.range legRow).card = p + 3 := by
    rw [← Fintype.card_subtype]
    convert hcardNL using 2
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc1, hc2])
  have hmem : i ∈ Finset.univ.filter fun i ↦ i ∉ Set.range legRow :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  rw [← heq] at hmem
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hmem
  exact ⟨z, hz⟩

/-- **(S5a) The refinement chain** (§5.3, the order of the rows and columns).
The non-leg rows of the glued matrix are the stable paths of `ψ` cut at the three marks, and its
non-arm columns the target edges of `T₃`: labelling the surviving edges of `ψ`, of `ψ` refined at
mark `0`, at marks `0, 1`, and at all three, by their stable path of `ψ` cut at the marks placed
so far, each stage splits one class at its new mark and changes nothing else (`SplitsAt`), and
the last stage, read through the glued labelling, is the residual block up to reindexing.

**What it states.** Three labellings `cls₁`, `cls₂`, `cls₃`, each `SplitsAt` the previous one at
the mark of its stage (`Placement.markEdge₀/₁/₂`), the first starting from the stable labelling of
`ψ`; and `|det A'|` for the residual block `A'` is `|det|` of the class matrix of `cls₃`
(`clsMatrix`, with the columns of `refineCol`).

**Proof.** Take for `cls₃` the glued stable path through the old edge (`CutPaths.gluedPath`;
an old edge survives exactly when its glued copy does, `isDangling_liftSE_iff`), relabelled; for
`cls₂`, `cls₁` the classes merged back at mark `2`, then at mark `1` (`Merge.merged`). The
`parent` and `others` clauses hold because the glued paths through old edges pass the old
vertices of valency two of `refine₃ ψ.data π` other than the marks (`CutPaths.others₃/₂/₁`). The
`split` clauses, that each mark separates even after merging back at the later marks, are not
shown by walking: merging back at a mark loses one class exactly when it separates
(`Merge.card_image_merged`), there are `p + 3` glued paths through old edges, since they have two
ends each, at the branch vertices of `refine₃ ψ.data π` and the marks
(`CutPaths.card_image_gluedPath`), and merged back at all three marks the classes are unions of
stable paths of `ψ` (`CutPaths.cut₀_eq_of_consecutive`), of which there are `p`
(`CutPaths.exists_cutLabels`). Old edges continue into old edges
(`CutPaths.isOld_of_consecutive`), so the `p + 3` old glued paths are exactly the non-leg rows,
and only old edges contribute to them; the residual block is then the class matrix of `cls₃`
with rows and columns reindexed (`matrix_eq_clsMatrix`, `abs_det_submatrix_equiv`). -/
theorem exists_refinementChain_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) (hleg : Function.Injective legRow)
    (harm : ArmColumns ψ π L legRow)
    (e : {i // i ∉ Set.range legRow} ≃
      {j // j ∉ Set.range fun k ↦ L.targetEdge.symm (π.armEdge k)}) :
    ∃ (cls₁ : NonDanglingEdge (refineDatum ψ.data π.edge₀) → Option (Fin p))
      (cls₂ : NonDanglingEdge (refineDatum (refineDatum ψ.data π.edge₀) π.edge₁) →
        Option (Option (Fin p)))
      (cls₃ : NonDanglingEdge (refine₃ ψ.data π) → Option (Option (Option (Fin p)))),
      SplitsAt ψ.data π.edge₀ ψ.fullDim.valid.1
          (fun x ↦ ψ.fullDim.labelling.row x.stablePath) cls₁ (π.markEdge₀ ψ.data hπ) ∧
        SplitsAt _ π.edge₁ (π.refine₁_connected ψ.data ψ.fullDim.valid.1) cls₁ cls₂
          (π.markEdge₁ ψ.data ψ.fullDim.valid.1 hπ) ∧
        SplitsAt _ π.edge₂ (π.refine₂_connected ψ.data ψ.fullDim.valid.1) cls₂ cls₃
          (π.markEdge₂ ψ.data ψ.fullDim.valid.1 hπ) ∧
        |((GluingDatum.LengthMatrixPresentation.matrix L.presentation).submatrix
            (fun i : {i // i ∉ Set.range legRow} ↦ i.1) (fun i ↦ (e i).1)).det| =
          |(clsMatrix (refine₃ ψ.data π) cls₃ (refineCol π.edge₂ (refineCol π.edge₁
            (refineCol π.edge₀ ψ.fullDim.labelling.targetEdge)))).det| := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  obtain ⟨cls₁, cls₂, lab, s₁, s₂, s₃, hinj, hsurj⟩ := CutPaths.exists_cutLabels hD hT hπ
    ψ.fullDim.targetGenus ψ.fullDim.trivalent ψ.fullDim.pathEnds ψ.fullDim.labelling.row
  refine ⟨cls₁, cls₂, fun z ↦ lab (CutPaths.gluedPath ψ.data π hD hT hπ z), s₁, s₂, s₃, ?_⟩
  set g := CutPaths.gluedPath ψ.data π hD hT hπ with hgdef
  -- every non-leg row is the row of an old glued path, and conversely
  obtain ⟨-, hcover₀⟩ := nonleg_cover ψ π hπ L legRow hleg harm
  have hcover : ∀ i ∉ Set.range legRow, ∃ z, L.row (g z) = i := hcover₀
  have hcardNL : Fintype.card {i // i ∉ Set.range legRow} = p + 3 := by
    have h := card_compl_range_add_three legRow hleg
    rw [Fintype.card_fin] at h
    omega
  have hinj' : ∀ z z', lab (g z) = lab (g z') → g z = g z' := by
    classical
    intro z z' h
    exact hinj (by simp) (by simp) h
  -- the row bijection
  let β : {i // i ∉ Set.range legRow} → Option (Option (Option (Fin p))) := fun i ↦
    lab (L.row.symm i.1)
  have hβ : Function.Bijective β := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i i' h ↦ ?_, by rw [hcardNL]; simp⟩
    obtain ⟨z, hz⟩ := hcover i.1 i.2
    obtain ⟨z', hz'⟩ := hcover i'.1 i'.2
    have h' : lab (g z) = lab (g z') := by
      simp only [β, ← hz, ← hz', Equiv.symm_apply_apply] at h
      exact h
    apply Subtype.ext
    rw [← hz, ← hz', hinj' z z' h']
  have hβrow : ∀ z (i : {i // i ∉ Set.range legRow}), L.row (g z) = i.1 ↔ lab (g z) = β i := by
    intro z i
    constructor
    · intro h
      show lab (g z) = lab (L.row.symm i.1)
      rw [← h, Equiv.symm_apply_apply]
    · intro h
      obtain ⟨z', hz'⟩ := hcover i.1 i.2
      have h' : lab (g z) = lab (g z') := by
        rw [h]
        show lab (L.row.symm i.1) = lab (g z')
        rw [← hz', Equiv.symm_apply_apply]
      rw [hinj' z z' h', hz']
  -- the column bijection
  let δ : (π.T₃).edges → {j // j ∉ Set.range fun k ↦ L.targetEdge.symm (π.armEdge k)} :=
    fun ε ↦ ⟨L.targetEdge.symm (π.liftE₃ ε), by
      rintro ⟨k, hk⟩
      exact π.liftE₃_ne_armEdge ε k (L.targetEdge.symm.injective hk).symm⟩
  have hδ : Function.Bijective δ := by
    refine ⟨fun ε ε' h ↦ π.liftE₃_injective (L.targetEdge.symm.injective
      (congrArg Subtype.val h)), fun j ↦ ?_⟩
    rcases π.T₆_edge_cases (L.targetEdge j.1) with ⟨ε, hε⟩ | ⟨k, hk⟩
    · refine ⟨ε, Subtype.ext ?_⟩
      show L.targetEdge.symm (π.liftE₃ ε) = j.1
      rw [← hε, Equiv.symm_apply_apply]
    · refine absurd ⟨k, ?_⟩ j.2
      show L.targetEdge.symm (π.armEdge k) = j.1
      rw [← hk, Equiv.symm_apply_apply]
  set col₃ := refineCol π.edge₂ (refineCol π.edge₁
    (refineCol π.edge₀ ψ.fullDim.labelling.targetEdge)) with hcol₃
  let γ := (Equiv.ofBijective δ hδ).symm.trans col₃.symm
  have hγ : ∀ j, L.targetEdge j.1 = π.liftE₃ (col₃ (γ j)) := by
    intro j
    show L.targetEdge j.1 = π.liftE₃ (col₃ (col₃.symm ((Equiv.ofBijective δ hδ).symm j)))
    rw [Equiv.apply_symm_apply]
    have hε := Equiv.apply_symm_apply (Equiv.ofBijective δ hδ) j
    set ε := (Equiv.ofBijective δ hδ).symm j
    have h1 : j.1 = L.targetEdge.symm (π.liftE₃ ε) := (congrArg Subtype.val hε).symm
    rw [h1, Equiv.apply_symm_apply]
  -- the residual block is the class matrix, reindexed
  have hblock : (GluingDatum.LengthMatrixPresentation.matrix L.presentation).submatrix
      (fun i : {i // i ∉ Set.range legRow} ↦ i.1) (fun i ↦ (e i).1) =
      (clsMatrix (refine₃ ψ.data π) (fun z ↦ lab (g z)) col₃).submatrix
        (Equiv.ofBijective β hβ) (e.trans γ) := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, matrix_eq_clsMatrix]
    simp only [clsMatrix]
    rw [CutPaths.sum_eq_sum_liftND hD hT hπ]
    · refine Finset.sum_congr rfl fun z _ ↦ ?_
      have hrow : L.row (CutPaths.liftND ψ.data π hD hT hπ z).stablePath = i.1 ↔
          lab (g z) = Equiv.ofBijective β hβ i := hβrow z i
      have hcol : (CutPaths.liftND ψ.data π hD hT hπ z).1.1.1 = L.targetEdge (e j).1 ↔
          z.1.1.1 = col₃ ((e.trans γ) j) := by
        rw [hγ]
        exact π.liftE₃_injective.eq_iff
      by_cases hc : lab (g z) = Equiv.ofBijective β hβ i ∧ z.1.1.1 = col₃ ((e.trans γ) j)
      · rw [if_pos ((and_congr hrow hcol).mpr hc), if_pos hc]
        show (1 : ℚ) / ((glueDatum ψ.data π).sourceEdgeIndex (liftSE ψ.data π z.1) : ℚ) = _
        rw [CutPaths.sourceEdgeIndex_liftSE z.1]
      · rw [if_neg (fun h ↦ hc ((and_congr hrow hcol).mp h)), if_neg hc]
    · intro x hx
      rw [if_neg]
      rintro ⟨hrow, -⟩
      obtain ⟨z, hz⟩ := hcover i.1 i.2
      rw [← hz] at hrow
      exact hx ((CutPaths.isOld_iff_of_stablePath_eq hD hT hπ (L.row.injective hrow)).mpr
        (CutPaths.isOld_liftND hD hT hπ z))
  rw [hblock, abs_det_submatrix_equiv]

/-- **(S5) The residual block** (§5.3). Delete the leg rows and
the arm columns from the glued matrix: the remaining block `A'` is `A_ψ` refined at the three
marks, and `|det A'| · ∏ a_k = |det A_ψ|`. True by induction over the marks, one refinement at a
time against the current refined matrix: split the row `h` through the mark into `h¹, h²` and
the column `t` under it into `t¹, t²`; every other row passes over `t¹` and `t²` alike (pass
once); replace `h²` by `h¹ + h²` (the old row `h`) and then `t¹` by `t¹ - t²`; the column `t¹`
is left with the single entry `1/a` (or `1` on a hairpin, where `a = 1`) in row `h¹`, and the
complementary minor is the previous matrix (`abs_det_refine`). Proof, from the
refinement chain `exists_refinementChain_glueDatum` (S5a): one step of the induction, for
any labelling that splits one class at the mark, is `abs_det_clsMatrix_refine` (from
`abs_det_refine`), the start is the stable labelling of `ψ` (`matrix_eq_clsMatrix`), and the
indices are those of the marks (`Placement.sourceEdgeIndex_markEdge₀/₁/₂`). -/
theorem abs_det_residual_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) (hleg : Function.Injective legRow)
    (harm : ArmColumns ψ π L legRow)
    (e : {i // i ∉ Set.range legRow} ≃
      {j // j ∉ Set.range fun k ↦ L.targetEdge.symm (π.armEdge k)}) :
    |((GluingDatum.LengthMatrixPresentation.matrix L.presentation).submatrix
        (fun i : {i // i ∉ Set.range legRow} ↦ i.1) (fun i ↦ (e i).1)).det| *
      ∏ k, (π.markIndex ψ.data k : ℚ) = |ψ.matrix.det| := by
  have hD := ψ.fullDim.valid.1
  obtain ⟨cls₁, cls₂, cls₃, h₁, h₂, h₃, hres⟩ :=
    exists_refinementChain_glueDatum ψ π hπ L legRow hleg harm e
  have s₁ := abs_det_clsMatrix_refine _ _ hD _ ψ.fullDim.labelling.targetEdge _ _ h₁
  have s₂ := abs_det_clsMatrix_refine _ _ (π.refine₁_connected _ hD) _
    (refineCol π.edge₀ ψ.fullDim.labelling.targetEdge) _ _ h₂
  have s₃ := abs_det_clsMatrix_refine _ _ (π.refine₂_connected _ hD) _
    (refineCol π.edge₁ (refineCol π.edge₀ ψ.fullDim.labelling.targetEdge)) _ _ h₃
  rw [π.sourceEdgeIndex_markEdge₀] at s₁
  rw [π.sourceEdgeIndex_markEdge₁ _ hD] at s₂
  rw [π.sourceEdgeIndex_markEdge₂ _ hD] at s₃
  rw [hres, Fin.prod_univ_three, FibreMember.matrix, matrix_eq_clsMatrix, ← s₁, ← s₂, ← s₃]
  ring

/-- **`|det A_N| · ∏ a_k = 8 |det A_ψ|`, in every labelling** (§5.3): expand
along the arm columns (S4, `abs_det_eq_of_doubled_columns`), then the residual block (S5). -/
theorem abs_det_glueDatum_labelling {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3))) :
    |(GluingDatum.LengthMatrixPresentation.matrix L.presentation).det| *
        ∏ k, (π.markIndex ψ.data k : ℚ) = 8 * |ψ.matrix.det| := by
  classical
  obtain ⟨legRow, hleg, harm⟩ := exists_armColumns_glueDatum ψ π hπ L
  have harmInj : Function.Injective fun k ↦ L.targetEdge.symm (π.armEdge k) :=
    L.targetEdge.symm.injective.comp π.armEdge_injective
  have hcard : Fintype.card {i // i ∉ Set.range legRow} =
      Fintype.card {j // j ∉ Set.range fun k ↦ L.targetEdge.symm (π.armEdge k)} := by
    have h1 := card_compl_range_add_three legRow hleg
    have h2 := card_compl_range_add_three _ harmInj
    omega
  let e := Fintype.equivOfCardEq hcard
  rw [abs_det_eq_of_doubled_columns _ legRow _ hleg harmInj harm e, mul_assoc,
    abs_det_residual_glueDatum ψ π hπ L legRow hleg harm e]

/-- `|det A_N| · ∏ a_k = 8 |det A_ψ|` for a full-dimensional presentation of the glued datum. -/
theorem abs_det_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (fd : FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3))) :
    |(GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).det| *
        ∏ k, (π.markIndex ψ.data k : ℚ) = 8 * |ψ.matrix.det| :=
  abs_det_glueDatum_labelling ψ π hπ fd.labelling

/-- The full-dimensional presentation of the glued datum with a given labelling. -/
def glueFullDim {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3))) :
    FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)) where
  valid := ⟨glueDatum_connected ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected,
    glueDatum_riemannHurwitz ψ.data π ψ.fullDim.valid.2⟩
  targetConnected := π.T₆_connected ψ.fullDim.targetConnected
  targetGenus := π.T₆_genus.trans ψ.fullDim.targetGenus
  saturated := glueDatum_saturated ψ π
  labelling := L
  det_ne_zero := fun hdet ↦ by
    have h := abs_det_glueDatum_labelling ψ π hπ L
    rw [hdet, abs_zero, zero_mul] at h
    exact ψ.det_matrix_ne_zero (abs_eq_zero.mp (by linarith [abs_nonneg ψ.matrix.det]))
  trivalent := nonDanglingValency_glueDatum_le_three ψ π hπ
  pathEnds := hasPathEnds_glueDatum ψ π hπ

/-- **(S6) The denominators of the non-leg rows** (§5.4): their product is
`D_ψ · ∏ a_k`.

**Proof.** On a row of a full-dimensional presentation `d` is the lcm of the indices displayed
on it (`rowDenominator_eq_lcm`, from Part II `lemma-edge-deno` via
`SharpRowDenominator.index_dvd_rowDenominator`), and the glued presentation is full-dimensional
for every labelling (`glueFullDim`). A non-leg row displays exactly the old edges of its glued
path (`nonleg_cover`), so the product is `∏ lcm` over the old glued paths of their index sets.
Merging back at a mark (`CutPaths.stage₂`, `stage₁`, `stage₀`) replaces two lcms by the lcm of
the union, and divides the product by `a_k` (`LcmMerge.prod_lcm_merge`) as soon as one of the two
sides has the single index `a_k` (`LcmMerge.lcm_split`). That is the index profile of §5.4
(constant, or two adjacent values changing once): a side with two indices contains a glued path with
two indices (`LcmMerge.exists_twoValued_of_merge`), such a path passes a ramified passage of `D` on
its stable path (`CutPaths.exists_ramified_of_twoValued`), which is a transition of a leaf-avoiding
row, and a row has at most one (`CutPaths.gluedPath_eq_of_twoValued`). After the three merges
the classes are the stable paths of `ψ` (`CutPaths.separations`), whose lcms are the `d` of `ψ`. -/
theorem prod_rowDenominator_residual_glueDatum {yG : Fin p → ℚ}
    (ψ : FibreMember core yG (2 + 2)) (π : Placement ψ.target (2 + 2))
    (hπ : π.NonDangling ψ.data)
    (L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) (hleg : Function.Injective legRow)
    (harm : ArmColumns ψ π L legRow) :
    ∏ r ∈ Finset.univ.filter (fun r ↦ r ∉ Set.range legRow), rowDenominator L.presentation r =
      denominatorProduct ψ.fullDim.labelling.presentation * ∏ k, π.markIndex ψ.data k := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hT0 := ψ.fullDim.targetGenus
  have h3 := ψ.fullDim.trivalent
  have hEnds := ψ.fullDim.pathEnds
  have h₁ := π.refine₁_connected ψ.data hD
  have h₂ := π.refine₂_connected ψ.data hD
  have hSimple := DraismaVargas.Count.OutgoingRowCalculus.simpleTarget_of_fullDim ψ.fullDim
  set g := CutPaths.gluedPath ψ.data π hD hT hπ with hg
  set ix := CutPaths.idx ψ.data π with hix
  obtain ⟨hnl, hcover⟩ := nonleg_cover ψ π hπ L legRow hleg harm
  obtain ⟨hs₃, hs₂, hs₁, hκ⟩ := CutPaths.separations hD hT hπ hT0 h3 hEnds
  -- (a) on a non-leg row, `d` is the lcm of the indices of its glued path
  have hrow : ∀ i ∈ Finset.univ.filter (fun r ↦ r ∉ Set.range legRow),
      rowDenominator L.presentation i = (LcmMerge.idxSet ix g (L.row.symm i)).lcm id := by
    intro i hi
    have hi' : i ∉ Set.range legRow := (Finset.mem_filter.mp hi).2
    obtain ⟨z₀, hz₀⟩ := hcover i hi'
    rw [show rowDenominator L.presentation i =
      rowDenominator (glueFullDim ψ π hπ L).labelling.presentation i from rfl, rowDenominator_eq_lcm]
    congr 1
    ext m
    simp only [Finset.mem_image, LcmMerge.mem_idxSet]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨hs, hrowe⟩ := (EdgeDenominator.mem_rowEdges _ _ _).mp he
      have hP : NonDanglingEdge.stablePath (⟨e, hs⟩ : NonDanglingEdge (glueDatum ψ.data π)) =
          g z₀ := L.row.injective (hrowe.trans hz₀.symm)
      obtain ⟨z, hz⟩ := CutPaths.eq_liftND_of_isOld hD hT hπ
        ((CutPaths.isOld_iff_of_stablePath_eq hD hT hπ hP).mpr (CutPaths.isOld_liftND hD hT hπ z₀))
      refine ⟨z, ?_, ?_⟩
      · show (CutPaths.liftND ψ.data π hD hT hπ z).stablePath = L.row.symm i
        rw [← hz, hP, ← hz₀, Equiv.symm_apply_apply]
      · have he' : e = liftSE ψ.data π z.1 := congrArg Subtype.val hz
        rw [he', CutPaths.sourceEdgeIndex_liftSE]
        rfl
    · rintro ⟨z, hz, rfl⟩
      refine ⟨liftSE ψ.data π z.1, (EdgeDenominator.mem_rowEdges _ _ _).mpr
        ⟨(CutPaths.liftND ψ.data π hD hT hπ z).2, ?_⟩, CutPaths.sourceEdgeIndex_liftSE z.1⟩
      show L.row (g z) = i
      rw [hz, Equiv.apply_symm_apply]
  -- (b) reindex the non-leg rows by the old glued paths
  have hfilter : Finset.univ.filter (fun r ↦ r ∉ Set.range legRow) =
      (Finset.univ.image g).image L.row := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      obtain ⟨z, hz⟩ := hcover i hi
      exact ⟨g z, ⟨z, rfl⟩, hz⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact hnl z
  rw [Finset.prod_congr rfl hrow, hfilter,
    Finset.prod_image fun a _ b _ h ↦ L.row.injective h]
  simp only [Equiv.symm_apply_apply]
  -- (c) the witnesses at the marks, and their indices
  have hw₂S : CutPaths.stage₂ ψ.data π hD hT hπ (Refine.someHalfND _ π.edge₂ h₂
      (Refine.someHalfND _ π.edge₁ h₁ (π.markEdge₁ ψ.data hD hπ))) =
      CutPaths.cut₂ ψ.data π hD hT hπ (Refine.someHalfND _ π.edge₁ h₁ (π.markEdge₁ ψ.data hD hπ)) := by
    rw [← CutPaths.cut₂_parent hD hT hπ, Refine.parentND_someHalfND]
  have hw₂N : CutPaths.stage₂ ψ.data π hD hT hπ (Refine.someHalfND _ π.edge₂ h₂
      (Refine.noneHalfND _ π.edge₁ h₁ (π.markEdge₁ ψ.data hD hπ))) =
      CutPaths.cut₂ ψ.data π hD hT hπ (Refine.noneHalfND _ π.edge₁ h₁ (π.markEdge₁ ψ.data hD hπ)) := by
    rw [← CutPaths.cut₂_parent hD hT hπ, Refine.parentND_someHalfND]
  have hw₁S : CutPaths.stage₁ ψ.data π hD hT hπ (Refine.someHalfND _ π.edge₂ h₂
      (Refine.someHalfND _ π.edge₁ h₁ (Refine.someHalfND _ π.edge₀ hD (π.markEdge₀ ψ.data hπ)))) =
      CutPaths.cut₁ ψ.data π hD hT hπ (Refine.someHalfND _ π.edge₀ hD (π.markEdge₀ ψ.data hπ)) := by
    rw [← CutPaths.cut₁_parent hD hT hπ, Refine.parentND_someHalfND, Refine.parentND_someHalfND]
  have hw₁N : CutPaths.stage₁ ψ.data π hD hT hπ (Refine.someHalfND _ π.edge₂ h₂
      (Refine.someHalfND _ π.edge₁ h₁ (Refine.noneHalfND _ π.edge₀ hD (π.markEdge₀ ψ.data hπ)))) =
      CutPaths.cut₁ ψ.data π hD hT hπ (Refine.noneHalfND _ π.edge₀ hD (π.markEdge₀ ψ.data hπ)) := by
    rw [← CutPaths.cut₁_parent hD hT hπ, Refine.parentND_someHalfND, Refine.parentND_someHalfND]
  have ha₃S : π.markIndex ψ.data 2 ∈ LcmMerge.idxSet ix g
      (g (Refine.someHalfND _ π.edge₂ h₂ (π.markEdge₂ ψ.data hD hπ))) :=
    (LcmMerge.mem_idxSet ix).mpr ⟨_, rfl, by
      rw [hix, CutPaths.idx, Refine.sourceEdgeIndex_someHalfND,
        π.sourceEdgeIndex_markEdge₂ _ hD]⟩
  have ha₃N : π.markIndex ψ.data 2 ∈ LcmMerge.idxSet ix g
      (g (Refine.noneHalfND _ π.edge₂ h₂ (π.markEdge₂ ψ.data hD hπ))) :=
    (LcmMerge.mem_idxSet ix).mpr ⟨_, rfl, by
      rw [hix, CutPaths.idx, Refine.sourceEdgeIndex_noneHalfND _ π.edge₂ h₂
        (show (π.markEdge₂ ψ.data hD hπ).1.1.1 = π.edge₂ from rfl),
        π.sourceEdgeIndex_markEdge₂ _ hD]⟩
  have ha₂S : π.markIndex ψ.data 1 ∈ LcmMerge.idxSet ix (CutPaths.stage₂ ψ.data π hD hT hπ)
      (CutPaths.cut₂ ψ.data π hD hT hπ
        (Refine.someHalfND _ π.edge₁ h₁ (π.markEdge₁ ψ.data hD hπ))) :=
    (LcmMerge.mem_idxSet ix).mpr ⟨_, hw₂S, by
      rw [hix, CutPaths.idx, Refine.sourceEdgeIndex_someHalfND, Refine.sourceEdgeIndex_someHalfND,
        π.sourceEdgeIndex_markEdge₁ _ hD]⟩
  have ha₂N : π.markIndex ψ.data 1 ∈ LcmMerge.idxSet ix (CutPaths.stage₂ ψ.data π hD hT hπ)
      (CutPaths.cut₂ ψ.data π hD hT hπ
        (Refine.noneHalfND _ π.edge₁ h₁ (π.markEdge₁ ψ.data hD hπ))) :=
    (LcmMerge.mem_idxSet ix).mpr ⟨_, hw₂N, by
      rw [hix, CutPaths.idx, Refine.sourceEdgeIndex_someHalfND,
        Refine.sourceEdgeIndex_noneHalfND _ π.edge₁ h₁
        (show (π.markEdge₁ ψ.data hD hπ).1.1.1 = π.edge₁ from rfl), π.sourceEdgeIndex_markEdge₁ _ hD]⟩
  have ha₁S : π.markIndex ψ.data 0 ∈ LcmMerge.idxSet ix (CutPaths.stage₁ ψ.data π hD hT hπ)
      (CutPaths.cut₁ ψ.data π hD hT hπ (Refine.someHalfND _ π.edge₀ hD (π.markEdge₀ ψ.data hπ))) :=
    (LcmMerge.mem_idxSet ix).mpr ⟨_, hw₁S, by
      rw [hix, CutPaths.idx, Refine.sourceEdgeIndex_someHalfND, Refine.sourceEdgeIndex_someHalfND,
        Refine.sourceEdgeIndex_someHalfND, π.sourceEdgeIndex_markEdge₀]⟩
  have ha₁N : π.markIndex ψ.data 0 ∈ LcmMerge.idxSet ix (CutPaths.stage₁ ψ.data π hD hT hπ)
      (CutPaths.cut₁ ψ.data π hD hT hπ (Refine.noneHalfND _ π.edge₀ hD (π.markEdge₀ ψ.data hπ))) :=
    (LcmMerge.mem_idxSet ix).mpr ⟨_, hw₁N, by
      rw [hix, CutPaths.idx, Refine.sourceEdgeIndex_someHalfND, Refine.sourceEdgeIndex_someHalfND,
        Refine.sourceEdgeIndex_noneHalfND _ π.edge₀ hD
        (show (π.markEdge₀ ψ.data hπ).1.1.1 = π.edge₀ from rfl), π.sourceEdgeIndex_markEdge₀]⟩
  -- (d) at each mark, not both sides carry two indices
  have huniq : ∀ z z', (CutPaths.anc ψ.data π hD z).stablePath =
      (CutPaths.anc ψ.data π hD z').stablePath → 2 ≤ (LcmMerge.idxSet ix g (g z)).card →
      2 ≤ (LcmMerge.idxSet ix g (g z')).card → g z = g z' := fun z z' ↦
    CutPaths.gluedPath_eq_of_twoValued hD hT hπ hT0 h3 hEnds ψ.fullDim hSimple
  have hpath_of : ∀ z z', CutPaths.stage₀ ψ.data π hD hT hπ z = CutPaths.stage₀ ψ.data π hD hT hπ z' →
      (CutPaths.anc ψ.data π hD z).stablePath = (CutPaths.anc ψ.data π hD z').stablePath :=
    fun z z' h ↦ CutPaths.stablePath_anc_eq hD hT hπ hT0 h3 hEnds h
  have hC₃ := LcmMerge.lcm_split ha₃S ha₃N (by
    rintro ⟨hA, hB⟩
    refine hs₃ (huniq _ _ ?_ hA hB)
    simp only [CutPaths.anc, Refine.parentND_someHalfND, Refine.parentND_noneHalfND _ π.edge₂ h₂
      (show (π.markEdge₂ ψ.data hD hπ).1.1.1 = π.edge₂ from rfl)])
  have hC₂ := LcmMerge.lcm_split ha₂S ha₂N (by
    rintro ⟨hA, hB⟩
    obtain ⟨x, hx, hx2⟩ := LcmMerge.exists_twoValued_of_merge ix g
      (CutPaths.stage₂ ψ.data π hD hT hπ) (fun _ ↦ rfl) ha₃S ha₃N hA
    obtain ⟨y, hy, hy2⟩ := LcmMerge.exists_twoValued_of_merge ix g
      (CutPaths.stage₂ ψ.data π hD hT hπ) (fun _ ↦ rfl) ha₃S ha₃N hB
    have h1 : CutPaths.stage₁ ψ.data π hD hT hπ x = CutPaths.stage₁ ψ.data π hD hT hπ y := by
      unfold CutPaths.stage₁
      rw [hx, hy, Merge.mergeFn_self]
      unfold Merge.mergeFn
      simp
    have h0 : CutPaths.stage₀ ψ.data π hD hT hπ x = CutPaths.stage₀ ψ.data π hD hT hπ y := by
      unfold CutPaths.stage₀
      rw [h1]
    have hgxy := huniq x y (hpath_of x y h0) hx2 hy2
    apply hs₂
    rw [← hx, ← hy]
    unfold CutPaths.stage₂
    rw [show CutPaths.gluedPath ψ.data π hD hT hπ x = CutPaths.gluedPath ψ.data π hD hT hπ y
      from hgxy])
  have hC₁ := LcmMerge.lcm_split ha₁S ha₁N (by
    rintro ⟨hA, hB⟩
    obtain ⟨x, hx, hx2⟩ := LcmMerge.exists_twoValued_of_merge ix
      (CutPaths.stage₂ ψ.data π hD hT hπ) (CutPaths.stage₁ ψ.data π hD hT hπ) (fun _ ↦ rfl)
      ha₂S ha₂N hA
    obtain ⟨x', hx', hx'2⟩ := LcmMerge.exists_twoValued_of_merge ix g
      (CutPaths.stage₂ ψ.data π hD hT hπ) (fun _ ↦ rfl) ha₃S ha₃N hx2
    obtain ⟨y, hy, hy2⟩ := LcmMerge.exists_twoValued_of_merge ix
      (CutPaths.stage₂ ψ.data π hD hT hπ) (CutPaths.stage₁ ψ.data π hD hT hπ) (fun _ ↦ rfl)
      ha₂S ha₂N hB
    obtain ⟨y', hy', hy'2⟩ := LcmMerge.exists_twoValued_of_merge ix g
      (CutPaths.stage₂ ψ.data π hD hT hπ) (fun _ ↦ rfl) ha₃S ha₃N hy2
    have hx1 : CutPaths.stage₁ ψ.data π hD hT hπ x' =
        CutPaths.cut₁ ψ.data π hD hT hπ (Refine.someHalfND _ π.edge₀ hD (π.markEdge₀ ψ.data hπ)) := by
      unfold CutPaths.stage₁
      rw [hx']
      exact hx
    have hy1 : CutPaths.stage₁ ψ.data π hD hT hπ y' =
        CutPaths.cut₁ ψ.data π hD hT hπ (Refine.noneHalfND _ π.edge₀ hD (π.markEdge₀ ψ.data hπ)) := by
      unfold CutPaths.stage₁
      rw [hy']
      exact hy
    have h0 : CutPaths.stage₀ ψ.data π hD hT hπ x' = CutPaths.stage₀ ψ.data π hD hT hπ y' := by
      unfold CutPaths.stage₀
      rw [hx1, hy1, Merge.mergeFn_self]
      unfold Merge.mergeFn
      simp
    have hgxy := huniq x' y' (hpath_of x' y' h0) hx'2 hy'2
    apply hs₁
    rw [← hx1, ← hy1]
    unfold CutPaths.stage₁ CutPaths.stage₂
    rw [show CutPaths.gluedPath ψ.data π hD hT hπ x' = CutPaths.gluedPath ψ.data π hD hT hπ y'
      from hgxy])
  -- (e) stage `0` is the stable labelling of `ψ`
  have hstage0 : ∏ Q ∈ Finset.univ.image (CutPaths.stage₀ ψ.data π hD hT hπ),
      (LcmMerge.idxSet ix (CutPaths.stage₀ ψ.data π hD hT hπ) Q).lcm id =
        denominatorProduct ψ.fullDim.labelling.presentation := by
    obtain ⟨κ, hκdef⟩ : ∃ κ : StablePath ψ.data → StablePath (glueDatum ψ.data π),
        ∀ x : NonDanglingEdge ψ.data, κ x.stablePath = CutPaths.cut₀ ψ.data π hD hT hπ x :=
      ⟨Quot.lift _ fun _ _ h ↦ CutPaths.cut₀_eq_of_consecutive hD hT hπ h, fun _ ↦ rfl⟩
    have hκinj : Function.Injective κ := by
      intro a b hab
      obtain ⟨x, rfl⟩ := Quot.exists_rep a
      obtain ⟨y, rfl⟩ := Quot.exists_rep b
      exact hκ x y ((hκdef x).symm.trans (hab.trans (hκdef y)))
    let desc : NonDanglingEdge ψ.data → NonDanglingEdge (refine₃ ψ.data π) := fun x ↦
      Refine.someHalfND _ π.edge₂ h₂ (Refine.someHalfND _ π.edge₁ h₁ (Refine.someHalfND _ π.edge₀ hD x))
    have hdesc : ∀ x, CutPaths.anc ψ.data π hD (desc x) = x := fun x ↦ by
      simp only [desc, CutPaths.anc, Refine.parentND_someHalfND]
    have hst : ∀ z, CutPaths.stage₀ ψ.data π hD hT hπ z = κ (CutPaths.anc ψ.data π hD z).stablePath :=
      fun z ↦ by rw [hκdef, CutPaths.cut₀_anc]
    have himg : Finset.univ.image (CutPaths.stage₀ ψ.data π hD hT hπ) = Finset.univ.image κ := by
      ext Q
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨_, (hst z).symm⟩
      · rintro ⟨h, rfl⟩
        obtain ⟨x, rfl⟩ := Quot.exists_rep h
        exact ⟨desc x, by rw [hst, hdesc]; rfl⟩
    rw [himg, Finset.prod_image fun a _ b _ h ↦ hκinj h]
    unfold denominatorProduct
    rw [← Equiv.prod_comp ψ.fullDim.labelling.row]
    refine Finset.prod_congr rfl fun h _ ↦ ?_
    rw [rowDenominator_eq_lcm]
    congr 1
    ext m
    simp only [LcmMerge.mem_idxSet, Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hst] at hz
      refine ⟨(CutPaths.anc ψ.data π hD z).1, (EdgeDenominator.mem_rowEdges _ _ _).mpr
        ⟨(CutPaths.anc ψ.data π hD z).2, congrArg _ (hκinj hz)⟩, ?_⟩
      rw [hix, CutPaths.idx_eq_anc hD]
    · rintro ⟨e, he, rfl⟩
      obtain ⟨hs, hrowe⟩ := (EdgeDenominator.mem_rowEdges _ _ _).mp he
      set x : NonDanglingEdge ψ.data := ⟨e, hs⟩ with hxdef
      refine ⟨desc x, ?_, ?_⟩
      · rw [hst, hdesc x]
        exact congrArg κ (ψ.fullDim.labelling.row.injective hrowe)
      · rw [hix, CutPaths.idx_eq_anc hD, hdesc x]
  -- (f) the chain of three merges
  rw [LcmMerge.prod_lcm_merge ix g (CutPaths.stage₂ ψ.data π hD hT hπ) (fun _ ↦ rfl) rfl rfl hs₃ hC₃,
    LcmMerge.prod_lcm_merge ix (CutPaths.stage₂ ψ.data π hD hT hπ)
      (CutPaths.stage₁ ψ.data π hD hT hπ) (fun _ ↦ rfl) hw₂S hw₂N hs₂ hC₂,
    LcmMerge.prod_lcm_merge ix (CutPaths.stage₁ ψ.data π hD hT hπ)
      (CutPaths.stage₀ ψ.data π hD hT hπ) (fun _ ↦ rfl) hw₁S hw₁N hs₁ hC₁,
    hstage0, Fin.prod_univ_three]
  ring

/-- A non-zero entry of a stable length matrix comes from a displayed source edge over its
column. -/
theorem exists_mem_rowEdges_of_matrix_ne_zero {S : CFGraph} {k : ℕ} {E : GluingDatum S k}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (L : StableLengthMatrixLabelling E ι) (r c : ι)
    (h : GluingDatum.LengthMatrixPresentation.matrix L.presentation r c ≠ 0) :
    ∃ edge ∈ EdgeDenominator.rowEdges L r, edge.1.1 = L.targetEdge c := by
  by_contra hno
  push Not at hno
  apply h
  unfold GluingDatum.LengthMatrixPresentation.matrix GluingDatum.LengthMatrixPresentation.row
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hx
  apply GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
  intro ht
  refine hno edge ?_ ht.symm
  rw [EdgeDenominator.rowEdges_eq_toFinset_path]
  exact List.mem_toFinset.mpr hedge

/-- **A leg row has denominator one** (Part II `lemma-edge-deno` (a)): it passes over its arm,
which ends at a leaf of the target. -/
theorem rowDenominator_legRow {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2))
    (fd : FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) (harm : ArmColumns ψ π fd.labelling legRow)
    (k : Fin 3) : rowDenominator fd.labelling.presentation (legRow k) = 1 := by
  refine EdgeDenominator.rowDenominator_eq_one_of_passesAboveLeaf fd ?_
  have hne : GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation (legRow k)
      (fd.labelling.targetEdge.symm (π.armEdge k)) ≠ 0 := by
    rw [harm, if_pos rfl]
    norm_num
  obtain ⟨edge, hmem, hedge⟩ := exists_mem_rowEdges_of_matrix_ne_zero _ _ _ hne
  refine ⟨edge, hmem, π.tipTarget k, (isLeafVertex_iff _ _).mpr (π.vertex_degree_tipTarget k), ?_⟩
  rw [hedge, Equiv.apply_symm_apply]
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr (congrArg Prod.snd (π.armEdge_ends k))

/-- **`D_N = D_ψ · ∏ a_k`** (§5.4): the leg rows have denominator one, and the other
rows are S6. -/
theorem denominatorProduct_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (fd : FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3))) :
    denominatorProduct fd.labelling.presentation =
      denominatorProduct ψ.fullDim.labelling.presentation * ∏ k, π.markIndex ψ.data k := by
  classical
  obtain ⟨legRow, hleg, harm⟩ := exists_armColumns_glueDatum ψ π hπ fd.labelling
  rw [denominatorProduct, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun r ↦ r ∈ Set.range legRow),
    prod_rowDenominator_residual_glueDatum ψ π hπ fd.labelling legRow hleg harm]
  have hone : ∏ r ∈ Finset.univ.filter (fun r ↦ r ∈ Set.range legRow),
      rowDenominator fd.labelling.presentation r = 1 := by
    refine Finset.prod_eq_one fun r hr ↦ ?_
    obtain ⟨k, rfl⟩ := (Finset.mem_filter.mp hr).2
    exact rowDenominator_legRow ψ π fd legRow harm k
  rw [hone, one_mul]

/-- **The stable presentation of the glued datum** (Theorem 5.1): an honest stable labelling by
the slot type of `Γ̃`, nonsingular, trivalent, with path ends. The labelling exists by the
counts (S1 and `T₆_edge_card`); it is nonsingular because `|det A_N| · ∏ a_k = 8 |det A_ψ| ≠ 0`
(`abs_det_glueDatum_labelling`). -/
theorem exists_stableLabelling_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data) :
    ∃ labelling : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)),
      (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0 ∧
        (∀ v, nonDanglingValency (glueDatum ψ.data π) v ≤ 3) ∧
          HasPathEnds (glueDatum ψ.data π) := by
  have hT : Fintype.card ψ.target.edges = p := by
    rw [Fintype.card_congr ψ.fullDim.labelling.targetEdge.symm, Fintype.card_fin]
  have hT₆ : Fintype.card π.T₆.edges = p + 1 + 1 + 1 + 3 := by
    rw [Multiset.card_coe, π.T₆_edge_card, ← Multiset.card_coe, hT]
  let L : StableLengthMatrixLabelling (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)) :=
    ⟨(Fintype.equivFinOfCardEq hT₆).symm,
      Fintype.equivFinOfCardEq (card_stablePath_glueDatum ψ π hπ)⟩
  refine ⟨L, fun hdet ↦ ?_, nonDanglingValency_glueDatum_le_three ψ π hπ,
    hasPathEnds_glueDatum ψ π hπ⟩
  have h := abs_det_glueDatum_labelling ψ π hπ L
  rw [hdet, abs_zero, zero_mul] at h
  exact ψ.det_matrix_ne_zero (abs_eq_zero.mp (by linarith [abs_nonneg ψ.matrix.det]))

/-- **The glued datum is full-dimensional** at every placement on the core (Theorem 5.1). -/
theorem nonempty_fullDim_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data) :
    Nonempty
      (FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3))) := by
  obtain ⟨labelling, hdet, htri, hends⟩ := exists_stableLabelling_glueDatum ψ π hπ
  exact ⟨{ valid := ⟨glueDatum_connected ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected,
               glueDatum_riemannHurwitz ψ.data π ψ.fullDim.valid.2⟩
           targetConnected := π.T₆_connected ψ.fullDim.targetConnected
           targetGenus := π.T₆_genus.trans ψ.fullDim.targetGenus
           saturated := glueDatum_saturated ψ π
           labelling := labelling
           det_ne_zero := hdet
           trivalent := htri
           pathEnds := hends }⟩

end Bijection

end GenusSixExistence.Tripod.Gluing
