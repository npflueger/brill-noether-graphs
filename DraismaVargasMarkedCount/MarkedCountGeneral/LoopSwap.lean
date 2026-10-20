module

public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame

@[expose] public section

/-!
# The drop lemma, loop case, part 2: the sheet swap over one target edge

When the dropped mark lies on a loop of the core, an isomorphism of the drops may reverse the
walk of the loop row; it is then composed with an automorphism reversing that row. Part I's
`lemma-loop-bridge` makes the row of a loop the hairpin `⟨A, e, C, e', A⟩` over one leaf edge `t`.
Its two occurrences `e = (t, i)` and `e' = (t, i')` are singleton blocks of `P_t`, and the sheets
`i, i'` lie in one block at both ends of `t` (`A` and `C`). Then the transposition `(i i')` over
`t`, the identity elsewhere, is a gluing-datum automorphism over the identity of the target
(`swapIso`): it fixes every source vertex, exchanges `e` and `e'`, and fixes every other source
edge. When `e` and `e'` carry one row label, it is a typed-frame automorphism (`exists_swap`).

The hairpin itself is proved in module `LoopHairpin`; here everything is generic.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

namespace LoopSwap

/-! ## 1.  Swapping two singleton blocks -/

/-- **Swapping two singleton blocks fixes a partition.** -/
theorem relabel_swap_eq {d : ℕ} (P : SheetPartition d) {i i' : Fin d}
    (hi : ∀ j, P.Rel i j → j = i) (hi' : ∀ j, P.Rel i' j → j = i') :
    P.relabel (Equiv.swap i i') = P := by
  have hri : P.repr i = i := hi _ (P.repr_idem i).symm
  have hri' : P.repr i' = i' := hi' _ (P.repr_idem i').symm
  ext1
  funext j
  change Equiv.swap i i' (P.repr ((Equiv.swap i i').symm j)) = P.repr j
  rw [Equiv.symm_swap]
  by_cases hj : j = i
  · subst hj
    rw [Equiv.swap_apply_left, hri', Equiv.swap_apply_right, hri]
  · by_cases hj' : j = i'
    · subst hj'
      rw [Equiv.swap_apply_right, hri, Equiv.swap_apply_left, hri']
    · rw [Equiv.swap_apply_of_ne_of_ne hj hj']
      have h1 : P.repr j ≠ i := fun h ↦ hj (hi j (hri.trans h.symm))
      have h2 : P.repr j ≠ i' := fun h ↦ hj' (hi' j (hri'.trans h.symm))
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-! ## 2.  The swap automorphism of a gluing datum -/

section Datum

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree) (t : target.edges)
  {i i' : Fin degree} (hi : ∀ j, (data.edgePartition t).Rel i j → j = i)
  (hi' : ∀ j, (data.edgePartition t).Rel i' j → j = i')
  (hEnds : ∀ v, ((t : target.V × target.V).1 = v ∨ (t : target.V × target.V).2 = v) →
    (data.vertexPartition v).Rel i i')

open Classical in
/-- The sheet permutation over a target edge: `(i i')` over `t`, the identity elsewhere. -/
noncomputable def swapPerm (i i' : Fin degree) (ε : target.edges) : Equiv.Perm (Fin degree) :=
  if ε = t then Equiv.swap i i' else Equiv.refl _

theorem swapPerm_self : swapPerm t i i' t = Equiv.swap i i' := by
  classical
  unfold swapPerm
  exact ite_eq_left rfl

theorem swapPerm_of_ne {ε : target.edges} (h : ε ≠ t) : swapPerm t i i' ε = Equiv.refl _ := by
  classical
  unfold swapPerm
  exact ite_eq_right h

include hi hi' hEnds in
/-- **The sheet swap over `t`**, an automorphism of the gluing datum over the identity of the
target. -/
noncomputable def swapIso : GeometricDatumIso data data where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends _ := Or.inl rfl
  vertexPerm _ := Equiv.refl _
  edgePerm := swapPerm t i i'
  vertexPartition _ := (Transport.DatumIso.relabel_refl _).symm
  edgePartition ε := by
    by_cases h : ε = t
    · subst h
      rw [swapPerm_self]
      exact (relabel_swap_eq _ hi hi').symm
    · rw [swapPerm_of_ne t h]
      exact (Transport.DatumIso.relabel_refl _).symm
  compatible ε v hv sheet := by
    change (data.vertexPartition v).Rel (swapPerm t i i' ε sheet) sheet
    by_cases h : ε = t
    · subst h
      rw [swapPerm_self]
      have hRel := hEnds v hv
      by_cases hs : sheet = i
      · subst hs
        rw [Equiv.swap_apply_left]
        exact hRel.symm
      · by_cases hs' : sheet = i'
        · subst hs'
          rw [Equiv.swap_apply_right]
          exact hRel
        · rw [Equiv.swap_apply_of_ne_of_ne hs hs']
          exact rfl
    · rw [swapPerm_of_ne t h]
      rfl

/-- The swap fixes every source vertex. -/
theorem swapIso_vertex (X : data.SourceVertex) :
    (swapIso data t hi hi' hEnds).sourceVertexEquiv X = X := rfl

/-- The swap fixes every source edge off `t`. -/
theorem swapIso_edge_of_ne (E : data.SourceEdge) (h : E.1.1 ≠ t) :
    (swapIso data t hi hi' hEnds).sourceEdgeEquiv E = E := by
  apply Subtype.ext
  change (E.1.1, swapPerm t i i' E.1.1 E.1.2) = E.1
  rw [swapPerm_of_ne t h]
  rfl

/-- Over `t`, the swap acts on the sheet. -/
theorem swapIso_edge_of_eq (E : data.SourceEdge) (h : E.1.1 = t) :
    ((swapIso data t hi hi' hEnds).sourceEdgeEquiv E).1 = (E.1.1, Equiv.swap i i' E.1.2) := by
  change (E.1.1, swapPerm t i i' E.1.1 E.1.2) = _
  rw [h, swapPerm_self]

end Datum

/-! ## 3.  Typed frames -/

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

/-- **An automorphism of the datum of a typed frame fixing every source vertex and every row label
is an automorphism of the typed frame.** -/
def typedFrameIsoOfFix (τ : TypedFrame core mark types degree)
    (α : GeometricDatumIso τ.data τ.data) (hV : ∀ X, α.sourceVertexEquiv X = X)
    (hR : ∀ E : NonDanglingEdge τ.data,
      τ.ident.row (markedRow (markSet τ.markSource) (α.nonDanglingEdgeEquiv τ.fullDim.valid.1 E)) =
        τ.ident.row (markedRow (markSet τ.markSource) E)) :
    TypedFrameIso τ τ where
  datum := α
  mark _ := hV _
  overCore_vertex vertex _ := congrArg τ.ident.vertex (Subtype.ext (hV vertex.1))
  overCore_row := hR

/-- **The swap of the two occurrences of a hairpin is an automorphism of the typed frame.** If two
surviving occurrences `e = (t, i)`, `e' = (t, i')` over one target edge are singleton blocks of
`P_t`, their sheets lie in one block at both ends of `t`, and their marked rows have one label,
some automorphism of the typed frame carries `e` to `e'`. -/
theorem exists_swap (τ : TypedFrame core mark types degree) {e e' : NonDanglingEdge τ.data}
    (ht : e'.1.1.1 = e.1.1.1)
    (hi : ∀ j, (τ.data.edgePartition e.1.1.1).Rel e.1.1.2 j → j = e.1.1.2)
    (hi' : ∀ j, (τ.data.edgePartition e.1.1.1).Rel e'.1.1.2 j → j = e'.1.1.2)
    (hEnds : ∀ v, ((e.1.1.1 : τ.target.V × τ.target.V).1 = v ∨
        (e.1.1.1 : τ.target.V × τ.target.V).2 = v) →
      (τ.data.vertexPartition v).Rel e.1.1.2 e'.1.1.2)
    (hRow : τ.ident.row (markedRow (markSet τ.markSource) e) =
      τ.ident.row (markedRow (markSet τ.markSource) e')) :
    ∃ α : TypedFrameIso τ τ, α.datum.sourceEdgeEquiv e.1 = e'.1 := by
  set α := swapIso τ.data e.1.1.1 hi hi' hEnds with hα
  have he : α.sourceEdgeEquiv e.1 = e'.1 := by
    apply Subtype.ext
    rw [swapIso_edge_of_eq _ _ _ _ _ _ rfl, Equiv.swap_apply_left]
    exact Prod.ext ht.symm rfl
  have he' : α.sourceEdgeEquiv e'.1 = e.1 := by
    apply Subtype.ext
    rw [swapIso_edge_of_eq _ _ _ _ _ _ ht, Equiv.swap_apply_right]
    exact Prod.ext ht rfl
  refine ⟨typedFrameIsoOfFix τ α (swapIso_vertex _ _ _ _ _) fun E ↦ ?_, he⟩
  have hRowOf : ∀ F G : NonDanglingEdge τ.data, F.1 = G.1 →
      markedRow (markSet τ.markSource) F = markedRow (markSet τ.markSource) G := by
    intro F G h
    rw [Subtype.ext h]
  by_cases hE : E.1.1.1 = e.1.1.1
  · by_cases hj : E.1.1.2 = e.1.1.2
    · have hEe : E.1 = e.1 := Subtype.ext (Prod.ext hE hj)
      rw [hRowOf _ e' (by rw [GeometricDatumIso.nonDanglingEdgeEquiv_val, hEe, he]),
        hRowOf E e hEe]
      exact hRow.symm
    · by_cases hj' : E.1.1.2 = e'.1.1.2
      · have hEe : E.1 = e'.1 := Subtype.ext (Prod.ext (hE.trans ht.symm) hj')
        rw [hRowOf _ e (by rw [GeometricDatumIso.nonDanglingEdgeEquiv_val, hEe, he']),
          hRowOf E e' hEe]
        exact hRow
      · rw [hRowOf _ E ?_]
        rw [GeometricDatumIso.nonDanglingEdgeEquiv_val]
        apply Subtype.ext
        rw [swapIso_edge_of_eq _ _ _ _ _ _ hE, Equiv.swap_apply_of_ne_of_ne hj hj']
  · rw [hRowOf _ E ?_]
    rw [GeometricDatumIso.nonDanglingEdgeEquiv_val]
    exact swapIso_edge_of_ne _ _ _ _ _ _ hE

end LoopSwap

end DraismaVargas.Count.MarkedCountGeneral
