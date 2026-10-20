module

public import DraismaVargasMarkedCount.MarkedCount.RegrowStable
public import DraismaVargasCount.GeometricStableTransport

@[expose] public section

/-!
# Regrowth, part 6: isomorphisms extend over the branches

An isomorphism of data `ι : GeometricDatumIso D D'` carrying the marks of `β` to those
of `β'` (`hx`, `ha`) extends to `regrowIso ι : GeometricDatumIso (regrowDatum β)
(regrowDatum β')`: the identity on the new target vertices and edges, and over the branch of
mark `j` the sheet permutation `π j = swap (σ b) b' ∘ σ` (`σ` the permutation at `x j`). It
carries `{a, b}` to `{a', b'}` (`branchPerm_a`, `branchPerm_other`) and permutes sheets only
inside the block of the mark (`rel_branchPerm`), so the second sheets `b, b'` may be chosen
arbitrarily: this is the independence of `P`.

The induced dictionaries are computed on the old part and on the lollipops
(`sourceVertexEquiv_oldSV`, `_wSV`, `sourceEdgeEquiv_oldSE`, `_ebSE`, `_e₁SE`).
-/

namespace DraismaVargas.Count.MarkedCount.Regrow

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)
open GenusSixExistence.Tripod.Gluing (SheetOps.pair)

variable {T T' : CFGraph.{0}} {d k : ℕ} {D : GluingDatum T d} {D' : GluingDatum T' d}
  (β : Branching D k) (β' : Branching D' k) (ι : GeometricDatumIso D D')
  (hx : ∀ j, ι.targetVertex (β.x j) = β'.x j)
  (ha : ∀ j, ι.vertexPerm (β.x j) (β.a j) = β'.a j)

theorem pair_relabel (a b : Fin d) (π : Equiv.Perm (Fin d)) :
    (SheetOps.pair a b).relabel π = SheetOps.pair (π a) (π b) := by
  apply SheetPartition.ext_repr
  funext i
  change π ((SheetOps.pair a b).repr (π.symm i)) = (SheetOps.pair (π a) (π b)).repr i
  rw [pair_repr, pair_repr]
  by_cases h : i = π b
  · subst h; simp
  · have h' : π.symm i ≠ b := fun h' ↦ h (by rw [← h', Equiv.apply_symm_apply])
    simp [h, h']

/-- **The sheet permutation over the branch of mark `j`.** -/
def branchPerm (j : Fin k) : Equiv.Perm (Fin d) :=
  (ι.vertexPerm (β.x j)).trans (Equiv.swap (ι.vertexPerm (β.x j) (β.other j)) (β'.other j))

include ha in
theorem branchPerm_a (j : Fin k) : branchPerm β β' ι j (β.a j) = β'.a j := by
  unfold branchPerm
  rw [Equiv.trans_apply, ha]
  refine Equiv.swap_apply_of_ne_of_ne ?_ (β'.a_ne j)
  rw [← ha]
  exact (ι.vertexPerm (β.x j)).injective.ne (β.a_ne j)

theorem branchPerm_other (j : Fin k) : branchPerm β β' ι j (β.other j) = β'.other j := by
  unfold branchPerm
  rw [Equiv.trans_apply, Equiv.swap_apply_left]

include hx ha in
/-- The branch permutation moves sheets only inside the block of the mark. -/
theorem rel_branchPerm (j : Fin k) (s : Fin d) :
    (D.vertexPartition (β.x j)).Rel ((ι.vertexPerm (β.x j)).symm (branchPerm β β' ι j s)) s := by
  set σ := ι.vertexPerm (β.x j)
  have hQ : D'.vertexPartition (β'.x j) = (D.vertexPartition (β.x j)).relabel σ := by
    rw [← hx]; exact ι.vertexPartition (β.x j)
  have hb' : (D.vertexPartition (β.x j)).Rel (σ.symm (β'.other j)) (β.a j) := by
    have h := β'.rel_a j
    rw [hQ, ← ha j, ← σ.apply_symm_apply (β'.other j)] at h
    exact ((SheetPartition.relabel_rel_iff _ σ _ _).mp h).symm
  have hab := β.rel_a j
  unfold branchPerm
  rw [Equiv.trans_apply]
  by_cases h1 : σ s = σ (β.other j)
  · rw [σ.injective h1, Equiv.swap_apply_left]
    exact hb'.trans hab
  · by_cases h2 : σ s = β'.other j
    · rw [h2, Equiv.swap_apply_right, Equiv.symm_apply_apply]
      rw [← h2, Equiv.symm_apply_apply] at hb'
      exact (hb'.trans hab).symm
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.symm_apply_apply]
      rfl

/-! ## The target isomorphism -/

/-- The target vertex dictionary: `ι` on the old vertices, the identity on the new ones. -/
def tvIso : (regrowTarget T β.x).V ≃ (regrowTarget T' β'.x).V :=
  Equiv.sumCongr ι.targetVertex (Equiv.refl (Fin k ⊕ Fin k))

/-- The occurrence map: `ι` on the old edges, the identity on the new ones. -/
def occIso : Occ T k ≃ Occ T' k := Equiv.sumCongr (Equiv.refl _) ι.targetEdge

/-- The target edge dictionary. -/
def teIso : (regrowTarget T β.x).edges ≃ (regrowTarget T' β'.x).edges :=
  (occEquiv β.x).symm.trans ((occIso ι).trans (occEquiv β'.x))

@[simp] theorem tvIso_oldV (v : T.V) : tvIso β β' ι (oldV β.x v) = oldV β'.x (ι.targetVertex v) :=
  rfl
@[simp] theorem tvIso_midV (j : Fin k) : tvIso β β' ι (midV β.x j) = midV β'.x j := rfl
@[simp] theorem tvIso_tipV (j : Fin k) : tvIso β β' ι (tipV β.x j) = tipV β'.x j := rfl

@[simp] theorem teIso_oldE (e : T.edges) :
    teIso β β' ι (oldE β.x e) = oldE β'.x (ι.targetEdge e) := by
  simp [teIso, oldE, occIso]
@[simp] theorem teIso_bridgeE (j : Fin k) : teIso β β' ι (bridgeE β.x j) = bridgeE β'.x j := by
  simp [teIso, bridgeE, occIso]
@[simp] theorem teIso_leafE (j : Fin k) : teIso β β' ι (leafE β.x j) = leafE β'.x j := by
  simp [teIso, leafE, occIso]

/-- The vertex sheet permutations. -/
def vpIso : (regrowTarget T β.x).V → Equiv.Perm (Fin d) :=
  Sum.elim ι.vertexPerm (Sum.elim (branchPerm β β' ι) (branchPerm β β' ι))

/-- The occurrence sheet permutations. -/
def occPerm : Occ T k → Equiv.Perm (Fin d)
  | .inl (.inl j) => branchPerm β β' ι j
  | .inl (.inr j) => branchPerm β β' ι j
  | .inr e => ι.edgePerm e

/-- The edge sheet permutations. -/
def epIso (e : (regrowTarget T β.x).edges) : Equiv.Perm (Fin d) :=
  occPerm β β' ι ((occEquiv β.x).symm e)

@[simp] theorem vpIso_oldV (v : T.V) : vpIso β β' ι (oldV β.x v) = ι.vertexPerm v := rfl
@[simp] theorem vpIso_midV (j : Fin k) : vpIso β β' ι (midV β.x j) = branchPerm β β' ι j := rfl
@[simp] theorem vpIso_tipV (j : Fin k) : vpIso β β' ι (tipV β.x j) = branchPerm β β' ι j := rfl
@[simp] theorem epIso_oldE (e : T.edges) : epIso β β' ι (oldE β.x e) = ι.edgePerm e := by
  simp [epIso, oldE, occPerm]
@[simp] theorem epIso_bridgeE (j : Fin k) :
    epIso β β' ι (bridgeE β.x j) = branchPerm β β' ι j := by
  simp [epIso, bridgeE, occPerm]
@[simp] theorem epIso_leafE (j : Fin k) : epIso β β' ι (leafE β.x j) = branchPerm β β' ι j := by
  simp [epIso, leafE, occPerm]

include hx ha

omit hx in
theorem P_relabel (j : Fin k) : β'.P j = (β.P j).relabel (branchPerm β β' ι j) := by
  unfold Branching.P
  rw [pair_relabel, branchPerm_a β β' ι ha, branchPerm_other]

/-- **Isomorphisms of data extend over the regrowth.** -/
def regrowIso : GeometricDatumIso (regrowDatum β) (regrowDatum β') where
  targetVertex := tvIso β β' ι
  targetEdge := teIso β β' ι
  ends e := by
    rcases edge_cases β.x e with ⟨f, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [teIso_oldE, oldE_ends, oldE_ends]
      rcases ι.ends f with h | h
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; rfl)
    · rw [teIso_bridgeE, bridgeE_ends, bridgeE_ends]
      refine Or.inl ?_
      rw [tvIso_oldV, tvIso_midV, hx]
    · rw [teIso_leafE, leafE_ends, leafE_ends]
      exact Or.inl rfl
  vertexPerm := vpIso β β' ι
  edgePerm := epIso β β' ι
  vertexPartition v := by
    rcases vertex_cases β.x v with ⟨w, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ι.vertexPartition w
    · exact P_relabel β β' ι ha j
    · exact P_relabel β β' ι ha j
  edgePartition e := by
    rcases edge_cases β.x e with ⟨f, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [teIso_oldE, ep_oldE, ep_oldE, epIso_oldE]
      exact ι.edgePartition f
    · rw [teIso_bridgeE, ep_bridgeE, ep_bridgeE, epIso_bridgeE]
      exact P_relabel β β' ι ha j
    · rw [teIso_leafE, ep_leafE, ep_leafE, epIso_leafE, SheetPartition.discrete_relabel]
  compatible e v hv s := by
    rcases edge_cases β.x e with ⟨f, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [oldE_ends] at hv
      rw [epIso_oldE]
      rcases vertex_cases β.x v with ⟨w, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · simp only [oldV_inj] at hv
        exact ι.compatible f w hv s
      · simp at hv
      · simp at hv
    · rw [bridgeE_ends] at hv
      rw [epIso_bridgeE]
      rcases vertex_cases β.x v with ⟨w, rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩
      · simp only [oldV_inj, midV_ne_oldV, or_false] at hv
        subst hv
        exact rel_branchPerm β β' ι hx ha j s
      · simp only [oldV_ne_midV, midV_inj, false_or] at hv
        subst hv
        rw [vpIso_midV, Equiv.symm_apply_apply]
        rfl
      · simp at hv
    · rw [leafE_ends] at hv
      rw [epIso_leafE]
      rcases vertex_cases β.x v with ⟨w, rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩
      · simp at hv
      · simp only [midV_inj, tipV_ne_midV, or_false] at hv
        subst hv
        rw [vpIso_midV, Equiv.symm_apply_apply]
        rfl
      · simp only [midV_ne_tipV, tipV_inj, false_or] at hv
        subst hv
        rw [vpIso_tipV, Equiv.symm_apply_apply]
        rfl

/-! ## The induced dictionaries -/

theorem sourceVertexEquiv_oldSV (X : D.SourceVertex) :
    (regrowIso β β' ι hx ha).sourceVertexEquiv (oldSV β X) = oldSV β' (ι.sourceVertexEquiv X) :=
  rfl

theorem sourceVertexEquiv_wSV (j : Fin k) :
    (regrowIso β β' ι hx ha).sourceVertexEquiv (wSV β j) = wSV β' j := by
  apply Subtype.ext
  change ((midV β'.x j : (regrowTarget T' β'.x).V),
      branchPerm β β' ι j ((β.P j).repr (β.a j))) = (midV β'.x j, (β'.P j).repr (β'.a j))
  have h1 : (β.P j).repr (β.a j) = β.a j := (pair_repr_eq_self_iff (β.a_ne j) _).mpr (β.a_ne j)
  have h2 : (β'.P j).repr (β'.a j) = β'.a j :=
    (pair_repr_eq_self_iff (β'.a_ne j) _).mpr (β'.a_ne j)
  rw [h1, h2, branchPerm_a β β' ι ha]

theorem sourceEdgeEquiv_oldSE (F : D.SourceEdge) :
    (regrowIso β β' ι hx ha).sourceEdgeEquiv (oldSE β F) = oldSE β' (ι.sourceEdgeEquiv F) := by
  apply Subtype.ext
  change (teIso β β' ι (oldE β.x F.1.1), epIso β β' ι (oldE β.x F.1.1) F.1.2) =
    (oldE β'.x (ι.targetEdge F.1.1), ι.edgePerm F.1.1 F.1.2)
  rw [teIso_oldE, epIso_oldE]

theorem sourceEdgeEquiv_ebSE (j : Fin k) :
    (regrowIso β β' ι hx ha).sourceEdgeEquiv (ebSE β j) = ebSE β' j := by
  apply Subtype.ext
  change (teIso β β' ι (bridgeE β.x j),
      epIso β β' ι (bridgeE β.x j) (((regrowDatum β).edgePartition (bridgeE β.x j)).repr
        (β.a j))) = (bridgeE β'.x j,
      ((regrowDatum β').edgePartition (bridgeE β'.x j)).repr (β'.a j))
  rw [teIso_bridgeE, epIso_bridgeE, ep_bridgeE, ep_bridgeE]
  have h1 : (β.P j).repr (β.a j) = β.a j := (pair_repr_eq_self_iff (β.a_ne j) _).mpr (β.a_ne j)
  have h2 : (β'.P j).repr (β'.a j) = β'.a j :=
    (pair_repr_eq_self_iff (β'.a_ne j) _).mpr (β'.a_ne j)
  rw [h1, h2, branchPerm_a β β' ι ha]

theorem sourceEdgeEquiv_e₁SE (j : Fin k) :
    (regrowIso β β' ι hx ha).sourceEdgeEquiv (e₁SE β j) = e₁SE β' j := by
  apply Subtype.ext
  change (teIso β β' ι (leafE β.x j),
      epIso β β' ι (leafE β.x j) (((regrowDatum β).edgePartition (leafE β.x j)).repr
        (β.a j))) = (leafE β'.x j,
      ((regrowDatum β').edgePartition (leafE β'.x j)).repr (β'.a j))
  rw [teIso_leafE, epIso_leafE, ep_leafE, ep_leafE]
  exact Prod.ext rfl (branchPerm_a β β' ι ha j)

end

end DraismaVargas.Count.MarkedCount.Regrow
