module

public import DraismaVargasMarkedCount.MarkedCount.RegrowDatum

@[expose] public section

/-!
# Regrowth, part 3: the dangling dictionary of the regrown datum

Which source edges of `regrowDatum β` dangle:

* an old edge dangles iff it dangles in `D` (`isDangling_oldSE_iff`);
* the bridge `eb j` and the two loop edges `e₁ j, e₂ j` survive (`not_isDangling_ebSE`, ...);
* every other new edge dangles (`isDangling_bridgeSE`, `isDangling_leafSE`): the sheets outside
  `{a, b}` form dangling paths of length two.

So the surviving valencies (`nonDanglingValency_oldSV`, `_wSV`, `_cSV`, ...) are those of `D`
plus one at every mark, three at `w j`, two at `C j`, and zero at the other new vertices.

The method is the public tripod's dangling dictionary (`Gluing.not_isDangling_of_witness`: an
edge property without a vertex of valency one has no dangling edge, and the non-dangling edges
of a connected datum are such a property), applied in both directions. The hypothesis on the
marks is that each has a surviving edge in `D` (`hMark`); for a marked frame it has two.

The counting is done through the explicit decompositions `sum_sourceVertex` and
`sum_sourceEdge` of sums over the regrown source.
-/

namespace DraismaVargas.Count.MarkedCount.Regrow

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open GenusSixExistence.Tripod.Gluing (SheetOps.pair wCount not_isDangling_of_witness
  wCount_nonDangling_ne_one nonDanglingValency_eq_wCount wCount_congr)

variable {T : CFGraph.{0}} {d k : ℕ} {D : GluingDatum T d} (β : Branching D k)

/-! ## 1.  Sums over the regrown source -/

/-- The forward map of the source-vertex decomposition. -/
def svOfSum : D.SourceVertex ⊕ ((Σ j : Fin k, (β.P j).Blocks) ⊕ (Σ j : Fin k, (β.P j).Blocks)) →
    (regrowDatum β).SourceVertex
  | .inl Y => oldSV β Y
  | .inr (.inl ⟨j, b⟩) => midSV β j b.1
  | .inr (.inr ⟨j, b⟩) => tipSV β j b.1

theorem rel_blocks_eq {Q : SheetPartition d} {b b' : Q.Blocks} (h : Q.Rel b.1 b'.1) : b = b' := by
  apply Subtype.ext
  have h1 := b.2
  have h2 := b'.2
  unfold SheetPartition.Rel at h
  rw [← h1, ← h2]
  exact h

theorem svOfSum_bijective : Function.Bijective (svOfSum β) := by
  constructor
  · rintro (Y | ⟨j, b⟩ | ⟨j, b⟩) (Y' | ⟨j', b'⟩ | ⟨j', b'⟩) h <;>
      simp only [svOfSum, oldSV_inj, oldSV_ne_midSV, oldSV_ne_tipSV, midSV_ne_oldSV,
        midSV_ne_tipSV, tipSV_ne_oldSV, tipSV_ne_midSV] at h
    · rw [h]
    · obtain ⟨rfl, hb⟩ := (midSV_eq_iff β _ _ _ _).mp h
      rw [rel_blocks_eq hb]
    · obtain ⟨rfl, hb⟩ := (tipSV_eq_iff β _ _ _ _).mp h
      rw [rel_blocks_eq hb]
  · intro X
    rcases sourceVertex_cases β X with ⟨Y, rfl⟩ | ⟨j, i, rfl⟩ | ⟨j, i, rfl⟩
    · exact ⟨.inl Y, rfl⟩
    · refine ⟨.inr (.inl ⟨j, (β.P j).toBlock i⟩), ?_⟩
      exact (midSV_eq_iff β _ _ _ _).mpr ⟨rfl, (β.P j).rel_repr_left i⟩
    · refine ⟨.inr (.inr ⟨j, (β.P j).toBlock i⟩), ?_⟩
      exact (tipSV_eq_iff β _ _ _ _).mpr ⟨rfl, (β.P j).rel_repr_left i⟩

/-- **Sums over the regrown source vertices.** -/
theorem sum_sourceVertex {M : Type*} [AddCommMonoid M] (f : (regrowDatum β).SourceVertex → M) :
    ∑ X, f X = ∑ Y, f (oldSV β Y) + ∑ j, ∑ b : (β.P j).Blocks, f (midSV β j b.1) +
      ∑ j, ∑ b : (β.P j).Blocks, f (tipSV β j b.1) := by
  rw [← Fintype.sum_bijective _ (svOfSum_bijective β) (fun z ↦ f (svOfSum β z)) f
    (fun _ ↦ rfl), Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma,
    Fintype.sum_sigma, add_assoc]
  rfl

/-- The forward map of the source-edge decomposition. -/
def seOfSum : D.SourceEdge ⊕ ((Σ j : Fin k, (β.P j).Blocks) ⊕ (Fin k × Fin d)) →
    (regrowDatum β).SourceEdge
  | .inl F => oldSE β F
  | .inr (.inl ⟨j, b⟩) => bridgeSE β j b.1
  | .inr (.inr ⟨j, i⟩) => leafSE β j i

theorem seOfSum_bijective : Function.Bijective (seOfSum β) := by
  constructor
  · rintro (F | ⟨j, b⟩ | ⟨j, i⟩) (F' | ⟨j', b'⟩ | ⟨j', i'⟩) h <;>
      simp only [seOfSum, oldSE_inj, oldSE_ne_bridgeSE, oldSE_ne_leafSE, bridgeSE_ne_oldSE,
        bridgeSE_ne_leafSE, leafSE_ne_oldSE, leafSE_ne_bridgeSE] at h
    · rw [h]
    · obtain ⟨rfl, hb⟩ := (bridgeSE_eq_iff β _ _ _ _).mp h
      rw [rel_blocks_eq hb]
    · obtain ⟨rfl, rfl⟩ := (leafSE_eq_iff β _ _ _ _).mp h
      rfl
  · intro E
    rcases sourceEdge_cases β E with ⟨F, rfl⟩ | ⟨j, i, rfl⟩ | ⟨j, i, rfl⟩
    · exact ⟨.inl F, rfl⟩
    · refine ⟨.inr (.inl ⟨j, (β.P j).toBlock i⟩), ?_⟩
      exact (bridgeSE_eq_iff β _ _ _ _).mpr ⟨rfl, (β.P j).rel_repr_left i⟩
    · exact ⟨.inr (.inr ⟨j, i⟩), rfl⟩

/-- **Sums over the regrown source edges.** -/
theorem sum_sourceEdge {M : Type*} [AddCommMonoid M] (f : (regrowDatum β).SourceEdge → M) :
    ∑ E, f E = ∑ F, f (oldSE β F) + ∑ j, ∑ b : (β.P j).Blocks, f (bridgeSE β j b.1) +
      ∑ j, ∑ i, f (leafSE β j i) := by
  rw [← Fintype.sum_bijective _ (seOfSum_bijective β) (fun z ↦ f (seOfSum β z)) f
    (fun _ ↦ rfl), Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma,
    Fintype.sum_prod_type, add_assoc]
  rfl

/-- Summing over the blocks of a partition a function supported on the block of `s`. -/
theorem sum_blocks_rel {M : Type*} [AddCommMonoid M] (Q : SheetPartition d) (s : Fin d)
    (f : Q.Blocks → M) :
    ∑ b : Q.Blocks, (if Q.Rel b.1 s then f b else 0) = f (Q.toBlock s) := by
  classical
  rw [Fintype.sum_eq_single (Q.toBlock s)]
  · exact ite_eq_left (Q.rel_repr_left s)
  · intro b hb
    exact ite_eq_right fun h ↦ hb (rel_blocks_eq (h.trans (Q.rel_repr_right s)))

/-! ## 2.  Two generic facts about valency -/

theorem isDangling_of_nonDanglingValency_eq_zero {S : CFGraph} (E : GluingDatum S d)
    {e : E.SourceEdge} {X : E.SourceVertex} (hInc : Incident E e X)
    (h0 : nonDanglingValency E X = 0) : IsDangling E e := by
  by_contra hnd
  rw [← card_nonDanglingIncident, Finset.card_eq_zero] at h0
  have h := (mem_nonDanglingIncident E X e).mpr ⟨hnd, hInc⟩
  rw [h0] at h
  exact Finset.notMem_empty e h

theorem nonDanglingValency_eq_zero_of_unique {S : CFGraph} (E : GluingDatum S d)
    (hE : E.Connected) (X : E.SourceVertex) (e : E.SourceEdge)
    (h : ∀ f : E.SourceEdge, ¬ IsDangling E f → Incident E f X → f = e) :
    nonDanglingValency E X = 0 := by
  classical
  have hle : nonDanglingValency E X ≤ 1 := by
    rw [← card_nonDanglingIncident]
    refine Finset.card_le_one.mpr fun f hf g hg ↦ ?_
    rw [mem_nonDanglingIncident] at hf hg
    rw [h f hf.1 hf.2, h g hg.1 hg.2]
  have hne := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one E hE X
  omega

/-! ## 3.  The other new edges dangle -/

variable (hD : D.Connected)

include hD

omit hD in
theorem incident_tipSV_unique (j : Fin k) {i : Fin d} (hi : ¬ (β.P j).Rel i (β.a j))
    (f : (regrowDatum β).SourceEdge) (hf : Incident (regrowDatum β) f (tipSV β j i)) :
    f = leafSE β j i := by
  rcases sourceEdge_cases β f with ⟨F, rfl⟩ | ⟨j', i', rfl⟩ | ⟨j', i', rfl⟩
  · exact absurd hf (incident_oldSE_tipSV β F j i)
  · exact absurd hf (incident_bridgeSE_tipSV β j' j i' i)
  · obtain ⟨rfl, hrel⟩ := (incident_leafSE_tipSV β _ _ _ _).mp hf
    rcases (β.P_rel_iff j' i' i).mp hrel with h | ⟨-, h⟩
    · rw [h]
    · exact absurd ((β.P_rel_a_iff j' i).mpr h) hi

/-- **A leaf edge outside `{a, b}` dangles**: its tip has no other edge. -/
theorem isDangling_leafSE (j : Fin k) {i : Fin d} (hi : ¬ (β.P j).Rel i (β.a j)) :
    IsDangling (regrowDatum β) (leafSE β j i) := by
  have hR := connected_regrowDatum β hD
  refine isDangling_of_nonDanglingValency_eq_zero _ (X := tipSV β j i) ?_ ?_
  · exact (incident_leafSE_tipSV β j j i i).mpr ⟨rfl, (β.P j).rel_repr_left i |>.symm.trans
      ((β.P j).rel_repr_left i)⟩
  · exact nonDanglingValency_eq_zero_of_unique _ hR _ (leafSE β j i)
      fun f _ hf ↦ incident_tipSV_unique β j hi f hf

/-- **A bridge edge outside `{a, b}` dangles**: past it, the leaf edge dangles. -/
theorem isDangling_bridgeSE (j : Fin k) {i : Fin d} (hi : ¬ (β.P j).Rel i (β.a j)) :
    IsDangling (regrowDatum β) (bridgeSE β j i) := by
  have hR := connected_regrowDatum β hD
  have hrefl : (β.P j).Rel i i := rfl
  refine isDangling_of_nonDanglingValency_eq_zero _ (X := midSV β j i)
    ((incident_bridgeSE_midSV β j j i i).mpr ⟨rfl, hrefl⟩) ?_
  refine nonDanglingValency_eq_zero_of_unique _ hR _ (bridgeSE β j i) fun f hnd hf ↦ ?_
  rcases sourceEdge_cases β f with ⟨F, rfl⟩ | ⟨j', i', rfl⟩ | ⟨j', i', rfl⟩
  · exact absurd hf (incident_oldSE_midSV β F j i)
  · obtain ⟨rfl, hrel⟩ := (incident_bridgeSE_midSV β _ _ _ _).mp hf
    exact (bridgeSE_eq_iff β _ _ _ _).mpr ⟨rfl, hrel⟩
  · exfalso
    obtain ⟨rfl, hrel⟩ := (incident_leafSE_midSV β _ _ _ _).mp hf
    rcases (β.P_rel_iff j' i' i).mp hrel with h | ⟨-, h⟩
    · subst h
      exact hnd (isDangling_leafSE β hD j' hi)
    · exact hi ((β.P_rel_a_iff j' i).mpr h)

omit hD

/-! ## 4.  The witness -/

/-- The edges that survive in the regrowth: the survivors of `D`, the bridges and the loop
edges. -/
def Survives (E : (regrowDatum β).SourceEdge) : Prop :=
  (∃ F, E = oldSE β F ∧ ¬ IsDangling D F) ∨ (∃ j, E = ebSE β j) ∨ (∃ j, E = e₁SE β j) ∨
    (∃ j, E = e₂SE β j)

theorem survives_oldSE (F : D.SourceEdge) : Survives β (oldSE β F) ↔ ¬ IsDangling D F := by
  constructor
  · rintro (⟨F', h, hF'⟩ | ⟨j, h⟩ | ⟨j, h⟩ | ⟨j, h⟩)
    · rw [oldSE_injective β h]; exact hF'
    · exact absurd h (oldSE_ne_bridgeSE β _ _ _)
    · exact absurd h (oldSE_ne_leafSE β _ _ _)
    · exact absurd h (oldSE_ne_leafSE β _ _ _)
  · intro h; exact Or.inl ⟨F, rfl, h⟩

theorem survives_bridgeSE (j : Fin k) (i : Fin d) :
    Survives β (bridgeSE β j i) ↔ (β.P j).Rel i (β.a j) := by
  constructor
  · rintro (⟨F', h, -⟩ | ⟨j', h⟩ | ⟨j', h⟩ | ⟨j', h⟩)
    · exact absurd h (bridgeSE_ne_oldSE β _ _ _)
    · obtain ⟨rfl, h⟩ := (bridgeSE_eq_iff β _ _ _ _).mp h; exact h
    · exact absurd h (bridgeSE_ne_leafSE β _ _ _ _)
    · exact absurd h (bridgeSE_ne_leafSE β _ _ _ _)
  · intro h
    exact Or.inr (Or.inl ⟨j, (bridgeSE_eq_iff β _ _ _ _).mpr ⟨rfl, h⟩⟩)

theorem survives_leafSE (j : Fin k) (i : Fin d) :
    Survives β (leafSE β j i) ↔ (β.P j).Rel i (β.a j) := by
  rw [β.P_rel_a_iff]
  constructor
  · rintro (⟨F', h, -⟩ | ⟨j', h⟩ | ⟨j', h⟩ | ⟨j', h⟩)
    · exact absurd h (leafSE_ne_oldSE β _ _ _)
    · exact absurd h (leafSE_ne_bridgeSE β _ _ _ _)
    · obtain ⟨rfl, h⟩ := (leafSE_eq_iff β _ _ _ _).mp h; exact Or.inl h
    · obtain ⟨rfl, h⟩ := (leafSE_eq_iff β _ _ _ _).mp h; exact Or.inr h
  · rintro (rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))

/-- The number of marks at a source vertex of `D`. -/
def markCount (Y : D.SourceVertex) : ℕ := (Finset.univ.filter fun j ↦ β.mark j = Y).card

open Classical in
/-- The number of bridges with property `W` at the old vertex `Y`. -/
def bridgeCount (W : (regrowDatum β).SourceEdge → Prop) (Y : D.SourceVertex) : ℕ :=
  ∑ j, ∑ b : (β.P j).Blocks,
    (if W (bridgeSE β j b.1) ∧ D.sourceEndpoint (β.x j) b.1 = Y then 1 else 0)

theorem bridgeCount_eq_zero (W : (regrowDatum β).SourceEdge → Prop) (Y : D.SourceVertex)
    (h : ∀ j (b : (β.P j).Blocks), W (bridgeSE β j b.1) → D.sourceEndpoint (β.x j) b.1 ≠ Y) :
    bridgeCount β W Y = 0 := by
  unfold bridgeCount
  exact Finset.sum_eq_zero fun j _ ↦ Finset.sum_eq_zero fun b _ ↦
    ite_eq_right fun hb ↦ h j b hb.1 hb.2

/-- The count of an edge property at an old vertex: old edges and the bridges of the marks. -/
theorem wCount_oldSV (W : (regrowDatum β).SourceEdge → Prop) (Y : D.SourceVertex) :
    wCount (regrowDatum β) W (oldSV β Y) =
      wCount D (fun F ↦ W (oldSE β F)) Y + bridgeCount β W Y := by
  classical
  unfold wCount bridgeCount
  rw [Finset.card_filter, Finset.card_filter, sum_sourceEdge]
  simp only [incident_oldSE_oldSV, incident_bridgeSE_oldSV, incident_leafSE_oldSV, and_false,
    ite_false, Finset.sum_const_zero, add_zero]

theorem wCount_survives_oldSV (Y : D.SourceVertex) :
    wCount (regrowDatum β) (Survives β) (oldSV β Y) = nonDanglingValency D Y + markCount β Y := by
  classical
  rw [wCount_oldSV, nonDanglingValency_eq_wCount]
  congr 1
  · exact wCount_congr _ _ fun F _ ↦ survives_oldSE β F
  · unfold markCount bridgeCount
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [survives_bridgeSE]
    rw [Fintype.sum_eq_single ((β.P j).toBlock (β.a j))]
    · have h1 : (β.P j).Rel ((β.P j).toBlock (β.a j)).1 (β.a j) := (β.P j).rel_repr_left _
      have h2 : D.sourceEndpoint (β.x j) ((β.P j).toBlock (β.a j)).1 = β.mark j :=
        sourceEndpoint_x_of_rel β j h1
      simp only [h1, h2, true_and]
    · intro b hb
      have : ¬ (β.P j).Rel b.1 (β.a j) := fun h ↦
        hb (rel_blocks_eq (h.trans ((β.P j).rel_repr_right _)))
      exact ite_eq_right fun h ↦ this h.1

open Classical in
/-- Counts over the blocks of `P j` at `w j` and `C j`. -/
theorem wCount_midSV (W : (regrowDatum β).SourceEdge → Prop) (j : Fin k) (i : Fin d) :
    wCount (regrowDatum β) W (midSV β j i) =
      ∑ b : (β.P j).Blocks, (if W (bridgeSE β j b.1) ∧ (β.P j).Rel b.1 i then 1 else 0) +
        ∑ i', (if W (leafSE β j i') ∧ (β.P j).Rel i' i then 1 else 0) := by
  classical
  unfold wCount
  rw [Finset.card_filter, sum_sourceEdge]
  simp only [incident_oldSE_midSV, incident_bridgeSE_midSV, incident_leafSE_midSV, and_false,
    ite_false, Finset.sum_const_zero, zero_add]
  congr 1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      exact Finset.sum_eq_zero fun b _ ↦ by simp [hj']
    · simp
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      exact Finset.sum_eq_zero fun b _ ↦ by simp [hj']
    · simp

open Classical in
theorem wCount_tipSV (W : (regrowDatum β).SourceEdge → Prop) (j : Fin k) (i : Fin d) :
    wCount (regrowDatum β) W (tipSV β j i) =
      ∑ i', (if W (leafSE β j i') ∧ (β.P j).Rel i' i then 1 else 0) := by
  classical
  unfold wCount
  rw [Finset.card_filter, sum_sourceEdge]
  simp only [incident_oldSE_tipSV, incident_bridgeSE_tipSV, incident_leafSE_tipSV, and_false,
    ite_false, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    exact Finset.sum_eq_zero fun b _ ↦ by simp [hj']
  · simp

/-- The count of the surviving edges over `{a, b}` at `w j` and `C j`, and nothing elsewhere
over the branch. -/
theorem wCount_survives_midSV (j : Fin k) (i : Fin d) :
    wCount (regrowDatum β) (Survives β) (midSV β j i) =
      if (β.P j).Rel i (β.a j) then 3 else 0 := by
  classical
  rw [wCount_midSV]
  simp only [survives_bridgeSE, survives_leafSE]
  by_cases hi : (β.P j).Rel i (β.a j)
  · rw [ite_eq_left hi]
    have h1 : ∀ b : (β.P j).Blocks,
        (if (β.P j).Rel b.1 (β.a j) ∧ (β.P j).Rel b.1 i then (1 : ℕ) else 0) =
          if (β.P j).Rel b.1 (β.a j) then 1 else 0 := fun b ↦ by
      by_cases hb : (β.P j).Rel b.1 (β.a j)
      · rw [ite_eq_left ⟨hb, hb.trans hi.symm⟩, ite_eq_left hb]
      · rw [ite_eq_right (fun h ↦ hb h.1), ite_eq_right hb]
    have h2 : ∀ i' : Fin d,
        (if (β.P j).Rel i' (β.a j) ∧ (β.P j).Rel i' i then (1 : ℕ) else 0) =
          if i' ∈ ({β.a j, β.other j} : Finset (Fin d)) then 1 else 0 := fun i' ↦ by
      by_cases hb : (β.P j).Rel i' (β.a j)
      · have hm : i' ∈ ({β.a j, β.other j} : Finset (Fin d)) := by
          rw [Finset.mem_insert, Finset.mem_singleton]; exact (β.P_rel_a_iff j i').mp hb
        rw [ite_eq_left ⟨hb, hb.trans hi.symm⟩, ite_eq_left hm]
      · have hm : i' ∉ ({β.a j, β.other j} : Finset (Fin d)) := by
          rw [Finset.mem_insert, Finset.mem_singleton]
          exact fun h ↦ hb ((β.P_rel_a_iff j i').mpr h)
        rw [ite_eq_right (fun h ↦ hb h.1), ite_eq_right hm]
    rw [Finset.sum_congr rfl fun b _ ↦ h1 b, Finset.sum_congr rfl fun i' _ ↦ h2 i',
      sum_blocks_rel (β.P j) (β.a j) (fun _ ↦ (1 : ℕ)), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, Finset.card_pair (β.a_ne j)]
    rfl
  · rw [ite_eq_right hi]
    have h1 : ∀ b : (β.P j).Blocks,
        (if (β.P j).Rel b.1 (β.a j) ∧ (β.P j).Rel b.1 i then (1 : ℕ) else 0) = 0 := fun b ↦
      ite_eq_right fun h ↦ hi (h.2.symm.trans h.1)
    have h2 : ∀ i' : Fin d,
        (if (β.P j).Rel i' (β.a j) ∧ (β.P j).Rel i' i then (1 : ℕ) else 0) = 0 := fun i' ↦
      ite_eq_right fun h ↦ hi (h.2.symm.trans h.1)
    rw [Finset.sum_congr rfl fun b _ ↦ h1 b, Finset.sum_congr rfl fun i' _ ↦ h2 i']
    simp

theorem wCount_survives_tipSV (j : Fin k) (i : Fin d) :
    wCount (regrowDatum β) (Survives β) (tipSV β j i) =
      if (β.P j).Rel i (β.a j) then 2 else 0 := by
  classical
  rw [wCount_tipSV]
  simp only [survives_leafSE]
  by_cases hi : (β.P j).Rel i (β.a j)
  · rw [ite_eq_left hi]
    have h2 : ∀ i' : Fin d,
        (if (β.P j).Rel i' (β.a j) ∧ (β.P j).Rel i' i then (1 : ℕ) else 0) =
          if i' ∈ ({β.a j, β.other j} : Finset (Fin d)) then 1 else 0 := fun i' ↦ by
      by_cases hb : (β.P j).Rel i' (β.a j)
      · have hm : i' ∈ ({β.a j, β.other j} : Finset (Fin d)) := by
          rw [Finset.mem_insert, Finset.mem_singleton]; exact (β.P_rel_a_iff j i').mp hb
        rw [ite_eq_left ⟨hb, hb.trans hi.symm⟩, ite_eq_left hm]
      · have hm : i' ∉ ({β.a j, β.other j} : Finset (Fin d)) := by
          rw [Finset.mem_insert, Finset.mem_singleton]
          exact fun h ↦ hb ((β.P_rel_a_iff j i').mpr h)
        rw [ite_eq_right (fun h ↦ hb h.1), ite_eq_right hm]
    rw [Finset.sum_congr rfl fun i' _ ↦ h2 i', Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, Finset.card_pair (β.a_ne j)]
    rfl
  · rw [ite_eq_right hi]
    have h2 : ∀ i' : Fin d,
        (if (β.P j).Rel i' (β.a j) ∧ (β.P j).Rel i' i then (1 : ℕ) else 0) = 0 := fun i' ↦
      ite_eq_right fun h ↦ hi (h.2.symm.trans h.1)
    rw [Finset.sum_congr rfl fun i' _ ↦ h2 i']
    simp

/-! ## 5.  The dictionary -/

variable (hMark : ∀ j, nonDanglingValency D (β.mark j) ≠ 0)

include hD hMark

/-- **No surviving-edge count is one**: the witness of the dictionary. -/
theorem wCount_survives_ne_one (X : (regrowDatum β).SourceVertex) :
    wCount (regrowDatum β) (Survives β) X ≠ 1 := by
  rcases sourceVertex_cases β X with ⟨Y, rfl⟩ | ⟨j, i, rfl⟩ | ⟨j, i, rfl⟩
  · rw [wCount_survives_oldSV]
    have hne := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one D hD Y
    by_cases hm : markCount β Y = 0
    · rw [hm, add_zero]; exact hne
    · obtain ⟨j, hj⟩ : ∃ j, β.mark j = Y := by
        by_contra hno
        push Not at hno
        apply hm
        unfold markCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun j _ ↦ hno j
      have := hMark j
      rw [hj] at this
      omega
  · rw [wCount_survives_midSV]; split_ifs <;> omega
  · rw [wCount_survives_tipSV]; split_ifs <;> omega

/-- The survivors of the witness survive. -/
theorem not_isDangling_of_survives {E : (regrowDatum β).SourceEdge} (hE : Survives β E) :
    ¬ IsDangling (regrowDatum β) E :=
  not_isDangling_of_witness _ (Survives β) (wCount_survives_ne_one β hD hMark) hE

theorem not_isDangling_ebSE (j : Fin k) : ¬ IsDangling (regrowDatum β) (ebSE β j) :=
  not_isDangling_of_survives β hD hMark (Or.inr (Or.inl ⟨j, rfl⟩))

theorem not_isDangling_e₁SE (j : Fin k) : ¬ IsDangling (regrowDatum β) (e₁SE β j) :=
  not_isDangling_of_survives β hD hMark (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))

theorem not_isDangling_e₂SE (j : Fin k) : ¬ IsDangling (regrowDatum β) (e₂SE β j) :=
  not_isDangling_of_survives β hD hMark (Or.inr (Or.inr (Or.inr ⟨j, rfl⟩)))

/-- **The old edges keep their status.** -/
theorem isDangling_oldSE_iff (F : D.SourceEdge) :
    IsDangling (regrowDatum β) (oldSE β F) ↔ IsDangling D F := by
  classical
  have hR := connected_regrowDatum β hD
  constructor
  · intro h
    by_contra hF
    exact not_isDangling_of_survives β hD hMark ((survives_oldSE β F).mpr hF) h
  · intro hF
    by_contra hnd
    refine not_isDangling_of_witness D (fun F' ↦ ¬ IsDangling (regrowDatum β) (oldSE β F'))
      (fun Y ↦ ?_) hnd hF
    -- the count in `D` at `Y`
    have hOld := wCount_oldSV β (fun E ↦ ¬ IsDangling (regrowDatum β) E) Y
    rw [← nonDanglingValency_eq_wCount] at hOld
    have hne := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hR
      (oldSV β Y)
    by_cases hm : ∃ j, β.mark j = Y
    · obtain ⟨j, rfl⟩ := hm
      have hge : nonDanglingValency D (β.mark j) ≤
          wCount D (fun F' ↦ ¬ IsDangling (regrowDatum β) (oldSE β F')) (β.mark j) := by
        rw [nonDanglingValency_eq_wCount]
        exact GenusSixExistence.Tripod.Gluing.wCount_le_of_imp _ _ fun F' _ h ↦
          not_isDangling_of_survives β hD hMark ((survives_oldSE β F').mpr h)
      have h1 := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one D hD
        (β.mark j)
      have h2 := hMark j
      omega
    · push Not at hm
      have hzero : bridgeCount β (fun E ↦ ¬ IsDangling (regrowDatum β) E) Y = 0 := by
        refine bridgeCount_eq_zero β _ Y fun j b hnd hY ↦ ?_
        by_cases hb : (β.P j).Rel b.1 (β.a j)
        · exact hm j ((sourceEndpoint_x_of_rel β j hb).symm.trans hY)
        · exact hnd (isDangling_bridgeSE β hD j hb)
      rw [hzero, add_zero] at hOld
      rw [← hOld]
      exact hne

/-- **The surviving edges of the regrowth** are exactly `Survives`. -/
theorem not_isDangling_iff (E : (regrowDatum β).SourceEdge) :
    ¬ IsDangling (regrowDatum β) E ↔ Survives β E := by
  constructor
  · intro h
    rcases sourceEdge_cases β E with ⟨F, rfl⟩ | ⟨j, i, rfl⟩ | ⟨j, i, rfl⟩
    · exact (survives_oldSE β F).mpr fun hF ↦ h ((isDangling_oldSE_iff β hD hMark F).mpr hF)
    · rw [survives_bridgeSE]
      by_contra hi
      exact h (isDangling_bridgeSE β hD j hi)
    · rw [survives_leafSE]
      by_contra hi
      exact h (isDangling_leafSE β hD j hi)
  · exact not_isDangling_of_survives β hD hMark

theorem nonDanglingValency_eq_wCount_survives (X : (regrowDatum β).SourceVertex) :
    nonDanglingValency (regrowDatum β) X = wCount (regrowDatum β) (Survives β) X := by
  rw [nonDanglingValency_eq_wCount]
  exact wCount_congr _ _ fun E _ ↦ not_isDangling_iff β hD hMark E

/-! ## 6.  The surviving valencies -/

theorem nonDanglingValency_oldSV (Y : D.SourceVertex) :
    nonDanglingValency (regrowDatum β) (oldSV β Y) = nonDanglingValency D Y + markCount β Y := by
  rw [nonDanglingValency_eq_wCount_survives β hD hMark, wCount_survives_oldSV]

theorem nonDanglingValency_midSV (j : Fin k) (i : Fin d) :
    nonDanglingValency (regrowDatum β) (midSV β j i) =
      if (β.P j).Rel i (β.a j) then 3 else 0 := by
  rw [nonDanglingValency_eq_wCount_survives β hD hMark, wCount_survives_midSV]

theorem nonDanglingValency_tipSV (j : Fin k) (i : Fin d) :
    nonDanglingValency (regrowDatum β) (tipSV β j i) =
      if (β.P j).Rel i (β.a j) then 2 else 0 := by
  rw [nonDanglingValency_eq_wCount_survives β hD hMark, wCount_survives_tipSV]

theorem nonDanglingValency_wSV (j : Fin k) :
    nonDanglingValency (regrowDatum β) (wSV β j) = 3 := by
  rw [wSV, nonDanglingValency_midSV β hD hMark]
  exact ite_eq_left (show (β.P j).Rel (β.a j) (β.a j) from rfl)

theorem nonDanglingValency_cSV (j : Fin k) :
    nonDanglingValency (regrowDatum β) (cSV β j) = 2 := by
  rw [cSV, nonDanglingValency_tipSV β hD hMark]
  exact ite_eq_left (show (β.P j).Rel (β.a j) (β.a j) from rfl)

end

end DraismaVargas.Count.MarkedCount.Regrow
