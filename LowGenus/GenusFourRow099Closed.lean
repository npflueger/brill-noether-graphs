module

public import LowGenus.GenusFourRow097Closed
public import LowGenus.GenusFiveConfigurations
public import LowGenus.GenusFourCubicAtlas

@[expose] public section

/-!
# Closed-orthant existence on genus-four Core 099 (`K₃,₃`)

Row `099` of the genus-four cubic atlas is `K₃,₃`, with slot `slot i j` running
from `aVertex i` to `bVertex j`.  This file proves the closed-orthant
obligation of `LowGenus.GenusFourRowsClosed` for this row: every nonloopy
forest face of every subdivision of `K₃,₃` carries a degree-three rank-one
divisor.

The proof is a cone march over `DegSpec`, whose slot lengths may vanish.  The
pencil is

```text
D = a₀ + a₁ + a₂ ,
```

and `bVertex j` is still reached by one ramp: potential `-t` at `bVertex j` and
`0` elsewhere, falling with slope `-1` along the three slots into `bVertex j`,
where `t` is the least of their three lengths.  By the generic
`DegSpec.prin_ramp_eq`, the ramp moves the chip at `aVertex i` to path
position `t` on `slot i j`, for each `i`:

```text
D + div(ramp) = Σᵢ (the point at position t on slot i j) .
```

This is visibly effective, with no vertex-by-vertex check, and on a shortest
slot position `t` is `bVertex j` itself.  Nothing changes at a face.  When
`t = 0`, the ramp is the zero script; `bVertex j` is then contracted onto some
`aVertex i`, and `D` already has a chip there.  The one closed-orthant field,
`RampData.repInv`, is free because the face's `rep` is the `compFold` of the
vanishing slots (`RampData.of_reachIn`).  Rank one then follows from reaching
the six core classes, by the class strong separator of a `DegSpec`
(`LowGenus.GenusFourRow097Closed.bnExists_of_reaches_coreVertices`).

So no chamber decomposition, no symmetry reduction and no face case analysis
is needed: the argument is uniform in the length vector.  The automorphism
group of `K₃,₃` (order 72) is never used.

## Relation to the generated certificate

`LowGenus/Generated/G4Row099.lean` proves the same statement
(`AtanasovRanganathan.GenusFourGeneratedRows.row099_closed`) by a kernel-checked
`.rpf` certificate tree.  This readable proof is the one
`AtanasovRanganathan.GenusFourRowsClosed.rowClosedCoverage` consumes; the
certificate is kept as an independent check.
-/

namespace AtanasovRanganathan.GenusFourRow099Closed

open Utilities
open Utilities.Certificate
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.ContractionForestCensusGeneral
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFourCubicAtlas

/-! ## Bipartite bookkeeping on the nine slots -/

/-- The `i`-th vertex of the first part of `K₃,₃`. -/
def aVertex (i : Fin 3) : Fin 6 := ⟨i.val, by have := i.isLt; omega⟩

/-- The `j`-th vertex of the second part of `K₃,₃`. -/
def bVertex (j : Fin 3) : Fin 6 := ⟨3 + j.val, by have := j.isLt; omega⟩

/-- The slot joining `aVertex i` to `bVertex j`. -/
def slot (i j : Fin 3) : Fin 9 :=
  ⟨3 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

theorem aVertex_inj_iff (i i' : Fin 3) : aVertex i = aVertex i' ↔ i = i' := by
  revert i i'
  decide

theorem bVertex_inj_iff (j j' : Fin 3) : bVertex j = bVertex j' ↔ j = j' := by
  revert j j'
  decide

theorem aVertex_ne_bVertex (i j : Fin 3) : aVertex i ≠ bVertex j := by
  revert i j
  decide

theorem slot_inj_iff (i j i' j' : Fin 3) :
    slot i j = slot i' j' ↔ i = i' ∧ j = j' := by
  revert i j i' j'
  decide

theorem exists_slot (edge : Fin 9) : ∃ i j, edge = slot i j := by
  revert edge
  decide

theorem sum_over_slots {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
    ∑ edge : Fin 9, f edge = ∑ i : Fin 3, ∑ j : Fin 3, f (slot i j) := by
  have hbij : Function.Bijective (fun ij : Fin 3 × Fin 3 => slot ij.1 ij.2) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by decide⟩
    intro x y hxy
    have := (slot_inj_iff x.1 x.2 y.1 y.2).mp hxy
    exact Prod.ext this.1 this.2
  calc
    ∑ edge : Fin 9, f edge = ∑ ij : Fin 3 × Fin 3, f (slot ij.1 ij.2) :=
      (Fintype.sum_bijective _ hbij _ f fun _ => rfl).symm
    _ = ∑ i : Fin 3, ∑ j : Fin 3, f (slot i j) := Fintype.sum_prod_type _

/-! ## The oriented `K₃,₃` core -/

theorem aVertex_or_bVertex (u : Fin 6) :
    (∃ i : Fin 3, u = aVertex i) ∨ (∃ j : Fin 3, u = bVertex j) := by
  revert u
  decide

/-! ## The oriented `K₃,₃` core -/

/-- The orientation of the row-099 core, read on the core itself: slot
`slot i j` runs from `aVertex i` to `bVertex j`.  On the closed orthant the
lengths are not part of this datum. -/
structure IsK33Core (core : ExplicitPotential.Core 6 9) : Prop where
  tail : ∀ i j : Fin 3, core.tail (slot i j) = aVertex i
  head : ∀ i j : Fin 3, core.head (slot i j) = bVertex j

theorem isK33Core_row099 : IsK33Core row099Core := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl

namespace IsK33Core

variable {core : ExplicitPotential.Core 6 9}

/-- `K₃,₃` is connected: if no slot crosses a cut, membership of every
`aVertex` agrees with membership of every `bVertex`, so the cut is trivial. -/
theorem connected (h : IsK33Core core) : core.Connected := by
  intro S hS
  obtain ⟨v, w, hv, hw⟩ := hS
  by_contra hNoCross
  simp only [not_exists, not_or] at hNoCross
  have hIff : ∀ i j : Fin 3, (aVertex i ∈ S ↔ bVertex j ∈ S) := by
    intro i j
    have hedge := hNoCross (slot i j)
    rw [h.tail, h.head] at hedge
    constructor
    · intro hA
      by_contra hB
      exact hedge.1 ⟨hA, hB⟩
    · intro hB
      by_contra hA
      exact hedge.2 ⟨hB, hA⟩
  have hConst : ∀ u u' : Fin 6, (u ∈ S ↔ u' ∈ S) := by
    intro u u'
    rcases aVertex_or_bVertex u with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;>
      rcases aVertex_or_bVertex u' with ⟨i', rfl⟩ | ⟨j', rfl⟩
    · exact (hIff i 0).trans (hIff i' 0).symm
    · exact hIff i j'
    · exact (hIff i' j).symm
    · exact (hIff 0 j).symm.trans (hIff 0 j')
  exact hw ((hConst v w).mp hv)

end IsK33Core

/-! ## The depth of the cone march

The least of the three slot lengths into `bVertex j`.  It is a function of the
length vector alone and may be zero. -/

section Depth

/-- Depth of the cone march into `bVertex j`. -/
def depth (L : Fin 9 → ℕ) (j : Fin 3) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty fun i : Fin 3 => L (slot i j)

theorem depth_le (L : Fin 9 → ℕ) (i j : Fin 3) : depth L j ≤ L (slot i j) :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_depth_eq (L : Fin 9 → ℕ) (j : Fin 3) :
    ∃ i : Fin 3, L (slot i j) = depth L j := by
  obtain ⟨i, _, hEq⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin 3))
      fun i : Fin 3 => L (slot i j)
  exact ⟨i, hEq.symm⟩

end Depth

/-! ## The cone march as a closed-orthant ramp -/

section Ramp

/-- Core potential of the cone march into `bVertex j`. -/
def conePot (j : Fin 3) (t : ℕ) : Fin 6 → ℤ := fun v =>
  if v = bVertex j then -(t : ℤ) else 0

/-- Slot signs of the cone march: `-1` on the three slots into `bVertex j`. -/
def coneSgn (core : ExplicitPotential.Core 6 9) (j : Fin 3) : Fin 9 → ℤ := fun e =>
  if core.head e = bVertex j then -1 else 0

/-- The cone-march firing script. -/
def coneScript (d : DegSpec 6 9) (j : Fin 3) : firing_script d.graph :=
  d.rampScript (conePot j (depth d.length j)) (coneSgn d.core j) (fun _ => 0)
    (depth d.length j)

/-- `rep`-equality on the core is generated by the vanishing slots.  This is
`compFold_iff` for `faceSpec`. -/
def RepGen (d : DegSpec 6 9) : Prop :=
  ∀ u v : Fin 6, d.rep u = d.rep v →
    ReachIn d.core (Finset.univ.filter fun e : Fin 9 => d.length e = 0) u v

variable {d : DegSpec 6 9}

theorem coneSgn_slot (h : IsK33Core d.core) (i j j' : Fin 3) :
    coneSgn d.core j (slot i j') = if j' = j then -1 else 0 := by
  simp only [coneSgn, h.head, bVertex_inj_iff]

theorem coneRamp (h : IsK33Core d.core) (hrep : RepGen d) (j : Fin 3) :
    DegSpec.RampData d (conePot j (depth d.length j)) (coneSgn d.core j)
      (fun _ => 0) (depth d.length j) := by
  refine DegSpec.RampData.of_reachIn ?_ ?_ hrep
  · intro e
    obtain ⟨i, j', rfl⟩ := exists_slot e
    rw [h.tail, h.head, coneSgn_slot h]
    by_cases hj : j' = j
    · subst hj
      simp [conePot, aVertex_ne_bVertex]
    · simp [conePot, aVertex_ne_bVertex, bVertex_inj_iff, hj]
  · intro e
    obtain ⟨i, j', rfl⟩ := exists_slot e
    rw [coneSgn_slot h]
    by_cases hj : j' = j
    · subst hj
      exact Or.inl (by simpa using depth_le d.length i j')
    · exact Or.inr (by simp [hj])

/-- **The divisor of the cone march.**  It moves the chip at `aVertex i` to
path position `depth` on `slot i j`, for each `i`. -/
theorem prin_coneScript (h : IsK33Core d.core) (hrep : RepGen d) (j : Fin 3) :
    prin d.graph (coneScript d j) =
      ∑ i : Fin 3, (one_chip (G := d.graph) (d.pathAt (slot i j) (depth d.length j)) -
        one_chip (G := d.graph) (d.coreVertex (aVertex i))) := by
  rw [coneScript, DegSpec.prin_ramp_eq (coneRamp h hrep j), sum_over_slots]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [coneSgn_slot h, ite_eq_left rfl, d.pathAt_zero, h.tail, zero_add,
      neg_one_smul, neg_sub]
  · intro j' _ hj'
    rw [coneSgn_slot h, ite_eq_right hj', zero_smul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Ramp

/-! ## The pencil and the core classes it reaches -/

section Pencil

variable {d : DegSpec 6 9}

/-- The degree-three pencil `a₀ + a₁ + a₂`. -/
def pencil (d : DegSpec 6 9) : CFDiv d.graph :=
  ∑ i : Fin 3, one_chip (G := d.graph) (d.coreVertex (aVertex i))

theorem deg_pencil (d : DegSpec 6 9) : deg (pencil d) = 3 := by
  rw [pencil, map_sum]
  simp [deg_one_chip]

/-- A sum of three chips is effective. -/
theorem effective_sum_one_chip (x : Fin 3 → d.graph.V) :
    effective (∑ i : Fin 3, one_chip (G := d.graph) (x i)) := by
  intro v
  rw [Finset.sum_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [one_chip]
  split_ifs <;> norm_num

/-- A sum of three chips has a chip at each of its summands. -/
theorem one_le_sum_one_chip (x : Fin 3 → d.graph.V) (i₀ : Fin 3) :
    1 ≤ (∑ i : Fin 3, one_chip (G := d.graph) (x i)) (x i₀) := by
  rw [Finset.sum_apply]
  calc (1 : ℤ) = one_chip (G := d.graph) (x i₀) (x i₀) := by simp [one_chip]
    _ ≤ ∑ i : Fin 3, one_chip (G := d.graph) (x i) (x i₀) := by
        refine Finset.single_le_sum (f := fun i => one_chip (G := d.graph) (x i) (x i₀))
          (fun i _ => ?_) (Finset.mem_univ i₀)
        simp only [one_chip]
        split_ifs <;> norm_num

/-- An explicit script realizing an effective representative with a chip at
`q` shows that `D` reaches `q`. -/
theorem reaches_of_script (D : CFDiv d.graph) (script : firing_script d.graph)
    (q : d.graph.V) (hEffective : effective (D + prin d.graph script))
    (hChip : 1 ≤ (D + prin d.graph script) q) :
    StrongSeparator.Reaches d.graph D q := by
  refine StrongSeparator.reaches_of_effective_representative ?_ hEffective hChip
  unfold linear_equiv
  rw [principal_iff_eq_prin]
  exact ⟨script, by abel⟩

/-- After the cone march into `bVertex j`, the pencil is the sum of the three
chips at depth `depth` on the slots into `bVertex j`. -/
theorem pencil_add_prin_coneScript (h : IsK33Core d.core) (hrep : RepGen d)
    (j : Fin 3) :
    pencil d + prin d.graph (coneScript d j) =
      ∑ i : Fin 3, one_chip (G := d.graph) (d.pathAt (slot i j) (depth d.length j)) := by
  rw [prin_coneScript h hrep, pencil, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => add_sub_cancel _ _

theorem reaches_aVertex (i : Fin 3) :
    StrongSeparator.Reaches d.graph (pencil d) (d.coreVertex (aVertex i)) := by
  refine reaches_of_script (pencil d) 0 _ ?_ ?_
  · rw [map_zero, add_zero]
    exact effective_sum_one_chip _
  · rw [map_zero, add_zero]
    exact one_le_sum_one_chip (fun i => d.coreVertex (aVertex i)) i

theorem reaches_bVertex (h : IsK33Core d.core) (hrep : RepGen d) (j : Fin 3) :
    StrongSeparator.Reaches d.graph (pencil d) (d.coreVertex (bVertex j)) := by
  refine reaches_of_script (pencil d) (coneScript d j) _ ?_ ?_
  · rw [pencil_add_prin_coneScript h hrep]
    exact effective_sum_one_chip _
  · obtain ⟨i₀, hi₀⟩ := exists_depth_eq d.length j
    have hAt : d.pathAt (slot i₀ j) (depth d.length j) = d.coreVertex (bVertex j) := by
      rw [d.pathAt_length (le_of_eq hi₀), h.head]
    rw [pencil_add_prin_coneScript h hrep, ← hAt]
    exact one_le_sum_one_chip
      (fun i => d.pathAt (slot i j) (depth d.length j)) i₀

/-- Every closed-orthant face of `K₃,₃` whose `rep` is generated by its
vanishing slots carries a degree-three rank-one divisor. -/
theorem bnExists_one_three (h : IsK33Core d.core) (hrep : RepGen d) :
    BNExists d.graph 1 3 := by
  refine LowGenus.GenusFourRow097Closed.bnExists_of_reaches_coreVertices d
    h.connected (pencil d) 3 (deg_pencil d) ?_
  intro v
  rcases aVertex_or_bVertex v with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact reaches_aVertex i
  · exact reaches_bVertex h hrep j

end Pencil

/-! ## The closed-orthant obligation -/

/-- The face's `rep` is the `compFold` of its vanishing slots. -/
theorem repGen_faceSpec (length : Fin 9 → ℕ)
    (hForest : IsForest row099Core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy row099Core (zeroSlots length)) :
    RepGen (faceSpec row099Core (by norm_num) length hForest hNotLoopy) :=
  fun u v hRep => (compFold_iff row099Core (zeroSlots length) u v).mp hRep

/-- **Closed-face degree-three pencil for public atlas row 099**, in the
statement of `AtanasovRanganathan.GenusFourGeneratedRows.row099_closed`: every
subdivision and every equal-genus contraction of `K₃,₃` carries a
degree-three rank-one divisor. -/
theorem row099_closed (length : Fin 9 → ℕ)
    (hForest : IsForest row099Core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy row099Core (zeroSlots length)) :
    BNExists (faceSpec row099Core (by norm_num) length hForest hNotLoopy).graph 1 3 :=
  bnExists_one_three isK33Core_row099 (repGen_faceSpec length hForest hNotLoopy)

end AtanasovRanganathan.GenusFourRow099Closed
