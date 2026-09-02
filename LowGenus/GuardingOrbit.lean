import LowGenus.GenusFiveClosedOrbit
import LowGenus.GuardingSet
import Utilities.Subdivision.DegenerateCanonical
import Utilities.Subdivision.DegenerateRelabelingReaches

/-!
# Guarding sets up to a core symmetry

A `Guarding.GuardingSet` asks for a picture at **every** chip-free core vertex.
Read the finished rows and most of those pictures are the same picture: rows
01, 04 and 13 have a *single* orbit of chip-free vertices under the core
automorphisms that fix their chip weight, and rows 02, 03 and 07 have two.  The
files nevertheless write every one of them out in full.

`OrbitGuard` is the same obligation with the redundancy removed: a chip weight,
one distinguished representative `base v` per chip-free vertex `v`, a core
symmetry carrying `base v` to `v`, and the guard at the representatives only.
`OrbitGuard.closedConstruction` puts the row together.

## What makes the transport work

`ClosedOrbit.relabeling` is a `DegSpec.Relabeling` between the face at
`length` and the face at `targetLength g length`, and
`DegSpec.Relabeling.reaches_iff` transports `StrongSeparator.Reaches` across
it.  Two bookkeeping facts complete the picture: the relabeling sends a
contracted core class to the class of its image
(`ClosedOrbit.vertexEquiv_relabeling_coreVertex`), and it sends a core-supported
divisor to the core-supported divisor of the reindexed weight
(`DegSpec.Relabeling.mapDiv_coreClassDivisor`), which for a symmetry-invariant
weight is the same weight.

## The kernel-reduction hazard, stated precisely

`CoreSymmetry.vertexPerm` and `slotPerm` applied **forward** reduce under any
construction, including `CoreSymmetry.ofMaps` — `ofMaps_vertexPerm` and
`ofMaps_slotPerm` (`Utilities/Subdivision/CoreSymmetry.lean:121,128`) are
proved `:= rfl`.  What does *not* reduce is `Equiv.symm`, and it enters through
`CoreSymmetry.reindexLength` (`:155`), hence through
`ClosedOrbit.targetLength`.  A row supplying its symmetries must therefore give
each permutation an **explicit inverse** — that is what
`CoreSymmetry.ofInverses` is for — and the test that detects a regression is a
`targetLength` reduction, not a `vertexPerm` one.  The generic form is
`CoreSymmetry.reindexLength_ofInverses`; the concrete form is the first of the
two `example`s at the foot of this file.

## Degree

The structure carries its degree as a parameter rather than hard-wiring four.
`closedConstruction` is stated at degree four because
`ClosedSubdivisionDharConstruction` is; the genus-four rows need the same
structure at degree three, and that exit can be added without touching
anything here.
-/

namespace AtanasovRanganathan.Guarding

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.CoreOrbitReduction
open Configurations
open AtanasovRanganathan.ClosedOrbit

variable {n p : ℕ}

/-! ## A chip anywhere in the class is enough

The bare-`DegSpec` twin of `Guarding.GuardingSet.classChip_reaches`, which is
stated for a `GuardingSet` and so is unavailable to a structure that does not
build one. -/

theorem reaches_coreClassDivisor_of_one_le (d : DegSpec n p) (chips : Fin n → ℤ)
    (hnn : ∀ v : Fin n, 0 ≤ chips v) {v : Fin n}
    (hClass : 1 ≤ d.coreClassDivisor chips (d.coreVertex v)) :
    Reaches d.graph (d.coreClassDivisor chips) (d.coreVertex v) :=
  reaches_of_effective_representative
    (linear_equiv.refl d.graph (d.coreClassDivisor chips))
    (d.coreClassDivisor_effective chips hnn) hClass

/-! ## Transporting one guard along a core symmetry -/

/-- Two faces at equal length vectors carry the same guard.  The two forest
and looplessness proofs are proofs of the same propositions, so the faces are
definitionally equal once the lengths are identified. -/
private theorem reaches_faceSpec_congr {core : Core n p} (core_nonempty : 0 < n)
    {l₁ l₂ : Fin p → ℕ} (h : l₁ = l₂)
    (f₁ : IsForest core (zeroSlots l₁)) (nl₁ : ¬ IsLoopy core (zeroSlots l₁))
    (f₂ : IsForest core (zeroSlots l₂)) (nl₂ : ¬ IsLoopy core (zeroSlots l₂))
    (chips : Fin n → ℤ) (u : Fin n)
    (H : Reaches (faceSpec core core_nonempty l₁ f₁ nl₁).graph
      ((faceSpec core core_nonempty l₁ f₁ nl₁).coreClassDivisor chips)
      ((faceSpec core core_nonempty l₁ f₁ nl₁).coreVertex u)) :
    Reaches (faceSpec core core_nonempty l₂ f₂ nl₂).graph
      ((faceSpec core core_nonempty l₂ f₂ nl₂).coreClassDivisor chips)
      ((faceSpec core core_nonempty l₂ f₂ nl₂).coreVertex u) := by
  subst h
  exact H

/-- **Guard transport.**  A core symmetry fixing the chip weight moves a proved
guard from a core vertex to its image, one face at a time. -/
theorem faceGuard_map {core : Core n p} (core_nonempty : 0 < n)
    (g : CoreSymmetry core) (chips : Fin n → ℤ)
    (hchips : ∀ v : Fin n, chips (g.vertexPerm v) = chips v) (u : Fin n)
    (length : Fin p → ℕ) (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length))
    (hguard : Reaches (faceSpec core core_nonempty length forest not_loopy).graph
      ((faceSpec core core_nonempty length forest not_loopy).coreClassDivisor chips)
      ((faceSpec core core_nonempty length forest not_loopy).coreVertex u)) :
    Reaches (faceSpec core core_nonempty (targetLength g length)
        (forest_target g length forest)
        (not_loopy_target g length not_loopy)).graph
      ((faceSpec core core_nonempty (targetLength g length)
        (forest_target g length forest)
        (not_loopy_target g length not_loopy)).coreClassDivisor chips)
      ((faceSpec core core_nonempty (targetLength g length)
        (forest_target g length forest)
        (not_loopy_target g length not_loopy)).coreVertex (g.vertexPerm u)) := by
  have hmap := DegSpec.Relabeling.mapDiv_coreClassDivisor
    (faceSpec core core_nonempty length forest not_loopy)
    (faceSpec core core_nonempty (targetLength g length)
      (forest_target g length forest) (not_loopy_target g length not_loopy))
    (relabeling g length core_nonempty forest not_loopy) g.vertexPerm
    (vertexEquiv_relabeling_coreVertex g length core_nonempty forest not_loopy)
    chips chips (fun w => (hchips w).symm)
  have hvertex := vertexEquiv_relabeling_coreVertex g length core_nonempty forest
    not_loopy u
  have htransport := (DegSpec.Relabeling.reaches_iff _ _
    (relabeling g length core_nonempty forest not_loopy)
    ((faceSpec core core_nonempty length forest not_loopy).coreClassDivisor chips)
    ((faceSpec core core_nonempty length forest not_loopy).coreVertex u)).mpr
    hguard
  rw [hmap, hvertex] at htransport
  exact htransport

/-! ## Guarding sets given one representative per orbit -/

/-- **A guarding set up to a core symmetry.**

`guard_base` is the only per-graph content: the picture at one representative
of each orbit of chip-free vertices.  Everything else is a finite table that a
concrete row discharges by `decide`. -/
structure OrbitGuard (core : Core n p) (core_nonempty : 0 < n) (degree : ℤ) where
  /-- The core-supported chip assignment. -/
  chips : Fin n → ℤ
  /-- Chips are chips. -/
  chips_nonneg : ∀ v : Fin n, 0 ≤ chips v
  /-- The displayed pencil's degree. -/
  chips_deg : ∑ v : Fin n, chips v = degree
  /-- The orbit representative a chip-free vertex is guarded from. -/
  base : Fin n → Fin n
  /-- A symmetry carrying `base v` to `v`. -/
  mover : Fin n → CoreSymmetry core
  /-- Every mover fixes the chip weight. -/
  mover_chips : ∀ v u : Fin n, chips ((mover v).vertexPerm u) = chips u
  /-- Every mover really lands on its vertex. -/
  mover_hits : ∀ v : Fin n, chips v = 0 → (mover v).vertexPerm (base v) = v
  /-- The guard, needed only at the representatives. -/
  guard_base : ∀ v : Fin n, chips v = 0 → ∀ (length : Fin p → ℕ)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)),
    Reaches (faceSpec core core_nonempty length forest not_loopy).graph
      ((faceSpec core core_nonempty length forest not_loopy).coreClassDivisor chips)
      ((faceSpec core core_nonempty length forest not_loopy).coreVertex (base v))

namespace OrbitGuard

variable {core : Core n p} {core_nonempty : 0 < n} {degree : ℤ}
variable (G : OrbitGuard core core_nonempty degree)

/-- **Every contracted core class is reached.**  Chip vertices are free, and a
chip-free vertex is transported from its orbit representative. -/
theorem reaches (length : Fin p → ℕ) (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)) (v : Fin n) :
    Reaches (faceSpec core core_nonempty length forest not_loopy).graph
      ((faceSpec core core_nonempty length forest not_loopy).coreClassDivisor
        G.chips)
      ((faceSpec core core_nonempty length forest not_loopy).coreVertex v) := by
  rcases eq_or_lt_of_le (G.chips_nonneg v) with hzero | hpos
  · -- chip free: move the guard from the orbit representative
    set g := G.mover v with hg
    -- the length vector whose image under `g` is the given one
    set l₀ : Fin p → ℕ := fun e => length (g.slotPerm e) with hl₀
    have hback : targetLength g l₀ = length := by
      funext e
      simp [targetLength, CoreSymmetry.reindexLength, hl₀]
    have forest₀ : IsForest core (zeroSlots l₀) :=
      (isForest_iff g l₀).1 (by rw [hback]; exact forest)
    have not_loopy₀ : ¬ IsLoopy core (zeroSlots l₀) := by
      intro hloopy
      exact not_loopy (by rw [← hback]; exact (isLoopy_iff g l₀).2 hloopy)
    have hmoved := faceGuard_map core_nonempty g G.chips (G.mover_chips v)
      (G.base v) l₀ forest₀ not_loopy₀
      (G.guard_base v hzero.symm l₀ forest₀ not_loopy₀)
    rw [G.mover_hits v hzero.symm] at hmoved
    exact reaches_faceSpec_congr core_nonempty hback _ _ forest not_loopy
      G.chips v hmoved
  · -- carries a chip
    refine reaches_coreClassDivisor_of_one_le _ G.chips G.chips_nonneg ?_
    exact DegSpec.one_le_coreClassDivisor_of_chip _ G.chips G.chips_nonneg
      (by omega)

/-- **The main theorem.**  A degree-four orbit guard closes the row on the
whole nonloopy forest orthant. -/
theorem closedConstruction (G : OrbitGuard core core_nonempty 4)
    (hConnected : core.Connected) :
    ClosedSubdivisionDharConstruction core core_nonempty :=
  ClosedSubdivisionDharConstruction.ofReachesFaceClasses core_nonempty hConnected
    (fun d => d.coreClassDivisor G.chips)
    (fun d => d.coreClassDivisor_effective G.chips G.chips_nonneg)
    (fun d => by rw [d.deg_coreClassDivisor, G.chips_deg])
    (fun length forest not_loopy center => G.reaches length forest not_loopy center)

end OrbitGuard

/-! ## Guards that may assume their class is chip free -/

/-- **A guarding set from a class-free guard.**

`GuardingSet.guard` must be proved at every chip-free core vertex and on every
face — including the faces where the vertex's own contracted class has
swallowed one of the chips.  Those faces need no picture at all: the class
divisor is then already positive there, and `classChip_reaches` finishes.  A
row can therefore assume the case away, which is what kills the collapsed-arm
branches of a `transferWeight`-style allocation.

This is an **additive** constructor.  `GuardingSet.guard` keeps its type, so
the downstream rows that build the
field directly are untouched; a row opts in by using this constructor
instead. -/
def ofClassFreeGuard {core : Core n p} (chips : Fin n → ℤ)
    (chips_nonneg : ∀ v : Fin n, 0 ≤ chips v)
    (chips_deg : ∑ v : Fin n, chips v = 4)
    (guard' : ∀ v : Fin n, chips v = 0 → ∀ d : DegSpec n p, d.core = core →
      (∀ x y : Fin n,
        d.rep x = d.rep y ↔ ReachIn core (zeroSlots d.length) x y) →
      (∀ u : Fin n, d.rep u = d.rep v → chips u = 0) →
      Reaches d.graph (d.coreClassDivisor chips) (d.coreVertex v)) :
    GuardingSet core where
  chips := chips
  chips_nonneg := chips_nonneg
  chips_deg := chips_deg
  guard := by
    intro v hv d hCore hRep
    by_cases hfree : ∀ u : Fin n, d.rep u = d.rep v → chips u = 0
    · exact guard' v hv d hCore hRep hfree
    · push Not at hfree
      obtain ⟨u, hu, hune⟩ := hfree
      have hchip : 1 ≤ chips u := by
        have := chips_nonneg u
        omega
      have hsum := d.one_le_classSum_of_chip chips chips_nonneg hchip
      refine reaches_coreClassDivisor_of_one_le d chips chips_nonneg ?_
      rw [d.coreClassDivisor_coreVertex, ← hu]
      exact hsum

/-! ## Reading a permutation off a list

Every genus-five row that supplies symmetries needs the same three table
readers.  They live here so the rows do not each carry a copy. -/

/-- A vertex permutation of an eight-vertex core, read off a list. -/
def vertexTable (data : List (Fin 8)) : Fin 8 → Fin 8 := fun i => data.getD i.val 0

/-- A slot permutation of a twelve-slot core, read off a list. -/
def slotTable (data : List (Fin 12)) : Fin 12 → Fin 12 := fun i => data.getD i.val 0

/-- A per-slot orientation-reversal flag, read off a list. -/
def flagTable (data : List Bool) : Fin 12 → Bool := fun i => data.getD i.val false

/-! ## Smoke tests

Two things have to keep working, and neither is visible from the statements
above.  Both are `example`s, so they cost a compile and export nothing. -/

section SmokeTest

open GenusFiveCoreAtlas
open Certificate.DegenerateSpec.DegSpec

/-- The involution `(0 1)(4 5)` of row 13's core, built with explicit
inverses. -/
private def row13Swap : CoreSymmetry row13Core :=
  CoreSymmetry.ofInverses row13Core
    (vertexTable [1, 0, 2, 3, 5, 4, 6, 7]) (vertexTable [1, 0, 2, 3, 5, 4, 6, 7])
    (slotTable [1, 0, 3, 2, 4, 6, 5, 8, 7, 9, 11, 10])
    (slotTable [1, 0, 3, 2, 4, 6, 5, 8, 7, 9, 11, 10])
    (flagTable [true, true, true, true, false, true, true, true, true,
      false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Smoke test 1: the kernel-reduction hazard.**  `targetLength` must reduce
definitionally on a *concrete* symmetry, or every closed-orthant orbit argument
silently stops being decidable.  The hazard is `Equiv.symm`, not forward
`vertexPerm`: a test phrased on `vertexPerm` passes even when the symmetry is
built the wrong way.  This one does not. -/
example (length : Fin 12 → ℕ) (e : Fin 12) :
    targetLength row13Swap length e =
      length (slotTable [1, 0, 3, 2, 4, 6, 5, 8, 7, 9, 11, 10] e) := rfl

/-- Row 13's `K_A + K_B` weight: one chip on each of the four core vertices
that are not an endpoint of a connector. -/
private def row13Chips : Fin 8 → ℤ :=
  fun v => if v = 2 ∨ v = 3 ∨ v = 6 ∨ v = 7 then 1 else 0

private theorem row13_cubic : row13Core.Cubic := by
  intro v; fin_cases v <;> decide

/-- **Smoke test 2: `C1` applies to a real row.**  On *every* nonloopy forest
face of row 13, `K_A + K_B` and the four connector-endpoint chips — the two
degree-four core weights the `2+2` rows choose between — have equal rank.  The
lengths are quantified, so this is the whole closed orthant, not the unit
metric. -/
example (length : Fin 12 → ℕ)
    (forest : IsForest row13Core (zeroSlots length))
    (not_loopy : ¬ IsLoopy row13Core (zeroSlots length)) :
    rank (faceSpec row13Core (by norm_num) length forest not_loopy).graph
        ((faceSpec row13Core (by norm_num) length forest not_loopy).coreClassDivisor
          row13Chips)
      = rank (faceSpec row13Core (by norm_num) length forest not_loopy).graph
        ((faceSpec row13Core (by norm_num) length forest not_loopy).coreClassDivisor
          fun v => 1 - row13Chips v) :=
  by
  set d := faceSpec row13Core (by norm_num) length forest not_loopy with hd
  exact d.rank_coreClassDivisor_eq_complement row13_cubic (mem_zeroSlots length)
    (fun x y => compFold_iff row13Core (zeroSlots length) x y)
    (d.graph_connected_of_coreConnected row13_connected) row13Chips (by decide)

end SmokeTest

end AtanasovRanganathan.Guarding
