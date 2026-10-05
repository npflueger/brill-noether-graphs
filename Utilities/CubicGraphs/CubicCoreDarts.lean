module

public import Utilities.CubicGraphs.WhiteheadConnectivity
public import Utilities.Subdivision.CubicCore
public import Utilities.Subdivision.SubdivisionConnectivity

@[expose] public section

/-!
# A cubic core as a dart graph

A connected cubic core (`Core.Cubic`, from `Utilities.Subdivision.CubicCore`)
is an ordered presentation of a trivalent graph; the Whitehead moves of
`Utilities.CubicGraphs.CubicDarts` act on cubic dart graphs, including loops.
This adapter retains each literal core slot and both of its ends.
Connectedness is derived from the core's cut condition, not added as a second
hypothesis. A loop still gives two distinct darts at one vertex.

This identifies the combinatorial *input type* of a core. It does not identify
the stable rows of a Draisma--Vargas gluing datum with that type, or prove that
it is preserved when a wall is crossed; those are separate questions about the
Draisma--Vargas construction.
-/

namespace DraismaVargas.LocalCases.CubicCoreDarts

open DraismaVargas.Infrastructure.CubicDarts
open CubicDartGraph
open Utilities.Certificate ExplicitPotential
open Finset

variable {n p : ℕ}

/-- Keep the slot label, exchanging its two ends. -/
def opposite (dart : Fin p × Bool) : Fin p × Bool := (dart.1, !dart.2)

/-- False is the tail dart; true is the head dart. -/
def vertex (core : Core n p) (dart : Fin p × Bool) : Fin n :=
  if dart.2 then core.head dart.1 else core.tail dart.1

@[simp] theorem vertex_tail (core : Core n p) (edge : Fin p) :
    vertex core (edge, false) = core.tail edge := rfl

@[simp] theorem vertex_head (core : Core n p) (edge : Fin p) :
    vertex core (edge, true) = core.head edge := rfl

@[simp] theorem opposite_opposite (dart : Fin p × Bool) :
    opposite (opposite dart) = dart := by simp [opposite]

theorem opposite_ne (dart : Fin p × Bool) : opposite dart ≠ dart := by
  rcases dart with ⟨edge, side⟩
  cases side <;> simp [opposite]

/-- Occurrence-sensitive incidence degree is precisely the dart fibre count. -/
theorem card_fibre (core : Core n p) (v : Fin n) :
    (univ.filter (fun dart : Fin p × Bool ↦ vertex core dart = v)).card =
      core.incidenceDegree v := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Core.incidenceDegree]
  apply Finset.sum_congr rfl
  intro edge _
  rw [Fintype.sum_bool]
  simp [vertex, add_comm]

/-- The core cut certificate supplies every dart path, including across
bridges and parallel edges. No simple-graph quotient is used. -/
theorem connected (core : Core n p) (hConnected : core.Connected)
    (first last : Fin p × Bool) :
    Relation.EqvGen (DartRel opposite (vertex core)) first last := by
  classical
  let P : Fin n → Prop := fun v ↦ ∃ dart, vertex core dart = v ∧
    Relation.EqvGen (DartRel opposite (vertex core)) first dart
  have hEdge (edge : Fin p) : P (core.tail edge) ↔ P (core.head edge) := by
    constructor
    · rintro ⟨dart, hVertex, hReach⟩
      refine ⟨(edge, true), rfl, DartRel.trans hReach ?_⟩
      exact DartRel.trans (DartRel.of_vert (q := (edge, false)) hVertex)
        (DartRel.of_op (show opposite (edge, false) = (edge, true) from rfl))
    · rintro ⟨dart, hVertex, hReach⟩
      refine ⟨(edge, false), rfl, DartRel.trans hReach ?_⟩
      exact DartRel.trans (DartRel.of_vert (q := (edge, true)) hVertex)
        (DartRel.of_op (show opposite (edge, true) = (edge, false) from rfl))
  have hFirst : P (vertex core first) := ⟨first, rfl, .refl _⟩
  have hLast : P (vertex core last) := by
    by_contra hNot
    obtain ⟨edge, hCross | hCross⟩ := hConnected (univ.filter P)
      ⟨vertex core first, vertex core last, by simpa using hFirst, by simpa using hNot⟩
    · have hTail : P (core.tail edge) := by simpa using hCross.1
      have hHead : ¬ P (core.head edge) := by simpa using hCross.2
      exact hHead ((hEdge edge).mp hTail)
    · have hHead : P (core.head edge) := by simpa using hCross.1
      have hTail : ¬ P (core.tail edge) := by simpa using hCross.2
      exact hTail ((hEdge edge).mpr hHead)
  obtain ⟨dart, hVertex, hReach⟩ := hLast
  exact DartRel.trans hReach (DartRel.of_vert hVertex)

/-- The adapter from a connected cubic core to a cubic dart graph. -/
def ofCore (core : Core n p) (hCubic : core.Cubic) (hConnected : core.Connected) :
    CubicDartGraph (Fin p × Bool) (Fin n) where
  op := opposite
  vert := vertex core
  op_invol := opposite_opposite
  op_ne := opposite_ne
  card_fibre v := (card_fibre core v).trans (hCubic v)
  conn := connected core hConnected

@[simp] theorem edgeCard_ofCore (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) :
    (ofCore core hCubic hConnected).edgeCard = p := by
  simp [CubicDartGraph.edgeCard]

/-- The dart genus is the genus `p + 1 - n` of the core. -/
theorem genus_ofCore (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) :
    (ofCore core hCubic hConnected).genus = p + 1 - n := by
  have h := (ofCore core hCubic hConnected).euler
  rw [edgeCard_ofCore, Fintype.card_fin] at h
  omega

/-- The adapter retains loops rather than deleting or splitting them. -/
theorem isLoopDart_iff (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) (dart : Fin p × Bool) :
    (ofCore core hCubic hConnected).IsLoopDart dart ↔
      core.tail dart.1 = core.head dart.1 := by
  rcases dart with ⟨edge, side⟩
  cases side <;> simp [CubicDartGraph.IsLoopDart, ofCore, opposite, vertex, eq_comm]

/-- The uniform linkage theorem applies to every connected cubic core of genus
at least two. The resulting path starts on its literal slot-end darts. -/
theorem reaches_caterpillar_ofCore (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) (hGenus : 2 ≤ p + 1 - n) :
    ReachesIso (ofCore core hCubic hConnected) (caterpillarDarts (p + 1 - n)) := by
  have h := reaches_caterpillar (ofCore core hCubic hConnected)
    (by rwa [genus_ofCore])
  rw [genus_ofCore core hCubic hConnected] at h
  exact h

/-! Literal loop-bearing input: the two loops and bridge are kept, with
genus two. This core is deliberately not loopless. -/

private def dumbbellCore : Core 2 3 where
  tail := ![0, 0, 1]
  head := ![0, 1, 1]

private theorem dumbbellCore_cubic : dumbbellCore.Cubic := by
  unfold Core.Cubic
  decide

private theorem dumbbellCore_connected : dumbbellCore.Connected :=
  (Core.connectedCheck_eq_true_iff dumbbellCore).mp (by decide)

example : (ofCore dumbbellCore dumbbellCore_cubic dumbbellCore_connected).genus = 2 :=
  genus_ofCore dumbbellCore dumbbellCore_cubic dumbbellCore_connected

example : (ofCore dumbbellCore dumbbellCore_cubic dumbbellCore_connected).IsLoopDart
    (0, false) := by
  rw [isLoopDart_iff]
  rfl

end DraismaVargas.LocalCases.CubicCoreDarts
