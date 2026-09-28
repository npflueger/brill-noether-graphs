import DraismaVargas.LocalCases.NonTrivalentValencyTwoTracks
import DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleTracks
import DraismaVargas.LocalCases.NonTrivalentValencyFourTracks

/-!
# The incoming pairing at a Part II wall, and what a Whitehead move can prescribe

Source: Vargas, Part II (arXiv:2609.09109), §5.1 (combinatorial setup and local
determinants): the labelling convention at a non-trivalent wall -- the
contracting edge `h_1` of the incoming type `H` has two trivalent ends `A_1`,
`A_2`, and the four edges `h_2 .. h_5` of `H_0` at the four-valent `A` are
distributed two at each end -- and the three combinatorial resolutions
`H_{2,3}`, `H_{2,4}`, `H_{2,5}` of `H_0` (Types I, II and III).  The model of a
type change is the Whitehead move `CubicDarts.CubicDartGraph.move` of the
tracked ambient graph (`OuterWalk.TypeChangeLink.tracks`).

The per-valency tracking modules state their move hypotheses as named
conditions: (H-I/II) is `NonTrivalentValencyThreeSimpleTracks.PrescribedSimpleMove`,
(H-II) is `NonTrivalentValencyTwoTracks.PrescribedMergedMove`, (H-III) is
`NonTrivalentValencyThreeTracks.PrescribedDoubledMove`, and (H-IV) is
`NonTrivalentValencyFourTracks.PrescribedPairingMove`; the two valency-two leaf
cases have `NonTrivalentValencyTwoSplitTracks.PrescribedSplitMove` and
`NonTrivalentValencyTwoBaseOneTracks.PrescribedBaseOneMove`.  Each opens with an
orientation clause and continues with a pair clause naming the moved star.

## What is proved

Everything here is valency-agnostic and needs no wall star, no anchor and no
no-return hypothesis: it is combinatorics of one Whitehead move `m` read through
the incoming tracking `wd.tracks`.

* `move_vert_base_iff`, `mem_movedStar_iff`, `right_mem_movedStar`: the star of
  `graph.vert m.base` in `graph.move m` is `{m.base, x, m.right}` with `x` the
  third dart of the old star `{m.base, m.left, x}`: the move keeps `m.base` and
  `x` at that end and brings `m.right` over from the other end.
* `vert_of_movedStar_eq_pair`: **whatever pair of darts a move places together
  with `m.base`, one of them sits at `graph.vert m.base` and the other at
  `graph.vert (graph.op m.base)`.**
* `baseDart`, `opBaseDart`: the two darts of the incoming cover's stable graph
  that the tracking sends to `m.base` and `graph.op m.base` -- the two ends of
  the vanishing row `label m.base` (`row_baseDart`), at two distinct branch
  vertices (`vtx_baseDart`, `vtx_opBaseDart`, `vertex_baseDart_ne`).  Every
  per-valency tracking module defines its own `leftEnd`/`rightEnd`/`facetDartLeft`
  under its own no-return input; under the orientation clause common to the
  (H-*) conditions they are `baseDart`/`opBaseDart`
  (`baseDart_eq_facetDartLeft_three`, `_two`, `_four` and their `opBaseDart`
  companions).
* `vertex_of_movedStar_eq_pair`: **the incoming pairing is the partition of the
  four surviving rows by the end of `h_1` they sit at, and every prescribed
  pair straddles the two ends** -- the two darts named in the second clause of
  any (H-*) condition sit one at `baseDart`'s branch vertex and one at
  `opBaseDart`'s, in one of the two orders.
* `exists_movedStar_darts`: the positive form.  The move *does* place together
  with `m.base` the tracked images of one dart at each end of `h_1`, other than
  the two darts of `h_1` itself; so a **row-level** (H-*) clause (the darts'
  *rows* are the prescribed pair) is always dischargeable by the dispatcher
  once the candidate's pair is the pair of rows the move names.
* `label_dart_of_row`: the only fact the star counts extract from the
  survivor clause of (H-*) is the label of the tracked dart, and it follows from
  the row equality `first.2.1.stablePath = (selectedLift …).stablePath` alone.
  This is why the (H-*) conditions of the valency-three and valency-two tracking
  modules state their survivor clause at row level.
* Per valency, the **necessity of the separation predicates at the occurrence
  level**: `separated_or_swapped_of_prescribedDoubledMove` ((H-III)),
  `separated_or_swapped_of_prescribedSimpleMove` ((H-I/II)),
  `separated_or_swapped_of_prescribedMergedMove` ((H-II)),
  `separated_or_swapped_of_prescribedPairingMove` ((H-IV)): the
  *occurrence-level* survivor clause implies the file's `…Separated` predicate
  up to the order of the pair.  Together with the incoming cover's geometry this
  pins exactly where that clause can and cannot be satisfied -- and hence why
  the valency-three and valency-two conditions are stated at row level, where
  separation is automatic (`vertex_of_movedStar_eq_pair`).  The valency-four
  condition (H-IV) states the occurrence-level clause, so its lemma reads
  `hPres : PrescribedPairingMove …`; the other three take the occurrence-level
  clauses as explicit hypotheses.
* `PrescribedMergedMoveRow`, `prescribedMergedMoveRow_of_prescribedMergedMove`,
  `prescribedMergedMoveRow_spec`: the row-level shape of (H-II).
  `PrescribedMergedMoveRow` is `NonTrivalentValencyTwoTracks.PrescribedMergedMove`
  itself, so the first witness is the identity; `prescribedMergedMoveRow_spec`
  is the fact the count uses.

## What is NOT proved -- and what is deliberately not claimed

* Nothing here says which of the two ends a given survivor sits at: that is the
  incoming cover's geometry, not a consequence of the move.
* The pass-through phenomenon (a survivor whose row reaches an end of `h_1`
  through an occurrence over the contracted target edge, so that the
  occurrence-level clause is unsatisfiable) comes from the source's local
  ramification count; it is not formalised here.
* No structure is introduced.  `PrescribedMergedMoveRow` is a `Prop` with the
  relative witness `prescribedMergedMoveRow_of_prescribedMergedMove`.

## Consumers

The move-to-type dispatchers that discharge the `link` binder of
`OuterWalk.coneEntry_of_reaches`, through the four `separated_or_swapped_*`
lemmas and `exists_movedStar_darts`.  The valency-four dispatcher
(`NonTrivalentValencyFourDispatcher`) calls `exists_movedStar_darts` and
`baseDart_eq_facetDartLeft_four` / `opBaseDart_eq_facetDartRight_four` directly
to close `link` at every four-valent wall; the valency-three and valency-two
cases use this module through their tracking and star-count modules.
-/

namespace DraismaVargas.LocalCases.IncomingPairing

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

/-! ## 1.  The star of `graph.vert m.base` after the move -/

section Darts

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {G : CubicDartGraph D V} (m : G.MoveData)

/-- A dart sits at `G.vert m.base` after the move iff it sat there before and is
not `m.left`, or it is `m.right`. -/
theorem move_vert_base_iff (d : D) :
    (G.move m).vert d = G.vert m.base ↔
      (d ≠ m.left ∧ G.vert d = G.vert m.base) ∨ d = m.right := by
  classical
  by_cases hl : d = m.left
  · subst hl
    have h1 : (G.move m).vert m.left = G.vert (G.op m.base) := by
      show G.vert (m.perm m.left) = _
      rw [m.perm_left, m.right_vert]
    constructor
    · intro h
      exact absurd (h1.symm.trans h) m.nonloop
    · rintro (⟨h, -⟩ | h)
      · exact absurd rfl h
      · exact absurd h m.left_ne_right
  · by_cases hr : d = m.right
    · subst hr
      have h1 : (G.move m).vert m.right = G.vert m.base := by
        show G.vert (m.perm m.right) = _
        rw [m.perm_right, m.left_vert]
      exact ⟨fun _ ↦ Or.inr rfl, fun _ ↦ h1⟩
    · have h1 : (G.move m).vert d = G.vert d := by
        show G.vert (m.perm d) = _
        rw [m.perm_of_ne hl hr]
      rw [h1]
      constructor
      · intro h
        exact Or.inl ⟨hl, h⟩
      · rintro (⟨-, h⟩ | h)
        · exact h
        · exact absurd h hr

/-- Membership in the moved star of `graph.vert m.base` with `m.base` removed --
the finset every (H-*) condition names. -/
theorem mem_movedStar_iff (d : D) :
    d ∈ (Finset.univ.filter fun d ↦ (G.move m).vert d = G.vert m.base).erase m.base ↔
      d ≠ m.base ∧ ((d ≠ m.left ∧ G.vert d = G.vert m.base) ∨ d = m.right) := by
  rw [Finset.mem_erase, Finset.mem_filter, move_vert_base_iff]
  simp only [Finset.mem_univ, true_and]

/-- The dart brought over from the other end belongs to the moved star. -/
theorem right_mem_movedStar :
    m.right ∈ (Finset.univ.filter fun d ↦ (G.move m).vert d = G.vert m.base).erase m.base :=
  (mem_movedStar_iff m _).mpr ⟨m.base_ne_right.symm, Or.inr rfl⟩

/-- **The two darts a move places together with `m.base` sit at the two ends of
the contracted edge, one at each.** -/
theorem vert_of_movedStar_eq_pair {x y : D}
    (h : (Finset.univ.filter fun d ↦ (G.move m).vert d = G.vert m.base).erase m.base =
      {x, y}) :
    (G.vert x = G.vert m.base ∧ G.vert y = G.vert (G.op m.base)) ∨
      (G.vert x = G.vert (G.op m.base) ∧ G.vert y = G.vert m.base) := by
  classical
  obtain ⟨r, hr, hrb, hrl, -⟩ :=
    G.exists_third (x := G.vert m.base) rfl m.left_vert m.base_ne_left
  have hrr : r ≠ m.right := by
    intro hbad
    apply m.nonloop
    rw [← m.right_vert, ← hbad, hr]
  have hrmem : r ∈ ({x, y} : Finset D) := by
    rw [← h]
    exact (mem_movedStar_iff m r).mpr ⟨hrb, Or.inl ⟨hrl, hr⟩⟩
  have hright : m.right ∈ ({x, y} : Finset D) := by
    rw [← h]
    exact right_mem_movedStar m
  have hx : x ∈ ({x, y} : Finset D) := Finset.mem_insert_self x {y}
  have hy : y ∈ ({x, y} : Finset D) := Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  rw [← h] at hx hy
  rcases (mem_movedStar_iff m x).mp hx with ⟨-, ⟨-, hxv⟩ | hxr⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hright
    rcases hright with hrx | hry
    · exact absurd (m.right_vert.symm.trans ((congrArg G.vert hrx).trans hxv)) m.nonloop
    · exact Or.inl ⟨hxv, (congrArg G.vert hry).symm.trans m.right_vert⟩
  · subst hxr
    rcases (mem_movedStar_iff m y).mp hy with ⟨-, ⟨-, hyv⟩ | hyr⟩
    · exact Or.inr ⟨m.right_vert, hyv⟩
    · subst hyr
      simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at hrmem
      exact absurd hrmem hrr

end Darts

/-! ## 2.  The two ends of the vanishing row, read through the tracking -/

section Wall

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- The dart of the incoming cover's stable graph that the tracking sends to
`m.base`: the vanishing row's dart at the end the move calls `graph.vert m.base`. -/
def baseDart : StableSourceDarts.Dart wd.cover := wd.tracks.iso.dart.symm m.base

/-- The dart the tracking sends to `graph.op m.base`: the vanishing row's other
dart. -/
def opBaseDart : StableSourceDarts.Dart wd.cover := wd.tracks.iso.dart.symm (graph.op m.base)

@[simp] theorem dart_baseDart : wd.tracks.iso.dart (baseDart m wd) = m.base :=
  Equiv.apply_symm_apply _ _

@[simp] theorem dart_opBaseDart : wd.tracks.iso.dart (opBaseDart m wd) = graph.op m.base :=
  Equiv.apply_symm_apply _ _

/-- Both darts lie on the vanishing row, the chart row of `label m.base`. -/
theorem row_baseDart :
    wd.fullDim.labelling.row (StableSourceDarts.row wd.cover (baseDart m wd)) = label m.base := by
  have h := wd.tracks.row_map (baseDart m wd)
  rw [dart_baseDart] at h
  exact h.symm

theorem row_opBaseDart :
    wd.fullDim.labelling.row (StableSourceDarts.row wd.cover (opBaseDart m wd)) =
      label (graph.op m.base) := by
  have h := wd.tracks.row_map (opBaseDart m wd)
  rw [dart_opBaseDart] at h
  exact h.symm

theorem vtx_baseDart : wd.tracks.iso.vtx (baseDart m wd).1 = graph.vert m.base := by
  have h := wd.tracks.iso.vert_map (baseDart m wd)
  rw [dart_baseDart] at h
  exact h.symm

theorem vtx_opBaseDart :
    wd.tracks.iso.vtx (opBaseDart m wd).1 = graph.vert (graph.op m.base) := by
  have h := wd.tracks.iso.vert_map (opBaseDart m wd)
  rw [dart_opBaseDart] at h
  exact h.symm

theorem baseDart_ne_opBaseDart : baseDart m wd ≠ opBaseDart m wd := by
  intro h
  have h' := congrArg wd.tracks.iso.dart h
  rw [dart_baseDart, dart_opBaseDart] at h'
  exact graph.op_ne m.base h'.symm

/-- The two ends of the vanishing row are distinct branch vertices. -/
theorem vertex_baseDart_ne : (baseDart m wd).1 ≠ (opBaseDart m wd).1 := by
  intro h
  have h' := congrArg wd.tracks.iso.vtx h
  rw [vtx_baseDart, vtx_opBaseDart] at h'
  exact m.nonloop h'.symm

/-- **Every pair a move names straddles the two ends of the vanishing row.**
If the moved star of `graph.vert m.base` with `m.base` removed is the tracked
image of two darts `first`, `second` of the incoming cover (the second clause of
every (H-*) condition), then one of them sits at the branch vertex of
`baseDart` and the other at that of `opBaseDart`. -/
theorem vertex_of_movedStar_eq_pair (first second : StableSourceDarts.Dart wd.cover)
    (h : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    (first.1 = (baseDart m wd).1 ∧ second.1 = (opBaseDart m wd).1) ∨
      (first.1 = (opBaseDart m wd).1 ∧ second.1 = (baseDart m wd).1) := by
  have hv : ∀ d : StableSourceDarts.Dart wd.cover,
      graph.vert (wd.tracks.iso.dart d) = wd.tracks.iso.vtx d.1 :=
    fun d ↦ wd.tracks.iso.vert_map d
  have hinj := wd.tracks.iso.vtx.injective
  rcases vert_of_movedStar_eq_pair m h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hinj ((hv first).symm.trans (h1.trans (vtx_baseDart m wd).symm)),
      hinj ((hv second).symm.trans (h2.trans (vtx_opBaseDart m wd).symm))⟩
  · exact Or.inr ⟨hinj ((hv first).symm.trans (h1.trans (vtx_opBaseDart m wd).symm)),
      hinj ((hv second).symm.trans (h2.trans (vtx_baseDart m wd).symm))⟩

/-- **The positive form: the move places with `m.base` one dart from each end.**
There are darts `x` at `baseDart`'s branch vertex and `y` at `opBaseDart`'s, other
than the two darts of the vanishing row, whose tracked images are exactly the
moved star of `graph.vert m.base` with `m.base` removed.  This is the pair of rows
a row-level (H-*) clause must name. -/
theorem exists_movedStar_darts :
    ∃ x y : StableSourceDarts.Dart wd.cover,
      x.1 = (baseDart m wd).1 ∧ y.1 = (opBaseDart m wd).1 ∧
      x ≠ baseDart m wd ∧ y ≠ opBaseDart m wd ∧
      (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
        {wd.tracks.iso.dart x, wd.tracks.iso.dart y} := by
  classical
  obtain ⟨r, hr, hrb, hrl, hall⟩ :=
    graph.exists_third (x := graph.vert m.base) rfl m.left_vert m.base_ne_left
  have hv : ∀ d : StableSourceDarts.Dart wd.cover,
      graph.vert (wd.tracks.iso.dart d) = wd.tracks.iso.vtx d.1 :=
    fun d ↦ wd.tracks.iso.vert_map d
  have hinj := wd.tracks.iso.vtx.injective
  refine ⟨wd.tracks.iso.dart.symm r, wd.tracks.iso.dart.symm m.right, ?_, ?_, ?_, ?_, ?_⟩
  · refine hinj ?_
    have h := hv (wd.tracks.iso.dart.symm r)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (hr.trans (vtx_baseDart m wd).symm)
  · refine hinj ?_
    have h := hv (wd.tracks.iso.dart.symm m.right)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (m.right_vert.trans (vtx_opBaseDart m wd).symm)
  · intro hbad
    have h := congrArg wd.tracks.iso.dart hbad
    rw [Equiv.apply_symm_apply, dart_baseDart] at h
    exact hrb h
  · intro hbad
    have h := congrArg wd.tracks.iso.dart hbad
    rw [Equiv.apply_symm_apply, dart_opBaseDart] at h
    exact m.right_ne h
  · ext d
    rw [mem_movedStar_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hdb, ⟨hdl, hdv⟩ | hdr⟩
      · rcases hall d hdv with h | h | h
        · exact absurd h hdb
        · exact absurd h hdl
        · exact Or.inl h
      · exact Or.inr hdr
    · rintro (rfl | rfl)
      · exact ⟨hrb, Or.inl ⟨hrl, hr⟩⟩
      · exact ⟨m.base_ne_right.symm, Or.inr rfl⟩

/-- **The label of a tracked dart is the chart row of its occurrence's stable
row.**  This is all that the star counts extract from the survivor clause
of the (H-*) conditions
(`NonTrivalentValencyTwoStarCount.label_dart_merged` and its `_iff`/`_ne_base`
forms), and it needs only the row equality -- which is why those conditions
state their survivor clause at row level rather than as
`first.2.1 = selectedLift …`. -/
theorem label_dart_of_row (d : StableSourceDarts.Dart wd.cover)
    (e : NonDanglingEdge wd.cover) (hd : d.2.1.stablePath = e.stablePath) :
    label (wd.tracks.iso.dart d) = wd.fullDim.labelling.row e.stablePath := by
  rw [wd.tracks.row_map d]
  exact congrArg _ hd

end Wall

/-! ## 3.  Necessity of the separation predicates, valency by valency

Each (H-*) condition opens with the orientation clause
`wd.tracks.iso.dart (facetDartLeft …) = m.base`, under which that file's
`facetDartLeft`/`facetDartRight` are `baseDart`/`opBaseDart`, and continues with
the pair clause of `vertex_of_movedStar_eq_pair`.  So (H-*) forces the two named
survivors to be incident to the two ends of the vanishing occurrence, one each --
its `…Separated` predicate up to the order of the pair. -/

section ThreeValent

open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)

theorem baseDart_eq_facetDartLeft_three
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    baseDart m wd = facetDartLeft m wd wallStar := by
  exact (Equiv.symm_apply_eq _).mpr hBase.symm

theorem opBaseDart_eq_facetDartRight_three
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    opBaseDart m wd = facetDartRight m wd wallStar := by
  exact (Equiv.symm_apply_eq _).mpr (op_base_eq m wd wallStar hBase)

variable {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- **The occurrence-level (H-III) forces `DoubledSeparated`, up to the order of
the doubled pair.**  The hypotheses are the occurrence-level form of (H-III):
the orientation clause, and two darts that *are* the occurrences of the two
doubled-direction survivors.  This is exactly why the occurrence-level clause
is unsatisfiable at a Type I/II incoming, where `e_delta` is a pass-through
survivor: it would force that survivor's own occurrence to sit at an end of the
vanishing occurrence.  The row-level (H-III) does not imply it, and does not
need to: at row level the separation of the two named rows is automatic
(`vertex_of_movedStar_eq_pair`).
`NonTrivalentValencyThreeTracks.prescribedDoubledMove_of_occurrence` turns
these same hypotheses into (H-III). -/
theorem separated_or_swapped_of_prescribedDoubledMove
    (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (first second : StableSourceDarts.Dart wd.cover)
    (hFirst : first.2.1 = doubledLift m wd src false)
    (hSecond : second.2.1 = doubledLift m wd src true)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    DoubledSeparated m wd wallStar src ∨
      (Incident wd.cover (doubledLift m wd src false).1 (rightEnd m wd) ∧
        Incident wd.cover (doubledLift m wd src true).1 (leftEnd m wd)) := by
  have hBaseD := baseDart_eq_facetDartLeft_three m wd wallStar hBase
  have hOpD := opBaseDart_eq_facetDartRight_three m wd wallStar hBase
  have hIncFirst : Incident wd.cover (doubledLift m wd src false).1 first.1.1 := by
    have h := first.2.2
    rwa [hFirst] at h
  have hIncSecond : Incident wd.cover (doubledLift m wd src true).1 second.1.1 := by
    have h := second.2.2
    rwa [hSecond] at h
  rcases vertex_of_movedStar_eq_pair m wd first second hStar with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, hBaseD] at hIncFirst
    rw [h2, hOpD] at hIncSecond
    exact Or.inl ⟨hIncFirst, hIncSecond⟩
  · rw [h1, hOpD] at hIncFirst
    rw [h2, hBaseD] at hIncSecond
    exact Or.inr ⟨hIncFirst, hIncSecond⟩

open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleTracks

/-- **The occurrence-level (H-I/II) forces `SimpleSeparated`, up to the order of
the pair `{e_alpha, e_delta}`.**  The hypotheses are the occurrence-level form
of (H-I/II); `NonTrivalentValencyThreeSimpleTracks.prescribedSimpleMove_of_occurrence`
turns them into (H-I/II).  At a Type I/II incoming they are unsatisfiable,
because `e_delta` reaches `A_u` through a pass-through occurrence -- which is
why (H-I/II) is stated at row level. -/
theorem separated_or_swapped_of_prescribedSimpleMove
    (base : SimpleBase (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (first second : StableSourceDarts.Dart wd.cover)
    (hFirst : first.2.1 = alphaLift m wd base)
    (hSecond : second.2.1 = deltaLift m wd base)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    SimpleSeparated m wd base ∨
      (Incident wd.cover (alphaLift m wd base).1 (rightEnd m wd) ∧
        Incident wd.cover (deltaLift m wd base).1 (leftEnd m wd)) := by
  have hBaseD := baseDart_eq_facetDartLeft_three m wd wallStar hBase
  have hOpD := opBaseDart_eq_facetDartRight_three m wd wallStar hBase
  have hIncFirst : Incident wd.cover (alphaLift m wd base).1 first.1.1 := by
    have h := first.2.2
    rwa [hFirst] at h
  have hIncSecond : Incident wd.cover (deltaLift m wd base).1 second.1.1 := by
    have h := second.2.2
    rwa [hSecond] at h
  rcases vertex_of_movedStar_eq_pair m wd first second hStar with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, hBaseD] at hIncFirst
    rw [h2, hOpD] at hIncSecond
    exact Or.inl ⟨hIncFirst, hIncSecond⟩
  · rw [h1, hOpD] at hIncFirst
    rw [h2, hBaseD] at hIncSecond
    exact Or.inr ⟨hIncFirst, hIncSecond⟩

end ThreeValent

section TwoValent

open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoTracks

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (hNoReturn : NoContractedReturn wd.cover wd.contracted)

theorem baseDart_eq_facetDartLeft_two
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) :
    baseDart m wd = facetDartLeft m wd hNoReturn := by
  exact (Equiv.symm_apply_eq _).mpr hBase.symm

theorem opBaseDart_eq_facetDartRight_two
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base) :
    opBaseDart m wd = facetDartRight m wd hNoReturn := by
  exact (Equiv.symm_apply_eq _).mpr (op_base_eq m wd hNoReturn hBase)

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)

/-- **The occurrence-level (H-II) forces `MergedSeparated`, up to the order of
the merged pair.**  The hypotheses are the occurrence-level form of (H-II);
`NonTrivalentValencyTwoTracks.prescribedMergedMove_of_occurrence` turns them
into (H-II).  They are unsatisfiable at every incoming shape with a pass-through
survivor (Configuration B, and the split incomings of Configuration A) -- which
is why (H-II) is stated at row level. -/
theorem separated_or_swapped_of_prescribedMergedMove
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd hNoReturn) = m.base)
    (first second : StableSourceDarts.Dart wd.cover)
    (hFirst : first.2.1 = selectedLift m wd sel false)
    (hSecond : second.2.1 = selectedLift m wd sel true)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    MergedSeparated m wd sel ∨
      (Incident wd.cover (selectedLift m wd sel false).1 (rightEnd m wd) ∧
        Incident wd.cover (selectedLift m wd sel true).1 (leftEnd m wd)) := by
  have hBaseD := baseDart_eq_facetDartLeft_two m wd hNoReturn hBase
  have hOpD := opBaseDart_eq_facetDartRight_two m wd hNoReturn hBase
  have hIncFirst : Incident wd.cover (selectedLift m wd sel false).1 first.1.1 := by
    have h := first.2.2
    rwa [hFirst] at h
  have hIncSecond : Incident wd.cover (selectedLift m wd sel true).1 second.1.1 := by
    have h := second.2.2
    rwa [hSecond] at h
  rcases vertex_of_movedStar_eq_pair m wd first second hStar with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, hBaseD] at hIncFirst
    rw [h2, hOpD] at hIncSecond
    exact Or.inl ⟨hIncFirst, hIncSecond⟩
  · rw [h1, hOpD] at hIncFirst
    rw [h2, hBaseD] at hIncSecond
    exact Or.inr ⟨hIncFirst, hIncSecond⟩

/-- **(H-II) at row level.**  The same orientation clause and the same moved
star, with the two named darts required only to carry the *stable rows* of the
two merged survivors, not to be those occurrences themselves.  It is what the
star count actually consumes (`label_dart_of_row`), and unlike the
occurrence-level clause it is satisfiable when a merged survivor reaches its end
of the vanishing occurrence through a pass-through occurrence over the
contracted target edge (Configuration B, and the split incomings of
Configuration A).

This is literally `NonTrivalentValencyTwoTracks.PrescribedMergedMove`; the
separate name records the row-level reading. -/
def PrescribedMergedMoveRow : Prop :=
  PrescribedMergedMove m wd hNoReturn sel

/-- (H-II) is the row-level condition, so this is the identity; the
occurrence-level clause reaches it through
`NonTrivalentValencyTwoTracks.prescribedMergedMove_of_occurrence`. -/
theorem prescribedMergedMoveRow_of_prescribedMergedMove
    (hPres : PrescribedMergedMove m wd hNoReturn sel) :
    PrescribedMergedMoveRow m wd hNoReturn sel := hPres

/-- Under the row-level (H-II) the two named darts still sit one at each end of
the vanishing occurrence, and their tracked labels are the chart rows of the two
merged survivors' incoming rows -- the two facts the star count at `A_u` uses. -/
theorem prescribedMergedMoveRow_spec (hPres : PrescribedMergedMoveRow m wd hNoReturn sel) :
    ∃ first second : StableSourceDarts.Dart wd.cover,
      ((first.1.1 = leftEnd m wd ∧ second.1.1 = rightEnd m wd) ∨
        (first.1.1 = rightEnd m wd ∧ second.1.1 = leftEnd m wd)) ∧
      label (wd.tracks.iso.dart first) =
        wd.fullDim.labelling.row (selectedLift m wd sel false).stablePath ∧
      label (wd.tracks.iso.dart second) =
        wd.fullDim.labelling.row (selectedLift m wd sel true).stablePath ∧
      (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
        {wd.tracks.iso.dart first, wd.tracks.iso.dart second} := by
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  have hBaseD := baseDart_eq_facetDartLeft_two m wd hNoReturn hBase
  have hOpD := opBaseDart_eq_facetDartRight_two m wd hNoReturn hBase
  refine ⟨first, second, ?_, label_dart_of_row m wd first _ hFirst,
    label_dart_of_row m wd second _ hSecond, hStar⟩
  rcases vertex_of_movedStar_eq_pair m wd first second hStar with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, hBaseD, h2, hOpD]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [h1, hOpD, h2, hBaseD]
    exact Or.inr ⟨rfl, rfl⟩

end TwoValent

section FourValent

open DraismaVargas.LocalCases.NonTrivalentValencyFourTracks

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)

theorem baseDart_eq_facetDartLeft_four
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    baseDart m wd = facetDartLeft m wd wallStar := by
  exact (Equiv.symm_apply_eq _).mpr hBase.symm

theorem opBaseDart_eq_facetDartRight_four
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    opBaseDart m wd = facetDartRight m wd wallStar := by
  exact (Equiv.symm_apply_eq _).mpr (op_base_eq m wd wallStar hBase)

variable (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlock) = 4)
  (pairing : Fin 3)

/-- **(H-IV) forces `SelectedSeparated`, up to the order of the side-`false`
pair.** -/
theorem separated_or_swapped_of_prescribedPairingMove
    (hPres : PrescribedPairingMove m wd wallStar anchorBlock hAnchor pairing) :
    SelectedSeparated m wd wallStar anchorBlock hAnchor pairing ∨
      (Incident wd.cover (selectedLift m wd wallStar anchorBlock hAnchor pairing false false).1
          (rightEnd m wd) ∧
        Incident wd.cover (selectedLift m wd wallStar anchorBlock hAnchor pairing false true).1
          (leftEnd m wd)) := by
  obtain ⟨hBase, first, second, hFirst, hSecond, hStar⟩ := hPres
  have hBaseD := baseDart_eq_facetDartLeft_four m wd wallStar hBase
  have hOpD := opBaseDart_eq_facetDartRight_four m wd wallStar hBase
  have hIncFirst : Incident wd.cover
      (selectedLift m wd wallStar anchorBlock hAnchor pairing false false).1 first.1.1 := by
    have h := first.2.2
    rwa [hFirst] at h
  have hIncSecond : Incident wd.cover
      (selectedLift m wd wallStar anchorBlock hAnchor pairing false true).1 second.1.1 := by
    have h := second.2.2
    rwa [hSecond] at h
  rcases vertex_of_movedStar_eq_pair m wd first second hStar with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, hBaseD] at hIncFirst
    rw [h2, hOpD] at hIncSecond
    exact Or.inl ⟨hIncFirst, hIncSecond⟩
  · rw [h1, hOpD] at hIncFirst
    rw [h2, hBaseD] at hIncSecond
    exact Or.inr ⟨hIncFirst, hIncSecond⟩

end FourValent

end

end DraismaVargas.LocalCases.IncomingPairing
