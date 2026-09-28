import DraismaVargas.LocalCases.NonTrivalentValencyFourStarCount
import DraismaVargas.LocalCases.IncomingPairing

/-!
# The valency-four move-to-pairing dispatcher: `TypeChangeLink m wd` for every move

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (the labelling
convention (1) at a non-trivalent wall: the contracting edge `h_1` of the
incoming type has two trivalent ends `A_1`, `A_2`, and the four edges of `H_0`
at the four-valent `A` are distributed two at each end; the three combinatorial
resolutions `H_{2,3}`, `H_{2,4}`, `H_{2,5}` of `H_0`) and Section 5.2 (Case
`{v4-nd4}`, `K = 0`), together with Draisma--Vargas Part I (arXiv:1909.12924),
the construction of the stable graph `H(M)` in Section 3 and the edge
labellings a limit inherits in Section 5.  At a four-valent wall all four
survivors are direct, so the occurrence-level hypothesis (H-IV) can be
discharged; doing so takes the two normalisations of §3 below.

`NonTrivalentValencyFourExitLink` provides the valency-four exit,
`NonTrivalentValencyFourTracks` the vertex dictionary and the hypothesis (H-IV)
(`NonTrivalentValencyFourTracks.PrescribedPairingMove`), and
`NonTrivalentValencyFourStarCount` the star count, so that
`OuterWalk.TypeChangeLink` at a four-valent wall follows from (H-IV) alone
(`NonTrivalentValencyFourStarCount.typeChangeLink_of_prescribedPairingMove`).
This module discharges (H-IV) from the move itself, and therefore delivers the
link at **every** wall datum of surviving valency four with no hypothesis beyond
`card (incidentEdges ⟨wd.a, wd.hab⟩) = 4`.

## What is proved

### 1.  Reading the move

* `filter_label_base`, `dart_facetDartLeft_cases`: the chart row `label m.base`
  carries exactly the two darts `m.base` and `graph.op m.base`
  (`NonTrivalentValencyThreeStarCount.card_filter_label`), so the tracked dart of
  the `A_1` end of the vanishing occurrence is one of them.  This is the
  orientation dichotomy.
* `dart_ne_opBase_of_mem_movedStar`, `row_ne_facet_of_mem_movedStar`: a dart the
  move places in the star of `graph.vert m.base` beside `m.base` does not carry
  the vanishing row, hence its occurrence is not the vanishing occurrence.

### 2.  Reading a survivor at an end as a four-branch label

* `target_ne_contracted_of_incident_end`: a survivor at an end of the vanishing
  occurrence other than the vanishing occurrence itself does not lie over the
  contracted target occurrence (`W4IncomingPrunedFibre`: at a four-valent wall the
  pruned fibre of every merged vertex carries at most one internal occurrence).
* `descent`, `liftEdge_descent`, `incident_descent`: it therefore descends to a
  surviving occurrence of the wall datum incident to the anchor, and
  `NonTrivalentValencyFourTracks.liftEdge` carries it back.
* `eq_sourceEdge_of_target`: **target-direction injectivity, read as a
  characterisation.**  A surviving occurrence at the anchor over the target
  direction `star.edge lbl` *is* `FourBranchAnchor.sourceEdge lbl`; the witness
  sheet does not enter.  This is what lets the dispatcher choose the star.
* `not_incident_both_ends`: no surviving occurrence other than the vanishing one
  joins the two ends -- it would descend to a loop of the wall target at the
  anchor, and the wall target is loopless (`GluingContraction.fst_ne_snd`).  So
  the two occurrences the move names carry two *different* target directions.

### 3.  The two normalisations

* `relabel`, `relabel_two`, `relabel_three`: **the star is chosen by the move.**
  `W4TargetPairings.Pairing.labelsOnSide pairing false` is the complement of
  `{0, pairing + 1}`, so it never contains the label `0`: with the star fixed,
  (H-IV) can name only the pairs of survivors avoiding `star.edge 0`, which is
  half of the four pairs a move can prescribe.  The star is the dispatcher's own
  choice (`FourStar` is a bare labelling `Fin 4 ≃ incidentEdges`), so the
  dispatcher relabels it to put the two named directions on the labels `2` and
  `3`, and then `pairing = 0` has exactly them on its side `false`
  (`labelsOnSide_zero_false`, `first_second_zero_false`).
* `swapArrival`, `swapWallData`, `linkOfSwap`, `facetEdge_swap`,
  `facetDartLeft_swap`: **the orientation is normalised by
  `CubicDartGraph.MoveData.swap`.**  `m.swap.base = graph.op m.base`, so the arrival
  has to be re-read at the label of the opposite dart -- which is the same chart
  coordinate (`MovedIncidenceIso.label_op_of_tracks`), so the wall payload is
  literally unchanged and `swapWallData` is `wd`'s own fields.  The vanishing
  occurrence is unchanged (`facetEdge_swap`, by the uniqueness
  `NonTrivalentValencyFourTracks.eq_facetEdge`), hence so is the `A_1` dart, and
  the moved graph is unchanged (`CubicDartGraph.move_swap`), so a link for `m.swap`
  transports to a link for `m` with only its `tracks` field rewritten.

### 4.  The headline

* `nonempty_typeChangeLink_of_orientation`: the link at a four-valent wall whose
  vanishing occurrence is oriented with its `A_1` end at `graph.vert m.base`.
* `typeChangeLink_four`, `typeChangeLink_four'`: **`OuterWalk.TypeChangeLink` at
  every four-valent wall datum of every Whitehead move, from
  `card (incidentEdges ⟨wd.a, wd.hab⟩) = 4` alone**, in the `Nonempty` form and in
  the bare form.
* `valency_four_or_three_or_two`: `OuterWalk.WallData.valency` re-exported, so the
  final dispatcher can case-split on the wall valency.
* `typeChangeLink_of_valency_three_two`, `link_of_valency_three_two`: the valency
  dispatcher itself, the second in exactly the shape of the `link` binder of
  `OuterWalk.coneEntry_of_reaches`, with the four-valent branch discharged,
  taking the valency-three and valency-two exits as explicit parameters.

## Hypotheses left explicit here

1. `h4 : card (incidentEdges ⟨wd.a, wd.hab⟩) = 4`.  Nothing else: `wallStar`,
   `anchorBlock`, `hAnchor` and `pairing` are all produced here, and (H-IV) is
   discharged, so the valency-four branch of the `link` binder needs nothing
   more.
2. The valency-three and valency-two branches.  `valency_four_or_three_or_two`
   only names them; they are discharged unconditionally elsewhere, by
   `NonTrivalentValencyThreeDispatcher` and by
   `NonTrivalentValencyTwoBaseOneLink.link_all`.
3. No claim is made that the pairing index computed here is the one the paper's
   count would assign: existence of *a* prescribed resolution realised by the
   move is all the walk needs.

No structure and no `Prop` is introduced.  `swapArrival`, `swapWallData`,
`relabel` and `descent` are inhabitants of existing structures built from data
already in hand, `dartOfLeftEnd` names a dart of an existing occurrence, and each
is used in the theorems above; `linkOfSwap` inhabits `OuterWalk.TypeChangeLink`.

## Consumers

The `link` binder of `OuterWalk.coneEntry_of_reaches`, at Part II Case
`{v4-nd4}`: `NonTrivalentValencyThreeDispatcher` uses `typeChangeLink_four'`, and
the final valency dispatcher `NonTrivalentValencyTwoDispatcher` uses
`link_of_valency_three_two`, case-splitting through
`valency_four_or_three_or_two`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourDispatcher

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.NonTrivalentValencyFourTracks
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

/-! ## 1.  Relabelling a four-star

`W4TargetPairings.Pairing.labelsOnSide pairing false` is the complement of
`Pairing.side pairing = {0, pairing + 1}`, so it is one of `{2,3}`, `{1,3}`,
`{1,2}`: the label `0` is always on the side `true`.  Since (H-IV) names the side
`false`, the dispatcher has to pick the star, not only the pairing. -/

section Relabel

variable {target : CFGraph} {wall : target.V}

/-- **Relabel a four-star so that two named incident occurrences carry the labels
`2` and `3`** -- the two labels the pairing `0` puts on its side `false`. -/
def relabel (star : W4TargetPairings.FourStar target wall)
    (first second : {edge : target.edges // edge ∈ GluingDatum.incidentEdges wall}) :
    W4TargetPairings.FourStar target wall where
  label :=
    ((Equiv.swap (3 : Fin 4) (Equiv.swap (2 : Fin 4) (star.label.symm first)
        (star.label.symm second))).trans
      (Equiv.swap (2 : Fin 4) (star.label.symm first))).trans star.label

theorem relabel_two (star : W4TargetPairings.FourStar target wall)
    (first second : {edge : target.edges // edge ∈ GluingDatum.incidentEdges wall})
    (hne : first ≠ second) :
    (relabel star first second).edge 2 = first.1 := by
  classical
  set j := star.label.symm first with hj
  set j' := star.label.symm second with hj'
  have hjne : j ≠ j' := fun h ↦ hne (by
    rw [← star.label.apply_symm_apply first, ← star.label.apply_symm_apply second, ← hj, ← hj', h])
  have hk : Equiv.swap (2 : Fin 4) j j' ≠ 2 := by
    intro hBad
    have h2 : Equiv.swap (2 : Fin 4) j j = 2 := Equiv.swap_apply_right _ _
    exact hjne ((Equiv.swap (2 : Fin 4) j).injective (h2.trans hBad.symm))
  show (star.label (Equiv.swap (2 : Fin 4) j
    (Equiv.swap (3 : Fin 4) (Equiv.swap (2 : Fin 4) j j') 2))).1 = first.1
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h ↦ hk h.symm), Equiv.swap_apply_left,
    hj, Equiv.apply_symm_apply]

theorem relabel_three (star : W4TargetPairings.FourStar target wall)
    (first second : {edge : target.edges // edge ∈ GluingDatum.incidentEdges wall}) :
    (relabel star first second).edge 3 = second.1 := by
  classical
  set j := star.label.symm first with hj
  set j' := star.label.symm second with hj'
  show (star.label (Equiv.swap (2 : Fin 4) j
    (Equiv.swap (3 : Fin 4) (Equiv.swap (2 : Fin 4) j j') 3))).1 = second.1
  rw [Equiv.swap_apply_left, Equiv.swap_apply_self, hj', Equiv.apply_symm_apply]

end Relabel

/-! ## 2.  The two labels the pairing `0` puts on its side `false` -/

theorem labelsOnSide_zero_false :
    W4TargetPairings.Pairing.labelsOnSide 0 false = ({2, 3} : Finset (Fin 4)) := by
  decide +kernel

/-- The side `false` of the pairing `0` consists of the labels `2` and `3`, in one
of the two orders (`firstLabel`/`secondLabel` are classical choices). -/
theorem first_second_zero_false :
    (firstLabel 0 false = 2 ∧ secondLabel 0 false = 3) ∨
      (firstLabel 0 false = 3 ∧ secondLabel 0 false = 2) := by
  have hf := firstLabel_mem 0 false
  have hs := secondLabel_mem 0 false
  have hne := firstLabel_ne_secondLabel 0 false
  rw [labelsOnSide_zero_false] at hf hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf hs
  rcases hf with hf | hf <;> rcases hs with hs | hs
  · exact absurd (hf.trans hs.symm) hne
  · exact Or.inl ⟨hf, hs⟩
  · exact Or.inr ⟨hf, hs⟩
  · exact absurd (hf.trans hs.symm) hne

/-! ## 3.  The dart of an occurrence at its first end -/

section Dart

variable {targetIn : CFGraph} {deg : ℕ}

/-- The dart of a surviving occurrence at its first end. -/
def dartOfLeftEnd (data : GluingDatum targetIn deg) (e : NonDanglingEdge data)
    (h3 : 3 ≤ nonDanglingValency data (data.sourceEnds e.1).1) :
    StableSourceDarts.Dart data :=
  ⟨⟨(data.sourceEnds e.1).1, h3⟩, ⟨e, Or.inl rfl⟩⟩

theorem dartOfLeftEnd_congr (data : GluingDatum targetIn deg)
    {e e' : NonDanglingEdge data} (h : e = e')
    (h3 : 3 ≤ nonDanglingValency data (data.sourceEnds e.1).1)
    (h3' : 3 ≤ nonDanglingValency data (data.sourceEnds e'.1).1) :
    dartOfLeftEnd data e h3 = dartOfLeftEnd data e' h3' := by
  subst h
  rfl

end Dart

/-! ## 4.  Reading the move through the incoming tracking -/

section Walk

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

include wd in
/-- **The vanishing chart row carries exactly the two darts of the contracted
edge.**  `NonTrivalentValencyThreeStarCount.card_filter_label` counts them, and
`MovedIncidenceIso.label_op_of_tracks` puts `graph.op m.base` among them. -/
theorem filter_label_base :
    (Finset.univ.filter fun d : D ↦ label d = label m.base) = {m.base, graph.op m.base} := by
  classical
  have hL : label (graph.op m.base) = label m.base :=
    MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hd with rfl | rfl
    · rfl
    · exact hL
  · rw [NonTrivalentValencyThreeStarCount.card_filter_label m wd (label m.base)]
    exact le_of_eq (Finset.card_pair (graph.op_ne m.base).symm).symm

include wd in
/-- **The orientation dichotomy.**  The tracked dart of the `A_1` end of the
vanishing occurrence is `m.base` or `graph.op m.base`. -/
theorem dart_facetDartLeft_cases
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩) :
    wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base ∨
      wd.tracks.iso.dart (facetDartLeft m wd wallStar) = graph.op m.base := by
  classical
  have hLab : label (wd.tracks.iso.dart (facetDartLeft m wd wallStar)) = label m.base := by
    rw [wd.tracks.row_map (facetDartLeft m wd wallStar)]
    exact facetEdge_row m wd
  have hmem : wd.tracks.iso.dart (facetDartLeft m wd wallStar) ∈
      (Finset.univ.filter fun d : D ↦ label d = label m.base) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLab⟩
  rw [filter_label_base m wd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

/-- A dart the move places in the star of `graph.vert m.base` beside `m.base` is
not the dart of the contracted edge at the other end. -/
theorem dart_ne_opBase_of_mem_movedStar {d : D}
    (hd : d ∈ (Finset.univ.filter fun c ↦ (graph.move m).vert c = graph.vert m.base).erase
      m.base) :
    d ≠ graph.op m.base := by
  intro hBad
  have hv : (graph.move m).vert d = graph.vert m.base :=
    (Finset.mem_filter.mp (Finset.mem_erase.mp hd).2).2
  rw [hBad] at hv
  refine m.nonloop ?_
  rw [← hv]
  show graph.vert (graph.op m.base) = graph.vert (m.perm (graph.op m.base))
  rw [m.perm_opBase]

include wd in
/-- **The two occurrences a move brings together are not the vanishing
occurrence.**  Their darts carry a chart row other than the vanishing one. -/
theorem row_ne_facet_of_mem_movedStar (d : StableSourceDarts.Dart wd.cover)
    (hd : wd.tracks.iso.dart d ∈
      (Finset.univ.filter fun c ↦ (graph.move m).vert c = graph.vert m.base).erase m.base) :
    d.2.1 ≠ facetEdge m wd := by
  classical
  intro hBad
  have hlab : label (wd.tracks.iso.dart d) = label m.base := by
    rw [wd.tracks.row_map d]
    show wd.fullDim.labelling.row d.2.1.stablePath = label m.base
    rw [hBad]
    exact facetEdge_row m wd
  have hmem : wd.tracks.iso.dart d ∈ (Finset.univ.filter fun c : D ↦ label c = label m.base) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlab⟩
  rw [filter_label_base m wd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact (Finset.mem_erase.mp hd).1 h
  · exact dart_ne_opBase_of_mem_movedStar m hd h

/-! ## 5.  Descending a survivor at an end to the anchor of the wall datum -/

/-- A surviving occurrence at an end of the vanishing occurrence, other than the
vanishing occurrence itself, does not lie over the contracted target occurrence:
at a four-valent wall the pruned fibre carries at most one internal occurrence. -/
theorem target_ne_contracted_of_incident_end
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (e : NonDanglingEdge wd.cover) (v : wd.cover.SourceVertex)
    (hv : Incident wd.cover (facetEdge m wd).1 v)
    (he : Incident wd.cover e.1 v) (hne : e ≠ facetEdge m wd) :
    (e.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted := by
  intro hBad
  exact hne (Subtype.ext (W4IncomingPrunedFibre.contracted_sourceEdge_eq_of_incident
    wd.cover wd.fullDim wd.hc wd.hab wd.hOne wallStar v e.1 (facetEdge m wd).1
    hBad (facetEdge_over_contracted m wd) e.2 (facetEdge m wd).2 he hv))

/-- A surviving occurrence away from the contracted target occurrence descends to
a surviving occurrence of the wall datum (`DanglingReflected`). -/
def descent (e : NonDanglingEdge wd.cover)
    (hT : (e.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted) :
    NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  ⟨sourceEdgeMap wd.cover wd.hc wd.hab wd.hOne ⟨e.1, hT⟩,
    fun hBad ↦ e.2 ((wd.hCompat m).2 ⟨e.1, hT⟩ hBad)⟩

theorem liftEdge_descent (e : NonDanglingEdge wd.cover)
    (hT : (e.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted) :
    liftEdge m wd (descent m wd e hT) = e :=
  Subtype.ext (sourceEdgeEmbedding_sourceEdgeMap wd.cover wd.hc wd.hab wd.hOne ⟨e.1, hT⟩)

theorem incident_descent (e : NonDanglingEdge wd.cover)
    (hT : (e.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted)
    {v : wd.cover.SourceVertex} (hv : Incident wd.cover e.1 v) :
    Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) (descent m wd e hT).1
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v) :=
  incident_sourceEdgeMap wd.cover wd.hc wd.hab wd.hOne ⟨e.1, hT⟩ hv

section Anchor

variable (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)

/-- **A surviving occurrence at the anchor is the four-branch survivor of its own
target direction.**  This is `NonDanglingStarInjective`, read as a
characterisation of `FourBranchAnchor.sourceEdge` in which the chosen witness
sheet does not appear -- which is what lets the dispatcher relabel the star. -/
theorem eq_sourceEdge_of_target
    (star : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩)
    (src : FourBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) star anchorBlock)
    (lbl : Fin 4) (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hInc : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlock))
    (hT : (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) = star.edge lbl) :
    g.1 = src.sourceEdge lbl := by
  have hBlock := ((incident_wallBlock_sourceVertex_iff
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) anchorBlock g.1).mp hInc).2
  refine src.target_injective.unique lbl g.1 (src.sourceEdge lbl) hBlock ?_ hT ?_ g.2
    (src.sourceEdge_survives lbl)
  · exact WallBlock.ofSourceEdge_eq_of_rel (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      star anchorBlock lbl (src.sheet lbl) (src.sheet_wall_rel lbl)
  · exact GluingDatum.sourceEdge_target _ _ _

/-- The target direction of a surviving occurrence at the anchor is one of the
four incident target occurrences of the wall vertex. -/
theorem mem_incidentEdges_of_incident_anchor
    (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hInc : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlock)) :
    (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ∈
      GluingDatum.incidentEdges
        (⟨wd.a, wd.hab⟩ : (contract wd.coverTarget wd.hab wd.hOne).V) :=
  ((incident_wallBlock_sourceVertex_iff (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    anchorBlock g.1).mp hInc).1

variable (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
    ⟨wd.a, wd.hab⟩)
  (hAnchor : nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlock) = 4)

include wallStar hAnchor in
/-- **No surviving occurrence other than the vanishing one joins the two ends of
the vanishing occurrence.**  It would descend to a loop of the wall target at the
anchor, and the wall target is loopless. -/
theorem not_incident_both_ends
    (e : NonDanglingEdge wd.cover)
    (hLeft : Incident wd.cover e.1 (leftEnd m wd))
    (hRight : Incident wd.cover e.1 (rightEnd m wd))
    (hT : (e.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted) : False := by
  have hmapL : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd) =
      anchorVertex m wd anchorBlock :=
    sourceVertexMap_leftEnd_eq_anchorVertex m wd wallStar anchorBlock hAnchor
  have hmapR : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (rightEnd m wd) =
      anchorVertex m wd anchorBlock := by
    rw [← sourceVertexMap_leftEnd_eq_rightEnd m wd]
    exact hmapL
  have hBoth : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (wd.cover.sourceEnds e.1).1 =
        anchorVertex m wd anchorBlock ∧
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (wd.cover.sourceEnds e.1).2 =
        anchorVertex m wd anchorBlock := by
    rcases hLeft with hl | hl <;> rcases hRight with hr | hr
    · exact absurd (hl.symm.trans hr) (leftEnd_ne_rightEnd m wd)
    · exact ⟨by rw [hl]; exact hmapL, by rw [hr]; exact hmapR⟩
    · exact ⟨by rw [hr]; exact hmapR, by rw [hl]; exact hmapL⟩
    · exact absurd (hl.symm.trans hr) (leftEnd_ne_rightEnd m wd)
  have hEnds := sourceEnds_sourceEdgeMap wd.cover wd.hc wd.hab wd.hOne ⟨e.1, hT⟩
  set g : (contractDatum wd.cover wd.hc wd.hab wd.hOne).SourceEdge :=
    sourceEdgeMap wd.cover wd.hc wd.hab wd.hOne ⟨e.1, hT⟩ with hg
  have hFst : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEnds g).1 =
      anchorVertex m wd anchorBlock := by
    rw [congrArg Prod.fst hEnds]
    exact hBoth.1
  have hSnd : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEnds g).2 =
      anchorVertex m wd anchorBlock := by
    rw [congrArg Prod.snd hEnds]
    exact hBoth.2
  refine GluingContraction.fst_ne_snd g.1.1 ?_
  rw [← sourceEnds_fst_fst (contractDatum wd.cover wd.hc wd.hab wd.hOne) g,
    ← sourceEnds_snd_fst (contractDatum wd.cover wd.hc wd.hab wd.hOne) g, hFst, hSnd]

end Anchor

end Walk

/-! ## 6.  The orientation normalisation: reading the move from the other end -/

section Swap

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **The same facet arrival, read at the label of the opposite dart.**  The two
darts of the contracted edge carry the same chart coordinate
(`MovedIncidenceIso.label_op_of_tracks`), so no payload changes: only the two
facet clauses are transported. -/
def swapArrival (m : graph.MoveData)
    (arrival : FacetArrival degree graph label (label m.base))
    (hL : label (graph.op m.base) = label m.base) :
    FacetArrival degree graph label (label m.swap.base) where
  baseStart := arrival.baseStart
  baseFinish := arrival.baseFinish
  start_pos := arrival.start_pos
  finish_facet := by
    show arrival.baseFinish (label (graph.op m.base)) = 0
    rw [hL]
    exact arrival.finish_facet
  finish_pos := by
    intro t ht
    refine arrival.finish_pos t ?_
    intro hBad
    exact ht (by show t = label (graph.op m.base); rw [hL]; exact hBad)
  facetGeneric := arrival.facetGeneric
  final := arrival.final
  terminal := arrival.terminal
  restart_nonneg := arrival.restart_nonneg

/-- **The same wall data.**  Every field of `OuterWalk.WallData` is a field of the
arrival's terminal state, which `swapArrival` leaves alone. -/
def swapWallData (m : graph.MoveData)
    {arrival : FacetArrival degree graph label (label m.base)} (wd : WallData arrival)
    (hL : label (graph.op m.base) = label m.base) :
    WallData (swapArrival m arrival hL) where
  target := wd.target
  data := wd.data
  wall := wd.wall
  candidate := wd.candidate
  fullDim := wd.fullDim
  matrix_eq := wd.matrix_eq
  tracks := wd.tracks
  column := wd.column
  column_zero := wd.column_zero
  column_unique := wd.column_unique

/-- **A link for the swapped move is a link for the move.**  The two descriptions
contract the same edge and permute the darts alike, so `graph.move m.swap` is
`graph.move m` (`CubicDartGraph.move_swap`) and only the `tracks` field is rewritten;
the base stage, the candidate, its presentation and the common-minor agreement
are literally the same data. -/
def linkOfSwap (m : graph.MoveData)
    {arrival : FacetArrival degree graph label (label m.base)} (wd : WallData arrival)
    (hL : label (graph.op m.base) = label m.base)
    (link : TypeChangeLink m.swap (swapWallData m wd hL)) :
    TypeChangeLink m wd where
  base := link.base
  baseValid := link.baseValid
  candidate := link.candidate
  outgoingFD := link.outgoingFD
  tracks := CubicDartGraph.move_swap graph m ▸ link.tracks
  agree := link.agree

variable (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival) (hL : label (graph.op m.base) = label m.base)

/-- The vanishing row does not change when the move is read from the other end. -/
theorem facetRow_swap :
    facetRow m.swap (swapWallData m wd hL) = facetRow m wd := by
  show wd.fullDim.labelling.row.symm (label (graph.op m.base)) = _
  rw [hL]
  rfl

/-- The vanishing occurrence does not change either
(`NonTrivalentValencyFourTracks.eq_facetEdge`). -/
theorem facetEdge_swap
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩) :
    facetEdge m.swap (swapWallData m wd hL) = facetEdge m wd :=
  eq_facetEdge m wd wallStar (facetEdge m.swap (swapWallData m wd hL))
    ((facetEdge_stablePath m.swap (swapWallData m wd hL)).trans (facetRow_swap m wd hL))

/-- Hence neither does its dart at the `A_1` end. -/
theorem facetDartLeft_swap
    (wallStar : W4TargetPairings.FourStar (contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩) :
    facetDartLeft m.swap (swapWallData m wd hL) wallStar = facetDartLeft m wd wallStar :=
  dartOfLeftEnd_congr wd.cover (facetEdge_swap m wd hL wallStar) _ _

end Swap

/-! ## 7.  (H-IV) from the move, and the link -/

section Headline

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- **`OuterWalk.TypeChangeLink` at a four-valent wall whose vanishing occurrence
is oriented with its `A_1` end at `graph.vert m.base`.**  The two occurrences the
move brings together are read as two four-branch labels; the star is relabelled so
that they are the labels `2` and `3`, and the pairing `0` then has exactly them on
its side `false`, which is (H-IV). -/
theorem nonempty_typeChangeLink_of_orientation
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4)
    (hBase : wd.tracks.iso.dart
      (facetDartLeft m wd (W4TargetPairings.FourStar.of_card h4)) = m.base) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  set star₀ := W4TargetPairings.FourStar.of_card h4 with hstar₀
  obtain ⟨anchorBlock, hAnchor⟩ :=
    NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne star₀ (wd.hCompat m) wd.coordinates (label m.base)
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨x, y, hx1, hy1, -, -, hStar⟩ := IncomingPairing.exists_movedStar_darts m wd
  -- the orientation identifies the two ends of the vanishing occurrence
  have hbd : IncomingPairing.baseDart m wd = facetDartLeft m wd star₀ :=
    IncomingPairing.baseDart_eq_facetDartLeft_four m wd star₀ hBase
  have hod : IncomingPairing.opBaseDart m wd = facetDartRight m wd star₀ :=
    IncomingPairing.opBaseDart_eq_facetDartRight_four m wd star₀ hBase
  have hxv : x.1.1 = leftEnd m wd := by rw [hx1, hbd]; rfl
  have hyv : y.1.1 = rightEnd m wd := by rw [hy1, hod]; rfl
  have hxInc : Incident wd.cover x.2.1.1 (leftEnd m wd) := by rw [← hxv]; exact x.2.2
  have hyInc : Incident wd.cover y.2.1.1 (rightEnd m wd) := by rw [← hyv]; exact y.2.2
  -- neither of them is the vanishing occurrence
  have hxmem : wd.tracks.iso.dart x ∈
      (Finset.univ.filter fun c ↦ (graph.move m).vert c = graph.vert m.base).erase m.base := by
    rw [hStar]
    exact Finset.mem_insert_self _ _
  have hymem : wd.tracks.iso.dart y ∈
      (Finset.univ.filter fun c ↦ (graph.move m).vert c = graph.vert m.base).erase m.base := by
    rw [hStar]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hxne : x.2.1 ≠ facetEdge m wd := row_ne_facet_of_mem_movedStar m wd x hxmem
  have hyne : y.2.1 ≠ facetEdge m wd := row_ne_facet_of_mem_movedStar m wd y hymem
  -- they descend to two survivors at the anchor
  have hTx : (x.2.1.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted :=
    target_ne_contracted_of_incident_end m wd star₀ x.2.1 (leftEnd m wd)
      (incident_facetEdge_leftEnd m wd) hxInc hxne
  have hTy : (y.2.1.1.1.1 : wd.coverTarget.edges) ≠ wd.contracted :=
    target_ne_contracted_of_incident_end m wd star₀ y.2.1 (rightEnd m wd)
      (incident_facetEdge_rightEnd m wd) hyInc hyne
  have hIncX : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (descent m wd x.2.1 hTx).1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlock) := by
    have h := incident_descent m wd x.2.1 hTx hxInc
    rwa [sourceVertexMap_leftEnd_eq_anchorVertex m wd star₀ anchorBlock hAnchor] at h
  have hIncY : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (descent m wd y.2.1 hTy).1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlock) := by
    have h := incident_descent m wd y.2.1 hTy hyInc
    rw [← sourceVertexMap_leftEnd_eq_rightEnd m wd,
      sourceVertexMap_leftEnd_eq_anchorVertex m wd star₀ anchorBlock hAnchor] at h
    exact h
  -- the two target directions are different
  set sx : {edge : (contract wd.coverTarget wd.hab wd.hOne).edges //
      edge ∈ GluingDatum.incidentEdges
        (⟨wd.a, wd.hab⟩ : (contract wd.coverTarget wd.hab wd.hOne).V)} :=
    ⟨(descent m wd x.2.1 hTx).1.1.1,
      mem_incidentEdges_of_incident_anchor m wd anchorBlock _ hIncX⟩ with hsx
  set sy : {edge : (contract wd.coverTarget wd.hab wd.hOne).edges //
      edge ∈ GluingDatum.incidentEdges
        (⟨wd.a, wd.hab⟩ : (contract wd.coverTarget wd.hab wd.hOne).V)} :=
    ⟨(descent m wd y.2.1 hTy).1.1.1,
      mem_incidentEdges_of_incident_anchor m wd anchorBlock _ hIncY⟩ with hsy
  have hsne : sx ≠ sy := by
    intro hBad
    have hT : ((descent m wd x.2.1 hTx).1.1.1 :
        (contract wd.coverTarget wd.hab wd.hOne).edges) =
        star₀.edge (star₀.label.symm sx) := by
      show sx.1 = (star₀.label (star₀.label.symm sx)).1
      rw [Equiv.apply_symm_apply]
    have hT' : ((descent m wd y.2.1 hTy).1.1.1 :
        (contract wd.coverTarget wd.hab wd.hOne).edges) =
        star₀.edge (star₀.label.symm sx) := by
      show sy.1 = (star₀.label (star₀.label.symm sx)).1
      rw [Equiv.apply_symm_apply, hBad]
    have hsrc₀ := NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne star₀ (wd.hForest m) anchorBlock hAnchor
    have hEqX := eq_sourceEdge_of_target m wd anchorBlock star₀ hsrc₀ (star₀.label.symm sx)
      (descent m wd x.2.1 hTx) hIncX hT
    have hEqY := eq_sourceEdge_of_target m wd anchorBlock star₀ hsrc₀ (star₀.label.symm sx)
      (descent m wd y.2.1 hTy) hIncY hT'
    have hEq : descent m wd x.2.1 hTx = descent m wd y.2.1 hTy :=
      Subtype.ext (hEqX.trans hEqY.symm)
    have hxy : x.2.1 = y.2.1 := by
      rw [← liftEdge_descent m wd x.2.1 hTx, ← liftEdge_descent m wd y.2.1 hTy, hEq]
    exact not_incident_both_ends m wd anchorBlock star₀ hAnchor x.2.1 hxInc
      (by rw [hxy]; exact hyInc) hTx
  -- relabel the star so that the two directions carry the labels 2 and 3
  set star := relabel star₀ sx sy with hstar
  have hs2 : star.edge 2 = (descent m wd x.2.1 hTx).1.1.1 := relabel_two star₀ sx sy hsne
  have hs3 : star.edge 3 = (descent m wd y.2.1 hTy).1.1.1 := relabel_three star₀ sx sy
  have hsrc := NonTrivalentUniqueFourValent.wallFourBranchAnchor wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne star (wd.hForest m) anchorBlock hAnchor
  have hGx : (descent m wd x.2.1 hTx).1 = hsrc.sourceEdge 2 :=
    eq_sourceEdge_of_target m wd anchorBlock star hsrc 2 (descent m wd x.2.1 hTx) hIncX hs2.symm
  have hGy : (descent m wd y.2.1 hTy).1 = hsrc.sourceEdge 3 :=
    eq_sourceEdge_of_target m wd anchorBlock star hsrc 3 (descent m wd y.2.1 hTy) hIncY hs3.symm
  have hLiftX : liftEdge m wd ⟨hsrc.sourceEdge 2, hsrc.sourceEdge_survives 2⟩ = x.2.1 := by
    rw [show (⟨hsrc.sourceEdge 2, hsrc.sourceEdge_survives 2⟩ :
      NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) =
        descent m wd x.2.1 hTx from Subtype.ext hGx.symm]
    exact liftEdge_descent m wd x.2.1 hTx
  have hLiftY : liftEdge m wd ⟨hsrc.sourceEdge 3, hsrc.sourceEdge_survives 3⟩ = y.2.1 := by
    rw [show (⟨hsrc.sourceEdge 3, hsrc.sourceEdge_survives 3⟩ :
      NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) =
        descent m wd y.2.1 hTy from Subtype.ext hGy.symm]
    exact liftEdge_descent m wd y.2.1 hTy
  have hSel : ∀ (which : Bool) (lbl : Fin 4), selectedLabel 0 false which = lbl →
      selectedLift m wd star anchorBlock hAnchor 0 false which =
        liftEdge m wd ⟨hsrc.sourceEdge lbl, hsrc.sourceEdge_survives lbl⟩ := by
    intro which lbl h
    subst h
    rfl
  -- (H-IV) for the pairing `0`
  refine ⟨NonTrivalentValencyFourStarCount.typeChangeLink_of_prescribedPairingMove m wd star
    anchorBlock hAnchor 0 ⟨hBase, ?_⟩⟩
  rcases first_second_zero_false with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · exact ⟨x, y, ((hSel false 2 hf).trans hLiftX).symm,
      ((hSel true 3 hs).trans hLiftY).symm, hStar⟩
  · exact ⟨y, x, ((hSel false 3 hf).trans hLiftY).symm,
      ((hSel true 2 hs).trans hLiftX).symm, by rw [hStar, Finset.pair_comm]⟩

/-- **`OuterWalk.TypeChangeLink` at every four-valent wall datum of every Whitehead
move, from the valency hypothesis alone.**  If the vanishing occurrence is
oriented the other way, the move is re-read from the other end of the contracted
edge (`CubicDartGraph.MoveData.swap`), which leaves the moved graph and the whole wall
payload unchanged. -/
theorem typeChangeLink_four
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  rcases dart_facetDartLeft_cases m wd (W4TargetPairings.FourStar.of_card h4) with h | h
  · exact nonempty_typeChangeLink_of_orientation m wd h4 h
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hBase' : (swapWallData m wd hL).tracks.iso.dart
        (facetDartLeft m.swap (swapWallData m wd hL)
          (W4TargetPairings.FourStar.of_card h4)) = m.swap.base :=
      (congrArg wd.tracks.iso.dart
        (facetDartLeft_swap m wd hL (W4TargetPairings.FourStar.of_card h4))).trans h
    exact (nonempty_typeChangeLink_of_orientation m.swap (swapWallData m wd hL) h4
      hBase').map (linkOfSwap m wd hL)

/-- The same headline in the shape the `link` binder of
`OuterWalk.coneEntry_of_reaches` asks for. -/
def typeChangeLink_four'
    (h4 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 4) :
    TypeChangeLink m wd :=
  (typeChangeLink_four m wd h4).some

/-- **The wall valency trichotomy**, re-exported so that the final dispatcher can
case-split (`OuterWalk.WallData.valency`). -/
theorem valency_four_or_three_or_two :
    (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩).card = 4 ∨
      (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 3 ∨
        (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 2 := by
  rcases wd.valency m with h2 | h3 | h4
  · exact Or.inr (Or.inr h2)
  · exact Or.inr (Or.inl h3)
  · exact Or.inl h4

end Headline

/-! ## 8.  The valency dispatcher, in the shape of the walk's `link` binder -/

section Dispatch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **The valency dispatcher at one wall.**  By `OuterWalk.WallData.valency` a wall
of the outer walk has surviving valency `4`, `3` or `2`; the four-valent branch is
discharged here, so only the other two are asked for. -/
def typeChangeLink_of_valency_three_two (m : graph.MoveData)
    {arrival : FacetArrival degree graph label (label m.base)} (wd : WallData arrival)
    (h3 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩).card = 3 → TypeChangeLink m wd)
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩).card = 2 → TypeChangeLink m wd) :
    TypeChangeLink m wd := by
  classical
  by_cases h4 : (GluingDatum.incidentEdges
      (target := contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩).card = 4
  · exact typeChangeLink_four' m wd h4
  · by_cases hThree : (GluingDatum.incidentEdges
        (target := contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩).card = 3
    · exact h3 hThree
    · refine h2 ?_
      rcases valency_four_or_three_or_two m wd with h | h | h
      · exact absurd h h4
      · exact absurd h hThree
      · exact h

/-- **The `link` binder of `OuterWalk.coneEntry_of_reaches`, with the four-valent
branch discharged.**  Its remaining explicit parameters are the valency-three and
valency-two exits; both are discharged unconditionally elsewhere
(`NonTrivalentValencyThreeDispatcher`, `NonTrivalentValencyTwoBaseOneLink.link_all`). -/
def link_of_valency_three_two {G : CubicDartGraph D V}
    (h3 : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival),
        (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 3 → TypeChangeLink m wd)
    (h2 : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival),
        (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 2 → TypeChangeLink m wd) :
    ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), TypeChangeLink m wd :=
  fun K hK m arrival wd ↦
    typeChangeLink_of_valency_three_two m wd (h3 K hK m arrival wd) (h2 K hK m arrival wd)

end Dispatch

end

end DraismaVargas.LocalCases.NonTrivalentValencyFourDispatcher
