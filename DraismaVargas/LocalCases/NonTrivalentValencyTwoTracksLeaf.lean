import DraismaVargas.LocalCases.NonTrivalentValencyTwoTracks
import DraismaVargas.LocalCases.NonTrivalentValencyTwoExitFree

/-!
# The vertex dictionary and (H-II) of the valency-two Base II type change at a leaf wall

Source: Vargas, Part II, arXiv:2609.09109, Section 5.1 (the labelling conventions (1)--(2) at a
non-trivalent wall and `lemma-above-w0`, whose `val u = 1` case is the statement
this module is about: "if `val u = 1` and `val v = 3`, the edge connecting
`A_1^{(q)}` and `A_2^{(q)}` passes above `u`") together with Section 5.4 (case
`{v2-nd4}`, base tree `T_2` = Base II, incoming sub-cases `2 + 2`, `1 + 3`,
`3 + 1`), and Draisma–Vargas Part I, arXiv:1909.12924 (the stable graph `H(M)` and its row
labels) and the non-dangling valency formula `lemma-ndval-of-GqA0`.

`NonTrivalentValencyTwoTracks` builds the vertex half of the `tracks` field of
the valency-two Base II link at a `2 + 2` wall, where the strong
`hNoReturn : StablePathFacetContraction.NoContractedReturn wd.cover wd.contracted`
of `NonTrivalentValencyTwoExit` holds.  Its §1 (the vanishing row is the
*single* occurrence `h₁` between two branch vertices:
`three_le_nonDanglingValency_end`, `eq_facetEdge`) and §5 ((H-II)) are **false
at a `1 + 3` / `3 + 1` wall**: by `LeafFacetNoReturn` and
`StableLocalProperties.leaf_block_dichotomy`, when one endpoint of the contracted
target occurrence is a leaf of the incoming target tree the vanishing row passes
above that leaf as **two** occurrences meeting at a divalent fold vertex, so it
is a two-occurrence path whose *outer* ends are the two branch vertices.  This
module restates §§1 and 5 of `NonTrivalentValencyTwoTracks` there, reuses its
§§0, 2, 3, 4, 6, 7 unchanged, and hands the result to the no-return-free exit
`NonTrivalentValencyTwoExitFree.typeChangeLink_of_receipts_free`.

## What is proved

### 0.  The fold above the leaf

* `LeafFold wd`: a divalent source vertex of the incoming cover that every
  surviving occurrence over the contracted target occurrence meets.  That is
  the *only* feature of the leaf used below, and it does not mention the
  Whitehead move, so it is carried unchanged across the move that
  `prescribedMove` builds.
* `nonDanglingValency_eq_two_of_leaf`, `leafFold_of_leaf_left`,
  `leafFold_of_leaf_right` (§6): the fold exists at an actual `1 + 3` wall and
  at an actual `3 + 1` wall, from `LeafFacetNoReturn.incident_of_leaf_fold`
  and `NonTrivalentValencyTwoLeafDictionary.incident_of_leaf_fold_right`
  together with the leaf count.  These two are the non-vacuity witnesses of
  `LeafFold`.

### 1.  The vanishing path, and its two outer ends

* `secondEdge`, `eq_facetEdge_or_eq_secondEdge`: **the vanishing row has
  exactly two occurrences**, the two surviving occurrences at the fold --
  `NonTrivalentValencyTwoTracks.eq_facetEdge` replaced by a two-element
  classification.  (Every occurrence of the vanishing row lies over `t₁` by
  `NonTrivalentValencyTwoTracks.over_contracted_of_facetRow`; every surviving
  occurrence over `t₁` meets the fold; the fold is divalent.)
* `outerEnd`, `leftEnd`, `rightEnd`: the ends away from the fold.
* `leftEnd_ne_rightEnd`: **the two outer ends are distinct.**  If they
  coincided the vanishing row would be a loop of the stable graph and every
  branch vertex would meet it twice or not at all, contradicting
  `InteriorGraphTracking.Tracks.hasSimpleEnd` at the non-loop dart `m.base`
  (`CubicDarts.MoveData.nonloop`).  This is what replaces
  `wd.cover.sourceEnds_ne` in `NonTrivalentValencyTwoTracks`, which is
  unavailable because the two ends now belong to two *different* occurrences.
* `three_le_nonDanglingValency_leftEnd`, `..._rightEnd`: **both outer ends are
  branch vertices** -- `NonTrivalentValencyTwoTracks.three_le_nonDanglingValency_end`
  without any no-return hypothesis.  A divalent outer end would carry a second
  surviving occurrence of the vanishing row, necessarily the other occurrence at
  the fold, forcing the two outer ends to coincide.
* `sourceVertexMap_outerEnd`, `outerEnd_target`,
  `four_le_nonDanglingValency_map_leftEnd`: both outer ends lie in one fibre,
  which is four-valent downstairs (the divalent fold contributes `0` to the
  fibre budget `nd(A) = 2 + Σ (nd V - 2)`).

### 2.  `AnchorEnds`, and the vertex dictionary

§§2--4 of `NonTrivalentValencyTwoTracks` use only six facts about the pair of
ends, and those six are true at a `2 + 2` wall *and* at a leaf wall.  They are
isolated as

* `AnchorEnds m wd anchorBlk p q`: `p ≠ q`, both branch vertices, both over the
  anchor, and the anchor fibre carries no other branch vertex;

and the dictionary is rebuilt on them:

* `branchEquivAnchorComplement` (that of `NonTrivalentValencyTwoTracks`, with
  the vanishing occurrence abstracted away), `coverBranchEquiv`, and
  `vertexEquiv` -- the composite
  `BranchVertex cand.datum ≃ BranchVertex M₀-minus-A ⊕ Bool ≃
   BranchVertex M-minus-{p,q} ⊕ Bool ≃ BranchVertex M ≃ V`.
  §3 of `NonTrivalentValencyTwoTracks` (`branchSide`, `candVertex`,
  `candBranchEquiv`) mentions neither the vanishing occurrence nor `hNoReturn`,
  so it is used verbatim.

### 3.  The leaf wall satisfies `AnchorEnds`

* `sourceVertexMap_leftEnd_eq_anchorVertex`,
  `eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre`, `anchorEnds_leaf`: the §2
  argument of `NonTrivalentValencyTwoTracks` at a leaf wall.  Because the fold
  sits above whichever endpoint is the leaf, the outer ends may lie above `a` or
  above `b`, so `GraphContraction.fold_a` is used alongside
  `GraphContraction.fold_self`.

### 4.  (H-II) at a leaf wall

* `facetDartLeft`, `facetDartRight`: the darts of the **outer** occurrences at
  the two ends.  Unlike at a `2 + 2` wall these belong to two different
  occurrences; `opposite_facetDartLeft` still identifies them as opposite
  darts, now through the proved row equality rather than `rfl`.
* `PrescribedMergedMoveLeaf`: (H-II) with the orientation clause naming the
  dart of the outer occurrence at the `A_u` end; the survivor clause is that of
  `NonTrivalentValencyTwoTracks` verbatim -- at the level of stable **rows**
  (`d.2.1.stablePath = ...`) -- and one clause still covers Configuration A and
  Configuration B.
* `prescribedMergedMoveLeaf_of_occurrence`, `prescribedMergedMoveLeaf_of_rows`:
  the occurrence-level clause implies (H-II), and (H-II) follows from the
  orientation clause together with two moved darts carrying the two merged
  rows -- the shape `IncomingPairing.exists_movedStar_darts` produces, and the
  one the valency dispatcher consumes.  At row level separation is automatic
  (`IncomingPairing.vertex_of_movedStar_eq_pair`), so `MergedSeparatedLeaf` is
  not a hypothesis of the latter.
* `MergedSeparatedLeaf`, `prescribedMove`,
  `prescribedMergedMove_prescribedMove`: **non-vacuity of (H-II), in relative
  form**, exactly as in `NonTrivalentValencyTwoTracks` (an absolute
  `∃ m, ...` does not typecheck, because `wd : WallData arrival` fixes
  `m.base`).
* `card_star_move_eq_incidenceCount`: the off-wall half of the star count, from
  `move_vert_eq_iff_of_ne` and `card_star_eq_incidenceCount` (§6 of
  `NonTrivalentValencyTwoTracks`).

### 5--7.  The link, and the dispatcher

* `vertexEquiv_anchor_false` / `vertexEquiv_anchor_true`: under (H-II) the
  `A_u` end goes to `graph.vert m.base` and the `A_v` end to
  `graph.vert (graph.op m.base)`.
* `typeChangeLink_of_incidence`, `typeChangeLink_of_incidence_leaf`:
  `OuterWalk.TypeChangeLink` from the star count alone, through
  `MovedIncidenceIso.tracksOfMovedIncidence` and
  `NonTrivalentValencyTwoExitFree.typeChangeLink_of_receipts_free` -- so **no
  no-return hypothesis of any kind appears**.
* `exists_anchorEnds`: anchor ends at **every** two-valent Base II wall, by the
  incoming trichotomy `val u + val v = 4` (`WallProgress.endpoints_of_contraction`
  and `W2R1Target.TwoStar.card_incidentEdges`): `2 + 2` through
  `NonTrivalentValencyTwoExit.noContractedReturn_of_two_two` and §§1--2 of
  `NonTrivalentValencyTwoTracks`, `1 + 3` and `3 + 1` through this module.
* `typeChangeLink_of_incidence_two`: **the dispatcher.**  At any two-valent
  Base II wall it produces a branch-vertex bijection `ve` such that the single
  star count against `ve` and `NonTrivalentValencyTwoExitFree.wallOutgoingFD'`
  yields the link.  The two `hIncidence` shapes are unified: the outgoing
  presentation is `wallOutgoingFD'` in all three sub-cases (not
  `NonTrivalentValencyTwoExit.wallOutgoingFD`, which only exists under the
  strong hypothesis), so no transport through `wallOutgoingFD'_eq` is needed;
  what varies between sub-cases is only the bijection, which is therefore
  returned rather than fixed.
* `exists_typeChangeLink_of_incidence_of_wallData`: the headline of
  `NonTrivalentValencyTwoExitFree`, with no hypothesis about the candidate and
  with its `InteriorGraphTracking.Tracks` input replaced by that star count.

## The hypotheses that remain

1. `hIncidence`, the star count
   `incidenceCount cand.datum v r =
    Nat.card {d // (graph.move m).vert d = ve v ∧ label d = row r}`.
   Exactly as in `NonTrivalentValencyTwoTracks`: away from the anchor it is the
   composite of the two transports (T1) and (T2), both proved in
   `NonTrivalentValencyTwoStarCountAll` (off the wall,
   `NonTrivalentValencyTwoTracks.incidenceCount_retainedVertex_retainedRow` and
   `WallSplitIncidence.incidenceCount_sourceVertexMap`; at an ordinary wall
   block, `NonTrivalentValencyTwoStarCount.incidenceCount_candVertex` /
   `incidenceCount_wall_eq_incoming` reused verbatim) -- and at the anchor it is
   what (H-II) prescribes together with the exact anchor stars of
   `NonTrivalentValencyTwoRows` and this file's
   `card_star_move_eq_incidenceCount`.
2. `MergedSeparatedLeaf`, and (H-II) itself.  `MergedSeparatedLeaf` is the
   geometric content of a type change at a leaf wall (the two merged survivors
   sit at the two *different* outer ends) and is a named hypothesis, in the
   style of `StablePathFacetContraction.NoContractedReturn`; it is not derived
   here.  (H-II) has the relative witness `prescribedMergedMove_prescribedMove`.
   Since (H-II) is stated at row level, `MergedSeparatedLeaf` is a hypothesis of
   that witness only; the dispatcher discharges (H-II) through
   `prescribedMergedMoveLeaf_of_rows`.
3. `wallStar : W2R1Target.TwoStar ... ⟨wd.a, wd.hab⟩`, `src`, `sel`, `hOrd`,
   and the wall labelling `labelling₀` / `hRowVal` / `hMatrixWall` of
   `NonTrivalentValencyTwoExitFree` -- **exactly the binders of
   `NonTrivalentValencyTwoExitFree.wallOutgoingFD'` and
   `typeChangeLink_of_receipts_free`**; nothing is added, and the headline
   `exists_typeChangeLink_of_incidence_of_wallData` discharges `hOrd`,
   `labelling₀`, `hRowVal` and `hMatrixWall` internally.
4. No no-return hypothesis of any kind remains: the `2 + 2` branch of
   `exists_anchorEnds` builds its own through
   `NonTrivalentValencyTwoExit.noContractedReturn_of_two_two`, and the leaf
   branches build a `LeafFold` instead.

`LeafFold` is the one structure introduced; its non-vacuity witnesses are
`leafFold_of_leaf_left` and `leafFold_of_leaf_right`, which inhabit it at an
actual `1 + 3` and at an actual `3 + 1` wall.  The `Prop` definitions
`AnchorEnds`, `PrescribedMergedMoveLeaf` and `MergedSeparatedLeaf` come with
`exists_anchorEnds` (unconditional at every two-valent Base II wall),
`prescribedMergedMove_prescribedMove` (relative) and the note above.

## Consumers

`NonTrivalentValencyTwoStarCountAll` discharges the star count above and
delivers `exists_typeChangeLink_of_prescribedMergedMove_of_wallData`:
`OuterWalk.TypeChangeLink` at Part II case `{v2-nd4}` in **all three** incoming
sub-cases from (H-II), `wd` and the incoming two-valent star alone, hence the
`link` hypothesis of `OuterWalk.coneEntry_of_reaches`.
`NonTrivalentValencyTwoTracks.typeChangeLink_of_incidence` is the `2 + 2`-only
route against the presentation of `NonTrivalentValencyTwoExit`; the dispatcher
here covers all three sub-cases.
-/
namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.PrunedFibreValency
open DraismaVargas.LocalCases.PrunedFibreTree
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-! ## 0.  The fold above the leaf -/

section FoldDef

variable {facet : coordinate} {arr : FacetArrival degree graph label facet}

/-- **The fold above the leaf.**  At a `1 + 3` or `3 + 1` wall one endpoint of
the contracted target occurrence `t₁` is a leaf of the incoming target tree,
and above it the count of `LeafFacetNoReturn` isolates a single divalent source vertex that
every surviving occurrence over `t₁` meets
(`LeafFacetNoReturn.incident_of_leaf_fold`).  That is the only feature of the
leaf the rest of this module uses, so it is abstracted here; §6 produces it in
both leaf orientations.  It does not mention the Whitehead move, so it is
carried unchanged across the move `prescribedMove` builds. -/
structure LeafFold (w : WallData arr) where
  /-- the fold vertex, above the leaf -/
  vertex : w.cover.SourceVertex
  /-- it is divalent -/
  nd_eq : nonDanglingValency w.cover vertex = 2
  /-- every surviving occurrence over the contracted target occurrence meets it -/
  incident : ∀ e : NonDanglingEdge w.cover, e.1.1.1 = w.contracted →
    Incident w.cover e.1 vertex

end FoldDef

variable (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-! ## 1.  The two occurrences of the vanishing row, and its outer ends -/

section LeafPath

variable (F : LeafFold wd)

/-- The chosen occurrence of the vanishing row
(`NonTrivalentValencyTwoTracks.facetEdge`) meets the fold. -/
theorem incident_facetEdge_fold :
    Incident wd.cover (NonTrivalentValencyTwoTracks.facetEdge m wd).1 F.vertex :=
  F.incident _ (NonTrivalentValencyTwoTracks.facetEdge_over_contracted m wd)

theorem exists_secondEdge :
    ∃ e : NonDanglingEdge wd.cover, e ≠ NonTrivalentValencyTwoTracks.facetEdge m wd ∧
      Incident wd.cover e.1 F.vertex := by
  classical
  obtain ⟨other, hNe, hPair⟩ := nonDanglingIncident_eq_pair wd.cover F.nd_eq
    (NonTrivalentValencyTwoTracks.facetEdge m wd).2 (incident_facetEdge_fold m wd F)
  have hMem : other ∈ nonDanglingIncident wd.cover F.vertex := by
    rw [hPair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  exact ⟨⟨other, hSurv⟩, fun h ↦ hNe (congrArg Subtype.val h), hInc⟩

/-- **The second occurrence of the vanishing row**: the other surviving
occurrence at the fold. -/
def secondEdge : NonDanglingEdge wd.cover := Classical.choose (exists_secondEdge m wd F)

theorem secondEdge_ne_facetEdge :
    secondEdge m wd F ≠ NonTrivalentValencyTwoTracks.facetEdge m wd :=
  (Classical.choose_spec (exists_secondEdge m wd F)).1

theorem incident_secondEdge_fold : Incident wd.cover (secondEdge m wd F).1 F.vertex :=
  (Classical.choose_spec (exists_secondEdge m wd F)).2

theorem secondEdge_stablePath :
    (secondEdge m wd F).stablePath = NonTrivalentValencyTwoTracks.facetRow m wd :=
  (PrunedFibreStablePath.stablePath_eq_of_incident_divalent wd.cover (secondEdge m wd F)
    (NonTrivalentValencyTwoTracks.facetEdge m wd) F.vertex (incident_secondEdge_fold m wd F)
    (incident_facetEdge_fold m wd F) F.nd_eq).trans
    (NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd)

theorem secondEdge_over_contracted : (secondEdge m wd F).1.1.1 = wd.contracted :=
  NonTrivalentValencyTwoTracks.over_contracted_of_facetRow m wd _ (secondEdge_stablePath m wd F)

/-- **The vanishing row is exactly the pair of occurrences at the fold.** -/
theorem eq_facetEdge_or_eq_secondEdge (e : NonDanglingEdge wd.cover)
    (he : e.stablePath = NonTrivalentValencyTwoTracks.facetRow m wd) :
    e = NonTrivalentValencyTwoTracks.facetEdge m wd ∨ e = secondEdge m wd F := by
  classical
  have hInc : Incident wd.cover e.1 F.vertex :=
    F.incident e (NonTrivalentValencyTwoTracks.over_contracted_of_facetRow m wd e he)
  rcases eq_or_eq_of_nonDanglingValency_eq_two wd.cover F.nd_eq
      (NonTrivalentValencyTwoTracks.facetEdge m wd).2 (secondEdge m wd F).2
      (incident_facetEdge_fold m wd F) (incident_secondEdge_fold m wd F)
      (fun hBad ↦ secondEdge_ne_facetEdge m wd F (Subtype.ext hBad.symm)) e.2 hInc with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-! ### The two outer ends -/

open scoped Classical in
/-- The end of an occurrence away from the fold. -/
def outerEnd (e : NonDanglingEdge wd.cover) : wd.cover.SourceVertex :=
  if (wd.cover.sourceEnds e.1).1 = F.vertex then (wd.cover.sourceEnds e.1).2
  else (wd.cover.sourceEnds e.1).1

theorem outerEnd_of_fst (e : NonDanglingEdge wd.cover)
    (h : (wd.cover.sourceEnds e.1).1 = F.vertex) :
    outerEnd m wd F e = (wd.cover.sourceEnds e.1).2 := by
  unfold outerEnd
  rw [if_pos h]

theorem outerEnd_of_not_fst (e : NonDanglingEdge wd.cover)
    (h : (wd.cover.sourceEnds e.1).1 ≠ F.vertex) :
    outerEnd m wd F e = (wd.cover.sourceEnds e.1).1 := by
  unfold outerEnd
  rw [if_neg h]

theorem incident_outerEnd (e : NonDanglingEdge wd.cover) :
    Incident wd.cover e.1 (outerEnd m wd F e) := by
  by_cases h : (wd.cover.sourceEnds e.1).1 = F.vertex
  · rw [outerEnd_of_fst m wd F e h]; exact Or.inr rfl
  · rw [outerEnd_of_not_fst m wd F e h]; exact Or.inl rfl

theorem outerEnd_ne_fold (e : NonDanglingEdge wd.cover) :
    outerEnd m wd F e ≠ F.vertex := by
  by_cases h : (wd.cover.sourceEnds e.1).1 = F.vertex
  · rw [outerEnd_of_fst m wd F e h]
    exact fun hBad ↦ wd.cover.sourceEnds_ne e.1 (h.trans hBad.symm)
  · rw [outerEnd_of_not_fst m wd F e h]
    exact h

/-- An occurrence through the fold meets only the fold and its outer end. -/
theorem eq_fold_or_eq_outerEnd (e : NonDanglingEdge wd.cover)
    (hInc : Incident wd.cover e.1 F.vertex) (v : wd.cover.SourceVertex)
    (hv : Incident wd.cover e.1 v) : v = F.vertex ∨ v = outerEnd m wd F e := by
  by_cases h : (wd.cover.sourceEnds e.1).1 = F.vertex
  · rcases hv with hv | hv
    · exact Or.inl (hv.symm.trans h)
    · exact Or.inr ((hv.symm).trans (outerEnd_of_fst m wd F e h).symm)
  · have h2 : (wd.cover.sourceEnds e.1).2 = F.vertex := hInc.resolve_left h
    rcases hv with hv | hv
    · exact Or.inr ((hv.symm).trans (outerEnd_of_not_fst m wd F e h).symm)
    · exact Or.inl (hv.symm.trans h2)

/-- **The `A_u` end of the vanishing path**: the outer end of `facetEdge`. -/
def leftEnd : wd.cover.SourceVertex :=
  outerEnd m wd F (NonTrivalentValencyTwoTracks.facetEdge m wd)

/-- **The `A_v` end of the vanishing path**: the outer end of `secondEdge`. -/
def rightEnd : wd.cover.SourceVertex := outerEnd m wd F (secondEdge m wd F)

theorem incident_facetEdge_leftEnd :
    Incident wd.cover (NonTrivalentValencyTwoTracks.facetEdge m wd).1 (leftEnd m wd F) :=
  incident_outerEnd m wd F _

theorem incident_secondEdge_rightEnd :
    Incident wd.cover (secondEdge m wd F).1 (rightEnd m wd F) :=
  incident_outerEnd m wd F _

theorem leftEnd_ne_fold : leftEnd m wd F ≠ F.vertex := outerEnd_ne_fold m wd F _

theorem rightEnd_ne_fold : rightEnd m wd F ≠ F.vertex := outerEnd_ne_fold m wd F _

/-- **The two outer ends are distinct.**  If they coincided, every branch
vertex would see the vanishing row either twice or not at all, and the row
would have no simple end -- contradicting `InteriorGraphTracking.Tracks.hasSimpleEnd`
at the non-loop dart `m.base`. -/
theorem leftEnd_ne_rightEnd : leftEnd m wd F ≠ rightEnd m wd F := by
  classical
  intro hEq
  obtain ⟨u, hu⟩ := wd.tracks.hasSimpleEnd m.base m.nonloop
  have hu' : incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) = 1 := hu
  have hFoldNe : u.1 ≠ F.vertex := by
    intro hBad
    have h3 := u.2
    rw [hBad, F.nd_eq] at h3
    omega
  by_cases hU : u.1 = leftEnd m wd F
  · have hEqSet : (incidentEdges wd.cover u.1).filter
        (fun e ↦ e.stablePath = NonTrivalentValencyTwoTracks.facetRow m wd) =
        {NonTrivalentValencyTwoTracks.facetEdge m wd, secondEdge m wd F} := by
      ext e
      simp only [Finset.mem_filter, mem_incidentEdges, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hRow⟩
        exact eq_facetEdge_or_eq_secondEdge m wd F e hRow
      · rintro (rfl | rfl)
        · exact ⟨by rw [hU]; exact incident_facetEdge_leftEnd m wd F,
            NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd⟩
        · exact ⟨by rw [hU, hEq]; exact incident_secondEdge_rightEnd m wd F,
            secondEdge_stablePath m wd F⟩
    have hCard : incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) = 2 := by
      show ((incidentEdges wd.cover u.1).filter
        (fun e ↦ e.stablePath = NonTrivalentValencyTwoTracks.facetRow m wd)).card = 2
      rw [hEqSet, Finset.card_pair (fun hBad ↦ secondEdge_ne_facetEdge m wd F hBad.symm)]
    omega
  · have hEmpty : (incidentEdges wd.cover u.1).filter
        (fun e ↦ e.stablePath = NonTrivalentValencyTwoTracks.facetRow m wd) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun e he ↦ ?_)
      rw [Finset.mem_filter, mem_incidentEdges] at he
      obtain ⟨hInc, hRow⟩ := he
      rcases eq_facetEdge_or_eq_secondEdge m wd F e hRow with rfl | rfl
      · rcases eq_fold_or_eq_outerEnd m wd F (NonTrivalentValencyTwoTracks.facetEdge m wd)
          (incident_facetEdge_fold m wd F) u.1 hInc with h | h
        · exact hFoldNe h
        · exact hU h
      · rcases eq_fold_or_eq_outerEnd m wd F (secondEdge m wd F)
          (incident_secondEdge_fold m wd F) u.1 hInc with h | h
        · exact hFoldNe h
        · exact hU (h.trans hEq.symm)
    have hCard : incidenceCount wd.cover u.1 (NonTrivalentValencyTwoTracks.facetRow m wd) = 0 := by
      show ((incidentEdges wd.cover u.1).filter
        (fun e ↦ e.stablePath = NonTrivalentValencyTwoTracks.facetRow m wd)).card = 0
      rw [hEmpty, Finset.card_empty]
    omega

/-- The surviving valency at the outer end of an occurrence of the vanishing
row is at least three: a second surviving occurrence there would lie on the
vanishing row as well, hence be the other occurrence at the fold, forcing the
two outer ends to coincide. -/
theorem three_le_nonDanglingValency_outerEnd (e f : NonDanglingEdge wd.cover)
    (hIncF : Incident wd.cover f.1 F.vertex)
    (hRowE : e.stablePath = NonTrivalentValencyTwoTracks.facetRow m wd)
    (hExh : ∀ g : NonDanglingEdge wd.cover,
      g.stablePath = NonTrivalentValencyTwoTracks.facetRow m wd → g = e ∨ g = f)
    (hNe : outerEnd m wd F e ≠ outerEnd m wd F f) :
    3 ≤ nonDanglingValency wd.cover (outerEnd m wd F e) := by
  classical
  have hInc : Incident wd.cover e.1 (outerEnd m wd F e) := incident_outerEnd m wd F e
  have hZero := nonDanglingValency_ne_zero_of_incident wd.cover e.2 hInc
  have hOne := NonDanglingValency.nonDanglingValency_ne_one wd.cover wd.fullDim.connected
    (outerEnd m wd F e)
  have hTwo : nonDanglingValency wd.cover (outerEnd m wd F e) ≠ 2 := by
    intro hT
    obtain ⟨other, hNeO, hPair⟩ := nonDanglingIncident_eq_pair wd.cover hT e.2 hInc
    have hOtherMem : other ∈ nonDanglingIncident wd.cover (outerEnd m wd F e) := by
      rw [hPair]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨hOtherSurv, hOtherInc⟩ := (mem_nonDanglingIncident _ _ _).mp hOtherMem
    have hRow : NonDanglingEdge.stablePath (⟨other, hOtherSurv⟩ : NonDanglingEdge wd.cover) =
        NonTrivalentValencyTwoTracks.facetRow m wd :=
      (PrunedFibreStablePath.stablePath_eq_of_incident_divalent wd.cover ⟨other, hOtherSurv⟩ e
        (outerEnd m wd F e) hOtherInc hInc hT).trans hRowE
    rcases hExh _ hRow with h | h
    · exact hNeO (congrArg Subtype.val h)
    · have hIncW : Incident wd.cover f.1 (outerEnd m wd F e) := by
        rw [← congrArg Subtype.val h]
        exact hOtherInc
      rcases eq_fold_or_eq_outerEnd m wd F f hIncF (outerEnd m wd F e) hIncW with hc | hc
      · exact outerEnd_ne_fold m wd F e hc
      · exact hNe hc
  omega

/-- **The `A_u` end is a branch vertex.** -/
theorem three_le_nonDanglingValency_leftEnd :
    3 ≤ nonDanglingValency wd.cover (leftEnd m wd F) :=
  three_le_nonDanglingValency_outerEnd m wd F _ (secondEdge m wd F)
    (incident_secondEdge_fold m wd F)
    (NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd)
    (eq_facetEdge_or_eq_secondEdge m wd F) (leftEnd_ne_rightEnd m wd F)

/-- **The `A_v` end is a branch vertex.** -/
theorem three_le_nonDanglingValency_rightEnd :
    3 ≤ nonDanglingValency wd.cover (rightEnd m wd F) :=
  three_le_nonDanglingValency_outerEnd m wd F (secondEdge m wd F) _
    (incident_facetEdge_fold m wd F) (secondEdge_stablePath m wd F)
    (fun g hg ↦ (eq_facetEdge_or_eq_secondEdge m wd F g hg).symm)
    (leftEnd_ne_rightEnd m wd F).symm

/-! ### Both outer ends lie in the anchor fibre -/

/-- The outer end of an occurrence over the contracted target occurrence lies
in the same fibre as the fold. -/
theorem sourceVertexMap_outerEnd (e : NonDanglingEdge wd.cover)
    (he : e.1.1.1 = wd.contracted) :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (outerEnd m wd F e) =
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne F.vertex := by
  have h := sourceVertexMap_sourceEnds_eq_of_contracted wd.cover wd.hc wd.hab wd.hOne e.1 he
  by_cases hc : (wd.cover.sourceEnds e.1).1 = F.vertex
  · rw [outerEnd_of_fst m wd F e hc, ← h, hc]
  · have h2 : (wd.cover.sourceEnds e.1).2 = F.vertex := (F.incident e he).resolve_left hc
    rw [outerEnd_of_not_fst m wd F e hc, h, h2]

/-- The outer end of an occurrence over the contracted target occurrence lies
above one of the two contracted endpoints. -/
theorem outerEnd_target (e : NonDanglingEdge wd.cover) (he : e.1.1.1 = wd.contracted) :
    (outerEnd m wd F e).1.1 = wd.a ∨ (outerEnd m wd F e).1.1 = wd.b := by
  by_cases hc : (wd.cover.sourceEnds e.1).1 = F.vertex
  · refine Or.inr ?_
    rw [outerEnd_of_fst m wd F e hc]
    show (wd.cover.sourceEnds e.1).2.1.1 = wd.b
    rw [sourceEnds_snd_fst wd.cover e.1, he]
  · refine Or.inl ?_
    rw [outerEnd_of_not_fst m wd F e hc]
    show (wd.cover.sourceEnds e.1).1.1.1 = wd.a
    rw [sourceEnds_fst_fst wd.cover e.1, he]

theorem sourceVertexMap_leftEnd_eq_rightEnd :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd F) =
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (rightEnd m wd F) :=
  (sourceVertexMap_outerEnd m wd F _
      (NonTrivalentValencyTwoTracks.facetEdge_over_contracted m wd)).trans
    (sourceVertexMap_outerEnd m wd F _ (secondEdge_over_contracted m wd F)).symm

theorem leftEnd_mem_activeFibre :
    leftEnd m wd F ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd F)) :=
  (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ _).mpr
    ⟨rfl, by have := three_le_nonDanglingValency_leftEnd m wd F; omega⟩

theorem rightEnd_mem_activeFibre :
    rightEnd m wd F ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd F)) :=
  (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ _).mpr
    ⟨(sourceVertexMap_leftEnd_eq_rightEnd m wd F).symm,
      by have := three_le_nonDanglingValency_rightEnd m wd F; omega⟩

/-- **The fibre of the vanishing path is four-valent downstairs.**  The fold
contributes `0` to the fibre budget; the two outer ends contribute `1` each. -/
theorem four_le_nonDanglingValency_map_leftEnd :
    4 ≤ nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd F)) := by
  classical
  have hSum := WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre wd.cover wd.hc wd.hab
    wd.hOne (wd.hCompat m) (wd.hForest m)
    (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd F))
    ⟨leftEnd m wd F, leftEnd_mem_activeFibre m wd F⟩
  set fibre := activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
    (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd F)) with hfibre
  have hNonneg : ∀ u ∈ fibre, (0 : ℤ) ≤ (nonDanglingValency wd.cover u : ℤ) - 2 := by
    intro u hu
    have := WallSplitIncidence.two_le_nonDanglingValency_of_mem_activeFibre wd.cover wd.hc wd.hab
      wd.hOne wd.fullDim.connected _ u hu
    omega
  have hPair : ({leftEnd m wd F, rightEnd m wd F} : Finset wd.cover.SourceVertex) ⊆ fibre := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact leftEnd_mem_activeFibre m wd F
    · exact rightEnd_mem_activeFibre m wd F
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg hPair (fun u hu _ ↦ hNonneg u hu)
  rw [Finset.sum_pair (leftEnd_ne_rightEnd m wd F)] at hLe
  have hL := three_le_nonDanglingValency_leftEnd m wd F
  have hR := three_le_nonDanglingValency_rightEnd m wd F
  omega

end LeafPath

/-! ## 2.  The vertex dictionary from an abstract pair of anchor ends

§§2--4 of `NonTrivalentValencyTwoTracks` read the vertex dictionary off the two
ends of the vanishing occurrence.  Only six facts about that pair are used, and
they are true both at
a `2 + 2` wall (where the pair is the two ends of the single vanishing
occurrence) and at a leaf wall (where it is the two *outer* ends of the
vanishing path).  They are isolated here as `AnchorEnds`, so that one
dictionary -- and one star-count obligation -- serves all three incoming
sub-cases. -/

section Dictionary

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- **The two anchor ends of the vanishing row.**  `p` and `q` are distinct
branch vertices of the incoming cover, both lying over the anchor, and the
anchor fibre carries no other branch vertex. -/
def AnchorEnds
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (p q : wd.cover.SourceVertex) : Prop :=
  p ≠ q ∧ 3 ≤ nonDanglingValency wd.cover p ∧ 3 ≤ nonDanglingValency wd.cover q ∧
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne p =
        NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk ∧
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne q =
          NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk ∧
        ∀ u : wd.cover.SourceVertex,
          u ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
            (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) →
            3 ≤ nonDanglingValency wd.cover u → u = p ∨ u = q

variable {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {p q : wd.cover.SourceVertex}

/-- **The branch-vertex dictionary across the wall contraction.**
`NonTrivalentValencyTwoTracks.branchEquivAnchorComplement` with the vanishing
occurrence replaced by the abstract pair. -/
def branchEquivAnchorComplement
    (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlk)
    (hEnds : AnchorEnds m wd anchorBlk p q) :
    {v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q} ≃
      {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk} := by
  classical
  have hMapP := hEnds.2.2.2.1
  have hMapQ := hEnds.2.2.2.2.1
  have hOnly := hEnds.2.2.2.2.2
  have hNeAnchor : ∀ v : wd.cover.SourceVertex, 3 ≤ nonDanglingValency wd.cover v →
      v ≠ p → v ≠ q →
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v ≠
        NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk := by
    intro v hv hvp hvq hBad
    have hMem : v ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v).mpr ⟨hBad, by omega⟩
    rcases hOnly v hMem hv with h | h
    · exact hvp h
    · exact hvq h
  refine Equiv.ofBijective
    (fun v ↦ ⟨⟨sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1,
      WallSplitIncidence.three_le_nonDanglingValency_sourceVertexMap wd.cover wd.hc wd.hab wd.hOne
        (wd.hCompat m) (wd.hForest m) wd.fullDim.connected v.1.1 v.1.2⟩,
      hNeAnchor v.1.1 v.1.2 v.2.1 v.2.2⟩) ⟨?_, ?_⟩
  · intro v v' hEq
    have hMap : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1 =
        sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v'.1.1 :=
      congrArg (fun w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
        w.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk} ↦ w.1.1) hEq
    have hLe := NonTrivalentValencyTwoTracks.wallDatum_trivalent_away_anchor m wd hOrd
      (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1)
      (hNeAnchor v.1.1 v.1.2 v.2.1 v.2.2)
    have hMemV : v.1.1 ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v.1.1).mpr
        ⟨rfl, by have := v.1.2; omega⟩
    have hMemV' : v'.1.1 ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1) :=
      (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne _ v'.1.1).mpr
        ⟨hMap.symm, by have := v'.1.2; omega⟩
    exact Subtype.ext (Subtype.ext (WallSplitIncidence.eq_of_mem_activeFibre_of_three_le wd.cover
      wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) wd.fullDim.connected _ hLe v.1.1 v'.1.1
      hMemV hMemV' v.1.2 v'.1.2))
  · intro w
    obtain ⟨u, hu, hThree⟩ := WallSplitIncidence.exists_three_le_mem_activeFibre wd.cover wd.hc
      wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) w.1.1 w.1.2
    obtain ⟨hMapU, -⟩ := (mem_activeFibreVertices wd.cover wd.hc wd.hab wd.hOne w.1.1 u).mp hu
    have hup : u ≠ p := by
      intro hBad
      exact w.2 (by rw [← hMapU, hBad, hMapP])
    have huq : u ≠ q := by
      intro hBad
      exact w.2 (by rw [← hMapU, hBad, hMapQ])
    exact ⟨⟨⟨u, hThree⟩, hup, huq⟩, Subtype.ext (Subtype.ext hMapU)⟩

@[simp] theorem branchEquivAnchorComplement_apply
    (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlk)
    (hEnds : AnchorEnds m wd anchorBlk p q)
    (v : {v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q}) :
    (branchEquivAnchorComplement m wd hOrd hEnds v).1.1 =
      sourceVertexMap wd.cover wd.hc wd.hab wd.hOne v.1.1 := rfl

/-- The `A_u` end as a branch vertex. -/
def leftBranch (hEnds : AnchorEnds m wd anchorBlk p q) : BranchVertex wd.cover :=
  ⟨p, hEnds.2.1⟩

/-- The `A_v` end as a branch vertex. -/
def rightBranch (hEnds : AnchorEnds m wd anchorBlk p q) : BranchVertex wd.cover :=
  ⟨q, hEnds.2.2.1⟩

/-- The two anchor ends complete the branch vertices of the incoming cover. -/
def coverBranchMap (hEnds : AnchorEnds m wd anchorBlk p q) :
    ({v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q} ⊕ Bool) → BranchVertex wd.cover
  | Sum.inl v => v.1
  | Sum.inr side => if side then rightBranch m wd hEnds else leftBranch m wd hEnds

/-- The two anchor ends complete the branch vertices of the incoming cover. -/
def coverBranchEquiv (hEnds : AnchorEnds m wd anchorBlk p q) :
    ({v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q} ⊕ Bool) ≃ BranchVertex wd.cover := by
  classical
  refine Equiv.ofBijective (coverBranchMap m wd hEnds) ⟨?_, ?_⟩
  · rintro (v | side) (v' | side') hEq
    · exact congrArg Sum.inl (Subtype.ext hEq)
    · exfalso
      cases side' with
      | false => exact v.2.1 (congrArg Subtype.val hEq)
      | true => exact v.2.2 (congrArg Subtype.val hEq)
    · exfalso
      cases side with
      | false => exact v'.2.1 (congrArg Subtype.val hEq).symm
      | true => exact v'.2.2 (congrArg Subtype.val hEq).symm
    · cases side <;> cases side' <;> first
        | rfl
        | exact absurd (congrArg Subtype.val hEq) hEnds.1
        | exact absurd (congrArg Subtype.val hEq) hEnds.1.symm
  · intro u
    by_cases hl : u.1 = p
    · exact ⟨Sum.inr false, Subtype.ext hl.symm⟩
    · by_cases hr : u.1 = q
      · exact ⟨Sum.inr true, Subtype.ext hr.symm⟩
      · exact ⟨Sum.inl ⟨u, hl, hr⟩, rfl⟩

variable (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-- **The vertex dictionary of the valency-two Base II type change**, from the
abstract pair of anchor ends.  Away from the anchor it is the outgoing
vertex of the wall datum read back through the branch dictionary of the wall
contraction and the incoming tracking, as in `NonTrivalentValencyTwoTracks`; the
two anchor ends `A_u` and `A_v` go to `p` and `q`. -/
def vertexEquiv (hEnds : AnchorEnds m wd anchorBlk p q) :
    BranchVertex (Prescribed.validCandidate sel).datum ≃ V :=
  ((NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).symm.trans
    (Equiv.sumCongr (branchEquivAnchorComplement m wd hOrd hEnds).symm
      (Equiv.refl Bool))).trans
    ((coverBranchEquiv m wd hEnds).trans wd.tracks.iso.vtx)

@[simp] theorem vertexEquiv_inl (hEnds : AnchorEnds m wd anchorBlk p q)
    (w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
      w.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk}) :
    vertexEquiv m wd src sel hOrd hEnds
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inl w)) =
      wd.tracks.iso.vtx ((branchEquivAnchorComplement m wd hOrd hEnds).symm w).1 := by
  have h : (NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).symm
      (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inl w)) = Sum.inl w :=
    (NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).symm_apply_apply (Sum.inl w)
  show wd.tracks.iso.vtx (coverBranchMap m wd hEnds
    (Equiv.sumCongr (branchEquivAnchorComplement m wd hOrd hEnds).symm (Equiv.refl Bool)
      ((NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).symm
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inl w))))) = _
  rw [h]
  rfl

@[simp] theorem vertexEquiv_anchor (hEnds : AnchorEnds m wd anchorBlk p q) (side : Bool) :
    vertexEquiv m wd src sel hOrd hEnds
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr side)) =
      wd.tracks.iso.vtx (if side then rightBranch m wd hEnds else leftBranch m wd hEnds) := by
  have h : (NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).symm
      (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr side)) =
      Sum.inr side :=
    (NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).symm_apply_apply
      (Sum.inr side)
  show wd.tracks.iso.vtx (coverBranchMap m wd hEnds
    (Equiv.sumCongr (branchEquivAnchorComplement m wd hOrd hEnds).symm (Equiv.refl Bool)
      ((NonTrivalentValencyTwoTracks.candBranchEquiv m wd src sel hOrd).symm
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr side))))) = _
  rw [h]
  rfl

end Dictionary

/-! ## 3.  The leaf wall satisfies `AnchorEnds` -/

section LeafAnchor

variable (F : LeafFold wd)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- **The vanishing path lies over the anchor.** -/
theorem sourceVertexMap_leftEnd_eq_anchorVertex
    (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlk) :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd F) =
      NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk := by
  classical
  have hMap : sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (leftEnd m wd F) =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
        (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)
        (leftEnd m wd F).1.2 := by
    show (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEndpoint
      (GraphContraction.fold wd.coverTarget wd.hab (leftEnd m wd F).1.1)
        (leftEnd m wd F).1.2 = _
    rcases outerEnd_target m wd F _
        (NonTrivalentValencyTwoTracks.facetEdge_over_contracted m wd) with h | h
    · rw [show (leftEnd m wd F).1.1 = wd.a from h, GraphContraction.fold_a]
    · rw [show (leftEnd m wd F).1.1 = wd.b from h, GraphContraction.fold_self]
  have hFour := four_le_nonDanglingValency_map_leftEnd m wd F
  rw [hMap] at hFour
  by_cases hRel : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      (⟨wd.a, wd.hab⟩ : GraphContraction.Vertex wd.coverTarget wd.b)).Rel anchorBlk.1
        (leftEnd m wd F).1.2
  · rw [hMap]
    exact (NonTrivalentValencyTwoRowEquiv.sourceEndpoint_eq_of_rel hRel).symm
  · exact absurd (hOrd (leftEnd m wd F).1.2 hRel) (by omega)

theorem sourceVertexMap_rightEnd_eq_anchorVertex
    (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlk) :
    sourceVertexMap wd.cover wd.hc wd.hab wd.hOne (rightEnd m wd F) =
      NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk :=
  (sourceVertexMap_leftEnd_eq_rightEnd m wd F).symm.trans
    (sourceVertexMap_leftEnd_eq_anchorVertex m wd F hOrd)

/-- **The anchor fibre carries exactly the two outer ends as branch
vertices.**  The fibre budget `nd(A) = 4 = 2 + Σ (nd V - 2)`, with the
divalent fold contributing `0`. -/
theorem eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlk)
    (u : wd.cover.SourceVertex)
    (hu : u ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hThree : 3 ≤ nonDanglingValency wd.cover u) :
    u = leftEnd m wd F ∨ u = rightEnd m wd F := by
  classical
  by_contra hBad
  obtain ⟨hBadL, hBadR⟩ := not_or.mp hBad
  have hSum := WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre wd.cover wd.hc wd.hab
    wd.hOne (wd.hCompat m) (wd.hForest m)
    (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) ⟨u, hu⟩
  rw [NonTrivalentValencyTwoTracks.nonDanglingValency_anchorVertex m wd src] at hSum
  have hL : leftEnd m wd F ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) := by
    rw [← sourceVertexMap_leftEnd_eq_anchorVertex m wd F hOrd]
    exact leftEnd_mem_activeFibre m wd F
  have hR : rightEnd m wd F ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) := by
    rw [← sourceVertexMap_leftEnd_eq_anchorVertex m wd F hOrd]
    exact rightEnd_mem_activeFibre m wd F
  have hNonneg : ∀ w ∈ activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk),
      (0 : ℤ) ≤ (nonDanglingValency wd.cover w : ℤ) - 2 := by
    intro w hw
    have := WallSplitIncidence.two_le_nonDanglingValency_of_mem_activeFibre wd.cover wd.hc wd.hab
      wd.hOne wd.fullDim.connected _ w hw
    omega
  have hTriple : ({leftEnd m wd F, rightEnd m wd F, u} : Finset wd.cover.SourceVertex) ⊆
      activeFibreVertices wd.cover wd.hc wd.hab wd.hOne
        (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hL
    · exact hR
    · exact hu
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg hTriple (fun w hw _ ↦ hNonneg w hw)
  rw [show ({leftEnd m wd F, rightEnd m wd F, u} : Finset wd.cover.SourceVertex) =
      insert (leftEnd m wd F) {rightEnd m wd F, u} from rfl,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨leftEnd_ne_rightEnd m wd F, fun h ↦ hBadL h.symm⟩),
    Finset.sum_pair (fun h ↦ hBadR h.symm)] at hLe
  have hLv := three_le_nonDanglingValency_leftEnd m wd F
  have hRv := three_le_nonDanglingValency_rightEnd m wd F
  omega

/-- **The leaf wall's anchor ends.** -/
theorem anchorEnds_leaf
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
      anchorBlk) :
    AnchorEnds m wd anchorBlk (leftEnd m wd F) (rightEnd m wd F) :=
  ⟨leftEnd_ne_rightEnd m wd F, three_le_nonDanglingValency_leftEnd m wd F,
    three_le_nonDanglingValency_rightEnd m wd F,
    sourceVertexMap_leftEnd_eq_anchorVertex m wd F hOrd,
    sourceVertexMap_rightEnd_eq_anchorVertex m wd F hOrd,
    eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre m wd F src hOrd⟩

end LeafAnchor

/-! ## 4.  (H-II) at a leaf wall -/

section Prescribed

variable (F : LeafFold wd)

/-- **The dart of the outer occurrence at the `A_u` end.**  At a leaf wall the
vanishing row is a path of two occurrences, and the dart (H-II) names is the
one of the *outer* occurrence there -- `NonTrivalentValencyTwoTracks.facetDartLeft` with the
single vanishing occurrence replaced by the occurrence of the path that meets
`A_u`. -/
def facetDartLeft : StableSourceDarts.Dart wd.cover :=
  ⟨⟨leftEnd m wd F, three_le_nonDanglingValency_leftEnd m wd F⟩,
    ⟨NonTrivalentValencyTwoTracks.facetEdge m wd, incident_facetEdge_leftEnd m wd F⟩⟩

/-- **The dart of the outer occurrence at the `A_v` end.** -/
def facetDartRight : StableSourceDarts.Dart wd.cover :=
  ⟨⟨rightEnd m wd F, three_le_nonDanglingValency_rightEnd m wd F⟩,
    ⟨secondEdge m wd F, incident_secondEdge_rightEnd m wd F⟩⟩

theorem facetDartLeft_ne_facetDartRight : facetDartRight m wd F ≠ facetDartLeft m wd F := by
  intro hBad
  exact (leftEnd_ne_rightEnd m wd F)
    (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad).symm

/-- **The two outer darts of the vanishing path are opposite**: they carry the
same stable row and are distinct. -/
theorem opposite_facetDartLeft :
    StableSourceDarts.opposite wd.cover wd.fullDim.connected wd.fullDim.pathEnds
        (facetDartLeft m wd F) = facetDartRight m wd F :=
  (StableSourceDarts.opposite_eq_of_row_eq wd.cover wd.fullDim.connected wd.fullDim.pathEnds
    (d := facetDartLeft m wd F) (e := facetDartRight m wd F)
    ((secondEdge_stablePath m wd F).trans
      (NonTrivalentValencyTwoTracks.facetEdge_stablePath m wd).symm)
    (facetDartLeft_ne_facetDartRight m wd F)).symm

/-- **Under (H-II) the `A_u` end sits at `graph.vert m.base`.** -/
theorem vert_base_eq (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base) :
    graph.vert m.base = wd.tracks.iso.vtx (facetDartLeft m wd F).1 := by
  have h := wd.tracks.iso.vert_map (facetDartLeft m wd F)
  rw [hBase] at h
  exact h

theorem op_base_eq (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base) :
    graph.op m.base = wd.tracks.iso.dart (facetDartRight m wd F) := by
  have h2 := wd.tracks.iso.op_map (facetDartLeft m wd F)
  have h3 : (StableSourceDarts.ofDatum wd.cover wd.fullDim.connected wd.fullDim.trivalent
      wd.fullDim.pathEnds).op (facetDartLeft m wd F) = facetDartRight m wd F :=
    opposite_facetDartLeft m wd F
  rw [hBase, h3] at h2
  exact h2

/-- **Under (H-II) the `A_v` end sits at `graph.vert (graph.op m.base)`.** -/
theorem vert_opBase_eq (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base) :
    graph.op m.base = wd.tracks.iso.dart (facetDartRight m wd F) ∧
      graph.vert (graph.op m.base) = wd.tracks.iso.vtx (facetDartRight m wd F).1 := by
  refine ⟨op_base_eq m wd F hBase, ?_⟩
  rw [op_base_eq m wd F hBase]
  exact wd.tracks.iso.vert_map (facetDartRight m wd F)

section Merged

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)

/-- Neither merged survivor lies on the vanishing row. -/
theorem stablePath_selectedLift_ne_facetRow (side : Bool) :
    (NonTrivalentValencyTwoTracks.selectedLift m wd sel side).stablePath ≠
      NonTrivalentValencyTwoTracks.facetRow m wd := by
  intro hBad
  refine incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
    (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    (NonDanglingEdge.stablePath (if side then
      (⟨(Prescribed.secondSelected sel).1,
          NonTrivalentValencyTwoTracks.secondSelected_survives m wd sel⟩ :
        NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      else ⟨(Prescribed.firstSelected sel).1,
        NonTrivalentValencyTwoTracks.firstSelected_survives m wd sel⟩)) ?_
  rw [← NonTrivalentValencyTwoTracks.stablePath_liftEdge m wd]
  exact hBad

theorem secondEdge_ne_selectedLift (side : Bool) :
    (secondEdge m wd F).1 ≠ (NonTrivalentValencyTwoTracks.selectedLift m wd sel side).1 := by
  intro hBad
  refine stablePath_selectedLift_ne_facetRow m wd sel side ?_
  rw [show NonTrivalentValencyTwoTracks.selectedLift m wd sel side = secondEdge m wd F from
    Subtype.ext hBad.symm]
  exact secondEdge_stablePath m wd F

/-- **(H-II) at a leaf wall.**  The two darts that the Whitehead move `m` places
together with `m.base` are the darts of the two merged survivors, in the
orientation that puts `A_u` -- the outer end of the vanishing path at which
`m.base` sits -- at `graph.vert m.base`.  The first conjunct is the orientation:
`m.base` is the dart of the **outer** occurrence of the vanishing path at the
`A_u` end.  The survivor clause is that of `NonTrivalentValencyTwoTracks`
verbatim, hence at the level of
stable **rows**: the two darts carry the rows of the two merged survivors, which
is what the star count consumes
(`NonTrivalentValencyTwoStarCount.label_dart_merged`, through
`IncomingPairing.label_dart_of_row`). -/
def PrescribedMergedMoveLeaf : Prop :=
  wd.tracks.iso.dart (facetDartLeft m wd F) = m.base ∧
    ∃ first second : StableSourceDarts.Dart wd.cover,
      first.2.1.stablePath =
          (NonTrivalentValencyTwoTracks.selectedLift m wd sel false).stablePath ∧
        second.2.1.stablePath =
            (NonTrivalentValencyTwoTracks.selectedLift m wd sel true).stablePath ∧
          (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
            {wd.tracks.iso.dart first, wd.tracks.iso.dart second}

/-- **The occurrence-level clause implies (H-II) at a leaf wall.**  The
occurrence-level form of the condition is strictly stronger than the row-level
one; the converse fails wherever a merged survivor reaches its outer end through
a pass-through occurrence over the contracted target edge.  At a `1 + 3` wall
all four survivors are in fact direct, so here the two forms are equally
satisfiable -- the row-level form keeps this file's clause literally that of
`NonTrivalentValencyTwoTracks`. -/
theorem prescribedMergedMoveLeaf_of_occurrence
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base)
    (first second : StableSourceDarts.Dart wd.cover)
    (hFirst : first.2.1 = NonTrivalentValencyTwoTracks.selectedLift m wd sel false)
    (hSecond : second.2.1 = NonTrivalentValencyTwoTracks.selectedLift m wd sel true)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart first, wd.tracks.iso.dart second}) :
    PrescribedMergedMoveLeaf m wd F sel :=
  ⟨hBase, first, second, by rw [hFirst], by rw [hSecond], hStar⟩

/-- **(H-II) at a leaf wall from the orientation clause and two moved darts
carrying the two merged rows.**  The shape the valency dispatcher consumes: the
two darts come from `IncomingPairing.exists_movedStar_darts`, which also says
that one sits at each end of the vanishing path, so no separation hypothesis is
needed here.  For the other order of the pair, apply it to `y`, `x` after
`Finset.pair_comm`. -/
theorem prescribedMergedMoveLeaf_of_rows
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base)
    (x y : StableSourceDarts.Dart wd.cover)
    (hx : x.2.1.stablePath =
      (NonTrivalentValencyTwoTracks.selectedLift m wd sel false).stablePath)
    (hy : y.2.1.stablePath =
      (NonTrivalentValencyTwoTracks.selectedLift m wd sel true).stablePath)
    (hStar : (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart x, wd.tracks.iso.dart y}) :
    PrescribedMergedMoveLeaf m wd F sel :=
  ⟨hBase, x, y, hx, hy, hStar⟩

/-- **The geometric content of a type change at a leaf wall**: the two merged
survivors lift to occurrences at the two *different* outer ends of the
vanishing path. -/
def MergedSeparatedLeaf : Prop :=
  Incident wd.cover (NonTrivalentValencyTwoTracks.selectedLift m wd sel false).1
      (leftEnd m wd F) ∧
    Incident wd.cover (NonTrivalentValencyTwoTracks.selectedLift m wd sel true).1
      (rightEnd m wd F)

/-- A third surviving occurrence at the `A_u` end, distinct from the outer
occurrence of the vanishing path and from the merged survivor there. -/
theorem exists_thirdEdge (hSep : MergedSeparatedLeaf m wd F sel) :
    ∃ e : NonDanglingEdge wd.cover, Incident wd.cover e.1 (leftEnd m wd F) ∧
      e ≠ NonTrivalentValencyTwoTracks.facetEdge m wd ∧
      e ≠ NonTrivalentValencyTwoTracks.selectedLift m wd sel false := by
  classical
  have hNd : nonDanglingValency wd.cover (leftEnd m wd F) = 3 := by
    have h1 := three_le_nonDanglingValency_leftEnd m wd F
    have h2 : nonDanglingValency wd.cover (leftEnd m wd F) ≤ 3 :=
      wd.fullDim.trivalent (leftEnd m wd F)
    omega
  have hNe := NonTrivalentValencyTwoTracks.facetEdge_ne_selectedLift m wd sel false
  set pair : Finset wd.cover.SourceEdge :=
    {(NonTrivalentValencyTwoTracks.facetEdge m wd).1,
      (NonTrivalentValencyTwoTracks.selectedLift m wd sel false).1} with hpair
  have hsub : pair ⊆ nonDanglingIncident wd.cover (leftEnd m wd F) := by
    intro e he
    rw [hpair] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(NonTrivalentValencyTwoTracks.facetEdge m wd).2, incident_facetEdge_leftEnd m wd F⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(NonTrivalentValencyTwoTracks.selectedLift m wd sel false).2, hSep.1⟩
  have hcard : (nonDanglingIncident wd.cover (leftEnd m wd F) \ pair).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_nonDanglingIncident, hNd, hpair,
      Finset.card_pair hNe]
  obtain ⟨e, he⟩ := Finset.card_pos.mp
    (by omega : 0 < (nonDanglingIncident wd.cover (leftEnd m wd F) \ pair).card)
  rw [Finset.mem_sdiff, hpair] at he
  obtain ⟨hMem, hNotMem⟩ := he
  obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hNotMem
  exact ⟨⟨e, hSurv⟩, hInc, fun h ↦ hNotMem (Or.inl (congrArg Subtype.val h)),
    fun h ↦ hNotMem (Or.inr (congrArg Subtype.val h))⟩

/-- The third occurrence at the `A_u` end. -/
def thirdEdge (hSep : MergedSeparatedLeaf m wd F sel) : NonDanglingEdge wd.cover :=
  Classical.choose (exists_thirdEdge m wd F sel hSep)

theorem thirdEdge_spec (hSep : MergedSeparatedLeaf m wd F sel) :
    Incident wd.cover (thirdEdge m wd F sel hSep).1 (leftEnd m wd F) ∧
      thirdEdge m wd F sel hSep ≠ NonTrivalentValencyTwoTracks.facetEdge m wd ∧
      thirdEdge m wd F sel hSep ≠ NonTrivalentValencyTwoTracks.selectedLift m wd sel false :=
  Classical.choose_spec (exists_thirdEdge m wd F sel hSep)

/-- The dart of the merged survivor at the `A_u` end. -/
def selectedDartLeft (hSep : MergedSeparatedLeaf m wd F sel) : StableSourceDarts.Dart wd.cover :=
  ⟨⟨leftEnd m wd F, three_le_nonDanglingValency_leftEnd m wd F⟩,
    ⟨NonTrivalentValencyTwoTracks.selectedLift m wd sel false, hSep.1⟩⟩

/-- The dart of the merged survivor at the `A_v` end. -/
def selectedDartRight (hSep : MergedSeparatedLeaf m wd F sel) : StableSourceDarts.Dart wd.cover :=
  ⟨⟨rightEnd m wd F, three_le_nonDanglingValency_rightEnd m wd F⟩,
    ⟨NonTrivalentValencyTwoTracks.selectedLift m wd sel true, hSep.2⟩⟩

/-- The remaining dart at the `A_u` end. -/
def thirdDart (hSep : MergedSeparatedLeaf m wd F sel) : StableSourceDarts.Dart wd.cover :=
  ⟨⟨leftEnd m wd F, three_le_nonDanglingValency_leftEnd m wd F⟩,
    ⟨thirdEdge m wd F sel hSep, (thirdEdge_spec m wd F sel hSep).1⟩⟩

/-- **The Whitehead move prescribed by the merged pair at a leaf wall.** -/
def prescribedMove (hSep : MergedSeparatedLeaf m wd F sel)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base) : graph.MoveData where
  base := m.base
  left := wd.tracks.iso.dart (thirdDart m wd F sel hSep)
  right := wd.tracks.iso.dart (selectedDartRight m wd F sel hSep)
  nonloop := m.nonloop
  left_vert := (wd.tracks.iso.vert_map (thirdDart m wd F sel hSep)).trans
    (vert_base_eq m wd F hBase).symm
  left_ne := by
    intro hBad
    exact (thirdEdge_spec m wd F sel hSep).2.1
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1)
        (wd.tracks.iso.dart.injective (hBad.trans hBase.symm)))
  right_vert := (wd.tracks.iso.vert_map (selectedDartRight m wd F sel hSep)).trans
    (vert_opBase_eq m wd F hBase).2.symm
  right_ne := by
    intro hBad
    exact (secondEdge_ne_selectedLift m wd F sel true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBad.trans (op_base_eq m wd F hBase)))).symm

/-- **Non-vacuity of (H-II) at a leaf wall, in relative form.** -/
theorem prescribedMergedMove_prescribedMove (hSep : MergedSeparatedLeaf m wd F sel)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base) :
    PrescribedMergedMoveLeaf (prescribedMove m wd F sel hSep hBase) wd F sel := by
  classical
  set m' := prescribedMove m wd F sel hSep hBase with hm'
  set dLeft := selectedDartLeft m wd F sel hSep with hdLeft
  set dRight := selectedDartRight m wd F sel hSep with hdRight
  have hLeftNeRight : dLeft ≠ dRight := by
    intro hBad
    exact (leftEnd_ne_rightEnd m wd F)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.1.1) hBad)
  have hLeftNeThird : dLeft ≠ thirdDart m wd F sel hSep := by
    intro hBad
    exact (thirdEdge_spec m wd F sel hSep).2.2
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1) hBad).symm
  have hBaseNeLeft : m.base ≠ wd.tracks.iso.dart dLeft := by
    intro hBad
    exact (NonTrivalentValencyTwoTracks.facetEdge_ne_selectedLift m wd sel false)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBase.trans hBad)))
  have hBaseNeRight : m.base ≠ wd.tracks.iso.dart dRight := by
    intro hBad
    exact (NonTrivalentValencyTwoTracks.facetEdge_ne_selectedLift m wd sel true)
      (congrArg (fun d : StableSourceDarts.Dart wd.cover ↦ d.2.1.1)
        (wd.tracks.iso.dart.injective (hBase.trans hBad)))
  refine ⟨hBase, dLeft, dRight, rfl, rfl, ?_⟩
  have hStar : (Finset.univ.filter fun d ↦ (graph.move m').vert d = graph.vert m.base) =
      {m.base, wd.tracks.iso.dart dRight, wd.tracks.iso.dart dLeft} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hd with rfl | rfl | rfl
      · exact congrArg graph.vert m'.perm_base
      · exact (congrArg graph.vert m'.perm_right).trans m'.left_vert
      · have h1 : wd.tracks.iso.dart dLeft ≠ m'.left :=
          fun hBad ↦ hLeftNeThird (wd.tracks.iso.dart.injective hBad)
        have h2 : wd.tracks.iso.dart dLeft ≠ m'.right :=
          fun hBad ↦ hLeftNeRight (wd.tracks.iso.dart.injective hBad)
        show graph.vert (m'.perm (wd.tracks.iso.dart dLeft)) = graph.vert m.base
        rw [m'.perm_of_ne h1 h2, wd.tracks.iso.vert_map dLeft, vert_base_eq m wd F hBase]
        rfl
    · rw [(graph.move m').card_fibre (graph.vert m.base)]
      exact le_of_eq (Finset.card_eq_three.mpr ⟨_, _, _, hBaseNeRight, hBaseNeLeft,
        fun hBad ↦ hLeftNeRight (wd.tracks.iso.dart.injective hBad).symm, rfl⟩).symm
  show (Finset.univ.filter fun d ↦ (graph.move m').vert d = graph.vert m.base).erase m.base =
    {wd.tracks.iso.dart dLeft, wd.tracks.iso.dart dRight}
  rw [hStar, Finset.erase_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨hBaseNeRight, hBaseNeLeft⟩), Finset.pair_comm]

end Merged

end Prescribed

/-! ### The off-wall half of the star count -/

section OffWall

variable (F : LeafFold wd)

/-- **Away from the two outer ends of the vanishing path the Whitehead move
does not change the star.**  `move_vert_eq_iff_of_ne` and
`card_star_eq_incidenceCount` (§6 of `NonTrivalentValencyTwoTracks`) -- neither
of which mentions a no-return
hypothesis, so both are reused verbatim -- combined at a leaf wall through
(H-II)'s orientation.  This is the half of `hIncidence` that is geometric only
through the incoming tracking. -/
theorem card_star_move_eq_incidenceCount
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base)
    (u : BranchVertex wd.cover) (hLeft : u.1 ≠ leftEnd m wd F)
    (hRight : u.1 ≠ rightEnd m wd F) (row : StablePath wd.cover) :
    incidenceCount wd.cover u.1 row =
      Nat.card {d : D // graph.vert (m.perm d) = wd.tracks.iso.vtx u ∧
        label d = wd.fullDim.labelling.row row} := by
  have hNeBase : wd.tracks.iso.vtx u ≠ graph.vert m.base := by
    rw [vert_base_eq m wd F hBase]
    intro hBad
    exact hLeft (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  have hNeOp : wd.tracks.iso.vtx u ≠ graph.vert (graph.op m.base) := by
    rw [(vert_opBase_eq m wd F hBase).2]
    intro hBad
    exact hRight (congrArg Subtype.val (wd.tracks.iso.vtx.injective hBad))
  refine (NonTrivalentValencyTwoTracks.card_star_eq_incidenceCount m wd u row).trans
    (Nat.card_congr (Equiv.subtypeEquivRight fun d ↦ ?_))
  constructor
  · rintro ⟨hv, hr⟩
    exact ⟨(NonTrivalentValencyTwoTracks.move_vert_eq_iff_of_ne m hNeBase hNeOp d).mpr hv, hr⟩
  · rintro ⟨hv, hr⟩
    exact ⟨(NonTrivalentValencyTwoTracks.move_vert_eq_iff_of_ne m hNeBase hNeOp d).mp hv, hr⟩

end OffWall

/-! ## 5.  Orientation, and the link reduced to the star count -/

section Link

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

/-- **`A_u` goes to `graph.vert m.base`** under (H-II) at a leaf wall. -/
theorem vertexEquiv_anchor_false (F : LeafFold wd)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base) :
    vertexEquiv m wd src sel hOrd (anchorEnds_leaf m wd F src hOrd)
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr false)) =
      graph.vert m.base := by
  rw [vertexEquiv_anchor m wd src sel hOrd (anchorEnds_leaf m wd F src hOrd) false,
    vert_base_eq m wd F hBase]
  rfl

/-- **`A_v` goes to `graph.vert (graph.op m.base)`** under (H-II) at a leaf wall. -/
theorem vertexEquiv_anchor_true (F : LeafFold wd)
    (hBase : wd.tracks.iso.dart (facetDartLeft m wd F) = m.base) :
    vertexEquiv m wd src sel hOrd (anchorEnds_leaf m wd F src hOrd)
        (NonTrivalentValencyTwoTracks.candBranchMap m wd src sel hOrd (Sum.inr true)) =
      graph.vert (graph.op m.base) := by
  rw [vertexEquiv_anchor m wd src sel hOrd (anchorEnds_leaf m wd F src hOrd) true,
    (vert_opBase_eq m wd F hBase).2]
  rfl

variable (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (hRowVal : ∀ pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row pth).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)))
  (hMatrixWall : ∀ (pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row pth) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)) column.1)

variable {p q : wd.cover.SourceVertex}

/-- **`OuterWalk.TypeChangeLink` at a two-valent Base II wall from the star
count alone, with no no-return hypothesis.**
`NonTrivalentValencyTwoExitFree.wallOutgoingFD'` supplies the outgoing
presentation at every incoming sub-case; this file's `vertexEquiv` supplies the
branch-vertex bijection; exactly one geometric input, `hIncidence`, is left. -/
def typeChangeLink_of_incidence (hEnds : AnchorEnds m wd anchorBlk p q)
    (hIncidence : ∀ (v : BranchVertex (Prescribed.validCandidate sel).datum)
        (r : StablePath (Prescribed.validCandidate sel).datum),
      incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) = vertexEquiv m wd src sel hOrd hEnds v ∧
          label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
            hRowVal hMatrixWall).labelling.row r}) :
    TypeChangeLink m wd :=
  NonTrivalentValencyTwoExitFree.typeChangeLink_of_receipts_free m wd src sel hOrd labelling₀
    hRowVal hMatrixWall
    (MovedIncidenceIso.tracksOfMovedIncidence _ _ graph m label
      (vertexEquiv m wd src sel hOrd hEnds)
      (MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks) hIncidence)

/-- **The link at a leaf wall**, from the star count against this file's
`vertexEquiv` at the leaf anchor ends. -/
def typeChangeLink_of_incidence_leaf (F : LeafFold wd)
    (hIncidence : ∀ (v : BranchVertex (Prescribed.validCandidate sel).datum)
        (r : StablePath (Prescribed.validCandidate sel).datum),
      incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
        Nat.card {d : D // graph.vert (m.perm d) =
            vertexEquiv m wd src sel hOrd (anchorEnds_leaf m wd F src hOrd) v ∧
          label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀
            hRowVal hMatrixWall).labelling.row r}) :
    TypeChangeLink m wd :=
  typeChangeLink_of_incidence m wd src sel hOrd labelling₀ hRowVal hMatrixWall
    (anchorEnds_leaf m wd F src hOrd) hIncidence

end Link

/-! ## 6.  Producers, and the dispatcher over the incoming trichotomy -/

section Producers

/-- **Above a target leaf an active source vertex is divalent.**  The count
behind `LeafFacetNoReturn` (`StableLocalProperties.leaf_block_dichotomy`: above a change-minimal
leaf every block is a single sheet with one incident occurrence, except for one
two-sheet block with two) read as a valency statement, using
`NonDanglingValency.nonDanglingValency_ne_one`. -/
theorem nonDanglingValency_eq_two_of_leaf {tgt : CFGraph} {deg : ℕ}
    (data : GluingDatum tgt deg)
    (fd : FullDimensionalSourcePresentation data coordinate) (v : data.SourceVertex)
    (hLeaf : (GluingDatum.incidentEdges v.1.1).card = 1)
    (hActive : nonDanglingValency data v ≠ 0) :
    nonDanglingValency data v = 2 := by
  classical
  have hDich := StableLocalProperties.leaf_block_dichotomy data fd.valid
    fd.noDanglingTargetFibres v.1.1 hLeaf (fd.changeMinimal v.1.1)
    (⟨v.1.2, v.2⟩ : (data.vertexPartition v.1.1).Blocks)
  have hBlock : StableLocalProperties.blockVertex data v.1.1
      (⟨v.1.2, v.2⟩ : (data.vertexPartition v.1.1).Blocks) = v := rfl
  rw [hBlock] at hDich
  have hOne := NonDanglingValency.nonDanglingValency_ne_one data fd.connected v
  have hLe := LeafFacetNoReturn.nonDanglingValency_le_card_incidentSourceEdge data v
  rcases hDich with ⟨hCard, -, -⟩ | ⟨hCard, -, -, -⟩ <;> rw [hCard] at hLe <;> omega

/-! ### The fold at a `1 + 3` wall (`u = a` a leaf) -/

theorem foldLeft_above :
    ((wd.cover.sourceEnds (NonTrivalentValencyTwoTracks.facetEdge m wd).1).1).1.1 = wd.a := by
  show (wd.cover.sourceEnds (NonTrivalentValencyTwoTracks.facetEdge m wd).1).1.1.1 = wd.a
  rw [sourceEnds_fst_fst wd.cover (NonTrivalentValencyTwoTracks.facetEdge m wd).1,
    NonTrivalentValencyTwoTracks.facetEdge_over_contracted m wd]

theorem foldLeft_nd
    (hLeaf : (GluingDatum.incidentEdges (target := wd.coverTarget) wd.a).card = 1) :
    nonDanglingValency wd.cover
      (wd.cover.sourceEnds (NonTrivalentValencyTwoTracks.facetEdge m wd).1).1 = 2 := by
  refine nonDanglingValency_eq_two_of_leaf wd.cover wd.fullDim _ ?_ ?_
  · rw [foldLeft_above m wd]
    exact hLeaf
  · exact nonDanglingValency_ne_zero_of_incident wd.cover
      (NonTrivalentValencyTwoTracks.facetEdge m wd).2
      (incident_left wd.cover (NonTrivalentValencyTwoTracks.facetEdge m wd).1)

/-- **The fold at a `1 + 3` wall.** -/
def leafFold_of_leaf_left
    (hLeaf : (GluingDatum.incidentEdges (target := wd.coverTarget) wd.a).card = 1) :
    LeafFold wd where
  vertex := (wd.cover.sourceEnds (NonTrivalentValencyTwoTracks.facetEdge m wd).1).1
  nd_eq := foldLeft_nd m wd hLeaf
  incident := fun e he ↦
    LeafFacetNoReturn.incident_of_leaf_fold wd.cover wd.fullDim (a := wd.a)
      (contracted := wd.contracted) rfl _ (foldLeft_above m wd) hLeaf (foldLeft_nd m wd hLeaf)
      e.1 he e.2

/-! ### The fold at a `3 + 1` wall (`v = b` a leaf) -/

theorem foldRight_above :
    ((wd.cover.sourceEnds (NonTrivalentValencyTwoTracks.facetEdge m wd).1).2).1.1 = wd.b := by
  show (wd.cover.sourceEnds (NonTrivalentValencyTwoTracks.facetEdge m wd).1).2.1.1 = wd.b
  rw [sourceEnds_snd_fst wd.cover (NonTrivalentValencyTwoTracks.facetEdge m wd).1,
    NonTrivalentValencyTwoTracks.facetEdge_over_contracted m wd]

theorem foldRight_nd
    (hLeaf : (GluingDatum.incidentEdges (target := wd.coverTarget) wd.b).card = 1) :
    nonDanglingValency wd.cover
      (wd.cover.sourceEnds (NonTrivalentValencyTwoTracks.facetEdge m wd).1).2 = 2 := by
  refine nonDanglingValency_eq_two_of_leaf wd.cover wd.fullDim _ ?_ ?_
  · rw [foldRight_above m wd]
    exact hLeaf
  · exact nonDanglingValency_ne_zero_of_incident wd.cover
      (NonTrivalentValencyTwoTracks.facetEdge m wd).2
      (incident_right wd.cover (NonTrivalentValencyTwoTracks.facetEdge m wd).1)

/-- **The fold at a `3 + 1` wall.** -/
def leafFold_of_leaf_right
    (hLeaf : (GluingDatum.incidentEdges (target := wd.coverTarget) wd.b).card = 1) :
    LeafFold wd where
  vertex := (wd.cover.sourceEnds (NonTrivalentValencyTwoTracks.facetEdge m wd).1).2
  nd_eq := foldRight_nd m wd hLeaf
  incident := fun e he ↦
    NonTrivalentValencyTwoLeafDictionary.incident_of_leaf_fold_right wd.cover wd.fullDim
      (b := wd.b) (contracted := wd.contracted) rfl _ (foldRight_above m wd) hLeaf
      (foldRight_nd m wd hLeaf) e.1 he e.2

/-! ### `AnchorEnds` in all three incoming sub-cases -/

section Trichotomy

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

include src hOrd in
/-- **The `2 + 2` anchor ends**: the two ends of the single vanishing
occurrence (`NonTrivalentValencyTwoTracks.leftEnd`, `rightEnd`), read as an
`AnchorEnds`. -/
theorem anchorEnds_of_noContractedReturn (hNoReturn : NoContractedReturn wd.cover wd.contracted) :
    AnchorEnds m wd anchorBlk (NonTrivalentValencyTwoTracks.leftEnd m wd)
      (NonTrivalentValencyTwoTracks.rightEnd m wd) :=
  ⟨NonTrivalentValencyTwoTracks.leftEnd_ne_rightEnd m wd,
    NonTrivalentValencyTwoTracks.three_le_nonDanglingValency_end m wd hNoReturn _
      (NonTrivalentValencyTwoTracks.incident_facetEdge_leftEnd m wd),
    NonTrivalentValencyTwoTracks.three_le_nonDanglingValency_end m wd hNoReturn _
      (NonTrivalentValencyTwoTracks.incident_facetEdge_rightEnd m wd),
    NonTrivalentValencyTwoTracks.sourceVertexMap_leftEnd_eq_anchorVertex m wd hNoReturn hOrd,
    (NonTrivalentValencyTwoTracks.sourceVertexMap_leftEnd_eq_rightEnd m wd).symm.trans
      (NonTrivalentValencyTwoTracks.sourceVertexMap_leftEnd_eq_anchorVertex m wd hNoReturn hOrd),
    NonTrivalentValencyTwoTracks.eq_leftEnd_or_eq_rightEnd_of_mem_activeFibre m wd hNoReturn src
      hOrd⟩

include src hOrd in
/-- **Anchor ends at every two-valent Base II wall.**  The incoming trichotomy
`val u + val v = 4` splits as `2 + 2` (`NonTrivalentValencyTwoTracks`, through
`NonTrivalentValencyTwoExit.noContractedReturn_of_two_two`), `1 + 3` and `3 + 1`
(this module). -/
theorem exists_anchorEnds :
    ∃ p q : wd.cover.SourceVertex, AnchorEnds m wd anchorBlk p q := by
  classical
  obtain ⟨hMerge, hA1, hA3, hB1, hB3, -, -⟩ := WallProgress.endpoints_of_contraction wd.cover
    wd.hc wd.hab wd.hOne wd.fullDim.valid wd.fullDim.changeMinimal
  have hStar := wallStar.card_incidentEdges
  by_cases hLeafA : (GluingDatum.incidentEdges (target := wd.coverTarget) wd.a).card = 1
  · exact ⟨_, _, anchorEnds_leaf m wd (leafFold_of_leaf_left m wd hLeafA) src hOrd⟩
  · by_cases hLeafB : (GluingDatum.incidentEdges (target := wd.coverTarget) wd.b).card = 1
    · exact ⟨_, _, anchorEnds_leaf m wd (leafFold_of_leaf_right m wd hLeafB) src hOrd⟩
    · exact ⟨_, _, anchorEnds_of_noContractedReturn m wd src hOrd
        (NonTrivalentValencyTwoExit.noContractedReturn_of_two_two m wd (by omega) (by omega))⟩

end Trichotomy

end Producers

/-! ## 7.  The dispatcher: one star count for all three incoming sub-cases -/

section Dispatcher

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (hRowVal : ∀ pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row pth).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)))
  (hMatrixWall : ∀ (pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row pth) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)) column.1)

include src in
/-- **`OuterWalk.TypeChangeLink` at any two-valent Base II wall, from one star
count.**  The incoming `2 + 2` / `1 + 3` / `3 + 1` trichotomy is discharged
internally by `exists_anchorEnds`; what the caller supplies is the star count
against the branch-vertex bijection this theorem hands back, and against the
no-return-free outgoing presentation
`NonTrivalentValencyTwoExitFree.wallOutgoingFD'`, which is the same
presentation in all three sub-cases. -/
theorem typeChangeLink_of_incidence_two :
    ∃ ve : BranchVertex (Prescribed.validCandidate sel).datum ≃ V,
      (∀ (v : BranchVertex (Prescribed.validCandidate sel).datum)
          (r : StablePath (Prescribed.validCandidate sel).datum),
        incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
          Nat.card {d : D // graph.vert (m.perm d) = ve v ∧
            label d = (NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd
              labelling₀ hRowVal hMatrixWall).labelling.row r}) →
        Nonempty (TypeChangeLink m wd) := by
  obtain ⟨p, q, hEnds⟩ := exists_anchorEnds m wd src hOrd
  exact ⟨vertexEquiv m wd src sel hOrd hEnds, fun hInc ↦
    ⟨typeChangeLink_of_incidence m wd src sel hOrd labelling₀ hRowVal hMatrixWall hEnds hInc⟩⟩

end Dispatcher

/-- **The Base II type-changing exit at a two-valent wall of the outer walk,
reduced to the star count.**  The headline of `NonTrivalentValencyTwoExitFree`
(`exists_typeChangeLink_baseTwo_of_wallData`), which carries no hypothesis about
the candidate, with its `InteriorGraphTracking.Tracks` input replaced by the
star count against an
explicitly produced branch-vertex bijection; the incoming trichotomy is
discharged inside. -/
theorem exists_typeChangeLink_of_incidence_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (_src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock),
      ∀ sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock,
        ∃ (out : FullDimensionalSourcePresentation (Prescribed.validCandidate sel).datum
              coordinate)
          (ve : BranchVertex (Prescribed.validCandidate sel).datum ≃ V),
          AgreeOffColumn wd.incomingMatrix
              (GluingDatum.LengthMatrixPresentation.matrix out.labelling.presentation)
              wd.column ∧
            ((∀ (v : BranchVertex (Prescribed.validCandidate sel).datum)
                (r : StablePath (Prescribed.validCandidate sel).datum),
                incidenceCount (Prescribed.validCandidate sel).datum v.1 r =
                  Nat.card {d : D // graph.vert (m.perm d) = ve v ∧
                    label d = out.labelling.row r}) → Nonempty (TypeChangeLink m wd)) := by
  classical
  obtain ⟨anchorBlock, src, -, hSelection⟩ :=
    NonTrivalentValencyTwoRowEquiv.exists_rowEquiv_of_wall_metric wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base) wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨-, -, hOrd, -, -⟩ := hSelection (Prescribed.Selection.default src)
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  refine ⟨anchorBlock, src, fun sel ↦ ?_⟩
  obtain ⟨ve, hve⟩ :=
    typeChangeLink_of_incidence_two m wd src sel hOrd labelling₀ hRowVal hMatrixWall
  refine ⟨NonTrivalentValencyTwoExitFree.wallOutgoingFD' m wd src sel hOrd labelling₀ hRowVal
    hMatrixWall, ve, ?_, hve⟩
  have h := NonTrivalentValencyTwoExitFree.agreeOffColumn_outLabelling' wd.cover wd.fullDim wd.hc
    wd.hab wd.hOne (wd.hForest m) (label m.base) labelling₀ src sel hOrd hRowVal hMatrixWall
    wd.coordinates wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  rw [wd.targetEdge_symm_contracted] at h
  exact h

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf
