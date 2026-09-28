import DraismaVargas.LocalCases.ClassifierInterface
import DraismaVargas.LocalCases.SecondEquation

/-!
# Wall arithmetic and the per-wall family dispatcher

This module classifies the walls of the march by the valency of the wall
vertex, and packages what a local classification must supply at one wall
(`WallInput`) into the fields of `SemanticAtlasMarch.State.PresentedProgress`.

The valency analysis below is arithmetic.  `MonovalentWall` proves Part I's
loop-12 argument and excludes valency one on exactly this module's incoming
full-dimensional/forest hypotheses, so `{2,3,4}` **is exhaustive** under that
bundle; `SourceFibreForest` additionally derives the forest from an actual
nonnegative wall metric with nonzero stable row lengths.  Those modules import
this one; the exclusion is not reproved here.  `ThirdEquation` provides the
input at a trivalent wall.  The divalent routes are not an exhaustive source
classifier by themselves: concentrated ramification alone does not exclude the
paper's nd2 cases (Figure 36), and empty-path presentations do not supply an
honest nonsingular incoming member.

`SemanticAtlasMarch.State.PresentedProgress`'s `familyAt` field asks for a
`BalancedGlobal.GaugeFamily` at **every** coordinate.  The four-valent wall
reaches one through `W4Bridge.auxR0SourceInput_of_contraction` and
`W4StableSource.AuxR0SourceInput.presentedFamily`, and the divalent one through
`SecondEquation.W2SourceInput` and the divalent case modules.  So the first
question this module answers is **"what are the wall types?"**

## 1.  The wall valency is `4 - ch(w₀)`, and four values occur

A wall of the march is a target occurrence of the incoming *full-dimensional*
datum whose length reaches zero; the wall datum is
`GluingContraction.contractDatum` at that occurrence and the wall vertex is the
merged vertex `w₀ = ⟨a, hab⟩`.  Three facts pin its valency completely.

* `ContractionRamification.card_incidentEdges_merge`:
  `val(w₀) + 2 = val(a) + val(b)`.
* `GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt`, applied to the
  change-minimal full-dimensional datum: `val(v) ≤ 3` at **every** target
  vertex, and `ChangeMinimal` reads the change off the valency,
  `ch(v) = 3 - val(v)`.
* `W4Bridge.targetExcess_contractDatum_merge_eq_one`: `exc(w₀) = 1`, that is
  `ch(w₀) + val(w₀) - 3 = 1`.

Together (`card_incidentEdges_merge_add_targetChange_eq_four` below)

```
val(w₀) + ch(w₀) = 4,        ch(w₀) = ch(a) + ch(b),
```

so **the wall valency is determined by the two contracted endpoints and nothing
else**, through the table

| `val(a), val(b)` | `val(w₀)` | `ch(w₀)` | local case |
|---|---|---|---|
| `(1,1)` | `0` | `4` | excluded, `one_le_card_incidentEdges_merge` |
| `(1,2)`, `(2,1)` | `1` | `3` | no `SourceCase` tag; excluded by `MonovalentWall` |
| `(1,3)`, `(3,1)`, `(2,2)` | `2` | `2` | `w2R1`, `w2M11`, `w2M1k`, `w2Mkk`, `w2P` |
| `(2,3)`, `(3,2)` | `3` | `1` | `w3Four`, `w3Shift`, `w3Nd3CoarseFine`, `w3Nd2CoarseFine` |
| `(3,3)` | `4` | `0` | `w4` |

`val(w₀) = 0` is the only value the arithmetic allows that a graph argument
excludes: it forces `val(a) = val(b) = 1`, hence (connectivity) a two-vertex
target with one occurrence, against `3 ≤ |E(target)|`, which
`three_le_card_target_edges` derives from
`SecondEquation.card_target_edges_eq_six_mul` with no star hypothesis at all.

**So `{2, 4}` does not exhaust the wall types, and by arithmetic alone neither
does `{2, 3, 4}`.**  The exact criterion is
`card_incidentEdges_merge_eq_two_or_four_iff` below: the wall is divalent or
four-valent **iff the two contracted valencies have the same parity**, i.e. iff
*both* or *neither* endpoint is divalent.  Equivalently
(`card_incidentEdges_merge_odd_of_exactly_one_divalent`) a wall with exactly one
divalent endpoint has valency `1` or `3`, and then
`not_nonempty_twoStar_of_exactly_one_divalent` /
`not_nonempty_fourStar_of_exactly_one_divalent` say in so many words that
**neither the divalent nor the four-valent local case applies at it**.

This is not an exotic corner.  Both realising models recorded in
`SecondEquation`'s module docstring have divalent target vertices, so both
present walls outside `{2, 4}`:

* the ten-vertex path `v₁ — ⋯ — v₁₀` at `degree = 3` (`|E| = 9`, `g(source) = 4`):
  contracting `v₁v₂` or `v₉v₁₀` is the `(1,2)` split, `val(w₀) = 1`.  Seven of its
  nine occurrences are divalent walls, two are monovalent, and **none** is
  four-valent — the whole four-valent route is inapplicable to that model;
* the trivalent `z` with two leaves and a length-seven branch: contracting
  `z u₁` is the `(3,2)` split, `val(w₀) = 3`, and contracting `u₆u₇` is `(2,1)`,
  `val(w₀) = 1`.

A target all of whose walls are divalent or four-valent is exactly a target with
no divalent vertex, every vertex a leaf or trivalent — because a divalent vertex
of a finite tree always has a neighbour that is not divalent (walk along the
divalent run; a tree's runs end at leaves).  Such targets exist: the cubic tree
with four internal vertices and six leaves has `|E| = 9`, three `(3,3)` walls and
six `(1,3)` walls.  So `{2, 4}` *is* exhaustive on a divalent-free target.

**But the divalent wall's own resolutions destroy that invariant.**  Read the
outgoing targets off the resolution modules: `ResolutionW4` splits `3 + 3` and
`ResolutionM11`/`ResolutionM1k` split `1 + 3`, all divalent-free; but
`W2R1Target`'s docstring says `w2-r1` "splits a divalent target wall into two
divalent endpoints", `ResolutionMkk` says "all candidates have divalent new
endpoints", and `ResolutionP` says "every new endpoint is divalent".  So the
moment the march crosses a `w2R1`, `w2Mkk` or `w2P` wall, its outgoing target
carries divalent vertices, and hence carries an occurrence with exactly one
divalent endpoint, and hence a wall of valency `1` or `3`.

The classification therefore cannot close on `{2, 4}`: three of the five
divalent shapes manufacture the walls that `{2, 4}` does not cover.  No
hypothesis in the library forbids divalent target vertices either —
`W4StableSource.CombinatorialType.divalentChangePositive` explicitly
contemplates them.

## 2.  The trivalent and monovalent walls

`SourceCase` reserves four `w3` tags; their local resolutions and global
candidates are built in the Case {w3} modules and in `ResolutionCoarseFine` /
`GlobalCoarseFine`, and `ThirdEquation` supplies the analogue of the
`SecondEquation` step (a `W3SourceInput` and `w3SourceInput_of_contraction`).
Two numerical facts are proved below:
`targetChange_merge_eq_one_of_trivalent` is the trivalent line of the table, and
`exists_unique_localRamification_of_targetChange_eq_one` says the single unit of
change sits on exactly one block — so unlike the divalent wall the trivalent
wall has *no* split branch, which is why its four shapes are shapes of one
distinguished block.  `targetChange_merge_eq_three_of_monovalent` is the
corresponding number at a monovalent wall, which has no tag.  No arithmetic
excludes the monovalent wall; `MonovalentWall` excludes it on the full
hypothesis bundle.

## 3.  The dispatcher, and how many `PresentedProgress` fields it reaches

`WallInput` is the per-coordinate package the classification has to produce:
the wall target, its datum and the three standing facts, the potential-theory
basepoint, the wall vertex, the tag, and a `BalancedGlobal.GaugeFamily` over
the ambient coordinate whose wall column is the crossed coordinate.
`ofFourValent` builds it from the four-valent route, reindexing
`Option target.edges` to the ambient coordinate along an equivalence carrying
the crossed coordinate to `none`.

`ofTrivalent` takes a presented family already over the ambient coordinate,
with the tag and its arity as parameters, and `LocalCases/W3WallInput.lean`
specializes it to `w3Nd3CoarseFine`, `w3Nd2CoarseFine` and `w3Shift`.

`ofGauge` is the route for a family with one base datum per member, and it is
what `w3Four` needs.  Figure 28's four members live over four *different* gauge
copies of the wall datum -- which is why `BalancedGlobal.GaugeFamily`
(abbreviated `W3FourClosure.GaugeFamily`) exists at all -- so their `.datum`s do
not share a type with a candidate over one `data`, and no `PresentedFamily` can
hold them.  `WallInput.family` is therefore a `GaugeFamily`,
`PresentedProgress.familyAt` likewise, and the one-datum constructors compose
with `BalancedGlobal.PresentedFamily.toGaugeFamily`, which is the identity on
every field the march reads (`ofTrivalent_eq_ofGauge`).  The same slot is what
`w2M11`, `w2M1k` and `w2Mkk` need, whose middle member lives over
`GlobalM11Arbitrary.SwappedDatum …`; their wall inputs are built in the
`A04*Wiring` and `A04*Tags` modules.  `w3Shift` does not need the slot, because
`W3ShiftClosure.equationThreeGaugeFamily` sets `base := fun _ => base`.

`presentedProgressOfWallInputs` then assembles **thirteen of the sixteen fields**
of `PresentedProgress` from `∀ wall, WallInput degree wall`, in the universal
atlas.  Note what this buys at the nonsingularity gate: `outgoingMatrix`
is gated on `det ≠ 0`, so `atlasOutgoingLabel` registers a member only when its
determinant is nonzero and falls back on the incoming label otherwise.  It
therefore needs **no** hypothesis of nonsingularity for every member, unlike
`ClassifierInterface.familyLabel`, and is safe against
`ClassifiedContinuation.SingularMember`.

The three fields that remain — `incomingAt`, `incomingNonzero`,
`incomingMatrix` — are not local-case data at all: they say that the chart the
march currently occupies is presented by a member of *every* wall's family, a
compatibility condition between the state and the classification.  They are
carried as explicit hypotheses.
-/

namespace DraismaVargas.LocalCases.WallProgress

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.W4Bridge
open DraismaVargas.LocalCases.BalancedGlobal

/-! ## 1.  Which wall valencies occur -/

section Valency

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

/-- **Every vertex of a connected graph with a second vertex meets an
occurrence.**  This is the only graph-theoretic input of the valency analysis,
and it is what excludes `val(w₀) = 0`. -/
theorem one_le_card_incidentEdges_of_connected {G : CFGraph}
    (hConnected : graph_connected G) {v w : G.V} (hne : w ≠ v) :
    1 ≤ (GluingDatum.incidentEdges v).card := by
  classical
  obtain ⟨first, hfirst, second, hsecond, hpos⟩ :=
    hConnected {v} ⟨v, w, Finset.mem_singleton_self v,
      by simpa using hne⟩
  rw [Finset.mem_singleton.mp hfirst] at hpos
  obtain ⟨pair, hmem, hends⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos G v second hpos
  let occurrence : G.edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hmem⟩⟩
  have hcoe : (occurrence : G.V × G.V) = pair := rfl
  refine Finset.card_pos.mpr ⟨occurrence, ?_⟩
  rw [mem_incidentEdges_iff, hcoe]
  rcases hends with hpair | hpair
  · exact Or.inl (by rw [hpair])
  · exact Or.inr (by rw [hpair])

/-- **The smallest admissible target, with no star hypothesis.**
`SecondEquation.three_le_card_target_edges_of_twoStar` reaches `3 ≤ |E(target)|`
through a two-star; the numerology alone already gets there, because
`|E| = 6 (degree + c(H)) - 15` is nonnegative and `degree, c(H) ≥ 1`. -/
theorem three_le_card_target_edges {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    3 ≤ target.edges.card := by
  have hCount := SecondEquation.card_target_edges_eq_six_mul data fullDim
  have hComponent :=
    TrivalenceClosure.one_le_stableComponentCount_of_presentation fullDim
  have hDegree : 1 ≤ (degree : ℤ) := by exact_mod_cast data.degree_pos
  omega

/-- The contracted target of a full-dimensional datum has at least two
vertices: genus zero makes `|V| = |E| + 1`, and `3 ≤ |E|`. -/
theorem nontrivial_vertex_contract {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    Nontrivial (GraphContraction.contract target hab hOne).V := by
  have hEdges := three_le_card_target_edges data fullDim
  have hGenus : (target.edges.card : ℤ) - Fintype.card target.V + 1 = 0 :=
    fullDim.targetGenus
  have hCard : Fintype.card (GraphContraction.contract target hab hOne).V
      = Fintype.card target.V - 1 :=
    GraphContraction.card_vertices_contract target hab hOne
  refine Fintype.one_lt_card_iff_nontrivial.mp ?_
  omega

/-! ### The valency identity -/

/-- **The wall's valency and the change it carries add to four.**  This is
Equation (C) at the merged vertex with the definition of `targetExcess`
unfolded, and it is the whole of the wall-type analysis: `ch(w₀) ≥ 0` bounds the
valency above by `4`, and connectivity bounds it below by `1`. -/
theorem card_incidentEdges_merge_add_targetChange_eq_four
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hMinimal : data.ChangeMinimal) :
    ((GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card : ℤ)
      + (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ = 4 := by
  have hExcess :=
    targetExcess_contractDatum_merge_eq_one data hc hab hOne hForest hMinimal
  unfold GluingDatum.targetExcess at hExcess
  linarith

/-- **The wall valency is at most four**, because the change it carries is a sum
of nonnegative local ramifications. -/
theorem card_incidentEdges_merge_le_four (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) (hMinimal : data.ChangeMinimal) :
    (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card ≤ 4 := by
  have hSum :=
    card_incidentEdges_merge_add_targetChange_eq_four data hc hab hOne hForest
      hMinimal
  have hNonneg := (contractDatum data hc hab hOne).targetChange_nonneg
    (valid_contractDatum data hc hab hOne hForest hValid) ⟨a, hab⟩
  omega

/-- **The wall valency is at least one.**  `val(w₀) = 0` would make the merged
vertex isolated in a connected target with at least two vertices. -/
theorem one_le_card_incidentEdges_merge {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    1 ≤ (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card := by
  have hNontrivial := nontrivial_vertex_contract data hab hOne fullDim
  obtain ⟨other, hother⟩ :=
    @exists_ne (GraphContraction.contract target hab hOne).V hNontrivial ⟨a, hab⟩
  exact one_le_card_incidentEdges_of_connected
    (GraphContraction.graph_connected_contract target hab hOne
      fullDim.targetConnected)
    hother

/-- **The four wall valencies.**  Exactly `1`, `2`, `3` and `4` survive the
arithmetic; valency `1` is excluded separately (`MonovalentWall`). -/
theorem card_incidentEdges_merge_cases {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted) :
    (GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 1 ∨
      (GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 2 ∨
        (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 3 ∨
          (GluingDatum.incidentEdges
            (target := GraphContraction.contract target hab hOne)
              ⟨a, hab⟩).card = 4 := by
  have hLower := one_le_card_incidentEdges_merge data hab hOne fullDim
  have hUpper := card_incidentEdges_merge_le_four data hc hab hOne hForest
    fullDim.valid fullDim.changeMinimal
  omega

/-- **The endpoint bookkeeping, uniformly in the valency.**  The merged valency
is the sum of the two endpoint valencies less two, each endpoint valency lies
between one and three, and change-minimality reads each endpoint change off its
valency.  `W4Bridge.endpoints_trivalent_of_fourStar` and
`SecondEquation.endpoints_of_twoStar` are the `val(w₀) = 4` and `val(w₀) = 2`
specializations. -/
theorem endpoints_of_contraction (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal) :
    (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card + 2
        = (GluingDatum.incidentEdges a).card + (GluingDatum.incidentEdges b).card ∧
      1 ≤ (GluingDatum.incidentEdges a).card ∧
        (GluingDatum.incidentEdges a).card ≤ 3 ∧
          1 ≤ (GluingDatum.incidentEdges b).card ∧
            (GluingDatum.incidentEdges b).card ≤ 3 ∧
              data.targetChange a
                  + ((GluingDatum.incidentEdges a).card : ℤ) = 3 ∧
                data.targetChange b
                  + ((GluingDatum.incidentEdges b).card : ℤ) = 3 := by
  have hMerge := card_incidentEdges_merge hc hab hOne
  have hLeftLe := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data
    hValid a (hMinimal a)
  have hRightLe := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data
    hValid b (hMinimal b)
  have hLeftMem : 1 ≤ (GluingDatum.incidentEdges a).card :=
    Finset.card_pos.mpr ⟨contracted, contracted_mem_incidentEdges_left hc⟩
  have hRightMem : 1 ≤ (GluingDatum.incidentEdges b).card :=
    Finset.card_pos.mpr ⟨contracted, contracted_mem_incidentEdges_right hc⟩
  have hLeftExcess : data.targetChange a
      + ((GluingDatum.incidentEdges a).card : ℤ) - 3 = 0 := hMinimal a
  have hRightExcess : data.targetChange b
      + ((GluingDatum.incidentEdges b).card : ℤ) - 3 = 0 := hMinimal b
  exact ⟨hMerge, hLeftMem, hLeftLe, hRightMem, hRightLe, by linarith, by linarith⟩

/-- **The exact criterion for the divalent and four-valent local cases.**  The wall is divalent
or four-valent precisely when the two contracted endpoint valencies have the
same parity — equivalently, when both endpoints are divalent or neither is. -/
theorem card_incidentEdges_merge_eq_two_or_four_iff {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    ((GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 2 ∨
        (GluingDatum.incidentEdges
          (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 4)
      ↔ ((GluingDatum.incidentEdges a).card = 2 ↔
          (GluingDatum.incidentEdges b).card = 2) := by
  obtain ⟨hMerge, hLeftMem, hLeftLe, hRightMem, hRightLe, _, _⟩ :=
    endpoints_of_contraction data hc hab hOne fullDim.valid fullDim.changeMinimal
  have hWallPos := one_le_card_incidentEdges_merge data hab hOne fullDim
  constructor
  · intro hWall
    refine ⟨fun hLeft ↦ ?_, fun hRight ↦ ?_⟩ <;>
      rcases hWall with hWall | hWall <;> omega
  · intro hIff
    by_cases hLeft : (GluingDatum.incidentEdges a).card = 2
    · have := hIff.mp hLeft
      omega
    · have hRight : (GluingDatum.incidentEdges b).card ≠ 2 := fun h ↦
        hLeft (hIff.mpr h)
      omega

/-- **A wall with exactly one divalent endpoint has odd valency**, so it is
neither divalent nor four-valent. -/
theorem card_incidentEdges_merge_odd_of_exactly_one_divalent
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card ≠ 2) :
    (GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 1 ∨
      (GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 3 := by
  obtain ⟨hMerge, _, _, hRightMem, hRightLe, _, _⟩ :=
    endpoints_of_contraction data hc hab hOne hValid hMinimal
  omega

/-- **Neither the divalent nor the four-valent local case applies at a wall with
exactly one divalent endpoint.**  `W2R1Target.TwoStar` forces valency two and
`W4TargetPairings.FourStar` forces valency four, and the merged vertex has
neither. -/
theorem not_nonempty_twoStar_of_exactly_one_divalent
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card ≠ 2) :
    ¬ Nonempty (W2R1Target.TwoStar (GraphContraction.contract target hab hOne)
      ⟨a, hab⟩) := by
  rintro ⟨star⟩
  have hStar := star.card_incidentEdges
  have hOdd := card_incidentEdges_merge_odd_of_exactly_one_divalent data hc hab
    hOne hValid hMinimal hLeft hRight
  omega

theorem not_nonempty_fourStar_of_exactly_one_divalent
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card ≠ 2) :
    ¬ Nonempty (W4TargetPairings.FourStar
      (GraphContraction.contract target hab hOne) ⟨a, hab⟩) := by
  rintro ⟨star⟩
  have hStar := card_incidentEdges_of_fourStar star
  have hOdd := card_incidentEdges_merge_odd_of_exactly_one_divalent data hc hab
    hOne hValid hMinimal hLeft hRight
  omega

/-! ### What the trivalent and monovalent walls have to balance -/

/-- **At a trivalent wall the change is one.**  This is the `val(w₀) = 3` line of
the table, and the exact analogue of `SecondEquation.W2SourceInput.targetChange_eq_two`
and of the `ch(w₀) = 0` that `W4StableSource`'s `change_zero` hypothesis
records. -/
theorem targetChange_merge_eq_one_of_trivalent (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hMinimal : data.ChangeMinimal)
    (hValency : (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 3) :
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ = 1 := by
  have hSum :=
    card_incidentEdges_merge_add_targetChange_eq_four data hc hab hOne hForest
      hMinimal
  rw [hValency] at hSum
  norm_num at hSum
  linarith

/-- **At a monovalent wall the change is three.**  No `SourceCase` tag balances
this number. -/
theorem targetChange_merge_eq_three_of_monovalent
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hMinimal : data.ChangeMinimal)
    (hValency : (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 1) :
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ = 3 := by
  have hSum :=
    card_incidentEdges_merge_add_targetChange_eq_four data hc hab hOne hForest
      hMinimal
  rw [hValency] at hSum
  norm_num at hSum
  linarith

/-- **One unit of change sits on exactly one block.**  Riemann--Hurwitz makes
every local ramification nonnegative, so a wall of total change one has a single
ramified block, carrying exactly one unit.  Taken with
`targetChange_merge_eq_one_of_trivalent` this is the trivalent wall's analogue of
`SecondEquation.W2SourceInput.ramification_split_or_concentrated`, and it says
why the trivalent wall has no split branch: there is nothing to split. -/
theorem exists_unique_localRamification_of_targetChange_eq_one
    (data : GluingDatum target degree) (wall : target.V) (hValid : data.Valid)
    (hChange : data.targetChange wall = 1) :
    ∃ sourceBlock : (data.vertexPartition wall).Blocks,
      data.localRamification wall sourceBlock = 1 ∧
        ∀ other : (data.vertexPartition wall).Blocks, other ≠ sourceBlock →
          data.localRamification wall other = 0 := by
  classical
  have hNonneg : ∀ blk : (data.vertexPartition wall).Blocks,
      0 ≤ data.localRamification wall blk :=
    fun blk ↦ data.localRamification_nonneg wall (hValid.2 wall) blk
  have hSum : (∑ blk : (data.vertexPartition wall).Blocks,
      data.localRamification wall blk) = 1 := by
    unfold GluingDatum.targetChange at hChange
    exact hChange
  have hExists : ∃ blk : (data.vertexPartition wall).Blocks,
      1 ≤ data.localRamification wall blk := by
    by_contra hNone
    push Not at hNone
    have hZero : (∑ blk : (data.vertexPartition wall).Blocks,
        data.localRamification wall blk) = 0 :=
      Finset.sum_eq_zero fun blk _ ↦ by
        have hLt := hNone blk
        have hGe := hNonneg blk
        omega
    omega
  obtain ⟨sourceBlock, hPos⟩ := hExists
  have hOthers : ∀ other : (data.vertexPartition wall).Blocks,
      other ∈ (Finset.univ : Finset (data.vertexPartition wall).Blocks) →
      other ≠ sourceBlock → data.localRamification wall other = 0 := by
    intro other _ hNe
    have hPair : data.localRamification wall sourceBlock
        + data.localRamification wall other
        ≤ ∑ blk : (data.vertexPartition wall).Blocks,
            data.localRamification wall blk := by
      have hSubset := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun blk : (data.vertexPartition wall).Blocks ↦
          data.localRamification wall blk)
        (Finset.subset_univ
          ({sourceBlock, other} : Finset (data.vertexPartition wall).Blocks))
        (fun blk _ _ ↦ hNonneg blk)
      rwa [Finset.sum_pair (Ne.symm hNe)] at hSubset
    have hGe := hNonneg other
    omega
  refine ⟨sourceBlock, ?_, fun other hNe ↦ hOthers other (Finset.mem_univ other) hNe⟩
  rwa [Finset.sum_eq_single_of_mem sourceBlock (Finset.mem_univ sourceBlock)
    hOthers] at hSum

end Valency

/-! ## 2.  The per-wall dispatcher

`PresentedProgress` needs one ambient coordinate type, while every presented
family in the library lives over `Option target.edges` for that wall's own target.
`WallInput` is the reindexed package, and the three constructors below are the
three routes that reach one.  Because `targetAt : coordinate → CFGraph.{0}`, the
ambient coordinate type of any actual assembly is `Type 0`; the section fixes
that. -/

section Dispatcher

open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ}

/-- Transport a presented family along an identity of arities.  The four
concentrated divalent tags all have arity three, so one constructor serves all
four. -/
def familyCast {target : CFGraph} {data : GluingDatum target degree}
    {wall : target.V} {n m : ℕ} (h : n = m)
    (family : PresentedFamily (coordinate := coordinate) n data wall) :
    PresentedFamily (coordinate := coordinate) m data wall := h ▸ family

@[simp] theorem familyCast_wallColumn {target : CFGraph}
    {data : GluingDatum target degree} {wall : target.V} {n m : ℕ} (h : n = m)
    (family : PresentedFamily (coordinate := coordinate) n data wall) :
    (familyCast h family).wallColumn = family.wallColumn := by
  subst h; rfl

/-- Transport a **gauge-mixed** family along an identity of arities.  Same as
`familyCast`, for the families whose members carry one base datum each. -/
def gaugeFamilyCast {target : CFGraph} {data : GluingDatum target degree}
    {wall : target.V} {n m : ℕ} (h : n = m)
    (family : GaugeFamily (coordinate := coordinate) n data wall) :
    GaugeFamily (coordinate := coordinate) m data wall := h ▸ family

@[simp] theorem gaugeFamilyCast_wallColumn {target : CFGraph}
    {data : GluingDatum target degree} {wall : target.V} {n m : ℕ} (h : n = m)
    (family : GaugeFamily (coordinate := coordinate) n data wall) :
    (gaugeFamilyCast h family).wallColumn = family.wallColumn := by
  subst h; rfl

@[simp] theorem gaugeFamilyCast_toGaugeFamily {target : CFGraph}
    {data : GluingDatum target degree} {wall : target.V} {n m : ℕ} (h : n = m)
    (family : PresentedFamily (coordinate := coordinate) n data wall) :
    gaugeFamilyCast h family.toGaugeFamily = (familyCast h family).toGaugeFamily := by
  subst h; rfl

/-- **Move a gauge-mixed family to a different coordinate labelling.**  The
gauge analogue of `ClassifierInterface.familyReindex`: `base`, `valid_of_old`,
`candidate` and `weight` are untouched -- only the presentations, which are
where the coordinate appears, are relabelled -- and the two proof fields are the
originals composed with `ClassifierInterface.det_matrix_reindex` and
`ClassifierInterface.matrix_reindex`, exactly as in the presented case.
`W3FourStableGraph.Figure28Receipts.gaugeFamily` is stated over
`Option target.edges` and needs this to reach the march's coordinate. -/
noncomputable def gaugeFamilyReindex {target : CFGraph}
    {data : GluingDatum target degree} {wall : target.V} {n : ℕ}
    {coordinate' : Type} [Fintype coordinate'] [DecidableEq coordinate']
    (relabel : coordinate ≃ coordinate')
    (family : GaugeFamily (coordinate := coordinate') n data wall) :
    GaugeFamily (coordinate := coordinate) n data wall where
  base := family.base
  valid_of_old := family.valid_of_old
  candidate := family.candidate
  presentation := fun i ↦ ClassifierInterface.reindex relabel (family.presentation i)
  wallColumn := relabel.symm family.wallColumn
  weight := family.weight
  positiveBalance := by
    refine ⟨family.positiveBalance.1, ?_⟩
    have hdet : ∀ i, (GluingDatum.LengthMatrixPresentation.matrix
        (ClassifierInterface.reindex relabel (family.presentation i))).det =
          (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation i)).det :=
      fun i ↦ ClassifierInterface.det_matrix_reindex relabel (family.presentation i)
    simpa only [hdet] using family.positiveBalance.2
  agreeOffWall := by
    intro first second row column hColumn
    have hNe : relabel column ≠ family.wallColumn := by
      intro hEq
      exact hColumn (by rw [← hEq, Equiv.symm_apply_apply])
    have := family.agreeOffWall first second (relabel row) (relabel column) hNe
    simpa only [ClassifierInterface.matrix_reindex, Matrix.submatrix_apply] using this

@[simp] theorem gaugeFamilyReindex_wallColumn {target : CFGraph}
    {data : GluingDatum target degree} {wall : target.V} {n : ℕ}
    {coordinate' : Type} [Fintype coordinate'] [DecidableEq coordinate']
    (relabel : coordinate ≃ coordinate')
    (family : GaugeFamily (coordinate := coordinate') n data wall) :
    (gaugeFamilyReindex relabel family).wallColumn =
      relabel.symm family.wallColumn := rfl

@[simp] theorem gaugeFamilyReindex_candidate {target : CFGraph}
    {data : GluingDatum target degree} {wall : target.V} {n : ℕ}
    {coordinate' : Type} [Fintype coordinate'] [DecidableEq coordinate']
    (relabel : coordinate ≃ coordinate')
    (family : GaugeFamily (coordinate := coordinate') n data wall) (i : Fin n) :
    (gaugeFamilyReindex relabel family).candidate i = family.candidate i := rfl

@[simp] theorem gaugeFamilyReindex_presentation {target : CFGraph}
    {data : GluingDatum target degree} {wall : target.V} {n : ℕ}
    {coordinate' : Type} [Fintype coordinate'] [DecidableEq coordinate']
    (relabel : coordinate ≃ coordinate')
    (family : GaugeFamily (coordinate := coordinate') n data wall) (i : Fin n) :
    (gaugeFamilyReindex relabel family).presentation i =
      ClassifierInterface.reindex relabel (family.presentation i) := rfl

/-- **What a local classification owes at one coordinate.**  The wall target and
its datum, the three standing facts `PresentedProgress` records about the
incoming stage, the potential-theory basepoint, the wall vertex, the source tag,
and a balanced family -- one base datum per member -- over the ambient
coordinate whose wall column is the coordinate crossed. -/
structure WallInput (degree : ℕ) (coordinate : Type) [Fintype coordinate]
    [DecidableEq coordinate] (wall : coordinate) where
  /-- The contracted target of this coordinate's occurrence. -/
  target : CFGraph.{0}
  /-- The wall datum. -/
  data : GluingDatum target degree
  /-- Validity of the wall datum. -/
  valid : data.Valid
  /-- Part-I standing hypothesis on the wall target. -/
  targetConnected : graph_connected target
  /-- Part-I standing hypothesis on the wall target. -/
  targetGenus : genus target = 0
  /-- The potential-theory basepoint. -/
  root : target.V
  /-- The merged vertex. -/
  wallVertex : target.V
  /-- Which of the ten determinant-balance shapes resolves it. -/
  case : SourceCase
  /-- **The balanced family, already over the ambient coordinate, with one base
  datum per member.**  A `BalancedGlobal.GaugeFamily`, not a `PresentedFamily`:
  Figure 28's four members live over four branch-swapped copies of `data`, and
  the middle member of `GlobalM11Arbitrary.candidates` over
  `GlobalM11Arbitrary.SwappedDatum …`, so their `candidate` slots do not share a
  type with a `Candidate target degree data wallVertex`.  Every route that
  produces a family over the one datum -- `ofFourValent`, `ofTrivalent` --
  composes with `BalancedGlobal.PresentedFamily.toGaugeFamily`, which keeps
  every field the march reads.  `ofGauge` is the route for a family that is
  genuinely gauge-mixed. -/
  family : GaugeFamily (coordinate := coordinate) case.arity data wallVertex
  /-- Its regrown column is the coordinate crossed. -/
  family_wallColumn : family.wallColumn = wall

namespace WallInput

variable {wall : coordinate}

/-- **The four-valent route.**  `W4Bridge.auxR0SourceInput_of_contraction`
produces the `AuxR0SourceInput` from a full-dimensional presentation and the
contraction receipts; `AuxR0SourceInput.presentedFamily` turns it into the
three-candidate family. -/
noncomputable def ofFourValent {target : CFGraph.{0}} [DecidableEq target.edges]
    {data : GluingDatum target degree} {wallVertex : target.V}
    (star : W4TargetPairings.FourStar target wallVertex)
    (source : AuxR0SourceInput data star)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (relabel : coordinate ≃ Option target.edges)
    (hrelabel : relabel wall = none) :
    WallInput degree coordinate wall where
  target := target
  data := data
  valid := source.valid
  targetConnected := targetConnected
  targetGenus := targetGenus
  root := root
  wallVertex := wallVertex
  case := SourceCase.w4
  family := (familyCast (show (3 : ℕ) = SourceCase.w4.arity from rfl)
    (ClassifierInterface.familyReindex relabel
      (AuxR0SourceInput.presentedFamily data star source))).toGaugeFamily
  family_wallColumn := by
    rw [PresentedFamily.toGaugeFamily_wallColumn, familyCast_wallColumn,
      ClassifierInterface.familyReindex_wallColumn]
    exact (Equiv.symm_apply_eq relabel).mpr hrelabel.symm

/-- **The trivalent route.**  Nothing in a `WallInput` beyond the tag depends on
*which* trivalent shape resolved the wall: the three built trivalent sources --
`W3Nd3CommonBalance` (Equation (4)), `W3Nd2CommonBalance` (Equation (5)) and
`W3ShiftClosure` (Equation (3)) -- are unrelated constructions that all end in
the same object, a `BalancedGlobal.PresentedFamily` over **one** datum whose
wall column is the crossed coordinate.  So one constructor serves them, with the
tag and its arity as parameters.

Unlike `ofFourValent`, this one takes the family already in the
ambient coordinate, and does not reindex.  That is not a simplification: the W3
square-labelling sections are parametric in the coordinate, so a caller
instantiates them directly at the march's coordinate through the incoming
member's own honest labelling -- which is what `W3Nd2PositiveExit.initialLabelling`
and `W3Nd3ArbitraryExit.initialLabelling` do -- and an
`Option target.edges` detour would only have to be undone.  `familyReindex` is
still available for a caller that wants one; compose it before calling. -/
noncomputable def ofTrivalent {target : CFGraph.{0}}
    {data : GluingDatum target degree} {wallVertex : target.V} {n : ℕ}
    (family : PresentedFamily (coordinate := coordinate) n data wallVertex)
    (hValid : data.Valid) (case : SourceCase) (harity : n = case.arity)
    (hwallColumn : family.wallColumn = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    WallInput degree coordinate wall where
  target := target
  data := data
  valid := hValid
  targetConnected := targetConnected
  targetGenus := targetGenus
  root := root
  wallVertex := wallVertex
  case := case
  family := (familyCast harity family).toGaugeFamily
  family_wallColumn := by
    rw [PresentedFamily.toGaugeFamily_wallColumn, familyCast_wallColumn]
    exact hwallColumn

@[simp] theorem ofTrivalent_case {target : CFGraph.{0}}
    {data : GluingDatum target degree} {wallVertex : target.V} {n : ℕ}
    (family : PresentedFamily (coordinate := coordinate) n data wallVertex)
    (hValid : data.Valid) (case : SourceCase) (harity : n = case.arity)
    (hwallColumn : family.wallColumn = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    (ofTrivalent family hValid case harity hwallColumn targetConnected
      targetGenus root).case = case := rfl

/-- **The gauge-mixed route.**  `ofTrivalent` with the one-datum restriction
removed: the family's members may sit over one branch-swapped copy of the wall
datum each, which is what Figure 28 forces and what `ofTrivalent` -- through
`BalancedGlobal.PresentedFamily` -- cannot express.  Everything else is
identical, tag and arity parameters included, and `ofTrivalent` is this
constructor precomposed with
`BalancedGlobal.PresentedFamily.toGaugeFamily`:

```
ofTrivalent family hValid case harity hwallColumn hConn hGenus root
  = ofGauge family.toGaugeFamily hValid case harity hwallColumn hConn hGenus root
```

(`ofTrivalent_eq_ofGauge` below, by `rfl`).  `hValid` is the validity of the
*incoming* wall datum; each member's own datum is validated inside the family by
`valid_of_old`, so no extra hypothesis appears.  `W3WallInput.ofFour` is a
caller: Figure 28's `w3Four` family. -/
noncomputable def ofGauge {target : CFGraph.{0}}
    {data : GluingDatum target degree} {wallVertex : target.V} {n : ℕ}
    (family : GaugeFamily (coordinate := coordinate) n data wallVertex)
    (hValid : data.Valid) (case : SourceCase) (harity : n = case.arity)
    (hwallColumn : family.wallColumn = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    WallInput degree coordinate wall where
  target := target
  data := data
  valid := hValid
  targetConnected := targetConnected
  targetGenus := targetGenus
  root := root
  wallVertex := wallVertex
  case := case
  family := gaugeFamilyCast harity family
  family_wallColumn := by rw [gaugeFamilyCast_wallColumn]; exact hwallColumn

@[simp] theorem ofGauge_case {target : CFGraph.{0}}
    {data : GluingDatum target degree} {wallVertex : target.V} {n : ℕ}
    (family : GaugeFamily (coordinate := coordinate) n data wallVertex)
    (hValid : data.Valid) (case : SourceCase) (harity : n = case.arity)
    (hwallColumn : family.wallColumn = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    (ofGauge family hValid case harity hwallColumn targetConnected
      targetGenus root).case = case := rfl

/-- **`ofTrivalent` is the constant-base instance of `ofGauge`.**  The two wall
inputs are literally the same term. -/
theorem ofTrivalent_eq_ofGauge {target : CFGraph.{0}}
    {data : GluingDatum target degree} {wallVertex : target.V} {n : ℕ}
    (family : PresentedFamily (coordinate := coordinate) n data wallVertex)
    (hValid : data.Valid) (case : SourceCase) (harity : n = case.arity)
    (hwallColumn : family.wallColumn = wall)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) :
    ofTrivalent family hValid case harity hwallColumn targetConnected
        targetGenus root =
      ofGauge family.toGaugeFamily hValid case harity hwallColumn
        targetConnected targetGenus root := by
  subst harity; rfl

end WallInput

end Dispatcher

/-! ## 3.  Thirteen of the sixteen `PresentedProgress` fields

The remaining three — `incomingAt`, `incomingNonzero`, `incomingMatrix` — are
not local-case data: they assert that the chart the march currently occupies is
presented by a member of *every* wall's family.  That is a compatibility
condition between the state and the classification, and it is carried here as a
hypothesis. -/

section Progress

open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.SemanticAtlasMarch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {baseStart baseFinish : coordinate → ℚ}

/-- The universal matrix atlas read as the chart map the march consumes.  Its
`hdet` obligation is a projection, `MatrixAtlas.atlasMatrix_det_ne_zero`. -/
def atlasChartMatrix (coordinate : Type) [Fintype coordinate]
    [DecidableEq coordinate] (degree : ℕ) :
    MatrixAtlas.chart coordinate degree → Matrix coordinate coordinate ℚ :=
  fun label ↦ MatrixAtlas.atlasMatrix label

@[simp] theorem atlasChartMatrix_apply
    (label : MatrixAtlas.chart coordinate degree) :
    atlasChartMatrix coordinate degree label = MatrixAtlas.atlasMatrix label := rfl

theorem atlasChartMatrix_det_ne_zero
    (label : MatrixAtlas.chart coordinate degree) :
    (atlasChartMatrix coordinate degree label).det ≠ 0 :=
  MatrixAtlas.atlasMatrix_det_ne_zero label

/-- **`simpleCrossings` is a genericity choice made once, at the seed.**  This is
`ClassifierInterface.simpleNegativeCrossings_of_chartGeneric` read on a semantic
state in the universal atlas, where `hdet` is a projection. -/
theorem simpleNegativeCrossings_of_atlasGeneric
    (current : SemanticAtlasMarch.State degree
      (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (hGeneric : ∀ first second : coordinate,
      DraismaVargas.LocalCases.FiniteAtlasMarch.chartCoordinates
          (atlasChartMatrix coordinate degree current.toMatrixState.label)
          baseFinish first < 0 →
      DraismaVargas.LocalCases.FiniteAtlasMarch.chartCoordinates
          (atlasChartMatrix coordinate degree current.toMatrixState.label)
          baseFinish second < 0 →
      DraismaVargas.LocalCases.FiniteAtlasMarch.chartCoordinates
            (atlasChartMatrix coordinate degree current.toMatrixState.label)
            baseStart first *
          DraismaVargas.LocalCases.FiniteAtlasMarch.chartCoordinates
            (atlasChartMatrix coordinate degree current.toMatrixState.label)
            baseFinish second =
        DraismaVargas.LocalCases.FiniteAtlasMarch.chartCoordinates
            (atlasChartMatrix coordinate degree current.toMatrixState.label)
            baseStart second *
          DraismaVargas.LocalCases.FiniteAtlasMarch.chartCoordinates
            (atlasChartMatrix coordinate degree current.toMatrixState.label)
            baseFinish first →
      first = second) :
    SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish :=
  ClassifierInterface.simpleNegativeCrossings_of_chartGeneric
    (atlasChartMatrix coordinate degree) current.toMatrixState
    (atlasChartMatrix_det_ne_zero current.toMatrixState.label) hGeneric

/-- **Atlas registration through the nonsingularity gate.**  A member is
registered only when its length matrix is nonsingular; a singular member falls
back on the incoming label, which `outgoingMatrix` never looks at.  So this
needs no hypothesis of nonsingularity for every member of the family, unlike
`ClassifierInterface.familyLabel`, and it is therefore safe against
`ClassifiedContinuation.SingularMember.singularFamily`.

`Guard` is the coordinate predicate the wall inputs are restricted by; the
march instantiates it at `SemanticAtlasMarch.State.FirstWall`, and the
definition itself never looks at it beyond indexing `input`. -/
noncomputable def atlasOutgoingLabel {Guard : coordinate → Prop}
    (input : ∀ wall : coordinate, Guard wall → WallInput degree coordinate wall)
    (hnodup : ∀ (wall : coordinate) (hw : Guard wall)
      (i : Fin (input wall hw).case.arity) row,
      (((input wall hw).family.presentation i).path row).Nodup)
    (fallback : MatrixAtlas.chart coordinate degree)
    (wall : coordinate) (hw : Guard wall) (i : Fin (input wall hw).case.arity) :
    MatrixAtlas.chart coordinate degree :=
  if h : (GluingDatum.LengthMatrixPresentation.matrix
      ((input wall hw).family.presentation i)).det ≠ 0 then
    MatrixAtlas.encodePresentation ((input wall hw).family.presentation i)
      (hnodup wall hw i) h
  else fallback

/-- `PresentedProgress.outgoingMatrix` for `atlasOutgoingLabel`, in its gated
form. -/
theorem atlasMatrix_atlasOutgoingLabel {Guard : coordinate → Prop}
    (input : ∀ wall : coordinate, Guard wall → WallInput degree coordinate wall)
    (hnodup : ∀ (wall : coordinate) (hw : Guard wall)
      (i : Fin (input wall hw).case.arity) row,
      (((input wall hw).family.presentation i).path row).Nodup)
    (fallback : MatrixAtlas.chart coordinate degree)
    (wall : coordinate) (hw : Guard wall) (i : Fin (input wall hw).case.arity)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix
      ((input wall hw).family.presentation i)).det ≠ 0) :
    atlasChartMatrix coordinate degree
        (atlasOutgoingLabel input hnodup fallback wall hw i) =
      GluingDatum.LengthMatrixPresentation.matrix
        ((input wall hw).family.presentation i) := by
  rw [atlasChartMatrix_apply, atlasOutgoingLabel, dif_pos hdet]
  exact MatrixAtlas.atlasMatrix_encodePresentation _ _ _

/-- **The assembly.**  A `WallInput` at every coordinate, duplicate-free
presentation rows, the seed genericity condition, and the incoming-chart
compatibility triple produce a `PresentedProgress` — and hence, through
`PresentedProgress.exists_step`, a semantic successor at every nonterminal
state.

Thirteen fields come from the dispatcher: `targetAt`, `dataAt`, `validAt`,
`targetConnectedAt`, `targetGenusAt`, `rootAt`, `targetWallAt`, `caseAt`,
`familyAt`, `wallColumn` are the `WallInput` fields verbatim, `simpleCrossings`
is the genericity hypothesis, and `outgoingLabel`/`outgoingMatrix` are the gated
atlas registration.  The three that remain are the last three arguments.

**Every wall-indexed input is asked only at a first wall.**
`input` is `∀ wall, current.FirstWall wall → WallInput …`, and so are `hnodup`,
`incoming`, `fullDim` and their side conditions; the fields of
`PresentedProgress` carry the same guard, so this is the identity on the wall
data and a genuine weakening of what the classifier must supply.  See the note
above `SemanticAtlasMarch.IsFirstWall` for why the total form is false.

**`fullDim` and `hFullDim`.**  The march payload carries a
`FullDimensionalSource.FullDimensionalSourcePresentation`
(`SemanticAtlasMarch.CarriesClearedPencil`), so the successor state needs one for
the *outgoing* member of the selected family.  A `BalancedGlobal.GaugeFamily`
carries only a bare `GluingDatum.LengthMatrixPresentation` per member, and
nothing derives the full-dimensional package from it, so it is carried
alongside.  Note where
the demand lands: on the classifier's exits, not on `WallInput`'s geometry, so
every field of `WallInput` is untouched.  Both are **gated on the outgoing
member's nonsingularity**, exactly as `outgoingMatrix` is: a total
`fullDim` would force every member of every family nonsingular, which
`W3WallInput.no_total_fullDim_of_singularFamily` refutes, and the gated form is
what `W3WallInput.nd2_exists_fullDim`/`nd3_exists_fullDim` supply. -/
noncomputable def presentedProgressOfWallInputs
    (current : SemanticAtlasMarch.State degree
      (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (input : ∀ wall : coordinate, current.FirstWall wall →
      WallInput degree coordinate wall)
    (hnodup : ∀ (wall : coordinate) (hw : current.FirstWall wall)
      (i : Fin (input wall hw).case.arity) row,
      (((input wall hw).family.presentation i).path row).Nodup)
    (hsimple : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish)
    (incoming : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      Fin (input wall hw).case.arity)
    (hIncomingNonzero : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      (GluingDatum.LengthMatrixPresentation.matrix
        ((input wall hw).family.presentation (incoming wall hw))).det ≠ 0)
    (hIncomingMatrix : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      GluingDatum.LengthMatrixPresentation.matrix
          ((input wall hw).family.presentation (incoming wall hw)) =
        atlasChartMatrix coordinate degree current.toMatrixState.label)
    (fullDim : ∀ (wall : coordinate) (hw : current.FirstWall wall)
      (outgoing : Fin (input wall hw).case.arity),
      (GluingDatum.LengthMatrixPresentation.matrix
        ((input wall hw).family.presentation outgoing)).det ≠ 0 →
      DraismaVargas.LocalCases.FullDimensionalSource.FullDimensionalSourcePresentation
        (((input wall hw).family.candidate outgoing)).datum coordinate)
    (hFullDim : ∀ (wall : coordinate) (hw : current.FirstWall wall)
      (outgoing : Fin (input wall hw).case.arity)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((input wall hw).family.presentation outgoing)).det ≠ 0),
      (fullDim wall hw outgoing hdet).labelling.presentation =
        (input wall hw).family.presentation outgoing) :
    current.PresentedProgress where
  targetAt := fun wall hw ↦ (input wall hw).target
  dataAt := fun wall hw ↦ (input wall hw).data
  validAt := fun wall hw ↦ (input wall hw).valid
  targetConnectedAt := fun wall hw ↦ (input wall hw).targetConnected
  targetGenusAt := fun wall hw ↦ (input wall hw).targetGenus
  rootAt := fun wall hw ↦ (input wall hw).root
  simpleCrossings := hsimple
  targetWallAt := fun wall hw ↦ (input wall hw).wallVertex
  caseAt := fun wall hw ↦ (input wall hw).case
  familyAt := fun wall hw ↦ (input wall hw).family
  wallColumn := fun wall hw ↦ (input wall hw).family_wallColumn
  incomingAt := incoming
  incomingNonzero := hIncomingNonzero
  incomingMatrix := hIncomingMatrix
  outgoingLabel := atlasOutgoingLabel input hnodup current.toMatrixState.label
  outgoingMatrix := fun wall hw outgoing hdet ↦
    atlasMatrix_atlasOutgoingLabel input hnodup current.toMatrixState.label wall
      hw outgoing hdet
  fullDimAt := fullDim
  fullDimPresentation := hFullDim

/-- **The step.**  Every nonterminal semantic state with a `WallInput` at every
coordinate has a semantic successor. -/
theorem exists_step_of_wallInputs
    (current : SemanticAtlasMarch.State degree
      (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (input : ∀ wall : coordinate, current.FirstWall wall →
      WallInput degree coordinate wall)
    (hnodup : ∀ (wall : coordinate) (hw : current.FirstWall wall)
      (i : Fin (input wall hw).case.arity) row,
      (((input wall hw).family.presentation i).path row).Nodup)
    (hsimple : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish)
    (incoming : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      Fin (input wall hw).case.arity)
    (hIncomingNonzero : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      (GluingDatum.LengthMatrixPresentation.matrix
        ((input wall hw).family.presentation (incoming wall hw))).det ≠ 0)
    (hIncomingMatrix : ∀ (wall : coordinate) (hw : current.FirstWall wall),
      GluingDatum.LengthMatrixPresentation.matrix
          ((input wall hw).family.presentation (incoming wall hw)) =
        atlasChartMatrix coordinate degree current.toMatrixState.label)
    (fullDim : ∀ (wall : coordinate) (hw : current.FirstWall wall)
      (outgoing : Fin (input wall hw).case.arity),
      (GluingDatum.LengthMatrixPresentation.matrix
        ((input wall hw).family.presentation outgoing)).det ≠ 0 →
      DraismaVargas.LocalCases.FullDimensionalSource.FullDimensionalSourcePresentation
        (((input wall hw).family.candidate outgoing)).datum coordinate)
    (hFullDim : ∀ (wall : coordinate) (hw : current.FirstWall wall)
      (outgoing : Fin (input wall hw).case.arity)
      (hdet : (GluingDatum.LengthMatrixPresentation.matrix
        ((input wall hw).family.presentation outgoing)).det ≠ 0),
      (fullDim wall hw outgoing hdet).labelling.presentation =
        (input wall hw).family.presentation outgoing)
    (hNonterminal : ¬ current.Terminal) :
    ∃ next : SemanticAtlasMarch.State degree
      (atlasChartMatrix coordinate degree) baseStart baseFinish,
      SemanticAtlasMarch.State.Step current next := by
  obtain ⟨next, hstep, _⟩ :=
    (presentedProgressOfWallInputs current input hnodup hsimple incoming
      hIncomingNonzero hIncomingMatrix fullDim hFullDim).exists_step
      (fun label ↦ atlasChartMatrix_det_ne_zero label) hNonterminal
  exact ⟨next, hstep⟩

end Progress

end DraismaVargas.LocalCases.WallProgress
