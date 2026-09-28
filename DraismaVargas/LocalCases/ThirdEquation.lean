import DraismaVargas.LocalCases.WallProgress

/-!
# A third wall equation by the same route: the trivalent wall

`WallProgress` proves that the wall valency is pinned by
`val(w₀) + ch(w₀) = 4` and that **four** values occur, not two;
`MonovalentWall` then leaves exactly the target valencies `{2, 3, 4}` on the
full-dimensional/forest bundle.  `val(w₀) = 4` reaches a presented family
through `W4Bridge`, and `val(w₀) = 2` through `SecondEquation`.  This module
runs the same route at `val(w₀) = 3`, the `(2,3)` line of the table, whose four
`SourceCase` tags are `w3Four`, `w3Shift`, `w3Nd3CoarseFine` and
`w3Nd2CoarseFine`.

The actual distinguished-block profiles are derived from `W3SourceInput` in
`W3R1SourceProfile`: nd2, or the three nd3 subcases of Figures 28--30, from
literal surviving occurrences and the paper's non-dangling ramification formula.
The nd2 indices are `k, k+1` on distinct target occurrences and a common stable
path.  In nd3, a maximal-index survivor has a target direction distinct from
both others; the other two either share a direction or not, with the exact
source index equations.  In particular a distinguished block with `nd = 0`, or a
singleton distinguished block -- both allowed by the interface `W3SourceInput`
alone, and discussed as such below -- does not occur for an actual source.
These are source profiles, not outgoing stable-row or determinant data; the
refinements constructed at the end of this file are interface constructors, not
the source-correct families.

As at the other two valencies, only the numerology changes, and this time it
changes in the *simplifying* direction.

* `W3SourceInput` is the trivalent analogue of `AuxR0SourceInput` and
  `W2SourceInput`, with the same five fields: validity, the stable-path count,
  dangling-no-glue, the wall-block valency trichotomy, and Equation (C).
* `w3SourceInput_of_contraction` discharges all five through exactly the
  theorems `W4Bridge` and `SecondEquation` use — `valid_contractDatum`,
  `stablePath_card_contractDatum`, `danglingEdgeNoGlue_contractDatum`,
  `wallBlock_nonDanglingValency_eq_zero_or_two_or_three` and
  `targetExcess_contractDatum_merge_eq_one`.  Not one of them is
  valency-specific; Equation (C) in particular is `exc(w₀) = exc(u) + exc(v) + 1`
  with both summands zero by change-minimality.
* `targetChange_eq_one` is the whole divergence, and it is
  `WallProgress.targetChange_merge_eq_one_of_trivalent` read on the interface:
  `exc = ch + val - 3 = 1` reads `ch(w₀) = 0` at a four-valent wall and
  `ch(w₀) = 2` at a divalent one; here it reads `ch(w₀) = 1`.
* `threeStarMerge` and `endpoints_of_threeStar` are the bookkeeping in both
  directions, mirroring `fourStarMerge`/`endpoints_trivalent_of_fourStar` and
  `twoStarMerge`/`endpoints_of_twoStar`.

## The numerology at the merged vertex

`ThreeStar` at the merged vertex gives `val(u) + val(v) = 5` by
`card_incidentEdges_merge`, and change-minimality gives `val ≤ 3` at every
target vertex, so the contracted occurrence joins endpoints of valencies
`(2,3)` or `(3,2)` and **nothing else** — against three splits at a divalent
wall and the single `(3,3)` at a four-valent one.  `endpoints_of_threeStar`
records this with `ch(u) + ch(v) = 1`, the same `1` that `targetChange_eq_one`
reaches from the other side; `targetChange_contractDatum_merge_eq_one` is the
proof that the two routes agree, and their inputs are disjoint — one sees only
the wall datum, the other only the datum being contracted plus the
source-topology receipt `hForest`.

## Why the hypotheses can hold at once

**Verdict: the hypothesis bundle of `w3SourceInput_of_contraction` is
inhabited, and the model is the one `WallProgress` predicted.**  A witness is
exhibited below at `|E(target)| = 9`, `degree = 3`, `c(H) = 1`,
`g(source) = 4`; the smaller admissible count `|E(target)| = 3` is excluded by
counting alone, with no hand argument (`card_target_edges_eq_nine_le`), which
is where the trivalent wall is *easier* than the divalent one.

*The two data are different data, by design.*  `fullDim` is a presentation of
`data`; the conclusion is an interface for `contractDatum data ...`.  The two
`FullDimensionalSource` inconsistencies are inconsistencies *within one datum*:
`equation_c` versus `ChangeMinimal`, and `stablePath_card` versus a square
labelling.  Here `ChangeMinimal` and the square labelling are asserted of
`data` only, while `equation_c` and `stablePath_card` are asserted of
`contractDatum data ...` only.  Both of `W4Bridge`'s receipts for that reading
are valency-free and apply verbatim: `targetExcess_contractDatum_merge_eq_one`
*derives* the wall's excess `1` from the full-dimensional datum's excess `0` at
both ends, and `not_nonempty_labelling_contractDatum` proves the wall datum has
no square labelling of its own.

*The arithmetic every model must satisfy, taken from the library's counting
theorems.*
`SecondEquation.card_target_edges_eq_six_mul` gives

```
|E(target)| = 6 · (degree + c(H)) - 15,
```

so `|E(target)| ∈ {3, 9, 15, …}`, and `four_le_card_target_edges_of_threeStar`
gives `|E(target)| ≥ 4` because a three-star at the merged vertex needs three
occurrences in the *contracted* target.  Together
(`card_target_edges_eq_nine_le`) `|E(target)| ≥ 9`, hence `degree + c(H) ≥ 4`
and, with `1 ≤ c(H)` and `g = 2 degree - 5 + 3 c(H)`, the smallest case is
`|E(target)| = 9`, `degree = 3`, `c(H) = 1`, `g(source) = 4`.  The witness below
passes this test, and passes `3 g - 3 c` and `saturated` separately.

*The witness.*  As `WallProgress`'s module docstring indicates — "the trivalent
`z` with two leaves and a length-seven branch: contracting `z u₁` is the `(3,2)`
split, `val(w₀) = 3`" — it lives on the very fibre `SecondEquation` pairs with
that target.  What decides the bundle is the **sheet labelling**:
of the `729` change-minimal fibres on this target carrying `SecondEquation`'s
block profile, `720` are full-dimensional presentations, and exactly `336` of
those satisfy the bundle at `z u₁`.  The naive labelling — every non-discrete partition equal to
`01∣2` — is in neither set: its source is *disconnected*, of genus `5`, so it is
not a presentation at all, and its merged block has source degree `5` with no
dangling incidence, `nd = 5`, so `hTrivalent` would fail as well.  The labelling
below was found by searching the change-minimal fibres against the counting
theorems, not by drawing a picture.

Target: the trivalent `z` with leaf neighbours `a`, `a₂` and the branch
`z — u₁ — ⋯ — u₆ — u₇`, `u₇` a leaf; ten vertices, nine occurrences.
Fibre at `degree = 3`, writing a sheet partition as its blocks:

| vertex | `z` | `a` | `a₂` | `u₁` | `u₂` | `u₃` | `u₄` | `u₅` | `u₆` | `u₇` |
|---|---|---|---|---|---|---|---|---|---|---|
| partition | `0∣1∣2` | `01∣2` | `01∣2` | `02∣1` | `02∣1` | `01∣2` | `01∣2` | `01∣2` | `01∣2` | `01∣2` |
| `b(v)` | 3 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| `val(v)` | 3 | 1 | 1 | 2 | 2 | 2 | 2 | 2 | 2 | 1 |
| `ch(v)` | 0 | 2 | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 2 |

| occurrence | `za` | `za₂` | `zu₁` | `u₁u₂` | `u₂u₃` | `u₃u₄` | `u₄u₅` | `u₅u₆` | `u₆u₇` |
|---|---|---|---|---|---|---|---|---|---|
| partition | `0∣1∣2` | `0∣1∣2` | `0∣1∣2` | `02∣1` | `0∣1∣2` | `01∣2` | `0∣1∣2` | `01∣2` | `0∣1∣2` |
| `m(e)` | 3 | 3 | 3 | 2 | 3 | 2 | 3 | 2 | 3 |

`b(z) = 3`, `b = 2` above every other vertex, and `m = (3,3,3,2,3,2,3,2,3)`:
this is `SecondEquation`'s `(1,3)` fibre exactly, with the blocks named.  Every
occurrence partition refines both endpoint partitions — the only two that are
not discrete are `u₁u₂ = 02∣1`, matching `u₁` and `u₂`, and `u₃u₄`, `u₅u₆`
`= 01∣2`, matching their endpoints — and
`ch(v) = ∑_{e ∋ v} m(e) - 2 b(v) - degree · (val(v) - 2)`
(`GluingDatum.targetChange_eq_card_formula`) gives the `ch` row above, so
`ch(v) + val(v) - 3 = 0` at every vertex and `fullDim.changeMinimal` holds.

The source has `∑ b(v) = 21` vertices and `∑ m(e) = 24` occurrences, is
connected, and so `g(source) = 24 - 21 + 1 = 4`.  Eight occurrences are dangling
— the sheet-`2` occurrences above `za`, `za₂`, `zu₁`, `u₂u₃`, `u₃u₄`, `u₄u₅`,
`u₅u₆`, `u₆u₇` — and each is a singleton block, so `danglingEdgeNoGlue` holds;
eight source vertices have `nd = 0`, so `stableComponentCount = 1 + 8 - 8 = 1`
(`TrivalenceClosure.stableComponentCount_eq_card_danglingEdges`).  Six source
vertices have `nd = 3` and seven have `nd = 2`, so the stable graph is trivalent
with `9` stable paths — `fullDim.stablePath_card` reads `9 = |E(target)|` — and
no stable path is a cycle, so `pathEnds` holds.  The three identities check:
`6 · (3 + 1) - 15 = 9`, `3 · 4 - 3 · 1 = 9`, and `fullDim.saturated` reads
`9 = 2 · 4 + 2 · 3 - 5`.

Contract `z u₁`: `val(z) = 3`, `val(u₁) = 2`, the `(3,2)` split of
`valencySplit_of_threeStar`, and `ch(z) + ch(u₁) = 0 + 1 = 1`.  The merged
partition is `join(0∣1∣2, 02∣1) = 02∣1`, so `b(w₀) = 2`, and `hForest` reads
`2 + 1 = 2 + 1` on the block `{0,2}` and `1 + 1 = 1 + 1` on the block `{1}`.  At
the merged vertex `val = 3` and `∑_{e ∋ w₀} m(e) = 3 + 3 + 2 = 8`, so
`ch(w₀) = 8 - 4 - 3 = 1` and `exc(w₀) = 1`, with local ramification `1` on the
block `{0,2}` and `0` on the block `{1}` — **one unit on exactly one block**,
which is `WallProgress.exists_unique_localRamification_of_targetChange_eq_one`
realised.  Their source degrees are `r + 2 + |A| = 1 + 2 + 2 = 5` and
`0 + 2 + 1 = 3` (`card_incidentSourceEdge_wallBlock` below) and both have
`nd = 3`, so `hTrivalent` holds — the ramified block deletes two of its five
incidences, which is `exists_isDangling_distinguishedBlock` in the model.  The
contracted datum again has nine stable paths, so `hStable` holds, and every
surviving occurrence dangling downstairs is dangling upstairs, so `hReflected`
holds.

Two further facts from the same search, recorded because they are the kind of
claim that is cheap to get wrong by eye.  First, on this target `z u₁` is the
**only** occurrence whose contraction satisfies the bundle.  Second, on the
ten-vertex path — `SecondEquation`'s other model — no occurrence does, and the
reason is not subtle: a path has `val ≤ 2` everywhere, so `val(u) + val(v) ≤ 4`
and `endpoints_of_threeStar`'s `5` is unreachable.  The trivalent wall is
genuinely a different picture from the divalent one, not a relabelling of it.

Finally, the bundle is not rare.  Enumerating *all* change-minimal fibres at
`degree = 3` over *all* thirty-seven ten-vertex trees of maximum valency three
gives `31215` full-dimensional presentations, of which `10998` carry an
occurrence whose contraction satisfies the whole bundle.  The `|E(target)| = 9`
floor of `card_target_edges_eq_nine_le` is therefore attained, and attained
often.

*What this file proves about the above, rather than asserting it.*
`four_le_card_target_edges_of_threeStar` and `card_target_edges_eq_nine_le`
(the numerology, with no `|E| = 3` branch to exclude by hand);
`valencySplit_of_threeStar` (the two splits and the change each forces);
`targetChange_contractDatum_merge_eq_one` (the two routes to `ch(w₀) = 1`
agree); and, on a `W3SourceInput` itself, `sum_localRamification`,
`localRamification_le_one`, `exists_unique_localRamification` (**the trivalent
wall is ramified on exactly one block** — no split branch, which is the
structural simplification over `SecondEquation`),
`card_incidentSourceEdge_wallBlock`,
`exists_isDangling_distinguishedBlock` and
`exists_isDangling_of_one_lt_blockCard`.

The model itself is prose, as `W4Bridge`'s and `SecondEquation`'s are, and is
not formalized as a `FullDimensionalSourcePresentation`.  The prose is
falsifiable: it was produced by testing candidate fibres against
`card_target_edges_eq_six_mul` and the derived checks rather than by drawing a
picture.

## Routing into the four shapes

`SecondEquation.W2SourceInput.ramification_split_or_concentrated` had to branch, because
`ch(w₀) = 2` can sit on one block or on two.  Here `ch(w₀) = 1` and
`WallProgress.exists_unique_localRamification_of_targetChange_eq_one` says the
single unit sits on exactly one block, so **there is no split branch**: the
four shapes are shapes of one distinguished block, and the invariant that
separates them is that block's surviving valency.  `distinguishedBlock` and
`route` below carry this: at the level of the interface the distinguished
block's `nd` is `3` (Equations (2), (3), (4) — the `w3-r1-nd3-*` family, whose
coarse-fine member is the `nd3` half of `ResolutionCoarseFine`), `2`
(Equation (5), `w3-r1-nd2`, the `nd2` half of `ResolutionCoarseFine`), or `0`.

The geometries of the global candidates (for instance
`GlobalCoarseFine.Nd3Geometry` and `GlobalCoarseFine.Nd2Geometry`) carry a
refinement of the wall partition as a *field* (`fine`, `endpoint`), because in
the paper it is the incoming resolution's endpoint.  A `W3SourceInput` does
determine one such refinement on its own — detach a single sheet from the
distinguished block: `nd2Geometry` builds Equation (5)'s geometry from it as
soon as the distinguished block has two sheets, and `shiftEndpoint` builds the
refinement Equation (3) runs on as soon as it has three.  The one alternative
the interface allows is a singleton distinguished block, which then has source
degree exactly four and deletes exactly one of its occurrences
(`card_incidentSourceEdge_distinguishedBlock_eq_four`).  What stays an input
rather than a consequence is *which* shape the incoming resolution puts the wall
in — `t2` versus `t3`, `a = k₄` versus `a > k₄` — exactly as on the divalent
side.
-/

namespace DraismaVargas.LocalCases.ThirdEquation

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.W4Bridge
open DraismaVargas.LocalCases.WallProgress

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-! ## The trivalent target star

`W2R1Target.TwoStar` and `W4TargetPairings.FourStar` are the divalent and
four-valent labelled stars; the trivalent one is not defined elsewhere, so it is
introduced here in exactly their shape. -/

/-- A labelling of the three occurrences at a trivalent target vertex. -/
structure ThreeStar (target : CFGraph) (wall : target.V) where
  label : Fin 3 ≃ {edge : target.edges // edge ∈ GluingDatum.incidentEdges wall}

/-- Canonically label the incident occurrences of any trivalent target
vertex. -/
noncomputable def ThreeStar.of_card {wall : target.V}
    (hcard : (GluingDatum.incidentEdges wall).card = 3) :
    ThreeStar target wall where
  label := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm

/-- A three-star is exactly a trivalent vertex. -/
@[simp] theorem ThreeStar.card_incidentEdges {wall : target.V}
    (star : ThreeStar target wall) :
    (GluingDatum.incidentEdges wall).card = 3 := by
  classical
  have hCard := Fintype.card_congr star.label
  simpa using hCard.symm

/-! ## The trivalent wall source interface -/

/-- The source-facing interface at a **trivalent** wall.  Field for field the
same as `W4StableSource.AuxR0SourceInput` and `SecondEquation.W2SourceInput`;
only the star, and hence the number `targetChange_eq_one` reads off Equation
(C), is different. -/
structure W3SourceInput {wall : target.V}
    (data : GluingDatum target degree)
    (star : ThreeStar target wall) where
  valid : data.Valid
  stablePath_card : Fintype.card (StablePath data) = target.edges.card + 1
  dangling_no_glue : DanglingEdgeNoGlue data
  nonDangling_valency : ∀ sourceBlock : WallBlock data wall,
    nonDanglingValency data
        (WallBlock.sourceVertex data wall sourceBlock) = 0 ∨
      nonDanglingValency data
          (WallBlock.sourceVertex data wall sourceBlock) = 2 ∨
        nonDanglingValency data
          (WallBlock.sourceVertex data wall sourceBlock) = 3
  equation_c : data.targetExcess wall = 1

namespace W3SourceInput

variable {wall : target.V}

/-- **The divergence from W4 and from W2, in one line.**  `exc = ch + val - 3`
with `val = 3` reads `ch(w₀) = 1`, against `0` at a four-valent wall and `2` at
a divalent one. -/
theorem targetChange_eq_one {data : GluingDatum target degree}
    {star : ThreeStar target wall} (input : W3SourceInput data star) :
    data.targetChange wall = 1 := by
  have hCard := star.card_incidentEdges
  have hEquation := input.equation_c
  unfold GluingDatum.targetExcess at hEquation
  omega

end W3SourceInput

/-! ## The merge -/

/-- Contracting an occurrence whose two endpoint valencies sum to `5`. -/
noncomputable def threeStarMerge (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (hCard : (GluingDatum.incidentEdges a).card
      + (GluingDatum.incidentEdges b).card = 5) :
    ThreeStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩ :=
  ThreeStar.of_card (by
    have hMerge := card_incidentEdges_merge hc hab hOne
    omega)

/-- The converse bookkeeping, the trivalent line of `WallProgress`'s
`endpoints_of_contraction`. -/
theorem endpoints_of_threeStar (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (star : ThreeStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    (GluingDatum.incidentEdges a).card
        + (GluingDatum.incidentEdges b).card = 5 ∧
      (GluingDatum.incidentEdges a).card ≤ 3 ∧
        (GluingDatum.incidentEdges b).card ≤ 3 ∧
          data.targetChange a + data.targetChange b = 1 := by
  have hStar := star.card_incidentEdges
  obtain ⟨hMerge, _, hLeftLe, _, hRightLe, hLeftChange, hRightChange⟩ :=
    endpoints_of_contraction data hc hab hOne hValid hMinimal
  refine ⟨by omega, hLeftLe, hRightLe, ?_⟩
  have hLeftCast : ((GluingDatum.incidentEdges a).card : ℤ)
      + ((GluingDatum.incidentEdges b).card : ℤ) = 5 := by
    have : (GluingDatum.incidentEdges a).card
        + (GluingDatum.incidentEdges b).card = 5 := by omega
    exact_mod_cast this
  linarith

/-! ## The bridge -/

/-- **The main theorem.**  A full-dimensional presentation of `data`, together
with the contraction receipts, feeds `W3SourceInput` for the *contracted* datum
at the merged vertex.  Every field is discharged by the very same valency-free
theorems that `W4Bridge.auxR0SourceInput_of_contraction` and
`SecondEquation.w2SourceInput_of_contraction` use. -/
theorem w3SourceInput_of_contraction {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {star : ThreeStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩}
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hStable : Nonempty
      (StablePath (contractDatum data hc hab hOne) ≃ StablePath data))
    (hReflected : DanglingReflected data hc hab hOne)
    (hTrivalent : ∀ sourceBlock : WallBlock (contractDatum data hc hab hOne)
        ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
            sourceBlock) ≤ 3) :
    W3SourceInput (contractDatum data hc hab hOne) star where
  valid := valid_contractDatum data hc hab hOne hForest fullDim.valid
  stablePath_card :=
    stablePath_card_contractDatum data hc hab hOne fullDim hStable
  dangling_no_glue :=
    danglingEdgeNoGlue_contractDatum data hReflected fullDim.danglingEdgeNoGlue
  nonDangling_valency :=
    wallBlock_nonDanglingValency_eq_zero_or_two_or_three
      (contractDatum data hc hab hOne)
      (valid_contractDatum data hc hab hOne hForest fullDim.valid) hTrivalent
  equation_c :=
    targetExcess_contractDatum_merge_eq_one data hc hab hOne hForest
      fullDim.changeMinimal

/-! ## What the numerology allows at a trivalent wall -/

section Numerology

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The trivalent wall inherits the four-valent wall's lower bound, not the
divalent wall's.**  A three-star at the merged vertex needs three occurrences in
the *contracted* target, so `|E(target)| ≥ 4`; a two-star needs only two and
`SecondEquation.three_le_card_target_edges_of_twoStar` stops at `3`. -/
theorem four_le_card_target_edges_of_threeStar
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (star : ThreeStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    4 ≤ target.edges.card := by
  classical
  have hStar := star.card_incidentEdges
  have hLe : (GluingDatum.incidentEdges
      (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V)).card
      ≤ Fintype.card ((GraphContraction.contract target hab hOne).edges) :=
    Finset.card_le_univ _
  have hCoe : Fintype.card ((GraphContraction.contract target hab hOne).edges)
      = Multiset.card (GraphContraction.contract target hab hOne).edges :=
    Multiset.card_coe _
  have hContract := edge_card_contract hab hOne
  omega

/-- **Everything counting gives at a trivalent wall, and it is everything.**
`SecondEquation.card_target_edges_eq_six_mul` puts `|E(target)|` in
`{3, 9, 15, …}` and `four_le_card_target_edges_of_threeStar` rules out `3`, so
the target has at least nine occurrences outright.  `SecondEquation`'s divalent
counterpart `card_target_edges_eq_three_or_nine_le` cannot close this way: its
`|E(target)| = 3` branch survives the count and is excluded in that module's
docstring by hand, through the forced `degree = 2` fibre over a four-vertex
tree.  Here there is no branch to exclude. -/
theorem card_target_edges_eq_nine_le (data : GluingDatum target degree)
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    9 ≤ target.edges.card := by
  have hFour := four_le_card_target_edges_of_threeStar hab hOne star
  have hCount := SecondEquation.card_target_edges_eq_six_mul data fullDim
  have hComponent :=
    TrivalenceClosure.one_le_stableComponentCount_of_presentation fullDim
  have hDegree : 1 ≤ (degree : ℤ) := by exact_mod_cast data.degree_pos
  omega

/-- **The smallest trivalent wall, as numbers.**  At `|E(target)| = 9` the two
identities of `TrivalenceClosure` leave exactly `degree + c(H) = 4`, and with
`1 ≤ c(H)` and `1 ≤ degree` the source genus is pinned by the component count.
The witness in the module docstring is the case `c(H) = 1`, `degree = 3`,
`g(source) = 4`. -/
theorem degree_add_stableComponentCount_of_card_target_edges_eq_nine
    (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hNine : target.edges.card = 9) :
    (degree : ℤ) + TrivalenceClosure.stableComponentCount data = 4 ∧
      genus data.sourceGraph
        = 2 * (degree : ℤ) - 5 + 3 * TrivalenceClosure.stableComponentCount data := by
  have hCount := SecondEquation.card_target_edges_eq_six_mul data fullDim
  rw [hNine] at hCount
  norm_num at hCount
  exact ⟨by linarith,
    TrivalenceClosure.genus_sourceGraph_eq_of_presentation fullDim⟩

end Numerology

/-! ## The two valency splits, and the change each forces -/

/-- **The trivalent analogue of `W4Bridge.endpoints_trivalent_of_fourStar` and
`SecondEquation.valencySplit_of_twoStar`.**  A three-star at the merged vertex
leaves exactly **two** possibilities for the valencies of the two contracted
endpoints -- fewer than the divalent wall's three -- and change-minimality of
the datum being contracted then reads the change at each endpoint off its
valency.  The single unit of change sits entirely on the divalent endpoint in
both. -/
theorem valencySplit_of_threeStar (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (star : ThreeStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    ((GluingDatum.incidentEdges a).card = 2 ∧
        (GluingDatum.incidentEdges b).card = 3 ∧
          data.targetChange a = 1 ∧ data.targetChange b = 0) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧
          (GluingDatum.incidentEdges b).card = 2 ∧
            data.targetChange a = 0 ∧ data.targetChange b = 1) := by
  obtain ⟨hSum, hLeftLe, hRightLe, _⟩ :=
    endpoints_of_threeStar data hc hab hOne hValid hMinimal star
  obtain ⟨_, hLeftMem, _, hRightMem, _, hLeftChange, hRightChange⟩ :=
    endpoints_of_contraction data hc hab hOne hValid hMinimal
  have hLeft : (GluingDatum.incidentEdges a).card = 2 ∨
      (GluingDatum.incidentEdges a).card = 3 := by omega
  rcases hLeft with hLeft | hLeft
  · refine Or.inl ⟨hLeft, by omega, ?_, ?_⟩ <;>
      · rw [hLeft] at hLeftChange
        have hRight : (GluingDatum.incidentEdges b).card = 3 := by omega
        rw [hRight] at hRightChange
        push_cast at hLeftChange hRightChange
        linarith
  · refine Or.inr ⟨hLeft, by omega, ?_, ?_⟩ <;>
      · rw [hLeft] at hLeftChange
        have hRight : (GluingDatum.incidentEdges b).card = 2 := by omega
        rw [hRight] at hRightChange
        push_cast at hLeftChange hRightChange
        linarith

/-- **The two routes to `ch(w₀) = 1` agree.**  `W3SourceInput.targetChange_eq_one`
reaches it downstairs, from Equation (C) and `val(w₀) = 3`; this reaches it
upstairs, from `W4Bridge.targetChange_contractDatum_merge` and the endpoint
bookkeeping.  The inputs are disjoint -- the first sees only the wall datum, the
second only the datum being contracted together with the source-topology receipt
`hForest` -- so the agreement is a consistency check on the bundle rather than a
restatement of one of its fields.  `WallProgress.targetChange_merge_eq_one_of_trivalent`
is the same number reached from the valency alone. -/
theorem targetChange_contractDatum_merge_eq_one (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (hForest : ContractionForest data a b contracted)
    (star : ThreeStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ = 1 := by
  obtain ⟨_, _, _, hChange⟩ :=
    endpoints_of_threeStar data hc hab hOne hValid hMinimal star
  rw [targetChange_contractDatum_merge data hc hab hOne hForest, hChange]

/-! ## The ramification the trivalent wall is obliged to carry -/

namespace W3SourceInput

variable {wall : target.V} {data : GluingDatum target degree}
  {star : ThreeStar target wall}

/-- The total ramification above the trivalent wall is exactly one unit.  This
is `targetChange_eq_one` with the definition of `targetChange` unfolded, in the
form the block-by-block statements below consume. -/
theorem sum_localRamification (input : W3SourceInput data star) :
    (∑ sourceBlock : WallBlock data wall,
      data.localRamification wall sourceBlock) = 1 := by
  have hChange := input.targetChange_eq_one
  unfold GluingDatum.targetChange at hChange
  exact hChange

/-- Riemann--Hurwitz at the wall: every block's local ramification is
nonnegative. -/
theorem localRamification_nonneg (input : W3SourceInput data star)
    (sourceBlock : WallBlock data wall) :
    0 ≤ data.localRamification wall sourceBlock :=
  data.localRamification_nonneg wall (input.valid.2 wall) sourceBlock

/-- No block above the trivalent wall carries more than the whole unit. -/
theorem localRamification_le_one (input : W3SourceInput data star)
    (sourceBlock : WallBlock data wall) :
    data.localRamification wall sourceBlock ≤ 1 := by
  have hSingle := Finset.single_le_sum
    (f := fun block : WallBlock data wall ↦ data.localRamification wall block)
    (fun block _ ↦ input.localRamification_nonneg block)
    (Finset.mem_univ sourceBlock)
  rw [input.sum_localRamification] at hSingle
  exact hSingle

/-- **The trivalent wall is ramified on exactly one block, and there is no
split branch.**  This is `WallProgress.exists_unique_localRamification_of_targetChange_eq_one`
read on the interface, and it is the structural divergence from
`SecondEquation`: there `ch(w₀) = 2` splits across two blocks or concentrates on
one, and `ramification_split_or_concentrated` has to branch; here the single
unit has nothing to split into, so the four `w3` shapes are four shapes of *one*
distinguished block. -/
theorem exists_unique_localRamification (input : W3SourceInput data star) :
    ∃ sourceBlock : WallBlock data wall,
      data.localRamification wall sourceBlock = 1 ∧
        ∀ other : WallBlock data wall, other ≠ sourceBlock →
          data.localRamification wall other = 0 :=
  exists_unique_localRamification_of_targetChange_eq_one data wall input.valid
    input.targetChange_eq_one

/-- The distinguished block: the unique block above the trivalent wall that
carries the wall's single unit of ramification. -/
noncomputable def distinguishedBlock (input : W3SourceInput data star) :
    WallBlock data wall :=
  input.exists_unique_localRamification.choose

@[simp] theorem localRamification_distinguishedBlock
    (input : W3SourceInput data star) :
    data.localRamification wall input.distinguishedBlock = 1 :=
  input.exists_unique_localRamification.choose_spec.1

theorem localRamification_eq_zero_of_ne (input : W3SourceInput data star)
    {other : WallBlock data wall} (hNe : other ≠ input.distinguishedBlock) :
    data.localRamification wall other = 0 :=
  input.exists_unique_localRamification.choose_spec.2 other hNe

/-- The source degree of a wall block, in terms of its local ramification.  At a
trivalent wall `val(w₀) - 2 = 1`, so
`NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form` reads
`N(A) = r(A) + 2 + |A|`: one more than the divalent wall's `r(A) + 2`
(`SecondEquation.W2SourceInput.card_incidentSourceEdge_wallBlock`) for every block of size
one, and more still for larger blocks.  Only `val(w₀) = 3` is used, so this is
stated for the three-star rather than for a `W3SourceInput`. -/
theorem card_incidentSourceEdge_wallBlock (star : ThreeStar target wall)
    (sourceBlock : WallBlock data wall) :
    (Fintype.card (IncidentSourceEdge data
        (WallBlock.sourceVertex data wall sourceBlock)) : ℤ)
      = data.localRamification wall sourceBlock + 2
          + ((data.vertexPartition wall).blockCard sourceBlock.1 : ℤ) := by
  have hForm := card_incidentSourceEdge_eq_localRamification_form data
    (WallBlock.sourceVertex data wall sourceBlock)
  have hTrivalent : (GluingDatum.incidentEdges
      (WallBlock.sourceVertex data wall sourceBlock).1.1).card = 3 :=
    star.card_incidentEdges
  have hBlock : data.localRamification
      (WallBlock.sourceVertex data wall sourceBlock).1.1
      ⟨(WallBlock.sourceVertex data wall sourceBlock).1.2,
        (WallBlock.sourceVertex data wall sourceBlock).2⟩
      = data.localRamification wall sourceBlock :=
    congrArg (data.localRamification wall) (Subtype.ext sourceBlock.2)
  have hCard : (data.vertexPartition
      (WallBlock.sourceVertex data wall sourceBlock).1.1).blockCard
        (WallBlock.sourceVertex data wall sourceBlock).1.2
      = (data.vertexPartition wall).blockCard sourceBlock.1 :=
    congrArg (data.vertexPartition wall).blockCard sourceBlock.2
  rw [hTrivalent, hBlock, hCard] at hForm
  push_cast at hForm ⊢
  linarith

/-- **A wall block whose source degree exceeds three deletes an occurrence.**
The trichotomy caps the surviving valency at `3`, so any excess incidence is
dangling.  This is the trivalent counterpart of
`SecondEquation.W2SourceInput.exists_isDangling_of_localRamification_eq_two`. -/
theorem exists_isDangling_of_four_le_card_incidentSourceEdge
    (input : W3SourceInput data star) (sourceBlock : WallBlock data wall)
    (hFour : 4 ≤ Fintype.card (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall sourceBlock))) :
    ∃ edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall sourceBlock),
      IsDangling data edge.1 := by
  classical
  by_contra hNone
  push Not at hNone
  have hFilter := StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency
    data (WallBlock.sourceVertex data wall sourceBlock)
  have hAll : ((Finset.univ : Finset (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall sourceBlock))).filter
        (fun edge ↦ ¬ IsDangling data edge.1)) = Finset.univ :=
    Finset.filter_true_of_mem fun edge _ ↦ hNone edge
  rw [hAll, Finset.card_univ] at hFilter
  have hTrichotomy := input.nonDangling_valency sourceBlock
  omega

/-- **The distinguished block always deletes an occurrence.**  Its source degree
is `r + 2 + |A| = 3 + |A| ≥ 4` by `card_incidentSourceEdge_wallBlock`, while
`nonDangling_valency` caps its surviving valency at `3`.  So the trivalent
wall's single unit of change is *never* paid for honestly: unlike the divalent
wall, which has a split branch in which both ramified blocks may keep all their
occurrences, here the one ramified block is forced to be dangling somewhere. -/
theorem exists_isDangling_distinguishedBlock (input : W3SourceInput data star) :
    ∃ edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall input.distinguishedBlock),
      IsDangling data edge.1 := by
  refine input.exists_isDangling_of_four_le_card_incidentSourceEdge
    input.distinguishedBlock ?_
  have hCard := card_incidentSourceEdge_wallBlock (data := data) star
    input.distinguishedBlock
  rw [input.localRamification_distinguishedBlock] at hCard
  have hPos : 0 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1 :=
    (data.vertexPartition wall).blockCard_pos _
  have hPosCast : (1 : ℤ) ≤ ((data.vertexPartition wall).blockCard
      input.distinguishedBlock.1 : ℤ) := by exact_mod_cast hPos
  have : (4 : ℤ) ≤ (Fintype.card (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) : ℤ) := by
    linarith
  exact_mod_cast this

/-- **Any wall block of size at least two deletes an occurrence**, ramified or
not: its source degree is at least `2 + 2 = 4`.  With
`exists_isDangling_distinguishedBlock` this says that at a trivalent wall the
only blocks that can keep all of their occurrences are the unramified
singletons. -/
theorem exists_isDangling_of_one_lt_blockCard (input : W3SourceInput data star)
    (sourceBlock : WallBlock data wall)
    (hCard : 1 < (data.vertexPartition wall).blockCard sourceBlock.1) :
    ∃ edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall sourceBlock),
      IsDangling data edge.1 := by
  refine input.exists_isDangling_of_four_le_card_incidentSourceEdge sourceBlock ?_
  have hForm := card_incidentSourceEdge_wallBlock (data := data) star sourceBlock
  have hNonneg := input.localRamification_nonneg sourceBlock
  have hCardCast : (2 : ℤ) ≤ ((data.vertexPartition wall).blockCard
      sourceBlock.1 : ℤ) := by exact_mod_cast hCard
  have : (4 : ℤ) ≤ (Fintype.card (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall sourceBlock)) : ℤ) := by linarith
  exact_mod_cast this

end W3SourceInput

/-! ## Routing into the four `w3` shapes -/

section Routing

variable {wall : target.V} {data : GluingDatum target degree}
  {star : ThreeStar target wall}

namespace W3SourceInput

/-- **The routing invariant, and why there is only one.**  The trivalent wall's
single unit of change sits on one block (`W3SourceInput.exists_unique_localRamification`),
so every `w3` shape is a shape of that one block and the invariant that
separates them is its surviving valency.  `nd = 3` is the `w3-r1-nd3-*` family —
Equations (2), (3) and (4), tags `w3Four`, `w3Shift`, `w3Nd3CoarseFine`, the last
resolved by the `nd3` half of `ResolutionCoarseFine`; `nd = 2` is Equation (5),
tag `w3Nd2CoarseFine`, the
`nd2` half of `ResolutionCoarseFine`; `nd = 0` is the isolated block, which is
not a wall shape at all.  This is the trivalent replacement for
`SecondEquation.W2SourceInput.ramification_split_or_concentrated`, and it is a trichotomy on
one block rather than a genuine branch on how the change is distributed. -/
theorem route (input : W3SourceInput data star) :
    nonDanglingValency data
        (WallBlock.sourceVertex data wall input.distinguishedBlock) = 3 ∨
      nonDanglingValency data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) = 2 ∨
        nonDanglingValency data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) = 0 := by
  rcases input.nonDangling_valency input.distinguishedBlock with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

/-- **The distinguished singleton block deletes exactly one occurrence.**  A
block of size one above a trivalent wall carrying the unit of ramification has
source degree `1 + 2 + 1 = 4`, so the trichotomy caps its surviving valency at
`3` and exactly one of its four incidences is dangling.  Together with
`W3SourceInput.exists_isDangling_of_one_lt_blockCard`, which handles every block
of size at least two, this says the trivalent wall never balances honestly. -/
theorem card_incidentSourceEdge_distinguishedBlock_eq_four
    (input : W3SourceInput data star)
    (hCard : (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1 = 1) :
    Fintype.card (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) = 4 := by
  have hForm := card_incidentSourceEdge_wallBlock (data := data)
    star input.distinguishedBlock
  rw [input.localRamification_distinguishedBlock, hCard] at hForm
  exact_mod_cast hForm

/-! ### The one refinement a `W3SourceInput` can manufacture on its own

The geometries of the global candidates (`GlobalCoarseFine.Nd3Geometry`,
`GlobalCoarseFine.Nd2Geometry`, and those of Equations (2) and (3)) all carry a
refinement of the wall partition as a *field* (`fine`, `endpoint`), because in
the paper it comes from the incoming
resolution's endpoint, which a wall interface does not see.  What the interface
does determine is the distinguished block, and a block of size at least two
admits one canonical refinement: detach a single sheet.  That single detachment
supplies Equation (5)'s geometry outright and Equations (2) and (4)'s geometry
in their `k₂ = 1` form. -/

/-- A sheet of the distinguished block other than its representative. -/
noncomputable def detachedSheet (input : W3SourceInput data star)
    (hCard : 1 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) : Fin degree :=
  ((data.vertexPartition wall).exists_other_of_one_lt_blockCard
    input.distinguishedBlock.1 hCard).choose

theorem rel_detachedSheet (input : W3SourceInput data star)
    (hCard : 1 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1
      (detachedSheet input hCard) :=
  ((data.vertexPartition wall).exists_other_of_one_lt_blockCard
    input.distinguishedBlock.1 hCard).choose_spec.1

theorem detachedSheet_ne (input : W3SourceInput data star)
    (hCard : 1 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    detachedSheet input hCard ≠ input.distinguishedBlock.1 :=
  (((data.vertexPartition wall).exists_other_of_one_lt_blockCard
    input.distinguishedBlock.1 hCard).choose_spec.2).symm

theorem blockCard_detachedSheet (input : W3SourceInput data star)
    (hCard : 1 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    (data.vertexPartition wall).blockCard (detachedSheet input hCard)
      = (data.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
  (congrArg Finset.card ((data.vertexPartition wall).block_eq_of_rel
    (input.rel_detachedSheet hCard))).symm

/-- The canonical refinement of the wall partition at a distinguished block of
size at least two: the block is split into the detached sheet and the rest. -/
noncomputable def wallRefinement (input : W3SourceInput data star)
    (hCard : 1 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) : SheetPartition degree :=
  (data.vertexPartition wall).detachSheet (detachedSheet input hCard)
    input.distinguishedBlock.1 (input.detachedSheet_ne hCard)
    (input.rel_detachedSheet hCard).symm

@[simp] theorem wallRefinement_eq (input : W3SourceInput data star)
    (hCard : 1 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    input.wallRefinement hCard = (data.vertexPartition wall).detachSheet
      (detachedSheet input hCard) input.distinguishedBlock.1
      (input.detachedSheet_ne hCard) (input.rel_detachedSheet hCard).symm := rfl

theorem wallRefinement_refines (input : W3SourceInput data star)
    (hCard : 1 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    (input.wallRefinement hCard).Refines (data.vertexPartition wall) :=
  (data.vertexPartition wall).detachSheet_refines _ _ _ _

/-- **Equation (5)'s geometry, from the interface alone.**  The coarse member is
the wall partition itself and the fine member detaches one sheet from the
distinguished block, so `k` is that block's size less one. -/
noncomputable def nd2Geometry (input : W3SourceInput data star)
    (hCard : 1 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    GlobalCoarseFine.Nd2Geometry data wall where
  fine := input.wallRefinement hCard
  anchor := input.distinguishedBlock.1
  fine_refines := input.wallRefinement_refines hCard
  k := (data.vertexPartition wall).blockCard input.distinguishedBlock.1 - 1
  k_pos := by omega
  fineCard := by
    have hRemainder := (data.vertexPartition wall).detachSheet_blockCard_remainder
      (detachedSheet input hCard) input.distinguishedBlock.1
      (input.detachedSheet_ne hCard) (input.rel_detachedSheet hCard).symm
    rw [input.wallRefinement_eq hCard, hRemainder,
      input.blockCard_detachedSheet hCard]
  wallCard := by omega

/-! ### Equation (3)'s geometry, at a distinguished block of size at least three

Equation (3)'s geometry asks for more than a single detachment: a block of size
at least two *beside* a separate singleton, both inside the same wall block, so
that the `k-1` and `k+1` candidates have somewhere to move a sheet from and to.
Detaching one sheet from a distinguished block of size `c` leaves a residual
block of size `c - 1`, and the requirement `1 < k` is then `2 < c`. -/

/-- Two further sheets of the distinguished block, when it has at least three. -/
theorem exists_shiftPair (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    ∃ pair : Fin degree × Fin degree,
      (data.vertexPartition wall).Rel input.distinguishedBlock.1 pair.1 ∧
        (data.vertexPartition wall).Rel input.distinguishedBlock.1 pair.2 ∧
          input.distinguishedBlock.1 ≠ pair.1 ∧
            input.distinguishedBlock.1 ≠ pair.2 ∧ pair.1 ≠ pair.2 := by
  classical
  have hErase : 1 < (((data.vertexPartition wall).block
      input.distinguishedBlock.1).erase input.distinguishedBlock.1).card := by
    rw [Finset.card_erase_of_mem
      ((data.vertexPartition wall).self_mem_block _)]
    have hBlock : (data.vertexPartition wall).blockCard
        input.distinguishedBlock.1
        = ((data.vertexPartition wall).block input.distinguishedBlock.1).card :=
      rfl
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hErase
  refine ⟨(x, y), ?_, ?_, ?_, ?_, hxy⟩
  · exact ((data.vertexPartition wall).mem_block_iff _ _).mp
      (Finset.mem_of_mem_erase hx)
  · exact ((data.vertexPartition wall).mem_block_iff _ _).mp
      (Finset.mem_of_mem_erase hy)
  · exact fun h ↦ (Finset.mem_erase.mp hx).1 h.symm
  · exact fun h ↦ (Finset.mem_erase.mp hy).1 h.symm

/-- The sheet the `k-1` candidate detaches. -/
noncomputable def shiftRemainder (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) : Fin degree :=
  (input.exists_shiftPair hCard).choose.1

/-- The separate singleton the `k+1` candidate absorbs. -/
noncomputable def shiftExtra (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) : Fin degree :=
  (input.exists_shiftPair hCard).choose.2

theorem rel_shiftRemainder (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1
      (shiftRemainder input hCard) :=
  (input.exists_shiftPair hCard).choose_spec.1

theorem rel_shiftExtra (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1
      (shiftExtra input hCard) :=
  (input.exists_shiftPair hCard).choose_spec.2.1

theorem ne_shiftRemainder (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    input.distinguishedBlock.1 ≠ shiftRemainder input hCard :=
  (input.exists_shiftPair hCard).choose_spec.2.2.1

theorem shiftExtra_ne (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    shiftExtra input hCard ≠ input.distinguishedBlock.1 :=
  ((input.exists_shiftPair hCard).choose_spec.2.2.2.1).symm

theorem shiftRemainder_ne_shiftExtra (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    shiftRemainder input hCard ≠ shiftExtra input hCard :=
  (input.exists_shiftPair hCard).choose_spec.2.2.2.2

/-- The refinement Equation (3) runs on: the separate singleton is detached from
the distinguished block, leaving a residual block of size `k = c - 1 > 1`. -/
noncomputable def shiftEndpoint (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) : SheetPartition degree :=
  (data.vertexPartition wall).detachSheet (shiftExtra input hCard)
    input.distinguishedBlock.1 (input.shiftExtra_ne hCard)
    (input.rel_shiftExtra hCard).symm

@[simp] theorem shiftEndpoint_eq (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    input.shiftEndpoint hCard = (data.vertexPartition wall).detachSheet
      (shiftExtra input hCard) input.distinguishedBlock.1
      (input.shiftExtra_ne hCard) (input.rel_shiftExtra hCard).symm := rfl

theorem blockCard_shiftExtra (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    (data.vertexPartition wall).blockCard (shiftExtra input hCard)
      = (data.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
  (congrArg Finset.card ((data.vertexPartition wall).block_eq_of_rel
    (input.rel_shiftExtra hCard))).symm

theorem shiftEndpoint_blockCard (input : W3SourceInput data star)
    (hCard : 2 < (data.vertexPartition wall).blockCard
      input.distinguishedBlock.1) :
    (input.shiftEndpoint hCard).blockCard input.distinguishedBlock.1
      = (data.vertexPartition wall).blockCard input.distinguishedBlock.1 - 1 := by
  rw [input.shiftEndpoint_eq hCard,
    (data.vertexPartition wall).detachSheet_blockCard_remainder
      (shiftExtra input hCard) input.distinguishedBlock.1
      (input.shiftExtra_ne hCard) (input.rel_shiftExtra hCard).symm,
    input.blockCard_shiftExtra hCard]

end W3SourceInput

end Routing

end DraismaVargas.LocalCases.ThirdEquation
