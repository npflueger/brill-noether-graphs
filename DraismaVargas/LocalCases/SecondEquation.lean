module

public import DraismaVargas.LocalCases.GlobalBookends
public import DraismaVargas.LocalCases.TrivalenceClosure
public import DraismaVargas.LocalCases.W4Bridge
public import DraismaVargas.LocalCases.W2R1Target

@[expose] public section

/-!
# The four-valent route at a divalent wall

`W4Bridge` drives the four-valent wall end to end: a
`FullDimensionalSourcePresentation` of a datum, plus the contraction hypotheses,
produces an `AuxR0SourceInput` for the contracted datum, which
`W4StableSource` turns into a `PresentedFamily`.  This module runs the same
route at a **divalent** wall (Draisma--Vargas Part I, Case {w2}) and records
what changes.

Only the numerology changes.

* `W2SourceInput` is the divalent analogue of `AuxR0SourceInput`, with the same
  five fields: validity, the stable-path count, dangling-no-glue, the
  wall-block valency trichotomy, and Equation (C).
* `w2SourceInput_of_contraction` discharges all five through exactly the
  theorems `W4Bridge` uses -- `valid_contractDatum`,
  `stablePath_card_contractDatum`, `danglingEdgeNoGlue_contractDatum`,
  `wallBlock_nonDanglingValency_eq_zero_or_two_or_three`, and
  `targetExcess_contractDatum_merge_eq_one`.  Not one of them is four-valent:
  Equation (C) in particular is `exc(w₀) = exc(u) + exc(v) + 1` with both
  summands zero by change-minimality, which is insensitive to the valencies.
* `targetChange_eq_two` is the whole divergence.  At a four-valent wall
  `exc = ch + val - 3 = 1` reads `ch(w₀) = 0`; at a divalent wall it reads
  `ch(w₀) = 2`.  So the divalent wall carries two units of change where the
  four-valent wall carries none, and that single line is what the downstream
  source classification must branch on.
* `twoStarMerge` and `endpoints_of_twoStar` are the bookkeeping in both
  directions, mirroring `fourStarMerge` and `endpoints_trivalent_of_fourStar`.

## The numerology at the merged vertex

`TwoStar` at the merged vertex gives `val(u) + val(v) = 4` by
`card_incidentEdges_merge`, and change-minimality gives `val ≤ 3` at every
target vertex, so the contracted occurrence joins endpoints of valencies
`(2,2)`, `(1,3)` or `(3,1)` -- against `(3,3)` forced in the four-valent case by
`endpoints_trivalent_of_fourStar`.  `endpoints_of_twoStar` records this together
with `ch(u) + ch(v) = 2`, which is the same `2` that `targetChange_eq_two`
reaches from the other side; the two routes agreeing is a genuine internal
consistency check on the bundle, not a restatement.

## Why the hypotheses can hold at once

A bundle of hypotheses can typecheck and still be unsatisfiable -- for
instance by asking for a target excess of both `0` and `1` -- and neither
typechecking nor `#print axioms` detects that.  This section, like the section
of the same name in `W4Bridge`, checks the bundle at the divalent wall.

**The hypothesis bundle of `w2SourceInput_of_contraction` is
inhabited.**  All three valency splits are realised, at `|E(target)| = 9`,
`degree = 3`, `c(H) = 1`, `g(source) = 4`; none is realised at the only smaller
count the numerology allows, `|E(target)| = 3`.

*The two data are different data, by design.*  `fullDim` is a presentation of
`data`; the conclusion is an interface for `contractDatum data ...`.  The two
`FullDimensionalSource` inconsistencies are inconsistencies *within one
datum*: `equation_c` versus `ChangeMinimal`, and `stablePath_card` versus a
square labelling.  Here `ChangeMinimal` and the square labelling are asserted
of `data` only, while `equation_c` and `stablePath_card` are asserted of
`contractDatum data ...` only.  Both of `W4Bridge`'s arguments for that reading
are valency-free and apply verbatim: `targetExcess_contractDatum_merge_eq_one`
*derives* the wall's excess `1` from the full-dimensional datum's excess `0` at
both ends, and `not_nonempty_labelling_contractDatum` proves the wall datum has
no square labelling of its own, so no declaration in the library can turn
`stablePath_card` into a contradiction.  Neither of the two mechanisms by which
such a bundle could be vacuous is available here.

*The splits are three, and each fixes the change at both endpoints.*
`valencySplit_of_twoStar` below.  `endpoints_of_twoStar` gives
`ch(u) + ch(v) = 2` upstairs and `W2SourceInput.targetChange_eq_two` gives
`ch(w₀) = 2` downstairs from `equation_c`;
`targetChange_contractDatum_merge_eq_two` is the proof that the two agree,
through `W4Bridge.targetChange_contractDatum_merge` and hence through
`hForest`.  The two routes use disjoint inputs -- one only the wall datum, one
only the datum being contracted plus the source-topology receipt -- so their
agreement is evidence, not a restatement.

*The arithmetic every model must satisfy, taken from the library and not by eye.*
`TrivalenceClosure.card_target_edges_eq_of_presentation` gives
`|E(target)| = 3 g(source) - 3 c(H)` for **every**
`FullDimensionalSourcePresentation`, and
`TrivalenceClosure.genus_sourceGraph_eq_of_presentation` gives
`g(source) = 2 degree - 5 + 3 c(H)`.  Together
(`card_target_edges_eq_six_mul` below)

```
|E(target)| = 6 · (degree + c(H)) - 15,
```

so `3` divides `|E(target)|` and the admissible values are `3, 9, 15, ...`.
Every candidate model has to be checked against this; a target with `t = 5`
occurrences, for instance, is not of this form.  The two models below are
checked against it, and against `3 g - 3 c` separately, before anything else is
claimed of them.

*How far counting alone settles the divalent wall.*  A two-star at the merged
vertex needs only two occurrences in the contracted target, so
`|E(target)| ≥ 3` (`three_le_card_target_edges_of_twoStar`), against
`|E(target)| ≥ 5` and hence `≥ 9` for a four-star.  So
`card_target_edges_eq_three_or_nine_le` is the whole of what counting gives at
a divalent wall: either `|E(target)| = 3` with `degree + c(H) = 3`, or
`|E(target)| ≥ 9`.  The bottom case survives the count and has to be excluded
by hand; it is excluded two paragraphs below.

*Split `(2,2)`: realised at `|E(target)| = 9`.*  Target: the path
`v₁ — ⋯ — v₁₀`, ten vertices and nine occurrences; `v₁, v₁₀` are leaves with
`ch = 2`, the other eight are divalent with `ch = 1`.  Fibre at `degree = 3`:
`m = (3,2,3,2,3,2,3,2,3)` occurrences above the nine target occurrences and
`b(v) = 2` source vertices above every target vertex, so `20` source vertices
and `23` source occurrences and `g(source) = 4`, with one dangling occurrence
at each end.  Surviving valencies are `nd = 3` at one block above each of
`v₃, …, v₈`, `nd = 2` at the other twelve pruned vertices and `nd = 0` at the
two dangling ones, so `fullDim.trivalent` and the trichotomy hold and the
stable graph is `3`-regular on six vertices with nine edges and one component:
`c(H) = 1` and `fullDim.stablePath_card` reads `9 = |E(target)|`.  The two
identities check: `6 · (3 + 1) - 15 = 9` and `3 · 4 - 3 · 1 = 9`, and
`fullDim.saturated` reads `9 = 2 · 4 + 2 · 3 - 5`.

Contract the occurrence `v₂v₃`: both endpoints divalent, `ch(v₂) = ch(v₃) = 1`,
which is the `(2,2)` split.  Above `v₂` the blocks are `{0,2}` (source degree
`3`, one incident occurrence dangling, so `nd = 2`) and `{1}` (degree `2`,
`nd = 2`); above `v₃` they are `{0,2}` (degree `3`, `nd = 3`) and `{1}`
(degree `2`, `nd = 2`).  `hForest` reads `1 + 1 = 1 + 1` on each of the two
merged blocks, whose surviving valencies are `2 + 3 - 2 = 3` and
`2 + 2 - 2 = 2`, so `hTrivalent` holds.  Both contracted occurrences are
interior to one and the same stable path, which also contains occurrences above
`v₁v₂`, so no stable class is destroyed and `hStable` holds.  At the merged
vertex `ch = 2`, `val = 2`, `exc = 1`.

*Split `(1,3)`: realised at `|E(target)| = 9`, by a different picture.*  Target:
a trivalent `z` with two leaf neighbours `a`, `a₂` and one branch
`z — u₁ — ⋯ — u₆ — u₇` with `u₇` a leaf; ten vertices, nine occurrences.  Fibre
at `degree = 3`: `m(z,a) = m(z,a₂) = m(z,u₁) = 3`, then `(2,3,2,3,2,3)` along
the branch; `b(z) = 3` and `b = 2` above every other target vertex, so `21`
source vertices and `24` source occurrences and `g(source) = 4`; three dangling
occurrences.  Exactly six source vertices have `nd = 3`, twelve have `nd = 2`
and three have `nd = 0`, so the stable graph is again `3`-regular on six
vertices with nine edges and `c(H) = 1`, `fullDim.stablePath_card` reads
`9 = |E(target)|`, and the same two identities check.

Contract `za`: `val(a) = 1`, `val(z) = 3`, `ch(a) = 2`, `ch(z) = 0`, the
`(1,3)` split.  Above a target leaf the fibre is forced: one source vertex `A`
of degree `2` and `degree - 2` dangling source vertices of degree `1`, with
`m = degree`.  Above `z` the three singleton blocks have degree `3` and
`nd = (2,3,2)`, the two with `nd = 2` each carrying a dangling occurrence that
comes from the other leaf `a₂`.  `A`'s two surviving occurrences run to two
*different* blocks above `z` -- which is what `hForest` forces -- and the merged
partition has two blocks, on which `hForest` reads `2 + 1 = 1 + 2` and
`1 + 1 = 1 + 1`.  Their surviving valencies are `2 + 2 + 3 - 2 · 2 = 3` and
`0 + 2 = 2`, so `hTrivalent` holds.  The stable path `z{1} — A — z{0}` continues
past `z{0}`, which has `nd = 2`, into the branch, so contraction only shortens
it and `hStable` holds.  At the merged vertex `ch = 2 + 0 = 2`, `val = 2`,
`exc = 1`.  `(3,1)` is this same picture with the two endpoints of the
contracted occurrence exchanged; nothing in the bundle distinguishes them
beyond which endpoint names the merged vertex.

*`|E(target)| = 3` does not occur at a divalent wall.*  `degree + c(H) = 3`
with `1 ≤ c(H)` (`TrivalenceClosure.one_le_stableComponentCount_of_presentation`)
and `1 ≤ degree` (`GluingDatum.degree_pos`) leaves `(degree, c(H)) = (1, 2)` or
`(2, 1)`.

The first is impossible: at `degree = 1` every sheet partition on `Fin 1` is
trivial, so the quotient source is the target graph and has genus `0`, against
`g(source) = 2 · 1 - 5 + 3 · 2 = 3`.  (Arithmetic in this prose, not a theorem:
the library has no `degree = 1` normal form for `sourceGraph`.)

The second is `degree = 2`, `c(H) = 1`, `g(source) = 2`
(`TrivalenceClosure.genus_sourceGraph_eq_of_connected_stable_graph`), and a
target tree on four vertices with all valencies at most three: the path on four
vertices, or the three-leaf star.  At `degree = 2` the fibre above every target
vertex is then forced.  `ch(v) = ∑_{e ∋ v} m(e) - 2 b(v) - (val(v) - 2) · 2`
with `ch(v) = 3 - val(v)` and `m(e) ≤ 2` leaves exactly one solution on each
tree.  The path gives the dumbbell source -- two two-occurrence bananas joined
by a single occurrence, `g = 2` -- whose middle occurrence is a whole stable
path between two `nd = 3` vertices, and which realises the `(2,2)` split.  The
star gives `K₂,₃`, whose two occurrences above the contracted target occurrence
are the whole of one stable path, and which realises `(1,3)`.  In both, the
merged block acquires source degree `4` and surviving valency `4`, so
`hTrivalent` fails, and the contraction swallows a whole stable class, so
`hStable` fails: the two fail together, which is the same coupling `W4Bridge`
records between them.  So the divalent wall also needs `|E(target)| ≥ 9`; it
just takes one argument more than the four-valent wall to get there, because
its star is smaller.

*What this file proves about the above, rather than asserting it.*
`card_target_edges_eq_six_mul`, `three_le_card_target_edges_of_twoStar` and
`card_target_edges_eq_three_or_nine_le` (the numerology);
`valencySplit_of_twoStar` (the three splits and the change each forces);
`targetChange_contractDatum_merge_eq_two` (the two routes to `ch(w₀) = 2`
agree); and, on a `W2SourceInput` itself, `sum_localRamification`,
`localRamification_le_two`, `exists_localRamification_pos` (**the divalent wall
is necessarily ramified** -- the sharpest divergence from the four-valent wall,
where `exc = ch + 4 - 3 = 1` reads `ch(w₀) = 0` and every wall block is
unramified), `ramification_split_or_concentrated`,
`card_incidentSourceEdge_wallBlock` and
`exists_isDangling_of_localRamification_eq_two`.

The two models themselves are given in prose, not as Lean objects:
constructing a `FullDimensionalSourcePresentation` for them would need their
pruned sources as explicit `CFGraph`s.  The prose is nevertheless falsifiable:
`card_target_edges_eq_six_mul` is a machine-checked test every claimed model
must pass, and both models above pass it.

## Towards a presented family at a divalent wall

`PresentedProgress.familyAt` consumes a `PresentedFamily`, and `W4StableSource`
builds one from an `AuxR0SourceInput`.  That route does not transfer: its
`AuxR0SourceInput.presentedFamily` runs through `change_zero`, the hypothesis
that the wall's total ramification vanishes, which is exactly what
`targetChange_eq_two` denies at a divalent wall.

What the divalent wall has instead is the two-block construction of Part I's
Case {w2-r1} (`W2R1SourceCandidates`, whose `Pair.candidates` are **two**
globally coupled candidates built from two distinct blocks above the wall whose
ramification-one positions are swapped), and `BalancingValencyTwo`, which
records the determinant balances of the paper's `w2-r2-nd3-M-11`, `-M-1k`,
`-M-kk` and `-P` subcases.  `ramification_split_or_concentrated` is the theorem
that routes a `W2SourceInput` into two ramification distributions: the total
ramification at the wall is `2` and each block's is nonnegative, so either two
distinct blocks carry one unit each -- the `w2-r1` configuration -- or a single
block carries both, which is the concentrated branch.
`exists_isDangling_of_localRamification_eq_two` shows that block has surviving
valency at most three but source degree four, so it necessarily deletes an
occurrence.  This does **not** prove its surviving valency is three: the
source excludes the nd2 cases separately using inherited rank and the incoming
nonsingular resolution (Part I, Case {w2-r2-nd2}, Figure 36), and
`W2SourceInput` does not retain those rank data.

The fields of a `PresentedFamily` -- a `LengthMatrixPresentation` for each
candidate, `agreeOffWall`, and a `PositiveBalance` on the determinants -- need
the divalent counterpart of `W4DeterminantContributions` and
`W4StablePathAssignment`, which attach the adjugate-row contributions
`c₁, c₂, c₃, s` of `BalancingValencyTwo` to actual stable-path rows.  They are
not constructed in this module.
-/
namespace DraismaVargas.LocalCases.SecondEquation

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
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.BalancedGlobal

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-! ## The divalent wall source interface -/

/-- The source-facing interface at a **divalent** wall. -/
structure W2SourceInput {wall : target.V}
    (data : GluingDatum target degree)
    (star : TwoStar target wall) where
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

namespace W2SourceInput

variable {wall : target.V}

/-- **The divergence from the four-valent wall, in one line.** -/
theorem targetChange_eq_two {data : GluingDatum target degree}
    {star : TwoStar target wall} (input : W2SourceInput data star) :
    data.targetChange wall = 2 := by
  have hCard := star.card_incidentEdges
  have hEquation := input.equation_c
  unfold GluingDatum.targetExcess at hEquation
  omega

end W2SourceInput

/-! ## The merge -/

/-- Contracting an occurrence whose two endpoint valencies sum to `4`. -/
noncomputable def twoStarMerge (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (hCard : (GluingDatum.incidentEdges a).card
      + (GluingDatum.incidentEdges b).card = 4) :
    TwoStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩ :=
  TwoStar.of_card (by
    have hMerge := card_incidentEdges_merge hc hab hOne
    omega)

/-- The converse bookkeeping. -/
theorem endpoints_of_twoStar (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (star : TwoStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    (GluingDatum.incidentEdges a).card
        + (GluingDatum.incidentEdges b).card = 4 ∧
      (GluingDatum.incidentEdges a).card ≤ 3 ∧
        (GluingDatum.incidentEdges b).card ≤ 3 ∧
          data.targetChange a + data.targetChange b = 2 := by
  have hStar := star.card_incidentEdges
  have hMerge := card_incidentEdges_merge hc hab hOne
  have hLeftLe := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data
    hValid a (hMinimal a)
  have hRightLe := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data
    hValid b (hMinimal b)
  have hLeftExcess : data.targetChange a
      + ((GluingDatum.incidentEdges a).card : ℤ) - 3 = 0 := hMinimal a
  have hRightExcess : data.targetChange b
      + ((GluingDatum.incidentEdges b).card : ℤ) - 3 = 0 := hMinimal b
  refine ⟨by omega, hLeftLe, hRightLe, by omega⟩

/-! ## The bridge -/

/-- **The main theorem.** -/
theorem w2SourceInput_of_contraction {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {star : TwoStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩}
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
    W2SourceInput (contractDatum data hc hab hOne) star where
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

/-! ## What the numerology allows at a divalent wall -/

section Numerology

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The count every claimed model must pass.**
`TrivalenceClosure.card_target_edges_eq_of_presentation` gives
`|E(target)| = 3 g(source) - 3 c(H)` and
`TrivalenceClosure.genus_sourceGraph_eq_of_presentation` gives
`g(source) = 2 degree - 5 + 3 c(H)`, for *every* full-dimensional presentation.
Together they leave `|E(target)| = 6 (degree + c(H)) - 15`, so `3` divides the
target-occurrence count and the admissible values are `3, 9, 15, ...`.  Both
models in the module docstring pass this test. -/
theorem card_target_edges_eq_six_mul (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    (target.edges.card : ℤ)
      = 6 * (degree : ℤ)
        + 6 * TrivalenceClosure.stableComponentCount data - 15 := by
  have hEdges := TrivalenceClosure.card_target_edges_eq_of_presentation fullDim
  have hGenus := TrivalenceClosure.genus_sourceGraph_eq_of_presentation fullDim
  linarith

/-- **The divalent wall does not inherit the four-valent wall's lower bound.**
A four-star at the merged vertex needs four occurrences in the contracted
target, so `|E(target)| ≥ 5` and `card_target_edges_eq_six_mul` lifts that to
`9`.  A two-star needs only two, so the same argument stops at `3`. -/
theorem three_le_card_target_edges_of_twoStar (data : GluingDatum target degree)
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : TwoStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    3 ≤ target.edges.card := by
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
  have hCount := card_target_edges_eq_six_mul data fullDim
  have hComponent :=
    TrivalenceClosure.one_le_stableComponentCount_of_presentation fullDim
  have hDegree : 1 ≤ (degree : ℤ) := by exact_mod_cast data.degree_pos
  omega

/-- **Everything counting gives at a divalent wall.**  Either the target has the
smallest admissible number of occurrences, `3`, which forces
`degree + c(H) = 3`, or it has at least `9`.  The module docstring excludes the
first by hand -- the fibre at `degree = 2` over a four-vertex tree is forced,
and both of the two shapes break `hTrivalent` and `hStable` together -- and
realises the second. -/
theorem card_target_edges_eq_three_or_nine_le (data : GluingDatum target degree)
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : TwoStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    (target.edges.card = 3 ∧
        (degree : ℤ) + TrivalenceClosure.stableComponentCount data = 3) ∨
      9 ≤ target.edges.card := by
  have hThree := three_le_card_target_edges_of_twoStar data hab hOne fullDim star
  have hCount := card_target_edges_eq_six_mul data fullDim
  have hComponent :=
    TrivalenceClosure.one_le_stableComponentCount_of_presentation fullDim
  have hDegree : 1 ≤ (degree : ℤ) := by exact_mod_cast data.degree_pos
  omega

end Numerology

/-! ## The three valency splits, and the change each forces -/

/-- **The divalent analogue of `W4Bridge.endpoints_trivalent_of_fourStar`.**  A
two-star at the merged vertex leaves exactly three possibilities for the
valencies of the two contracted endpoints, and change-minimality of the datum
being contracted then reads the change at each endpoint off its valency.  So
the hypotheses of `w2SourceInput_of_contraction` pin each other down just as
tightly as the four-valent ones do: the shape of the target at the contracted
occurrence is one of three, and the `(3,3)` shape forced in the four-valent
case is not among them.  Each split distributes the two units of change
differently -- evenly in the `(2,2)` case, entirely on the leaf in the other
two -- which is what makes the two realising pictures in the module docstring
genuinely different. -/
theorem valencySplit_of_twoStar (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (star : TwoStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    ((GluingDatum.incidentEdges a).card = 2 ∧
        (GluingDatum.incidentEdges b).card = 2 ∧
          data.targetChange a = 1 ∧ data.targetChange b = 1) ∨
      ((GluingDatum.incidentEdges a).card = 1 ∧
          (GluingDatum.incidentEdges b).card = 3 ∧
            data.targetChange a = 2 ∧ data.targetChange b = 0) ∨
        ((GluingDatum.incidentEdges a).card = 3 ∧
            (GluingDatum.incidentEdges b).card = 1 ∧
              data.targetChange a = 0 ∧ data.targetChange b = 2) := by
  obtain ⟨hSum, hLeftLe, hRightLe, _⟩ :=
    endpoints_of_twoStar data hc hab hOne hValid hMinimal star
  have hLeftExcess : data.targetChange a
      + ((GluingDatum.incidentEdges a).card : ℤ) - 3 = 0 := hMinimal a
  have hRightExcess : data.targetChange b
      + ((GluingDatum.incidentEdges b).card : ℤ) - 3 = 0 := hMinimal b
  have hLeft : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges a).card = 2 ∨
        (GluingDatum.incidentEdges a).card = 3 := by omega
  rcases hLeft with hLeft | hLeft | hLeft
  · exact Or.inr (Or.inl ⟨hLeft, by omega, by omega, by omega⟩)
  · exact Or.inl ⟨hLeft, by omega, by omega, by omega⟩
  · exact Or.inr (Or.inr ⟨hLeft, by omega, by omega, by omega⟩)

/-- **The two routes to `ch(w₀) = 2` agree.**
`W2SourceInput.targetChange_eq_two` reaches it downstairs, from Equation (C)
and `val(w₀) = 2`; this reaches it upstairs, from
`W4Bridge.targetChange_contractDatum_merge` and the endpoint bookkeeping of
`endpoints_of_twoStar`.  The inputs are disjoint -- the first sees only the
wall datum, the second only the datum being contracted together with the
source-topology receipt `hForest` -- so the agreement is a genuine consistency
check on the bundle rather than a restatement of one of its fields. -/
theorem targetChange_contractDatum_merge_eq_two (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (hForest : ContractionForest data a b contracted)
    (star : TwoStar (GraphContraction.contract target hab hOne) ⟨a, hab⟩) :
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ = 2 := by
  obtain ⟨_, _, _, hChange⟩ :=
    endpoints_of_twoStar data hc hab hOne hValid hMinimal star
  rw [targetChange_contractDatum_merge data hc hab hOne hForest, hChange]

/-! ## The ramification the divalent wall is obliged to carry -/

namespace W2SourceInput

variable {wall : target.V} {data : GluingDatum target degree}
  {star : TwoStar target wall}

/-- The total ramification above the divalent wall is exactly two units.  This
is `targetChange_eq_two` with the definition of `targetChange` unfolded, in the
form the block-by-block statements below consume. -/
theorem sum_localRamification (input : W2SourceInput data star) :
    (∑ sourceBlock : WallBlock data wall,
      data.localRamification wall sourceBlock) = 2 := by
  have hChange := input.targetChange_eq_two
  unfold GluingDatum.targetChange at hChange
  exact hChange

/-- Riemann--Hurwitz at the wall: every block's local ramification is
nonnegative. -/
theorem localRamification_nonneg (input : W2SourceInput data star)
    (sourceBlock : WallBlock data wall) :
    0 ≤ data.localRamification wall sourceBlock :=
  data.localRamification_nonneg wall (input.valid.2 wall) sourceBlock

/-- No single block above the divalent wall carries more than the whole two
units. -/
theorem localRamification_le_two (input : W2SourceInput data star)
    (sourceBlock : WallBlock data wall) :
    data.localRamification wall sourceBlock ≤ 2 := by
  have hSingle := Finset.single_le_sum
    (f := fun block : WallBlock data wall ↦ data.localRamification wall block)
    (fun block _ ↦ input.localRamification_nonneg block)
    (Finset.mem_univ sourceBlock)
  rw [input.sum_localRamification] at hSingle
  exact hSingle

/-- **The divalent wall is necessarily ramified.**  This is the sharpest
divergence from the four-valent wall.  There `exc = ch + 4 - 3 = 1` reads
`ch(w₀) = 0`, so every block above the wall is unramified and the whole four-valent
family construction runs through its `change_zero` hypothesis; here it reads
`ch(w₀) = 2` and some block above the wall must carry ramification. -/
theorem exists_localRamification_pos (input : W2SourceInput data star) :
    ∃ sourceBlock : WallBlock data wall,
      1 ≤ data.localRamification wall sourceBlock := by
  by_contra hNone
  push Not at hNone
  have hZero : (∑ sourceBlock : WallBlock data wall,
      data.localRamification wall sourceBlock) = 0 := by
    refine Finset.sum_eq_zero fun sourceBlock _ ↦ ?_
    have hLt := hNone sourceBlock
    have hNonneg := input.localRamification_nonneg sourceBlock
    omega
  have hSum := input.sum_localRamification
  omega

/-- **The divalent wall's ramification either splits or concentrates.**  The
total is `2` and every summand is nonnegative, so either two distinct blocks
carry one unit each, or a single block carries both.  The first branch is the
paper's `w2-r1` configuration, the one `W2R1SourceCandidates` resolves. The
second branch only identifies a ramification-two
block; it does not establish surviving valency three or route into the
`w2-r2-nd3-*` determinant balances. The nd2 exclusions need inherited rank. -/
theorem ramification_split_or_concentrated (input : W2SourceInput data star) :
    (∃ first second : WallBlock data wall, first ≠ second ∧
        data.localRamification wall first = 1 ∧
          data.localRamification wall second = 1) ∨
      ∃ sourceBlock : WallBlock data wall,
        data.localRamification wall sourceBlock = 2 := by
  classical
  by_cases hTwo : ∃ first second : WallBlock data wall, first ≠ second ∧
      1 ≤ data.localRamification wall first ∧
        1 ≤ data.localRamification wall second
  · obtain ⟨first, second, hNe, hFirst, hSecond⟩ := hTwo
    have hPair : data.localRamification wall first
        + data.localRamification wall second
        ≤ ∑ sourceBlock : WallBlock data wall,
            data.localRamification wall sourceBlock := by
      have hSubset := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun block : WallBlock data wall ↦ data.localRamification wall block)
        (Finset.subset_univ ({first, second} : Finset (WallBlock data wall)))
        (fun block _ _ ↦ input.localRamification_nonneg block)
      rwa [Finset.sum_pair hNe] at hSubset
    rw [input.sum_localRamification] at hPair
    exact Or.inl ⟨first, second, hNe, by omega, by omega⟩
  · push Not at hTwo
    obtain ⟨sourceBlock, hPos⟩ := input.exists_localRamification_pos
    refine Or.inr ⟨sourceBlock, ?_⟩
    have hOthers : ∀ other : WallBlock data wall, other ∈
        (Finset.univ : Finset (WallBlock data wall)) → other ≠ sourceBlock →
        data.localRamification wall other = 0 := by
      intro other _ hNe
      have hLt := hTwo sourceBlock other (Ne.symm hNe) hPos
      have hNonneg := input.localRamification_nonneg other
      omega
    have hSum := input.sum_localRamification
    rwa [Finset.sum_eq_single_of_mem sourceBlock (Finset.mem_univ sourceBlock)
      hOthers] at hSum

/-- The source degree of a wall block, in terms of its local ramification.  At
a divalent wall the local-degree term of
`NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form`
vanishes, so a wall block carries exactly `r(A) + 2` incident occurrences.
Only `val(w₀) = 2` is used, so this is stated for the two-star rather than for a
`W2SourceInput`; with `localRamification_nonneg` and `localRamification_le_two`
it pins every wall block of an input between source degree `2` and `4`. -/
theorem card_incidentSourceEdge_wallBlock (star : TwoStar target wall)
    (sourceBlock : WallBlock data wall) :
    (Fintype.card (IncidentSourceEdge data
        (WallBlock.sourceVertex data wall sourceBlock)) : ℤ)
      = data.localRamification wall sourceBlock + 2 := by
  have hForm := card_incidentSourceEdge_eq_localRamification_form data
    (WallBlock.sourceVertex data wall sourceBlock)
  have hDivalent : (GluingDatum.incidentEdges
      (WallBlock.sourceVertex data wall sourceBlock).1.1).card = 2 :=
    star.card_incidentEdges
  have hBlock : data.localRamification
      (WallBlock.sourceVertex data wall sourceBlock).1.1
      ⟨(WallBlock.sourceVertex data wall sourceBlock).1.2,
        (WallBlock.sourceVertex data wall sourceBlock).2⟩
      = data.localRamification wall sourceBlock :=
    congrArg (data.localRamification wall) (Subtype.ext sourceBlock.2)
  rw [hDivalent, hBlock] at hForm
  simpa using hForm

/-- **A wall block carrying the whole two units deletes an occurrence.**  Its
source degree is `4` by `card_incidentSourceEdge_wallBlock`, while
`nonDangling_valency` caps its surviving valency at `3`.  So the concentrated
branch of `ramification_split_or_concentrated` is never honest-and-unramified:
the two units of change at a divalent wall are paid for either by splitting
across two blocks or by deleting an occurrence. -/
theorem exists_isDangling_of_localRamification_eq_two
    (input : W2SourceInput data star) (sourceBlock : WallBlock data wall)
    (hTwo : data.localRamification wall sourceBlock = 2) :
    ∃ edge : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall sourceBlock),
      IsDangling data edge.1 := by
  classical
  by_contra hNone
  push Not at hNone
  have hCard := card_incidentSourceEdge_wallBlock (data := data) star sourceBlock
  rw [hTwo] at hCard
  have hFilter := StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency
    data (WallBlock.sourceVertex data wall sourceBlock)
  have hAll : ((Finset.univ : Finset (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall sourceBlock))).filter
        (fun edge ↦ ¬ IsDangling data edge.1)) = Finset.univ :=
    Finset.filter_true_of_mem fun edge _ ↦ hNone edge
  rw [hAll, Finset.card_univ] at hFilter
  have hTrichotomy := input.nonDangling_valency sourceBlock
  omega

end W2SourceInput

end DraismaVargas.LocalCases.SecondEquation
