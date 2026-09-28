import DraismaVargas.Infrastructure.ContractionRamification
import DraismaVargas.Infrastructure.NonnegativeRationalRealization
import Utilities.Iso.GraphContractionFibreTree

/-!
# Contracting a whole set of target edge occurrences

`DraismaVargas/Infrastructure/ContractionRamification.lean` contracts **one**
target edge occurrence of a gluing datum and keeps the datum valid
(`valid_contractDatumAt`).  The terminal face of Part I has to contract
**every** zero-length target occurrence at once, so that single step has to be
iterated.

Contraction changes the *type* of the target: `GraphContraction.contract G hab
hOne` has vertex type `{v : G.V // v ≠ b}`, so "contract a
`Finset target.edges`" cannot be stated as a fold over that `Finset` — after
the first step the remaining occurrences live in a different type.  Rather than
fight that with dependent rewriting, this file **bundles** the target together
with the datum over it and a nonnegative realization of that datum (`Step`),
makes a single contraction a *relation* between bundles (`Contracts`), and
iterates with `Relation.ReflTransGen`.  Nothing is ever transported across a
step: every statement about a contracted stage is a statement about the new
bundle, and the invariants of interest are each preserved by a two-case
induction.

## Why the realization is part of the stage

The terminal face wants to contract exactly the occurrences of target length
zero.  That is not a property of the pair `(target, data)`, so a stage that
carried only those two could not express the flag, and the terminal conclusion
could not say that every surviving occurrence has *positive* length — which is
precisely the statement that turns the terminal stage into a positive
`GluingDatum.IntegralRealization` (`Step.integralRealization`).  A stage
therefore carries a third field

```lean
realization : data.NonnegativeIntegralRealization
```

the *closed-cone* form (natural-number lengths, possibly zero, exact dilation
equation).  The strictly positive `IntegralRealization` cannot be the bundled
type: the starting stage is exactly the one that has zero-length occurrences.

**Carrying the realization costs nothing.**  `contractDatum` reads the edge
partition of a surviving occurrence off the *old* datum through `unfoldEdge`,
so `contractRealization` — restriction of the lengths along `unfoldEdge` on
target occurrences and along `unfoldSourceEdge` on source occurrences — is a
realization of the contracted datum with the dilation equation holding *by
`rfl`*, term by term.  In particular **no hypothesis is forced onto the
iteration**: `Contracts` places no condition on the lengths, and no theorem
below needs one.  What a contraction does
forget is the length of the occurrence it removes; contracting an occurrence of
positive length would therefore shorten the total length of the target.  That
is recorded, not assumed: `ContractsFlagged` remembers the flag carried by each
contracted occurrence, and the driver returns the *flagged* closure, so
`exists_terminal_positive` certifies that only zero-length occurrences were
contracted.

## The `num_edges = 1` side condition

`contractDatumAt` needs `num_edges target a b = 1` at the occurrence being
contracted.  In the intended application the target is connected of genus zero,
i.e. a tree, so it has no parallel occurrences and the hypothesis is free; that
is `num_edges_eq_one_of_genus_zero_of_connected`.  The proof deletes one of two
parallel occurrences — the deleted graph is still connected, because the other
occurrence of the same pair survives — and contradicts
`Utilities.graph_connected_card_vertices_le_card_edges_add_one`.

Main results:

* `num_edges_eq_one_of_genus_zero_of_connected` — a connected genus-zero graph
  has no parallel occurrences;
* `unfoldSourceEdge`, `contractRealization`, `contractRealizationAt` — the
  carried nonnegative realization, and `contractRealization_targetLength_foldEdge`
  / `contractRealization_sourceLength_sourceEdgeMap` for "a surviving
  occurrence keeps its old length";
* `positiveOfTargetLength_pos` — a nonnegative realization with positive target
  lengths *is* a positive `IntegralRealization`;
* `Step`, `Step.contractAt`, `Contracts` — the bundled stage and one
  contraction of it;
* `valid_of_contracts`, `graph_connected_of_contracts`, `genus_of_contracts`,
  `card_edges_of_contracts` — the one-step bookkeeping;
* `valid_of_contractsMany`, `graph_connected_of_contractsMany`,
  `genus_of_contractsMany` — the same along `Relation.ReflTransGen`, and
  `invariants_of_contractsMany` for the three at once;
* `exists_targetLength_eq_of_contractsMany`,
  `exists_sourceLength_eq_of_contractsMany` — every length of a later stage is
  a length of an earlier one: the iteration creates no new length;
* `exists_terminal` — the driver: contracting flagged occurrences one at a
  time terminates in a stage with no flagged occurrence left, still valid,
  still connected, still of genus zero; `exists_terminal_flagged` is the same
  with the stronger `ContractsFlagged` closure in the conclusion;
* `exists_terminal_positive` — the driver at the flag "target length is zero":
  every surviving occurrence of the terminal stage has positive length;
  `exists_terminal_positive_flagged` adds that only zero-length occurrences were
  contracted, and `exists_terminal_integralRealization` packages the terminal
  stage as a positive `GluingDatum.IntegralRealization`;
* `exists_edgeless` — the extreme case, contracting the target down to a point.
-/

namespace DraismaVargas.Infrastructure

namespace IteratedContraction

open GraphContraction GluingContraction ContractionRamification

universe u

/-! ### A connected graph of genus zero has no parallel occurrences

The counting input is
`Utilities.graph_connected_card_vertices_le_card_edges_add_one`: a connected
loopless multigraph has at least `|V| - 1` edge occurrences.  Genus zero says
it has exactly `|V| - 1`, so deleting any occurrence must disconnect it; two
parallel occurrences give one whose deletion manifestly does not. -/

section NoParallel

/-- Delete one edge occurrence, keeping the vertex type (and its instances)
untouched.

The definition is `@[reducible]` on purpose.  `eraseOccurrence G pair` has
`V := G.V` only up to unfolding, and instance search runs at reducible
transparency: without the attribute, `DecidablePred fun e => e = (x, y) ∨ e =
(y, x)` over the new vertex type is not synthesisable and every `num_edges`
statement about the erased graph fails to elaborate. -/
@[reducible] def eraseOccurrence (G : CFGraph.{u}) (pair : G.V × G.V) : CFGraph.{u} where
  V := G.V
  instDecidableEq := G.instDecidableEq
  instFintype := G.instFintype
  instNonempty := G.instNonempty
  edges := G.edges.erase pair
  loopless := fun x hx => G.loopless x (Multiset.mem_of_mem_erase hx)

theorem card_vertices_eraseOccurrence (G : CFGraph) (pair : G.V × G.V) :
    Fintype.card (eraseOccurrence G pair).V = Fintype.card G.V := rfl

theorem card_edges_eraseOccurrence (G : CFGraph) {pair : G.V × G.V}
    (hpair : pair ∈ G.edges) :
    Multiset.card (eraseOccurrence G pair).edges = Multiset.card G.edges - 1 := by
  show Multiset.card (G.edges.erase pair) = Multiset.card G.edges - 1
  rw [Multiset.card_erase_of_mem hpair, Nat.pred_eq_sub_one]

/-- Deleting an occurrence that does not join `x` and `y` leaves the
multiplicity at `x`, `y` alone. -/
theorem num_edges_eraseOccurrence_of_not (G : CFGraph) {pair : G.V × G.V}
    (hpair : pair ∈ G.edges) (x y : G.V)
    (hno : ¬ (pair = (x, y) ∨ pair = (y, x))) :
    num_edges (eraseOccurrence G pair) x y = num_edges G x y := by
  have hfilter : G.edges.filter (fun e => e = (x, y) ∨ e = (y, x))
      = (G.edges.erase pair).filter (fun e => e = (x, y) ∨ e = (y, x)) := by
    conv_lhs => rw [← Multiset.cons_erase hpair]
    exact Multiset.filter_cons_of_neg _ hno
  exact congrArg Multiset.card hfilter.symm

/-- Deleting an occurrence that joins `x` and `y` drops the multiplicity at
`x`, `y` by exactly one. -/
theorem num_edges_eraseOccurrence_of_mem (G : CFGraph) {pair : G.V × G.V}
    (hpair : pair ∈ G.edges) (x y : G.V)
    (hmem : pair = (x, y) ∨ pair = (y, x)) :
    num_edges G x y = num_edges (eraseOccurrence G pair) x y + 1 := by
  have hfilter : G.edges.filter (fun e => e = (x, y) ∨ e = (y, x))
      = pair ::ₘ (G.edges.erase pair).filter (fun e => e = (x, y) ∨ e = (y, x)) := by
    conv_lhs => rw [← Multiset.cons_erase hpair]
    exact Multiset.filter_cons_of_pos _ hmem
  calc num_edges G x y
      = Multiset.card (pair ::ₘ (G.edges.erase pair).filter
          (fun e => e = (x, y) ∨ e = (y, x))) := congrArg Multiset.card hfilter
    _ = num_edges (eraseOccurrence G pair) x y + 1 := Multiset.card_cons _ _

/-- Deleting one of two parallel occurrences preserves connectedness: the other
occurrence of the same pair is still there to carry any cut that the deleted
one used to carry. -/
theorem graph_connected_eraseOccurrence (G : CFGraph) (hConnected : graph_connected G)
    {pair : G.V × G.V} (hpair : pair ∈ G.edges)
    (hTwo : 2 ≤ num_edges G pair.1 pair.2) :
    graph_connected (eraseOccurrence G pair) := by
  intro S hS
  obtain ⟨x, hxS, y, hyS, hpos⟩ := hConnected S hS
  refine ⟨x, hxS, y, hyS, ?_⟩
  by_cases hcase : pair = (x, y) ∨ pair = (y, x)
  · have hsame : num_edges G x y = num_edges G pair.1 pair.2 := by
      rcases hcase with rfl | rfl
      · rfl
      · exact num_edges_symmetric G x y
    have hdrop := num_edges_eraseOccurrence_of_mem G hpair x y hcase
    omega
  · rw [num_edges_eraseOccurrence_of_not G hpair x y hcase]
    exact hpos

/-- A connected graph of genus zero has no parallel occurrences: deleting one
of two would leave a connected graph with fewer than `|V| - 1` occurrences. -/
theorem num_edges_le_one_of_genus_zero_of_connected (G : CFGraph)
    (hConnected : graph_connected G) (hGenus : genus G = 0) (x y : G.V) :
    num_edges G x y ≤ 1 := by
  by_contra hcon
  have hxy : 1 < num_edges G x y := Nat.not_le.mp hcon
  obtain ⟨pair, hpairMem, hpairEnds⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos G x y (by omega)
  have hTwo : 2 ≤ num_edges G pair.1 pair.2 := by
    rcases hpairEnds with rfl | rfl
    · exact hxy
    · rw [show ((y, x) : G.V × G.V).1 = y from rfl, show ((y, x) : G.V × G.V).2 = x from rfl,
        num_edges_symmetric G y x]
      exact hxy
  have hConn' := graph_connected_eraseOccurrence G hConnected hpairMem hTwo
  have hBound := Utilities.graph_connected_card_vertices_le_card_edges_add_one _ hConn'
  rw [card_vertices_eraseOccurrence, card_edges_eraseOccurrence G hpairMem] at hBound
  have hOneLe : 1 ≤ Multiset.card G.edges :=
    Multiset.card_pos.mpr (fun h => by simp [h] at hpairMem)
  have hVerts : (Fintype.card G.V : ℤ) = (Multiset.card G.edges : ℤ) + 1 := by
    unfold genus at hGenus
    omega
  have hVertsNat : Fintype.card G.V = Multiset.card G.edges + 1 := by exact_mod_cast hVerts
  omega

/-- The `num_edges = 1` side condition of `contractDatumAt` is free over a
connected target of genus zero. -/
theorem num_edges_eq_one_of_genus_zero_of_connected (G : CFGraph)
    (hConnected : graph_connected G) (hGenus : genus G = 0) (e : G.edges) :
    num_edges G (e : G.V × G.V).1 (e : G.V × G.V).2 = 1 := by
  obtain ⟨⟨u, v⟩, k⟩ := e
  show num_edges G u v = 1
  have hmem : (u, v) ∈ G.edges :=
    Multiset.count_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt)
  have hpos := GraphContraction.num_edges_pos_of_mem_edges G u v hmem
  have hle := num_edges_le_one_of_genus_zero_of_connected G hConnected hGenus u v
  omega

end NoParallel

/-! ### Carrying a nonnegative realization along one contraction

`GluingContraction.contractDatum` defines the edge partition of the contracted
datum at an occurrence `e` to be the edge partition of the *old* datum at
`unfoldEdge … e`, the surviving occurrence above it.  Every quantity the
dilation equation mentions is therefore literally the old one:
`(contractDatum …).sourceEdgeIndex` at a contracted source occurrence is
`data.sourceEdgeIndex` at the source occurrence it comes from.  Restricting the
lengths along `unfoldEdge` and `unfoldSourceEdge` consequently produces a
realization of the contracted datum whose `dilation_length` field is the old
`dilation_length` field applied to the corresponding source occurrence — no
rewriting, no arithmetic, and above all **no hypothesis**: the carry works at
every occurrence, whatever its length. -/

section Carry

variable {target : CFGraph.{u}} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- The surviving source occurrence underlying a source occurrence of the
contracted datum.  It exists because the contracted edge partition at `e.1.1`
*is* the old edge partition at `unfoldEdge … e.1.1`, so the block
representative condition transfers verbatim. -/
noncomputable def unfoldSourceEdge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (contractDatum data hc hab hOne).SourceEdge) : data.SourceEdge :=
  ⟨(unfoldEdge hc hab hOne e.1.1, e.1.2), e.2⟩

@[simp] theorem unfoldSourceEdge_edge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (contractDatum data hc hab hOne).SourceEdge) :
    (unfoldSourceEdge data hc hab hOne e).1.1 = unfoldEdge hc hab hOne e.1.1 := rfl

@[simp] theorem unfoldSourceEdge_sheet (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (contractDatum data hc hab hOne).SourceEdge) :
    (unfoldSourceEdge data hc hab hOne e).1.2 = e.1.2 := rfl

/-- `unfoldSourceEdge` inverts `GluingContraction.sourceEdgeMap`: the source
correspondence of the contraction is exactly the restriction of the identity on
sheets along `foldEdge`. -/
theorem unfoldSourceEdge_sourceEdgeMap (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) :
    unfoldSourceEdge data hc hab hOne (sourceEdgeMap data hc hab hOne e) = e.1 :=
  Subtype.ext (Prod.ext (unfoldEdge_foldEdge hc hab hOne ⟨e.1.1.1, e.2⟩) rfl)

/-- **The realization is carried by a contraction.**  Target lengths are read
through `unfoldEdge` and source lengths through `unfoldSourceEdge`; the
dilation equation of the contracted datum at a source occurrence is *the same
equation* as the dilation equation of the old datum at the source occurrence
below it. -/
noncomputable def contractRealization (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (contractDatum data hc hab hOne).NonnegativeIntegralRealization where
  targetLength := fun e => realization.targetLength (unfoldEdge hc hab hOne e)
  sourceLength := fun e => realization.sourceLength (unfoldSourceEdge data hc hab hOne e)
  dilation_length := fun e => realization.dilation_length (unfoldSourceEdge data hc hab hOne e)

@[simp] theorem contractRealization_targetLength (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (GraphContraction.contract target hab hOne).edges) :
    (contractRealization data realization hc hab hOne).targetLength e
      = realization.targetLength (unfoldEdge hc hab hOne e) := rfl

@[simp] theorem contractRealization_sourceLength (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (contractDatum data hc hab hOne).SourceEdge) :
    (contractRealization data realization hc hab hOne).sourceLength e
      = realization.sourceLength (unfoldSourceEdge data hc hab hOne e) := rfl

/-- A surviving target occurrence keeps its old length. -/
theorem contractRealization_targetLength_foldEdge (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (f : {f : target.edges // f ≠ contracted}) :
    (contractRealization data realization hc hab hOne).targetLength
        (foldEdge hc hab hOne f)
      = realization.targetLength f.1 := by
  rw [contractRealization_targetLength, unfoldEdge_foldEdge]

/-- A surviving source occurrence keeps its old length. -/
theorem contractRealization_sourceLength_sourceEdgeMap (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) :
    (contractRealization data realization hc hab hOne).sourceLength
        (sourceEdgeMap data hc hab hOne e)
      = realization.sourceLength e.1 := by
  rw [contractRealization_sourceLength, unfoldSourceEdge_sourceEdgeMap]

/-- The carried realization at a chosen target occurrence, matching
`GluingContraction.contractDatumAt`. -/
noncomputable def contractRealizationAt (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) (edge : target.edges)
    (hOne : num_edges target (edge : target.V × target.V).1
      (edge : target.V × target.V).2 = 1) :
    (contractDatumAt data edge hOne).NonnegativeIntegralRealization :=
  contractRealization data realization (contracted := edge)
    (a := (edge : target.V × target.V).1) (b := (edge : target.V × target.V).2)
    rfl (fst_ne_snd edge) hOne

@[simp] theorem contractRealizationAt_targetLength (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) (edge : target.edges)
    (hOne : num_edges target (edge : target.V × target.V).1
      (edge : target.V × target.V).2 = 1)
    (e : (contractTarget edge hOne).edges) :
    (contractRealizationAt data realization edge hOne).targetLength e
      = realization.targetLength (unfoldEdge rfl (fst_ne_snd edge) hOne e) := rfl

/-- A surviving target occurrence keeps its old length, at a chosen
occurrence. -/
theorem contractRealizationAt_targetLength_foldEdge (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) (edge : target.edges)
    (hOne : num_edges target (edge : target.V × target.V).1
      (edge : target.V × target.V).2 = 1)
    (f : {f : target.edges // f ≠ edge}) :
    (contractRealizationAt data realization edge hOne).targetLength
        (foldEdge rfl (fst_ne_snd edge) hOne f)
      = realization.targetLength f.1 :=
  contractRealization_targetLength_foldEdge data realization rfl (fst_ne_snd edge) hOne f

/-- A nonnegative realization all of whose target lengths are positive **is** a
positive `GluingDatum.IntegralRealization`: positivity of the source lengths is
forced by the dilation equation `index * source = target`, since a product of
naturals that is positive has positive factors.  This is what makes the
terminal conclusion of `exists_terminal_positive` usable downstream. -/
def positiveOfTargetLength_pos {data : GluingDatum target degree}
    (realization : data.NonnegativeIntegralRealization)
    (hPositive : ∀ e : target.edges, 0 < realization.targetLength e) :
    data.IntegralRealization where
  targetLength := realization.targetLength
  targetLength_pos := hPositive
  sourceLength := realization.sourceLength
  sourceLength_pos := by
    intro e
    have hDilation := realization.dilation_length e
    have hTarget := hPositive e.1.1
    rcases Nat.eq_zero_or_pos (realization.sourceLength e) with hZero | hPos
    · rw [hZero, Nat.mul_zero] at hDilation
      omega
    · exact hPos
  dilation_length := realization.dilation_length

@[simp] theorem positiveOfTargetLength_pos_targetLength {data : GluingDatum target degree}
    (realization : data.NonnegativeIntegralRealization)
    (hPositive : ∀ e : target.edges, 0 < realization.targetLength e) :
    (positiveOfTargetLength_pos realization hPositive).targetLength
      = realization.targetLength := rfl

@[simp] theorem positiveOfTargetLength_pos_sourceLength {data : GluingDatum target degree}
    (realization : data.NonnegativeIntegralRealization)
    (hPositive : ∀ e : target.edges, 0 < realization.targetLength e) :
    (positiveOfTargetLength_pos realization hPositive).sourceLength
      = realization.sourceLength := rfl

end Carry

/-! ### One stage of the iteration

A stage is a target graph, a gluing datum over it, and a nonnegative
realization of that datum.  Bundling the three is what makes a plain relation —
rather than a dependent fold — able to describe the iteration: the contracted
stage is a new bundle, and the change of the target's vertex type is invisible
from outside.  Carrying the realization is what makes "this occurrence has
length zero" a property of a stage, hence a legitimate flag for the driver. -/

/-- One stage of the iterated contraction: a target graph, a gluing datum of
the fixed sheet degree over it, and a closed-cone realization of that datum.

The realization is `NonnegativeIntegralRealization` rather than
`IntegralRealization` because the whole point of the iteration is to remove the
occurrences of length **zero**; a stage that had to have positive lengths could
not be the starting stage.  `Step.integralRealization` upgrades a terminal
stage, where positivity has been achieved, to the positive form. -/
structure Step (degree : ℕ) : Type (u + 1) where
  /-- The target graph of this stage. -/
  target : CFGraph.{u}
  /-- The gluing datum of this stage. -/
  data : GluingDatum target degree
  /-- The closed-cone realization of this stage: natural target and source
  lengths, possibly zero, satisfying the dilation equation exactly. -/
  realization : data.NonnegativeIntegralRealization

variable {degree : ℕ}

/-- Contract one target occurrence of a stage.  All three components move: the
target is `GluingContraction.contractTarget`, the datum is
`GluingContraction.contractDatumAt`, and the realization is
`contractRealizationAt`, which restricts the old lengths to the surviving
occurrences. -/
noncomputable def Step.contractAt (s : Step.{u} degree) (edge : s.target.edges)
    (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
      (edge : s.target.V × s.target.V).2 = 1) : Step.{u} degree :=
  ⟨contractTarget edge hOne, contractDatumAt s.data edge hOne,
    contractRealizationAt s.data s.realization edge hOne⟩

@[simp] theorem Step.contractAt_target (s : Step.{u} degree) (edge : s.target.edges)
    (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
      (edge : s.target.V × s.target.V).2 = 1) :
    (s.contractAt edge hOne).target = contractTarget edge hOne := rfl

@[simp] theorem Step.contractAt_data (s : Step.{u} degree) (edge : s.target.edges)
    (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
      (edge : s.target.V × s.target.V).2 = 1) :
    (s.contractAt edge hOne).data = contractDatumAt s.data edge hOne := rfl

@[simp] theorem Step.contractAt_realization (s : Step.{u} degree) (edge : s.target.edges)
    (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
      (edge : s.target.V × s.target.V).2 = 1) :
    (s.contractAt edge hOne).realization
      = contractRealizationAt s.data s.realization edge hOne := rfl

/-- Every target length of a contracted stage is a target length of the stage
it came from. -/
@[simp] theorem Step.contractAt_targetLength (s : Step.{u} degree) (edge : s.target.edges)
    (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
      (edge : s.target.V × s.target.V).2 = 1)
    (e : (contractTarget edge hOne).edges) :
    (s.contractAt edge hOne).realization.targetLength e
      = s.realization.targetLength (unfoldEdge rfl (fst_ne_snd edge) hOne e) := rfl

/-- A target occurrence of a stage that survives a contraction keeps its
length. -/
theorem Step.contractAt_targetLength_foldEdge (s : Step.{u} degree) (edge : s.target.edges)
    (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
      (edge : s.target.V × s.target.V).2 = 1)
    (f : {f : s.target.edges // f ≠ edge}) :
    (s.contractAt edge hOne).realization.targetLength
        (foldEdge rfl (fst_ne_snd edge) hOne f)
      = s.realization.targetLength f.1 :=
  contractRealizationAt_targetLength_foldEdge s.data s.realization edge hOne f

/-- The positive realization of a stage all of whose target occurrences have
positive length.  This is the object the terminal face of Part I consumes; it
is produced from `exists_terminal_positive`. -/
def Step.integralRealization (s : Step.{u} degree)
    (hPositive : ∀ e : s.target.edges, 0 < s.realization.targetLength e) :
    s.data.IntegralRealization :=
  positiveOfTargetLength_pos s.realization hPositive

@[simp] theorem Step.integralRealization_targetLength (s : Step.{u} degree)
    (hPositive : ∀ e : s.target.edges, 0 < s.realization.targetLength e) :
    (s.integralRealization hPositive).targetLength = s.realization.targetLength := rfl

@[simp] theorem Step.integralRealization_sourceLength (s : Step.{u} degree)
    (hPositive : ∀ e : s.target.edges, 0 < s.realization.targetLength e) :
    (s.integralRealization hPositive).sourceLength = s.realization.sourceLength := rfl

/-- One contraction of a stage: pick a target occurrence whose source fibre is
a forest, check that it is the only occurrence joining its endpoints, and
contract it.  The whole iteration is the reflexive-transitive closure of this
relation, which is why no dependent transport is ever needed.

Bundling the realization costs **no** hypothesis here: the realization is
carried at every occurrence, whatever its length. -/
inductive Contracts : Step.{u} degree → Step.{u} degree → Prop
  | contract (s : Step.{u} degree) (edge : s.target.edges)
      (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
        (edge : s.target.V × s.target.V).2 = 1)
      (hForest : ContractionForestAt s.data edge) :
      Contracts s (s.contractAt edge hOne)

/-- The iteration: finitely many contractions, in order. -/
abbrev ContractsMany : Step.{u} degree → Step.{u} degree → Prop :=
  Relation.ReflTransGen Contracts

/-- `Contracts`, remembering that the contracted occurrence carried a given
flag.  The driver returns the closure of *this* relation, so the caller learns
not only that the terminal stage was reached by contractions but that every
contracted occurrence was flagged — for the flag "target length is zero", that
only zero-length occurrences were removed. -/
inductive ContractsFlagged (flag : ∀ s : Step.{u} degree, s.target.edges → Prop) :
    Step.{u} degree → Step.{u} degree → Prop
  | contract (s : Step.{u} degree) (edge : s.target.edges)
      (hOne : num_edges s.target (edge : s.target.V × s.target.V).1
        (edge : s.target.V × s.target.V).2 = 1)
      (hForest : ContractionForestAt s.data edge) (hFlag : flag s edge) :
      ContractsFlagged flag s (s.contractAt edge hOne)

/-- Finitely many flagged contractions, in order. -/
abbrev ContractsFlaggedMany (flag : ∀ s : Step.{u} degree, s.target.edges → Prop) :
    Step.{u} degree → Step.{u} degree → Prop :=
  Relation.ReflTransGen (ContractsFlagged flag)

theorem contracts_of_contractsFlagged {flag : ∀ s : Step.{u} degree, s.target.edges → Prop}
    {s t : Step.{u} degree} (h : ContractsFlagged flag s t) : Contracts s t := by
  cases h with
  | contract edge hOne hForest _ => exact Contracts.contract s edge hOne hForest

theorem contractsMany_of_contractsFlaggedMany
    {flag : ∀ s : Step.{u} degree, s.target.edges → Prop} {s t : Step.{u} degree}
    (h : ContractsFlaggedMany flag s t) : ContractsMany s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (contracts_of_contractsFlagged hstep)

/-! ### One-step preservation -/

/-- Validity is preserved by one contraction: this is
`ContractionRamification.valid_contractDatumAt`, whose forest receipt is
carried by the relation. -/
theorem valid_of_contracts {s t : Step.{u} degree} (h : Contracts s t)
    (hValid : s.data.Valid) : t.data.Valid := by
  cases h with
  | contract edge hOne hForest => exact valid_contractDatumAt s.data edge hOne hForest hValid

/-- Connectedness of the target is preserved by one contraction. -/
theorem graph_connected_of_contracts {s t : Step.{u} degree} (h : Contracts s t)
    (hConnected : graph_connected s.target) : graph_connected t.target := by
  cases h with
  | contract edge hOne _ =>
      exact GraphContraction.graph_connected_contract s.target (fst_ne_snd edge) hOne hConnected

/-- One contraction does not change the genus of the target: it removes one
vertex and one edge occurrence. -/
theorem genus_of_contracts {s t : Step.{u} degree} (h : Contracts s t) :
    genus t.target = genus s.target := by
  cases h with
  | contract edge hOne _ =>
      exact GraphContraction.genus_contract s.target (fst_ne_snd edge) hOne

/-- Genus zero is preserved by one contraction. -/
theorem genus_zero_of_contracts {s t : Step.{u} degree} (h : Contracts s t)
    (hGenus : genus s.target = 0) : genus t.target = 0 := by
  rw [genus_of_contracts h]; exact hGenus

/-- One contraction removes exactly one target edge occurrence; this is the
termination measure of the iteration. -/
theorem card_edges_of_contracts {s t : Step.{u} degree} (h : Contracts s t) :
    Multiset.card t.target.edges = Multiset.card s.target.edges - 1 := by
  cases h with
  | contract edge hOne _ =>
      exact GraphContraction.card_edges_contract s.target (fst_ne_snd edge) hOne

/-- The target of a stage that can be contracted has at least one edge
occurrence, so the measure of `card_edges_of_contracts` really does drop. -/
theorem one_le_card_edges_of_contracts {s t : Step.{u} degree} (h : Contracts s t) :
    1 ≤ Multiset.card s.target.edges := by
  cases h with
  | contract edge hOne _ => exact GraphContraction.one_le_card_edges s.target hOne

theorem card_edges_lt_of_contracts {s t : Step.{u} degree} (h : Contracts s t) :
    Multiset.card t.target.edges < Multiset.card s.target.edges := by
  have h1 := one_le_card_edges_of_contracts h
  have h2 := card_edges_of_contracts h
  omega

/-- One contraction creates no new target length: every length of the
contracted stage is a length of the stage it came from. -/
theorem exists_targetLength_eq_of_contracts {s t : Step.{u} degree} (h : Contracts s t)
    (e : t.target.edges) :
    ∃ f : s.target.edges, s.realization.targetLength f = t.realization.targetLength e := by
  cases h with
  | contract edge hOne _ => exact ⟨unfoldEdge rfl (fst_ne_snd edge) hOne e, rfl⟩

/-- One contraction creates no new source length. -/
theorem exists_sourceLength_eq_of_contracts {s t : Step.{u} degree} (h : Contracts s t)
    (e : t.data.SourceEdge) :
    ∃ f : s.data.SourceEdge, s.realization.sourceLength f = t.realization.sourceLength e := by
  cases h with
  | contract edge hOne _ =>
      exact ⟨unfoldSourceEdge s.data rfl (fst_ne_snd edge) hOne e, rfl⟩

/-! ### Preservation along the whole iteration

Each of these is one two-case induction over `Relation.ReflTransGen`. -/

/-- Validity survives any number of contractions. -/
theorem valid_of_contractsMany {s t : Step.{u} degree} (h : ContractsMany s t)
    (hValid : s.data.Valid) : t.data.Valid := by
  induction h with
  | refl => exact hValid
  | tail _ hstep ih => exact valid_of_contracts hstep ih

/-- Connectedness of the target survives any number of contractions. -/
theorem graph_connected_of_contractsMany {s t : Step.{u} degree} (h : ContractsMany s t)
    (hConnected : graph_connected s.target) : graph_connected t.target := by
  induction h with
  | refl => exact hConnected
  | tail _ hstep ih => exact graph_connected_of_contracts hstep ih

/-- The genus of the target is unchanged by any number of contractions. -/
theorem genus_of_contractsMany {s t : Step.{u} degree} (h : ContractsMany s t) :
    genus t.target = genus s.target := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [genus_of_contracts hstep]; exact ih

/-- Genus zero survives any number of contractions. -/
theorem genus_zero_of_contractsMany {s t : Step.{u} degree} (h : ContractsMany s t)
    (hGenus : genus s.target = 0) : genus t.target = 0 := by
  rw [genus_of_contractsMany h]; exact hGenus

/-- The measure never increases along the iteration. -/
theorem card_edges_le_of_contractsMany {s t : Step.{u} degree} (h : ContractsMany s t) :
    Multiset.card t.target.edges ≤ Multiset.card s.target.edges := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans (le_of_lt (card_edges_lt_of_contracts hstep)) ih

/-- The iteration creates no new target length: every target length of a later
stage is a target length of the earlier one.  In particular the terminal stage
of `exists_terminal_positive` has no length that was not already there. -/
theorem exists_targetLength_eq_of_contractsMany {s t : Step.{u} degree}
    (h : ContractsMany s t) :
    ∀ e : t.target.edges,
      ∃ f : s.target.edges, s.realization.targetLength f = t.realization.targetLength e := by
  induction h with
  | refl => exact fun e => ⟨e, rfl⟩
  | tail _ hstep ih =>
      intro e
      obtain ⟨g, hg⟩ := exists_targetLength_eq_of_contracts hstep e
      obtain ⟨f, hf⟩ := ih g
      exact ⟨f, hf.trans hg⟩

/-- The iteration creates no new source length. -/
theorem exists_sourceLength_eq_of_contractsMany {s t : Step.{u} degree}
    (h : ContractsMany s t) :
    ∀ e : t.data.SourceEdge,
      ∃ f : s.data.SourceEdge, s.realization.sourceLength f = t.realization.sourceLength e := by
  induction h with
  | refl => exact fun e => ⟨e, rfl⟩
  | tail _ hstep ih =>
      intro e
      obtain ⟨g, hg⟩ := exists_sourceLength_eq_of_contracts hstep e
      obtain ⟨f, hf⟩ := ih g
      exact ⟨f, hf.trans hg⟩

/-- The three invariants wanted by `LocalCases.ClosedEndpoint.ContractedGluing`,
preserved together. -/
theorem invariants_of_contractsMany {s t : Step.{u} degree} (h : ContractsMany s t)
    (hValid : s.data.Valid) (hConnected : graph_connected s.target)
    (hGenus : genus s.target = 0) :
    t.data.Valid ∧ graph_connected t.target ∧ genus t.target = 0 :=
  ⟨valid_of_contractsMany h hValid, graph_connected_of_contractsMany h hConnected,
    genus_zero_of_contractsMany h hGenus⟩

/-! ### The driver

A "should be contracted" flag is given as a *rule* `flag`, assigning to each
stage a predicate on its own occurrences, rather than as a subset of the
occurrences of the starting target.  That is what keeps the flag free of
transport: the flag of the contracted stage is `flag` evaluated at the new
bundle, not the image of the old flag under `foldEdge`.  Since a stage
carries its realization, `fun s e => s.realization.targetLength e = 0` is an
admissible rule, and that instance is `exists_terminal_positive`.

The caller has to supply the forest receipt at every flagged occurrence of
every reachable stage; that is the genuinely restrictive input.  It is
suppliable on the `LocalCases` side: `DraismaVargas/LocalCases/ZeroForestBridge.lean`
proves `contractionForest_of_isForest_of_targetLength_eq_zero`, which turns a
census forest plus a vanishing target length into `ContractionForest`.  That
file may not be imported here (it is in `LocalCases`, this file is in
`Infrastructure`), so the receipt stays a hypothesis of the driver and a
`LocalCases`-side wrapper discharges it. -/

private theorem exists_terminal_aux
    (flag : ∀ s : Step.{u} degree, s.target.edges → Prop) :
    ∀ n : ℕ, ∀ s : Step.{u} degree, Multiset.card s.target.edges ≤ n →
      s.data.Valid → graph_connected s.target → genus s.target = 0 →
      (∀ t : Step.{u} degree, ContractsMany s t → t.data.Valid → graph_connected t.target →
        genus t.target = 0 → ∀ e : t.target.edges, flag t e → ContractionForestAt t.data e) →
      ∃ final : Step.{u} degree, ContractsFlaggedMany flag s final ∧
        (∀ e : final.target.edges, ¬ flag final e) ∧
        final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hcard hValid hConnected hGenus _
      refine ⟨s, Relation.ReflTransGen.refl, ?_, hValid, hConnected, hGenus⟩
      intro e _
      have hmem : (e : s.target.V × s.target.V) ∈ s.target.edges := Multiset.coe_mem
      have hpos : 0 < Multiset.card s.target.edges :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨_, hmem⟩
      omega
  | succ n ih =>
      intro s hcard hValid hConnected hGenus hForest
      by_cases hex : ∃ e : s.target.edges, flag s e
      · obtain ⟨e, he⟩ := hex
        have hOne := num_edges_eq_one_of_genus_zero_of_connected s.target hConnected hGenus e
        have hreceipt : ContractionForestAt s.data e :=
          hForest s Relation.ReflTransGen.refl hValid hConnected hGenus e he
        have hstep : Contracts s (s.contractAt e hOne) :=
          Contracts.contract s e hOne hreceipt
        have hstepF : ContractsFlagged flag s (s.contractAt e hOne) :=
          ContractsFlagged.contract s e hOne hreceipt he
        have hcard' : Multiset.card (s.contractAt e hOne).target.edges ≤ n := by
          have h1 := one_le_card_edges_of_contracts hstep
          have h2 := card_edges_of_contracts hstep
          omega
        obtain ⟨hValid', hConnected', hGenus'⟩ :=
          invariants_of_contractsMany (Relation.ReflTransGen.single hstep) hValid hConnected hGenus
        obtain ⟨final, hreach, hno, hv, hc, hg⟩ :=
          ih (s.contractAt e hOne) hcard' hValid' hConnected' hGenus'
            (fun t hts => hForest t (Relation.ReflTransGen.head hstep hts))
        exact ⟨final, Relation.ReflTransGen.head hstepF hreach, hno, hv, hc, hg⟩
      · exact ⟨s, Relation.ReflTransGen.refl, fun e he => hex ⟨e, he⟩, hValid, hConnected, hGenus⟩

/-- **The driver, with the flag recorded.**  Starting from a valid stage over a
connected target of genus zero, contracting flagged occurrences one at a time
reaches a stage with no flagged occurrence left, still valid, still over a
connected target of genus zero — and *every contracted occurrence was flagged*,
which is what `ContractsFlaggedMany` in the conclusion says.  Termination is
`Multiset.card target.edges`, which `card_edges_of_contracts` drops by one at
every step.

The only input beyond the invariants is the forest receipt at each flagged
occurrence of each reachable stage; the `num_edges = 1` side condition of
`contractDatumAt` is supplied internally by
`num_edges_eq_one_of_genus_zero_of_connected`. -/
theorem exists_terminal_flagged (flag : ∀ s : Step.{u} degree, s.target.edges → Prop)
    (s : Step.{u} degree) (hValid : s.data.Valid) (hConnected : graph_connected s.target)
    (hGenus : genus s.target = 0)
    (hForest : ∀ t : Step.{u} degree, ContractsMany s t → t.data.Valid →
      graph_connected t.target → genus t.target = 0 →
      ∀ e : t.target.edges, flag t e → ContractionForestAt t.data e) :
    ∃ final : Step.{u} degree, ContractsFlaggedMany flag s final ∧
      (∀ e : final.target.edges, ¬ flag final e) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 :=
  exists_terminal_aux flag (Multiset.card s.target.edges) s le_rfl hValid hConnected hGenus hForest

/-- **The driver.**  Starting from a valid stage over a connected target of
genus zero, contracting flagged occurrences one at a time reaches a stage with
no flagged occurrence left, still valid, still over a connected target of genus
zero.  Termination is `Multiset.card target.edges`, which
`card_edges_of_contracts` drops by one at every step.

The only input beyond the invariants is the forest receipt at each flagged
occurrence of each reachable stage; the `num_edges = 1` side condition of
`contractDatumAt` is supplied internally by
`num_edges_eq_one_of_genus_zero_of_connected`. -/
theorem exists_terminal (flag : ∀ s : Step.{u} degree, s.target.edges → Prop)
    (s : Step.{u} degree) (hValid : s.data.Valid) (hConnected : graph_connected s.target)
    (hGenus : genus s.target = 0)
    (hForest : ∀ t : Step.{u} degree, ContractsMany s t → t.data.Valid →
      graph_connected t.target → genus t.target = 0 →
      ∀ e : t.target.edges, flag t e → ContractionForestAt t.data e) :
    ∃ final : Step.{u} degree, ContractsMany s final ∧
      (∀ e : final.target.edges, ¬ flag final e) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 := by
  obtain ⟨final, hreach, hno, hv, hc, hg⟩ :=
    exists_terminal_flagged flag s hValid hConnected hGenus hForest
  exact ⟨final, contractsMany_of_contractsFlaggedMany hreach, hno, hv, hc, hg⟩

/-! ### The terminal stage of the zero-length flag

This is the instance the terminal face of Part I needs, and the reason the
realization is bundled into `Step` at all. -/

/-- **The terminal conclusion.**  Contracting the zero-length target
occurrences one at a time reaches a stage every one of whose target occurrences
has *positive* length, still valid, still over a connected target of genus
zero, and reached by contracting zero-length occurrences only
(`ContractsFlaggedMany`).

By `Step.integralRealization` the terminal stage carries a genuine positive
`GluingDatum.IntegralRealization`; that is the object
`LocalCases.ClosedEndpoint.ContractedGluing` asks for.

The forest receipt is left exactly as the driver's hypothesis.  On the
`LocalCases` side it is discharged by
`ZeroForestBridge.contractionForest_of_isForest_of_targetLength_eq_zero`, which
needs only a census forest for the zero set of each reachable stage; that file
cannot be imported here because `Infrastructure` may not depend on
`LocalCases`. -/
theorem exists_terminal_positive_flagged (s : Step.{u} degree) (hValid : s.data.Valid)
    (hConnected : graph_connected s.target) (hGenus : genus s.target = 0)
    (hForest : ∀ t : Step.{u} degree, ContractsMany s t → t.data.Valid →
      graph_connected t.target → genus t.target = 0 →
      ∀ e : t.target.edges, t.realization.targetLength e = 0 →
        ContractionForestAt t.data e) :
    ∃ final : Step.{u} degree,
      ContractsFlaggedMany (fun r e => r.realization.targetLength e = 0) s final ∧
      (∀ e : final.target.edges, 0 < final.realization.targetLength e) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 := by
  obtain ⟨final, hreach, hno, hv, hc, hg⟩ :=
    exists_terminal_flagged (fun r e => r.realization.targetLength e = 0) s hValid hConnected
      hGenus hForest
  exact ⟨final, hreach, fun e => Nat.pos_of_ne_zero (hno e), hv, hc, hg⟩

/-- The terminal conclusion in the plain `ContractsMany` form: contracting the
zero-length target occurrences reaches a valid stage over a connected target of
genus zero all of whose target occurrences have positive length.
`exists_terminal_positive_flagged` is the same statement with the additional
information that only zero-length occurrences were contracted. -/
theorem exists_terminal_positive (s : Step.{u} degree) (hValid : s.data.Valid)
    (hConnected : graph_connected s.target) (hGenus : genus s.target = 0)
    (hForest : ∀ t : Step.{u} degree, ContractsMany s t → t.data.Valid →
      graph_connected t.target → genus t.target = 0 →
      ∀ e : t.target.edges, t.realization.targetLength e = 0 →
        ContractionForestAt t.data e) :
    ∃ final : Step.{u} degree, ContractsMany s final ∧
      (∀ e : final.target.edges, 0 < final.realization.targetLength e) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 := by
  obtain ⟨final, hreach, hpos, hv, hc, hg⟩ :=
    exists_terminal_positive_flagged s hValid hConnected hGenus hForest
  exact ⟨final, contractsMany_of_contractsFlaggedMany hreach, hpos, hv, hc, hg⟩

/-- The same terminal stage with the positive source lengths that the dilation
equation forces, packaged as the positive `GluingDatum.IntegralRealization`
that `LocalCases.ClosedEndpoint.ContractedGluing` consumes. -/
theorem exists_terminal_integralRealization (s : Step.{u} degree) (hValid : s.data.Valid)
    (hConnected : graph_connected s.target) (hGenus : genus s.target = 0)
    (hForest : ∀ t : Step.{u} degree, ContractsMany s t → t.data.Valid →
      graph_connected t.target → genus t.target = 0 →
      ∀ e : t.target.edges, t.realization.targetLength e = 0 →
        ContractionForestAt t.data e) :
    ∃ final : Step.{u} degree, ∃ positive : final.data.IntegralRealization,
      ContractsMany s final ∧
      (∀ e : final.target.edges,
        positive.targetLength e = final.realization.targetLength e) ∧
      (∀ e : final.data.SourceEdge,
        positive.sourceLength e = final.realization.sourceLength e) ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 := by
  obtain ⟨final, hreach, hpos, hv, hc, hg⟩ :=
    exists_terminal_positive s hValid hConnected hGenus hForest
  exact ⟨final, final.integralRealization hpos, hreach, fun _ => rfl, fun _ => rfl, hv, hc, hg⟩

/-- A target with no occurrence at all is edgeless. -/
theorem edges_eq_zero_of_isEmpty {G : CFGraph} (h : ∀ _e : G.edges, False) : G.edges = 0 := by
  by_contra hne
  obtain ⟨pair, hpair⟩ := Multiset.exists_mem_of_ne_zero hne
  exact h ⟨pair, ⟨0, Multiset.count_pos.mpr hpair⟩⟩

/-- A connected target of genus zero with no occurrence left is a single
vertex: this is what makes `exists_edgeless` a contraction *down to a point*.
-/
theorem card_vertices_eq_one_of_edges_eq_zero {G : CFGraph} (hGenus : genus G = 0)
    (hEdges : G.edges = 0) : Fintype.card G.V = 1 := by
  unfold genus at hGenus
  rw [hEdges] at hGenus
  simp only [Multiset.card_zero, Nat.cast_zero] at hGenus
  omega

/-- The extreme case of the driver: with every occurrence flagged, the target
is contracted all the way down to a single vertex
(`card_vertices_eq_one_of_edges_eq_zero`).  The datum is still valid,
so this is also the statement that a valid datum over a tree stays valid under
total contraction. -/
theorem exists_edgeless (s : Step.{u} degree) (hValid : s.data.Valid)
    (hConnected : graph_connected s.target) (hGenus : genus s.target = 0)
    (hForest : ∀ t : Step.{u} degree, ContractsMany s t → t.data.Valid →
      graph_connected t.target → genus t.target = 0 →
      ∀ e : t.target.edges, ContractionForestAt t.data e) :
    ∃ final : Step.{u} degree, ContractsMany s final ∧ final.target.edges = 0 ∧
      final.data.Valid ∧ graph_connected final.target ∧ genus final.target = 0 := by
  obtain ⟨final, hreach, hno, hv, hc, hg⟩ :=
    exists_terminal (fun _ _ => True) s hValid hConnected hGenus
      (fun t hts hvt hct hgt e _ => hForest t hts hvt hct hgt e)
  exact ⟨final, hreach, edges_eq_zero_of_isEmpty (fun e => hno e trivial), hv, hc, hg⟩

end IteratedContraction

end DraismaVargas.Infrastructure
