module

public import DraismaVargas.LocalCases.ClosedEndpoint
public import DraismaVargas.LocalCases.TerminalContraction
public import DraismaVargas.LocalCases.ZeroForestPreservation

@[expose] public section

/-!
# The contracted gluing receipt of a terminal face

`Candidate.ClearedFace.ContractedGluing`
(in `ClosedEndpoint`) is the first of the two source-dependent inputs of a
completed terminal face.  Its seven fields are

```
contractedTarget, contractedData, realization, valid,
targetConnected, targetGenus, sourceEquiv
```

and this file produces all seven from a terminal face's **own** census receipt,
namely the `forest` field of `Candidate.ClearedFace.SourceContractionTopology`.
It also produces that structure itself, `notLoopy` field included, so nothing
about the source has to be assumed beyond the single census forest.

## How the pieces fit

`TerminalContraction.faceStep face` is the starting stage of an iterated
contraction: the expanded target of the candidate, the candidate's outgoing
datum, and the face's own nonnegative realization.  Both

```
(faceStep face).data = candidate.datum
(faceStep face).realization = face.realization
```

hold **definitionally**, so `topology.forest` is literally the census forest
hypothesis of `ZeroForestPreservation.exists_terminal_sourceCorrespondence`.
That theorem contracts every zero-length target occurrence and returns, in one
package, a terminal stage with

* strictly positive target lengths — which upgrades its nonnegative
  realization to a genuine `GluingDatum.IntegralRealization`
  (`Step.integralRealization`), the third field;
* validity, target connectedness and target genus zero — fields four, five and
  six, transported along the contraction by the driver;
* a `SourceCorrespondence` from the face's stage to it, together with the
  identification `hZero` of its contracted occurrence set with the vanishing
  source occurrences — which is exactly the input of
  `TerminalContraction.faceSourceEquivOfTerminal`, the seventh field.

Nothing else is consumed.  In particular no positivity assumption on the
coordinates is made: this is the general, zero-carrying counterpart of
`ZeroFreeTerminalFace`.

## Which hypotheses are genuinely needed

Exactly three, and all three are about the stage the contraction starts at:

* `candidate.datum.Valid`,
* `graph_connected (TargetExpansion.graph tgt wall candidate.right)`,
* `genus (TargetExpansion.graph tgt wall candidate.right) = 0`.

None of them is available from `face`, `topology` or `candidate` alone.
`GluingDatum.Valid` is `Connected ∧ RiemannHurwitz` of the *source*, so it says
nothing about the target; `ClearedFace` records only lengths and a scale; and
`SourceContractionTopology` is a statement about the source core.

They are, however, consequences of the corresponding statements about the
**incoming** target and datum, by `Candidate.datum_valid`,
`TargetExpansion.graph_connected` and `TargetExpansion.graph_genus`; that form
is `nonempty_contractedGluing_of_incoming` below, and it matches the hypotheses
`ZeroFreeTerminalFace.contractedGluing` already takes.

## `¬ IsLoopy` is free

`SourceContractionTopology` has a second field, `notLoopy`, and §1 of this file
discharges it from the *same* two target hypotheses, so producing the structure
costs nothing beyond `IsForest`.

One might try to read looplessness off `GraphContraction.contract`; that would
need the whole iterated-contraction dictionary, and it is also not enough on its
own —
`sourceEnds_ne` only says that a source occurrence is not *already* a loop.  A
surviving occurrence becomes a loop exactly when its two endpoints are joined by
a walk of vanishing source occurrences, and the census forest condition does
**not** forbid that: `IsForest` is `C + |F| = n`, and adjoining a loop to `F`
leaves `C` alone while raising `|F|`, so the count is consistent.

What forbids it is that the *target* is a tree.  A source occurrence vanishes
exactly when the target occurrence under it does (the dilation index is
positive), so a vanishing source walk projects to a walk of vanishing target
occurrences between the two ends `a`, `b` of the surviving occurrence `c`.  That
walk avoids `c`, because `c` has positive length and a connected genus-zero
target has no parallel occurrences; hence `a` and `b` are still joined after
deleting `c`, hence the deleted graph is connected, hence
`|V| ≤ |E| - 1 + 1 = |E| = |V| - 1`.

So `¬ IsLoopy` is free **relative to the target hypotheses the contracted gluing
already needs** — it demands nothing new of the caller.

## `Nonempty`, and why

`ZeroForestPreservation.exists_terminal_sourceCorrespondence` is `Prop`-valued,
so the terminal stage is only ever obtained through `Exists.elim`; the strongest
statement provable from it is `Nonempty (ContractedGluing topology)`.  This is
not a weakening.  `ContractedGluing` is consumed only through
`ContractedGluing.bnExists`, whose conclusion `BNExists … 1 degree` is a `Prop`,
so a consumer may take the datum from `Classical.choice` — which is what
`contractedGluing` below does.
-/

namespace DraismaVargas.LocalCases.TerminalGluing

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.IteratedContraction
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.TerminalContraction
open DraismaVargas.LocalCases.ZeroForestBridge
open DraismaVargas.LocalCases.ZeroForestPreservation

/-! ## 0.  Three general lemmas

`Utilities.walk_has_edge_across_cut` and
`Utilities.Certificate.ContractionForestCensusGeneral.symmetric_reflTransGen`
are both `private`, and the first is stated for `SimpleGraph.Walk` rather than
for `Relation.ReflTransGen`.  The two `_local` lemmas below are the forms needed
here, proved from scratch. -/

section Generic

/-- A chain of `R`-steps from inside a predicate to outside it takes one step
across.  This is the `Relation.ReflTransGen` form of the `private` lemma
`Utilities.walk_has_edge_across_cut`. -/
theorem exists_cross_of_reflTransGen_local {α : Type*} {R : α → α → Prop} {S : α → Prop}
    {x y : α} (h : Relation.ReflTransGen R x y) (hx : S x) :
    ¬ S y → ∃ u v, S u ∧ ¬ S v ∧ R u v := by
  induction h with
  | refl => exact fun hy ↦ absurd hx hy
  | @tail m z _ hstep ih =>
    intro hz
    by_cases hm : S m
    · exact ⟨m, z, hm, hz, hstep⟩
    · exact ih hm

/-- Reflexive-transitive closure of a symmetric relation is symmetric.  The
`private` census lemma `symmetric_reflTransGen` is the same statement fixed at
`Fin n`. -/
theorem reflTransGen_symm_local {α : Type*} {R : α → α → Prop}
    (hSymm : ∀ x y, R x y → R y x) {x y : α} (h : Relation.ReflTransGen R x y) :
    Relation.ReflTransGen R y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail m z _ hstep ih => exact Relation.ReflTransGen.head (hSymm m z hstep) ih

/-- **A pair joined by exactly one occurrence determines that occurrence.**  If
`num_edges G x y = 1` then any two edge occurrences of `G` running between `x`
and `y`, in either orientation, are equal — not merely equal as vertex pairs. -/
theorem eq_of_num_edges_eq_one_local {G : CFGraph} {x y : G.V}
    (hOne : num_edges G x y = 1) (f c : G.edges)
    (hf : (f : G.V × G.V) = (x, y) ∨ (f : G.V × G.V) = (y, x))
    (hc : (c : G.V × G.V) = (x, y) ∨ (c : G.V × G.V) = (y, x)) :
    f = c := by
  classical
  have hCard : Multiset.card
      (G.edges.filter (fun e ↦ e = (x, y) ∨ e = (y, x))) = 1 := hOne
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.mp hCard
  have hfz : (f : G.V × G.V) = z := by
    have hMem : (f : G.V × G.V) ∈ G.edges.filter (fun e ↦ e = (x, y) ∨ e = (y, x)) :=
      Multiset.mem_filter.mpr ⟨Multiset.coe_mem, hf⟩
    rw [hz] at hMem
    exact Multiset.mem_singleton.mp hMem
  have hcz : (c : G.V × G.V) = z := by
    have hMem : (c : G.V × G.V) ∈ G.edges.filter (fun e ↦ e = (x, y) ∨ e = (y, x)) :=
      Multiset.mem_filter.mpr ⟨Multiset.coe_mem, hc⟩
    rw [hz] at hMem
    exact Multiset.mem_singleton.mp hMem
  have hPz : z = (x, y) ∨ z = (y, x) := hfz ▸ hf
  have hCount : G.edges.count z = 1 := by
    have h1 : (G.edges.filter (fun e ↦ e = (x, y) ∨ e = (y, x))).count z = 1 := by
      rw [hz]; exact Multiset.count_singleton_self z
    rwa [Multiset.count_filter, ite_eq_left hPz] at h1
  obtain ⟨pf, i⟩ := f
  obtain ⟨pc, j⟩ := c
  simp only at hfz hcz
  subst hfz
  subst hcz
  have hi : (i : ℕ) < 1 := hCount ▸ i.isLt
  have hj : (j : ℕ) < 1 := hCount ▸ j.isLt
  have hij : i = j := Fin.ext (by omega)
  rw [hij]

end Generic

/-! ## 1.  `¬ IsLoopy` over a connected genus-zero target

The `notLoopy` field of `Candidate.ClearedFace.SourceContractionTopology`, for
an arbitrary nonnegative realization of an arbitrary gluing datum whose target
is a tree.  See the module docstring for why the census forest condition alone
does not give it, and why the target hypotheses do. -/

section NotLoopy

variable {target : CFGraph} {degree : ℕ}

/-- One step of a walk through vanishing target occurrences. -/
def TargetZeroStep (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization) (x y : target.V) : Prop :=
  ∃ f : target.edges, realization.targetLength f = 0 ∧
    ((f : target.V × target.V) = (x, y) ∨ (f : target.V × target.V) = (y, x))

/-- A slot of the canonical zero set lies over a vanishing target occurrence:
the dilation index is positive, so the dilation equation forces it. -/
theorem targetLength_eq_zero_of_mem_sourceZeroSet (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    {slot : Fin data.sourceGraph.edges.card} (hSlot : slot ∈ realization.sourceZeroSet) :
    realization.targetLength (realization.sourceEdgeAt slot).1.1 = 0 := by
  have hDil := realization.dilation_length (realization.sourceEdgeAt slot)
  rw [(GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet
    realization slot).mp hSlot, Nat.mul_zero] at hDil
  exact hDil.symm

/-- **The projection, one step.**  A census step through the zero source set
projects to a step through vanishing target occurrences. -/
theorem targetZeroStep_of_slotStep (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    {u v : data.SourceVertex}
    (h : SlotStep data realization realization.sourceZeroSet u v) :
    TargetZeroStep data realization u.1.1 v.1.1 := by
  obtain ⟨slot, hSlot, hEnds⟩ := h
  refine ⟨(realization.sourceEdgeAt slot).1.1,
    targetLength_eq_zero_of_mem_sourceZeroSet data realization hSlot, ?_⟩
  rcases hEnds with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [← h1, ← h2]; rfl
  · right; rw [← h1, ← h2]; rfl

/-- **The projection.**  A whole census walk through the zero source set
projects to a walk through vanishing target occurrences. -/
theorem reflTransGen_targetZeroStep (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    {u v : data.SourceVertex}
    (h : Relation.ReflTransGen
      (SlotStep data realization realization.sourceZeroSet) u v) :
    Relation.ReflTransGen (TargetZeroStep data realization) u.1.1 v.1.1 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail _ _ _ hstep ih =>
    exact ih.tail (targetZeroStep_of_slotStep data realization hstep)

/-- A vanishing step survives the deletion of an occurrence of positive length:
the two cannot be the same occurrence, and over a connected genus-zero target
they cannot even be parallel. -/
theorem num_edges_eraseOccurrence_pos_of_targetZeroStep
    (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (c : target.edges) (hc : realization.targetLength c ≠ 0)
    {x y : target.V} (h : TargetZeroStep data realization x y) :
    0 < num_edges (eraseOccurrence target (c : target.V × target.V)) x y := by
  obtain ⟨f, hfZero, hfEnds⟩ := h
  have hpairMem : (c : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  by_cases hcase :
      (c : target.V × target.V) = (x, y) ∨ (c : target.V × target.V) = (y, x)
  · exfalso
    have hOneC : num_edges target
        (c : target.V × target.V).1 (c : target.V × target.V).2 = 1 :=
      num_edges_eq_one_of_genus_zero_of_connected target hConnected hGenus c
    have hOne : num_edges target x y = 1 := by
      rcases hcase with hEq | hEq
      · rw [← hOneC, hEq]
      · rw [← hOneC, hEq]; exact num_edges_symmetric target x y
    have hEqOcc := eq_of_num_edges_eq_one_local hOne f c hfEnds hcase
    rw [hEqOcc] at hfZero
    exact hc hfZero
  · rw [num_edges_eraseOccurrence_of_not target hpairMem x y hcase]
    rcases hfEnds with hEq | hEq
    · exact GraphContraction.num_edges_pos_of_mem_edges target x y
        (hEq ▸ Multiset.coe_mem)
    · exact GraphContraction.num_edges_pos_of_mem_edges' target x y
        (hEq ▸ Multiset.coe_mem)

/-- Deleting an occurrence whose two ends remain joined by a walk in the
deleted graph preserves connectedness.  The cut form of connectedness makes this
a two-case argument: a cut crossed by the deleted occurrence alone is crossed by
one of the steps of that walk. -/
theorem graph_connected_eraseOccurrence_of_reflTransGen
    (G : CFGraph) (hConnected : graph_connected G) (pair : G.V × G.V)
    (hpairMem : pair ∈ G.edges)
    (hReach : Relation.ReflTransGen
      (fun x y ↦ 0 < num_edges (eraseOccurrence G pair) x y) pair.1 pair.2) :
    graph_connected (eraseOccurrence G pair) := by
  have hSymm : ∀ x y : G.V, 0 < num_edges (eraseOccurrence G pair) x y →
      0 < num_edges (eraseOccurrence G pair) y x := by
    intro x y h
    rwa [num_edges_symmetric] at h
  intro S hS
  obtain ⟨v, hvS, w, hwS, hpos⟩ := hConnected S hS
  by_cases hcase : pair = (v, w) ∨ pair = (w, v)
  · rcases hcase with hEq | hEq
    · obtain ⟨u, z, huS, hzS, hstep⟩ :=
        exists_cross_of_reflTransGen_local (S := fun t ↦ t ∈ S) hReach
          (by rw [hEq]; exact hvS) (by rw [hEq]; exact hwS)
      exact ⟨u, huS, z, hzS, hstep⟩
    · obtain ⟨u, z, huS, hzS, hstep⟩ :=
        exists_cross_of_reflTransGen_local (S := fun t ↦ t ∈ S)
          (reflTransGen_symm_local hSymm hReach)
          (by rw [hEq]; exact hvS) (by rw [hEq]; exact hwS)
      exact ⟨u, huS, z, hzS, hstep⟩
  · exact ⟨v, hvS, w, hwS, by
      rw [num_edges_eraseOccurrence_of_not G hpairMem v w hcase]; exact hpos⟩

/-- **The `notLoopy` field, from the target alone.**  Contracting the vanishing
source occurrences of any nonnegative realization over a connected genus-zero
target leaves no surviving occurrence a loop. -/
theorem not_isLoopy_sourceZeroSet (data : GluingDatum target degree)
    (realization : data.NonnegativeIntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ¬ IsLoopy (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet := by
  rintro ⟨slot, hSlot, hEq⟩
  have hLenNe : realization.sourceLength (realization.sourceEdgeAt slot) ≠ 0 := fun h ↦
    hSlot ((GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet
      realization slot).mpr h)
  have hTargetNe :
      realization.targetLength (realization.sourceEdgeAt slot).1.1 ≠ 0 := by
    intro h
    exact hLenNe (sourceLength_eq_zero_of_targetLength_eq_zero data realization h
      (realization.sourceEdgeAt slot) rfl)
  have hReach0 := (compFold_iff (UnitSubdivisionPresentation.core data.sourceGraph)
    realization.sourceZeroSet _ _).mp hEq
  have hReach1 := (reachIn_iff_reflTransGen_slotStep data realization
    realization.sourceZeroSet _ _).mp hReach0
  rw [vertexEquiv_symm_core_tail data realization slot,
    vertexEquiv_symm_core_head data realization slot] at hReach1
  have hReach2 := reflTransGen_targetZeroStep data realization hReach1
  have hReach3 : Relation.ReflTransGen
      (fun x y ↦ 0 < num_edges
        (eraseOccurrence target ((realization.sourceEdgeAt slot).1.1 :
          target.V × target.V)) x y)
      ((realization.sourceEdgeAt slot).1.1 : target.V × target.V).1
      ((realization.sourceEdgeAt slot).1.1 : target.V × target.V).2 :=
    Relation.ReflTransGen.mono (fun _ _ hStep ↦
      num_edges_eraseOccurrence_pos_of_targetZeroStep data realization hConnected
        hGenus (realization.sourceEdgeAt slot).1.1 hTargetNe hStep) _ _ hReach2
  have hConn' := graph_connected_eraseOccurrence_of_reflTransGen target hConnected
    ((realization.sourceEdgeAt slot).1.1 : target.V × target.V) Multiset.coe_mem hReach3
  have hBound := Utilities.graph_connected_card_vertices_le_card_edges_add_one _ hConn'
  rw [card_vertices_eraseOccurrence,
    card_edges_eraseOccurrence target Multiset.coe_mem] at hBound
  have hOneLe : 1 ≤ Multiset.card target.edges :=
    Multiset.card_pos.mpr (fun h ↦ by
      simpa [h] using (Multiset.coe_mem (x := (realization.sourceEdgeAt slot).1.1)))
  have hVerts : (Fintype.card target.V : ℤ) = (Multiset.card target.edges : ℤ) + 1 := by
    unfold genus at hGenus
    omega
  have hVertsNat : Fintype.card target.V = Multiset.card target.edges + 1 := by
    exact_mod_cast hVerts
  omega

end NotLoopy

/-! ## 2.  The terminal face -/

section TerminalFace

variable {tgt : CFGraph.{0}} {degree : ℕ} {datum : GluingDatum tgt degree} {wall : tgt.V}
  {candidate : Candidate tgt degree datum wall} {coordinate : Type*}
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}

/-- **`SourceContractionTopology`, produced rather than assumed.**  Only the
census forest is a genuine source-side hypothesis; the second field comes from
§1 and the same two target hypotheses the contracted gluing receipt needs
anyway. -/
theorem sourceContractionTopology
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hForest : IsForest
      (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    Candidate.ClearedFace.SourceContractionTopology face where
  forest := hForest
  notLoopy :=
    not_isLoopy_sourceZeroSet candidate.datum face.realization hConnected hGenus

/-- **The contracted gluing receipt of a terminal face.**  Contracting every
zero-length occurrence of a cleared face whose zero source set is a census
forest produces all seven fields of `Candidate.ClearedFace.ContractedGluing`.

The only source-side input is `topology.forest`; `topology.notLoopy` is used
only to name the target `topology.contractedSpec.graph` of the resulting
`LaplacianEquiv`. -/
theorem nonempty_contractedGluing
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face)
    (hValid : candidate.datum.Valid)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    Nonempty (Candidate.ClearedFace.ContractedGluing topology) := by
  obtain ⟨final, sc, -, hPositive, hZero, hValidFinal, hConnectedFinal,
      hGenusFinal, -⟩ :=
    ZeroForestPreservation.exists_terminal_sourceCorrespondence (faceStep face)
      hValid hConnected hGenus topology.forest
  exact ⟨{ contractedTarget := final.target
           contractedData := final.data
           realization := final.integralRealization hPositive
           valid := hValidFinal
           targetConnected := hConnectedFinal
           targetGenus := hGenusFinal
           sourceEquiv := faceSourceEquivOfTerminal face topology sc hPositive hZero }⟩

/-- The same receipt as data.  `ContractedGluing` is a `Type`, but the terminal
stage it names is produced by a `Prop`-valued existential, so the choice
principle is unavoidable here; it is harmless, since every consumer of the
structure lands in `Prop`. -/
noncomputable def contractedGluing
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face)
    (hValid : candidate.datum.Valid)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    Candidate.ClearedFace.ContractedGluing topology :=
  Classical.choice (nonempty_contractedGluing face topology hValid hConnected hGenus)

/-- **The whole source-side receipt from the census forest alone.**  This is the
form a completed terminal face wants: the topology is produced by
`sourceContractionTopology`, not assumed. -/
theorem nonempty_contractedGluing_of_isForest
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hForest : IsForest
      (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet)
    (hValid : candidate.datum.Valid)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    Nonempty (Candidate.ClearedFace.ContractedGluing
      (sourceContractionTopology face hForest hConnected hGenus)) :=
  nonempty_contractedGluing face _ hValid hConnected hGenus

/-! ### The same, stated on the incoming target

`Candidate.datum_valid`, `TargetExpansion.graph_connected` and
`TargetExpansion.graph_genus` move all three hypotheses back across the one-edge
vertex split, to exactly the form `ZeroFreeTerminalFace.contractedGluing` takes
and the form a march state naturally carries. -/

theorem sourceContractionTopology_of_incoming
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (hForest : IsForest
      (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet)
    (hConnected : graph_connected tgt) (hGenus : genus tgt = 0) :
    Candidate.ClearedFace.SourceContractionTopology face :=
  sourceContractionTopology face hForest
    (TargetExpansion.graph_connected tgt wall candidate.right hConnected)
    (by rw [TargetExpansion.graph_genus tgt wall candidate.right, hGenus])

theorem nonempty_contractedGluing_of_incoming
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face)
    (hValid : datum.Valid)
    (hConnected : graph_connected tgt)
    (hGenus : genus tgt = 0) :
    Nonempty (Candidate.ClearedFace.ContractedGluing topology) :=
  nonempty_contractedGluing face topology (candidate.datum_valid hValid)
    (TargetExpansion.graph_connected tgt wall candidate.right hConnected)
    (by rw [TargetExpansion.graph_genus tgt wall candidate.right, hGenus])

noncomputable def contractedGluing_of_incoming
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face)
    (hValid : datum.Valid)
    (hConnected : graph_connected tgt)
    (hGenus : genus tgt = 0) :
    Candidate.ClearedFace.ContractedGluing topology :=
  Classical.choice
    (nonempty_contractedGluing_of_incoming face topology hValid hConnected hGenus)

/-! ### The rank-one pencil on the canonical contracted source

This is the whole point of the receipt: `ClearedFace.exists_subdivisionPencil`
consumes `ContractedGluing` only through `ContractedGluing.bnExists`. -/

/-- **A terminal face whose zero source set is a census forest carries the
degree-`degree` rank-one pencil on its canonical positive contraction.**  The
zero-carrying counterpart of `ZeroFreeTerminalFace.bnExists_contractedSpec`. -/
theorem bnExists_contractedSpec
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face)
    (hValid : candidate.datum.Valid)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    BNExists topology.contractedSpec.graph 1 degree :=
  (contractedGluing face topology hValid hConnected hGenus).bnExists

/-- The gonality bound at a terminal face, once the second receipt
(`InputRefinement`) is supplied.  This is
`ClearedFace.regularSubdivisionGonality_le` with its first argument
discharged; the connectivity its pendant pushforward needs is `hValid.1`. -/
theorem regularSubdivisionGonality_le
    {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
    (face : Candidate.ClearedFace candidate presentation coordinates)
    (topology : Candidate.ClearedFace.SourceContractionTopology face)
    (hValid : candidate.datum.Valid)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0)
    (input : Candidate.ClearedFace.InputRefinement spec topology) :
    spec.regularSubdivisionGonality ≤ degree :=
  Candidate.ClearedFace.regularSubdivisionGonality_le
    (contractedGluing face topology hValid hConnected hGenus) input hValid.1

end TerminalFace

end DraismaVargas.LocalCases.TerminalGluing
