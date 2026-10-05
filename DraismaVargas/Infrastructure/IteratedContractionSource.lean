module

public import DraismaVargas.Infrastructure.ContractionFibre
public import DraismaVargas.Infrastructure.IteratedContraction

@[expose] public section

/-!
# The source correspondence carried along an iterated contraction

`DraismaVargas/Infrastructure/ContractionFibre.lean` describes the source side
of **one** contraction of a gluing datum: `sourceVertexMap` is surjective, its
fibres are the classes of `ReachThroughContracted` (walks through the single
contracted occurrence), the surviving source occurrences correspond bijectively
to the source occurrences downstairs (`sourceEdgeEquiv`), and that bijection
preserves `sourceEdgeIndex`.

This file carries all of that along `IteratedContraction.ContractsMany`.

## Why one induction, not six compositions

The six statements are

1. the composed source vertex map is surjective;
2. the composed source occurrence map is a bijection from the source
   occurrences lying over *surviving* target occurrences onto **all** source
   occurrences of the final stage;
3. ordered endpoint compatibility;
4. preservation of `sourceEdgeIndex`;
5. the fibre equation: two source vertices of the starting stage have the same
   image exactly when a walk through the *set* of contracted occurrences joins
   them;
6. preservation of `sourceLength`.

(1), (3), (4) and (6) compose mechanically, and (2) composes because
`ContractionFibre.sourceEdgeEquiv` is an `Equiv`.  **(5) does not compose.**
The one-step statement at stage `k` speaks about occurrences of the `k`-th
source graph, whereas the composed statement speaks about occurrences of the
`0`-th; gluing them needs the composed occurrence bijection to carry "lies over
the occurrence contracted at stage `k+1`" back to an occurrence of the starting
target.  Concretely, the inductive step of (5) uses
* (2) — surjectivity of the composed occurrence map, so that the freshly
  contracted occurrence upstairs is the image of an occurrence of the *starting*
  stage, and no occurrence appears downstream out of nowhere;
* (3) — to know the endpoints of that occurrence are the images of its
  endpoints upstairs;
* (1) — surjectivity of the composed vertex map, to split a transitivity step
  downstairs into two steps upstairs;
* (5) itself at the previous stage, for the two ends.

So all six are carried simultaneously by a single induction over
`Relation.ReflTransGen`.

## What is proved

* `StepThroughSet`, `ReachThroughSet` — the many-occurrence generalisation of
  `ContractionFibre.ContractedStep` / `ContractionFibre.ReachThroughContracted`;
* `SourceCorrespondence` — the six conjuncts, packaged;
* `FullCorrespondence` — `SourceCorrespondence` together with the target
  occurrence bijection it lies over; this is the object the induction actually
  carries, because the *target* occurrence bijection is what says which
  occurrence of the starting target is being contracted next;
* `stepCorrespondence` — the inductive step, as **data**;
* `nonempty_sourceCorrespondence` — the theorem:
  `ContractsMany s t → Nonempty (SourceCorrespondence s t)`;
* `sourceZeroSet_eq_filter`, `stepThroughSet_iff_sourceLength_eq_zero` — the
  zero-set identification: the zero set of the quotient source is the set of
  slots lying over the zero-length target occurrences, so a step of
  `StepThroughSet s Z` for `Z` the zero-length target occurrences is exactly a
  step along a zero-length source occurrence.

`ContractsMany` is `Prop`-valued (`Relation.ReflTransGen` of a `Prop`-valued
relation), so the iterated statement can only be `Prop`-valued; the one-step
constructions `stepCorrespondence` and `reflCorrespondence` are `Type`-valued
and are exported as such.
-/

namespace DraismaVargas.Infrastructure

namespace IteratedContractionSource

open GraphContraction GluingContraction ContractionFibre IteratedContraction

universe u

variable {degree : ℕ}

/-! ## Walks through a set of contracted occurrences -/

/-- One step of a walk over contracted occurrences: the two ends of a source
occurrence lying over a member of `F`. -/
def StepThroughSet (s : Step.{u} degree) (F : Finset s.target.edges)
    (x y : s.data.SourceVertex) : Prop :=
  ∃ e : s.data.SourceEdge, e.1.1 ∈ F ∧
    (s.data.sourceEnds e).1 = x ∧ (s.data.sourceEnds e).2 = y

/-- Joined by a walk in the quotient source all of whose occurrences lie over a
member of `F`.  This is `ContractionFibre.ReachThroughContracted` with a whole
`Finset` of occurrences in place of a single one. -/
def ReachThroughSet (s : Step.{u} degree) (F : Finset s.target.edges) :
    s.data.SourceVertex → s.data.SourceVertex → Prop :=
  Relation.EqvGen (StepThroughSet s F)

theorem reachThroughSet_equivalence (s : Step.{u} degree) (F : Finset s.target.edges) :
    Equivalence (ReachThroughSet s F) :=
  Relation.EqvGen.is_equivalence _

theorem ReachThroughSet.refl (s : Step.{u} degree) (F : Finset s.target.edges)
    (x : s.data.SourceVertex) : ReachThroughSet s F x x :=
  Relation.EqvGen.refl x

theorem ReachThroughSet.symm {s : Step.{u} degree} {F : Finset s.target.edges}
    {x y : s.data.SourceVertex} (h : ReachThroughSet s F x y) :
    ReachThroughSet s F y x :=
  Relation.EqvGen.symm x y h

theorem ReachThroughSet.trans {s : Step.{u} degree} {F : Finset s.target.edges}
    {x y z : s.data.SourceVertex} (hxy : ReachThroughSet s F x y)
    (hyz : ReachThroughSet s F y z) : ReachThroughSet s F x z :=
  Relation.EqvGen.trans x y z hxy hyz

theorem StepThroughSet.reach {s : Step.{u} degree} {F : Finset s.target.edges}
    {x y : s.data.SourceVertex} (h : StepThroughSet s F x y) :
    ReachThroughSet s F x y :=
  Relation.EqvGen.rel x y h

theorem StepThroughSet.mono {s : Step.{u} degree} {F F' : Finset s.target.edges}
    (hsub : F ⊆ F') {x y : s.data.SourceVertex} (h : StepThroughSet s F x y) :
    StepThroughSet s F' x y := by
  obtain ⟨e, hmem, hfst, hsnd⟩ := h
  exact ⟨e, hsub hmem, hfst, hsnd⟩

theorem ReachThroughSet.mono {s : Step.{u} degree} {F F' : Finset s.target.edges}
    (hsub : F ⊆ F') {x y : s.data.SourceVertex} (h : ReachThroughSet s F x y) :
    ReachThroughSet s F' x y := by
  induction h with
  | rel u v huv => exact (huv.mono hsub).reach
  | refl u => exact ReachThroughSet.refl s F' u
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Nothing is contracted along the empty set, so the walk relation is
equality. -/
theorem reachThroughSet_empty_iff (s : Step.{u} degree) (x y : s.data.SourceVertex) :
    ReachThroughSet s ∅ x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | rel u v huv => exact absurd huv.choose_spec.1 (Finset.notMem_empty _)
    | refl u => rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  · rintro rfl
    exact ReachThroughSet.refl s ∅ x

/-! ## The interface: the composed source correspondence -/

/-- The source-side correspondence carried along an iterated contraction.
`contracted` is the set of occurrences of the starting target that were
contracted along the way; `vertexMap` and `edgeMap` are the composites of the
per-step source maps. -/
structure SourceCorrespondence (s t : Step.{u} degree) where
  /-- The occurrences of the starting target contracted along the path. -/
  contracted : Finset s.target.edges
  /-- The composite of the per-step source vertex maps. -/
  vertexMap : s.data.SourceVertex → t.data.SourceVertex
  /-- The composite of the per-step source occurrence maps, on the source
  occurrences lying over surviving target occurrences. -/
  edgeMap : {e : s.data.SourceEdge // e.1.1 ∉ contracted} ≃ t.data.SourceEdge
  /-- (1) -/
  vertexMap_surjective : Function.Surjective vertexMap
  /-- (3) ordered endpoint compatibility -/
  sourceEnds_edgeMap : ∀ e, t.data.sourceEnds (edgeMap e) =
    (vertexMap (s.data.sourceEnds e.1).1, vertexMap (s.data.sourceEnds e.1).2)
  /-- (4) index preservation -/
  sourceEdgeIndex_edgeMap : ∀ e,
    t.data.sourceEdgeIndex (edgeMap e) = s.data.sourceEdgeIndex e.1
  /-- (5) the fibre equation: the crux. -/
  vertexMap_eq_iff : ∀ x y, vertexMap x = vertexMap y ↔ ReachThroughSet s contracted x y
  /-- (6) source lengths are preserved -/
  sourceLength_edgeMap : ∀ e,
    t.realization.sourceLength (edgeMap e) = s.realization.sourceLength e.1

/-- The object the induction actually carries: a `SourceCorrespondence`
together with the bijection of **target** occurrences it lies over.

The extra data is what makes the inductive step possible at all.  When one more
target occurrence of the intermediate stage is contracted, `contracted` has to
grow by the occurrence of the *starting* target lying over it — and only
`targetMap` says which occurrence that is. -/
structure FullCorrespondence (s t : Step.{u} degree) extends SourceCorrespondence s t where
  /-- The surviving occurrences of the starting target are the occurrences of
  the final target. -/
  targetMap : {f : s.target.edges // f ∉ contracted} ≃ t.target.edges
  /-- The source occurrence bijection lies over the target occurrence
  bijection. -/
  edgeMap_fst : ∀ e, (edgeMap e).1.1 = targetMap ⟨e.1.1.1, e.2⟩

/-! ## One contraction, read at a chosen occurrence

`ContractionFibre` carries the endpoints `a`, `b` of the contracted occurrence
as separate parameters together with `hc : (contracted : _ × _) = (a, b)`.  A
`Step` contracts at an occurrence, so `hc` is `rfl` there; these wrappers do
that instantiation once. -/

section AtOccurrence

variable {target : CFGraph.{u}} (data : GluingDatum target degree) (edge : target.edges)
  (hOne : num_edges target (edge : target.V × target.V).1
    (edge : target.V × target.V).2 = 1)

/-- `GluingContraction.sourceVertexMap` at a chosen target occurrence. -/
noncomputable def sourceVertexMapAt (x : data.SourceVertex) :
    (contractDatumAt data edge hOne).SourceVertex :=
  sourceVertexMap data (contracted := edge) (a := (edge : target.V × target.V).1)
    (b := (edge : target.V × target.V).2) rfl (fst_ne_snd edge) hOne x

/-- `GluingContraction.foldEdgeEquiv` at a chosen target occurrence. -/
noncomputable def foldEdgeEquivAt :
    {f : target.edges // f ≠ edge} ≃ (contractTarget edge hOne).edges :=
  foldEdgeEquiv (contracted := edge) (a := (edge : target.V × target.V).1)
    (b := (edge : target.V × target.V).2) rfl (fst_ne_snd edge) hOne

/-- `ContractionFibre.sourceEdgeEquiv` at a chosen target occurrence. -/
noncomputable def sourceEdgeEquivAt :
    {e : data.SourceEdge // e.1.1 ≠ edge} ≃ (contractDatumAt data edge hOne).SourceEdge :=
  sourceEdgeEquiv data (contracted := edge) (a := (edge : target.V × target.V).1)
    (b := (edge : target.V × target.V).2) rfl (fst_ne_snd edge) hOne

theorem sourceVertexMapAt_surjective :
    Function.Surjective (sourceVertexMapAt data edge hOne) :=
  sourceVertexMap_surjective data _ _ hOne

/-- The source occurrence bijection lies over the target occurrence
bijection. -/
theorem fst_sourceEdgeEquivAt (e : {e : data.SourceEdge // e.1.1 ≠ edge}) :
    (sourceEdgeEquivAt data edge hOne e).1.1 = foldEdgeEquivAt edge hOne ⟨e.1.1.1, e.2⟩ :=
  rfl

theorem sourceEnds_sourceEdgeEquivAt (e : {e : data.SourceEdge // e.1.1 ≠ edge}) :
    (contractDatumAt data edge hOne).sourceEnds (sourceEdgeEquivAt data edge hOne e)
      = (sourceVertexMapAt data edge hOne (data.sourceEnds e.1).1,
        sourceVertexMapAt data edge hOne (data.sourceEnds e.1).2) :=
  sourceEnds_sourceEdgeMap data _ _ hOne e

theorem sourceEdgeIndex_sourceEdgeEquivAt (e : {e : data.SourceEdge // e.1.1 ≠ edge}) :
    (contractDatumAt data edge hOne).sourceEdgeIndex (sourceEdgeEquivAt data edge hOne e)
      = data.sourceEdgeIndex e.1 :=
  sourceEdgeIndex_sourceEdgeEquiv data _ _ hOne e

/-- A surviving source occurrence keeps its old length, at a chosen target
occurrence. -/
theorem sourceLength_sourceEdgeEquivAt (realization : data.NonnegativeIntegralRealization)
    (e : {e : data.SourceEdge // e.1.1 ≠ edge}) :
    (contractRealizationAt data realization edge hOne).sourceLength
        (sourceEdgeEquivAt data edge hOne e)
      = realization.sourceLength e.1 :=
  contractRealization_sourceLength_sourceEdgeMap data realization rfl (fst_ne_snd edge) hOne e

/-- The fibre equation for one contraction, at a chosen occurrence. -/
theorem sourceVertexMapAt_eq_iff (x y : data.SourceVertex) :
    sourceVertexMapAt data edge hOne x = sourceVertexMapAt data edge hOne y ↔
      ReachThroughContracted data edge x y :=
  sourceVertexMap_eq_iff data _ _ hOne x y

/-- Above the contracted occurrence the two ends collapse. -/
theorem sourceVertexMapAt_sourceEnds_eq_of_contracted (e : data.SourceEdge)
    (he : e.1.1 = edge) :
    sourceVertexMapAt data edge hOne (data.sourceEnds e).1
      = sourceVertexMapAt data edge hOne (data.sourceEnds e).2 :=
  sourceVertexMap_sourceEnds_eq_of_contracted data _ _ hOne e he

end AtOccurrence

/-! ## The reflexive case: nothing contracted -/

/-- The identity correspondence.  Nothing is contracted, the two source maps
are the identity, and the fibre equation degenerates to `x = y` because a walk
through the empty set of occurrences is a constant walk. -/
def reflCorrespondence (s : Step.{u} degree) : FullCorrespondence s s where
  contracted := ∅
  vertexMap := id
  edgeMap := Equiv.subtypeUnivEquiv
    (fun e : s.data.SourceEdge => Finset.notMem_empty e.1.1)
  vertexMap_surjective := Function.surjective_id
  sourceEnds_edgeMap := fun _ => rfl
  sourceEdgeIndex_edgeMap := fun _ => rfl
  vertexMap_eq_iff := fun x y => (reachThroughSet_empty_iff s x y).symm
  sourceLength_edgeMap := fun _ => rfl
  targetMap := Equiv.subtypeUnivEquiv (fun f : s.target.edges => Finset.notMem_empty f)
  edgeMap_fst := fun _ => rfl

/-! ## The inductive step: one more contraction -/

section OneMore

variable {s m : Step.{u} degree} (sc : FullCorrespondence s m) (edge : m.target.edges)

/-- The occurrence of the **starting** target lying over the occurrence of the
intermediate target that is about to be contracted.  This is the occurrence
that has to be added to `contracted`, and reading it off is exactly what the
extra field `targetMap` of `FullCorrespondence` is for. -/
def preimageEdge : s.target.edges := (sc.targetMap.symm edge).1

theorem preimageEdge_notMem : preimageEdge sc edge ∉ sc.contracted :=
  (sc.targetMap.symm edge).2

/-- The updated set of contracted occurrences. -/
def nextContracted : Finset s.target.edges :=
  sc.contracted.cons (preimageEdge sc edge) (preimageEdge_notMem sc edge)

theorem mem_nextContracted_iff (f : s.target.edges) :
    f ∈ nextContracted sc edge ↔ f = preimageEdge sc edge ∨ f ∈ sc.contracted :=
  Finset.mem_cons

theorem mem_nextContracted_self : preimageEdge sc edge ∈ nextContracted sc edge :=
  Finset.mem_cons_self _ _

theorem notMem_nextContracted_iff (f : s.target.edges) :
    f ∉ nextContracted sc edge ↔ f ∉ sc.contracted ∧ f ≠ preimageEdge sc edge := by
  rw [mem_nextContracted_iff sc edge f]
  tauto

theorem subset_nextContracted : sc.contracted ⊆ nextContracted sc edge :=
  Finset.subset_cons _

/-- A surviving occurrence of the starting target is the one lying over the
occurrence being contracted exactly when `targetMap` sends it there. -/
theorem targetMap_eq_iff (g : {f : s.target.edges // f ∉ sc.contracted}) :
    sc.targetMap g = edge ↔ g.1 = preimageEdge sc edge := by
  constructor
  · intro h
    have h2 : g = sc.targetMap.symm edge := by rw [← h, Equiv.symm_apply_apply]
    exact congrArg Subtype.val h2
  · intro h
    have h2 : g = sc.targetMap.symm edge := Subtype.ext h
    rw [h2, Equiv.apply_symm_apply]

/-- **The bridge that makes conjunct (5) compose.**  A source occurrence of the
starting stage lands over the occurrence being contracted exactly when it lies
over `preimageEdge`, an occurrence of the *starting* target. -/
theorem edgeMap_fst_eq_iff (e : {e : s.data.SourceEdge // e.1.1 ∉ sc.contracted}) :
    (sc.edgeMap e).1.1 = edge ↔ e.1.1.1 = preimageEdge sc edge := by
  rw [sc.edgeMap_fst e]
  exact targetMap_eq_iff sc edge ⟨e.1.1.1, e.2⟩

variable (hOne : num_edges m.target (edge : m.target.V × m.target.V).1
    (edge : m.target.V × m.target.V).2 = 1)

/-- The updated target occurrence bijection. -/
noncomputable def nextTargetEquiv :
    {f : s.target.edges // f ∉ nextContracted sc edge} ≃ (contractTarget edge hOne).edges :=
  (Equiv.subtypeEquivRight (notMem_nextContracted_iff sc edge)).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun f : s.target.edges => f ∉ sc.contracted)
        (fun f : s.target.edges => f ≠ preimageEdge sc edge)).symm.trans
      ((Equiv.subtypeEquiv sc.targetMap
          (fun g => not_congr (targetMap_eq_iff sc edge g).symm)).trans
        (foldEdgeEquivAt edge hOne)))

/-- The updated source occurrence bijection. -/
noncomputable def nextEdgeEquiv :
    {e : s.data.SourceEdge // e.1.1 ∉ nextContracted sc edge} ≃
      (contractDatumAt m.data edge hOne).SourceEdge :=
  (Equiv.subtypeEquivRight
      (fun e : s.data.SourceEdge => notMem_nextContracted_iff sc edge e.1.1)).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun e : s.data.SourceEdge => e.1.1 ∉ sc.contracted)
        (fun e : s.data.SourceEdge => e.1.1 ≠ preimageEdge sc edge)).symm.trans
      ((Equiv.subtypeEquiv sc.edgeMap
          (fun g => not_congr (edgeMap_fst_eq_iff sc edge g).symm)).trans
        (sourceEdgeEquivAt m.data edge hOne)))

theorem nextTargetEquiv_apply (f : {f : s.target.edges // f ∉ nextContracted sc edge})
    (h₁ : f.1 ∉ sc.contracted) (h₂ : sc.targetMap ⟨f.1, h₁⟩ ≠ edge) :
    nextTargetEquiv sc edge hOne f
      = foldEdgeEquivAt edge hOne ⟨sc.targetMap ⟨f.1, h₁⟩, h₂⟩ := rfl

theorem nextEdgeEquiv_apply (e : {e : s.data.SourceEdge // e.1.1 ∉ nextContracted sc edge})
    (h₁ : e.1.1.1 ∉ sc.contracted) (h₂ : (sc.edgeMap ⟨e.1, h₁⟩).1.1 ≠ edge) :
    nextEdgeEquiv sc edge hOne e
      = sourceEdgeEquivAt m.data edge hOne ⟨sc.edgeMap ⟨e.1, h₁⟩, h₂⟩ := rfl

/-! ### Conjuncts (3) and (4) for the composed step -/

theorem sourceEnds_nextEdgeEquiv
    (e : {e : s.data.SourceEdge // e.1.1 ∉ nextContracted sc edge}) :
    (contractDatumAt m.data edge hOne).sourceEnds (nextEdgeEquiv sc edge hOne e)
      = (sourceVertexMapAt m.data edge hOne (sc.vertexMap (s.data.sourceEnds e.1).1),
        sourceVertexMapAt m.data edge hOne (sc.vertexMap (s.data.sourceEnds e.1).2)) := by
  obtain ⟨h₁, h₂⟩ := (notMem_nextContracted_iff sc edge e.1.1.1).mp e.2
  have h₃ : (sc.edgeMap ⟨e.1, h₁⟩).1.1 ≠ edge := fun hcon =>
    h₂ ((edgeMap_fst_eq_iff sc edge ⟨e.1, h₁⟩).mp hcon)
  rw [nextEdgeEquiv_apply sc edge hOne e h₁ h₃,
    sourceEnds_sourceEdgeEquivAt m.data edge hOne ⟨sc.edgeMap ⟨e.1, h₁⟩, h₃⟩,
    sc.sourceEnds_edgeMap ⟨e.1, h₁⟩]

theorem sourceEdgeIndex_nextEdgeEquiv
    (e : {e : s.data.SourceEdge // e.1.1 ∉ nextContracted sc edge}) :
    (contractDatumAt m.data edge hOne).sourceEdgeIndex (nextEdgeEquiv sc edge hOne e)
      = s.data.sourceEdgeIndex e.1 := by
  obtain ⟨h₁, h₂⟩ := (notMem_nextContracted_iff sc edge e.1.1.1).mp e.2
  have h₃ : (sc.edgeMap ⟨e.1, h₁⟩).1.1 ≠ edge := fun hcon =>
    h₂ ((edgeMap_fst_eq_iff sc edge ⟨e.1, h₁⟩).mp hcon)
  rw [nextEdgeEquiv_apply sc edge hOne e h₁ h₃,
    sourceEdgeIndex_sourceEdgeEquivAt m.data edge hOne ⟨sc.edgeMap ⟨e.1, h₁⟩, h₃⟩,
    sc.sourceEdgeIndex_edgeMap ⟨e.1, h₁⟩]

/-- **Conjunct (6) for the composed step.**  Exactly the same composition as
conjunct (4): the freshly contracted stage keeps the length a surviving source
occurrence had at the intermediate stage, and the intermediate stage kept the
length it had at the start. -/
theorem sourceLength_nextEdgeEquiv
    (e : {e : s.data.SourceEdge // e.1.1 ∉ nextContracted sc edge}) :
    (contractRealizationAt m.data m.realization edge hOne).sourceLength
        (nextEdgeEquiv sc edge hOne e)
      = s.realization.sourceLength e.1 := by
  obtain ⟨h₁, h₂⟩ := (notMem_nextContracted_iff sc edge e.1.1.1).mp e.2
  have h₃ : (sc.edgeMap ⟨e.1, h₁⟩).1.1 ≠ edge := fun hcon =>
    h₂ ((edgeMap_fst_eq_iff sc edge ⟨e.1, h₁⟩).mp hcon)
  rw [nextEdgeEquiv_apply sc edge hOne e h₁ h₃,
    sourceLength_sourceEdgeEquivAt m.data edge hOne m.realization
      ⟨sc.edgeMap ⟨e.1, h₁⟩, h₃⟩,
    sc.sourceLength_edgeMap ⟨e.1, h₁⟩]

/-- The composed source occurrence bijection still lies over the composed
target occurrence bijection. -/
theorem edgeMap_fst_nextEdgeEquiv
    (e : {e : s.data.SourceEdge // e.1.1 ∉ nextContracted sc edge}) :
    (nextEdgeEquiv sc edge hOne e).1.1
      = nextTargetEquiv sc edge hOne ⟨e.1.1.1, e.2⟩ := by
  obtain ⟨h₁, h₂⟩ := (notMem_nextContracted_iff sc edge e.1.1.1).mp e.2
  have h₃ : (sc.edgeMap ⟨e.1, h₁⟩).1.1 ≠ edge := fun hcon =>
    h₂ ((edgeMap_fst_eq_iff sc edge ⟨e.1, h₁⟩).mp hcon)
  have h₄ : sc.targetMap ⟨e.1.1.1, h₁⟩ ≠ edge := by
    rw [← sc.edgeMap_fst ⟨e.1, h₁⟩]
    exact h₃
  rw [nextEdgeEquiv_apply sc edge hOne e h₁ h₃,
    nextTargetEquiv_apply sc edge hOne ⟨e.1.1.1, e.2⟩ h₁ h₄,
    fst_sourceEdgeEquivAt m.data edge hOne ⟨sc.edgeMap ⟨e.1, h₁⟩, h₃⟩]
  exact congrArg (fun z => foldEdgeEquivAt edge hOne z)
    (Subtype.ext (sc.edgeMap_fst ⟨e.1, h₁⟩))

/-! ### Conjunct (5), the easy direction -/

/-- A walk through the enlarged set of contracted occurrences is collapsed by
the composed vertex map.  The two cases are: a step through an occurrence
already contracted, where the previous fibre equation applies; and a step
through the newly contracted occurrence, where `sourceVertexMap` collapses the
two ends because the corresponding occurrence downstairs lies over the
occurrence being contracted. -/
theorem sourceVertexMapAt_comp_eq_of_reach {x y : s.data.SourceVertex}
    (h : ReachThroughSet s (nextContracted sc edge) x y) :
    sourceVertexMapAt m.data edge hOne (sc.vertexMap x)
      = sourceVertexMapAt m.data edge hOne (sc.vertexMap y) := by
  induction h with
  | rel u v huv =>
      obtain ⟨e, hmem, hfst, hsnd⟩ := huv
      rcases (mem_nextContracted_iff sc edge e.1.1).mp hmem with hnew | hold
      · have h₁ : e.1.1 ∉ sc.contracted := by
          rw [hnew]; exact preimageEdge_notMem sc edge
        have h₃ : (sc.edgeMap ⟨e, h₁⟩).1.1 = edge :=
          (edgeMap_fst_eq_iff sc edge ⟨e, h₁⟩).mpr hnew
        have key := sourceVertexMapAt_sourceEnds_eq_of_contracted m.data edge hOne
          (sc.edgeMap ⟨e, h₁⟩) h₃
        rw [sc.sourceEnds_edgeMap ⟨e, h₁⟩] at key
        rw [← hfst, ← hsnd]
        exact key
      · have hreach : ReachThroughSet s sc.contracted u v :=
          StepThroughSet.reach ⟨e, hold, hfst, hsnd⟩
        rw [(sc.vertexMap_eq_iff u v).mpr hreach]
  | refl u => rfl
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-! ### Conjunct (5), the substantive direction

This is the step that does not compose on its own.  A walk downstairs through
the newly contracted occurrence of the *intermediate* target has to be pulled
back to a walk upstairs through occurrences of the *starting* target, and the
pullback uses every other conjunct: surjectivity of the composed occurrence map
(to find the occurrence upstairs), ordered endpoint compatibility (to know its
ends), surjectivity of the composed vertex map (to split a transitivity step),
and the previous fibre equation (to connect the ends to the given vertices). -/
theorem reach_nextContracted_of_reachThroughContracted {p q : m.data.SourceVertex}
    (h : ReachThroughContracted m.data edge p q) :
    ∀ x y : s.data.SourceVertex, sc.vertexMap x = p → sc.vertexMap y = q →
      ReachThroughSet s (nextContracted sc edge) x y := by
  induction h with
  | rel p q hpq =>
      obtain ⟨e', he', hfst, hsnd⟩ := hpq
      intro x y hx hy
      have hover : (sc.edgeMap.symm e').1.1.1 = preimageEdge sc edge := by
        refine (edgeMap_fst_eq_iff sc edge (sc.edgeMap.symm e')).mp ?_
        rw [Equiv.apply_symm_apply]
        exact he'
      have hends : m.data.sourceEnds e'
          = (sc.vertexMap (s.data.sourceEnds (sc.edgeMap.symm e').1).1,
            sc.vertexMap (s.data.sourceEnds (sc.edgeMap.symm e').1).2) := by
        have hraw := sc.sourceEnds_edgeMap (sc.edgeMap.symm e')
        rwa [Equiv.apply_symm_apply] at hraw
      have hp : sc.vertexMap (s.data.sourceEnds (sc.edgeMap.symm e').1).1 = p := by
        rw [← hfst, hends]
      have hq : sc.vertexMap (s.data.sourceEnds (sc.edgeMap.symm e').1).2 = q := by
        rw [← hsnd, hends]
      have hstep : StepThroughSet s (nextContracted sc edge)
          (s.data.sourceEnds (sc.edgeMap.symm e').1).1
          (s.data.sourceEnds (sc.edgeMap.symm e').1).2 := by
        refine ⟨(sc.edgeMap.symm e').1, ?_, rfl, rfl⟩
        rw [hover]
        exact mem_nextContracted_self sc edge
      have hleft : ReachThroughSet s (nextContracted sc edge) x
          (s.data.sourceEnds (sc.edgeMap.symm e').1).1 :=
        ((sc.vertexMap_eq_iff _ _).mp (hx.trans hp.symm)).mono (subset_nextContracted sc edge)
      have hright : ReachThroughSet s (nextContracted sc edge)
          (s.data.sourceEnds (sc.edgeMap.symm e').1).2 y :=
        ((sc.vertexMap_eq_iff _ _).mp (hq.trans hy.symm)).mono (subset_nextContracted sc edge)
      exact hleft.trans (hstep.reach.trans hright)
  | refl p =>
      intro x y hx hy
      exact ((sc.vertexMap_eq_iff x y).mp (hx.trans hy.symm)).mono
        (subset_nextContracted sc edge)
  | symm p q _ ih =>
      intro x y hx hy
      exact (ih y x hy hx).symm
  | trans p q r _ _ ihFirst ihSecond =>
      intro x z hx hz
      obtain ⟨y, hy⟩ := sc.vertexMap_surjective q
      exact (ihFirst x y hx hy).trans (ihSecond y z hy hz)

/-- **Conjunct (5) for the composed step.** -/
theorem next_vertexMap_eq_iff (x y : s.data.SourceVertex) :
    sourceVertexMapAt m.data edge hOne (sc.vertexMap x)
        = sourceVertexMapAt m.data edge hOne (sc.vertexMap y) ↔
      ReachThroughSet s (nextContracted sc edge) x y := by
  constructor
  · intro h
    exact reach_nextContracted_of_reachThroughContracted sc edge
      ((sourceVertexMapAt_eq_iff m.data edge hOne _ _).mp h) x y rfl rfl
  · exact fun h => sourceVertexMapAt_comp_eq_of_reach sc edge hOne h

/-! ### The inductive step, assembled -/

/-- One more contraction, as **data**: a `FullCorrespondence` to the
intermediate stage and one contraction of that stage compose to a
`FullCorrespondence` to the contracted stage. -/
noncomputable def stepCorrespondence : FullCorrespondence s (m.contractAt edge hOne) where
  contracted := nextContracted sc edge
  vertexMap := fun x => sourceVertexMapAt m.data edge hOne (sc.vertexMap x)
  edgeMap := nextEdgeEquiv sc edge hOne
  vertexMap_surjective :=
    (sourceVertexMapAt_surjective m.data edge hOne).comp sc.vertexMap_surjective
  sourceEnds_edgeMap := sourceEnds_nextEdgeEquiv sc edge hOne
  sourceEdgeIndex_edgeMap := sourceEdgeIndex_nextEdgeEquiv sc edge hOne
  vertexMap_eq_iff := next_vertexMap_eq_iff sc edge hOne
  sourceLength_edgeMap := sourceLength_nextEdgeEquiv sc edge hOne
  targetMap := nextTargetEquiv sc edge hOne
  edgeMap_fst := edgeMap_fst_nextEdgeEquiv sc edge hOne

end OneMore

/-! ## The theorem -/

/-- **The composed source correspondence exists along any iteration**, in the
form the induction carries: the target occurrence bijection included.

One induction over `Relation.ReflTransGen` carrying all six conjuncts (plus
the target occurrence bijection) simultaneously; see the module docstring for
why the six cannot be composed separately. -/
theorem nonempty_fullCorrespondence {s t : Step.{u} degree} (h : ContractsMany s t) :
    Nonempty (FullCorrespondence s t) := by
  induction h with
  | refl => exact ⟨reflCorrespondence s⟩
  | tail _ hstep ih =>
      obtain ⟨sc⟩ := ih
      cases hstep with
      | contract edge hOne _ => exact ⟨stepCorrespondence sc edge hOne⟩

/-- **The composed source correspondence exists along any iteration.**

`ContractsMany` is `Relation.ReflTransGen` of a `Prop`-valued relation, so the
conclusion can only be `Prop`-valued; the two constructions it is assembled
from, `reflCorrespondence` and `stepCorrespondence`, are `Type`-valued. -/
theorem nonempty_sourceCorrespondence {s t : Step.{u} degree} (h : ContractsMany s t) :
    Nonempty (SourceCorrespondence s t) :=
  (nonempty_fullCorrespondence h).map FullCorrespondence.toSourceCorrespondence

/-! ## The zero-set identification

`realization.sourceZeroSet` is a set of **slots** of the quotient source.  The
dilation equation `sourceEdgeIndex e * sourceLength e = targetLength e.1.1`
together with `GluingDatum.sourceEdgeIndex_pos` says a source occurrence has
length zero exactly when the target occurrence under it does, so the zero set of
the source is exactly the set of slots lying over zero-length target
occurrences.

This is the hinge between conjunct (5) and the degenerate subdivision of the
quotient source: for `Z` the set of zero-length target occurrences,
`StepThroughSet s Z` — the relation whose equivalence closure
`ReachThroughSet s Z` the fibre equation computes — is literally "joined by a
source occurrence of length zero", which is the relation whose classes the
union-find fold `compFold` collapses. -/

section ZeroSet

variable {target : CFGraph.{u}} {data : GluingDatum target degree}

/-- A source occurrence has length zero exactly when the target occurrence
under it does.  (A local copy of the statement proved in
`LocalCases.ClosedFaceRealization`, which `Infrastructure` does not import.) -/
theorem sourceLength_eq_zero_iff_local
    (realization : data.NonnegativeIntegralRealization) (e : data.SourceEdge) :
    realization.sourceLength e = 0 ↔ realization.targetLength e.1.1 = 0 := by
  constructor
  · intro h
    rw [← realization.dilation_length e, h, Nat.mul_zero]
  · intro h
    have hdil := realization.dilation_length e
    rw [h] at hdil
    rcases Nat.mul_eq_zero.mp hdil with hidx | hlen
    · exact absurd hidx (Nat.ne_of_gt (data.sourceEdgeIndex_pos e))
    · exact hlen

/-- A slot of the quotient source is a zero slot exactly when it lies over a
zero-length target occurrence. -/
theorem mem_sourceZeroSet_iff_targetLength_eq_zero
    (realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    slot ∈ realization.sourceZeroSet ↔
      realization.targetLength (realization.sourceEdgeAt slot).1.1 = 0 := by
  rw [realization.mem_sourceZeroSet slot]
  exact sourceLength_eq_zero_iff_local realization _

/-- **The zero-set identification.**  Given the set `Z` of zero-length target
occurrences, the zero set of the quotient source is exactly the set of slots of
the source occurrences lying over a member of `Z`. -/
theorem sourceZeroSet_eq_filter (realization : data.NonnegativeIntegralRealization)
    (Z : Finset target.edges)
    (hZ : ∀ f : target.edges, f ∈ Z ↔ realization.targetLength f = 0) :
    realization.sourceZeroSet
      = Finset.univ.filter fun slot => (realization.sourceEdgeAt slot).1.1 ∈ Z := by
  ext slot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_sourceZeroSet_iff_targetLength_eq_zero, hZ]

end ZeroSet

/-- The `Step` form of the zero-set identification. -/
theorem step_mem_sourceZeroSet_iff (s : Step.{u} degree)
    (slot : Fin s.data.sourceGraph.edges.card) :
    slot ∈ s.realization.sourceZeroSet ↔
      s.realization.targetLength (s.realization.sourceEdgeAt slot).1.1 = 0 :=
  mem_sourceZeroSet_iff_targetLength_eq_zero s.realization slot

/-- **The hinge between conjunct (5) and the zero-length fold.**  For `Z` the set of
zero-length target occurrences of a stage, a step of the walk relation carried
by `SourceCorrespondence` is exactly a step along a source occurrence of length
zero. -/
theorem stepThroughSet_iff_sourceLength_eq_zero (s : Step.{u} degree)
    (Z : Finset s.target.edges)
    (hZ : ∀ f : s.target.edges, f ∈ Z ↔ s.realization.targetLength f = 0)
    (x y : s.data.SourceVertex) :
    StepThroughSet s Z x y ↔
      ∃ e : s.data.SourceEdge, s.realization.sourceLength e = 0 ∧
        (s.data.sourceEnds e).1 = x ∧ (s.data.sourceEnds e).2 = y := by
  constructor
  · rintro ⟨e, hmem, hfst, hsnd⟩
    exact ⟨e, (sourceLength_eq_zero_iff_local s.realization e).mpr ((hZ _).mp hmem),
      hfst, hsnd⟩
  · rintro ⟨e, hlen, hfst, hsnd⟩
    exact ⟨e, (hZ _).mpr ((sourceLength_eq_zero_iff_local s.realization e).mp hlen),
      hfst, hsnd⟩

end IteratedContractionSource

end DraismaVargas.Infrastructure
