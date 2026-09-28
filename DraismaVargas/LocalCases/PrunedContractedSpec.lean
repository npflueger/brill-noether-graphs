import DraismaVargas.LocalCases.PrunedRealizationSpec
import Utilities.Subdivision.SubdivisionConnectivity
import Utilities.Subdivision.PathSplitRefinement

/-!
# The pruned contracted spec

At a terminal face the stable model is matched not with the whole contracted
quotient source but with the contracted source with its **pendant trees
deleted**.  This file builds that object beside
`SourceContractionTopology.contractedSpec`, without changing anything about
`degSpec`, `rep`, `contractedSpec`, `ContractedGluing` or `TerminalGluing`.

* `KeptSlot` — a positive slot of `topology.degSpec` whose source occurrence is
  not dangling.
* `KeptClass` — a contraction class containing a quotient-source vertex of
  positive non-dangling valency.
* `prunedSpec` — `contractedSpec` restricted to the kept classes and the kept
  slots, reindexed by `Finset.equivFin` exactly as `contractedSpec` itself is
  reindexed by `Fintype.equivFin`.
* `prunedSpec_laplacianEquiv` — its identification with the subgraph of
  `contractedSpec.graph` induced on the kept classes and the interiors of the
  kept slots.
* `bnExists_prunedSpec` — the pendant-deletion pushforward
  (`Infrastructure.PendantDeletion.bnExists_induce_of_genus_eq`), specialised.
* `genus_prunedSpec_eq_genus_sourceGraph` — the Euler transport.

## Where the proofs live

Every construction of §§1–5 below depends on the cleared face only through the
pair `(candidate.datum, face.realization)`, so it is carried out once, on that
pair alone, in `DraismaVargas.LocalCases.PrunedRealizationSpec`, which mentions
no cleared face.  §§1–5 here are **thin wrappers**: the adapter
`toSourceTopology` turns a `SourceContractionTopology face` into the
`PrunedRealizationSpec.SourceTopology candidate.datum face.realization` it
literally is (same two fields), and each declaration delegates.  Both sides
are definitionally equal — `SourceTopology` is a `Prop`, so proof irrelevance
makes `topology.degSpec` and `topology.toSourceTopology.degSpec` the same
term — which is why the wrapper bodies are one line each.

One definition is **deliberately not** a wrapper: `prunedSpec` keeps its own
`PendantDeletion.Spec.restrict` body, because `RefinementCore`
(`prunedSpec_core_tail`, `prunedSpec_core_head`) rewrites with `prunedSpec`'s
*equation lemma* and then with
`PendantDeletion.Spec.restrict_core_tail`/`_head`.  Routing it through the
generic definition makes that first rewrite produce
`PrunedRealizationSpec.prunedSpec …` and the second one fails to match.  The
two bodies are definitionally equal, so every generic lemma still applies.

§5b and §6 are proved here in full: §5b because
`RefinementPresentation`/`PackedSpec` are not available to
`PrunedRealizationSpec`, §6 because it is a non-vacuity witness for this file's
pushforward.

## Two named hypotheses, and why they are named

`prunedSpec_laplacianEquiv` and `bnExists_prunedSpec` do **not** hold with no
input beyond `SourceContractionTopology`.  Two facts about dangling
occurrences are needed; both are isolated here as named propositions rather
than smuggled into a definition, and both are proved in
`PrunedContractedSpecResidues`.

* `PendantSeparated` — *a dangling positive slot has an endpoint class that
  pruning discards*.  This is what makes the restricted spec the induced
  subgraph: a dropped slot survives the induction exactly when it has length
  one and two kept endpoint classes.  The converse direction is free and is
  proved here (`keptClass_tail_of_keptSlot`, `keptClass_head_of_keptSlot`):
  a *non*-dangling slot always has two kept endpoint classes.
* the count `classCard + keptSlotCard = keptClassCard + slotCard` — equivalently
  *the number of discarded classes equals the number of dangling positive
  slots*.  `genus_prunedSpec_eq_genus_sourceGraph_iff` proves this is
  **equivalent** to the genus identity, so nothing is lost by naming it: it is
  the genus identity, counted.

Both come from the same structural fact — the far side of a dangling
occurrence is a pendant tree, all of whose vertices have non-dangling valency
zero and whose classes never escape it — which is a theorem about
`DanglingSide`, not about this construction.

## Layering

`Candidate.ClearedFace.InputRefinement` targets `prunedSpec`, so this module must sit
**strictly below** `ClosedEndpoint`.  It therefore cannot import
`InputRefinementData` or `RefinementCore`, which import `ClosedEndpoint`.  In
particular the genus of `contractedSpec` is proved here directly as
`genus_contractedSpec_eq` (a six-line proof from the two fields of
`SourceContractionTopology`), and the non-vacuity instance of §6 is built
explicitly.  `PrunedRealizationSpec` imports strictly less than this file.
-/

namespace DraismaVargas.LocalCases.BalancedGlobal.Candidate.ClearedFace.SourceContractionTopology

open Utilities
open Utilities.Certificate
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.TerminalContraction
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*}
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {coordinates : coordinate → ℚ}
  {face : ClearedFace candidate presentation coordinates}

/-! ## 0.  The adapter

`SourceContractionTopology face` and
`PrunedRealizationSpec.SourceTopology candidate.datum face.realization` have
the same two fields, so the first yields the second.  Both are `Prop`s, so
proof irrelevance makes the round trip definitional: `topology.degSpec` and
`topology.toSourceTopology.degSpec` are the *same term*, and every wrapper
below typechecks against the statement it always had. -/

/-- A cleared-face contraction topology **is** a `SourceTopology` of its own
nonnegative integral realization. -/
theorem toSourceTopology (topology : SourceContractionTopology face) :
    PrunedRealizationSpec.SourceTopology candidate.datum face.realization :=
  ⟨topology.forest, topology.notLoopy⟩

/-! ## 1.  Classes, kept slots and kept classes -/

/-- The contraction class of a core index of the quotient source. -/
noncomputable def classOfCore (topology : SourceContractionTopology face)
    (v : Fin (Fintype.card candidate.datum.sourceGraph.V)) : topology.degSpec.Class :=
  PrunedRealizationSpec.classOfCore topology.toSourceTopology v

/-- The contraction class of a quotient-source vertex. -/
noncomputable def classOf (topology : SourceContractionTopology face)
    (v : candidate.datum.SourceVertex) : topology.degSpec.Class :=
  classOfCore topology (vertexIndex candidate.datum v)

/-- **A positive slot that survives pruning**: its source occurrence is not
dangling. -/
def KeptSlot (topology : SourceContractionTopology face)
    (e : topology.degSpec.PositiveSlot) : Prop :=
  PrunedRealizationSpec.KeptSlot topology.toSourceTopology e

/-- **A contraction class that survives pruning**: it contains a
quotient-source vertex meeting a surviving occurrence. -/
def KeptClass (topology : SourceContractionTopology face)
    (c : topology.degSpec.Class) : Prop :=
  PrunedRealizationSpec.KeptClass topology.toSourceTopology c

/-- The kept slots, as a subset of the slot indices of `contractedSpec`. -/
noncomputable def keptSlots (topology : SourceContractionTopology face) :
    Finset (Fin topology.degSpec.slotCard) :=
  PrunedRealizationSpec.keptSlots topology.toSourceTopology

/-- The kept classes, as a subset of the core indices of `contractedSpec`. -/
noncomputable def keptClasses (topology : SourceContractionTopology face) :
    Finset (Fin topology.degSpec.classCard) :=
  PrunedRealizationSpec.keptClasses topology.toSourceTopology

@[simp] theorem mem_keptSlots (topology : SourceContractionTopology face)
    (e' : Fin topology.degSpec.slotCard) :
    e' ∈ keptSlots topology ↔ KeptSlot topology (topology.degSpec.slotIndex.symm e') :=
  PrunedRealizationSpec.mem_keptSlots topology.toSourceTopology e'

@[simp] theorem mem_keptClasses (topology : SourceContractionTopology face)
    (c' : Fin topology.degSpec.classCard) :
    c' ∈ keptClasses topology ↔
      KeptClass topology (topology.degSpec.classIndex.symm c') :=
  PrunedRealizationSpec.mem_keptClasses topology.toSourceTopology c'

theorem mem_keptClasses_classIndex (topology : SourceContractionTopology face)
    {c : topology.degSpec.Class} (hc : KeptClass topology c) :
    topology.degSpec.classIndex c ∈ keptClasses topology :=
  PrunedRealizationSpec.mem_keptClasses_classIndex topology.toSourceTopology hc

/-! ## 2.  A non-dangling slot has two kept endpoint classes -/

/-- A source occurrence meeting a vertex, not dangling, forces positive
non-dangling valency there. -/
theorem nonDanglingValency_pos_of_incident
    {edge : candidate.datum.SourceEdge} {v : candidate.datum.SourceVertex}
    (hDangling : ¬ IsDangling candidate.datum edge)
    (hIncident : Incident candidate.datum edge v) :
    0 < nonDanglingValency candidate.datum v :=
  PrunedRealizationSpec.nonDanglingValency_pos_of_incident hDangling hIncident

theorem classOf_sourceEnds_fst (topology : SourceContractionTopology face)
    (slot : Fin candidate.datum.sourceGraph.edges.card) :
    classOf topology (candidate.datum.sourceEnds (face.realization.sourceEdgeAt slot)).1 =
      classOfCore topology (topology.degSpec.core.tail slot) :=
  PrunedRealizationSpec.classOf_sourceEnds_fst topology.toSourceTopology slot

theorem classOf_sourceEnds_snd (topology : SourceContractionTopology face)
    (slot : Fin candidate.datum.sourceGraph.edges.card) :
    classOf topology (candidate.datum.sourceEnds (face.realization.sourceEdgeAt slot)).2 =
      classOfCore topology (topology.degSpec.core.head slot) :=
  PrunedRealizationSpec.classOf_sourceEnds_snd topology.toSourceTopology slot

/-- **Free half of the separation.**  The tail class of a kept slot is kept. -/
theorem keptClass_tail_of_keptSlot (topology : SourceContractionTopology face)
    {e : topology.degSpec.PositiveSlot} (he : KeptSlot topology e) :
    KeptClass topology (classOfCore topology (topology.degSpec.core.tail e.val)) :=
  PrunedRealizationSpec.keptClass_tail_of_keptSlot topology.toSourceTopology he

/-- and so is the head class. -/
theorem keptClass_head_of_keptSlot (topology : SourceContractionTopology face)
    {e : topology.degSpec.PositiveSlot} (he : KeptSlot topology e) :
    KeptClass topology (classOfCore topology (topology.degSpec.core.head e.val)) :=
  PrunedRealizationSpec.keptClass_head_of_keptSlot topology.toSourceTopology he

/-! ## 3.  `contractedSpec` endpoints, read as classes -/

theorem contractedSpec_tail (topology : SourceContractionTopology face)
    (e' : Fin topology.degSpec.slotCard) :
    topology.degSpec.classIndex.symm (topology.contractedSpec.core.tail e') =
      classOfCore topology
        (topology.degSpec.core.tail (topology.degSpec.slotIndex.symm e').val) :=
  PrunedRealizationSpec.contractedSpec_tail topology.toSourceTopology e'

theorem contractedSpec_head (topology : SourceContractionTopology face)
    (e' : Fin topology.degSpec.slotCard) :
    topology.degSpec.classIndex.symm (topology.contractedSpec.core.head e') =
      classOfCore topology
        (topology.degSpec.core.head (topology.degSpec.slotIndex.symm e').val) :=
  PrunedRealizationSpec.contractedSpec_head topology.toSourceTopology e'

theorem tail_mem_keptClasses (topology : SourceContractionTopology face) :
    ∀ e' ∈ keptSlots topology,
      topology.contractedSpec.core.tail e' ∈ keptClasses topology :=
  PrunedRealizationSpec.tail_mem_keptClasses topology.toSourceTopology

theorem head_mem_keptClasses (topology : SourceContractionTopology face) :
    ∀ e' ∈ keptSlots topology,
      topology.contractedSpec.core.head e' ∈ keptClasses topology :=
  PrunedRealizationSpec.head_mem_keptClasses topology.toSourceTopology

/-! ## 4.  The pruned spec -/

/-- **The pruned contracted spec.**  `contractedSpec` with the dangling
occurrences and the classes they hang from removed. -/
noncomputable def prunedSpec (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) :
    SubdivisionGraph.Spec (keptClasses topology).card (keptSlots topology).card :=
  PendantDeletion.Spec.restrict topology.contractedSpec (keptClasses topology)
    (keptSlots topology) hKept (tail_mem_keptClasses topology)
    (head_mem_keptClasses topology)

/-- **The pendant-separation receipt.**  A dangling positive slot has an
endpoint class that pruning discards.  Its converse is free
(`keptClass_tail_of_keptSlot`). -/
def PendantSeparated (topology : SourceContractionTopology face) : Prop :=
  PrunedRealizationSpec.PendantSeparated topology.toSourceTopology

theorem dropped_of_pendantSeparated (topology : SourceContractionTopology face)
    (hSep : PendantSeparated topology) :
    ∀ e' ∉ keptSlots topology, topology.contractedSpec.length e' = 1 →
      topology.contractedSpec.core.tail e' ∉ keptClasses topology ∨
        topology.contractedSpec.core.head e' ∉ keptClasses topology :=
  PrunedRealizationSpec.dropped_of_pendantSeparated topology.toSourceTopology hSep

/-- **`prunedSpec` is the induced subgraph.**  The kept vertices are the kept
classes together with the interiors of the kept slots. -/
noncomputable def prunedVertices (topology : SourceContractionTopology face) :
    Finset topology.contractedSpec.Vertex :=
  PrunedRealizationSpec.prunedVertices topology.toSourceTopology

noncomputable def prunedSpec_laplacianEquiv (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) (hSep : PendantSeparated topology) :
    LaplacianEquiv (prunedSpec topology hKept).graph
      (inducedSubgraph topology.contractedSpec.graph (prunedVertices topology)
        (PendantDeletion.Spec.keptVertices_nonempty hKept)) :=
  PrunedRealizationSpec.prunedSpec_laplacianEquiv topology.toSourceTopology hKept hSep

/-! ## 5.  Genus, and the pushforward -/

/-- The genus of `contractedSpec`, proved directly from the two fields of
`SourceContractionTopology`: this module sits below `ClosedEndpoint`. -/
theorem genus_contractedSpec_eq (topology : SourceContractionTopology face) :
    genus topology.contractedSpec.graph = genus candidate.datum.sourceGraph :=
  PrunedRealizationSpec.genus_contractedSpec_eq topology.toSourceTopology

theorem genus_contractedSpec_card (topology : SourceContractionTopology face) :
    genus topology.contractedSpec.graph =
      (topology.degSpec.slotCard : ℤ) - (topology.degSpec.classCard : ℤ) + 1 :=
  SubdivisionGraph.Spec.genus_graph _

theorem genus_prunedSpec (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) :
    genus (prunedSpec topology hKept).graph =
      ((keptSlots topology).card : ℤ) - ((keptClasses topology).card : ℤ) + 1 :=
  PrunedRealizationSpec.genus_prunedSpec topology.toSourceTopology hKept

/-- **The Euler transport, as an equivalence.**  The genus identity the
pushforward needs is *exactly* the count "discarded classes = dangling positive
slots", in subtraction-free form. -/
theorem genus_prunedSpec_eq_genus_sourceGraph_iff
    (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) :
    genus (prunedSpec topology hKept).graph = genus candidate.datum.sourceGraph ↔
      topology.degSpec.classCard + (keptSlots topology).card =
        (keptClasses topology).card + topology.degSpec.slotCard :=
  PrunedRealizationSpec.genus_prunedSpec_eq_genus_sourceGraph_iff
    topology.toSourceTopology hKept

/-- **The Euler transport.** -/
theorem genus_prunedSpec_eq_genus_sourceGraph (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty)
    (hCount : topology.degSpec.classCard + (keptSlots topology).card =
      (keptClasses topology).card + topology.degSpec.slotCard) :
    genus (prunedSpec topology hKept).graph = genus candidate.datum.sourceGraph :=
  PrunedRealizationSpec.genus_prunedSpec_eq_genus_sourceGraph
    topology.toSourceTopology hKept hCount

/-- **The pushforward, specialised.**  The pencil produced on the whole
contracted quotient source is carried to the pruned contracted spec. -/
theorem bnExists_prunedSpec (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) (hSep : PendantSeparated topology)
    (hConnected : graph_connected topology.contractedSpec.graph)
    (hGenus : genus (prunedSpec topology hKept).graph =
      genus topology.contractedSpec.graph)
    {d : ℤ} (hBN : BNExists topology.contractedSpec.graph 1 d) :
    BNExists (prunedSpec topology hKept).graph 1 d :=
  PrunedRealizationSpec.bnExists_prunedSpec topology.toSourceTopology hKept hSep
    hConnected hGenus hBN

/-- The same with the genus hypothesis replaced by the count it is equivalent
to (`genus_prunedSpec_eq_genus_sourceGraph_iff`). -/
theorem bnExists_prunedSpec_of_count (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) (hSep : PendantSeparated topology)
    (hConnected : graph_connected topology.contractedSpec.graph)
    (hCount : topology.degSpec.classCard + (keptSlots topology).card =
      (keptClasses topology).card + topology.degSpec.slotCard)
    {d : ℤ} (hBN : BNExists topology.contractedSpec.graph 1 d) :
    BNExists (prunedSpec topology hKept).graph 1 d :=
  PrunedRealizationSpec.bnExists_prunedSpec_of_count topology.toSourceTopology
    hKept hSep hConnected hCount hBN

/-! ## 5b.  Both extra hypotheses are free where the pushforward is used

`bnExists_prunedSpec` asks for connectivity of `contractedSpec.graph` and for
the genus identity. Both are free at the point of use, and the two lemmas below
are the generic form of that, stated without mentioning
`Candidate.ClearedFace.ContractedGluing` or `Candidate.ClearedFace.InputRefinement` (this
module sits below `ClosedEndpoint`).

* Connectivity: `ContractedGluing.sourceEquiv` is a `LaplacianEquiv` onto
  `realization.sourceSpec.graph`, which
  `GluingDatum.IntegralRealization.sourceSpec_connected` makes connected from
  `contracted.valid.1`.
* Genus: a `RefinementPresentation` onto `prunedSpec.graph` carries a split
  chain and a relabeling, both `LaplacianEquiv`s, so the genus of
  `prunedSpec.graph` is the genus of the presented packed spec — which is
  `genus spec.graph`, and `SourceGenusMatches` closes the loop. -/

theorem graph_connected_contractedSpec {H : CFGraph}
    (topology : SourceContractionTopology face)
    (equiv : LaplacianEquiv topology.contractedSpec.graph H)
    (hH : graph_connected H) :
    graph_connected topology.contractedSpec.graph :=
  equiv.graphConnected_iff.mpr hH

/-- **The genus hypothesis is free at the point of use.**  Any refinement
presentation of a packed spec of the quotient source's genus onto
`prunedSpec.graph` supplies it. -/
theorem genus_prunedSpec_of_refinement (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) {source : PackedSpec}
    (refinement : RefinementPresentation source (prunedSpec topology hKept).graph)
    (hSource : genus source.graph = genus candidate.datum.sourceGraph) :
    genus (prunedSpec topology hKept).graph = genus topology.contractedSpec.graph := by
  rw [refinement.relabeling.genus_eq, refinement.chain.laplacianEquiv.genus_eq, hSource,
    genus_contractedSpec_eq topology]

/-- and therefore the pushforward runs with no genus hypothesis of its own. -/
theorem bnExists_prunedSpec_of_refinement (topology : SourceContractionTopology face)
    (hKept : (keptClasses topology).Nonempty) (hSep : PendantSeparated topology)
    (hConnected : graph_connected topology.contractedSpec.graph) {source : PackedSpec}
    (refinement : RefinementPresentation source (prunedSpec topology hKept).graph)
    (hSource : genus source.graph = genus candidate.datum.sourceGraph)
    {d : ℤ} (hBN : BNExists topology.contractedSpec.graph 1 d) :
    BNExists (prunedSpec topology hKept).graph 1 d :=
  bnExists_prunedSpec topology hKept hSep hConnected
    (genus_prunedSpec_of_refinement topology hKept refinement hSource) hBN

/-! ## 6.  Non-vacuity: the theta with one grafted arm

The pushforward is inserted between `contractedSpec.graph` and
`prunedSpec.graph`, and this section gives a witness that this shape is
inhabited.  Here is the smallest one, built explicitly (see the layering
remark in the header): the theta with a pendant arm of arbitrary positive
length grafted at one of its two vertices, restricted to the theta.

`Spec.restrict` fires with all four of its hypotheses discharged by `decide`,
the genus identity holds on the nose, and the transport runs **both ways at
every rank and degree** — so a pencil on the theta at any scale is a pencil on
the theta-with-arm at that same scale, and conversely.  Because the arm is a
single slot of arbitrary length, its subdivision is a pendant path of arbitrary
length, so pendant edges and pendant paths are both covered. -/

namespace ThetaArm

open Utilities.Certificate.SubdivisionGraph

/-- The core of a theta with one arm grafted at its first vertex: three
parallel slots from vertex `0` to vertex `1`, and one arm slot from vertex `0`
to the tip `2`. -/
def core : ExplicitPotential.Core 3 4 where
  tail := ![0, 0, 0, 0]
  head := ![1, 1, 1, 2]

/-- The theta with one grafted arm, at arbitrary positive lengths. -/
def spec (lengths : Fin 4 → ℕ) (hPositive : ∀ i, 0 < lengths i) :
    SubdivisionGraph.Spec 3 4 where
  core := core
  length := lengths
  core_nonempty := by omega
  core_loopless := by decide
  length_pos := hPositive

/-- The two theta vertices. -/
def keptCore : Finset (Fin 3) := {0, 1}

/-- The three theta slots. -/
def keptArm : Finset (Fin 4) := {0, 1, 2}

theorem keptCore_card : keptCore.card = 2 := by decide

theorem keptArm_card : keptArm.card = 3 := by decide

theorem keptCore_nonempty : keptCore.Nonempty := by decide

theorem tail_mem_core : ∀ e ∈ keptArm, core.tail e ∈ keptCore := by decide

theorem head_mem_core : ∀ e ∈ keptArm, core.head e ∈ keptCore := by decide

/-- The arm slot is separated: its tip is not a kept vertex. -/
theorem dropped_core : ∀ e ∉ keptArm, core.tail e ∉ keptCore ∨ core.head e ∉ keptCore := by
  decide

theorem tail_core_eq_zero : ∀ e ∈ keptArm, core.tail e = 0 := by decide

theorem head_core_eq_one : ∀ e ∈ keptArm, core.head e = 1 := by decide

theorem core_connected : core.Connected := by
  show ∀ S : Finset (Fin 3), (∃ v w : Fin 3, v ∈ S ∧ w ∉ S) →
    ∃ edge : Fin 4,
      (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
        (core.head edge ∈ S ∧ core.tail edge ∉ S)
  decide

variable (lengths : Fin 4 → ℕ) (hPositive : ∀ i, 0 < lengths i)

theorem tail_mem : ∀ e ∈ keptArm, (spec lengths hPositive).core.tail e ∈ keptCore :=
  tail_mem_core

theorem head_mem : ∀ e ∈ keptArm, (spec lengths hPositive).core.head e ∈ keptCore :=
  head_mem_core

theorem dropped : ∀ e ∉ keptArm, (spec lengths hPositive).length e = 1 →
    (spec lengths hPositive).core.tail e ∉ keptCore ∨
      (spec lengths hPositive).core.head e ∉ keptCore :=
  fun e he _ ↦ dropped_core e he

theorem spec_core_connected : (spec lengths hPositive).core.Connected := core_connected

/-- **The theta**, as the restriction of the theta with an arm. -/
noncomputable def theta : SubdivisionGraph.Spec keptCore.card keptArm.card :=
  PendantDeletion.Spec.restrict (spec lengths hPositive) keptCore keptArm
    keptCore_nonempty (tail_mem lengths hPositive) (head_mem lengths hPositive)

theorem theta_eq :
    theta lengths hPositive =
      PendantDeletion.Spec.restrict (spec lengths hPositive) keptCore keptArm
        keptCore_nonempty (tail_mem lengths hPositive) (head_mem lengths hPositive) := rfl

/-- The restriction really is a theta: two core vertices, and all three slots
run between the same pair. -/
theorem theta_banana (e f : Fin keptArm.card) :
    (theta lengths hPositive).core.tail e = (theta lengths hPositive).core.tail f ∧
      (theta lengths hPositive).core.head e = (theta lengths hPositive).core.head f := by
  have hTail : ∀ g : Fin keptArm.card,
      PendantDeletion.Spec.keptVertexAt keptCore
        ((theta lengths hPositive).core.tail g) = 0 := by
    intro g
    rw [theta_eq, PendantDeletion.Spec.restrict_core_tail]
    exact tail_core_eq_zero _ (PendantDeletion.Spec.keptSlotAt_mem keptArm g)
  have hHead : ∀ g : Fin keptArm.card,
      PendantDeletion.Spec.keptVertexAt keptCore
        ((theta lengths hPositive).core.head g) = 1 := by
    intro g
    rw [theta_eq, PendantDeletion.Spec.restrict_core_head]
    exact head_core_eq_one _ (PendantDeletion.Spec.keptSlotAt_mem keptArm g)
  exact ⟨PendantDeletion.Spec.keptVertexAt_injective keptCore
      ((hTail e).trans (hTail f).symm),
    PendantDeletion.Spec.keptVertexAt_injective keptCore
      ((hHead e).trans (hHead f).symm)⟩

/-- Its slot lengths are the theta's three lengths. -/
theorem theta_length (e : Fin keptArm.card) :
    (theta lengths hPositive).length e =
      lengths (PendantDeletion.Spec.keptSlotAt keptArm e) := rfl

theorem genus_theta : genus (theta lengths hPositive).graph = 2 := by
  rw [theta_eq, PendantDeletion.Spec.genus_restrict, keptCore_card, keptArm_card]
  norm_num

theorem genus_spec : genus (spec lengths hPositive).graph = 2 := by
  rw [SubdivisionGraph.Spec.genus_graph]
  norm_num

theorem graph_connected_spec : graph_connected (spec lengths hPositive).graph :=
  SubdivisionGraph.Spec.graph_connected_of_coreConnected _
    (spec_core_connected lengths hPositive)

/-- **Non-vacuity.**  Brill--Noether existence transports both ways between the
theta with a grafted arm and the theta, at every rank and every degree — hence
at the pencil's own scale, whatever that scale is. -/
theorem bnExists_theta_iff (r d : ℤ) :
    BNExists (spec lengths hPositive).graph r d ↔
      BNExists (theta lengths hPositive).graph r d := by
  have hEquiv := PendantDeletion.Spec.laplacianEquiv_restrict
    keptCore_nonempty (tail_mem lengths hPositive) (head_mem lengths hPositive)
    (dropped lengths hPositive)
  have hGenus :
      genus (inducedSubgraph (spec lengths hPositive).graph
        (PendantDeletion.Spec.keptVertices (spec lengths hPositive) keptCore keptArm)
        (PendantDeletion.Spec.keptVertices_nonempty keptCore_nonempty)) =
      genus (spec lengths hPositive).graph := by
    rw [hEquiv.genus_eq, ← theta_eq, genus_theta, genus_spec]
  rw [theta_eq]
  exact (PendantDeletion.bnExists_induce_iff_of_genus_eq _ _ _
    (graph_connected_spec lengths hPositive) hGenus r d).trans
    (hEquiv.bnExists_iff r d).symm

/-- The direction the terminal identification uses: a pencil on the theta with
a grafted arm is a pencil on the theta. -/
theorem bnExists_theta_of_arm {r d : ℤ}
    (h : BNExists (spec lengths hPositive).graph r d) :
    BNExists (theta lengths hPositive).graph r d :=
  (bnExists_theta_iff lengths hPositive r d).mp h

/-- and the converse, which is the retraction. -/
theorem bnExists_arm_of_theta {r d : ℤ}
    (h : BNExists (theta lengths hPositive).graph r d) :
    BNExists (spec lengths hPositive).graph r d :=
  (bnExists_theta_iff lengths hPositive r d).mpr h

end ThetaArm

end DraismaVargas.LocalCases.BalancedGlobal.Candidate.ClearedFace.SourceContractionTopology
