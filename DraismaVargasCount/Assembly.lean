module

public import DraismaVargasCount.CaterpillarAllMembers
public import DraismaVargasCount.StarSupplyAssembly
public import DraismaVargasCount.CensusAssembly
public import DraismaVargasCount.ValencyTwoPairing
public import DraismaVargasCount.ValencyFourRealisation
public import DraismaVargasCount.SimpleWallSupply
public import DraismaVargasCount.PencilTransportProducer

@[expose] public section

/-!
# The genus-six odd-subdivision witness, assembled

Every connected graph of genus six has a regular subdivision of odd order carrying a divisor of
degree four and rank at least one (`DraismaVargas.Count.genusSix_witness`). This module is the top
of that proof. It names the five results the proof combines and composes them; everything else
lives in the modules they come from.

The argument is the mod-2 form of the count of tropical morphisms to trees of Draisma and Vargas:

* J. Draisma and A. Vargas, *Catalan-many tropical morphisms to trees; Part I: Constructions*,
  arXiv:1909.12924;
* A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space and a count*,
  arXiv:2609.09109.

A *core* is a finite multigraph with labelled edges, its *slots*; a connected cubic core of genus
six has ten vertices and fifteen slots. A *request* `y` assigns a rational length to every slot.
The *fibre* over `y` is the finite set of isomorphism classes of full-dimensional tropical
morphisms of degree four from the metric graph `(core, y)` to metric trees
(`GeometricFibre core y 4`); a class is *open* when every edge of its tree has positive length.
Part II shows that over a general metric graph of genus six the open classes, counted with
multiplicity, number the Catalan number `C₃ = 5`. Only the parity is needed here:
`GeometricFibre.openOddCount core y 4`, the number of open classes of odd multiplicity, is odd.
The proof has five steps.

1. **Base count** (`Assembly.baseCount_genusSix`). Over the caterpillar of loops
   (`FibreCaterpillar.catCore 2`), at every positive request, there are exactly five open classes
   and every member has multiplicity one: every member comes from a ballot sequence
   (`CaterpillarAllMembers`; Part II, `prop-divisors-on-chain`). So the open odd count there is
   `5` (`Assembly.openOddCount_caterpillar`), which is odd.
2. **Trivalent walls** (`Assembly.trivalentWalls_genusSix`). Over one core, any two positive
   general requests are joined by segments that cross the walls of the fibre one at a time, and
   the parity of the open odd count survives every such wall. At a wall the classes that change
   openness are the classes of the stars of its limits, and every star has an even number of
   classes of odd multiplicity. This is proved separately for each of the ten wall types of
   Part I (`StarSupplyAssembly.inConeSupplySimple_genusSix`).
3. **Type changes** (`Assembly.typeChanges_genusSix`). Across every Whitehead move between cores
   there are positive general requests on the two sides whose open odd counts have the same
   parity. As the moved slot shrinks to length zero the classes of both sides specialise to
   common limits, and at every limit they correspond bijectively
   (`FacetCensus.typeChangeSupplyPositive_of_metricCensus`). The correspondence is proved
   separately for each valency of the merged vertex of the limit tree: two
   (`ValencyTwoPairing.v2ClauseSupply`), three (`CensusAssembly.v3Clause_of_resolved`) or four
   (`ValencyFourRealisation.v4ClauseSupply_genusSix`), dispatched by
   `CensusAssembly.stepCensus_of_supplies`.
4. **Propagation** (`Assembly.c34_genusSix`). Whitehead moves connect any two connected cubic
   cores of genus six, up to relabelling (`CoreOfDarts.exists_chain`). Steps 2 and 3 therefore
   carry the parity of step 1 to every core and every positive general request
   (`SimpleWallSupply.c34_of_base_positive`). The result is `CountSchedule.C34 2`: over every
   connected cubic core of genus six, at every positive general request, the open odd count is
   odd.
5. **Endgame** (`DraismaVargas.Count.genusSix_witness`). Up to reductions that preserve
   Brill--Noether existence on every regular subdivision, a connected genus-six graph `H` is a
   specialisation of a connected cubic core: the request carries the lengths of `H` on the slots
   it keeps and zero on the slots it contracts. By `CountSchedule.C34 2` and a limit argument the
   fibre over that request has a closed class of odd multiplicity. The pencil of such a class
   descends to a regular subdivision of `H` of odd order, as a divisor of degree four and rank at
   least one (`CorePencilCoverProducer.witness_of_c34_and_markerFreePencilCover`, with the
   descent `PencilTransportProducer.markerFreePencilCoverSupply`).
-/

namespace DraismaVargas.Count.Assembly

open DraismaVargas.Count.FibreCaterpillar (catCore)

/-! ## 1.  The base count -/

/-- **Step 1: the base count.** Over the genus-six caterpillar of loops, at every positive
request, the fibre has exactly five open classes, and every member has multiplicity one. -/
theorem baseCount_genusSix {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    Nat.card {c : GeometricFibre (catCore 2) request (2 + 2) // c.Open} = 5 ∧
      ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.absMult = 1 :=
  ⟨CaterpillarAllMembers.card_open_genusSix hRequest,
    CaterpillarAllMembers.absMult_eq_one_genusSix request⟩

/-- **The base count, mod 2.** Every class over the caterpillar has multiplicity one, hence odd
multiplicity, so the open odd count is the number of open classes: five. -/
theorem openOddCount_caterpillar {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    GeometricFibre.openOddCount (catCore 2) request (2 + 2) = 5 := by
  obtain ⟨hCard, hMult⟩ := baseCount_genusSix hRequest
  have hOdd (c : GeometricFibre (catCore 2) request (2 + 2)) : c.IsOdd := by
    obtain ⟨mem, rfl⟩ := GeometricFibre.cls_surjective c
    exact (GeometricFibre.isOdd_cls_iff mem).mpr
      (FibreMember.hasOddMult_of_absMult_eq_one (hMult mem))
  rw [GeometricFibre.openOddCount, ← hCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c ↦ and_iff_left (hOdd c))

/-! ## 2.  The trivalent walls -/

/-- **Step 2: the trivalent walls.** Over every core with ten vertices and fifteen slots, crossing
a wall on a segment between positive requests preserves the parity of the open odd count, when
the wall is the only one on the segment and has codimension one
(`SimpleWallSupply.InConeSupplySimple`, in degree four). -/
theorem trivalentWalls_genusSix :
    SimpleWallSupply.InConeSupplySimple (2 + 2) (4 * 2 + 2) (6 * 2 + 3) :=
  StarSupplyAssembly.inConeSupplySimple_genusSix

/-! ## 3.  The type changes -/

/-- **Step 3: the type changes.** Across every Whitehead move between genus-six cores there are
positive general requests on the two sides whose open odd counts have the same parity
(`SimpleWallSupply.TypeChangeSupplyPositive`, in degree four). -/
theorem typeChanges_genusSix :
    SimpleWallSupply.TypeChangeSupplyPositive (2 + 2) (4 * 2 + 2) (6 * 2 + 3) :=
  FacetCensus.typeChangeSupplyPositive_of_metricCensus fun _ _ hStep ↦
    CensusAssembly.stepCensus_of_supplies (ValencyTwoPairing.v2ClauseSupply (by norm_num)
      (by norm_num)) ValencyFourRealisation.v4ClauseSupply_genusSix (by norm_num) (by norm_num)
      hStep

/-! ## 4.  Propagation -/

/-- **Step 4: propagation.** Over every connected cubic core of genus six, at every positive
general request, the number of open classes of odd multiplicity is odd. The base count at one
positive general request over the caterpillar is carried to every core by the trivalent walls
and the type changes. -/
theorem c34_genusSix : CountSchedule.C34 2 := by
  intro n p core hCubic hConnected hGenus y hPositive hGeneral
  obtain ⟨rfl, rfl⟩ := StepSupplyGenusSix.index_of_genusSix hCubic hGenus
  obtain ⟨request, hRequest⟩ := SimpleWallSupply.exists_positiveGeneral (catCore 2) (2 + 2)
  refine SimpleWallSupply.c34_of_base_positive trivalentWalls_genusSix typeChanges_genusSix
    (by norm_num) StepSupplyGenusSix.catCubicCore request hRequest.1 hRequest.2 ?_ core hCubic
    hConnected y hPositive hGeneral
  rw [StepSupplyGenusSix.catCubicCore_core, openOddCount_caterpillar hRequest.1]
  decide

end DraismaVargas.Count.Assembly

namespace DraismaVargas.Count

universe u

/-- **The genus-six odd-subdivision witness** (step 5, the endgame). Every connected graph of
genus six has a regular subdivision of odd order carrying a divisor of degree four and rank at
least one. It follows from `Assembly.c34_genusSix` and the descent of pencils from the fibre to
the subdivisions of the graph. -/
theorem genusSix_witness :
    ∀ H : CFGraph.{u}, graph_connected H → genus H = 6 →
      ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
        Utilities.BNExists (Utilities.Gonality.regularSubdivision H N hN) 1 4 :=
  CorePencilCoverProducer.witness_of_c34_and_markerFreePencilCover Assembly.c34_genusSix
    PencilTransportProducer.markerFreePencilCoverSupply

end DraismaVargas.Count
