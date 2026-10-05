module

public import DraismaVargas.LocalCases.ClassInjectivity
public import DraismaVargas.LocalCases.WallProgress

@[expose] public section

/-!
# Pruning preserves connectivity inside a contracted source fibre

Source: Draisma–Vargas Part I, arXiv:1909.12924, the non-dangling union lemma
(`lemma-class-union`) and the discussion of the non-dangling subgraph above
`A_0` (subsection `subsection-the-graph-GqA0`, up to `lemma-ndval-of-GqA0`).
Before using the forest Euler count, one needs the non-dangling part of a
contracted fibre to be connected.

We prove that actual source vertices meeting surviving occurrences and joined
by contracted source occurrences can also be joined using only surviving
contracted occurrences.  No stable-path equivalence or connectivity hypothesis
is assumed.  This connectivity statement does not itself need the forest count.

The proof reuses `ClassInjectivity.nonDanglingValency_eq_zero_of_mem_side`:
every vertex on the genus-zero side of a dangling cut has no survivor.  Take
the last departure from the first vertex of a walk.  If that first occurrence
dangled, one endpoint of the entire walk would lie on its genus-zero side.
Thus that occurrence survives.  Remove the departed vertex and induct on the
finite set of allowed vertices.  This deletes dangling detours without
assuming the original walk was already simple or pruned.
-/

namespace DraismaVargas.LocalCases.PrunedContractionFibre

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre
open W4StableSource StableLocalProperties WallDegeneration ClassInjectivity

variable {target : CFGraph} {degree : ℕ}

/-- An unoriented step through an actual occurrence over the contracted
target occurrence. -/
def FibreStep (data : GluingDatum target degree) (contracted : target.edges)
    (first second : data.SourceVertex) : Prop :=
  ∃ edge : data.SourceEdge, edge.1.1 = contracted ∧
    (data.sourceEnds edge = (first, second) ∨ data.sourceEnds edge = (second, first))

theorem FibreStep.symm {data : GluingDatum target degree} {contracted : target.edges}
    {first second : data.SourceVertex} (h : FibreStep data contracted first second) :
    FibreStep data contracted second first := by
  obtain ⟨edge, hTarget, hEnds⟩ := h
  exact ⟨edge, hTarget, hEnds.symm⟩

theorem FibreStep.num_edges_pos {data : GluingDatum target degree} {contracted : target.edges}
    {first second : data.SourceVertex} (h : FibreStep data contracted first second) :
    0 < num_edges data.sourceGraph first second := by
  obtain ⟨edge, _, hEnds⟩ := h
  exact num_edges_pos_of_sourceEnds data hEnds

theorem FibreStep.reachThroughContracted {data : GluingDatum target degree}
    {contracted : target.edges} {first second : data.SourceVertex}
    (h : FibreStep data contracted first second) :
    ReachThroughContracted data contracted first second := by
  obtain ⟨edge, hTarget, hEnds | hEnds⟩ := h
  · exact ContractedStep.reach ⟨edge, hTarget, congrArg Prod.fst hEnds,
      congrArg Prod.snd hEnds⟩
  · exact (ContractedStep.reach ⟨edge, hTarget, congrArg Prod.fst hEnds,
      congrArg Prod.snd hEnds⟩).symm

/-- The same occurrence-safe step after pruning. -/
def SurvivingFibreStep (data : GluingDatum target degree) (contracted : target.edges)
    (first second : data.SourceVertex) : Prop :=
  ∃ edge : data.SourceEdge, edge.1.1 = contracted ∧ ¬ IsDangling data edge ∧
    (data.sourceEnds edge = (first, second) ∨ data.sourceEnds edge = (second, first))

theorem SurvivingFibreStep.fibreStep {data : GluingDatum target degree}
    {contracted : target.edges} {first second : data.SourceVertex}
    (h : SurvivingFibreStep data contracted first second) :
    FibreStep data contracted first second := by
  obtain ⟨edge, hTarget, _, hEnds⟩ := h
  exact ⟨edge, hTarget, hEnds⟩

/-- Read the established full-fibre relation as an unoriented walk of actual
contracted occurrences. -/
theorem reflTransGen_fibreStep_of_reachThroughContracted
    (data : GluingDatum target degree) (contracted : target.edges)
    {first second : data.SourceVertex}
    (h : ReachThroughContracted data contracted first second) :
    Relation.ReflTransGen (FibreStep data contracted) first second := by
  induction h with
  | rel first second hStep =>
    obtain ⟨edge, hTarget, hFirst, hSecond⟩ := hStep
    exact Relation.ReflTransGen.single
      ⟨edge, hTarget, Or.inl (Prod.ext hFirst hSecond)⟩
  | refl => exact Relation.ReflTransGen.refl
  | symm _ _ _ ih => exact reflTransGen_symm FibreStep.symm ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Finite-set form of pruning a walk.  Its endpoints meet survivors; every
chosen step in the resulting walk is an actual surviving contracted
occurrence. -/
theorem surviving_walk_of_walk_within (data : GluingDatum target degree)
    (contracted : target.edges) :
    ∀ vertices : Finset data.SourceVertex, ∀ first second : data.SourceVertex,
      first ∈ vertices → second ∈ vertices →
      nonDanglingValency data first ≠ 0 → nonDanglingValency data second ≠ 0 →
      Relation.ReflTransGen (fun x y ↦ FibreStep data contracted x y ∧
        x ∈ vertices ∧ y ∈ vertices) first second →
      Relation.ReflTransGen (SurvivingFibreStep data contracted) first second := by
  classical
  intro vertices
  refine Finset.strongInductionOn vertices ?_
  · intro vertices ih first second hFirstMem hSecondMem hFirstActive hSecondActive hWalk
    by_cases hEq : first = second
    · subst second
      exact Relation.ReflTransGen.refl
    · obtain ⟨next, hStep, hAvoid⟩ := exists_step_avoiding
        (R := fun x y ↦ FibreStep data contracted x y ∧ x ∈ vertices ∧ y ∈ vertices)
        (fun {_ _} h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩) hWalk hEq
      obtain ⟨edge, hTarget, hEnds⟩ := hStep.1
      have hSurvives : ¬ IsDangling data edge := by
        intro hDangling
        rcases NonDanglingValency.danglingSide_of_isDangling data hEnds hDangling
          with hCut | hCut
        · obtain ⟨cut⟩ := hCut
          exact hFirstActive (nonDanglingValency_eq_zero_of_danglingSide data cut)
        · obtain ⟨cut⟩ := hCut
          have hInside : second ∈ cut.side :=
            mem_side_of_avoiding cut.toSeparatingEdgeCut
              (Relation.ReflTransGen.mono
                (fun _ _ h ↦ ⟨h.1.1.num_edges_pos, h.2.2⟩) _ _ hAvoid)
          exact hSecondActive (nonDanglingValency_eq_zero_of_mem_side data cut.side.card
            next first cut le_rfl second hInside)
      have hNextActive : nonDanglingValency data next ≠ 0 :=
        nonDanglingValency_ne_zero_of_incident data hSurvives
          (incident_of_sourceEnds data hEnds.symm)
      have hNextNe : next ≠ first := by
        intro hSame
        have hPos := hStep.1.num_edges_pos
        have hZero : num_edges data.sourceGraph first first = 0 :=
          num_edges_self_zero data.sourceGraph first
        rw [hSame] at hPos
        omega
      have hTail : Relation.ReflTransGen
          (fun x y ↦ FibreStep data contracted x y ∧
            x ∈ vertices.erase first ∧ y ∈ vertices.erase first) next second :=
        Relation.ReflTransGen.mono
          (fun _ _ h ↦ ⟨h.1.1, Finset.mem_erase.mpr ⟨h.2.1, h.1.2.1⟩,
            Finset.mem_erase.mpr ⟨h.2.2, h.1.2.2⟩⟩) _ _ hAvoid
      exact Relation.ReflTransGen.head ⟨edge, hTarget, hSurvives, hEnds⟩
        (ih (vertices.erase first) (Finset.erase_ssubset hFirstMem) next second
          (Finset.mem_erase.mpr ⟨hNextNe, hStep.2.2⟩)
          (Finset.mem_erase.mpr ⟨Ne.symm hEq, hSecondMem⟩)
          hNextActive hSecondActive hTail)

/-- **The non-dangling part of a contracted fibre is connected.**  Full-fibre
reachability between vertices carrying survivors can be realized using only
surviving contracted occurrences.  In particular this is not an assumed
`hStable` compatibility condition. -/
theorem surviving_walk_of_reachThroughContracted
    (data : GluingDatum target degree) (contracted : target.edges)
    {first second : data.SourceVertex}
    (hFirst : nonDanglingValency data first ≠ 0)
    (hSecond : nonDanglingValency data second ≠ 0)
    (hReach : ReachThroughContracted data contracted first second) :
    Relation.ReflTransGen (SurvivingFibreStep data contracted) first second := by
  classical
  apply surviving_walk_of_walk_within data contracted Finset.univ first second
    (Finset.mem_univ _) (Finset.mem_univ _) hFirst hSecond
  exact Relation.ReflTransGen.mono
    (fun _ _ h ↦ ⟨h, Finset.mem_univ _, Finset.mem_univ _⟩) _ _
      (reflTransGen_fibreStep_of_reachThroughContracted data contracted hReach)

/-- On vertices carrying survivors, equality in the actual contraction fibre
is precisely connectivity by surviving contracted occurrences.  This is the
pruned connectivity statement needed before applying the forest Euler count. -/
theorem sourceVertexMap_eq_iff_surviving_walk
    (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {first second : data.SourceVertex}
    (hFirst : nonDanglingValency data first ≠ 0)
    (hSecond : nonDanglingValency data second ≠ 0) :
    sourceVertexMap data hc hab hOne first = sourceVertexMap data hc hab hOne second ↔
      Relation.ReflTransGen (SurvivingFibreStep data contracted) first second := by
  rw [sourceVertexMap_eq_iff data hc hab hOne]
  constructor
  · exact surviving_walk_of_reachThroughContracted data contracted hFirst hSecond
  · intro hWalk
    clear hFirst hSecond
    induction hWalk with
    | refl => exact ReachThroughContracted.refl data contracted first
    | tail _ hStep ih => exact ih.trans hStep.fibreStep.reachThroughContracted

end DraismaVargas.LocalCases.PrunedContractionFibre
