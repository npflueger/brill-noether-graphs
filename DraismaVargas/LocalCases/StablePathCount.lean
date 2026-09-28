import DraismaVargas.LocalCases.Trivalence

/-!
# The stable-path count

The trivalence count of `Trivalence` needs two identifications that it does not
prove itself.  This module supplies the first:

```
∑_{v ∈ V₃} nonDanglingValency data v = 2 * Fintype.card (StablePath data),
```

`sum_stableValency_eq_two_mul_card_stablePath`, with `V₃ = stableVertices data`.
Each stable path has two ends, and both lie at vertices of surviving valency at
least three, so summing the surviving valency over `V₃` counts every stable
path exactly twice.

**The hypothesis `W4StableSource.HasPathEnds` is carried explicitly and is
never derived here.**  It says that no stable path is a cycle.  It is a
consequence of trivalence of the stable graph, which is exactly what the
Draisma--Vargas count is being used to prove, so deriving it here would be
circular; `W4StableSource` carries it as a hypothesis for the same reason, and
`FullDimensionalSource.FullDimensionalSourcePresentation` supplies it as the
`pathEnds` field.  It is used for one of the two inequalities only, and the
closing section says exactly which.

## How the count is made

Everything is assembled from one quantity, `incidenceCount data vertex path`:
the number of surviving occurrences of `path` that meet `vertex`.  Summed over
`path` it is the surviving valency (`sum_incidenceCount_vertex`); summed over
`vertex` it is twice the number of occurrences of the path
(`sum_incidenceCount_path`), because a quotient-source occurrence has two
*distinct* ends.  At a vertex of surviving valency two it is `0` or `2`
(`incidenceCount_eq_zero_or_two`): the two occurrences there are consecutive,
so a stable path either misses such a vertex or passes straight through it.
That already makes the number of ends of a path even.

The remaining input is graph-theoretic and is isolated in `junctionGraph`: one
vertex per surviving occurrence, one edge occurrence per vertex of surviving
valency two, joining the two occurrences that meet there.  Its walk components
are exactly the stable paths (`reach_junctionGraph_iff`,
`componentCount_junctionGraph`), so the spanning-forest bound
`Trivalence.card_V_le_card_edges_add_componentCount` reads
`#occurrences ≤ #junctions + #stable paths` (`card_nonDanglingEdge_le`).

This works with the `Consecutive` quotient `W4StableSource.StablePath`, not
with the rows of a presentation, so the objection `Trivalence` records against
`PresentationDecomposition.Decomposes` — that two rows may meet at a
valency-two vertex, so the rows need not be maximal paths — does not arise.

-/

namespace DraismaVargas.LocalCases.StablePathCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.PrunedSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.Trivalence

variable {target : CFGraph} {degree : ℕ}

/-! ## Incidences of a surviving occurrence -/

/-- **Every occurrence has exactly two ends.**  The two endpoints of a
quotient-source occurrence are distinct, so the vertices it meets are a
two-element finset. -/
theorem card_filter_incident (data : GluingDatum target degree)
    (edge : data.SourceEdge) :
    ((Finset.univ : Finset data.SourceVertex).filter fun vertex ↦
        Incident data edge vertex).card = 2 := by
  classical
  have hSet : ((Finset.univ : Finset data.SourceVertex).filter fun vertex ↦
      Incident data edge vertex)
        = {(data.sourceEnds edge).1, (data.sourceEnds edge).2} := by
    ext vertex
    constructor
    · intro hMem
      rcases (Finset.mem_filter.mp hMem).2 with hLeft | hRight
      · exact Finset.mem_insert.mpr (Or.inl hLeft.symm)
      · exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr hRight.symm))
    · intro hMem
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hMem with hLeft | hRight
      · exact Or.inl hLeft.symm
      · exact Or.inr (Finset.mem_singleton.mp hRight).symm
  rw [hSet]
  exact Finset.card_pair (data.sourceEnds_ne edge)

/-- The surviving occurrences at a source vertex, as a finset of
`NonDanglingEdge`. -/
noncomputable def incidentEdges (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : Finset (NonDanglingEdge data) :=
  (Finset.univ : Finset (NonDanglingEdge data)).filter fun edge ↦
    Incident data edge.1 vertex

@[simp] theorem mem_incidentEdges (data : GluingDatum target degree)
    (vertex : data.SourceVertex) (edge : NonDanglingEdge data) :
    edge ∈ incidentEdges data vertex ↔ Incident data edge.1 vertex := by
  simp [incidentEdges]

/-- The surviving valency is the number of surviving occurrences at the
vertex, counted in the subtype of surviving occurrences. -/
theorem card_incidentEdges (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    (incidentEdges data vertex).card = nonDanglingValency data vertex := by
  classical
  rw [← card_nonDanglingIncident data vertex]
  refine Finset.card_bij (fun edge _ ↦ edge.1) ?_ ?_ ?_
  · intro edge hEdge
    exact (mem_nonDanglingIncident data vertex edge.1).mpr
      ⟨edge.2, (mem_incidentEdges data vertex edge).mp hEdge⟩
  · intro first _ second _ hEq
    exact Subtype.ext hEq
  · intro edge hEdge
    have hEdge' := (mem_nonDanglingIncident data vertex edge).mp hEdge
    exact ⟨⟨edge, hEdge'.1⟩,
      (mem_incidentEdges data vertex ⟨edge, hEdge'.1⟩).mpr hEdge'.2, rfl⟩

/-! ## Incidences split by stable path -/

/-- The surviving occurrences belonging to one stable path. -/
noncomputable def classEdges (data : GluingDatum target degree)
    (path : StablePath data) : Finset (NonDanglingEdge data) :=
  (Finset.univ : Finset (NonDanglingEdge data)).filter fun edge ↦
    edge.stablePath = path

@[simp] theorem mem_classEdges (data : GluingDatum target degree)
    (path : StablePath data) (edge : NonDanglingEdge data) :
    edge ∈ classEdges data path ↔ edge.stablePath = path := by
  simp [classEdges]

/-- The number of surviving occurrences of the stable path `path` that meet
the source vertex `vertex`.  This is the single quantity every count below is
made of: summed over `path` it is the surviving valency, summed over `vertex`
it is twice the number of occurrences of the path. -/
noncomputable def incidenceCount (data : GluingDatum target degree)
    (vertex : data.SourceVertex) (path : StablePath data) : ℕ :=
  ((incidentEdges data vertex).filter fun edge ↦ edge.stablePath = path).card

theorem incidenceCount_pos_iff (data : GluingDatum target degree)
    (vertex : data.SourceVertex) (path : StablePath data) :
    0 < incidenceCount data vertex path ↔
      ∃ edge : NonDanglingEdge data,
        Incident data edge.1 vertex ∧ edge.stablePath = path := by
  unfold incidenceCount
  rw [Finset.card_pos]
  constructor
  · rintro ⟨edge, hEdge⟩
    rw [Finset.mem_filter, mem_incidentEdges] at hEdge
    exact ⟨edge, hEdge.1, hEdge.2⟩
  · rintro ⟨edge, hIncident, hPath⟩
    exact ⟨edge, Finset.mem_filter.mpr
      ⟨(mem_incidentEdges data vertex edge).mpr hIncident, hPath⟩⟩

/-- **Splitting the surviving valency by stable path.**  Every surviving
occurrence at a vertex lies on exactly one stable path. -/
theorem sum_incidenceCount_vertex (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    (∑ path : StablePath data, incidenceCount data vertex path)
      = nonDanglingValency data vertex := by
  rw [← card_incidentEdges data vertex]
  exact (Finset.card_eq_sum_card_fiberwise
    (fun edge _ ↦ Finset.mem_univ edge.stablePath)).symm

/-- **Counting the incidences of one stable path.**  Each of its occurrences
has exactly two ends, so the incidences of a stable path, summed over all
source vertices, number twice its occurrences. -/
theorem sum_incidenceCount_path (data : GluingDatum target degree)
    (path : StablePath data) :
    (∑ vertex : data.SourceVertex, incidenceCount data vertex path)
      = 2 * (classEdges data path).card := by
  have hCount : ∀ vertex : data.SourceVertex,
      incidenceCount data vertex path
        = ∑ edge : NonDanglingEdge data,
            if Incident data edge.1 vertex ∧ edge.stablePath = path then 1 else 0 := by
    intro vertex
    unfold incidenceCount incidentEdges
    rw [Finset.filter_filter, Finset.card_filter]
  have hInner : ∀ edge : NonDanglingEdge data,
      (∑ vertex : data.SourceVertex,
          if Incident data edge.1 vertex ∧ edge.stablePath = path then 1 else 0)
        = if edge.stablePath = path then 2 else 0 := by
    intro edge
    by_cases hPath : edge.stablePath = path
    · simp only [hPath, and_true, if_true]
      rw [← Finset.card_filter]
      exact card_filter_incident data edge.1
    · simp [hPath]
  rw [Finset.sum_congr rfl fun vertex _ ↦ hCount vertex, Finset.sum_comm,
    Finset.sum_congr rfl fun edge _ ↦ hInner edge, ← Finset.sum_filter,
    Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-! ## Junctions: the vertices a stable path passes through -/

/-- The source vertices of surviving valency two: the interior vertices of the
stable paths. -/
noncomputable def junctionVertices (data : GluingDatum target degree) :
    Finset data.SourceVertex :=
  (Finset.univ : Finset data.SourceVertex).filter fun vertex ↦
    nonDanglingValency data vertex = 2

@[simp] theorem mem_junctionVertices (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    vertex ∈ junctionVertices data ↔ nonDanglingValency data vertex = 2 := by
  simp [junctionVertices]

/-- **A stable path passes straight through a valency-two vertex.**  At such a
vertex a stable path has either no incidence at all or both of them: the two
surviving occurrences there are consecutive, hence lie on the same path. -/
theorem incidenceCount_eq_zero_or_two (data : GluingDatum target degree)
    {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) (path : StablePath data) :
    incidenceCount data vertex path = 0 ∨ incidenceCount data vertex path = 2 := by
  by_cases hPos : 0 < incidenceCount data vertex path
  · right
    obtain ⟨first, hIncident, hPath⟩ :=
      (incidenceCount_pos_iff data vertex path).mp hPos
    obtain ⟨other, hNe, hPair⟩ :=
      nonDanglingIncident_eq_pair data hValency first.2 hIncident
    have hOtherMem : other ∈ nonDanglingIncident data vertex := by
      rw [hPair]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self other)
    rw [mem_nonDanglingIncident] at hOtherMem
    obtain ⟨second, hSecondVal⟩ :
        ∃ second : NonDanglingEdge data, second.1 = other :=
      ⟨⟨other, hOtherMem.1⟩, rfl⟩
    have hSecondIncident : Incident data second.1 vertex := by
      rw [hSecondVal]
      exact hOtherMem.2
    have hNe' : first ≠ second := by
      intro hEq
      apply hNe
      rw [← hSecondVal, ← hEq]
    have hConsecutive : Consecutive data first second :=
      ⟨hNe', vertex, hIncident, hSecondIncident, hValency⟩
    have hSecondPath : second.stablePath = path :=
      (stablePath_eq_of_consecutive hConsecutive).symm.trans hPath
    have hSet :
        ((incidentEdges data vertex).filter fun edge ↦ edge.stablePath = path)
          = {first, second} := by
      ext edge
      constructor
      · intro hMem
        rw [Finset.mem_filter, mem_incidentEdges] at hMem
        have hEdgeMem : edge.1 ∈ nonDanglingIncident data vertex :=
          (mem_nonDanglingIncident data vertex edge.1).mpr ⟨edge.2, hMem.1⟩
        rw [hPair] at hEdgeMem
        rcases Finset.mem_insert.mp hEdgeMem with hEq | hEq
        · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hEq))
        · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
            (Subtype.ext ?_)))
          rw [hSecondVal]
          exact Finset.mem_singleton.mp hEq
      · intro hMem
        rcases Finset.mem_insert.mp hMem with hEq | hEq
        · subst hEq
          exact Finset.mem_filter.mpr
            ⟨(mem_incidentEdges data vertex edge).mpr hIncident, hPath⟩
        · rw [Finset.mem_singleton] at hEq
          subst hEq
          exact Finset.mem_filter.mpr
            ⟨(mem_incidentEdges data vertex edge).mpr hSecondIncident, hSecondPath⟩
    unfold incidenceCount
    rw [hSet, Finset.card_pair hNe']
  · left
    omega

/-- **Where `HasPathEnds` enters, and the only place it does.**  Every stable
path meets some source vertex of surviving valency different from two — that
is exactly the hypothesis that no stable path is a cycle. -/
theorem exists_end_vertex (data : GluingDatum target degree)
    (hEnds : HasPathEnds data) (path : StablePath data) :
    ∃ vertex : data.SourceVertex, nonDanglingValency data vertex ≠ 2 ∧
      0 < incidenceCount data vertex path := by
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep path
  obtain ⟨first, vertex, hPath, hEnd⟩ := hEnds edge
  refine ⟨vertex, hEnd.2,
    (incidenceCount_pos_iff data vertex path).mpr ⟨first, hEnd.1, ?_⟩⟩
  rw [hPath]
  exact hEdge

/-! ## The ends of a stable path -/

/-- The junctions a stable path passes through. -/
noncomputable def classJunctions (data : GluingDatum target degree)
    (path : StablePath data) : Finset data.SourceVertex :=
  (junctionVertices data).filter fun vertex ↦ 0 < incidenceCount data vertex path

/-- **The ends of a stable path**: its incidences at vertices of surviving
valency different from two. -/
noncomputable def endCount (data : GluingDatum target degree)
    (path : StablePath data) : ℕ :=
  ∑ vertex ∈ (Finset.univ : Finset data.SourceVertex).filter
      (fun vertex ↦ ¬ nonDanglingValency data vertex = 2),
    incidenceCount data vertex path

/-- At its junctions a stable path has exactly two incidences each. -/
theorem sum_incidenceCount_junctionVertices (data : GluingDatum target degree)
    (path : StablePath data) :
    (∑ vertex ∈ junctionVertices data, incidenceCount data vertex path)
      = 2 * (classJunctions data path).card := by
  have hRestrict :
      (∑ vertex ∈ classJunctions data path, incidenceCount data vertex path)
        = ∑ vertex ∈ junctionVertices data, incidenceCount data vertex path := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro vertex hMem hNotMem
    unfold classJunctions at hNotMem
    rw [Finset.mem_filter] at hNotMem
    have hZero : ¬ 0 < incidenceCount data vertex path := fun hPos ↦
      hNotMem ⟨hMem, hPos⟩
    omega
  have hTwo :
      (∑ vertex ∈ classJunctions data path, incidenceCount data vertex path)
        = ∑ _vertex ∈ classJunctions data path, 2 := by
    refine Finset.sum_congr rfl ?_
    intro vertex hMem
    unfold classJunctions at hMem
    rw [Finset.mem_filter, mem_junctionVertices] at hMem
    rcases incidenceCount_eq_zero_or_two data hMem.1 path with hZero | hTwo
    · omega
    · exact hTwo
  rw [← hRestrict, hTwo, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The ends and the junctions of a stable path account for all its
incidences.**  Every occurrence of the path has two ends, and each junction of
the path swallows two of them, so the number of remaining ends has the same
parity as zero. -/
theorem endCount_add_two_mul_card_classJunctions
    (data : GluingDatum target degree) (path : StablePath data) :
    endCount data path + 2 * (classJunctions data path).card
      = 2 * (classEdges data path).card := by
  unfold endCount
  rw [← sum_incidenceCount_junctionVertices data path]
  rw [Nat.add_comm]
  unfold junctionVertices
  rw [Finset.sum_filter_add_sum_filter_not]
  exact sum_incidenceCount_path data path

/-- **Every stable path has at least two ends.**  It has at least one by
`HasPathEnds`, and its number of ends is even. -/
theorem two_le_endCount (data : GluingDatum target degree)
    (hEnds : HasPathEnds data) (path : StablePath data) :
    2 ≤ endCount data path := by
  obtain ⟨vertex, hValency, hPos⟩ := exists_end_vertex data hEnds path
  have hMem : vertex ∈ (Finset.univ : Finset data.SourceVertex).filter
      (fun vertex ↦ ¬ nonDanglingValency data vertex = 2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValency⟩
  have hLe : incidenceCount data vertex path ≤ endCount data path :=
    Finset.single_le_sum (f := fun vertex ↦ incidenceCount data vertex path)
      (fun _ _ ↦ Nat.zero_le _) hMem
  have hParity := endCount_add_two_mul_card_classJunctions data path
  omega

/-! ## The global counts -/

/-- The surviving occurrences are partitioned by their stable paths. -/
theorem sum_card_classEdges (data : GluingDatum target degree) :
    (∑ path : StablePath data, (classEdges data path).card)
      = Fintype.card (NonDanglingEdge data) := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise
    (fun edge _ ↦ Finset.mem_univ edge.stablePath)).symm

/-- Every junction belongs to exactly one stable path. -/
theorem sum_card_classJunctions (data : GluingDatum target degree) :
    (∑ path : StablePath data, (classJunctions data path).card)
      = (junctionVertices data).card := by
  have hCard : ∀ path : StablePath data, (classJunctions data path).card
      = ∑ vertex ∈ junctionVertices data,
          if 0 < incidenceCount data vertex path then 1 else 0 := by
    intro path
    unfold classJunctions
    rw [Finset.card_filter]
  have hOne : ∀ vertex ∈ junctionVertices data,
      (∑ path : StablePath data,
        if 0 < incidenceCount data vertex path then 1 else 0) = 1 := by
    intro vertex hMem
    rw [mem_junctionVertices] at hMem
    have hEach : ∀ path : StablePath data,
        (if 0 < incidenceCount data vertex path then 2 else 0)
          = incidenceCount data vertex path := by
      intro path
      rcases incidenceCount_eq_zero_or_two data hMem path with hZero | hTwo
      · rw [hZero]
        norm_num
      · rw [hTwo]
        norm_num
    have hDouble : (∑ path : StablePath data,
        if 0 < incidenceCount data vertex path then 2 else 0) = 2 := by
      rw [Finset.sum_congr rfl fun path _ ↦ hEach path,
        sum_incidenceCount_vertex data vertex, hMem]
    have hSplit : (∑ path : StablePath data,
        if 0 < incidenceCount data vertex path then 2 else 0)
          = 2 * ∑ path : StablePath data,
              if 0 < incidenceCount data vertex path then 1 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro path _
      by_cases hPos : 0 < incidenceCount data vertex path <;> simp [hPos]
    omega
  rw [Finset.sum_congr rfl fun path _ ↦ hCard path, Finset.sum_comm,
    Finset.sum_congr rfl hOne, Finset.sum_const, smul_eq_mul, mul_one]

/-- **The ends of the stable paths are exactly the incidences at the vertices
of the stable graph.**  A vertex of surviving valency different from two and
different from zero has valency at least three, and an isolated vertex carries
no incidence at all. -/
theorem sum_endCount (data : GluingDatum target degree)
    (hNeOne : ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≠ 1) :
    (∑ path : StablePath data, endCount data path)
      = ∑ vertex ∈ stableVertices data, nonDanglingValency data vertex := by
  unfold endCount
  rw [Finset.sum_comm,
    Finset.sum_congr rfl fun vertex _ ↦ sum_incidenceCount_vertex data vertex]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro vertex hMem
    rw [mem_stableVertices] at hMem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    omega
  · intro vertex hMem hNotMem
    rw [Finset.mem_filter] at hMem
    rw [mem_stableVertices] at hNotMem
    have hNeOneAt := hNeOne vertex
    omega

/-! ## The junction graph and the spanning-forest bound -/

section JunctionGraph

variable (data : GluingDatum target degree)

private theorem nonDanglingIncident_nonempty {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    (nonDanglingIncident data vertex).Nonempty := by
  rw [← Finset.card_pos, card_nonDanglingIncident, hValency]
  norm_num

/-- A chosen surviving occurrence at a valency-two vertex. -/
private noncomputable def anchor {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) : data.SourceEdge :=
  (nonDanglingIncident_nonempty data hValency).choose

private theorem anchor_mem {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    anchor data hValency ∈ nonDanglingIncident data vertex :=
  (nonDanglingIncident_nonempty data hValency).choose_spec

private theorem anchor_not_dangling {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    ¬ IsDangling data (anchor data hValency) :=
  ((mem_nonDanglingIncident data vertex _).mp (anchor_mem data hValency)).1

private theorem anchor_incident {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    Incident data (anchor data hValency) vertex :=
  ((mem_nonDanglingIncident data vertex _).mp (anchor_mem data hValency)).2

/-- The two surviving occurrences that meet at a valency-two vertex. -/
private noncomputable def junctionPair {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    NonDanglingEdge data × NonDanglingEdge data :=
  (⟨anchor data hValency, anchor_not_dangling data hValency⟩,
    ⟨stepEdge data hValency (anchor data hValency),
      stepEdge_not_dangling data hValency (anchor data hValency)⟩)

private theorem junctionPair_ne {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    (junctionPair data hValency).1 ≠ (junctionPair data hValency).2 := by
  intro hEq
  exact stepEdge_ne data hValency (anchor data hValency)
    (congrArg Subtype.val hEq).symm

private theorem junctionPair_fst_incident {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    Incident data (junctionPair data hValency).1.1 vertex :=
  anchor_incident data hValency

private theorem junctionPair_snd_incident {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2) :
    Incident data (junctionPair data hValency).2.1 vertex :=
  stepEdge_incident data hValency (anchor data hValency)

/-- At a valency-two vertex there are no surviving occurrences besides the
two of `junctionPair`. -/
private theorem eq_junctionPair {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    (edge : NonDanglingEdge data) (hIncident : Incident data edge.1 vertex) :
    edge = (junctionPair data hValency).1 ∨
      edge = (junctionPair data hValency).2 := by
  rcases eq_or_eq_stepEdge data hValency (anchor_not_dangling data hValency)
    (anchor_incident data hValency) edge.2 hIncident with hEq | hEq
  · exact Or.inl (Subtype.ext hEq)
  · exact Or.inr (Subtype.ext hEq)

/-- **The junction graph.**  One vertex for every surviving occurrence, one
edge occurrence for every junction, joining the two surviving occurrences that
meet there.  Its components are the stable paths, and the spanning-forest
bound applied to it is the only place a graph-theoretic input is used. -/
@[reducible] noncomputable def junctionGraph
    (hNonempty : Nonempty (NonDanglingEdge data)) : CFGraph where
  V := NonDanglingEdge data
  instNonempty := hNonempty
  edges := (junctionVertices data).attach.val.map fun vertex ↦
    junctionPair data ((mem_junctionVertices data vertex.1).mp vertex.2)
  loopless := by
    intro edge hMem
    rw [Multiset.mem_map] at hMem
    obtain ⟨vertex, -, hEq⟩ := hMem
    exact junctionPair_ne data _ (by rw [hEq])

private theorem card_edges_junctionGraph
    (hNonempty : Nonempty (NonDanglingEdge data)) :
    Multiset.card (junctionGraph data hNonempty).edges
      = (junctionVertices data).card := by
  show Multiset.card ((junctionVertices data).attach.val.map _) = _
  rw [Multiset.card_map]
  exact Finset.card_attach

/-- **The edges of the junction graph are exactly the consecutive pairs.** -/
private theorem num_edges_junctionGraph_pos_iff
    (hNonempty : Nonempty (NonDanglingEdge data))
    (first second : NonDanglingEdge data) :
    0 < num_edges (junctionGraph data hNonempty) first second ↔
      Consecutive data first second := by
  constructor
  · intro hPos
    unfold num_edges at hPos
    rw [Multiset.card_pos_iff_exists_mem] at hPos
    obtain ⟨pair, hPair⟩ := hPos
    rw [Multiset.mem_filter] at hPair
    obtain ⟨hMem, hShape⟩ := hPair
    obtain ⟨vertex, -, hEq⟩ := Multiset.mem_map.mp hMem
    have hValency := (mem_junctionVertices data vertex.1).mp vertex.2
    rcases hShape with hShape | hShape
    · have hFst : (junctionPair data hValency).1 = first :=
        congrArg Prod.fst (hEq.trans hShape)
      have hSnd : (junctionPair data hValency).2 = second :=
        congrArg Prod.snd (hEq.trans hShape)
      refine ⟨?_, vertex.1, ?_, ?_, hValency⟩
      · rw [← hFst, ← hSnd]
        exact junctionPair_ne data hValency
      · rw [← hFst]
        exact junctionPair_fst_incident data hValency
      · rw [← hSnd]
        exact junctionPair_snd_incident data hValency
    · have hFst : (junctionPair data hValency).1 = second :=
        congrArg Prod.fst (hEq.trans hShape)
      have hSnd : (junctionPair data hValency).2 = first :=
        congrArg Prod.snd (hEq.trans hShape)
      refine consecutive_symm ⟨?_, vertex.1, ?_, ?_, hValency⟩
      · rw [← hFst, ← hSnd]
        exact junctionPair_ne data hValency
      · rw [← hFst]
        exact junctionPair_fst_incident data hValency
      · rw [← hSnd]
        exact junctionPair_snd_incident data hValency
  · rintro ⟨hNe, vertex, hFirst, hSecond, hValency⟩
    have hMemVertex : vertex ∈ junctionVertices data :=
      (mem_junctionVertices data vertex).mpr hValency
    have hShape : junctionPair data hValency = (first, second) ∨
        junctionPair data hValency = (second, first) := by
      rcases eq_junctionPair data hValency first hFirst with hFst | hFst
      · rcases eq_junctionPair data hValency second hSecond with hSnd | hSnd
        · exact absurd (hFst.trans hSnd.symm) hNe
        · exact Or.inl (Prod.ext hFst.symm hSnd.symm)
      · rcases eq_junctionPair data hValency second hSecond with hSnd | hSnd
        · exact Or.inr (Prod.ext hSnd.symm hFst.symm)
        · exact absurd (hFst.trans hSnd.symm) hNe
    unfold num_edges
    rw [Multiset.card_pos_iff_exists_mem]
    refine ⟨junctionPair data hValency, Multiset.mem_filter.mpr ⟨?_, hShape⟩⟩
    exact Multiset.mem_map.mpr ⟨⟨vertex, hMemVertex⟩, Finset.mem_attach _ _, rfl⟩

/-- **The components of the junction graph are the stable paths.** -/
private theorem reach_junctionGraph_iff
    (hNonempty : Nonempty (NonDanglingEdge data))
    (first second : NonDanglingEdge data) :
    Reach (junctionGraph data hNonempty) first second ↔
      first.stablePath = second.stablePath := by
  constructor
  · intro hReach
    induction hReach with
    | refl => rfl
    | @tail middle final _ hStep ih =>
        exact ih.trans (stablePath_eq_of_consecutive
          ((num_edges_junctionGraph_pos_iff data hNonempty middle final).mp hStep))
  · intro hPath
    have hEqv := (stablePath_eq_iff first second).mp hPath
    clear hPath
    induction hEqv with
    | rel x y hxy =>
        exact reach_single
          ((num_edges_junctionGraph_pos_iff data hNonempty x y).mpr hxy)
    | refl x => exact reach_refl _ _
    | symm x y _ ih => exact reach_symm ih
    | trans x y z _ _ ihLeft ihRight => exact reach_trans ihLeft ihRight

/-- Two maps with the same fibres have images of the same size. -/
private theorem card_image_eq_card_image {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq β] [DecidableEq γ] (f : α → β) (g : α → γ)
    (hFibre : ∀ first second : α, f first = f second ↔ g first = g second) :
    (Finset.univ.image f).card = (Finset.univ.image g).card := by
  refine Finset.card_bij (fun b hb ↦ g (Finset.mem_image.mp hb).choose) ?_ ?_ ?_
  · intro b _
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · intro first hFirst second hSecond hEq
    have hFirstSpec := (Finset.mem_image.mp hFirst).choose_spec
    have hSecondSpec := (Finset.mem_image.mp hSecond).choose_spec
    rw [← hFirstSpec.2, ← hSecondSpec.2]
    exact (hFibre _ _).mpr hEq
  · intro c hc
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨f a, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have hSpec := (Finset.mem_image.mp
      (Finset.mem_image_of_mem f (Finset.mem_univ a))).choose_spec
    exact (hFibre _ _).mp hSpec.2

private theorem componentCount_junctionGraph
    (hNonempty : Nonempty (NonDanglingEdge data)) :
    componentCount (junctionGraph data hNonempty)
      = Fintype.card (StablePath data) := by
  have hFibre : ∀ first second : NonDanglingEdge data,
      component (junctionGraph data hNonempty) first
          = component (junctionGraph data hNonempty) second ↔
        first.stablePath = second.stablePath := by
    intro first second
    constructor
    · intro hEq
      have hMem : second ∈ component (junctionGraph data hNonempty) first := by
        rw [hEq]
        exact self_mem_component _
      exact (reach_junctionGraph_iff data hNonempty first second).mp
        ((mem_component (G := junctionGraph data hNonempty) first second).mp hMem)
    · intro hPath
      exact component_eq_of_reach
        ((reach_junctionGraph_iff data hNonempty first second).mpr hPath)
  have hImage :
      ((Finset.univ : Finset (NonDanglingEdge data)).image
          fun edge ↦ edge.stablePath)
        = (Finset.univ : Finset (StablePath data)) := by
    ext path
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    obtain ⟨edge, hEdge⟩ := Quot.exists_rep path
    exact ⟨edge, hEdge⟩
  have hCount : componentCount (junctionGraph data hNonempty)
      = ((Finset.univ : Finset (NonDanglingEdge data)).image
          fun edge : NonDanglingEdge data ↦ edge.stablePath).card := by
    unfold componentCount
    exact card_image_eq_card_image (α := NonDanglingEdge data)
      (component (junctionGraph data hNonempty))
      (fun edge : NonDanglingEdge data ↦ edge.stablePath) hFibre
  rw [hCount, hImage, Finset.card_univ]

end JunctionGraph

/-- **The spanning-forest bound for the junction graph.**  There are at least
as many stable paths as surviving occurrences minus junctions.  No hypothesis
whatever is needed: this is `Trivalence.card_V_le_card_edges_add_componentCount`
transported along the identification of the components of the junction graph
with the stable paths. -/
theorem card_nonDanglingEdge_le (data : GluingDatum target degree) :
    Fintype.card (NonDanglingEdge data)
      ≤ (junctionVertices data).card + Fintype.card (StablePath data) := by
  by_cases hNonempty : Nonempty (NonDanglingEdge data)
  · have hBound :=
      card_V_le_card_edges_add_componentCount (junctionGraph data hNonempty)
    rw [card_edges_junctionGraph data hNonempty,
      componentCount_junctionGraph data hNonempty] at hBound
    exact hBound
  · rw [not_nonempty_iff] at hNonempty
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _

/-! ## The stable-path count -/

/-- **The ends, the occurrences and the junctions of all stable paths at
once.**  Summing the per-path identity
`endCount_add_two_mul_card_classJunctions` over the stable paths. -/
theorem sum_endCount_add_two_mul_card_junctionVertices
    (data : GluingDatum target degree) :
    (∑ path : StablePath data, endCount data path)
        + 2 * (junctionVertices data).card
      = 2 * Fintype.card (NonDanglingEdge data) := by
  have hAdd : (∑ path : StablePath data,
      (endCount data path + 2 * (classJunctions data path).card))
        = ∑ path : StablePath data, 2 * (classEdges data path).card :=
    Finset.sum_congr rfl fun path _ ↦
      endCount_add_two_mul_card_classJunctions data path
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_card_classJunctions, sum_card_classEdges] at hAdd
  exact hAdd

/-- **The upper bound, which needs no `HasPathEnds`.**  The total valency of
the stable graph is at most twice the number of stable paths.  This is the
inequality the trivalence count consumes, and it is the spanning-forest bound
for the junction graph in disguise. -/
theorem sum_stableValency_le_two_mul_card_stablePath
    (data : GluingDatum target degree)
    (hNeOne : ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≠ 1) :
    (∑ vertex ∈ stableVertices data, nonDanglingValency data vertex)
      ≤ 2 * Fintype.card (StablePath data) := by
  have hSum := sum_endCount data hNeOne
  have hGlobal := sum_endCount_add_two_mul_card_junctionVertices data
  have hForest := card_nonDanglingEdge_le data
  omega

/-- **The lower bound, which is exactly what `HasPathEnds` buys.**  Every
stable path has at least two ends, so the total valency of the stable graph is
at least twice the number of stable paths. -/
theorem two_mul_card_stablePath_le_sum_stableValency
    (data : GluingDatum target degree)
    (hNeOne : ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≠ 1)
    (hPathEnds : HasPathEnds data) :
    2 * Fintype.card (StablePath data)
      ≤ ∑ vertex ∈ stableVertices data, nonDanglingValency data vertex := by
  have hSum := sum_endCount data hNeOne
  have hLower : (∑ _path : StablePath data, 2)
      ≤ ∑ path : StablePath data, endCount data path :=
    Finset.sum_le_sum fun path _ ↦ two_le_endCount data hPathEnds path
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at hLower
  omega

/-- **The stable-path count.**  The total surviving valency of the vertices of
the stable graph is twice the number of stable paths: each stable path has two
ends, both at vertices of surviving valency at least three.

The hypothesis `hPathEnds : HasPathEnds data` is carried explicitly and is not
derived anywhere in this file — it says no stable path is a cycle, which is a
consequence of trivalence, so deriving it here would be circular.  It is used
only for the lower bound; `sum_stableValency_le_two_mul_card_stablePath` has
the upper bound without it. -/
theorem sum_stableValency_eq_two_mul_card_stablePath
    (data : GluingDatum target degree)
    (hNeOne : ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≠ 1)
    (hPathEnds : HasPathEnds data) :
    (∑ vertex ∈ stableVertices data, nonDanglingValency data vertex)
      = 2 * Fintype.card (StablePath data) :=
  Nat.le_antisymm (sum_stableValency_le_two_mul_card_stablePath data hNeOne)
    (two_mul_card_stablePath_le_sum_stableValency data hNeOne hPathEnds)

/-- **Every stable path has exactly two ends.**  A corollary of the count, not
an input to it. -/
theorem endCount_eq_two (data : GluingDatum target degree)
    (hNeOne : ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≠ 1)
    (hPathEnds : HasPathEnds data) (path : StablePath data) :
    endCount data path = 2 := by
  by_contra hNe
  have hThree : 2 < endCount data path := by
    have := two_le_endCount data hPathEnds path
    omega
  have hStrict : (∑ _path : StablePath data, 2)
      < ∑ path : StablePath data, endCount data path :=
    Finset.sum_lt_sum (fun other _ ↦ two_le_endCount data hPathEnds other)
      ⟨path, Finset.mem_univ _, hThree⟩
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at hStrict
  have hSum := sum_endCount data hNeOne
  have hCount :=
    sum_stableValency_eq_two_mul_card_stablePath data hNeOne hPathEnds
  omega

/-! ## The form the trivalence count consumes -/

/-- The stable-path count over a connected quotient source, in `ℤ` and in the
notation of `Trivalence`. -/
theorem sum_stableValency_eq_two_mul_card_stablePath_int
    (data : GluingDatum target degree) (hConnected : data.Connected)
    (hPathEnds : HasPathEnds data) :
    (∑ vertex ∈ stableVertices data, (nonDanglingValency data vertex : ℤ))
      = 2 * (Fintype.card (StablePath data) : ℤ) := by
  have hCount := sum_stableValency_eq_two_mul_card_stablePath data
    (nonDanglingValency_ne_one data hConnected) hPathEnds
  rw [← Nat.cast_sum]
  exact_mod_cast hCount

/-- **Trivalence from the stable-path count.**  Combined with
`Trivalence.nonDanglingValency_le_three_of_sum_le`, the count replaces the
numerical saturation hypothesis of `Trivalence.trivalent_of_euler_saturated` by
a comparison between the number of stable paths — which
`FullDimensionalSourcePresentation.stablePath_card` identifies with `|E(target)|` — and the
number of stable vertices. -/
theorem nonDanglingValency_le_three_of_two_mul_card_stablePath_le
    (data : GluingDatum target degree) (hConnected : data.Connected)
    (hPathEnds : HasPathEnds data)
    (hSaturated : 2 * Fintype.card (StablePath data)
      ≤ 3 * (stableVertices data).card) :
    ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≤ 3 := by
  refine nonDanglingValency_le_three_of_sum_le data ?_
  rw [sum_stableValency_eq_two_mul_card_stablePath_int data hConnected hPathEnds]
  exact_mod_cast hSaturated

/-- **The Euler relation of the stable graph.**  Its edges are the stable
paths, its vertices are `stableVertices data`, its components are those of the
pruned source other than the isolated vertices, and its first Betti number is
that of the pruned source:
`|E(H)| - |V(H)| + c(H) = b₁(Γ)` with `c(H) = c(Γ) - |V₀|`. -/
theorem card_stablePath_add_componentCount_eq
    (data : GluingDatum target degree) (hConnected : data.Connected)
    (hPathEnds : HasPathEnds data) :
    (Fintype.card (StablePath data) : ℤ)
        + (componentCount (prunedSource data) : ℤ)
      = cyclomatic (prunedSource data)
        + ((isolatedVertices data).card : ℤ)
        + ((stableVertices data).card : ℤ) := by
  have hCount :=
    sum_stableValency_eq_two_mul_card_stablePath_int data hConnected hPathEnds
  have hIdentity :=
    sum_stableValency_add_two_mul_card_sourceVertex data hConnected
  have hEuler := cyclomatic_prunedSource data
  linarith

/-- **The saturation hypothesis of `Trivalence.trivalent_of_euler_saturated`,
translated.**  Given the stable-path count, the Euler-saturation inequality
that trivalence rests on says exactly that there are at most `3/2` times as
many ends of stable paths as there are stable vertices. -/
theorem euler_saturated_iff_two_mul_card_stablePath_le
    (data : GluingDatum target degree) (hConnected : data.Connected)
    (hPathEnds : HasPathEnds data) :
    (2 * cyclomatic (prunedSource data)
          + 2 * ((isolatedVertices data).card : ℤ)
        ≤ ((stableVertices data).card : ℤ)
          + 2 * (componentCount (prunedSource data) : ℤ))
      ↔ 2 * Fintype.card (StablePath data)
          ≤ 3 * (stableVertices data).card := by
  have hEuler :=
    card_stablePath_add_componentCount_eq data hConnected hPathEnds
  constructor
  · intro hSaturated
    have hCast : (2 * Fintype.card (StablePath data) : ℤ)
        ≤ (3 * (stableVertices data).card : ℤ) := by linarith
    exact_mod_cast hCast
  · intro hLe
    have hCast : (2 * Fintype.card (StablePath data) : ℤ)
        ≤ (3 * (stableVertices data).card : ℤ) := by exact_mod_cast hLe
    linarith

/-!
## What this does, and does not, close

`sum_stableValency_eq_two_mul_card_stablePath` is the first of the two
identifications that `Trivalence` names as needed: the total valency of the
stable graph is twice the number of stable
paths.  It is proved from the `Consecutive` quotient itself, not from a
presentation, so the objection recorded there — that
`PresentationDecomposition.Decomposes` allows two rows to meet at a
valency-two vertex, hence does not count maximal paths — does not arise: the
quotient is maximal by construction.

The two directions have different hypotheses, and it is worth being explicit
about which is which.

* `sum_stableValency_le_two_mul_card_stablePath` needs only `nd ≠ 1`.  It is
  the spanning-forest bound `Trivalence.card_V_le_card_edges_add_componentCount`
  applied to the *junction graph*: one vertex per surviving occurrence, one
  edge per valency-two vertex.  Its components are the stable paths
  (`reach_junctionGraph_iff`), so `m ≤ |T| + #stable paths`, and this is
  exactly `∑_{V₃} nd ≤ 2 · #stable paths`.  This is the direction the
  trivalence count consumes.
* `two_mul_card_stablePath_le_sum_stableValency` needs `HasPathEnds` and
  cannot be had without it: a stable path that is a *cycle* has no ends at
  all, contributes nothing to the left-hand side and one to the right.  The
  three-edge cycle through three valency-two vertices is a counterexample to
  the identity — and to `endCount_eq_two` — as soon as `HasPathEnds` is
  dropped.  `HasPathEnds` is a consequence of trivalence of the stable graph,
  which is what the Draisma--Vargas count is being used to prove, so deriving
  it here would be circular; `W4StableSource` carries it as a hypothesis for
  the same reason, and `FullDimensionalSource` supplies it as the `pathEnds`
  field.

What else trivalence needs is unchanged by this file except in its shape.
`nonDanglingValency_le_three_of_two_mul_card_stablePath_le` reduces the
numerical saturation hypothesis of `Trivalence.trivalent_of_euler_saturated` to
`2 · #stable paths ≤ 3 · |V₃|`, in which the left-hand side is what
`FullDimensionalSourcePresentation.stablePath_card` controls.  The second identification
named by `Trivalence` — that deleting the dangling occurrences does not change
the first Betti number — is not addressed here.
-/

end DraismaVargas.LocalCases.StablePathCount
