module

public import Utilities.Gonality.GonalityTransport
public import Utilities.Foundations.RankDeterminingSet
public import Utilities.Subdivision.ExplicitPotentialRankOne
public import Utilities.Subdivision.SubdivisionCoreSupport

@[expose] public section

/-!
# Subdivision pencils with an explicit scale and divisor

Depends only on the subdivision, gonality and rank-determining APIs of
`Utilities`. No all-genus existence theorem is imported or assumed. Keeping
the scale and effective divisor makes the interface suitable for arithmetic
descent.
-/

namespace DraismaVargas

open Utilities Utilities.Gonality Utilities.Certificate.SubdivisionGraph

/-- A concrete effective pencil on a positive regular subdivision. -/
structure SubdivisionPencil {n p : ℕ} (spec : Spec n p) (d : ℕ) where
  scale : ℕ
  scale_pos : 0 < scale
  divisor : CFDiv (spec.scale scale scale_pos).graph
  effective : _root_.effective divisor
  degree_eq : deg divisor = (d : ℤ)
  rank_ge_one : rank (spec.scale scale scale_pos).graph divisor ≥ 1

namespace SubdivisionPencil

variable {n p d : ℕ} {spec : Spec n p}

theorem bnExists (w : SubdivisionPencil spec d) :
    BNExists (spec.scale w.scale w.scale_pos).graph 1 (d : ℤ) :=
  ⟨w.divisor, w.degree_eq, w.rank_ge_one⟩

theorem gonality_le (w : SubdivisionPencil spec d) :
    spec.regularSubdivisionGonality ≤ d := by
  have h : divisorialGonality (spec.scale w.scale w.scale_pos).graph ≤ d := by
    exact_mod_cast divisorialGonality_le_of_BNExists w.bnExists
  exact (spec.regularSubdivisionGonality_le w.scale_pos rfl).trans h

/-- Replace any rank-one witness by an effective one without changing scale. -/
theorem exists_of_BNExists {N : ℕ} (hN : 0 < N)
    (h : BNExists (spec.scale N hN).graph 1 (d : ℤ)) :
    ∃ w : SubdivisionPencil spec d, w.scale = N := by
  obtain ⟨D, hdeg, hrank⟩ := h
  obtain ⟨E, heff, hedeg, herank⟩ := exists_effective_of_rank_ge_one hrank
  exact ⟨⟨N, hN, E, heff, hedeg.trans hdeg, herank⟩, rfl⟩

/-- The exact existential scale contract, equivalent to a pencil record. -/
theorem nonempty_iff : Nonempty (SubdivisionPencil spec d) ↔
    ∃ (N : ℕ) (hN : 0 < N), BNExists (spec.scale N hN).graph 1 (d : ℤ) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.scale, w.scale_pos, w.bnExists⟩
  · rintro ⟨N, hN, h⟩
    obtain ⟨w, _⟩ := exists_of_BNExists hN h
    exact ⟨w⟩

/-- Low-genus discrete pencils give a scale-one record. -/
theorem exists_at_one (h : BNExists spec.graph 1 (d : ℤ)) :
    ∃ w : SubdivisionPencil spec d, w.scale = 1 := by
  apply exists_of_BNExists Nat.one_pos
  exact ((Spec.laplacianEquiv _ _ spec.scaleOneRelabeling).bnExists_iff 1 (d : ℤ)).mpr h

/-! ## Exact metric slopes on subdivided source edges -/

/-- If the endpoint rise is an integral slope times the path length, the
canonical integer interpolator has that slope on every genuine unit step. -/
theorem interpolationStep_eq_slope_of_exactRise {length offset : ℕ}
    {rise slope : ℤ} (hLength : 0 < length) (hOffset : offset < length)
    (hRise : rise = slope * (length : ℤ)) :
    Utilities.Certificate.SubdivisionArithmetic.step length rise offset = slope := by
  subst rise
  unfold Utilities.Certificate.SubdivisionArithmetic.step
    Utilities.Certificate.SubdivisionArithmetic.potential
    Utilities.Certificate.SubdivisionArithmetic.quotient
    Utilities.Certificate.SubdivisionArithmetic.bend
    Utilities.Certificate.SubdivisionArithmetic.remainder
  have hLengthInt : (length : ℤ) ≠ 0 := by exact_mod_cast hLength.ne'
  rw [Int.mul_ediv_cancel _ hLengthInt, Int.mul_emod_left]
  push_cast
  rw [max_eq_left (by omega), max_eq_left (by omega)]
  ring

/-- Under exact integral slopes, the interpolated script has zero principal
coefficient at every subdivision-interior vertex. -/
theorem prin_interpolatedScript_interior_eq_zero_of_exactSlopes
    (spec : Spec n p) (potential : Fin n → ℤ) (slope : Fin p → ℤ)
    (hRise : ∀ edge, spec.coreRise potential edge =
      slope edge * (spec.length edge : ℤ))
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    prin spec.graph (spec.interpolatedScript potential)
      (spec.interiorVertex edge offset) = 0 := by
  rw [spec.prin_interpolatedScript_interior_eq_stepDifference]
  rw [interpolationStep_eq_slope_of_exactRise (spec.length_pos edge)
      (by have := offset.isLt; omega) (hRise edge),
    interpolationStep_eq_slope_of_exactRise (spec.length_pos edge)
      (by have := offset.isLt; omega) (hRise edge)]
  exact sub_self _

/-- Under exact integral slopes, the interpolated principal divisor at a core
vertex is the signed sum of the incident source-edge slopes. -/
theorem prin_interpolatedScript_core_eq_incidenceSum_of_exactSlopes
    (spec : Spec n p) (potential : Fin n → ℤ) (slope : Fin p → ℤ)
    (hRise : ∀ edge, spec.coreRise potential edge =
      slope edge * (spec.length edge : ℤ))
    (vertex : Fin n) :
    prin spec.graph (spec.interpolatedScript potential)
        (spec.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if spec.core.tail edge = vertex then slope edge else 0) +
          (if spec.core.head edge = vertex then -slope edge else 0)) := by
  rw [spec.prin_interpolatedScript_core_eq_endpointSum]
  apply Finset.sum_congr rfl
  intro edge _
  rw [interpolationStep_eq_slope_of_exactRise (spec.length_pos edge)
      (spec.length_pos edge) (hRise edge),
    interpolationStep_eq_slope_of_exactRise (spec.length_pos edge)
      (by have := spec.length_pos edge; omega) (hRise edge)]

/-- The exact semantic contract needed to read a pencil off a realized
Draisma--Vargas gluing datum (in the sense of Draisma--Vargas Part I,
arXiv:1909.12924).

The divisor is supported on core vertices.  For every requested core chip,
the caller supplies an integral core potential whose rise on each source edge
is an exact integral slope times that edge's subdivision length.  The final
hypothesis is precisely the resulting core-vertex residual.  Exact slopes make
every interior residual zero, so the core rank-determining theorem promotes
these finitely many firing scripts to rank one. -/
theorem rank_coreDivisor_ge_one_of_exactCorePotentials (spec : Spec n p)
    (weight : Fin n → ℤ)
    (hConnected : graph_connected spec.graph)
    (potential : Fin n → Fin n → ℤ)
    (slope : Fin n → Fin p → ℤ)
    (hRise : ∀ anchor edge, spec.coreRise (potential anchor) edge =
      slope anchor edge * (spec.length edge : ℤ))
    (hCore : ∀ anchor vertex,
      0 ≤ weight vertex - (if vertex = anchor then 1 else 0) +
        ∑ edge : Fin p,
          ((if spec.core.tail edge = vertex then slope anchor edge else 0) +
            (if spec.core.head edge = vertex then -slope anchor edge else 0))) :
    rank spec.graph
      (Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor spec weight) ≥ 1 := by
  let divisor : CFDiv spec.graph :=
    Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor spec weight
  apply spec.rank_ge_one_of_forall_mem_coreVertices hConnected divisor
  intro requested hRequested
  obtain ⟨anchor, _hAnchor, rfl⟩ := (spec.mem_coreVertices requested).mp hRequested
  let script : firing_script spec.graph :=
    spec.interpolatedScript (potential anchor)
  refine ⟨divisor - one_chip (spec.coreVertex anchor) +
      prin spec.graph script, ?_, ?_⟩
  · intro vertex
    rcases vertex with vertex | interior
    · simp only [Pi.add_apply, Pi.sub_apply, divisor,
        one_chip, Spec.coreVertex, Sum.inl.injEq]
      change 0 ≤ weight vertex -
        (if vertex = anchor then 1 else 0) +
          prin spec.graph script (spec.coreVertex vertex)
      rw [show prin spec.graph script (spec.coreVertex vertex) =
          ∑ edge : Fin p,
            ((if spec.core.tail edge = vertex then slope anchor edge else 0) +
              (if spec.core.head edge = vertex then -slope anchor edge else 0)) by
        exact prin_interpolatedScript_core_eq_incidenceSum_of_exactSlopes
          spec (potential anchor) (slope anchor) (hRise anchor) vertex]
      exact hCore anchor vertex
    · rcases interior with ⟨edge, offset⟩
      change 0 ≤ 0 - 0 +
        prin spec.graph script (spec.interiorVertex edge offset)
      rw [show prin spec.graph script (spec.interiorVertex edge offset) = 0 by
        exact prin_interpolatedScript_interior_eq_zero_of_exactSlopes
          spec (potential anchor) (slope anchor) (hRise anchor) edge offset]
      omega
  · exact Utilities.Certificate.StrongSeparator.linearEquiv_add_prin
      (divisor - one_chip (spec.coreVertex anchor)) script

/-- Compatibility existence wrapper; the named core divisor itself has rank one. -/
theorem bnExists_and_effective_of_exactCorePotentials (spec : Spec n p)
    (degree : ℤ) (weight : Fin n → ℤ)
    (hConnected : graph_connected spec.graph)
    (hWeight : ∀ vertex, 0 ≤ weight vertex)
    (hDegree : (∑ vertex : Fin n, weight vertex) = degree)
    (potential : Fin n → Fin n → ℤ)
    (slope : Fin n → Fin p → ℤ)
    (hRise : ∀ anchor edge, spec.coreRise (potential anchor) edge =
      slope anchor edge * (spec.length edge : ℤ))
    (hCore : ∀ anchor vertex,
      0 ≤ weight vertex - (if vertex = anchor then 1 else 0) +
        ∑ edge : Fin p,
          ((if spec.core.tail edge = vertex then slope anchor edge else 0) +
            (if spec.core.head edge = vertex then -slope anchor edge else 0))) :
    BNExists spec.graph 1 degree ∧
      _root_.effective
        (Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor spec weight) := by
  refine ⟨⟨_, (Utilities.Subdivision.SubdivisionCoreSupport.deg_coreDivisor
    spec weight).trans hDegree, ?_⟩,
    Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor_effective spec weight hWeight⟩
  exact rank_coreDivisor_ge_one_of_exactCorePotentials spec weight hConnected
    potential slope hRise hCore

/-- It suffices to move a degree-d effective divisor to each source core vertex.
This is the semantic endpoint for pulled-back tree potentials. -/
def ofCoreReachability {N : ℕ} (hN : 0 < N)
    (hconn : graph_connected (spec.scale N hN).graph)
    (D : CFDiv (spec.scale N hN).graph) (heff : _root_.effective D)
    (hdeg : deg D = (d : ℤ))
    (hreaches : ∀ x ∈ (spec.scale N hN).coreVertices,
      winnable (spec.scale N hN).graph (D - one_chip x)) :
    SubdivisionPencil spec d where
  scale := N
  scale_pos := hN
  divisor := D
  effective := heff
  degree_eq := hdeg
  rank_ge_one := (spec.scale N hN).rank_ge_one_of_forall_mem_coreVertices hconn D hreaches

end SubdivisionPencil
end DraismaVargas
