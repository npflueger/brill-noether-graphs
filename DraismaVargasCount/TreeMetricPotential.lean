import DraismaVargas.Infrastructure.TargetSeparation
import DraismaVargas.Infrastructure.RationalRealization
import DraismaVargas.Infrastructure.TargetTreePotential

/-! Integrating arbitrary integral edge rises on a tree, including zero lengths. -/
namespace DraismaVargas.Count.TreeMetricPotential

open Utilities DraismaVargas.Infrastructure
open TargetSeparation IteratedContraction

variable {target : CFGraph}

noncomputable def cutValue (edge : target.edges) (v : target.V) : ℤ := by
  classical
  exact if (underlyingSimpleGraph (eraseOccurrence target (edge : target.V × target.V))).Reachable
    (edge : target.V × target.V).1 v then 0 else 1

theorem cutValue_tail (edge : target.edges) :
    cutValue edge (edge : target.V × target.V).1 = 0 := by
  classical
  exact if_pos (SimpleGraph.Reachable.refl _)

theorem cutValue_head (hConnected : graph_connected target) (hGenus : genus target = 0)
    (edge : target.edges) : cutValue edge (edge : target.V × target.V).2 = 1 := by
  classical
  exact if_neg (not_reachable_eraseOccurrence hConnected hGenus Multiset.coe_mem)

theorem cutValue_other (hConnected : graph_connected target) (hGenus : genus target = 0)
    (edge other : target.edges) (hNe : edge ≠ other) :
    cutValue edge (other : target.V × target.V).1 =
      cutValue edge (other : target.V × target.V).2 := by
  classical
  have hAway : ¬ ((edge : target.V × target.V) =
        ((other : target.V × target.V).1, (other : target.V × target.V).2) ∨
      (edge : target.V × target.V) =
        ((other : target.V × target.V).2, (other : target.V × target.V).1)) := by
    intro h
    have hTwo := two_le_num_edges_of_ne h (Or.inl rfl) hNe
    have hOne := IteratedContraction.num_edges_le_one_of_genus_zero_of_connected
      target hConnected hGenus (other : target.V × target.V).1 (other : target.V × target.V).2
    omega
  have hAdj : (underlyingSimpleGraph target).Adj
      (other : target.V × target.V).1 (other : target.V × target.V).2 := by
    rw [underlyingSimpleGraph_adj]
    exact num_edges_pos_of_ends (edge := other) (Or.inl rfl)
  have hLink := (adj_eraseOccurrence (target := target) Multiset.coe_mem hAdj hAway).reachable
  have hIff : (underlyingSimpleGraph (eraseOccurrence target (edge : target.V × target.V))).Reachable
      (edge : target.V × target.V).1 (other : target.V × target.V).1 ↔
      (underlyingSimpleGraph (eraseOccurrence target (edge : target.V × target.V))).Reachable
      (edge : target.V × target.V).1 (other : target.V × target.V).2 :=
    ⟨fun h ↦ h.trans hLink, fun h ↦ h.trans hLink.symm⟩
  simp only [cutValue, hIff]

noncomputable def integrate (rise : target.edges → ℤ) (v : target.V) : ℤ :=
  ∑ edge : target.edges, rise edge * cutValue edge v

theorem integrate_rise (hConnected : graph_connected target) (hGenus : genus target = 0)
    (rise : target.edges → ℤ) (edge : target.edges) :
    integrate rise (edge : target.V × target.V).2 -
      integrate rise (edge : target.V × target.V).1 = rise edge := by
  classical
  simp only [integrate, ← Finset.sum_sub_distrib, ← mul_sub]
  rw [Finset.sum_eq_single edge]
  · rw [cutValue_tail, cutValue_head hConnected hGenus]
    ring
  · intro other _ hNe
    rw [cutValue_other hConnected hGenus other edge hNe, sub_self, mul_zero]
  · simp

variable {degree : ℕ} (data : GluingDatum target degree)

/-- An auxiliary positive metric is used only to obtain the combinatorial
unit-chip flow. The actual closed metric is integrated separately. -/
noncomputable def unitRealization : data.IntegralRealization :=
  GluingDatum.IntegralRealization.ofPositiveRational data (fun _ ↦ 1) (fun _ ↦ by norm_num)

noncomputable def chipSlope (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor : target.V) : target.edges → ℤ :=
  (unitRealization data).targetTreeSlope hConnected hGenus root anchor

theorem chipSlope_incidence (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor vertex : target.V) :
    GluingDatum.targetEdgeIncidence (chipSlope data hConnected hGenus root anchor) vertex =
      (if vertex = anchor then 1 else 0) - (if vertex = root then 1 else 0) :=
  (unitRealization data).targetTreeSlope_incidence hConnected hGenus root anchor vertex

/-- The integral potential for any natural metric, with no positivity assumption. -/
noncomputable def chipPotential (hConnected : graph_connected target) (hGenus : genus target = 0)
    (length : target.edges → ℕ) (root anchor : target.V) : target.V → ℤ :=
  integrate (fun edge ↦ chipSlope data hConnected hGenus root anchor edge * (length edge : ℤ))

theorem chipPotential_rise (hConnected : graph_connected target) (hGenus : genus target = 0)
    (length : target.edges → ℕ) (root anchor : target.V) (edge : target.edges) :
    chipPotential data hConnected hGenus length root anchor (edge : target.V × target.V).2 -
      chipPotential data hConnected hGenus length root anchor (edge : target.V × target.V).1 =
        chipSlope data hConnected hGenus root anchor edge * (length edge : ℤ) :=
  integrate_rise hConnected hGenus _ edge

end DraismaVargas.Count.TreeMetricPotential
