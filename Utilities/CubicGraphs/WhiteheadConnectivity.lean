module

public import Utilities.CubicGraphs.WhiteheadSlide
public import Utilities.CubicGraphs.WhiteheadPeel
public import Utilities.CubicGraphs.WhiteheadGenusTwo
public import Utilities.CubicGraphs.WhiteheadLoop

@[expose] public section

/-!
# Whitehead connectivity of all connected cubic dart types

Every actual cubic dart graph of genus at least two reaches the caterpillar
of the same genus. This is a genus induction: create a loop by genuine
Whitehead moves, peel it, apply the smaller-genus theorem, and lift the
resulting path while sliding the planted loop to the last spine edge.
The genus-two classification starts the induction. Every ingredient acts
on actual dart graphs, including loops and parallel edges.

Consequently any two such graphs of the same genus are linked, as in the
cubic case of Caporaso's ordinary linkage theorem (Theorem 2.4.3,
arXiv:1001.2815v5). No cycle, loop, peeling or induction data is assumed of
the input. This is connectivity of graph types, as used by Vargas, Part II
(arXiv:2609.09109) through the connectivity of the tropical moduli space in
codimension one; it does not transport charts or metric edge lengths along the
resulting path.
-/

namespace DraismaVargas.Infrastructure.CubicDarts

open CubicDartGraph

universe u v

/-- The induction is polymorphic in the actual finite dart and vertex sets,
so it applies to the literal complement sets produced by peeling. -/
theorem reaches_caterpillar_genus (g : ℕ) :
    ∀ {D : Type u} {V : Type v} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
      (G : CubicDartGraph D V), G.genus = g → 2 ≤ g →
      ReachesIso G (caterpillarDarts g) := by
  induction g using Nat.strong_induction_on with
  | h g ih =>
    intro D V _ _ _ _ G hGenus hg
    by_cases hTwo : g = 2
    · rw [hTwo] at hGenus ⊢
      exact GenusTwo.reachesIso_caterpillar G hGenus
    have hThree : 3 ≤ g := by omega
    obtain ⟨H, hReach, ell, hLoop⟩ := WhiteheadLoop.reaches_loop G (by omega)
    have hHGenus : H.genus = g := hReach.genus_eq.trans hGenus
    obtain ⟨L, _, hPeel, hSmall, _⟩ := exists_peel_of_loop H ell hLoop (by omega)
    have hSmaller : L.peel.genus < g := by omega
    have hInd := ih L.peel.genus hSmaller L.peel rfl hSmall
    have hPlant := plant_reachesIso_caterpillar (L.peel.genus - 2) hInd L.root
    have hIndex : L.peel.genus - 2 + 1 = g - 2 := by omega
    have hPath := ((ReachesIso.of_reaches hReach).trans L.reachesIso_plant_peel).trans hPlant
    change ReachesIso G (caterpillar (g - 2))
    rw [← hIndex]
    exact hPath

variable {D V D' V' : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']

/-- Every connected cubic dart graph of genus at least two reaches the
canonical caterpillar of that genus. -/
theorem reaches_caterpillar (G : CubicDartGraph D V) (hg : 2 ≤ G.genus) :
    ReachesIso G (caterpillarDarts G.genus) :=
  reaches_caterpillar_genus G.genus G rfl hg

/-- Ordinary cubic linkage, allowing loops, parallel edges, and distinct
finite dart/vertex types on the two input graphs. -/
theorem reachesIso_of_genus_eq (G : CubicDartGraph D V) (H : CubicDartGraph D' V')
    (hg : 2 ≤ G.genus) (hEqual : G.genus = H.genus) : ReachesIso G H := by
  have hG := reaches_caterpillar G hg
  have hH := reaches_caterpillar H (by omega)
  rw [← hEqual] at hH
  exact hG.trans hH.symm

example : ReachesIso theta (caterpillarDarts 2) :=
  reaches_caterpillar_genus 2 theta theta_genus (by omega)

example : ReachesIso thetaTwoLollipops (caterpillarDarts 4) := by
  apply reaches_caterpillar_genus 4 thetaTwoLollipops
  · change (plant (plant theta 0) (Sum.inl 0)).genus = 4
    rw [genus_plant, genus_plant, theta_genus]
  · omega

end DraismaVargas.Infrastructure.CubicDarts
