import Utilities.Subdivision.DegenerateSubdivisionIso
import Utilities.Subdivision.LaplacianEquivSeparator

/-!
# Reaching a vertex transports along a closed-face relabeling

`DegSpec.Relabeling` already transports `BNExists`
(`DegenerateSubdivisionIso.bnExists_iff`).  A row proof, however, is assembled
one *vertex* at a time: `Guarding.GuardingSet.guard` asks for
`StrongSeparator.Reaches d.graph D (d.coreVertex v)` at each chip-free `v`.
This file adds the missing per-vertex transport, so a picture proved at one
core vertex can be moved to its image under a core automorphism instead of
being written out again.

`Reaches G D v` unfolds to `winnable G (D - one_chip v)`, so the whole
transport is `LaplacianEquiv.winnable_mapDiv_iff` plus the observation that
`mapDiv` sends `one_chip v` to `one_chip (φ v)`.  The second half,
`mapDiv_coreClassDivisor`, says that a core-supported divisor transports to the
core-supported divisor of the reindexed weight; that is the only place where
the class bijection has to be matched with a permutation of core vertices.

Layering: `Utilities` only, and additive — nothing existing is modified.
-/

namespace Utilities.Certificate

open Utilities
open Utilities.Certificate.StrongSeparator

universe u v

/-! ## One chip, and reaching, along a Laplacian equivalence -/

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- **Reaching a vertex is a relabeling-invariant statement.**

`LaplacianEquiv.mapDiv_one_chip` and `mapDiv_sub`
(`Utilities/Subdivision/LaplacianEquiv.lean:105,96`) already do all the work;
this is the `Reaches` reading of `winnable_mapDiv_iff`. -/
theorem LaplacianEquiv.reaches_mapDiv_iff (φ : LaplacianEquiv G H)
    (D : CFDiv G) (x : G.V) :
    Reaches H (φ.mapDiv D) (φ.toEquiv x) ↔ Reaches G D x := by
  unfold Reaches
  rw [← φ.mapDiv_one_chip x, ← φ.mapDiv_sub, φ.winnable_mapDiv_iff]

end Utilities.Certificate

namespace Utilities.Certificate.DegenerateSpec.DegSpec

open Utilities
open Utilities.Certificate.StrongSeparator

variable {n p n' p' : ℕ} (source : DegSpec n p) (target : DegSpec n' p')

namespace Relabeling

variable (r : Relabeling source target)

/-- **Reaching a vertex transports along a closed-face relabeling.** -/
theorem reaches_iff (D : CFDiv source.graph) (x : source.Vertex) :
    Reaches target.graph ((laplacianEquiv source target r).mapDiv D)
        (vertexEquiv source target r x) ↔
      Reaches source.graph D x :=
  (laplacianEquiv source target r).reaches_mapDiv_iff D x

/-- A core-supported divisor transports to the core-supported divisor of the
reindexed weight, once the class bijection is matched with a permutation `π`
of core vertices. -/
theorem mapDiv_coreClassDivisor (π : Fin n ≃ Fin n')
    (hπ : ∀ u : Fin n,
      vertexEquiv source target r (source.coreVertex u) = target.coreVertex (π u))
    (w : Fin n → ℤ) (w' : Fin n' → ℤ) (hw : ∀ u : Fin n, w u = w' (π u)) :
    (laplacianEquiv source target r).mapDiv (source.coreClassDivisor w)
      = target.coreClassDivisor w' := by
  classical
  -- the class bijection is compatible with `π`
  have hclass : ∀ u₁ u₂ : Fin n,
      target.rep (π u₁) = target.rep (π u₂) ↔ source.rep u₁ = source.rep u₂ := by
    intro u₁ u₂
    rw [← target.coreVertex_eq_iff, ← hπ, ← hπ, ← source.coreVertex_eq_iff]
    exact (vertexEquiv source target r).injective.eq_iff
  funext y
  rcases y with cls | interior
  · obtain ⟨c, hc⟩ := cls
    have hVertex : (Sum.inl ⟨c, hc⟩ : target.Vertex) = target.coreVertex c := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hc.symm
    rw [hVertex]
    obtain ⟨u, hu⟩ := π.surjective c
    subst hu
    have hsymm : (laplacianEquiv source target r).toEquiv.symm
        (target.coreVertex (π u)) = source.coreVertex u := by
      rw [← hπ u]
      exact (laplacianEquiv source target r).toEquiv.symm_apply_apply _
    show source.coreClassDivisor w
        ((laplacianEquiv source target r).toEquiv.symm
          (target.coreVertex (π u))) = _
    rw [hsymm, source.coreClassDivisor_coreVertex,
      target.coreClassDivisor_coreVertex]
    refine Finset.sum_nbij' (fun v => π v) (fun v' => π.symm v') ?_ ?_ ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact (hclass v u).mpr hv
    · intro v' hv'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv' ⊢
      refine (hclass (π.symm v') u).mp ?_
      rw [π.apply_symm_apply]
      exact hv'
    · intro v _; simp
    · intro v' _; simp
    · intro v _; exact hw v
  · obtain ⟨e, o⟩ := interior
    -- an interior vertex has an interior preimage, so both sides vanish
    show source.coreClassDivisor w
        ((laplacianEquiv source target r).toEquiv.symm (Sum.inr ⟨e, o⟩)) = _
    rcases hz : (laplacianEquiv source target r).toEquiv.symm
        (Sum.inr ⟨e, o⟩) with cls | inte
    · exfalso
      have hback := congrArg (laplacianEquiv source target r).toEquiv hz
      rw [Equiv.apply_symm_apply] at hback
      simp [laplacianEquiv, vertexEquiv] at hback
    · rfl

end Relabeling

end Utilities.Certificate.DegenerateSpec.DegSpec
