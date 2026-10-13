module

public import Utilities.Transmission.TransmissionCorner
public import Utilities.Transmission.TransmissionShift

@[expose] public section

/-!
# Corner domination under an output shift

`outputShift τ k` (`Utilities.Transmission.TransmissionShift`) moves every slipface row by `k`
in its first coordinate, so corners move the same way: a corner list dominating `τ` after its
first coordinates are shifted by `k` dominates `outputShift τ k`. With the window box lemma
(`Utilities.Window.cornersDominate_of_boxDominates`) this reduces corner domination of any
finite-length permutation, of any shift, to a `decide`.
-/

namespace Utilities

/-- **Corner domination under an output shift.** Shifting outputs by `k` moves every corner by
`k` in its first coordinate. -/
theorem cornersDominate_outputShift (τ : AspPerm) (k : ℤ) (C : List Corner)
    (h : CornersDominate τ (C.map fun c ↦ (c.1 + k, c.2))) :
    CornersDominate (outputShift τ k) C := by
  intro a b
  have hab := h (a + k) b
  rw [outputShift_chi, outputShift_s, show a + 1 + k = a + k + 1 by ring]
  rcases hab with h1 | h2 | ⟨c, hc, h3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl (by omega))
  · obtain ⟨c, hcC, rfl⟩ := List.mem_map.mp hc
    refine Or.inr (Or.inr ⟨c, hcC, ?_⟩)
    unfold cornerBound at h3 ⊢
    simp only at h3
    rw [show c.1 + k - (a + k) = c.1 - a by ring] at h3
    exact h3

end Utilities
