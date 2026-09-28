import DraismaVargasCount.TransportedChipEndgame
import DraismaVargasCount.RowHairpinPosition

/-!
# Helper facts for the genus-six odd-subdivision witness

The genus-six odd-subdivision witness (`DraismaVargas.Count.genusSix_witness`, step 5 of
`Assembly`) has the shape

```
∀ H : CFGraph.{u}, graph_connected H → genus H = 6 →
  ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
    BNExists (Gonality.regularSubdivision H N hN) 1 4
```

and the genus-six Brill--Noether existence theorem consumes it.  This file records the
facts the endgame (`CorePencilCoverProducer`) uses to reach that shape from a closed
fibre member of odd multiplicity.

## Two facts that make the final shape free

Both are checked here rather than asserted.

* `regularSubdivision_eq_scale_graph` --
  `Utilities.Gonality.regularSubdivision H N hN` is **definitionally**
  `((UnitSubdivisionPresentation.spec H).scale N hN).graph`.  No transport lemma is
  needed between the two spellings; `rfl` does it.
* **There is no universe obstruction.**  `regularSubdivision` has type
  `CFGraph.{u} → (k : ℕ) → 0 < k → CFGraph.{0}`: the subdivided graph is built
  from `Fin`-indexed data (`UnitSubdivisionPresentation.spec H` is a
  `Spec (Fintype.card H.V) H.edges.card`) and so always lands in universe zero,
  which is where the whole count lives (`FibreMember.target : CFGraph.{0}`).
  The witness may therefore be proved for `H` in **any** universe by a count
  that only ever sees `CFGraph.{0}`.

## What is proved

* `exists_eq_two_pow_mul_odd_pos` -- the odd part of a positive natural,
  packaged with positivity: `k = 2 ^ a * N` with `N` odd and positive.  The endgame
  applies it to the member's own realization scale `memberScale member`, so that the
  subdivision it produces has odd order `N`.
* `regularSubdivision_eq_scale_graph` -- as above.
* `exists_internal_root`, `edges_card_pos_of_genus_six` -- an internal root of the
  member's target tree, unconditionally: the zeroth vertex of any stable row is a path
  end and `RowHairpinPosition.start_not_leaf` says a path end is never a target leaf, so
  the only input is `0 < p`, which `edges_card_pos_of_genus_six` supplies for the unit
  subdivision specification of a genus-six graph.
-/

namespace DraismaVargas.Count.OddWitness

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph

universe u

/-- **The odd part of a positive natural**, in the shape the endgame uses:
`k = 2 ^ a * N` with `N` odd and positive. -/
theorem exists_eq_two_pow_mul_odd_pos {k : ℕ} (hk : 0 < k) :
    ∃ a N : ℕ, 0 < N ∧ Odd N ∧ k = 2 ^ a * N := by
  obtain ⟨a, N, hodd, hfac⟩ := Nat.exists_eq_two_pow_mul_odd hk.ne'
  refine ⟨a, N, ?_, hodd, hfac⟩
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · exact absurd hodd (by simp)
  · exact hpos

/-- **`regularSubdivision` is the scaled specification graph, definitionally.**
Recorded as a theorem so that the identification the assembly relies on is a
checked fact and not a reading of two definitions. -/
theorem regularSubdivision_eq_scale_graph (H : CFGraph.{u}) (N : ℕ) (hN : 0 < N) :
    Utilities.Gonality.regularSubdivision H N hN =
      ((UnitSubdivisionPresentation.spec H).scale N hN).graph := rfl

/-! ## An internal root -/

/-- **An internal root always exists**, as soon as the core has a slot.  The
zeroth vertex of any stable row is a path end, and
`RowHairpinPosition.start_not_leaf` says a path end never projects to a target
leaf.  No genus, cubicity, connectivity, closedness or multiplicity hypothesis
is used. -/
theorem exists_internal_root {n p degree : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} {y : Fin p → ℚ}
    (member : FibreMember core y degree) (hp : 0 < p) :
    ∃ root : member.target.V, ¬ IsLeafVertex member.target root := by
  have hne : Nonempty (DraismaVargas.LocalCases.W4StableSource.StablePath member.data) :=
    ⟨member.ident.row.symm ⟨0, hp⟩⟩
  obtain ⟨path⟩ := hne
  exact ⟨(RowPosition.rowVertex member.fullDim path 0).1.1,
    RowHairpinPosition.start_not_leaf member.fullDim path⟩

/-- At genus six a graph has at least six edge occurrences, so
`exists_internal_root`'s hypothesis is automatic for `UnitSubdivisionPresentation.spec`.
`genus` is `|E| - |V| + 1` over `ℤ` and `|V|` is positive. -/
theorem edges_card_pos_of_genus_six (H : CFGraph.{u}) (hgenus : genus H = 6) :
    0 < Multiset.card H.edges := by
  have hV : 0 < Fintype.card H.V := Fintype.card_pos
  have hgen : (Multiset.card H.edges : ℤ) - Fintype.card H.V + 1 = 6 := hgenus
  have hpos : (0 : ℤ) < Multiset.card H.edges := by
    have : (0 : ℤ) < Fintype.card H.V := by exact_mod_cast hV
    omega
  exact_mod_cast hpos

end DraismaVargas.Count.OddWitness
