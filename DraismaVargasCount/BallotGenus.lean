import DraismaVargasCount.BallotDatum

/-!
# The source of the ballot-parametrized caterpillar has genus `g`

The Euler count of `Count.BallotDatum.ballotDatum m s`, which completes the validity of the
ballot-parametrized caterpillar datum.  Every partition of that datum is a star
partition, so the number of source vertices over a target vertex is
`d + 1 - |block|` and likewise for occurrences, and the whole count reduces to
two sums of block sizes over `range (6m+4)` and `range (6m+3)`.

Grouping those sums three at a time -- one leaf edge, one spine edge and one
stem per lollipop -- gives

```
∑ vertex blocks = 9m + T + 8,     ∑ occurrence blocks = 6m + T + 4,
T = s_1 + s_2 + … + s_{g-2},
```

so the slope sum `T` **cancels** and the genus is `2m + 2 = g` for every
ballot sequence.  The one input is `2 max (s_{i-1}, s_i) = s_{i-1} + s_i + 1`
(`two_mul_sum_max`), summed over the spine, together with the boundary values
`s_1 = s_{g-1} = 2` which make the two shifted slope windows agree
(`sum_slope_shift`).

## What is proved

* `card_sourceVertex_add`, `card_sourceEdge_add` -- the two Euler counts,
  stated additively so that no truncated subtraction occurs.
* `sum_qv`, `sum_pe` -- the two block-size sums in closed form.
* `genus_sourceGraph_ballotDatum : genus (ballotDatum m s).sourceGraph = 2m+2`.
* `saturated_ballotDatum` -- `3g - 3 = 2g + 2d - 5`, the `saturated` field of
  `FullDimensionalSourcePresentation`, for every slope sequence.

## What is not proved here

* Nothing beyond the two cardinalities and the genus.  `saturated_ballotDatum`
  is one field of `FullDimensionalSourcePresentation`; the others
  (`labelling`, `det_ne_zero`, `trivalent`, `pathEnds`, …) are supplied by
  `BallotFullDimensional` and `BallotValency`, and are not touched here.  No `FibreMember`
  is constructed.
* The genus statement says nothing about which morphisms exist: it is the
  Euler characteristic of the source of *this* datum.  That every morphism over the
  caterpillar comes from a ballot datum is `CaterpillarAllMembers`.
* As in `Count.BallotDatum`, the hypothesis `g = 2 * (m + 1)` lives in the type
  of `s` and no genericity hypothesis on edge lengths is used or supplied.
-/
namespace DraismaVargas.Count.BallotDatum

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.Count

variable {m : ℕ}

/-! ## 1.  The two block-size functions -/

/-- The number of sheets glued at the target vertex numbered `a`. -/
def qv (m : ℕ) (s : Slopes (2 * (m + 1))) (a : ℕ) : ℕ :=
  ((Finset.range (m + 2)).filter (VertPred m s a)).card

/-- The number of sheets glued along the target occurrence numbered `e`. -/
def pe (m : ℕ) (s : Slopes (2 * (m + 1))) (e : ℕ) : ℕ :=
  ((Finset.range (m + 2)).filter (EdgePred m s e)).card

theorem qv_le (m : ℕ) (s : Slopes (2 * (m + 1))) (a : ℕ) : qv m s a ≤ m + 2 := by
  have := Finset.card_filter_le (Finset.range (m + 2)) (VertPred m s a)
  rwa [Finset.card_range] at this

theorem pe_le (m : ℕ) (s : Slopes (2 * (m + 1))) (e : ℕ) : pe m s e ≤ m + 2 := by
  have := Finset.card_filter_le (Finset.range (m + 2)) (EdgePred m s e)
  rwa [Finset.card_range] at this

theorem card_blocks_vertexPartition_ballot (m : ℕ) (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) :
    Fintype.card ((ballotDatum m s).vertexPartition v).Blocks
      = (m + 2) + 1 - qv m s v.val :=
  card_blocks_catStar _ (vertPred_zero s _)

theorem card_blocks_edgePartition_ballot (m : ℕ) (s : Slopes (2 * (m + 1)))
    (i : Fin (6 * m + 3)) :
    Fintype.card ((ballotDatum m s).edgePartition (occ m i)).Blocks
      = (m + 2) + 1 - pe m s i.val := by
  rw [ballotDatum_edgePart_occ]
  exact card_blocks_catStar _ (edgePred_zero s _)

/-! ## 2.  The two Euler counts, in a form with no truncated subtraction -/

theorem card_sourceVertex_add (m : ℕ) (s : Slopes (2 * (m + 1))) :
    Fintype.card (ballotDatum m s).SourceVertex
        + ∑ a ∈ Finset.range (6 * m + 4), qv m s a
      = (6 * m + 4) * (m + 3) := by
  rw [GluingDatum.card_sourceVertex_eq_sum_card_blocks,
    Finset.sum_congr rfl (fun v _ => card_blocks_vertexPartition_ballot m s v),
    show (∑ a ∈ Finset.range (6 * m + 4), qv m s a)
      = ∑ v : (catTree m).V, qv m s v.val from
      (Fin.sum_univ_eq_sum_range (fun a => qv m s a) (6 * m + 4)).symm,
    ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun v _ => show ((m + 2) + 1 - qv m s v.val) + qv m s v.val
      = m + 3 by have := qv_le m s v.val; omega),
    Finset.sum_const, Finset.card_univ, card_vertices_catTree, smul_eq_mul]

theorem card_sourceEdge_add (m : ℕ) (s : Slopes (2 * (m + 1))) :
    Fintype.card (ballotDatum m s).SourceEdge
        + ∑ e ∈ Finset.range (6 * m + 3), pe m s e
      = (6 * m + 3) * (m + 3) := by
  rw [GluingDatum.card_sourceEdge_eq_sum_card_blocks]
  have hEquiv := Fintype.sum_equiv (catEdgeEquiv m)
    (fun i : Fin (6 * m + 3) =>
      Fintype.card ((ballotDatum m s).edgePartition (occ m i)).Blocks)
    (fun e : (catTree m).edges =>
      Fintype.card ((ballotDatum m s).edgePartition e).Blocks)
    (fun _ => rfl)
  rw [← hEquiv,
    Finset.sum_congr rfl (fun i _ => card_blocks_edgePartition_ballot m s i),
    show (∑ e ∈ Finset.range (6 * m + 3), pe m s e)
      = ∑ i : Fin (6 * m + 3), pe m s i.val from
      (Fin.sum_univ_eq_sum_range (fun e => pe m s e) (6 * m + 3)).symm,
    ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun i _ => show ((m + 2) + 1 - pe m s i.val) + pe m s i.val
      = m + 3 by have := pe_le m s i.val; omega),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## 3.  The two block-size sums, grouped three at a time -/

/-- Summing over `range (3n)` in blocks of three. -/
theorem sum_range_three (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (3 * n), f i
      = ∑ t ∈ Finset.range n, (f (3 * t) + f (3 * t + 1) + f (3 * t + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

/-- The value of `pe` at each of the three occurrences of one lollipop block. -/
theorem pe_triple (m : ℕ) (s : Slopes (2 * (m + 1))) {t : ℕ} (ht : t < 2 * m) :
    pe m s (3 * t) + pe m s (3 * t + 1) + pe m s (3 * t + 2)
      = 3 + s.slope (t + 1) := by
  have h0 : pe m s (3 * t) = 1 := card_edgePred_leaf s (Or.inl (by omega))
  have h1 : pe m s (3 * t + 1) = s.slope (t + 1) := by
    rw [pe, card_edgePred_spine s (show (3 * t + 1) % 3 = 1 by omega),
      show (3 * t + 1 + 2) / 3 = t + 1 by omega]
  have h2 : pe m s (3 * t + 2) = 2 :=
    card_edgePred_stem s (by omega) (by omega)
  rw [h0, h1, h2]
  ring

theorem pe_triple_last (m : ℕ) (s : Slopes (2 * (m + 1))) :
    pe m s (3 * (2 * m)) + pe m s (3 * (2 * m) + 1) + pe m s (3 * (2 * m) + 2) = 4 := by
  have h0 : pe m s (3 * (2 * m)) = 1 := card_edgePred_leaf s (Or.inl (by omega))
  have h1 : pe m s (3 * (2 * m) + 1) = 2 := by
    rw [pe, card_edgePred_spine s (show (3 * (2 * m) + 1) % 3 = 1 by omega),
      show (3 * (2 * m) + 1 + 2) / 3 = 2 * m + 1 by omega,
      Slopes.slope_of_ge s (show 2 * (m + 1) - 1 ≤ 2 * m + 1 by omega)]
  have h2 : pe m s (3 * (2 * m) + 2) = 1 :=
    card_edgePred_leaf s (Or.inr (by omega))
  rw [h0, h1, h2]

/-- The value of `qv` at each of the three vertices of one lollipop block. -/
theorem qv_triple (m : ℕ) (s : Slopes (2 * (m + 1))) (t : ℕ) :
    qv m s (3 * t) + qv m s (3 * t + 1) + qv m s (3 * t + 2)
      = 4 + max (s.slope (t + 1)) (s.slope (t + 2)) := by
  have h0 : qv m s (3 * t) = 2 := card_vertPred_pair s (by omega)
  have h1 : qv m s (3 * t + 1) = 2 := card_vertPred_pair s (by omega)
  have h2 : qv m s (3 * t + 2)
      = max (s.slope (t + 1)) (s.slope (t + 2)) := by
    rw [qv, card_vertPred_junction s (show (3 * t + 2) % 3 = 2 by omega),
      show lolli (3 * t + 2) = t + 2 by unfold lolli; omega,
      show t + 2 - 1 = t + 1 by omega]
  rw [h0, h1, h2]

theorem qv_triple_last (m : ℕ) (s : Slopes (2 * (m + 1))) :
    qv m s (3 * (2 * m)) + qv m s (3 * (2 * m) + 1) + qv m s (3 * (2 * m) + 2) = 6 := by
  have h0 : qv m s (3 * (2 * m)) = 2 := card_vertPred_pair s (by omega)
  have h1 : qv m s (3 * (2 * m) + 1) = 2 := card_vertPred_pair s (by omega)
  have h2 : qv m s (3 * (2 * m) + 2) = 2 := by
    rw [qv, card_vertPred_junction s (show (3 * (2 * m) + 2) % 3 = 2 by omega),
      show lolli (3 * (2 * m) + 2) = 2 * m + 2 by unfold lolli; omega,
      Slopes.slope_of_ge s (show 2 * (m + 1) - 1 ≤ 2 * m + 2 - 1 by omega),
      Slopes.slope_of_ge s (show 2 * (m + 1) - 1 ≤ 2 * m + 2 by omega), max_self]
  rw [h0, h1, h2]

/-! ## 4.  The one identity that makes the genus independent of the slopes -/

/-- Shifting the window of the slope sum by one changes nothing, because
`s_1 = s_{g-1} = 2`. -/
theorem sum_slope_shift (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (∑ t ∈ Finset.range (2 * m), s.slope (t + 1))
      = ∑ t ∈ Finset.range (2 * m), s.slope (t + 2) := by
  have hlast : s.slope (2 * m + 1) = 2 :=
    Slopes.slope_of_ge s (show 2 * (m + 1) - 1 ≤ 2 * m + 1 by omega)
  have hone : s.slope 1 = 2 := Slopes.slope_one s
  have hA : (∑ t ∈ Finset.range (2 * m + 1), s.slope (t + 1))
      = (∑ t ∈ Finset.range (2 * m), s.slope (t + 1)) + s.slope (2 * m + 1) :=
    Finset.sum_range_succ (fun t => s.slope (t + 1)) (2 * m)
  have hB : (∑ t ∈ Finset.range (2 * m + 1), s.slope (t + 1))
      = (∑ t ∈ Finset.range (2 * m), s.slope (t + 2)) + s.slope 1 :=
    Finset.sum_range_succ' (fun t => s.slope (t + 1)) (2 * m)
  rw [hlast] at hA
  rw [hone] at hB
  omega

/-- **`2 max (s_{i-1}, s_i) = s_{i-1} + s_i + 1`, summed over the spine.** -/
theorem two_mul_sum_max (m : ℕ) (s : Slopes (2 * (m + 1))) :
    2 * (∑ t ∈ Finset.range (2 * m), max (s.slope (t + 1)) (s.slope (t + 2)))
      = (∑ t ∈ Finset.range (2 * m), s.slope (t + 1))
        + (∑ t ∈ Finset.range (2 * m), s.slope (t + 2)) + 2 * m := by
  rw [Finset.mul_sum]
  have hcongr : ∀ t ∈ Finset.range (2 * m),
      2 * max (s.slope (t + 1)) (s.slope (t + 2))
        = s.slope (t + 1) + s.slope (t + 2) + 1 := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hstep : SlopeStepRel (s.slope (t + 1)) (s.slope (t + 2)) :=
      Slopes.slope_rel s (i := t + 1) (by omega)
        (show (t + 1) + 1 ≤ 2 * (m + 1) - 1 by omega)
    have hpos := Slopes.one_le_slope s (t + 1)
    have hpos' := Slopes.one_le_slope s (t + 2)
    rcases hstep with h | h
    · rw [max_eq_right (by omega)]; omega
    · rw [max_eq_left (by omega)]; omega
  rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-! ## 5.  The two sums, and the genus -/

theorem sum_pe (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (∑ e ∈ Finset.range (6 * m + 3), pe m s e)
      = 6 * m + (∑ t ∈ Finset.range (2 * m), s.slope (t + 1)) + 4 := by
  rw [show 6 * m + 3 = 3 * (2 * m + 1) by ring, sum_range_three,
    Finset.sum_range_succ,
    Finset.sum_congr rfl (fun t ht => pe_triple m s (Finset.mem_range.mp ht)),
    pe_triple_last, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  ring

theorem sum_qv (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (∑ a ∈ Finset.range (6 * m + 4), qv m s a)
      = 9 * m + (∑ t ∈ Finset.range (2 * m), s.slope (t + 1)) + 8 := by
  have hlast : qv m s (6 * m + 3) = 2 := card_vertPred_pair s (by omega)
  have hshift := sum_slope_shift m s
  have hmax := two_mul_sum_max m s
  rw [show 6 * m + 4 = (6 * m + 3) + 1 by ring, Finset.sum_range_succ, hlast,
    show 6 * m + 3 = 3 * (2 * m + 1) by ring, sum_range_three,
    Finset.sum_range_succ,
    Finset.sum_congr rfl (fun t _ => qv_triple m s t),
    qv_triple_last, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  omega

/-- **The source of the ballot-parametrized caterpillar datum has genus
`g = 2m + 2`, for every slope sequence.**  The slope sum cancels between the
vertex and the occurrence count, which is why the genus does not see the
ballot sequence at all. -/
theorem genus_sourceGraph_ballotDatum (m : ℕ) (s : Slopes (2 * (m + 1))) :
    genus (ballotDatum m s).sourceGraph = 2 * (m : ℤ) + 2 := by
  have hV := card_sourceVertex_add m s
  have hE := card_sourceEdge_add m s
  rw [sum_qv m s] at hV
  rw [sum_pe m s] at hE
  have hedges : Multiset.card (ballotDatum m s).sourceGraph.edges =
      Fintype.card (ballotDatum m s).SourceEdge :=
    GluingDatum.sourceGraph_edges_card _
  have hvertices : Fintype.card (ballotDatum m s).sourceGraph.V =
      Fintype.card (ballotDatum m s).SourceVertex :=
    Fintype.card_congr (Equiv.refl _)
  have hgoal : (Fintype.card (ballotDatum m s).SourceEdge : ℤ)
      - (Fintype.card (ballotDatum m s).SourceVertex : ℤ) + 1 = 2 * (m : ℤ) + 2 := by
    have hVZ : (Fintype.card (ballotDatum m s).SourceVertex : ℤ)
        + (9 * (m : ℤ) + (∑ t ∈ Finset.range (2 * m), s.slope (t + 1) : ℕ) + 8)
        = (6 * (m : ℤ) + 4) * ((m : ℤ) + 3) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) hV
    have hEZ : (Fintype.card (ballotDatum m s).SourceEdge : ℤ)
        + (6 * (m : ℤ) + (∑ t ∈ Finset.range (2 * m), s.slope (t + 1) : ℕ) + 4)
        = (6 * (m : ℤ) + 3) * ((m : ℤ) + 3) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) hE
    linarith
  rw [genus, hedges, hvertices]
  exact hgoal

/-- **Full-dimensionality as a number**, `3g - 3 = 2g + 2d - 5` with
`d = g/2 + 1`, for every slope sequence. -/
theorem saturated_ballotDatum (m : ℕ) (s : Slopes (2 * (m + 1))) :
    ((catTree m).edges.card : ℤ)
      = 2 * genus (ballotDatum m s).sourceGraph + 2 * ((m : ℤ) + 2) - 5 := by
  rw [card_edges_catTree, genus_sourceGraph_ballotDatum]
  push_cast
  ring


/-! ## 6.  Consistency with Part I's caterpillar datum -/

/-- **Consistency.**  The genus theorem for Part I's caterpillar datum is the
specialisation of the parametrized one at the distinguished ballot sequence. -/
example (m : ℕ) : genus (caterpillarDatum m).sourceGraph = 2 * (m : ℤ) + 2 := by
  rw [← ballotDatum_zig m]
  exact genus_sourceGraph_ballotDatum m (zig m)

/-- Genus six: the source of every one of the five ballot caterpillars has
genus six. -/
example (s : Slopes 6) : genus (ballotDatum 2 s).sourceGraph = 6 := by
  have h := genus_sourceGraph_ballotDatum 2 s
  norm_num at h
  exact h

end DraismaVargas.Count.BallotDatum
