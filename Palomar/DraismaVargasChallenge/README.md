# A rank-one divisor of degree ⌈g/2⌉ + 1 on a subdivision

`Challenge.lean` imports only Mathlib. It defines finite multigraphs, divisors,
chip-firing equivalence, the Baker–Norine rank test, and subdivision with
prescribed edge lengths locally. It then states two theorems whose bodies are
deliberately `sorry`.

## The theorems

1. **`regular_subdivision_gonality_le_ceil_half_genus_add_one`.** Every
   connected finite graph `G` of genus `g` has a regular subdivision (every
   edge replaced by a path of `n ≥ 1` edges) that carries a divisor of degree
   `⌈g/2⌉ + 1` and rank at least one.
   Library declaration:
   `DraismaVargas.graph_regularSubdivisionGonality_le_ceil_half_genus_add_one`.

2. **`common_refinement_gonality_le_ceil_half_genus_add_one`.** Give every edge
   of a connected finite graph `G` of genus `g` a positive integer length. Up to
   scale, this is a metric graph with rational edge lengths. Then for some
   `n ≥ 1`, cutting each edge `e` into `n · length(e)` unit edges gives a graph
   carrying a divisor of degree `⌈g/2⌉ + 1` and rank at least one. Constant
   length one recovers theorem 1.
   Library declaration:
   `DraismaVargas.regularSubdivisionGonality_le_ceil_half_genus_add_one`.

Both are the discrete form of Theorem 1 of [DV1]: the tree gonality of a metric
graph of genus `g` is at most `⌈g/2⌉ + 1`. A tropical morphism of degree `d` to
a tree gives a divisor of degree `d` and rank at least one, so the theorem
bounds divisorial gonality as well. [V2] continues [DV1], and the library's
proof of the even-genus construction follows the route through walls between
cells described there. Odd genus reduces to the next even genus, as in [DV1].
Baker first proved the bound for metric graphs by specialization from
algebraic curves ([Baker], Theorem 3.12). Draisma and Vargas gave a
combinatorial, constructive proof.

## Formulation choices

- **Witness form.** The library states the bound as an inequality: the least
  divisorial gonality over all regular subdivisions of a graph is at most
  `⌈g/2⌉ + 1`. The challenge instead asserts an explicit subdivision and an
  explicit divisor, with no minimum and no infimum. For connected graphs the
  two forms are equivalent. The infimum of a nonempty set of natural numbers
  is attained, and regular subdivisions of connected graphs are connected.
- **Exact degree and lower bound on rank.** The divisor has degree exactly
  `⌈g/2⌉ + 1`. This is equivalent to asking for degree at most `⌈g/2⌉ + 1`,
  because adding chips does not lower the rank. The divisor is not required
  to be effective: every divisor of nonnegative rank is equivalent to an
  effective one.
- **The degree.** It is written `⌈(genus G : ℚ) / 2⌉ + 1`, using Mathlib's
  ceiling on `ℚ`. The genus is the cyclomatic number `|E| − |V| + 1` of `G`,
  which subdivision does not change. The library writes the same number in `ℕ`
  as `(|E| + 2 − |V|) / 2 + 1`.
- **Subdivisions are taken, not avoided.** The bound is claimed on some
  subdivision, not on `G` itself. Baker's conjecture that the bound holds for
  the finite graph `G` itself ([Baker], Conjecture 3.10) is not claimed.
  Divisorial gonality can drop under regular subdivision: the repository's
  tricycle example shows this.
- **Metric graphs are not formalized.** A metric graph with positive integer
  edge lengths is represented by the finite graph together with the lengths.
  The conclusion is read on the unit-edge refinement. For a metric graph with
  integer edge lengths, the least divisorial gonality over these refinements
  equals the divisorial gonality of the metric graph. That identification is a
  theorem in the literature ([vDSW]) and is not formalized here. Tree gonality
  and tropical morphisms are not formalized either.
- **Graphs and lengths.** Graphs are finite, nonempty multigraphs without
  loops. Parallel edges are allowed. A metric graph with a loop is covered
  after a vertex is placed in the interior of the loop. Lengths are assigned to
  edge occurrences (`G.edges → ℕ`), so parallel edges may have different
  lengths. The subdivision construction accepts length zero as a junk value,
  which deletes the edge, but theorem 2 assumes every length is positive. The
  library's own presentation, a core on vertices `Fin n` with `p` numbered edge
  slots, is equivalent.
- **Regular subdivision.** `regularSubdivision G n hn` gives every edge length
  `n * 1`, which is `n` times the unit length. That product equals `n`
  propositionally but not definitionally. The form matches the library's
  scaling of unit lengths definitionally. It is the same construction as the
  regular subdivision in the repository's `HighlightsStatements.lean`, up to
  unfolding definitions.
- **Universes.** Both theorems hold for graphs whose vertex type lies in any
  universe. Subdivisions have vertex type in `Type`.

## References

- [DV1] J. Draisma and A. Vargas, *Catalan-many tropical morphisms to trees;
  Part I: Constructions*, arXiv:1909.12924.
- [V2] A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space
  and a count*, arXiv:2609.09109.
- [Baker] M. Baker, *Specialization of linear systems from curves to graphs*,
  Algebra & Number Theory 2 (2008).
- [vDSW] J. van Dobben de Bruyn, H. Smit and M. van der Wegen, *Discrete and
  metric divisorial gonality can be different*, J. Combin. Theory Ser. A
  (2022); [doi:10.1016/j.jcta.2022.105619](https://doi.org/10.1016/j.jcta.2022.105619).
