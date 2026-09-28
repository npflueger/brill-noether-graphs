import GenusSixExistence.Existence
import GenusSixExistence.OnceMarked
import GenusSixExistence.Highlights

/-!
# Brill--Noether existence in genus six

Every connected finite graph of genus six satisfies Brill--Noether existence
(`GenusSixExistence.bnExists`), and so does every connected finite graph of genus at most six
(`GenusSixExistence.brillNoetherExistenceThroughSix`, extending the Atanasov--Ranganathan theorem
of the library `LowGenus` by one genus). As a consequence, every connected finite graph of genus
at most five satisfies once-marked Brill--Noether existence at every vertex
(`GenusSixExistence.onceMarkedBNExistenceThroughFive`).

The genus-six theorem combines the conditional theorem
`GenusSixOddDescent.bnExists_genus_six_of_oddWitness` with the odd-subdivision witness
`DraismaVargas.Count.genusSix_witness` of the library `DraismaVargasCount`. The once-marked
theorem attaches a cycle at the marked vertex, applies the genus-six theorem to the resulting
genus-six graph, and collapses the cycle again (`Utilities.bnExists_vertexWedge_one_iff`).

The modules under `GenusSixExistence/OnceMarked/` reduce once-marked existence in genus at most
five to a single diagonal statement; their declarations keep the `MarkedGraphs` namespace.

Add an import line above whenever a module is added under `GenusSixExistence/`, or
`lake build GenusSixExistence` will silently skip it.
-/
