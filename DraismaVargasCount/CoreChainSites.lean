module

public import DraismaVargasCount.CountSchedule
public import Utilities.CubicGraphs.CoreOfDarts

@[expose] public section

/-!
# The outer half of the count schedule: a chain of sites over a chain of cores

**Source.**  Vargas, Part II (arXiv:2609.09109), the section on invariance of the count
under continuous deformation (`sec-deformation-invariance`) and the proof of the main theorem:
from the caterpillar base to any general `y` over any connected cubic genus-six core, a chain
of cubic types, one link per type change.

`CountSchedule` proves the in-cone half of the propagation (step 4 of the genus-six
assembly), and its `Site.odd_of_reflTransGen` takes the chain of cores as a
`Relation.ReflTransGen` of links.  `CoreOfDarts.exists_chain` supplies the chain of cores:
the Whitehead chain of `CubicDartGraph`s descends verbatim to a chain of `Core`s.  This file
spends that chain on `CountSchedule.Site`.

## What is proved here

* `siteOf` -- a bundled connected cubic core plus a request is a
  `CountSchedule.Site`.
* `StepSupply` -- the hypothesis that one Whitehead step of cores can be crossed
  by the count: from any request over the first core there is *some* request
  over the second with a `CountTransportLink.CountLink` between them.  It is a hypothesis
  of the general statements below; the genus-six assembly does not use it in this
  unrestricted form, but crosses each step with positive general requests
  (`SimpleWallSupply.exists_siteChain_positive`).
* `exists_siteChain_of_coreChain` -- **the composition**: a finite chain of core
  Whitehead steps plus `StepSupply` gives a
  `Relation.ReflTransGen CountSchedule.Site.Link` between the two sites.  This
  is the object `CountSchedule.Site.odd_of_reflTransGen` consumes.
* `exists_siteChain` -- the same, with the chain produced rather than assumed:
  for *any* two connected cubic cores of the same genus at least two, a site
  chain from one to a core that is a **relabelling** (`CoreOfDarts.CoreIso`) of
  the other.
* `RelabelInvariant` -- the one further obligation, named: the count is
  unchanged by a relabelling of the core together with the matching
  relabelling of the request.  It is proved in `CoreRelabelInvariance`
  (`CoreRelabel.relabelInvariant`).
* `exists_siteChain_to_target`, `odd_of_chain` -- assuming `RelabelInvariant`
  the chain reaches the requested core itself, and oddness of the count
  transports along it.

## What `StepSupply` packages

A step of the chain is crossed, in the Draisma--Vargas argument, by marching
inside the current cone to a facet and then crossing the type change:

* the in-cone march is `CountSchedule.Schedule.transport`, whose own `link`
  hypothesis is the parity of the count across a trivalent wall (step 2 of the
  assembly); `CountSchedule.Schedule.siteLink` is precisely a producer of the shape
  `StepSupply` asks for, once that parity is available;
* the type change itself is step 3 of the assembly.

`StepSupply` therefore packages both and asserts neither.  Note what it
deliberately does *not* do: it does not weight or multiply the count.
`CountTransportLink.CountLink` is an `Iff` of `Odd`, neutral between a trivalent
and a non-trivalent wall by design, so nothing here assumes the walls along the
chain are trivalent.

## What is not proved here

* **`StepSupply`**, as just described.  Every theorem below that produces a site
  chain takes it as a hypothesis.
* **`RelabelInvariant`**, which is proved in `CoreRelabelInvariance`.
  `CoreOfDarts.exists_chain` ends at a core `CoreIso`-related to the target,
  because a Whitehead move precomposes the vertex map with a transposition of
  darts and never permutes vertex *labels*, while
  `Infrastructure.CubicDarts.reachesIso_of_genus_eq` concludes only
  `ReachesIso`.  `CoreOfDarts.coreIsoOfIso` and `CoreOfDarts.CoreIso.toIso`
  show that `CoreIso` is exactly what remains, so `RelabelInvariant` is stated at
  exactly the needed strength and not stronger.  It is an equivariance
  statement about `GeometricFibre.openOddCount` under a slot permutation, a
  vertex permutation and per-slot orientation flips; `exists_siteChain` is stated
  without it.
* `exists_siteChain` and below assume `2 ≤ p + 1 - n`, the genus bound of
  `reachesIso_of_genus_eq`.
* No genericity of the requests is assumed or provided here: the requests along
  the chain are whatever `StepSupply` hands back.  Genericity is
  `CountSchedule.Schedule.general` and lives in the in-cone half.
* `openOddCount` throughout is `Count.GeometricFibre.openOddCount`.
-/

namespace DraismaVargas.Count.CoreChainSites

open DraismaVargas.LocalCases.CoreOfDarts
open DraismaVargas.Count.CountSchedule
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ}

/-! ## 1.  Sites over bundled cores -/

/-- A connected cubic core together with a request is a site of the count. -/
def siteOf (degree : ℕ) (c : CubicCore n p) (y : Fin p → ℚ) : Site degree where
  vertices := n
  slots := p
  core := c.core
  request := y

@[simp] theorem siteOf_core (degree : ℕ) (c : CubicCore n p) (y : Fin p → ℚ) :
    (siteOf degree c y).core = c.core := rfl

@[simp] theorem siteOf_request (degree : ℕ) (c : CubicCore n p) (y : Fin p → ℚ) :
    (siteOf degree c y).request = y := rfl

@[simp] theorem siteOf_openOddCount (degree : ℕ) (c : CubicCore n p) (y : Fin p → ℚ) :
    (siteOf degree c y).openOddCount = GeometricFibre.openOddCount c.core y degree := rfl

/-! ## 2.  The hypothesis one Whitehead step costs -/

/-- **What one Whitehead step of cores costs the count**: the parity across the trivalent
walls of a cone and across a type change, together.  From any request over the first core
there is some request over the second carrying a `CountLink`.  It is a hypothesis of every
theorem below that uses it. -/
def StepSupply (degree n p : ℕ) : Prop :=
  ∀ c c' : CubicCore n p, Step c c' → ∀ y : Fin p → ℚ, ∃ y' : Fin p → ℚ,
    CountTransportLink.CountLink degree c.core y c'.core y'

/-! ## 3.  The composition -/

/-- **A chain of cores becomes a chain of sites.**  This is the object
`CountSchedule.Site.odd_of_reflTransGen` consumes. -/
theorem exists_siteChain_of_coreChain (hsupply : StepSupply degree n p)
    {c c' : CubicCore n p} (h : Relation.ReflTransGen Step c c') (y : Fin p → ℚ) :
    ∃ y' : Fin p → ℚ, Relation.ReflTransGen (Site.Link (degree := degree))
      (siteOf degree c y) (siteOf degree c' y') := by
  induction h with
  | refl => exact ⟨y, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨u, hchain⟩ := ih
      obtain ⟨v, hlink⟩ := hsupply _ _ hstep u
      exact ⟨v, hchain.tail hlink⟩

/-- **The outer half of the schedule, with the chain produced.**  Between any
two connected cubic cores of genus at least two there is a site chain, ending
over a core that is a relabelling of the requested one.

The `CoreIso` is described in the module docstring; it is removed by
`RelabelInvariant` in `exists_siteChain_to_target`. -/
theorem exists_siteChain (hsupply : StepSupply degree n p) (hGenus : 2 ≤ p + 1 - n)
    (c c' : CubicCore n p) (y : Fin p → ℚ) :
    ∃ (c'' : CubicCore n p) (y' : Fin p → ℚ), Nonempty (CoreIso c''.core c'.core) ∧
      Relation.ReflTransGen (Site.Link (degree := degree))
        (siteOf degree c y) (siteOf degree c'' y') := by
  obtain ⟨c'', hchain, hiso⟩ := exists_chain c c' hGenus
  obtain ⟨y', hsite⟩ := exists_siteChain_of_coreChain hsupply hchain y
  exact ⟨c'', y', hiso, hsite⟩

/-! ## 4.  Relabelling invariance, named -/

/-- **The one obligation left by the chain**: `openOddCount` is a relabelling
invariant.  A `CoreIso` carries slot `e` to `slot e`, so the request matching
`y` over the relabelled core is `y ∘ slot.symm`.

It is proved in `CoreRelabelInvariance` (`CoreRelabel.relabelInvariant`).  It is
exactly what `CoreOfDarts.exists_chain` leaves: no weaker statement removes the `CoreIso`,
and by `CoreOfDarts.CoreIso.toIso` no stronger one is needed. -/
def RelabelInvariant (degree : ℕ) : Prop :=
  ∀ {n p : ℕ} {c c' : Core n p} (i : CoreIso c c') (y : Fin p → ℚ),
    GeometricFibre.openOddCount c y degree =
      GeometricFibre.openOddCount c' (fun e ↦ y (i.slot.symm e)) degree

/-- Under `RelabelInvariant` the chain reaches the requested core itself. -/
theorem exists_siteChain_to_target (hinv : RelabelInvariant degree)
    (hsupply : StepSupply degree n p) (hGenus : 2 ≤ p + 1 - n)
    (c c' : CubicCore n p) (y : Fin p → ℚ) :
    ∃ y' : Fin p → ℚ, Relation.ReflTransGen (Site.Link (degree := degree))
      (siteOf degree c y) (siteOf degree c' y') := by
  obtain ⟨c'', y'', ⟨i⟩, hchain⟩ := exists_siteChain hsupply hGenus c c' y
  refine ⟨fun e ↦ y'' (i.slot.symm e), hchain.tail ?_⟩
  show CountTransportLink.CountLink degree c''.core y'' c'.core fun e ↦ y'' (i.slot.symm e)
  rw [CountTransportLink.CountLink, hinv i y'']

/-- **The consequence the schedule wanted**: oddness of the count transports
from any connected cubic core of genus at least two to any other, given the two
named hypotheses. -/
theorem odd_of_chain (hinv : RelabelInvariant degree) (hsupply : StepSupply degree n p)
    (hGenus : 2 ≤ p + 1 - n) (c c' : CubicCore n p) (y : Fin p → ℚ)
    (hodd : Odd (GeometricFibre.openOddCount c.core y degree)) :
    ∃ y' : Fin p → ℚ, Odd (GeometricFibre.openOddCount c'.core y' degree) := by
  obtain ⟨y', hchain⟩ := exists_siteChain_to_target hinv hsupply hGenus c c' y
  exact ⟨y', Site.odd_of_reflTransGen hchain hodd⟩

end DraismaVargas.Count.CoreChainSites
