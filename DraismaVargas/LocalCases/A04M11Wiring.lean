import DraismaVargas.LocalCases.A04MoreTags
import DraismaVargas.LocalCases.M11CertifiedOpposite
import DraismaVargas.LocalCases.M11HonestGaugeFamily

/-!
# The wall input and the full-dimensional supply at the `w2M11` tag

`A04FourTags` defines `FullDimSupply`, the two fields of
`SemanticAtlasMarch.State.PresentedProgress` that are not derived automatically, read
at one `WallProgress.WallInput`: an outgoing full-dimensional presentation at
every nonsingular member of the wall's family, and the statement that it
presents that member.  It inhabits them for `w3Nd2CoarseFine`,
`w3Nd3CoarseFine` and `w4`; `A04MoreTags` adds `w2P`, `w2Mkk` in both
orientations and `w3Four`, and bundles everything one wall must supply as
`RoutedWall`.  This file treats the tag `w2M11` (Draisma--Vargas Part I, Case
{w2-r2-nd3-M-11}, Figure 32), using `M11HonestGaugeFamily.gaugeFamily`.

| tag | wall input | supply | routed | carried |
|---|---|---|---|---|
| `w2M11` | `ofW2M11` (`WallInput.ofGauge` on `M11HonestGaugeFamily.gaugeFamily`) | `w2M11Supply` | `routedW2M11` | `hChart` |

`hChart` is the **state–classifier equation** and nothing else: that the chart
the march currently occupies is the identified incoming member's own honest
length matrix.  As at `w2P` and `w2Mkk`, it is one named hypothesis and there
are no others, because the three things one would expect to carry are theorems:

1. **`hW25Nodup`** (the presented rows are duplicate-free).  The family presents its members by
   `StableLengthMatrixLabelling.presentation`, so `A04MoreTags.nodup_labelling_path`
   is the whole proof and `RoutedWall.HonestlyPresented` the property.
2. **The outgoing full-dimensional presentations.**
   `M11FullDimensional.outgoingPresentation` is unconditional beyond the
   chosen member's own nonsingularity — the M11 stable-incidence dictionary
   `M11StableGraphs.between` is *proved*, at every position, the remote one
   included, so no `dictionary`/`memberGenus` hypothesis appears here (in
   contrast with `A04MoreTags.w2MkkFirstSupply`, which takes both as
   hypotheses).
3. **The incoming determinant and matrix.**
   `M11CertifiedOpposite.outgoingLabelling_self` says transport to member `0`
   and back is the identity on the identified member's own labelling, so
   `hW25IncomingNonzero` is `M11CertifiedOpposite.incomingDet_ne_zero` and
   `hW25IncomingMatrix` is `hChart` transported.

## Why `presentation_eq` is `rfl`

`M11FullDimensional.outgoingPresentation` is
`StableGraphFullDimensional.presentationOfEquivalence` at the labelling
`M11FullDimensional.outgoingLabelling input profile hCard incoming incomingFD
outgoing`, which is `M11CommonBalance.labelling input profile hCard
(M11FullDimensional.initialLabelling …) outgoing`; and
`presentationOfEquivalence`'s `labelling` field is that argument verbatim.
`m11Family` is `M11HonestGaugeFamily.gaugeFamily` at exactly that `initial`, so
the family's `presentation outgoing` is the same term and the second field of
`FullDimSupply` is literal at each of the three positions, as it is for every
honestly presented tag.  The
`outgoingPresentation` is stated on `M11RemoteCandidates.candidates … outgoing`
and the supply wants `(input.family.candidate outgoing).datum`: those are
definitionally equal position by position (see `M11HonestGaugeFamily`), so no
bridge is needed and none is written.

## What the wall input is

`WallProgress.WallInput.ofGauge` with `case := SourceCase.w2M11`, arity
`rfl : 3 = SourceCase.w2M11.arity`, `hValid := input.valid` — the *incoming*
datum's validity; the remote member's own validity is inside the family, by
`valid_of_old` — and the same `hConnected`/`hGenus`/`root` every tag takes.
The gauge-mixed constructor is needed because the middle member of Figure 32
does not live over `data`: it lives over the branch-swapped copy
`M11RemoteCandidates.swappedDatum`.
-/

namespace DraismaVargas.LocalCases.A04M11Wiring

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallProgress
open DraismaVargas.LocalCases.A04FourTags (FullDimSupply)
open DraismaVargas.LocalCases.A04MoreTags (RoutedWall)
open M11SourceCandidates M11RemoteCandidates M11FullDimensional

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {wall : coordinate}

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wallVertex}
  {block : WallBlock data wallVertex}
  (input : W2SourceInput data star)
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wallVertex).blockCard block.1 = 2)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (M11RemoteCandidates.candidates input profile hCard incoming).datum coordinate)

/-! ## 1.  The wall input -/

/-- Figure 32's honest gauge family in the identified member's own square
coordinates. -/
noncomputable def m11Family :
    GaugeFamily (coordinate := coordinate) 3 data wallVertex :=
  M11HonestGaugeFamily.gaugeFamily input profile hCard hConnected hGenus
    (M11FullDimensional.initialLabelling input profile hCard incoming incomingFD)

/-- **Figure 32's wall input.**  Gauge-mixed: position `1` lives over the
branch-swapped copy `M11RemoteCandidates.swappedDatum`, which is exactly what
`WallInput.ofGauge` exists for. -/
noncomputable def ofW2M11
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofGauge (m11Family input profile hCard hConnected hGenus incoming incomingFD)
    input.valid SourceCase.w2M11 rfl hwallColumn hConnected hGenus root

@[simp] theorem ofW2M11_case
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2M11 (wall := wall) input profile hCard hConnected hGenus incoming incomingFD
      hwallColumn root).case = SourceCase.w2M11 := rfl

/-! ## 2.  The full-dimensional supply -/

/-- Figure 32's three outgoing presentations, one
`M11FullDimensional.outgoingPresentation` per member.  The remote position is
not special: `M11StableGraphs.between` is proved there too. -/
noncomputable def m11FullDim : ∀ outgoing : Fin 3,
    (GluingDatum.LengthMatrixPresentation.matrix
      ((m11Family input profile hCard hConnected hGenus incoming
        incomingFD).presentation outgoing)).det ≠ 0 →
    FullDimensionalSourcePresentation
      ((m11Family input profile hCard hConnected hGenus incoming
        incomingFD).candidate outgoing).datum coordinate
  | 0 => fun hdet ↦ M11FullDimensional.outgoingPresentation input profile hCard hConnected
      hGenus incoming 0 incomingFD hdet
  | 1 => fun hdet ↦ M11FullDimensional.outgoingPresentation input profile hCard hConnected
      hGenus incoming 1 incomingFD hdet
  | 2 => fun hdet ↦ M11FullDimensional.outgoingPresentation input profile hCard hConnected
      hGenus incoming 2 incomingFD hdet

/-- **The full-dimensional supply for `w2M11`, with nothing carried.**  On
exactly the hypotheses
`ofW2M11` and `M11FullDimensional.outgoingPresentation` already take. -/
noncomputable def w2M11Supply
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2M11 (wall := wall) input profile hCard hConnected hGenus incoming
      incomingFD hwallColumn root) where
  fullDim := m11FullDim input profile hCard hConnected hGenus incoming incomingFD
  presentation_eq := by
    intro outgoing hdet
    fin_cases outgoing <;> rfl

/-! ## 3.  The incoming side -/

/-- The family's presented matrices are Equation (6)'s own square matrices. -/
theorem ofW2M11_presentation_matrix
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2M11 (wall := wall) input profile hCard hConnected hGenus incoming
          incomingFD hwallColumn root).family.presentation i) =
      M11CommonBalance.squareMatrix input profile hCard
        (M11FullDimensional.initialLabelling input profile hCard incoming incomingFD) i :=
  M11HonestGaugeFamily.presentation_matrix input profile hCard
    (M11FullDimensional.initialLabelling input profile hCard incoming incomingFD) i

/-- **`hW25IncomingNonzero` for `w2M11`.**
`M11CertifiedOpposite.incomingDet_ne_zero`. -/
theorem ofW2M11_incomingNonzero
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW2M11 (wall := wall) input profile hCard hConnected hGenus incoming
        incomingFD hwallColumn root).family.presentation incoming)).det ≠ 0 := by
  rw [ofW2M11_presentation_matrix input profile hCard hConnected hGenus incoming incomingFD
    hwallColumn root]
  exact M11CertifiedOpposite.incomingDet_ne_zero input profile hCard incoming incomingFD

/-- **`hW25IncomingMatrix` for `w2M11`, modulo the state–classifier equation.**
`hChart` is the single named hypothesis; the rest is
`M11CertifiedOpposite.outgoingLabelling_self`. -/
theorem ofW2M11_incomingMatrix
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2M11 (wall := wall) input profile hCard hConnected hGenus incoming
          incomingFD hwallColumn root).family.presentation incoming) = chart := by
  rw [ofW2M11_presentation_matrix input profile hCard hConnected hGenus incoming incomingFD
    hwallColumn root]
  change GluingDatum.LengthMatrixPresentation.matrix
    (M11FullDimensional.outgoingLabelling input profile hCard incoming incomingFD
      incoming).presentation = chart
  rw [M11CertifiedOpposite.outgoingLabelling_self input profile hCard incoming incomingFD]
  exact hChart

/-- **`hW25Nodup` for `w2M11`.** -/
theorem ofW2M11_nodup
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) (row : coordinate) :
    (((ofW2M11 (wall := wall) input profile hCard hConnected hGenus incoming
      incomingFD hwallColumn root).family.presentation i).path row).Nodup := by
  fin_cases i <;> exact A04MoreTags.nodup_labelling_path _ row

/-- The `w2M11` family is honestly presented. -/
theorem ofW2M11_honestlyPresented
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW2M11 (wall := wall) input profile hCard hConnected
      hGenus incoming incomingFD hwallColumn root) := by
  intro i
  fin_cases i <;> exact ⟨_, rfl⟩

/-! ## 4.  The routed wall -/

/-- **`w2M11` as a routed wall.**  Nothing is carried but `hChart`. -/
noncomputable def routedW2M11
    (hwallColumn : (m11Family input profile hCard hConnected hGenus incoming
      incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW2M11 (wall := wall) input profile hCard hConnected hGenus incoming incomingFD
      hwallColumn root)
    (w2M11Supply input profile hCard hConnected hGenus incoming incomingFD hwallColumn root)
    (ofW2M11_honestlyPresented input profile hCard hConnected hGenus incoming incomingFD
      hwallColumn root)
    incoming
    (ofW2M11_incomingNonzero input profile hCard hConnected hGenus incoming incomingFD
      hwallColumn root)
    (ofW2M11_incomingMatrix input profile hCard hConnected hGenus incoming incomingFD
      hwallColumn root chart hChart)

/-! ### Where the incoming position comes from

The incoming side is an arbitrary incoming `w2M11` cover identified with a
named Figure 32 member carrying an honest presentation in the original
coordinates.  In such an identification the `position` is `hW25Incoming`, the
`fd` is the `incomingFD` above, the matrix clause is `hChart`, and the column
clause is literally

```
fd.labelling.targetEdge.symm (M11CommonBalance.columnEquiv input profile hCard position none)
  = fullDim.labelling.targetEdge.symm contracted
```

whose left-hand side is this family's regrown column by
`m11Family_wallColumn` below.  So `hwallColumn` is discharged by that clause
the moment the march's crossed coordinate is the original contracted column,
and it is stated as a hypothesis here for the same reason it is at every other
tag: the identification of the march's coordinate belongs to the global march
(its source-certified initial state), not to the local case. -/

/-- The `w2M11` family's regrown column, read on the identified member's own
occurrence dictionary: transport to member `0` and back cancels, exactly as at
`w2P` (`A04MoreTags.ofW2P_family_wallColumn`). -/
theorem m11Family_wallColumn :
    (m11Family input profile hCard hConnected hGenus incoming incomingFD).wallColumn =
      incomingFD.labelling.targetEdge.symm
        (M11CommonBalance.columnEquiv input profile hCard incoming none) := by
  show ((incomingFD.labelling.targetEdge.trans
      ((M11CommonBalance.columnEquiv input profile hCard incoming).symm.trans
        (M11CommonBalance.columnEquiv input profile hCard 0))).trans
      (M11CommonBalance.columnEquiv input profile hCard 0).symm).symm none = _
  refine (Equiv.symm_apply_eq _).mpr ?_
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

end DraismaVargas.LocalCases.A04M11Wiring
