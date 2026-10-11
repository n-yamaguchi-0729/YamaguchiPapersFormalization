/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticAllBranchCharacteristicZero
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticComplementCover
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticQuotientInertia
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Divisorial inertia along horizontal normal-crossings boundaries

A horizontal boundary branch has characteristic zero at its generic point.
When it specializes to positive residue characteristic, the branch admits a
height-two split chart.  Every connected finite-etale Galois cover of the
global boundary complement remains Galois on this chart, and its pointed
finite quotient has inertia of order prime to the residue characteristic.

Only local Noetherianity is used; there is no finite-type or Nagata
hypothesis.
-/

noncomputable section

open CategoryTheory EtaleFundamentalGroups TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- Let a component of a horizontal strict-normal-crossings divisor meet a
point of prime positive residue characteristic.  There is a height-two split
chart around that component branch such that every connected Galois cover of
the global divisor complement remains Galois after restriction, and every
pointed finite-quotient inertia group on the chart has order prime to the
residue characteristic.

This is the arbitrary-dimensional divisorial-inertia statement: the
height-two chart is constructed inside the stalk, so the dimension of `X` is
not restricted. -/
theorem IsHorizontalOver.exists_localSplitChart_component_galoisCover_quotientInertia_coprime
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (hHorizontal : D.IsHorizontalOver structural)
    [CharZero (S.residueField (genericPoint S))]
    (hNC : D.IsStrictNormalCrossings)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (p : ℕ) [CharP (X.residueField (D.1.subschemeι z)) p]
    (hp : p.Prime) :
    let x := D.1.subschemeι z
    let q := (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
    let A := X.presheaf.stalk x
    ∃ P : AlgebraicGeometry.Spec A,
      q < P.asIdeal ∧ P.asIdeal.height = 2 ∧
        let : P.asIdeal.IsPrime := P.isPrime
        let V := Localization.AtPrime P.asIdeal
        let qV := q.map (algebraMap A V)
        ∃ (r : ℕ) (t : Fin 2 → V) (i : Fin 2)
          (hVdomain : IsDomain V) (hVregular : IsRegularRing V)
          (hVnormal : IsIntegrallyClosed V)
          (hboundary : (D.1.stalkIdeal x).map (algebraMap A V) =
            Ideal.span {boundaryProduct t r})
          (hLocalNC : IsSplitStrictNormalCrossingsAt
            (boundaryProduct t r) t r)
          (_hi : i.1 < r)
          (_hqi : qV = Ideal.span {t i})
          (_hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
            CharZero (V ⧸ Ideal.span {t j}))
          (_hpV : CharP (V ⧸ IsLocalRing.maximalIdeal V) p),
            letI : IsDomain V := hVdomain
            letI : IsRegularRing V := hVregular
            letI : IsIntegrallyClosed V := hVnormal
            let hf :=
              Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
                hLocalNC
            letI : IsDomain (Localization.Away (boundaryProduct t r)) :=
              IsLocalization.Away.isDomain
                (Localization.Away (boundaryProduct t r)) hf
            letI : Nonempty D.1.supportComplement :=
              D.1.supportComplement_nonempty_of_localizationAway
                x P.asIdeal (boundaryProduct t r) hf hboundary
            IdealSheafData.PointedGaloisQuotientInertiaCoprime
                hLocalNC qV p ∧
              ∀ (W : FiniteEtale D.1.supportComplement),
                CategoryTheory.PreGaloisCategory.IsGalois W →
                CategoryTheory.PreGaloisCategory.IsGalois
                  (D.1.pullbackSupportComplementCoverToBoundaryAway
                    x P t hboundary W) := by
  dsimp only
  let x : X := D.1.subschemeι z
  let qSpec := D.1.componentBranchPrimeAt Z hZ z hz
  let q := qSpec.asIdeal
  let : q.IsPrime := qSpec.2
  have hqheight : q.height = 1 :=
    D.2.componentBranchPrimeAt_height_eq_one Z hZ z hz
  have hDq : D.1.stalkIdeal x ≤ q :=
    D.1.stalkIdeal_le_componentBranchPrimeAt Z hZ z hz
  have hCharZero : D.1.HasCharacteristicZeroBranchesAt x :=
    hHorizontal.hasCharacteristicZeroBranchesAt D structural x
  let phi : (X.presheaf.stalk x ⧸ q) →+* X.residueField x :=
    Scheme.specializationPrimeQuotientToResidueField
      (D.1.componentGenericPoint_specializes_subschemeι Z hZ z hz)
  have hchart :=
    hNC.exists_arithmeticLocalSplitChart_galoisCover_quotientIdealInertia_coprime
      hCharZero q hqheight hDq phi p hp
  dsimp only at hchart
  obtain ⟨P, hqP, hPheight, r, t, i, hVdomain, hVregular,
      hVnormal, hboundary, hLocalNC, hi, hqi, hlocalizedCharZero,
      hpV, hcoprime⟩ := hchart
  let : P.asIdeal.IsPrime := P.isPrime
  refine ⟨P, hqP, hPheight, r, t, i, hVdomain, hVregular,
    hVnormal, hboundary, hLocalNC, hi, hqi, hlocalizedCharZero,
    hpV, hcoprime, ?_⟩
  intro W hW
  exact D.1.pullbackSupportComplementCoverToBoundaryAway_isGalois
    x P t hboundary hLocalNC W hW

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
