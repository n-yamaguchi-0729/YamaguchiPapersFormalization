/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BoundaryAwayFieldEquiv
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normality of a retained normalization localization

Let `M / K` be a finite extension of the fraction field of a domain `R`.
The normalization `integralClosure R M` is integrally closed, and every
localization of it at a prime remains integrally closed.  This file records
that fact in the precise form needed by a retained completed chosen factor.

In particular, if the retained localization is finite over a second base
`C`, then it is the integral closure of `C` in its own fraction field.  This
removes the global Noetherian/regularity argument formerly used to identify
the chosen factor with that integral closure.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uK uM uC uD uOmega

/-- The canonical algebra on a fraction ring obtained by composing through
its source domain.  Naming this algebra keeps every downstream tower on the
same data instead of rebuilding equivalent `SMul` instances. -/
@[reducible] private noncomputable def fractionRingCompositeAlgebra
    {C : Type uC} {D : Type uD}
    [CommRing C] [CommRing D] [IsDomain D] [Algebra C D] :
    Algebra C (FractionRing D) :=
  ((algebraMap D (FractionRing D)).comp (algebraMap C D)).toAlgebra

/-- The scalar tower carried by `fractionRingCompositeAlgebra`. -/
private theorem fractionRingCompositeAlgebra_isScalarTower
    {C : Type uC} {D : Type uD}
    [CommRing C] [CommRing D] [IsDomain D] [Algebra C D] :
    @IsScalarTower C D (FractionRing D)
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D (FractionRing D)).toSMul
      (fractionRingCompositeAlgebra (C := C) (D := D)).toSMul := by
  refine @IsScalarTower.of_algebraMap_eq C D (FractionRing D)
    _ _ _ (inferInstance : Algebra C D)
      (inferInstance : Algebra D (FractionRing D))
      (fractionRingCompositeAlgebra (C := C) (D := D)) ?_
  intro x
  rfl

/-- A prime localization of the normalization in a finite fraction-field
extension is integrally closed.

Both normality steps are source-produced: normality of the normalization is
`integralClosure.isIntegrallyClosedOfFiniteExtension`, and normality of its
prime localization is localization stability of integral closedness. -/
theorem
    integralClosureLocalizationAtPrime_isIntegrallyClosed_of_finiteExtension
    {R : Type uR} {K : Type uK} {M : Type uM}
    [CommRing R] [IsDomain R]
    [Field K] [Field M]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K M] [Algebra R M] [IsScalarTower R K M]
    [FiniteDimensional K M]
    (p : Ideal (integralClosure R M)) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  let : IsIntegrallyClosed (integralClosure R M) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  exact
    isIntegrallyClosed_of_isLocalization
      (Localization.AtPrime p) p.primeCompl
        p.primeCompl_le_nonZeroDivisors

/-- If a retained normalization localization is finite over `C`, then it is
the integral closure of `C` in its own fraction field.

No Noetherian or regularity hypothesis on `C` is needed.  In the completed
chosen-factor application, the `C`-algebra and module-finiteness structures
come from the explicit root-cover tensor equivalence. -/
theorem
    integralClosureLocalizationAtPrime_isIntegralClosure_of_finiteExtension
    {R : Type uR} {K : Type uK} {M : Type uM}
    [CommRing R] [IsDomain R]
    [Field K] [Field M]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K M] [Algebra R M] [IsScalarTower R K M]
    [FiniteDimensional K M]
    (p : Ideal (integralClosure R M)) [p.IsPrime]
    {C : Type uC} [CommRing C]
    [Algebra C (Localization.AtPrime p)]
    [Module.Finite C (Localization.AtPrime p)] :
    let D := Localization.AtPrime p
    let P := FractionRing D
    @IsIntegralClosure D C P _ _ _
      (fractionRingCompositeAlgebra (C := C) (D := D))
      (inferInstance : Algebra D P) := by
  dsimp only
  let D := Localization.AtPrime p
  let P := FractionRing D
  let : IsIntegrallyClosed D :=
    integralClosureLocalizationAtPrime_isIntegrallyClosed_of_finiteExtension
      (K := K) p
  let cPAlgebra : Algebra C P :=
    fractionRingCompositeAlgebra (C := C) (D := D)
  let : Algebra C P := cPAlgebra
  let : @IsScalarTower C D P
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D P).toSMul
      cPAlgebra.toSMul :=
    fractionRingCompositeAlgebra_isScalarTower
  let : Algebra.IsIntegral C D := Algebra.IsIntegral.of_finite C D
  exact IsIntegralClosure.of_isIntegrallyClosed D C P

/-- A sourced bijective comparison with a retained normalization
localization transports a primitive boundary-Away map to that literal local
factor.

Unlike the older regular-pair terminal, normality of the target factor is
not obtained from Noetherian regularity of the completed base.  It is
obtained internally from the concrete fact that the factor is a prime
localization of a normalization. -/
theorem
    integralClosureLocalizationAtPrime_boundaryAway_of_bijective_fieldTower
    {R : Type uR} {K : Type uK} {M : Type uM}
    [CommRing R] [IsDomain R]
    [Field K] [Field M]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K M] [Algebra R M] [IsScalarTower R K M]
    [FiniteDimensional K M]
    (p : Ideal (integralClosure R M)) [p.IsPrime]
    {C : Type uC} [CommRing C]
    [Algebra C (Localization.AtPrime p)]
    [Module.Finite C (Localization.AtPrime p)]
    {Omega : Type uOmega} [Field Omega] :
    let D := Localization.AtPrime p
    let P := FractionRing D
    ∀ [Algebra C Omega] [Algebra Omega P]
      [@IsScalarTower C Omega P
        (inferInstance : Algebra C Omega).toSMul
        (inferInstance : Algebra Omega P).toSMul
        (fractionRingCompositeAlgebra (C := C) (D := D)).toSMul],
      Function.Bijective (algebraMap Omega P) →
        ∀ f : C,
          (Localization.awayMap
            (algebraMap C (integralClosure C Omega)) f).Etale →
          @RingHom.Etale
            (Localization.Away f)
            (Localization.Away (algebraMap C D f)) _ _
            (Localization.awayMap (algebraMap C D) f) := by
  dsimp only
  let D := Localization.AtPrime p
  let P := FractionRing D
  let cPAlgebra : Algebra C P :=
    fractionRingCompositeAlgebra (C := C) (D := D)
  let : Algebra C P := cPAlgebra
  let : @IsScalarTower C D P
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D P).toSMul
      cPAlgebra.toSMul :=
    fractionRingCompositeAlgebra_isScalarTower
  intro _ _ _ hbij f hAwayOmega
  let : IsIntegralClosure D C P :=
    integralClosureLocalizationAtPrime_isIntegralClosure_of_finiteExtension
      (K := K) p
  have hAwayP :=
    integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
      hbij f hAwayOmega
  let chosenEquiv : integralClosure C P ≃ₐ[C] D :=
    IsIntegralClosure.equiv C (integralClosure C P) P D
  exact localization_awayMap_etale_of_algEquiv chosenEquiv f hAwayP

end EtaleFundamentalGroups

end
