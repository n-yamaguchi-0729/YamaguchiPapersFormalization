/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.ProsolvableBoundary

/-!
# Prosolvable comparison from actual boundary-cover extensions

This is the public categorical endpoint of the boundary argument.  It does
not assume injectivity, essential surjectivity, or the desired prosolvable
comparison.  Its input is an actual finite-etale extension object, together
with its pullback isomorphism, for every finite abelian Galois cover occurring
over an open-normal pullback component.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open ProCGroups.FiniteStepSolvableQuotients
open scoped ProCGroupsSolvableQuotients

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Actual extensions of all finite abelian covers over the geometric
open-normal pullback models identify the maximal prosolvable quotients across
the boundary complement. -/
noncomputable def prosolvableBoundaryEquivOfPullbackModelExtensions
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor)
    [ConnectedSpace D.1.supportComplement]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ D.1.supportComplement)
    (extend : ∀
      (U : OpenNormalSubgroup
        π₁ᵉᵗ(xi ≫ D.1.supportComplement.ι))
      (W : FiniteEtale
        (openNormalPullbackModel D.1.supportComplement.ι xi U).sourceScheme)
      (_hW : IsGalois W),
      IsMulCommutative (Aut W) →
        Σ Z : FiniteEtale
          (openNormalPullbackModel D.1.supportComplement.ι xi U).targetScheme,
          (pullback
            (openNormalPullbackModel D.1.supportComplement.ι xi U).hom).obj Z ≅ W) :
    (π₁ᵉᵗ(xi) ⧸ ProCGroups.ProC.proCResidualCore
        ProCGroups.FiniteGroupClass.solvable π₁ᵉᵗ(xi)) ≃ₜ*
      (π₁ᵉᵗ(xi ≫ D.1.supportComplement.ι) ⧸
        ProCGroups.ProC.proCResidualCore ProCGroups.FiniteGroupClass.solvable
          π₁ᵉᵗ(xi ≫ D.1.supportComplement.ι)) := by
  letI : IsIntegral D.1.supportComplement :=
    isIntegral_of_isOpenImmersion D.1.supportComplement.ι
  letI : ConnectedSpace X := inferInstance
  letI : ConnectedSpace D.1.supportComplement := inferInstance
  let f := fundamentalGroupHom D.1.supportComplement.ι xi
  have hsurjective : Function.Surjective f :=
    fundamentalGroupHom_surjective_of_isOpenImmersion
      D.1.supportComplement.ι xi
  have hkill : OpenNormalFiniteDiscreteAbelianMapsKillKernel f :=
    fundamentalGroupHom_openNormalFiniteDiscreteAbelianMapsKillKernel_of_pullbackModel_extensions
      D.1.supportComplement.ι xi extend
  have hab : OpenNormalAbelianizationInjective f :=
    openNormalAbelianizationInjective_of_finiteDiscreteAbelianMapsKillKernel
      f hsurjective hkill
  exact prosolvableResidualQuotientContinuousMulEquiv
    f hsurjective hab

end AlgebraicGeometry.FiniteEtale
