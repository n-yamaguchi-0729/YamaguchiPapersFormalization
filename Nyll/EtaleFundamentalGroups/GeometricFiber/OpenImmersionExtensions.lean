/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.Injectivity
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Nyll.EtaleFundamentalGroups.GaloisCovers.ExtendedQuotientKernel
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Fundamental-group equivalences from finite-etale extensions

For a nonempty open subscheme of a normal locally Noetherian integral
scheme, the induced map on etale fundamental groups is always surjective.
If every finite-etale cover of the open subscheme actually extends across
the open immersion, pullback is essentially surjective and the same map is
injective.  Compact-to-Hausdorff continuity then upgrades that specific map
to a continuous multiplicative equivalence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Essential surjectivity of finite-etale pullback across a nonempty open
immersion upgrades the induced fundamental-group homomorphism itself to a
continuous multiplicative equivalence. -/
noncomputable def fundamentalGroupEquivOfOpenImmersionEssSurj
    {U X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    (hEss : (pullback j).EssSurj)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U) :
    π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(xi ≫ j) := by
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : ConnectedSpace X := inferInstance
  letI : ConnectedSpace U := inferInstance
  letI : (pullback j).EssSurj := hEss
  let f := fundamentalGroupHom j xi
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    f.toMonoidHom f.continuous_toFun
      ⟨fundamentalGroupHom_injective_of_pullback_essSurj j xi,
        fundamentalGroupHom_surjective_of_isOpenImmersion j xi⟩

@[simp]
theorem fundamentalGroupEquivOfOpenImmersionEssSurj_apply
    {U X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    (hEss : (pullback j).EssSurj)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U) (gamma : π₁ᵉᵗ(xi)) :
    fundamentalGroupEquivOfOpenImmersionEssSurj j hEss xi gamma =
      fundamentalGroupHom j xi gamma := by
  rfl

/-- Actual extensions of all finite-etale Galois covers already suffice to
identify the two fundamental groups.  This avoids first reconstructing
essential surjectivity for arbitrary disconnected covers. -/
noncomputable def fundamentalGroupEquivOfOpenImmersionGaloisExtensions
    {U X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U] [ConnectedSpace U]
    (extend : ∀ (W : FiniteEtale U) (_hW : IsGalois W),
      Σ Z : FiniteEtale X, (pullback j).obj Z ≅ W)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U) :
    π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(xi ≫ j) := by
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : ConnectedSpace X := inferInstance
  let f := fundamentalGroupHom j xi
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    f.toMonoidHom f.continuous_toFun
      ⟨fundamentalGroupHom_injective_of_galoisCover_extensions j xi extend,
        fundamentalGroupHom_surjective_of_isOpenImmersion j xi⟩

@[simp]
theorem fundamentalGroupEquivOfOpenImmersionGaloisExtensions_apply
    {U X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U] [ConnectedSpace U]
    (extend : ∀ (W : FiniteEtale U) (_hW : IsGalois W),
      Σ Z : FiniteEtale X, (pullback j).obj Z ≅ W)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U) (gamma : π₁ᵉᵗ(xi)) :
    fundamentalGroupEquivOfOpenImmersionGaloisExtensions
        j extend xi gamma =
      fundamentalGroupHom j xi gamma := by
  rfl

/-- Actual extension objects for every finite-etale cover of the open
subscheme provide the essential-surjectivity input and hence identify the
two etale fundamental groups. -/
noncomputable def fundamentalGroupEquivOfOpenImmersionExtensions
    {U X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    (extend : ∀ W : FiniteEtale U,
      Σ Z : FiniteEtale X, (pullback j).obj Z ≅ W)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U) :
    π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(xi ≫ j) := by
  let hEss : (pullback j).EssSurj :=
    ⟨fun W ↦ by
      let extension := extend W
      exact ⟨extension.1, ⟨extension.2⟩⟩⟩
  exact fundamentalGroupEquivOfOpenImmersionEssSurj j hEss xi

@[simp]
theorem fundamentalGroupEquivOfOpenImmersionExtensions_apply
    {U X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    (extend : ∀ W : FiniteEtale U,
      Σ Z : FiniteEtale X, (pullback j).obj Z ≅ W)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U) (gamma : π₁ᵉᵗ(xi)) :
    fundamentalGroupEquivOfOpenImmersionExtensions j extend xi gamma =
      fundamentalGroupHom j xi gamma := by
  rfl

end AlgebraicGeometry.FiniteEtale

end
