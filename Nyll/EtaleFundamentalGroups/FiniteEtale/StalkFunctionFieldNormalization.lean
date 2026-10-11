/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.Normalization.Localization.IntegralClosureAtPrimeEquiv
import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-!
# Function-field normalizations over local rings

A connected finite-etale cover of a normal locally Noetherian integral
scheme normalizes every local ring to an etale algebra.  The proof first
works on an affine neighbourhood and then localizes its normalization at the
prime represented by the chosen point.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct
open AlgebraicGeometry


namespace EtaleFundamentalGroups

universe u

/-- Etaleness of a normalization passes from a domain to its localization at
a prime.  The localized normalization is obtained by tensor base change and
then identified with the literal integral closure over the localized base. -/
theorem integralClosure_localizationAtPrime_etale_of_etale
    {R K L : Type u} [CommRing R] [IsDomain R]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (hEtale : Algebra.Etale R (integralClosure R L))
    (P : Ideal R) [P.IsPrime] :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := L) P
    Algebra.Etale (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) := by
  let S := Localization.AtPrime P
  let C := integralClosure R L
  let Cₚ := Localization
    (Algebra.algebraMapSubmonoid C P.primeCompl)
  let : Algebra.Etale R C := hEtale
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower R S L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  have hCₚ : Algebra.Etale S Cₚ := by
    let : Algebra.Etale S (S ⊗[R] C) := inferInstance
    exact Algebra.Etale.of_equiv
      (Localization.tensorRightAlgEquiv P.primeCompl C)
  let : Algebra.Etale S Cₚ := hCₚ
  exact Algebra.Etale.of_equiv
    (localizationIntegralClosureAtPrimeAlgEquiv
      (K := K) (L := L) P)

/-- On any nonempty affine open of the base, a connected finite-etale cover
makes the normalization in its function field etale. -/
theorem
    integralClosure_functionField_etale_on_affineOpen_of_finiteEtale_isConnected
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra Γ(X, U) Y.left.functionField :=
      X.affineExtensionAlgebra U Y.left.functionField
    Algebra.Etale Γ(X, U)
      (integralClosure Γ(X, U) Y.left.functionField) := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let f : Y.left ⟶ X := Y.hom
  let : IsFiniteEtale f := Y.prop
  let V : Y.left.Opens := f ⁻¹ᵁ U
  let : Nonempty V := ⟨⟨genericPoint Y.left, by
    change f (genericPoint Y.left) ∈ U
    rw [f.map_genericPoint_of_denseRange
      (finiteEtale_hom_denseRange_of_isConnected Y)]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))⟩⟩
  have hV : IsAffineOpen V := hU.preimage f
  let R := Γ(X, U)
  let T := Γ(Y.left, V)
  let K := X.functionField
  let L := Y.left.functionField
  let : Algebra R T := (f.app U).hom.toAlgebra
  let : Module.Finite R T := by
    rw [← RingHom.finite_algebraMap]
    exact f.finite_app U hU
  have hEtale : (f.app U).hom.Etale := by
    simpa only [f.app_eq_appLE] using
      f.etale_appLE hU hV (show V ≤ f ⁻¹ᵁ U from le_rfl)
  let : Algebra.Etale R T := hEtale.toAlgebra
  let : IsIntegrallyClosed R :=
    IsNormalIntegral.affine_isIntegrallyClosed U hU
  let : Algebra R K := (X.germToFunctionField U).hom.toAlgebra
  let : IsFractionRing R K :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra T L :=
    (Y.left.germToFunctionField V).hom.toAlgebra
  let : IsFractionRing T L :=
    functionField_isFractionRing_of_isAffineOpen Y.left V hV
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra R L := X.affineExtensionAlgebra U L
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R T L := by
    apply IsScalarTower.of_algebraMap_eq'
    exact Scheme.Hom.functionFieldMap_comp_germToFunctionField
      f (finiteEtale_hom_denseRange_of_isConnected Y) U
  exact integralClosure_etale_of_finiteEtale_fractionField
    (R := R) (T := T) (K := K) (L := L)

/-- For every point of a normal locally Noetherian integral scheme, the
normalization of its local ring in the function field of a connected
finite-etale cover is etale.  All algebra structures are the canonical
function-field tower structures. -/
theorem
    integralClosure_functionField_etale_on_stalk_of_finiteEtale_isConnected
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] (x : X) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra (X.presheaf.stalk x) Y.left.functionField :=
      X.stalkExtensionAlgebra x Y.left.functionField
    Algebra.Etale (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x)
        Y.left.functionField) := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K := X.functionField
  let L := Y.left.functionField
  let A := X.presheaf.stalk x
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra A L := X.stalkExtensionAlgebra x L
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := x) (by simp)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let R := Γ(X, U)
  let : Algebra R K := (X.germToFunctionField U).hom.toAlgebra
  let : IsFractionRing R K :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra R L := X.affineExtensionAlgebra U L
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  have hGlobal : Algebra.Etale R (integralClosure R L) :=
    integralClosure_functionField_etale_on_affineOpen_of_finiteEtale_isConnected
      Y U hU
  let xU : U := ⟨x, hxU⟩
  let P : Ideal R := (hU.primeIdealOf xU).asIdeal
  let : P.IsPrime := (hU.primeIdealOf xU).isPrime
  let : Algebra R A := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : IsLocalization.AtPrime A P := hU.isLocalization_stalk xU
  let : IsScalarTower R A K := functionField_isScalarTower X U xU
  let : IsScalarTower R A L := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    calc
      algebraMap R L r = algebraMap K L (algebraMap R K r) :=
        IsScalarTower.algebraMap_apply R K L r
      _ = algebraMap K L (algebraMap A K (algebraMap R A r)) := by
        rw [← IsScalarTower.algebraMap_apply R A K]
      _ = algebraMap A L (algebraMap R A r) :=
        (IsScalarTower.algebraMap_apply A K L _).symm
  let S := Localization.AtPrime P
  let : Algebra S L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower R S L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  have hLocal : Algebra.Etale S (integralClosure S L) :=
    integralClosure_localizationAtPrime_etale_of_etale
      (K := K) hGlobal P
  let e : S ≃ₐ[R] A :=
    IsLocalization.algEquiv P.primeCompl S A
  have he :
      (algebraMap S L).comp e.symm.toRingHom = algebraMap A L := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext r
    simp only [RingHom.comp_apply]
    change algebraMap S L (e.symm (algebraMap R A r)) =
      algebraMap A L (algebraMap R A r)
    calc
      algebraMap S L (e.symm (algebraMap R A r)) =
          algebraMap S L (algebraMap R S r) := by
        rw [← e.commutes r, e.symm_apply_apply]
      _ = algebraMap R L r :=
        (IsScalarTower.algebraMap_apply R S L r).symm
      _ = algebraMap A L (algebraMap R A r) :=
        IsScalarTower.algebraMap_apply R A L r
  exact integralClosure_etale_of_baseRingEquiv
    e.symm.toRingEquiv he hLocal

end EtaleFundamentalGroups

end
