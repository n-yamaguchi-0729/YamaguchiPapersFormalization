/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.IteratedRadical.ExponentUnit.IntegralClosurePrimeOrUnit
import EtaleFundamentalGroups.Kummer.IteratedRadical.TargetActionComponentEtale

/-!
# Exponent units from a target action and componentwise purity

Compatible roots in a target field construct the iterated-radical action and
its chosen fraction-field tower.  Componentwise normalization etaleness then
produces global normalization etaleness, which combines with primitive
boundary-away etaleness to force every radical exponent to be a unit.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uA uK uK'

/-- Source-produced target roots, componentwise purity, and primitive
boundary-away etaleness force all iterated-radical exponents to be units.
The target action, its injectivity, both fraction-field towers, and the
selected tensor-component comparison are all constructed internally. -/
theorem
    all_exponents_isUnit_of_targetAction_components_boundaryAway_primeOrUnit
    {A L : Type uA} {K : Type uK} {K' : Type uK'}
    [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [FaithfulSMul A L]
    [Algebra K L] [IsScalarTower A K L]
    {r b : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    [IsDomain (iteratedRadical A r n a)]
    [Field K']
    [Algebra (iteratedRadical A r n a) K']
    [IsFractionRing (iteratedRadical A r n a) K']
    [Algebra A K'] [IsScalarTower A (iteratedRadical A r n a) K']
    [Algebra K K'] [IsScalarTower A K K']
    (x : Fin r → L)
    (hx : ∀ i, x i ^ n i = algebraMap A L (a i))
    (s : Fin b → A)
    (hsPrimeOrUnit : ∀ i, Prime (s i) ∨ IsUnit (s i))
    (hCharZero : ∀ i, Prime (s i) →
      CharZero (A ⧸ Ideal.span {s i}))
    (f : A) (hAssoc : Associated f (∏ i, s i))
    (hlocal : ∀ (m : Ideal (K' ⊗[K] L)) [m.IsMaximal],
      let : Algebra (iteratedRadical A r n a)
          (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentLeftScalarAlgebra
          (R := iteratedRadical A r n a) m
      Algebra.Etale (iteratedRadical A r n a)
        (integralClosure (iteratedRadical A r n a)
          (GenericTensorFieldComponent m))) :
    let Full := iteratedRadical A r n a
    let ρ : Full →ₐ[A] L := iteratedRadicalTargetAlgHom n a x hx
    let : Algebra Full L := ρ.toRingHom.toAlgebra
    (Localization.awayMap
      ((algebraMap Full (integralClosure Full L)).comp
        (algebraMap A Full)) f).Etale →
    ∀ i, IsUnit (n i : A) := by
  intro Full ρ algebraFullL hAway
  have hρ : Function.Injective ρ :=
    iteratedRadicalTargetAlgHom_injective n a hn x hx
  let : FaithfulSMul Full L :=
    (faithfulSMul_iff_algebraMap_injective Full L).mpr hρ
  have hEtale : Algebra.Etale Full (integralClosure Full L) := by
    exact
      integralClosure_etale_of_iteratedRadicalTargetAction_genericTensorFieldComponents
        (K := K) (K' := K') n a hn x hx hlocal
  exact
    all_exponents_isUnit_of_iteratedRadical_integralClosure_etale_boundaryAway_primeOrUnit_universe
      (A := A) n a hn s hsPrimeOrUnit hCharZero f hAssoc
        (L := L) hEtale hAway

end EtaleFundamentalGroups.Kummer

end
