/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.OfFieldTowerEtale
import Nyll.EtaleFundamentalGroups.Kummer.FieldTowers.ChosenFractionField
import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.TargetAction

/-!
# Etaleness from a source-produced iterated-radical target action

A compatible family of target roots constructs the full iterated-radical
action on the target field.  When the root ring is a domain and the base acts
faithfully, that action is injective and hence extends to its chosen fraction
field.  The resulting field tower selects the tensor component equal to the
target field, so componentwise normalization etaleness transfers to the
normalization in the target without map- or comparison-shaped assumptions.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uA uK uK'

/-- Target roots and their power equations produce all action and field-tower
data needed to transfer componentwise normalization etaleness to the target
field. -/
theorem
    integralClosure_etale_of_iteratedRadicalTargetAction_genericTensorFieldComponents
    {A L : Type uA} {K : Type uK} {K' : Type uK'}
    [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [FaithfulSMul A L]
    [Algebra K L] [IsScalarTower A K L]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    [IsDomain (iteratedRadical A r n a)]
    [Field K']
    [Algebra (iteratedRadical A r n a) K']
    [IsFractionRing (iteratedRadical A r n a) K']
    [Algebra A K'] [IsScalarTower A (iteratedRadical A r n a) K']
    [Algebra K K'] [IsScalarTower A K K']
    (x : Fin r → L)
    (hx : ∀ i, x i ^ n i = algebraMap A L (a i))
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
    Algebra.Etale Full (integralClosure Full L) := by
  intro Full ρ algebraFullL
  have hρ : Function.Injective ρ :=
    iteratedRadicalTargetAlgHom_injective n a hn x hx
  let : FaithfulSMul Full L :=
    (faithfulSMul_iff_algebraMap_injective Full L).mpr hρ
  let : Algebra K' L :=
    chosenFractionFieldToFaithfulFieldAlgebra
      (R := Full) (K := K') (F := L)
  let : IsScalarTower Full K' L :=
    chosenFractionFieldToFaithfulField_isScalarTower
      (R := Full) (K := K') (F := L)
  let : IsScalarTower K K' L :=
    chosenFractionFieldToFaithfulField_isScalarTower_of_fractionFieldTower
      (R := A) (D := Full) (K := K) (K' := K') (L := L) ρ hρ
  exact
    EtaleFundamentalGroups.integralClosure_etale_of_genericTensorFieldComponents_of_fieldTower
      (D := Full) (K := K) (K' := K') (L := L) hlocal

end EtaleFundamentalGroups.Kummer

end
