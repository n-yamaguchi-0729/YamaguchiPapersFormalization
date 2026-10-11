/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.OfFieldTower

/-!
# Etaleness from field-tower tensor components

When `K'` already acts on `L` over `K`, the multiplication map selects a
canonical maximal component of `K' ⊗[K] L` whose field is `L`.  Consequently,
etaleness of the integral closures of all tensor components implies etaleness
of the integral closure in `L`; neither a maximal ideal nor a comparison
equivalence is an input.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uD uK uK' uL

/-- Componentwise etaleness for the generic tensor product transfers to the
original ambient field along the component canonically selected by its
`K'`-action. -/
theorem integralClosure_etale_of_genericTensorFieldComponents_of_fieldTower
    {D : Type uD} {K : Type uK} {K' : Type uK'} {L : Type uL}
    [CommRing D] [Field K] [Field K'] [Field L]
    [Algebra K K'] [Algebra K L]
    [Algebra K' L] [IsScalarTower K K' L]
    [Algebra D K'] [Algebra D L] [IsScalarTower D K' L]
    (hlocal : ∀ (m : Ideal (K' ⊗[K] L)) [m.IsMaximal],
      letI : Algebra D (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentLeftScalarAlgebra (R := D) m
      Algebra.Etale D
        (integralClosure D (GenericTensorFieldComponent m))) :
    Algebra.Etale D (integralClosure D L) := by
  let m := fieldTowerTensorComponentIdeal
    (K := K) (K' := K') (L := L)
  let : m.IsMaximal :=
    fieldTowerTensorComponentIdeal_isMaximal
      (K := K) (K' := K') (L := L)
  let M := GenericTensorFieldComponent m
  let : Algebra D M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := D) m
  have hEtaleM : Algebra.Etale D (integralClosure D M) := hlocal m
  let E : integralClosure D M ≃ₐ[D] integralClosure D L :=
    fieldTowerTensorComponentIntegralClosureAlgEquiv
      (B := D) (K := K) (K' := K') (L := L)
  let : Algebra.Etale D (integralClosure D M) := hEtaleM
  exact Algebra.Etale.of_equiv E

end EtaleFundamentalGroups

end
