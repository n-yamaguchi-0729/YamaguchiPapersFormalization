/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FiniteQuotientRealization
import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverIdealImage

/-!
# Normalization inertia in explicit finite quotients

An explicit finite quotient of an etale fundamental group can be realized by
a pointed connected finite-etale Galois cover.  This file transports
coprimality of normalization-prime inertia in the cover's function-field
Galois group to the corresponding subgroup image in the prescribed quotient.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Kummer

universe u uA uG

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
variable [IsLocallyNoetherian X]
variable (W : FiniteEtale X) [hW : IsGalois W]

local instance finiteQuotientNormalizationInertia_isIntegral :
    IsIntegral W.left :=
  isIntegral_left_of_isConnected_finiteEtale W

local notation "K" => X.functionField
local notation "L" => W.left.functionField

local instance finiteQuotientNormalizationInertia_algebraKL : Algebra K L :=
  finiteEtaleFunctionFieldAlgebra W

variable (A : Type uA) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [Algebra A X.functionField] [IsFractionRing A X.functionField]

local instance finiteQuotientNormalizationInertia_algebraAL : Algebra A L :=
  ((algebraMap K L).comp (algebraMap A K)).toAlgebra

local instance finiteQuotientNormalizationInertia_towerAKL :
    IsScalarTower A K L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finiteQuotientNormalizationInertia_finiteDimensional :
    FiniteDimensional K L :=
  finiteDimensional_functionField_of_finiteEtale_isConnected W

local instance finiteQuotientNormalizationInertia_isGaloisField :
    _root_.IsGalois K L :=
  isGalois_functionField_of_isGalois_finiteEtale W hW

local notation "B" => integralClosure A L

local instance finiteQuotientNormalizationInertia_fractionRingB :
    IsFractionRing B L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L B

local instance finiteQuotientNormalizationInertia_galoisAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

local instance finiteQuotientNormalizationInertia_deckAction :
    MulSemiringAction (Aut W)ᵐᵒᵖ B :=
  finiteEtaleGaloisCoverNormalizationAction W hW A B

/-- Coprimality of inertia at a prime of the original normalization passes
through a pointed-cover realization to the corresponding image in any
explicit finite quotient. -/
theorem finiteQuotient_normalizationInertiaImage_coprime
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (w : (fiber xi).obj W)
    {G : Type uG} [Group G]
    (e : (Aut W)ᵐᵒᵖ ≃* G)
    (phi : π₁ᵉᵗ(xi) →* G)
    (hcomp : e.toMonoidHom.comp
      (finiteEtaleGaloisCoverQuotientMonoidHom xi W hW w) = phi)
    (q : Ideal B) (p : ℕ)
    (hcoprime : Nat.Coprime
      (Nat.card (q.toAddSubgroup.inertia Gal(L/K))) p) :
    Nat.Coprime
      (Nat.card
        ((Subgroup.comap
          (finiteEtaleGaloisCoverQuotientMonoidHom xi W hW w)
          (q.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ)).map phi)) p := by
  apply (quotientDeckMulEquiv_quotient_subgroup_coprime_iff
    xi W hW w e phi hcomp
    (Subgroup.comap
      (finiteEtaleGaloisCoverQuotientMonoidHom xi W hW w)
      (q.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ)) p).2
  rw [natCard_finiteEtaleGaloisCoverIdealInertia_image_eq
    xi W hW w A B q]
  exact hcoprime

end EtaleFundamentalGroups.Kummer

end
