/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.IteratedRadical.EtaleFactorExponentUnit

/-!
# Exponent units from an étale normalization of an iterated radical cover

This file connects the height-two purity output to the terminal radical
exponent obstruction.  An integral closure inside a field is a domain and is
integral over the root cover.  Once purity makes it étale, those facts make it
faithfully flat, so no separate chosen local factor is needed for the
exponent-unit conclusion.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe u

/--
If the normalization of a positive iterated radical cover in a field is
étale, and its composite with the original base is étale away from the whole
boundary, then every radical exponent is a unit in the original base.

Faithful flatness of the normalization is produced internally from
integrality, its domain structure, and étale flatness.
-/
theorem all_exponents_isUnit_of_iteratedRadical_integralClosure_etale
    {A : Type u} [CommRing A] [IsDomain A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (haPrime : ∀ i, Prime (a i))
    (hCharZero : ∀ i, CharZero (A ⧸ Ideal.span {a i}))
    {L : Type u} [Field L]
    [Algebra (iteratedRadical A r n a) L]
    [FaithfulSMul (iteratedRadical A r n a) L]
    (hEtale : Algebra.Etale
      (iteratedRadical A r n a)
      (integralClosure (iteratedRadical A r n a) L))
    (hAway : (Localization.awayMap
      ((algebraMap (iteratedRadical A r n a)
          (integralClosure (iteratedRadical A r n a) L)).comp
        (algebraMap A (iteratedRadical A r n a)))
      (∏ i ∈ (Finset.univ : Finset (Fin r)), a i)).Etale) :
    ∀ i, IsUnit (n i : A) := by
  let B := iteratedRadical A r n a
  let D := integralClosure B L
  let mapAD : A →+* D := (algebraMap B D).comp (algebraMap A B)
  let : Algebra A D := mapAD.toAlgebra
  let : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale B D := hEtale
  let : FaithfulSMul B D :=
    (faithfulSMul_iff_algebraMap_injective B D).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective B L
      exact congrArg Subtype.val hxy
  let : Module.FaithfullyFlat B D := inferInstance
  change (Localization.awayMap (algebraMap A D)
    (∏ i ∈ (Finset.univ : Finset (Fin r)), a i)).Etale at hAway
  exact all_exponents_isUnit_of_iteratedRadical_formallyEtaleFactor
    (A := A) n a hn haPrime hCharZero (D := D) hAway

end EtaleFundamentalGroups.Kummer

end
