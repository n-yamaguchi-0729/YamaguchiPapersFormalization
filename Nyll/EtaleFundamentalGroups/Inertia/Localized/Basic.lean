/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Primes.Basic

/-!
# Inertia at a localized normalization prime

This file defines the inertia subgroup at a normalization prime after
localizing the base at a prime ideal.  The construction uses only the
canonical fraction-field maps and the generic action on an integral closure;
it has no DVR, height, regularity, finiteness, or Galois-extension hypothesis.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

omit [IsDomain A] [Algebra A L] [IsScalarTower A K L] in
/-- The canonical Galois action on `L` commutes with scalars from the prime
localization of `A`.  This is a named non-instance producer so consumers can
reuse the same local instance without adding a global typeclass path. -/
theorem localizationAtPrime_galois_smulCommClass
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
    SMulCommClass Gal(L/K) (Localization.AtPrime P) L := by
  let V := Localization.AtPrime P
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  refine ⟨fun σ v x ↦ ?_⟩
  change σ (algebraMap V L v * x) = algebraMap V L v * σ x
  rw [map_mul, IsScalarTower.algebraMap_apply V K L, AlgEquiv.commutes]

/-- The inertia subgroup at the ideal transported to the normalization of the
prime localization.  Its action is the generic integral-closure action
induced by the canonical action of `Gal(L/K)` on `L`; no DVR or height
assumption is needed. -/
noncomputable def localizedNormalizationInertia
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    Subgroup Gal(L/K) := by
  let V := Localization.AtPrime P
  letI : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  letI : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  letI : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  letI : SMulCommClass Gal(L/K) V L :=
    localizationAtPrime_galois_smulCommClass (K := K) (L := L) P
  exact
    (localizedNormalizationPrime (K := K) (L := L) P Q).toAddSubgroup.inertia
      Gal(L/K)

end EtaleFundamentalGroups

end
