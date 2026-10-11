/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameValue
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinateTower
import EtaleFundamentalGroups.Inertia.ActualFiniteTameOrderTower
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# Actual quotient-scalar compatibility over every divisible pair of degrees

The common-upper-stage calculation uses the existing normalized raw maps.
No finite root group is opened while the third finite stage is in scope.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- Common finite upper stages prove the scalar power law independently
of an inclusion between the two selected finite fields. -/
theorem actualFiniteTameNormalizationMap_pow_of_dvd
    (E F : FiniteGaloisIntermediateField K L)
    (h : actualFiniteStageTameOrder A K L Q E ∣ actualFiniteStageTameOrder A K L Q F)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualFiniteTameNormalizationMap A K L Q F).toFun
        (actualFiniteRawTameValue A K L Q F σ) ^
        (actualFiniteStageTameOrder A K L Q F / actualFiniteStageTameOrder A K L Q E) =
      (actualFiniteTameNormalizationMap A K L Q E).toFun
        (actualFiniteRawTameValue A K L Q E σ) := by
  let T : FiniteGaloisIntermediateField K L := E ⊔ F
  have hE := actualFiniteTameNormalizationMap_tower A K L Q E T le_sup_left σ
  have hF := actualFiniteTameNormalizationMap_tower A K L Q F T le_sup_right σ
  have hFT := actualFiniteStageTameOrder_dvd_of_le A K L Q F T le_sup_right
  rw [hF, ← pow_mul, Nat.div_mul_div hFT h]
  exact hE.symm

/-- The scalar of the SAME quotient coordinate obeys every actual degree
divisibility relation. -/
theorem actualFiniteQuotientTameValue_pow_of_dvd
    (E F : FiniteGaloisIntermediateField K L)
    (h : actualFiniteStageTameOrder A K L Q E ∣ actualFiniteStageTameOrder A K L Q F)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    actualFiniteQuotientTameValue A K L Q F σ ^
        (actualFiniteStageTameOrder A K L Q F / actualFiniteStageTameOrder A K L Q E) =
      actualFiniteQuotientTameValue A K L Q E σ := by
  rw [actualFiniteQuotientTameValue_eq_normalizationMap A K L Q E σ,
    actualFiniteQuotientTameValue_eq_normalizationMap A K L Q F σ]
  exact ((normalizationMaximalQuotientResidueEquiv A L Q).symm.map_pow
    ((actualFiniteTameNormalizationMap A K L Q F).toFun
      (actualFiniteRawTameValue A K L Q F σ))
    (actualFiniteStageTameOrder A K L Q F / actualFiniteStageTameOrder A K L Q E)).symm.trans
      (congrArg (normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun
        (actualFiniteTameNormalizationMap_pow_of_dvd A K L Q E F h σ))

/-- Equal actual degrees give equal quotient scalars, independently of
which finite Galois stage realizes the degree. -/
theorem actualFiniteQuotientTameValue_eq_of_tameOrder_eq
    (E F : FiniteGaloisIntermediateField K L)
    (h : actualFiniteStageTameOrder A K L Q E = actualFiniteStageTameOrder A K L Q F)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    actualFiniteQuotientTameValue A K L Q E σ =
      actualFiniteQuotientTameValue A K L Q F σ := by
  have hdiv : actualFiniteStageTameOrder A K L Q E ∣ actualFiniteStageTameOrder A K L Q F :=
    h ▸ dvd_refl (actualFiniteStageTameOrder A K L Q E)
  have hvalue := actualFiniteQuotientTameValue_pow_of_dvd A K L Q E F hdiv σ
  rw [h, Nat.div_self (actualFiniteStageTameOrder_pos A K L Q F), pow_one] at hvalue
  exact hvalue.symm

end EtaleFundamentalGroups.Inertia
