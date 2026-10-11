/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.OriginalFiniteInertiaRestriction
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationCoefficientSquare
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTowerAction
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationLocalTower
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.RingTheory.Localization.PrimeLocalizationSquare
import Mathlib.Algebra.Group.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localization of finite inertia restrictions

Constructs the local ring maps induced by finite restrictions of original inertia. Proves their
coefficient equations and compatibility with finite normalization towers.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [rA : CommRing A] [fK : Field K] [fL : Field L]
  [aAK : Algebra A K] [frAK : IsFractionRing A K]
  [aKL : Algebra K L] [aAL : Algebra A L] [tAKL : IsScalarTower A K L]
  [gKL : IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [qPrime : Q.IsPrime]

omit qPrime in
/-- The prescribed finite coefficient restriction preserves the prescribed
finite prime, directly from the already-proved original coefficient congruence. -/
theorem actualFiniteNormalizationRestrictionRingHom_prime
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    finiteAbsoluteNormalizationPrime A K L Q E =
      (finiteAbsoluteNormalizationPrime A K L Q E).comap
        (actualFiniteNormalizationRestrictionRingHom A K L E
          (actualNormalizationInertiaElement A K L Q σ)) := by
  let P := finiteAbsoluteNormalizationPrime A K L Q E
  let s := actualFiniteNormalizationRestrictionRingHom A K L E
    (actualNormalizationInertiaElement A K L Q σ)
  have hdiff : ∀ b : finiteAbsoluteNormalizationAlgebra A K L E,
      s.toFun b - b ∈ P := originalInertia_finiteNormalization_difference A K L Q E σ
  apply Ideal.ext
  intro b
  change b ∈ P ↔ s.toFun b ∈ P
  constructor
  · intro hb
    simpa only [sub_add_cancel] using P.add_mem (hdiff b) hb
  · intro hb
    simpa only [sub_sub_self] using P.sub_mem hb (hdiff b)

/-- Localize the prescribed finite restriction using its proved prime
preservation. This is the same native localRingHom underlying its existing
individual inertia localization. -/
def actualFiniteInertiaLocalRingHom
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) →+*
      Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) := by
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact Localization.localRingHom
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (actualFiniteNormalizationRestrictionRingHom A K L E
      (actualNormalizationInertiaElement A K L Q σ))
    (actualFiniteNormalizationRestrictionRingHom_prime A K L Q E σ)

/-- The localized automorphism is the prescribed original finite restriction
on coefficients. -/
theorem actualFiniteInertiaLocalRingHom_algebraMap
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q)
    (b : finiteAbsoluteNormalizationAlgebra A K L E) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    (actualFiniteInertiaLocalRingHom A K L Q E σ).toFun
        (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) b) =
      algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
        ((actualFiniteNormalizationRestrictionRingHom A K L E
          (actualNormalizationInertiaElement A K L Q σ)).toFun b) := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact Localization.localRingHom_to_map
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (actualFiniteNormalizationRestrictionRingHom A K L E
      (actualNormalizationInertiaElement A K L Q σ))
    (actualFiniteNormalizationRestrictionRingHom_prime A K L Q E σ) b

/-- The same original inertia element acts compatibly on two actual finite
local normalizations. The square follows from the actual coefficient tower
square and the literal localRingHom coefficient equations. -/
theorem actualFiniteInertiaLocalRingHom_tower
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
    (actualFiniteNormalizationTowerLocalRingMap A K L Q E F h).comp
        (actualFiniteInertiaLocalRingHom A K L Q E σ) =
      (actualFiniteInertiaLocalRingHom A K L Q F σ).comp
        (actualFiniteNormalizationTowerLocalRingMap A K L Q E F h) := by
  let B : Type w := finiteAbsoluteNormalizationAlgebra A K L E
  let rB : CommRing B :=
    inferInstanceAs (CommRing (finiteAbsoluteNormalizationAlgebra A K L E))
  let C : Type w := finiteAbsoluteNormalizationAlgebra A K L F
  let rC : CommRing C :=
    inferInstanceAs (CommRing (finiteAbsoluteNormalizationAlgebra A K L F))
  let P : Ideal B := finiteAbsoluteNormalizationPrime A K L Q E
  let R : Ideal C := finiteAbsoluteNormalizationPrime A K L Q F
  have pPrime : P.IsPrime := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have rPrime : R.IsPrime := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
  let f : B →+* C := actualFiniteNormalizationTowerRingMap A K L E F h
  let s : B →+* B := actualFiniteNormalizationRestrictionRingHom A K L E
    (actualNormalizationInertiaElement A K L Q σ)
  let t : C →+* C := actualFiniteNormalizationRestrictionRingHom A K L F
    (actualNormalizationInertiaElement A K L Q σ)
  have hf : P = R.comap f := actualFiniteNormalizationPrime_tower A K L Q E F h
  have hs : P = P.comap s :=
    actualFiniteNormalizationRestrictionRingHom_prime A K L Q E σ
  have ht : R = R.comap t :=
    actualFiniteNormalizationRestrictionRingHom_prime A K L Q F σ
  have hcomm : f.comp s = t.comp f := actualFiniteNormalizationTowerRingMap_action
    A K L E F h (actualNormalizationInertiaElement A K L Q σ)
  change (Localization.localRingHom P R f hf).comp (Localization.localRingHom P P s hs) =
    (Localization.localRingHom R R t ht).comp (Localization.localRingHom P R f hf)
  clear_value f s t P R
  clear_value rB rC
  clear_value B C
  clear actualFiniteInertiaLocalRingHom_tower
  clear σ h E F qPrime Q gKL tAKL aAL aKL frAK aAK fL L fK K rA A
  exact primeLocalization_commuting_square P R f s t hf hs ht hcomm

end EtaleFundamentalGroups.Inertia

end
