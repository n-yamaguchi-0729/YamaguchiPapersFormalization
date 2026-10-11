/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteTameNormalizationMap
import EtaleFundamentalGroups.Inertia.ActualFiniteRawTameTower
import EtaleFundamentalGroups.Inertia.ActualFiniteRawTameValue
import EtaleFundamentalGroups.Inertia.ActualFiniteTameOrderTower
import EtaleFundamentalGroups.Inertia.ActualFiniteTameIndex
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTowerOrder
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationLocalTower
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.RingTheory.Localization.DedekindPrime
import ValuedFieldTheory.Ramification.HilbertRamification.CanonicalCharacterTower
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# Tower compatibility of canonical tame coordinates

Proves compatibility of finite tame coordinates with the power maps determined by tame-order
ratios. Deduces independence of the finite stage when tame orders agree.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory RamificationTheory.HilbertRamification

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- Apply the actual normalization operations to the proved raw scalar
tower. Once the raw values and their equation are retained, the original
inertia element is cleared before either e/n expression is opened. -/
theorem actualFiniteTameNormalizationMap_tower
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    (actualFiniteTameNormalizationMap A K L Q E).toFun
        (actualFiniteRawTameValue A K L Q E σ) =
      (actualFiniteTameNormalizationMap A K L Q F).toFun
        (actualFiniteRawTameValue A K L Q F σ) ^
          (actualFiniteStageTameOrder A K L Q F / actualFiniteStageTameOrder A K L Q E) := by
  let pE := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let pF := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
  let dF := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L F
  let vF := localizationAtPrime_isDiscreteValuationRing
    (finiteAbsoluteNormalizationAlgebra A K L F)
    (finiteAbsoluteNormalizationPrime A K L Q F)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q F)
  obtain ⟨π, hπ, hraw⟩ := actualFiniteRawTameValue_tower A K L Q E F h σ
  let xE : Q.ResidueField := actualFiniteRawTameValue A K L Q E σ
  let xF : Q.ResidueField := actualFiniteRawTameValue A K L Q F σ
  change (actualFiniteTameNormalizationMap A K L Q E).toFun xE =
    (actualFiniteTameNormalizationMap A K L Q F).toFun xF ^
      (actualFiniteStageTameOrder A K L Q F / actualFiniteStageTameOrder A K L Q E)
  change xE = xF ^
    ((IsDiscreteValuationRing.addVal
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q F))).toFun
      ((actualFiniteNormalizationTowerLocalRingMap A K L Q E F h).toFun π)).toNat at hraw
  clear_value xE xF
  clear actualFiniteTameNormalizationMap_tower
  clear σ
  let nE : ℕ := actualFiniteStageTameOrder A K L Q E
  let nF : ℕ := actualFiniteStageTameOrder A K L Q F
  let eE : ℕ := (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A
  let eF : ℕ := (finiteAbsoluteNormalizationPrime A K L Q F).ramificationIdx A
  have hnEpos : 0 < nE := actualFiniteStageTameOrder_pos A K L Q E
  have hnE : nE ∣ eE := (actualFiniteStage_tame_arithmetic A K L Q E).1
  have hnF : nF ∣ eF := (actualFiniteStage_tame_arithmetic A K L Q F).1
  have hnEF : nE ∣ nF := actualFiniteStageTameOrder_dvd_of_le A K L Q E F h
  have he : eF =
      ((IsDiscreteValuationRing.addVal
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q F))).toFun
        ((actualFiniteNormalizationTowerLocalRingMap A K L Q E F h).toFun π)).toNat * eE :=
    actualFiniteNormalization_ramificationIdx_tower_addVal A K L Q E F h π hπ
  change xE ^ (eE / nE) = (xF ^ (eF / nF)) ^ (nF / nE)
  exact normalizedCharacter_tower (MonoidHom.id Q.ResidueField) xE xF
    hnEpos hnE hnF hnEF he hraw

/-- The SAME canonical ambient residue coordinate is compatible with the
actual finite tower, with exponent the ratio of the actual tame orders.
All restriction, residue, ramification and normalization inputs are proved
from the original data, rather than supplied as comparison hypotheses. -/
theorem actualFiniteTameCoordinate_tower
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val =
      (((actualFiniteTameCoordinate A K L Q F).hom'.toFun σ).val).val ^
        (actualFiniteStageTameOrder A K L Q F / actualFiniteStageTameOrder A K L Q E) := by
  exact (actualFiniteTameCoordinate_eq_normalizationMap A K L Q E σ).trans
    ((actualFiniteTameNormalizationMap_tower A K L Q E F h σ).trans
      (congrArg
        (fun z : Q.ResidueField => z ^
          (actualFiniteStageTameOrder A K L Q F / actualFiniteStageTameOrder A K L Q E))
        (actualFiniteTameCoordinate_eq_normalizationMap A K L Q F σ).symm))

/-- A finite stage representing a given tame order does not affect the
SAME canonical ambient coordinate. The actual finite Galois compositum is
used as a common upper stage, so no choice or comparison datum is assumed. -/
theorem actualFiniteTameCoordinate_eq_of_tameOrder_eq
    (E F : FiniteGaloisIntermediateField K L)
    (hn : actualFiniteStageTameOrder A K L Q E = actualFiniteStageTameOrder A K L Q F)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val =
      (((actualFiniteTameCoordinate A K L Q F).hom'.toFun σ).val).val := by
  let T : FiniteGaloisIntermediateField K L := E ⊔ F
  have hE := actualFiniteTameCoordinate_tower A K L Q E T le_sup_left σ
  have hF := actualFiniteTameCoordinate_tower A K L Q F T le_sup_right σ
  have hp :
      (((actualFiniteTameCoordinate A K L Q T).hom'.toFun σ).val).val ^
          (actualFiniteStageTameOrder A K L Q T / actualFiniteStageTameOrder A K L Q E) =
        (((actualFiniteTameCoordinate A K L Q T).hom'.toFun σ).val).val ^
          (actualFiniteStageTameOrder A K L Q T / actualFiniteStageTameOrder A K L Q F) :=
    congrArg (fun n : ℕ =>
      (((actualFiniteTameCoordinate A K L Q T).hom'.toFun σ).val).val ^
        (actualFiniteStageTameOrder A K L Q T / n)) hn
  exact hE.trans (hp.trans hF.symm)

end EtaleFundamentalGroups.Inertia

end
