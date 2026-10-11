/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoefficientEvaluation
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.ActualFiniteLocalResidue
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaLocalization
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.RingTheory.Localization.DedekindPrime
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import ValuedFieldTheory.Ramification.HilbertRamification.RingHomUniformizerCoefficient

/-!
# Raw coefficient-ratio values of finite inertia

Constructs the ambient residue of a finite local uniformizer ratio and supplies its unit
coefficient witness. Expresses the canonical tame coordinate as its normalization power.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- The ambient residue of an actual coefficient ratio σ(π)/π. The
uniformizer and ratio are constructed in the literal finite local ring;
this is the raw value, before the canonical e/n power is applied. -/
def actualFiniteRawTameValue (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) : Q.ResidueField := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  let : IsDiscreteValuationRing
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) :=
    localizationAtPrime_isDiscreteValuationRing
      (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)
      (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
  let hπ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
  exact (actualFiniteLocalResidueMap A K L Q E).toFun
    (ringHomUniformizerCoefficient
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
      (actualFiniteInertiaLocalRingHom A K L Q E σ) hπ.choose)

/-- The constructed raw scalar comes from an actual unit coefficient of
an actual uniformizer. No roots carrier or normalized character is exposed
in this interface, so two raw stages may be compared before normalization. -/
theorem actualFiniteRawTameValue_exists_coefficient
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    ∃ π c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E),
      Irreducible π ∧ IsUnit c ∧
      π * c = (actualFiniteInertiaLocalRingHom A K L Q E σ).toFun π ∧
      actualFiniteRawTameValue A K L Q E σ =
        (actualFiniteLocalResidueMap A K L Q E).toFun c := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  let : IsDiscreteValuationRing
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) :=
    localizationAtPrime_isDiscreteValuationRing
      (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)
      (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
  let hπ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
  let hc := actualFiniteTameCoordinate_exists_coefficient A K L Q E σ hπ.choose hπ.choose_spec
  have hs := ringHomUniformizerCoefficient_unit_spec
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
    (actualFiniteInertiaLocalRingHom A K L Q E σ) hπ.choose hπ.choose_spec.ne_zero
    ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2.1⟩
  exact ⟨hπ.choose, ringHomUniformizerCoefficient
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
      (actualFiniteInertiaLocalRingHom A K L Q E σ) hπ.choose,
    hπ.choose_spec, hs.1, hs.2, rfl⟩

/-- The SAME existing canonical coordinate is the e/n power of the actual
raw coefficient scalar just constructed. -/
theorem actualFiniteTameCoordinate_eq_raw_pow
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val =
      actualFiniteRawTameValue A K L Q E σ ^
        ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
          actualFiniteStageTameOrder A K L Q E) := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  let : IsDiscreteValuationRing
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) :=
    localizationAtPrime_isDiscreteValuationRing
      (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)
      (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
  let hπ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
  let hc := actualFiniteTameCoordinate_exists_coefficient A K L Q E σ
    hπ.choose hπ.choose_spec
  have heq := ringHomUniformizerCoefficient_eq_of_mul_eq
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
    (actualFiniteInertiaLocalRingHom A K L Q E σ) hπ.choose hπ.choose_spec.ne_zero
    hc.choose hc.choose_spec.2.1
  exact hc.choose_spec.2.2.trans (congrArg
    (fun c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) =>
      (actualFiniteLocalResidueMap A K L Q E).toFun c ^
        ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
          actualFiniteStageTameOrder A K L Q E)) heq.symm)

end EtaleFundamentalGroups.Inertia

end
