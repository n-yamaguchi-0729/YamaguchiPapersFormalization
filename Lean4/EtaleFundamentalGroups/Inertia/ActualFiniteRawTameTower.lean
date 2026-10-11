/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.ActualFiniteRawTameValue
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaLocalization
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaAmbientResidue
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationLocalTower
import EtaleFundamentalGroups.Inertia.ActualFiniteLocalResidue
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.RingTheory.Localization.DedekindPrime
import ValuedFieldTheory.Ramification.HilbertRamification.RingAmbientCoefficientTower

/-!
# Raw tame values in finite towers

Proves the power relation between raw coefficient-ratio residues of the same original inertia
element at nested finite local normalizations.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v w

/-- The two independently constructed raw values of the SAME original inertia
element satisfy the literal finite local tower relation. The ratio witnesses,
commuting square, residue fixedness and ambient triangle are all supplied by
their original-input owners. No finite inertia action or roots carrier is opened. -/
theorem actualFiniteRawTameValue_tower
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
    letI := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L F
    letI := localizationAtPrime_isDiscreteValuationRing
      (finiteAbsoluteNormalizationAlgebra A K L F)
      (finiteAbsoluteNormalizationPrime A K L Q F)
      (finiteAbsoluteNormalizationPrime_ne_bot A K L Q F)
    ∃ π : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E),
      Irreducible π ∧
      actualFiniteRawTameValue A K L Q E σ =
        actualFiniteRawTameValue A K L Q F σ ^
          ((IsDiscreteValuationRing.addVal
            (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q F))).toFun
            ((actualFiniteNormalizationTowerLocalRingMap A K L Q E F h).toFun π)).toNat := by
  let pE := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let pF := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
  let dF := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L F
  let vF := localizationAtPrime_isDiscreteValuationRing
    (finiteAbsoluteNormalizationAlgebra A K L F)
    (finiteAbsoluteNormalizationPrime A K L Q F)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q F)
  obtain ⟨π, c, hπ, _, hc, hE⟩ := actualFiniteRawTameValue_exists_coefficient A K L Q E σ
  obtain ⟨ρ, d, hρ, _, hd, hF⟩ := actualFiniteRawTameValue_exists_coefficient A K L Q F σ
  refine ⟨π, hπ, ?_⟩
  have hraw := uniformizerAmbientCoefficient_tower_addVal_of_ringHom
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q F)) Q.ResidueField
    (actualFiniteNormalizationTowerLocalRingMap A K L Q E F h)
    (actualFiniteNormalizationTowerLocalRingMap_injective A K L Q E F h)
    (actualFiniteInertiaLocalRingHom A K L Q E σ)
    (actualFiniteInertiaLocalRingHom A K L Q F σ)
    (actualFiniteInertiaLocalRingHom_tower A K L Q E F h σ)
    (actualFiniteLocalResidueMap A K L Q E) (actualFiniteLocalResidueMap A K L Q F)
    (actualFiniteLocalResidueMap_tower A K L Q E F h)
    (actualFiniteLocalResidueMap_comp_inertia A K L Q F σ)
    π hπ ρ hρ c d hc hd
  exact hE.trans (hraw.trans (congrArg
    (fun z : Q.ResidueField => z ^
      ((IsDiscreteValuationRing.addVal
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q F))).toFun
        ((actualFiniteNormalizationTowerLocalRingMap A K L Q E F h).toFun π)).toNat)
    hF.symm))

end EtaleFundamentalGroups.Inertia

end
