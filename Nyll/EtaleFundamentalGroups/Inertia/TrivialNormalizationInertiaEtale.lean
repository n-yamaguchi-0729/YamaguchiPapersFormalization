/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.TrivialInertiaUnramified
import Nyll.EtaleFundamentalGroups.Purity.Local.DimensionOne
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# A DVR normalization with trivial inertia is finite étale

The integral closure in a finite Galois extension is finite and torsion-free.
Trivial inertia supplies unramifiedness even for imperfect residue fields,
and flatness over the DVR supplies étaleness.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- Trivial inertia at every closed normalization point gives an étale
normalization of a DVR, in arbitrary residue characteristic. -/
theorem integralClosure_etale_of_dvr_of_inertia_eq_bot
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hI : letI := IsIntegralClosure.MulSemiringAction R K L (integralClosure R L)
      ∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal R)], Q.inertia Gal(L/K) = ⊥) :
    Algebra.Etale R (integralClosure R L) := by
  let S := integralClosure R L
  let : Module.Finite R S := IsIntegralClosure.finite R K L S
  let : IsFractionRing S L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  let : MulSemiringAction Gal(L/K) S := IsIntegralClosure.MulSemiringAction R K L S
  have : IsGaloisGroup Gal(L/K) R S := IsGaloisGroup.of_isFractionRing Gal(L/K) R S K L
  have : Module.IsTorsionFree R L := Module.IsTorsionFree.trans_faithfulSMul R K L
  have : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R L
  apply etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
  intro Q hQ
  have hUnder : (Q.under R).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
      (fun x => Algebra.IsIntegral.isIntegral x) Q
  have : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.eq_maximalIdeal hUnder).symm⟩
  exact isUnramifiedAt_of_inertia_eq_bot Gal(L/K) (IsLocalRing.maximalIdeal R) hI Q

end EtaleFundamentalGroups.Inertia
