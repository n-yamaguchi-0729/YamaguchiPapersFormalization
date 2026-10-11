/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationContinuity
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Topology.Constructions
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy of actual finite inertia restriction

The coefficient automorphism underlying the SAME intrinsic finite inertia
restriction factors through the locally constant finite Galois restriction.
Injectivity of the intrinsic subgroup inclusion then proves local constancy
without installing any replacement topology on the original inertia group.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The constructor for actual intrinsic restriction has the prescribed
coefficient automorphism. -/
theorem actualFiniteInertiaRestriction_coefficient
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ).val =
      (actualFiniteInertiaCoefficientMap A K L Q E).hom'.toFun σ := rfl

/-- The existing coefficient restriction is locally constant on original
inertia by restriction of the ambient coefficient map to its subgroup. -/
theorem actualFiniteInertiaCoefficientMap_isLocallyConstant
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L) :
    IsLocallyConstant (actualFiniteInertiaCoefficientMap A K L Q E).hom'.toFun :=
  (actualFiniteNormalizationRestriction_isLocallyConstant A K L E).comp_continuous
    continuous_subtype_val

/-- Restricting actual original inertia to its intrinsic finite normalization
inertia is locally constant for the original subgroup topology. -/
theorem actualFiniteInertiaRestriction_isLocallyConstant
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L) :
    IsLocallyConstant (actualFiniteInertiaRestriction A K L Q E).hom'.toFun := by
  have hmap :
      (fun σ : (actualNormalizationInertiaGroup A K L Q).carrier =>
        ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ).val) =
      (actualFiniteInertiaCoefficientMap A K L Q E).hom'.toFun :=
    funext (actualFiniteInertiaRestriction_coefficient A K L Q E)
  apply IsLocallyConstant.desc (actualFiniteInertiaRestriction A K L Q E).hom'.toFun
    (fun τ : (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)).carrier => τ.val)
  · change IsLocallyConstant
      (fun σ : (actualNormalizationInertiaGroup A K L Q).carrier =>
        ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ).val)
    rw [hmap]
    exact actualFiniteInertiaCoefficientMap_isLocallyConstant A K L Q E
  · exact Subtype.val_injective

/-- The actual restriction is continuous into the discrete intrinsic finite
group; more generally, it is continuous for any topology on that target. -/
theorem actualFiniteInertiaRestriction_continuous
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L)
    [TopologicalSpace (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)).carrier] :
    Continuous (actualFiniteInertiaRestriction A K L Q E).hom'.toFun :=
  (actualFiniteInertiaRestriction_isLocallyConstant A K L Q E).continuous

end EtaleFundamentalGroups.Inertia
