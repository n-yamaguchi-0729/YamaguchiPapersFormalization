/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaSeparation
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.FiniteGrp

/-!
# Native group owners for original and finite wild inertia

The maps are the restrictions of the already constructed original inertia
maps to the independently defined subgroups. Their joint faithfulness is
inherited from actual finite inertia separation.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The SAME independent original wild subgroup as a native group object. -/
def actualNormalizationWildGroup : GrpCat.{w} := by
  let gP : Group (Subtype (actualNormalizationWildSubgroup A K L Q).carrier) :=
    Subgroup.toGroup (actualNormalizationWildSubgroup A K L Q)
  exact GrpCat.of (Subtype (actualNormalizationWildSubgroup A K L Q).carrier)

/-- The actual finite wild group with its proved finiteness. -/
def actualFiniteWildFiniteGroup (E : FiniteGaloisIntermediateField K L) : FiniteGrp.{w} := by
  have fI : Finite (actualFiniteStageInertiaGroup A K L Q E).carrier :=
    actualFiniteStageInertiaGroup_finite A K L Q E
  have fP : Finite (actualFiniteWildGroup A K L Q E).carrier :=
    Finite.of_injective
      (fun σ : (actualFiniteWildGroup A K L Q E).carrier =>
        (show (actualFiniteStageInertiaGroup A K L Q E).carrier from σ.val))
      Subtype.val_injective
  exact FiniteGrp.of (actualFiniteWildGroup A K L Q E).carrier

/-- The literal finite restriction on the independently defined global wild group. -/
def actualNormalizationWildRestriction (E : FiniteGaloisIntermediateField K L) :
    GrpCat.Hom (actualNormalizationWildGroup A K L Q) (actualFiniteWildGroup A K L Q E) where
  hom' :=
    { toFun := fun σ =>
        ⟨(actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ.val,
          (mem_actualNormalizationWildSubgroup A K L Q σ.val).mp σ.property E⟩
      map_one' := Subtype.ext (actualFiniteInertiaRestriction A K L Q E).hom'.map_one
      map_mul' := fun σ τ => Subtype.ext
        ((actualFiniteInertiaRestriction A K L Q E).hom'.map_mul σ.val τ.val) }

/-- The actual wild restrictions jointly determine an original wild element. -/
theorem actualNormalizationWildRestriction_jointly_injective
    (σ τ : (actualNormalizationWildGroup A K L Q).carrier)
    (h : ∀ E : FiniteGaloisIntermediateField K L,
      (actualNormalizationWildRestriction A K L Q E).hom'.toFun σ =
        (actualNormalizationWildRestriction A K L Q E).hom'.toFun τ) : σ = τ := by
  apply Subtype.ext
  apply actualFiniteInertiaRestriction_jointly_injective A K L Q
  intro E
  exact congrArg Subtype.val (h E)

end EtaleFundamentalGroups.Inertia

end
