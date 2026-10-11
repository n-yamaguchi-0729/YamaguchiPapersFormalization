/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinateKernel
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The independent wild subgroup is detected by canonical finite characters

Only proved kernels of the actual normalized coordinates enter this
comparison. The global subgroup itself retains its principal-unit definition.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- An original inertia element is wild exactly when every SAME canonical
finite coordinate is trivial. -/
theorem mem_actualNormalizationWildSubgroup_iff_coordinates_eq_one
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    σ ∈ actualNormalizationWildSubgroup A K L Q ↔
      ∀ E : FiniteGaloisIntermediateField K L,
        (actualFiniteTameCoordinate A K L Q E).hom'.toFun σ = 1 := by
  simp only [actualNormalizationWildSubgroup, Subgroup.mem_iInf,
    ← actualFiniteTameCoordinate_ker, MonoidHom.mem_ker]
  rfl

end EtaleFundamentalGroups.Inertia
