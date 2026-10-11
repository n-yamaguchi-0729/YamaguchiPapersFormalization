/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteNormalizationGaloisFaithful
import EtaleFundamentalGroups.Inertia.FiniteGaloisRestrictionSeparation
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationRestriction
import SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Actual finite inertia restrictions separate original inertia

Finite normalization faithfulness and finite Galois closure separation are
both proved from the original inputs. No separation premise is added.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Every original inertia element is determined by its actual intrinsic
finite-normalization restrictions. -/
theorem actualFiniteInertiaRestriction_jointly_injective
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (σ τ : (actualNormalizationInertiaGroup A K L Q).carrier)
    (h : ∀ E : FiniteGaloisIntermediateField K L,
      (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ =
        (actualFiniteInertiaRestriction A K L Q E).hom'.toFun τ) : σ = τ := by
  apply Subtype.ext
  apply finiteGaloisRestrictionGroupMap_jointly_injective K L
  intro E
  apply finiteNormalizationGaloisGroupMap_injective A K L E
  exact congrArg Subtype.val (h E)

end EtaleFundamentalGroups.Inertia
