/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Morphisms.UnramifiedPointRigidity
import EtaleFundamentalGroups.Inertia.NormalizationBaseChange
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Point rigidity of actual normalization endomorphisms

Normalization of an integral source is integral and its structure map is
separated. If this structure map is unramified, fixing a nonempty test
morphism forces an actual normalization endomorphism to be the identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The actual extension by normalization is rigid at a nonempty point
whenever the normalization morphism is unramified. -/
theorem normalizationEndomorphism_eq_id_of_fixes_nonempty
    {X S T : Scheme.{u}} [IsIntegral X] [Nonempty T]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [FormallyUnramified f.fromNormalization] [LocallyOfFiniteType f.fromNormalization]
    (σ : X ⟶ X) (hσ : σ ≫ f = f) (z : T ⟶ f.normalization)
    (hz : z ≫ normalizationEndomorphism f σ hσ = z) :
    normalizationEndomorphism f σ hσ = 𝟙 f.normalization :=
  Scheme.Hom.eq_id_of_unramified_of_fixes_nonempty f.fromNormalization
    (normalizationEndomorphism f σ hσ) (normalizationEndomorphism_fromNormalization f σ hσ)
    z hz

end EtaleFundamentalGroups.Inertia
