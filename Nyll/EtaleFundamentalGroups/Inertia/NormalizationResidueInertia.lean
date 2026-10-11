/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ResiduePointFixedness
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPointRigidity
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Literal point-and-residue inertia on an unramified normalization

An actual normalization endomorphism fixing a point and acting trivially
on its residue field fixes the canonical residue-field point morphism.
The proved normalization rigidity therefore makes that endomorphism the
identity. This uses the original point-and-residue condition directly,
without defining a substitute inertia group.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- On an unramified normalization of an integral source, the original
point-and-residue inertia condition forces the actual normalization
endomorphism to be the identity. -/
theorem normalizationEndomorphism_eq_id_of_trivial_residue
    {X S : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [FormallyUnramified f.fromNormalization] [LocallyOfFiniteType f.fromNormalization]
    (σ : X ⟶ X) (hσ : σ ≫ f = f) (y : f.normalization)
    (hy : normalizationEndomorphism f σ hσ y = y)
    (hres : (normalizationEndomorphism f σ hσ).residueFieldMap y =
      (f.normalization.residueFieldCongr hy).hom) :
    normalizationEndomorphism f σ hσ = 𝟙 f.normalization := by
  have hfixed : f.normalization.fromSpecResidueField y ≫
      normalizationEndomorphism f σ hσ = f.normalization.fromSpecResidueField y :=
    Scheme.Hom.fixes_fromSpecResidueField_of_residueFieldMap_eq
      (normalizationEndomorphism f σ hσ) y hy hres
  exact normalizationEndomorphism_eq_id_of_fixes_nonempty f σ hσ
    (f.normalization.fromSpecResidueField y) hfixed

end EtaleFundamentalGroups.Inertia
