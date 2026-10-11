/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperGeometricallyReducedSections
import Nyll.SchemeTheory.Affine.SpecFlatBaseChangeSections
import Mathlib.RingTheory.Etale.Descent

/-!
# Étale descent for proper global sections along a field extension

The actual flat section comparison identifies the extended section
algebra with the global sections of the field-base-changed scheme.
Geometric reducedness there supplies étaleness, which faithfully flat
descent reflects to the original section algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- To obtain an étale proper section algebra over a field, it suffices
that the family becomes geometrically reduced after a field extension. -/
theorem etale_appTop_of_isProper_of_geometricallyReduced_field_baseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    [GeometricallyReduced
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L))))] :
    f.appTop.hom.Etale := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let fL := pullback.snd f g
  let : Algebra K Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra L Γ(pullback f g, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ fL.appTop).hom.toAlgebra
  have hEtaleL : Algebra.Etale L Γ(pullback f g, ⊤) :=
    (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of L)).inv fL.appTop).mpr
        (finite_etale_appTop_of_isProper_of_geometricallyReduced_overField fL).2
  have hEtaleTensor : Algebra.Etale L (L ⊗[K] Γ(X, ⊤)) :=
    Algebra.Etale.of_equiv (specPullbackSectionsTensorEquiv (A := L) f).symm
  have hEtale : Algebra.Etale K Γ(X, ⊤) :=
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat L
  exact (RingHom.Etale.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv f.appTop).mp hEtale

end AlgebraicGeometry
