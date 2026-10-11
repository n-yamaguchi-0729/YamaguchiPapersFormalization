/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange

/-!
# Proj Space exists iso hom comp eq of is Pullback of comp eq map
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
    (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Z : Scheme.{0})
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (Z₁ : Scheme.{0}) (ι₁ : Z₁ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₁ : Z₁
      ⟶ Z)
    (h₁ : IsPullback e₁ (ι₁ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom
      (algebraMap A B))))
    (h₁' : e₁ ≫ ι = ι₁ ≫ ProjSpace.map A B n)
    (Z₂ : Scheme.{0}) (ι₂ : Z₂ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₂ : Z₂
      ⟶ Z)
    (h₂ : IsPullback e₂ (ι₂ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom
      (algebraMap A B))))
    (h₂' : e₂ ≫ ι = ι₂ ≫ ProjSpace.map A B n) :
    ∃ φ : Z₁ ≅ Z₂, φ.hom ≫ ι₂ = ι₁ ∧ φ.hom ≫ e₂ = e₁ := by
  refine ⟨h₁.isoIsPullback _ _ h₂, ?_, by simp⟩
  apply (AlgebraicGeometry.ProjSpace.isPullback_map A B n).hom_ext
  · rw [Category.assoc, ← h₂', ← Category.assoc, IsPullback.isoIsPullback_hom_fst, h₁']
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd]
end ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
