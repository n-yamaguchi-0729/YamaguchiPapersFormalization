/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange

/-!
# Proj Space exists is Closed Immersion is Pullback comp eq map
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_isPullback_comp_eq_map
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (B : Type u) [CommRing B] [Algebra A B] :
    ∃ (Z' : Scheme.{u}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B))
      (_ : IsClosedImmersion ι') (e : Z' ⟶ Z),
      IsPullback e (ι' ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom
        (algebraMap A B))) ∧
      e ≫ ι = ι' ≫ ProjSpace.map A B n := by
  refine ⟨pullback ι (ProjSpace.map A B n), pullback.snd ι (ProjSpace.map A B n), inferInstance,
    pullback.fst ι (ProjSpace.map A B n), ?_, pullback.condition⟩
  exact (IsPullback.of_hasPullback ι (ProjSpace.map A B n)).paste_vert (ProjSpace.isPullback_map A
    B n)
end ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
