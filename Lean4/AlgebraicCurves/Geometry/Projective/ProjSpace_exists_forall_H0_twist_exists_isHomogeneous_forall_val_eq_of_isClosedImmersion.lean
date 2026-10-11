/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.ProjectiveSpace.Basic
import SchemeTheory.ProjectiveSpace.Cover
import AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion

/-!
# Proj Space exists forall H0 twist exists is Homogeneous forall val eq of is Closed
Immersion
-/

section ProofImplementation

namespace AlgebraicGeometry.ProjSpace

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] :
    ∃ d₂ : ℕ, ∀ d : ℕ, d₂ ≤ d →
      ∀ c ∈ (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι),
        ∃ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (j : Fin (n + 1)),
            (c s).val j =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι
                  j ≤ ProjSpace.pullbackChart ι j)
                ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
                  (MvPolynomial.X j)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
                (MvPolynomial.X j)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X j ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow j d)⟩
                    den_mem := ⟨d, rfl⟩ }))) := by
  obtain ⟨d₂, hd₂⟩ :=
    exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion ι
  refine ⟨d₂, fun d hd c hc => ?_⟩
  obtain ⟨g, hg⟩ := AlgebraicGeometry.ProjSpace.exists_twistObj_top_forall_res_eq_of_mem_H0_twist ι
    d c hc
  obtain ⟨F, hF, hxF⟩ := hd₂ d hd (ProjSpace.objToTwistFam ι (ι ≫ ProjSpace.π A n) d g)
    (ProjSpace.objToTwistFam_mem ι (ι ≫ ProjSpace.π A n) d g)
  refine ⟨F, hF, fun s j => ?_⟩
  have hj := hxF j
  simp only [ProjSpace.objToTwistFam, ite_eq_left] at hj
  rw [← hg s]
  change ProjSpace.restrictFun _ (g.val j) = _
  rw [hj]
  erw [ProjSpace.restrictFun_restrictFun]
end AlgebraicGeometry.ProjSpace
end ProofImplementation
