/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Is Finite ring Krull Dim stalk quotient eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.IsFinite_ringKrullDim_stalk_quotient_eq_zero

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace FD0625672e

open scoped TensorProduct

theorem ringKrullDim_quotient_map_maximalIdeal_eq_zero
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.QuasiFinite R S] :
    ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0 := by
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars R)
  have : IsArtinianRing ((maximalIdeal R).Fiber S) := inferInstance
  have hA : IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    e.surjective.isArtinianRing
  have : Ring.KrullDimLE 0 (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp hA).2
  have : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
    rw [Ideal.Quotient.nontrivial_iff]
    exact ((((local_hom_TFAE (algebraMap R S)).out 1 3 rfl rfl).mp inferInstance).trans_lt
      (inferInstance : (maximalIdeal S).IsMaximal).ne_top.lt_top).ne
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

end FD0625672e

theorem _root_.AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      (maximalIdeal (Y.presheaf.stalk (g.base x))).map (g.stalkMap x).hom) = 0 := by
  let : Algebra (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := (g.stalkMap x).hom.toAlgebra
  have : Algebra.QuasiFinite (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := g.quasiFiniteAt x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  exact FD0625672e.ringKrullDim_quotient_map_maximalIdeal_eq_zero (Y.presheaf.stalk (g.base x))
    (X.presheaf.stalk x)

end AlgebraicCurves.Geometry.Schemes.Proofs.IsFinite_ringKrullDim_stalk_quotient_eq_zero
end ProofImplementation
