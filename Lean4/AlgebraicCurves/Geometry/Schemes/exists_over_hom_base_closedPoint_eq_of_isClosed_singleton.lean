/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Rational points corresponding to closed points

Over an algebraically closed field, a closed point of a scheme locally of finite type
is the image of the closed point under a morphism over the field.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_over_hom_base_closedPoint_eq_of_isClosed_singleton

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t, z.left.base
        (IsLocalRing.closedPoint k) = x := by
  refine ⟨Over.homMk (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ?_, ?_⟩
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ≫ t = 𝟙 _
    rw [Category.assoc, ← SpecMap_residueFieldIsoBase_inv t x hx, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id]
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) = x
    have hmem : (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) ∈ Set.range (X.fromSpecResidueField x).base :=
      ⟨(Spec.map (residueFieldIsoBase t x hx).hom).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem
end exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
