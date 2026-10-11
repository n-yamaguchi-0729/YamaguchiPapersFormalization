/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isReduced_of_smooth_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.SmoothReduced
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# is Reduced of smooth of field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.isReduced_of_smooth_of_field
open _root_.AlgebraicGeometry
open _root_.CategoryTheory

universe u



section SchemeLevel

private theorem ringHomSmooth_appTop {K : Type u} [Field K] {X : Scheme.{u}}
    [IsAffine X] (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] :
    RingHom.Smooth ((g.appTop).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) := by
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective))
    (HasRingHomProperty.appTop (P := @Smooth) g ‹Smooth g›)

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
end AlgebraicGeometry
open scoped _root_.AlgebraicGeometry in
theorem AlgebraicGeometry.isReduced_of_smooth_field
    {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [Smooth sX] :
    IsReduced X := by
  have : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    let U := X.affineCover.X i
    let g : U ⟶ Spec (CommRingCat.of K) := X.affineCover.f i ≫ sX
    have : IsAffine U := inferInstance
    have : Smooth g := inferInstance
    have hψ := ringHomSmooth_appTop g
    let : Algebra K Γ(U, ⊤) :=
      ((g.appTop).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    have hsm : Algebra.Smooth K Γ(U, ⊤) := hψ
    have : _root_.IsReduced ↑Γ(U, ⊤) := Algebra.Smooth.isReduced_of_field (K := K)
    exact isReduced_of_isAffine_isReduced U
  exact IsReduced.of_openCover X X.affineCover

end SchemeLevel

theorem _root_.AlgebraicGeometry.isReduced_of_smooth_of_field {K : Type u} [Field K] {X :
  Scheme.{u}} (sX : X ⟶ Spec (.of K)) [Smooth sX] :
    IsReduced X :=
  AlgebraicGeometry.isReduced_of_smooth_field sX
end AlgebraicCurves.Geometry.Schemes.Proofs.isReduced_of_smooth_of_field
end ProofImplementation
