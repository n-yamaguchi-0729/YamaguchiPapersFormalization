/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.SchemeFibreEndo
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# locally Quasi Finite of forall locally Quasi Finite scheme Fibre Endo
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
    {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hcomm : h ≫ f = f)
    (hfib : ∀ s : S, LocallyQuasiFinite (schemeFibreEndo f h hcomm s)) :
    LocallyQuasiFinite h := by
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro y
  let s : S := f.base y
  let ι : Spec (S.residueField s) ⟶ S := S.fromSpecResidueField s
  let Xs : Scheme.{u} := pullback f ι
  let π : Xs ⟶ X := pullback.fst f ι
  let hs : Xs ⟶ Xs := schemeFibreEndo f h hcomm s
  have : LocallyQuasiFinite hs := hfib s
  have hsq : IsPullback π hs h π := by
    refine IsPullback.of_isLimit' ⟨(schemeFibreEndo_fst f h hcomm s).symm⟩ ?_
    refine PullbackCone.IsLimit.mk _ (fun c => pullback.lift c.fst (c.snd ≫ pullback.snd f ι) ?_)
      ?_ ?_ ?_
    · calc c.fst ≫ f = c.fst ≫ (h ≫ f) := by rw [hcomm]
        _ = (c.fst ≫ h) ≫ f := (Category.assoc _ _ _).symm
        _ = (c.snd ≫ π) ≫ f := by rw [c.condition]
        _ = (c.snd ≫ pullback.snd f ι) ≫ ι :=
          by rw [Category.assoc, pullback.condition, Category.assoc]
    · intro c
      exact pullback.lift_fst _ _ _
    · intro c
      apply pullback.hom_ext
      · rw [Category.assoc, schemeFibreEndo_fst, ← Category.assoc, pullback.lift_fst, c.condition]
      · rw [Category.assoc, schemeFibreEndo_snd, pullback.lift_snd]
    · intro c m hm₁ hm₂
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        exact hm₁
      · rw [pullback.lift_snd, ← hm₂, Category.assoc, schemeFibreEndo_snd]
  let g : Spec (X.residueField y) ⟶ Xs :=
    pullback.lift (X.fromSpecResidueField y) (Spec.map (f.residueFieldMap y))
      (by rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField])
  have hg : g ≫ π = X.fromSpecResidueField y := pullback.lift_fst _ _ _
  have hcond : h.fiberι y ≫ h = h.fiberToSpecResidueField y ≫ X.fromSpecResidueField y :=
    pullback.condition
  let k : h.fiber y ⟶ Xs :=
    pullback.lift (h.fiberι y) (h.fiberToSpecResidueField y ≫ Spec.map (f.residueFieldMap y))
      (by
        calc h.fiberι y ≫ f = h.fiberι y ≫ (h ≫ f) := by rw [hcomm]
          _ = (h.fiberι y ≫ h) ≫ f := (Category.assoc _ _ _).symm
          _ = (h.fiberToSpecResidueField y ≫ X.fromSpecResidueField y) ≫ f := by rw [hcond]
          _ = (h.fiberToSpecResidueField y ≫ Spec.map (f.residueFieldMap y)) ≫ ι := by
              rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
                Category.assoc])
  have hk : k ≫ π = h.fiberι y := pullback.lift_fst _ _ _
  have hmid : k ≫ hs = h.fiberToSpecResidueField y ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, schemeFibreEndo_fst, ← Category.assoc, hk, hcond, Category.assoc, hg]
    · rw [Category.assoc, schemeFibreEndo_snd, pullback.lift_snd, Category.assoc, pullback.lift_snd]
  have hbig : IsPullback (k ≫ π) (h.fiberToSpecResidueField y) h (g ≫ π) := by
    rw [hk, hg]
    exact IsPullback.of_hasPullback h (X.fromSpecResidueField y)
  have hfinal : IsPullback k (h.fiberToSpecResidueField y) hs g := IsPullback.of_right hbig hmid hsq
  exact MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hfinal (hfib s)
end locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
