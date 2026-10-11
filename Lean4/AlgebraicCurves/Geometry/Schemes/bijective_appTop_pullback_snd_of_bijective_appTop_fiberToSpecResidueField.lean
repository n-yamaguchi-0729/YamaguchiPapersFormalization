/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import AlgebraicCurves.Geometry.Schemes.bijective_appTop_pullback_snd_of_bijective_appTop

/-!
# bijective app Top pullback snd of bijective app Top fiber To Spec Residue Field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace FibreIdentGC3

theorem bijective_of_bijective_comp_iso {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsIso g]
    (h : Function.Bijective (f ≫ g)) : Function.Bijective f := by
  have : IsIso (f ≫ g) := (ConcreteCategory.isIso_iff_bijective _).mpr h
  have : IsIso f := IsIso.of_isIso_comp_right f g
  exact ConcreteCategory.bijective_of_isIso f

theorem bijective_of_iso_comp_bijective {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsIso f]
    (h : Function.Bijective (f ≫ g)) : Function.Bijective g := by
  have : IsIso (f ≫ g) := (ConcreteCategory.isIso_iff_bijective _).mpr h
  have : IsIso g := IsIso.of_isIso_comp_left f g
  exact ConcreteCategory.bijective_of_isIso g

theorem bijective_comp_of_bijective {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsIso g]
    (h : Function.Bijective f) : Function.Bijective (f ≫ g) := by
  have : IsIso f := (ConcreteCategory.isIso_iff_bijective _).mpr h
  exact ConcreteCategory.bijective_of_isIso (f ≫ g)

theorem bijective_iso_comp_of_bijective {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsIso f]
    (h : Function.Bijective g) : Function.Bijective (f ≫ g) := by
  have : IsIso g := (ConcreteCategory.isIso_iff_bijective _).mpr h
  exact ConcreteCategory.bijective_of_isIso (f ≫ g)

theorem bijective_appTop_of_iso_over {P P' S : Scheme.{u}} (e : P ≅ P') (s : P ⟶ S) (s' : P' ⟶ S)
    (he : e.hom ≫ s' = s) (h : Function.Bijective s'.appTop) : Function.Bijective s.appTop := by
  rw [← he, Scheme.Hom.comp_appTop]
  have : IsIso e.hom.appTop := (inferInstance : IsIso (e.hom.app ⊤))
  exact bijective_comp_of_bijective _ _ h

end FibreIdentGC3

theorem
  _root_.AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
    {X Y : Scheme.{u}} (q : X ⟶ Y) [QuasiCompact q] [QuasiSeparated q]
    {K : Type u} [Field K] (k : Spec (CommRingCat.of K) ⟶ Y)
    (h : Function.Bijective (q.fiberToSpecResidueField (k.base (IsLocalRing.closedPoint
      K))).appTop) :
    Function.Bijective (pullback.snd q k).appTop := by
  set y := k.base (IsLocalRing.closedPoint K) with hy
  let φ : Y.residueField y ⟶ CommRingCat.of K := Y.descResidueField (Scheme.stalkClosedPointTo k)
  have hk : Spec.map φ ≫ Y.fromSpecResidueField y = k :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y k
  have hFibreQuasiSeparated : QuasiSeparated (q.fiberToSpecResidueField y) := by
    change QuasiSeparated (pullback.snd q (Y.fromSpecResidueField y))
    infer_instance
  have hFibreSpace : QuasiSeparatedSpace ↥(q.fiber y) :=
    @quasiSeparatedSpace_of_quasiSeparated _ _ (q.fiberToSpecResidueField y)
      inferInstance hFibreQuasiSeparated
  have h0 : Function.Bijective ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
    (q.fiberToSpecResidueField y).appTop) :=
    FibreIdentGC3.bijective_iso_comp_of_bijective _ _ h
  let : Algebra (Y.residueField y) K := φ.hom.toAlgebra
  have h1 := AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop
    (k := Y.residueField y) (q.fiberToSpecResidueField y) h0 K
  have hφ : CommRingCat.ofHom (algebraMap (Y.residueField y) K) = φ := rfl
  rw [hφ] at h1
  have h2 : Function.Bijective (pullback.snd (q.fiberToSpecResidueField y) (Spec.map φ)).appTop :=
    FibreIdentGC3.bijective_of_iso_comp_bijective _ _ h1
  let e : pullback (q.fiberToSpecResidueField y) (Spec.map φ) ≅ pullback q k :=
    pullbackLeftPullbackSndIso q (Y.fromSpecResidueField y) (Spec.map φ) ≪≫ pullback.congrHom rfl hk
  have he : e.hom ≫ pullback.snd q k = pullback.snd (q.fiberToSpecResidueField y) (Spec.map φ) := by
    change ((pullbackLeftPullbackSndIso q (Y.fromSpecResidueField y) (Spec.map φ)).hom ≫
      (pullback.congrHom rfl hk).hom) ≫ pullback.snd q k = _
    simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
      pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
    all_goals rfl
  exact FibreIdentGC3.bijective_appTop_of_iso_over e.symm _ _
    (by rw [Iso.symm_hom, Iso.inv_comp_eq, he]) h2
end bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
