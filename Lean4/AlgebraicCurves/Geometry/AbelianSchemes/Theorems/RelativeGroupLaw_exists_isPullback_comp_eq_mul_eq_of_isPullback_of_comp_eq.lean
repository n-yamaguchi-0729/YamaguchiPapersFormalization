/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_of_isPullback

/-!
# Relative Group Law exists is Pullback comp eq mul eq of is Pullback of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace DescB

theorem baseChange_mul_fst {S S' : Type} [CommRing S] [CommRing S']
    (u : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' (pullback.snd f
      u)) :
    ((G.baseChange u).mul t' x y).1 ≫ pullback.fst f u =
      (G.mul (t' ≫ u)
        ⟨x.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ pullback.fst f u,
          by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩).1 := by
  have h := congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul u G t' x y)
  rw [RelativeGroupLaw.baseChangePointToBase_coe] at h
  exact h

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (G : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1)
      :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

end DescB

end RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

namespace GoodReductionJacobian.RelativeGroupLaw



open _root_.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian in
open DescB in
theorem exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L :
      RelativeGroupLaw R f)
    {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (φ₁ : R₁ →+* R) (φ₂ : R₂ →+* R) (ψ : R₁ →+* R₂) (hψ
      : φ₂.comp ψ = φ₁)
    (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)) (L₁ : RelativeGroupLaw R₁ f₁) (hA₁ :
      AbelianSchemePropertyBundle R₁ f₁)
    (a₁ : A ⟶ A₁) (ha₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom φ₁)))
    (hLa₁ : (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ₁))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1)) :
    ∃ (A₂ : Scheme.{0}) (f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)) (L₂ : RelativeGroupLaw R₂ f₂) (_ :
      AbelianSchemePropertyBundle R₂ f₂)
      (a₂ : A ⟶ A₂) (ha₂ : IsPullback a₂ f f₂ (Spec.map (CommRingCat.ofHom φ₂)))
      (b : A₂ ⟶ A₁) (hb : IsPullback b f₂ f₁ (Spec.map (CommRingCat.ofHom ψ))) (_ : a₂ ≫ b = a₁),
      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₂ = (L₂.mul (t ≫ Spec.map (CommRingCat.ofHom φ₂))
        ⟨P.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R₂)) (P Q : SchemeHomOver t f₂),
      (L₂.mul t P Q).1 ≫ b = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom ψ))
        ⟨P.1 ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, Q.2]⟩).1) := by
  have hSpec : Spec.map (CommRingCat.ofHom φ₁) =
      Spec.map (CommRingCat.ofHom φ₂) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  let ι := Spec.map (CommRingCat.ofHom ψ)
  have hP := IsPullback.of_hasPullback f₁ ι
  let a₂ : A ⟶ pullback f₁ ι := pullback.lift a₁ (f ≫ Spec.map (CommRingCat.ofHom φ₂))
    (by rw [ha₁.w, hSpec, Category.assoc])
  have ha₂fst : a₂ ≫ pullback.fst f₁ ι = a₁ := pullback.lift_fst _ _ _
  have ha₂snd : a₂ ≫ pullback.snd f₁ ι = f ≫ Spec.map (CommRingCat.ofHom φ₂) := pullback.lift_snd _
    _ _
  have ha₂ : IsPullback a₂ f (pullback.snd f₁ ι) (Spec.map (CommRingCat.ofHom φ₂)) := by
    refine IsPullback.of_right ?_ ha₂snd hP
    rw [ha₂fst, ← hSpec]
    exact ha₁
  refine ⟨pullback f₁ ι, pullback.snd f₁ ι, L₁.baseChange ι,
    GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback hA₁ hP, a₂, ha₂, pullback.fst
      f₁ ι, hP, ha₂fst, ?_, ?_⟩
  · intro T t P Q
    apply pullback.hom_ext
    · rw [Category.assoc, ha₂fst, hLa₁ T t P Q, baseChange_mul_fst]
      exact mul_val_congr L₁ (by rw [hSpec, Category.assoc]) _ _ _ _
        (show P.1 ≫ a₁ = (P.1 ≫ a₂) ≫ pullback.fst f₁ ι by rw [Category.assoc, ha₂fst])
        (show Q.1 ≫ a₁ = (Q.1 ≫ a₂) ≫ pullback.fst f₁ ι by rw [Category.assoc, ha₂fst])
    · have h1 : (L.mul t P Q).1 ≫ a₂ ≫ pullback.snd f₁ ι = t ≫ Spec.map (CommRingCat.ofHom φ₂) := by
        rw [ha₂snd, ← Category.assoc, (L.mul t P Q).2]
      rw [Category.assoc]
      symm
      refine Eq.trans ?_ h1.symm
      exact ((L₁.baseChange ι).mul (t ≫ Spec.map (CommRingCat.ofHom φ₂))
        ⟨P.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, Q.2]⟩).2
  · intro T t P Q
    exact baseChange_mul_fst ι L₁ t P Q
end GoodReductionJacobian.RelativeGroupLaw
end ProofImplementation

attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst
