/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_rigidified_cube_pullback_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product

/-!
# Pullback of a rigidified line bundle on a triple product

A base-change square compatible with multiplication also preserves the unit section.
The induced map on triple products therefore pulls back both the line bundle and
its rigidification along the cube section.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.CubePullback


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation
open _root_.AlgebraicGeometry.RelPicard


namespace CubeRigBC

variable {S₁ : Type} [CommRing S₁] {A₁ : Scheme.{0}}
  {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
  {S : Type} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
  (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)

theorem eq_one_of_mul_self {R : Type} [CommRing R] {B : Scheme.{0}}
    {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t g)
    (hx : G.mul t x x = x) : x = G.one t := by
  have h1 := congrArg (G.mul t (G.inv t x)) hx
  rwa [← G.mul_assoc, G.inv_mul_cancel, G.one_mul] at h1

include ha hLa in
theorem one_comp {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 ≫ a = (L₁.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  have h := hLa T t (L.one t) (L.one t)
  rw [L.one_mul] at h
  have hx := eq_one_of_mul_self L₁ (t ≫ Spec.map (CommRingCat.ofHom φ))
    ⟨(L.one t).1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, (L.one t).2]⟩
    (Subtype.ext h.symm)
  exact congrArg Subtype.val hx

include ha hLa in
theorem f_one_a : f ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ a =
    a ≫ f₁ ≫ (L₁.one (𝟙 (Spec (CommRingCat.of S₁)))).1 := by
  have hL : (L.one f).1 = f ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    have := L.one_natural (𝟙 (Spec (CommRingCat.of S))) f f (Category.comp_id f)
    rw [← this]; rfl
  have hL₁ : (L₁.one (a ≫ f₁)).1 = a ≫ f₁ ≫ (L₁.one (𝟙 (Spec (CommRingCat.of S₁)))).1 := by
    have := L₁.one_natural (𝟙 (Spec (CommRingCat.of S₁))) (a ≫ f₁) (a ≫ f₁) (Category.comp_id _)
    rw [← this]; rfl
  have key : (L₁.one (f ≫ Spec.map (CommRingCat.ofHom φ))).1 = (L₁.one (a ≫ f₁)).1 := by
    rw [ha.w]
  rw [← Category.assoc, ← hL, one_comp L₁ φ L a ha hLa f, key, hL₁]

/-- The map on triple fibre products induced by the given base-change square. -/
noncomputable abbrev a3 : pullback (prodStr f f) f ⟶ pullback (prodStr f₁ f₁) f₁ :=
  pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
    (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
    a (Spec.map (CommRingCat.ofHom φ))
    (by
      have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
          pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
      change (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
        pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
          pullback.fst f₁ f₁ ≫ f₁
      rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _),
        h1, Category.assoc, ha.w])
    ha.w.symm

include hLa in
theorem rigSection_comp_a3 :
    rigSection (prodStr f f) f ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) ≫ a3 φ a ha =
      a ≫ rigSection (prodStr f₁ f₁) f₁ ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of S₁)))) := by
  have hone := f_one_a L₁ φ L a ha hLa
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    unfold rigSection
    rw [pullback.lift_fst_assoc, pullback.lift_fst, RelativeGroupLaw.prod_one,
      RelativeGroupLaw.prod_one,
      prodPairPt_coe, prodPairPt_coe]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst,
        Category.assoc, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, hone]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd,
        Category.assoc, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, hone]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc]
    unfold rigSection
    rw [pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]

end CubeRigBC

open CubeRigBC in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem exists_rigidified_cube_pullback_of_isPullback
    {S₁ : Type} [CommRing S₁] {A₁ : Scheme.{0}}
    {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ : RelativeGroupLaw S₁ f₁)
    {S : Type} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    (M₁ : RigidifiedLineBundle (prodStr f₁ f₁)
      ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of S₁)))) f₁) :
    ∃ M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f,
      M.L = (Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 :
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            change (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _),
              h1, Category.assoc, ha.w])
          ha.w.symm)).obj M₁.L :=
  ⟨{ L := (Scheme.Modules.pullback (a3 φ a ha)).obj M₁.L
     isInvertible := M₁.isInvertible.pullback _
     rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app M₁.L ≪≫
        (Scheme.Modules.pullbackCongr (rigSection_comp_a3 L₁ φ L a ha hLa)).app M₁.L ≪≫
        ((Scheme.Modules.pullbackComp _ _).app M₁.L).symm ≪≫
        (Scheme.Modules.pullback a).mapIso M₁.rigidified.some ≪≫
        Scheme.Modules.pullbackUnitIso a⟩ }, rfl⟩
end JacobianVarieties.Picard.Proofs.CubePullback
end ProofImplementation
