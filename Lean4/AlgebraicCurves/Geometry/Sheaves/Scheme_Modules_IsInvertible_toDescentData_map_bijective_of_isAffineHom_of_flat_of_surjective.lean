/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_toDescentData_map_bijective_of_openCover
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_toDescentData_map_bijective_unit_of_flat_of_surjective

/-!
# Scheme Modules Is Invertible to Descent Data map bijective of is Affine Hom of flat of
surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleDescentFullyFaithful

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.CategoryTheory.Bicategory

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace HomDescFF
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

/-- The pseudofunctor of modules used for descent. -/
abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (AlgebraicGeometry.Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem isSeparatedFor_of_le {C : Type*} [Category C] {P : Cᵒᵖ ⥤ Type*} {X : C}
    {R R' : Presieve X} (h : R ≤ R') (hR : Presieve.IsSeparatedFor P R) :
    Presieve.IsSeparatedFor P R' := by
  intro x t₁ t₂ ht₁ ht₂
  exact hR (x.restrict h) t₁ t₂ (Presieve.isAmalgamation_restrict h x t₁ ht₁)
    (Presieve.isAmalgamation_restrict h x t₂ ht₂)

theorem bijective_map_iff_of_iso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M M' N N' : C} (eM : M ≅ M') (eN : N ≅ N') :
    Function.Bijective (F.map : (M ⟶ N) → _) ↔ Function.Bijective (F.map : (M' ⟶ N') → _) := by
  have hcomp : (F.map : (M' ⟶ N') → _) ∘ (Iso.homCongr eM eN) =
      (Iso.homCongr (F.mapIso eM) (F.mapIso eN)) ∘ (F.map : (M ⟶ N) → _) := by
    funext f
    simp [Iso.homCongr_apply, Functor.map_comp]
  constructor
  · intro h
    have h1 : Function.Bijective ((Iso.homCongr (F.mapIso eM) (F.mapIso eN)) ∘ (F.map : (M ⟶ N) →
      _)) :=
      (Function.Bijective.of_comp_iff' (Iso.homCongr (F.mapIso eM) (F.mapIso eN)).bijective _).mpr h
    rw [← hcomp] at h1
    exact (Function.Bijective.of_comp_iff _ (Iso.homCongr eM eN).bijective).mp h1
  · intro h
    have h1 : Function.Bijective ((F.map : (M' ⟶ N') → _) ∘ (Iso.homCongr eM eN)) :=
      (Function.Bijective.of_comp_iff _ (Iso.homCongr eM eN).bijective).mpr h
    rw [hcomp] at h1
    exact (Function.Bijective.of_comp_iff' (Iso.homCongr (F.mapIso eM) (F.mapIso eN)).bijective
      _).mp h1

/--
The trivialization of a pullback obtained by factoring through a morphism with a given
trivialization.
-/
def trivOfFac {X T U : Scheme.{u}} {L : X.Modules} (g : U ⟶ X) (t : T ⟶ X) (a : T ⟶ U) (h : a ≫ g =
  t)
    (e : (Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit U.ringCatSheaf) :
    (Scheme.Modules.pullback t).obj L ≅ SheafOfModules.unit T.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr h.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp a g).app L).symm ≪≫
    (Scheme.Modules.pullback a).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso a

variable {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) (L₁ L₂ : Y.Modules)

theorem pullback_sieve_eq (Z : Over Y) (f : Z ⟶ Over.mk (𝟙 Y)) :
    Sieve.pullback (Over.isoMk (Iso.refl Z.left) (by simp) :
        (Over.map Z.hom).obj (Over.mk (𝟙 Z.left)) ≅ Z).inv
      (Sieve.functorPushforward (Over.map Z.hom)
        (Sieve.generate (Presieve.ofArrows (fun _ : Unit => Over.mk (pullback.snd q Z.hom))
          (fun _ : Unit => Over.homMk (pullback.snd q Z.hom))))) =
    Sieve.pullback f (Sieve.generate (Presieve.ofArrows (fun _ : Unit => Over.mk q)
          (fun _ : Unit => Over.homMk q))) := by
  have hf : f.left = Z.hom := by simpa using Over.w f
  ext W k
  have hkw : k.left ≫ Z.hom = W.hom := Over.w k
  constructor
  · rintro ⟨Z'', g, h, ⟨Y₃, m, f', ⟨i⟩, rfl⟩, fac⟩
    have hm : m.left ≫ pullback.snd q Z.hom = Z''.hom := Over.w m
    have hh : h.left ≫ (Z''.hom ≫ Z.hom) = W.hom := Over.w h
    have hk : k.left = h.left ≫ m.left ≫ pullback.snd q Z.hom := by
      have := congr_arg CommaMorphism.left fac
      simpa using this
    have key : (h.left ≫ m.left ≫ pullback.fst q Z.hom) ≫ q = k.left ≫ Z.hom := by
      rw [hk]
      simp only [Category.assoc]
      erw [pullback.condition]
      try rfl
    refine ⟨Over.mk q, Over.homMk (h.left ≫ m.left ≫ pullback.fst q Z.hom) (key.trans hkw),
      Over.homMk q,
      ⟨()⟩, ?_⟩
    ext
    simp only [Over.comp_left, Over.homMk_left]
    erw [key, hf]
    try rfl
  · rintro ⟨Y₃, b, f', ⟨i⟩, fac⟩
    have hb : b.left ≫ q = k.left ≫ Z.hom := by
      have := congr_arg CommaMorphism.left fac
      simpa [hf] using this
    have hl : pullback.lift b.left k.left hb ≫ pullback.snd q Z.hom = k.left := pullback.lift_snd _
      _ _
    refine ⟨Over.mk (pullback.snd q Z.hom), Over.homMk (pullback.snd q Z.hom),
      Over.homMk (pullback.lift b.left k.left hb) ?_, ?_, ?_⟩
    · change pullback.lift b.left k.left hb ≫ (pullback.snd q Z.hom ≫ Z.hom) = W.hom
      rw [← Category.assoc]
      erw [hl]
      exact hkw
    · exact ⟨Over.mk (pullback.snd q Z.hom), 𝟙 _, Over.homMk (pullback.snd q Z.hom), ⟨()⟩,
        Category.id_comp _⟩
    · ext
      change k.left ≫ 𝟙 _ = pullback.lift b.left k.left hb ≫ pullback.snd q Z.hom
      erw [hl]
      simp

theorem isSheafFor_pullback_of_trivial [QuasiCompact q] [Flat q] [Surjective q]
    (Z : Over Y) (f : Z ⟶ Over.mk (𝟙 Y))
    (e₁ : (Scheme.Modules.pullback Z.hom).obj L₁ ≅ SheafOfModules.unit Z.left.ringCatSheaf)
    (e₂ : (Scheme.Modules.pullback Z.hom).obj L₂ ≅ SheafOfModules.unit Z.left.ringCatSheaf) :
    Presieve.IsSheafFor (MOD.presheafHom L₁ L₂)
      (Sieve.pullback f (Sieve.generate (Presieve.ofArrows (fun _ : Unit => Over.mk q)
          (fun _ : Unit => Over.homMk q)))).arrows := by
  have hB := AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_unit_of_flat_of_surjective
    (pullback.snd q Z.hom)
  have hB' : Function.Bijective ((MOD.toDescentData (fun _ : Unit => pullback.snd q Z.hom)).map :
      ((Scheme.Modules.pullback Z.hom).obj L₁ ⟶ (Scheme.Modules.pullback Z.hom).obj L₂) → _) :=
    (bijective_map_iff_of_iso (C := Z.left.Modules)
      (MOD.toDescentData (fun _ : Unit => pullback.snd q Z.hom)) e₁ e₂).mpr hB
  have hB'' := (Pseudofunctor.bijective_toDescentData_map_iff (F := MOD)
    (fun _ : Unit => pullback.snd q Z.hom)
    ((Scheme.Modules.pullback Z.hom).obj L₁) ((Scheme.Modules.pullback Z.hom).obj L₂)).mp hB'
  have h2 := Presieve.isSheafFor_iso (MOD.overMapCompPresheafHomIso L₁ L₂ Z.hom).symm hB''
  rw [Presieve.isSheafFor_iff_generate,
    Presieve.isSheafFor_over_map_op_comp_iff Z.hom (MOD.presheafHom L₁ L₂) _
      (e := (Over.isoMk (Iso.refl Z.left)
        (by simp) : (Over.map Z.hom).obj (Over.mk (𝟙 Z.left)) ≅ Z)),
    pullback_sieve_eq q Z f] at h2
  exact h2

theorem isSeparatedFor_pullback_cover {ι : Type u} (W : ι → Y.Opens) (hW : ∀ y : Y, ∃ i, y ∈ W i)
    (Z : Over Y) (f : Z ⟶ Over.mk (𝟙 Y)) :
    Presieve.IsSeparatedFor (MOD.presheafHom L₁ L₂)
      (Sieve.pullback f (Sieve.generate (Presieve.ofArrows (fun i => Over.mk (W i).ι)
          (fun i => Over.homMk (W i).ι)))).arrows := by
  have hcov : ∀ x : Z.left, ∃ i, x ∈ Set.range ((Z.hom ⁻¹ᵁ (W i)).ι).base := by
    intro x
    obtain ⟨i, hi⟩ := hW (Z.hom.base x)
    exact ⟨i, by simpa using hi⟩
  have hZ := AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover
    (fun i => (Z.hom ⁻¹ᵁ (W i)).ι) hcov
    ((Scheme.Modules.pullback Z.hom).obj L₁) ((Scheme.Modules.pullback Z.hom).obj L₂)
  have hZ' := (Pseudofunctor.bijective_toDescentData_map_iff (F := MOD)
    (fun i => (Z.hom ⁻¹ᵁ (W i)).ι)
    ((Scheme.Modules.pullback Z.hom).obj L₁) ((Scheme.Modules.pullback Z.hom).obj L₂)).mp hZ
  have h2 := Presieve.isSheafFor_iso (MOD.overMapCompPresheafHomIso L₁ L₂ Z.hom).symm hZ'
  rw [Presieve.isSheafFor_iff_generate,
    Presieve.isSheafFor_over_map_op_comp_iff Z.hom (MOD.presheafHom L₁ L₂) _
      (e := (Over.isoMk (Iso.refl Z.left)
        (by simp) : (Over.map Z.hom).obj (Over.mk (𝟙 Z.left)) ≅ Z))] at h2
  refine isSeparatedFor_of_le ?_ h2.isSeparatedFor
  have hf : f.left = Z.hom := by simpa using Over.w f
  rintro W' k ⟨Z'', g, h, ⟨Y₃, m, f', ⟨i⟩, rfl⟩, fac⟩
  have hm : m.left ≫ (Z.hom ⁻¹ᵁ (W i)).ι = Z''.hom := Over.w m
  have hh : h.left ≫ (Z''.hom ≫ Z.hom) = W'.hom := Over.w h
  have hk : k.left = h.left ≫ m.left ≫ (Z.hom ⁻¹ᵁ (W i)).ι := by
    have := congr_arg CommaMorphism.left fac
    simpa using this
  have hkw : k.left ≫ Z.hom = W'.hom := Over.w k
  have key : (h.left ≫ m.left ≫ (Z.hom ∣_ (W i))) ≫ (W i).ι = k.left ≫ Z.hom := by
    rw [hk]
    simp only [Category.assoc]
    erw [morphismRestrict_ι]
    try rfl
  refine ⟨Over.mk (W i).ι, Over.homMk (h.left ≫ m.left ≫ (Z.hom ∣_ (W i))) (key.trans hkw),
    Over.homMk (W i).ι, ⟨i⟩, ?_⟩
  ext
  simp only [Over.comp_left, Over.homMk_left]
  erw [key, hf]
  try rfl

end AlgebraicGeometry.Scheme.Modules.HomDescFF

end
end AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleDescentFullyFaithful

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite CategoryTheory.Bicategory

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleDescentFullyFaithful in
open AlgebraicGeometry.Scheme.Modules.HomDescFF in
theorem toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (L₁ L₂ : Y.Modules) (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂)
      :
    Function.Bijective
      ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).map : (L₁ ⟶ L₂) → _) := by
  choose U₁ hU₁ e₁ using h₁.exists_trivialization
  choose U₂ hU₂ e₂ using h₂.exists_trivialization
  let W : Y → Y.Opens := fun y => U₁ y ⊓ U₂ y
  have hW : ∀ y : Y, ∃ i, y ∈ W i := fun y => ⟨y, hU₁ y, hU₂ y⟩
  have eW₁ : ∀ y, Nonempty ((Scheme.Modules.pullback (W y).ι).obj L₁ ≅
      SheafOfModules.unit (W y : Scheme.{u}).ringCatSheaf) := fun y =>
    ⟨trivOfFac (U₁ y).ι (W y).ι (Y.homOfLE inf_le_left) (Y.homOfLE_ι _) (e₁ y).some⟩
  have eW₂ : ∀ y, Nonempty ((Scheme.Modules.pullback (W y).ι).obj L₂ ≅
      SheafOfModules.unit (W y : Scheme.{u}).ringCatSheaf) := fun y =>
    ⟨trivOfFac (U₂ y).ι (W y).ι (Y.homOfLE inf_le_right) (Y.homOfLE_ι _) (e₂ y).some⟩
  apply (Pseudofunctor.bijective_toDescentData_map_iff (F := MOD)
    (fun _ : Unit => q) L₁ L₂).mpr
  rw [Presieve.isSheafFor_iff_generate]
  refine Presieve.isSheafFor_trans _
    (Sieve.generate (Presieve.ofArrows (fun y => Over.mk (W y).ι)
      (fun y => Over.homMk (U := Over.mk (W y).ι) (V := Over.mk (𝟙 Y)) (W y).ι))) _
    ?_ ?_ ?_
  · have hcov : ∀ y : Y, ∃ i, y ∈ Set.range ((W i).ι).base := fun y =>
      ⟨y, by simpa using (show y ∈ W y from ⟨hU₁ y, hU₂ y⟩)⟩
    have hZ := AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover
      (fun y => (W y).ι) hcov L₁ L₂
    exact (Presieve.isSheafFor_iff_generate _).mp
      ((Pseudofunctor.bijective_toDescentData_map_iff (F := MOD)
        (fun y => (W y).ι) L₁ L₂).mp hZ)
  · intro Z f _
    exact isSeparatedFor_pullback_cover L₁ L₂ W hW Z f
  · rintro Z f ⟨Y₃, a, f', ⟨y⟩, rfl⟩
    have ha : a.left ≫ (W y).ι = Z.hom := Over.w a
    exact isSheafFor_pullback_of_trivial q L₁ L₂ Z _
      (trivOfFac (W y).ι Z.hom a.left ha (eW₁ y).some)
      (trivOfFac (W y).ι Z.hom a.left ha (eW₂ y).some)
end AlgebraicGeometry.Scheme.Modules.IsInvertible
end ProofImplementation
