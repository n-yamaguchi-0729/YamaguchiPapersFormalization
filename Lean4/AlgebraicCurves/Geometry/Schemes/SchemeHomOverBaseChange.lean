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

import Mathlib.AlgebraicGeometry.Pullbacks
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# Base change of morphisms over a scheme

Morphisms commuting with their structure maps induce morphisms of the base-changed schemes.
Their projections, identities, compositions, and induced module comparisons are compatible.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

variable {B C X Y Z : Scheme.{u}}

/-- Restrict a morphism over `B` after an arbitrary base change `C ⟶ B`. -/
def fibreRestrictAlong (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g c) (pullback.snd f c) :=
  ⟨pullback.lift (pullback.fst g c ≫ φ.1) (pullback.snd g c)
      (by rw [Category.assoc, φ.2, pullback.condition]),
    pullback.lift_snd _ _ _⟩
@[reassoc (attr := simp)]
theorem fibreRestrictAlong_coe_comp_fst (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f) :
    (fibreRestrictAlong c f g φ).1 ≫ pullback.fst f c = pullback.fst g c ≫ φ.1 :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem fibreRestrictAlong_coe_comp_snd (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f) :
    (fibreRestrictAlong c f g φ).1 ≫ pullback.snd f c = pullback.snd g c :=
  pullback.lift_snd _ _ _

theorem fibreRestrictAlong_coe_eq_pullbackMap (c : C ⟶ B) (f : X ⟶ B) (g : Y ⟶ B)
    (φ : SchemeHomOver g f)
    (eq₁ : g ≫ 𝟙 B = φ.1 ≫ f) (eq₂ : c ≫ 𝟙 B = 𝟙 C ≫ c) :
    (fibreRestrictAlong c f g φ).1 =
      pullback.map g c f c φ.1 (𝟙 C) (𝟙 B) eq₁ eq₂ := by
  apply pullback.hom_ext
  · simp [fibreRestrictAlong, pullback.map]
  · simp [fibreRestrictAlong, pullback.map]

theorem fibreRestrictAlong_schemeHomOverId (c : C ⟶ B) (f : X ⟶ B) :
    fibreRestrictAlong c f f (schemeHomOverId f) = schemeHomOverId (pullback.snd f c) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [fibreRestrictAlong, schemeHomOverId]
  · simp [fibreRestrictAlong, schemeHomOverId]

theorem fibreRestrictAlong_schemeHomOverComp (c : C ⟶ B) (f : X ⟶ B)
    (g : Y ⟶ B) (e : Z ⟶ B) (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    fibreRestrictAlong c f e (schemeHomOverComp ψ φ) =
      schemeHomOverComp (fibreRestrictAlong c g e ψ) (fibreRestrictAlong c f g φ) := by
  apply Subtype.ext
  apply pullback.hom_ext <;> simp only [fibreRestrictAlong, schemeHomOverComp,
    Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]

/-- The inclusion of the generic fibre induced by an algebra `R → K`. -/
def specGenericFibreInclusion : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))
@[simp]
theorem specGenericFibreInclusion_eq :
    specGenericFibreInclusion R K = Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
  rfl

variable {X Y Z : Scheme.{u}}

/-- Restrict a morphism over `Spec R` to the generic fibre over `K`. -/
def genericFibreRestrict (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)) :=
  ⟨pullback.lift (pullback.fst g (specGenericFibreInclusion R K) ≫ φ.1)
      (pullback.snd g (specGenericFibreInclusion R K))
      (by rw [Category.assoc, φ.2, pullback.condition]),
    pullback.lift_snd _ _ _⟩

theorem fibreRestrictAlong_specGenericFibreInclusion
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    fibreRestrictAlong (specGenericFibreInclusion R K) f g φ =
      genericFibreRestrict R K f g φ :=
  rfl
@[simp]
theorem genericFibreRestrict_coe_comp_snd (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) :
    (genericFibreRestrict R K f g φ).1 ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd g (specGenericFibreInclusion R K) :=
  (genericFibreRestrict R K f g φ).2
@[simp]
theorem genericFibreRestrict_coe_comp_fst (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver g f) :
    (genericFibreRestrict R K f g φ).1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      pullback.fst g (specGenericFibreInclusion R K) ≫ φ.1 :=
  pullback.lift_fst _ _ _

theorem genericFibreRestrict_schemeHomOverId (f : X ⟶ Spec (CommRingCat.of R)) :
    genericFibreRestrict R K f f (schemeHomOverId f) =
      schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K)) :=
  fibreRestrictAlong_schemeHomOverId (specGenericFibreInclusion R K) f

theorem genericFibreRestrict_schemeHomOverComp
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (e : Z ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver e g) (φ : SchemeHomOver g f) :
    genericFibreRestrict R K f e (schemeHomOverComp ψ φ) =
      schemeHomOverComp (genericFibreRestrict R K g e ψ)
        (genericFibreRestrict R K f g φ) :=
  fibreRestrictAlong_schemeHomOverComp (specGenericFibreInclusion R K) f g e ψ φ

end NeronModelInfra
