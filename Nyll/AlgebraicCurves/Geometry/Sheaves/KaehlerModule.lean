/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_KaehlerModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.SectionsAlgebra
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Nyll.AlgebraicCurves.Foundations.Algebra.PresheafOfModules_ExteriorPower
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet

/-!
# Kaehler Module
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- The presheaf of relative Kaehler differentials for f. -/
def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf

local instance kaehlerPresheafModule (U : X.Opens) :
    Module Γ(X, U) (f.kaehlerPresheaf.obj (op U)) :=
  (f.kaehlerPresheaf.obj (op U)).isModule

/-- The module sheaf obtained by sheafifying the relative differential presheaf. -/
def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.kaehlerPresheaf

/-- The specified determinant degree of the relative differential module sheaf. -/
def topDifferentials (d : ℕ) : X.Modules :=
  Scheme.Modules.det d f.kaehler

/-- The specified exterior degree of the relative differential presheaf. -/
abbrev topPresheaf (d : ℕ) : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj f.kaehlerPresheaf

@[simp] lemma kaehlerPresheaf_obj (U : (X.Opens)ᵒᵖ) :
    f.kaehlerPresheaf.obj U = CommRingCat.KaehlerDifferential (f.constToPresheaf.app U) := rfl

/-- The map from presheaf differentials to sections of the sheafified differential module. -/
def kaehlerToSections (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U) : Type u) → (Γ(f.kaehler, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom s

/-- The linear sheafification map on the differential module over the selected open. -/
def kaehlerToSectionsₗ (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U)) →ₗ[Γ(X, U)] (Γ(f.kaehler, U) : Type u) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom

/-- The map from exterior presheaf differentials to sections of the corresponding determinant
sheaf. -/
def topToSections (d : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U)) : Type u) → (Γ(f.topDifferentials d, U) : Type u)
      :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
    (exteriorPower.map d (f.kaehlerToSectionsₗ U) s)

theorem kaehlerToSections_add (U : X.Opens) (s t : f.kaehlerPresheaf.obj (op U)) :
    f.kaehlerToSections U (s + t) = f.kaehlerToSections U s + f.kaehlerToSections U t :=
  map_add (f.kaehlerToSectionsₗ U) s t

theorem kaehlerPresheaf_nontrivial_polynomial (A : Type u) [CommRing A] [Nontrivial A] :
    letI f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    Nontrivial (f.kaehlerPresheaf.obj (op ⊤)) := by
  set f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A))) with hf
  let Γ' : Type u := Γ(Spec (CommRingCat.of (Polynomial A)), ⊤)
  let algA : Algebra A Γ' := f.sectionsAlgebra ⊤
  let e : Γ' ≃+* Polynomial A := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial
    A))).commRingCatIsoToRingEquiv
  let : Algebra Γ' (Polynomial A) := e.toRingHom.toAlgebra
  have hcomp : (algebraMap Γ' (Polynomial A)).comp (algebraMap A Γ') = algebraMap A (Polynomial A)
    := by
    refine RingHom.ext fun a => ?_
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).hom.hom
      ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = algebraMap A
        (Polynomial A) a
    have h1 : f.appLE ⊤ ⊤ le_top = f.appTop := by
      unfold Scheme.Hom.appLE
      have ht : (show op (⊤ : (Spec (CommRingCat.of (Polynomial A))).Opens) ⟶ op ⊤ from
          (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of (Polynomial A))).Opens) ≤ f ⁻¹ᵁ ⊤)).op) =
          𝟙 (op ⊤) := Subsingleton.elim _ _
      have hm : (Spec (CommRingCat.of (Polynomial A))).presheaf.map
          (show op (⊤ : (Spec (CommRingCat.of (Polynomial A))).Opens) ⟶ op ⊤ from
            (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of (Polynomial A))).Opens) ≤ f ⁻¹ᵁ ⊤)).op) =
          𝟙 Γ(Spec (CommRingCat.of (Polynomial A)), ⊤) :=
        (congrArg (fun i : op (⊤ : (Spec (CommRingCat.of (Polynomial A))).Opens) ⟶ op ⊤ =>
          (Spec (CommRingCat.of (Polynomial A))).presheaf.map i) ht).trans
          (CategoryTheory.Functor.map_id _ _)
      exact (congrArg (fun k : Γ(Spec (CommRingCat.of (Polynomial A)), ⊤) ⟶
          Γ(Spec (CommRingCat.of (Polynomial A)), ⊤) => f.appTop ≫ k) hm).trans
        (Category.comp_id f.appTop)
    rw [h1]
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    rw [← hf] at h2
    have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    rw [h3]
    change algebraMap A (Polynomial A) (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom a) = _
    rw [Iso.inv_hom_id]; rfl
  have : IsScalarTower A Γ' (Polynomial A) := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hsurj : Function.Surjective (KaehlerDifferential.map A A Γ' (Polynomial A)) :=
    KaehlerDifferential.map_surjective_of_surjective A A (h := e.surjective)
  have : Nontrivial (Ω[Polynomial A⁄A]) :=
    (KaehlerDifferential.polynomialEquiv A).toEquiv.nontrivial
  exact hsurj.nontrivial

end AlgebraicGeometry.Scheme.Hom

end
