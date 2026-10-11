/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperLocalSectionsBaseChange
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperGeometricallyReducedSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
import Nyll.SchemeTheory.FiniteEtale.Algebra.LocalEtaleFromClosedFiber
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale

/-!
# The section algebra of a proper geometrically reduced local family

The actual section-module comparison respects multiplication on pure tensors.
It therefore gives an algebra equivalence with the actual section ring of
every base change. The original section algebra is finite projective and
étale, by the actual closed-fibre algebra and the local criterion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

open Scheme.TwoAffineOpenCover
open Scheme.Modules

/-- A proper flat family over a Noetherian local ring has finite projective
global sections and arbitrary algebra base change when its actual closed-fibre
section algebra is étale. -/
theorem finite_projective_sectionAlgebra_and_baseChange_of_etale_closedFiber
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f]
    (hEtaleFiber : (pullback.snd f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop.hom.Etale) :
    let : Algebra R Γ(X, ⊤) := algebraOfHom f ⊤
    (Module.Finite R Γ(X, ⊤) ∧ Module.Projective R Γ(X, ⊤)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        let : Algebra A Γ(pullback f (specMap R A), ⊤) :=
          algebraOfHom (pullback.snd f (specMap R A)) ⊤
        ∃ e : A ⊗[R] Γ(X, ⊤) ≃ₐ[A] Γ(pullback f (specMap R A), ⊤),
          ∀ (a : A) (s : Γ(X, ⊤)), e (a ⊗ₜ[R] s) =
            algebraMap A Γ(pullback f (specMap R A), ⊤) a *
              (pullback.fst f (specMap R A)).appTop s := by
  intro hRΓ
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let hRM : Module R Γ(M, ⊤) := moduleSectionsOfHom f M ⊤
  obtain ⟨hfinite, hbase⟩ :=
    finite_projective_sections_and_baseChange_of_proper_flat_of_etale_closedFiber f hEtaleFiber
  let eR : Γ(M, ⊤) ≃ₗ[R] Γ(X, ⊤) := LinearEquiv.refl R Γ(X, ⊤)
  have hfin : Module.Finite R Γ(M, ⊤) := hfinite.1
  have hproj : Module.Projective R Γ(M, ⊤) := hfinite.2
  refine ⟨⟨Module.Finite.equiv eR, Module.Projective.of_equiv eR⟩, ?_⟩
  intro A _ _ hAΓ
  let p := pullback.fst f (specMap R A)
  let fA := pullback.snd f (specMap R A)
  let MA := (Scheme.Modules.pullback p).obj M
  let hAM : Module A Γ(MA, ⊤) := moduleSectionsOfHom fA MA ⊤
  obtain ⟨e, he⟩ := hbase A
  let u := Scheme.Modules.pullbackUnitIso p
  let v : Γ(MA, ⊤) ≃ₗ[A] Γ(pullback f (specMap R A), ⊤) :=
    { toFun := u.hom.app ⊤
      invFun := u.inv.app ⊤
      left_inv := fun s =>
        congrArg (fun k : MA ⟶ MA => k.val.app (Opposite.op ⊤) s) u.hom_inv_id
      right_inv := fun s =>
        congrArg (fun k : SheafOfModules.unit (pullback f (specMap R A)).ringCatSheaf ⟶
            SheafOfModules.unit (pullback f (specMap R A)).ringCatSheaf =>
          k.val.app (Opposite.op ⊤) s) u.inv_hom_id
      map_add' := fun s t => map_add (u.hom.app ⊤).hom s t
      map_smul' := fun a s =>
        Scheme.Modules.Hom.app_smul u.hom
          (algebraMap A Γ(pullback f (specMap R A), ⊤) a) s }
  let β : A ⊗[R] Γ(X, ⊤) ≃ₗ[A] Γ(pullback f (specMap R A), ⊤) :=
    (eR.symm.baseChange R A _ _).trans (e.trans v)
  have hβ (a : A) (s : Γ(X, ⊤)) : β (a ⊗ₜ[R] s) =
      algebraMap A Γ(pullback f (specMap R A), ⊤) a * p.appTop s := by
    change v (e ((eR.symm.baseChange R A _ _) (a ⊗ₜ[R] s))) = _
    rw [LinearEquiv.baseChange_tmul]
    change v (e (a ⊗ₜ[R] s)) = _
    have hs := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
      p ⊤ s
    exact (congrArg v (he a s)).trans ((v.map_smul a _).trans
      (congrArg (fun z : Γ(pullback f (specMap R A), ⊤) => a • z) hs))
  have hOne : β 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, hβ, map_one, map_one, one_mul]
  have hMul (x y : A ⊗[R] Γ(X, ⊤)) : β (x * y) = β x * β y := by
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
    | tmul a s =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
      | tmul b t =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hβ, hβ, hβ, map_mul, map_mul]
        ring
  exact ⟨AlgEquiv.ofLinearEquiv β hOne hMul, hβ⟩

/-- Arbitrary base change for the actual section algebra of a proper flat
geometrically reduced family over a Noetherian local ring. The coefficient
algebras are the original maps from the affine bases. -/
theorem finite_projective_sectionAlgebra_and_baseChange_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [GeometricallyReduced f] :
    let : Algebra R Γ(X, ⊤) := algebraOfHom f ⊤
    (Module.Finite R Γ(X, ⊤) ∧ Module.Projective R Γ(X, ⊤)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        let : Algebra A Γ(pullback f (specMap R A), ⊤) :=
          algebraOfHom (pullback.snd f (specMap R A)) ⊤
        ∃ e : A ⊗[R] Γ(X, ⊤) ≃ₐ[A] Γ(pullback f (specMap R A), ⊤),
          ∀ (a : A) (s : Γ(X, ⊤)), e (a ⊗ₜ[R] s) =
            algebraMap A Γ(pullback f (specMap R A), ⊤) a *
              (pullback.fst f (specMap R A)).appTop s := by
  exact finite_projective_sectionAlgebra_and_baseChange_of_etale_closedFiber f
    (finite_etale_appTop_of_isProper_of_geometricallyReduced_overField
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).2

/-- Étaleness of the closed-fibre section algebra implies étaleness of the
actual global-section algebra of a proper flat Noetherian local family. -/
theorem finite_etale_sectionAlgebra_of_proper_flat_of_etale_closedFiber
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f]
    (hEtaleFiber : (pullback.snd f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop.hom.Etale) :
    let : Algebra R Γ(X, ⊤) := algebraOfHom f ⊤
    Module.Finite R Γ(X, ⊤) ∧ Algebra.Etale R Γ(X, ⊤) := by
  intro hRΓ
  obtain ⟨hfinite, hbase⟩ :=
    finite_projective_sectionAlgebra_and_baseChange_of_etale_closedFiber f hEtaleFiber
  have hfin : Module.Finite R Γ(X, ⊤) := hfinite.1
  have hproj : Module.Projective R Γ(X, ⊤) := hfinite.2
  let k := IsLocalRing.ResidueField R
  let fₖ := pullback.snd f (specMap R k)
  let hₖΓ : Algebra k Γ(pullback f (specMap R k), ⊤) := algebraOfHom fₖ ⊤
  obtain ⟨e, _⟩ := hbase k
  have hEtale : Algebra.Etale k Γ(pullback f (specMap R k), ⊤) := by
    apply RingHom.etale_algebraMap.mp
    change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      fₖ.appLE ⊤ ⊤ le_top).hom).Etale
    have hApp : fₖ.appTop = fₖ.appLE ⊤ ⊤ le_top := fₖ.app_eq_appLE
    rw [← hApp]
    exact (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv fₖ.appTop).mpr hEtaleFiber
  have hTensorEtale : Algebra.Etale k (k ⊗[R] Γ(X, ⊤)) := Algebra.Etale.of_equiv e.symm
  exact ⟨hfin, Algebra.etale_of_finite_projective_of_etale_closedFiber R Γ(X, ⊤)⟩

/-- The actual section algebra of a proper flat geometrically reduced family
over a Noetherian local ring is finite étale. The closed-fibre comparison is
constructed from sections, rather than assumed. -/
theorem finite_etale_sectionAlgebra_of_proper_flat_geometricallyReduced_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [GeometricallyReduced f] :
    let : Algebra R Γ(X, ⊤) := algebraOfHom f ⊤
    Module.Finite R Γ(X, ⊤) ∧ Algebra.Etale R Γ(X, ⊤) := by
  exact finite_etale_sectionAlgebra_of_proper_flat_of_etale_closedFiber f
    (finite_etale_appTop_of_isProper_of_geometricallyReduced_overField
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).2

end AlgebraicGeometry
