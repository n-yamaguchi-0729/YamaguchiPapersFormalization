/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ClosedFiberEtaleDescent
import Nyll.EtaleFundamentalGroups.FiniteEtale.NoetherianLocalProperModel
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperLocalSectionAlgebra
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite étale sections over an arbitrary local base

A proper flat finitely presented family has an actual Noetherian local model.
Its closed-fibre section algebra is étale by descent along the residue-field
extension, without assuming that the model has geometrically reduced fibres.
The resulting arbitrary base-change comparison transports its finite étale
section algebra to the original family.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

open Scheme.TwoAffineOpenCover

/-- The actual section algebra of a proper flat finitely presented family
with geometrically reduced fibres over any local ring is finite projective
and étale. The Noetherian model and its closed-fibre comparison are constructed
from the original family. -/
theorem finite_projective_etale_sectionAlgebra_and_baseChange_local
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    let : Algebra R Γ(X, ⊤) := algebraOfHom f ⊤
    (Module.Finite R Γ(X, ⊤) ∧ Module.Projective R Γ(X, ⊤) ∧
      Algebra.Etale R Γ(X, ⊤)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        let : Algebra A Γ(pullback f (specMap R A), ⊤) :=
          algebraOfHom (pullback.snd f (specMap R A)) ⊤
        Nonempty (A ⊗[R] Γ(X, ⊤) ≃ₐ[A] Γ(pullback f (specMap R A), ⊤)) := by
  intro hRΓ
  obtain ⟨S, hSRing, hSNoetherian, hSLocal, hSR, hLocalMap,
      Y, g, p, hProper, hFlat, hModel⟩ := exists_noetherian_local_proper_flat_model f
  let qS := Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))
  have hEtaleFiber : (pullback.snd g qS).appTop.hom.Etale := by
    exact (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).inv
        (pullback.snd g qS).appTop).mp
      (etale_closedFiber_sections_of_isPullback_of_geometricallyReduced g f p hModel)
  let hSΓ : Algebra S Γ(Y, ⊤) := algebraOfHom g ⊤
  obtain ⟨hFinite, hBase⟩ :=
    finite_projective_sectionAlgebra_and_baseChange_of_etale_closedFiber g hEtaleFiber
  have hFiniteS : Module.Finite S Γ(Y, ⊤) := hFinite.1
  have hProjectiveS : Module.Projective S Γ(Y, ⊤) := hFinite.2
  have hEtaleS : Algebra.Etale S Γ(Y, ⊤) :=
    (finite_etale_sectionAlgebra_of_proper_flat_of_etale_closedFiber g hEtaleFiber).2
  let b := specMap S R
  let gR := pullback.snd g b
  let hRΓModel : Algebra R Γ(pullback g b, ⊤) := algebraOfHom gR ⊤
  obtain ⟨eBase, _⟩ := hBase R
  let eX : X ≅ pullback g b := hModel.isoPullback
  let eSections : Γ(pullback g b, ⊤) ≃ₐ[R] Γ(X, ⊤) := {
    toRingEquiv := (Scheme.Γ.mapIso eX.op).commRingCatIsoToRingEquiv
    commutes' := fun r => by
      change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        gR.appLE ⊤ ⊤ le_top) ≫ eX.hom.appTop) r =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ ⊤ le_top) r
      have hgTop : gR.appTop = gR.appLE ⊤ ⊤ le_top := gR.app_eq_appLE
      have hfTop : f.appTop = f.appLE ⊤ ⊤ le_top := f.app_eq_appLE
      rw [← hgTop, ← hfTop]
      congr 2
      rw [Category.assoc, ← Scheme.Hom.comp_appTop]
      exact congrArg ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ·)
        (congrArg Scheme.Hom.appTop hModel.isoPullback_hom_snd)
  }
  let e : R ⊗[S] Γ(Y, ⊤) ≃ₐ[R] Γ(X, ⊤) := eBase.trans eSections
  refine ⟨⟨Module.Finite.equiv e.toLinearEquiv,
    Module.Projective.of_equiv e.toLinearEquiv, Algebra.Etale.of_equiv e⟩, ?_⟩
  intro A _ _ hAΓ
  let : Algebra S A := ((algebraMap R A).comp (algebraMap S R)).toAlgebra
  have : IsScalarTower S R A := IsScalarTower.of_algebraMap_eq' rfl
  let a := specMap R A
  let bA := specMap S A
  let fA := pullback.snd f a
  let gA := pullback.snd g bA
  let hAΓModel : Algebra A Γ(pullback g bA, ⊤) := algebraOfHom gA ⊤
  obtain ⟨eBaseA, _⟩ := hBase A
  have hBaseMaps : a ≫ b = bA := by
    dsimp only [a, b, bA, specMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hModelA : IsPullback (pullback.fst f a ≫ p) fA g bA := by
    rw [← hBaseMaps]
    exact (IsPullback.of_hasPullback f a).paste_horiz hModel
  let eXA : pullback f a ≅ pullback g bA := hModelA.isoPullback
  let eSectionsA : Γ(pullback g bA, ⊤) ≃ₐ[A] Γ(pullback f a, ⊤) := {
    toRingEquiv := (Scheme.Γ.mapIso eXA.op).commRingCatIsoToRingEquiv
    commutes' := fun t => by
      change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        gA.appLE ⊤ ⊤ le_top) ≫ eXA.hom.appTop) t =
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ fA.appLE ⊤ ⊤ le_top) t
      have hgTop : gA.appTop = gA.appLE ⊤ ⊤ le_top := gA.app_eq_appLE
      have hfTop : fA.appTop = fA.appLE ⊤ ⊤ le_top := fA.app_eq_appLE
      rw [← hgTop, ← hfTop]
      congr 2
      rw [Category.assoc, ← Scheme.Hom.comp_appTop]
      exact congrArg ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ·)
        (congrArg Scheme.Hom.appTop hModelA.isoPullback_hom_snd)
  }
  let eTensor : A ⊗[R] Γ(X, ⊤) ≃ₐ[A] A ⊗[R] (R ⊗[S] Γ(Y, ⊤)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) e.symm
  exact ⟨eTensor.trans ((Algebra.TensorProduct.cancelBaseChange S R A A Γ(Y, ⊤)).trans
    (eBaseA.trans eSectionsA))⟩

/-- Proper flat finitely presented geometrically reduced families over an
arbitrary local ring have finite projective étale section algebras. -/
theorem finite_projective_etale_sectionAlgebra_of_proper_flat_geometricallyReduced_local
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    let : Algebra R Γ(X, ⊤) := algebraOfHom f ⊤
    Module.Finite R Γ(X, ⊤) ∧ Module.Projective R Γ(X, ⊤) ∧
      Algebra.Etale R Γ(X, ⊤) :=
  (finite_projective_etale_sectionAlgebra_and_baseChange_local f).1

end AlgebraicGeometry
