/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.ProperSplitClosedFiberSections
import SchemeTheory.Affine.FaithfullyFlatSectionSurjectivity
import SchemeTheory.Affine.SpecFlatBaseChangeSections
import SchemeTheory.Etale.ClosedFiberBaseChange
import SchemeTheory.Etale.LocalResidueFieldExtension
import SchemeTheory.FiniteEtale.Algebra.FiniteEtaleSplittingField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Restriction to an etale closed-fibre section algebra

For a proper scheme over a Noetherian local ring, an etale closed-fibre
section algebra implies surjectivity of the actual restriction map. A finite
separable splitting field is lifted to a concrete faithfully flat local
Noetherian extension. The actual cartesian closed-fibre comparison transports
the split section algebra, and faithfully flat descent returns the desired
restriction-surjectivity statement over the original local ring.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- Proper restriction to the closed fibre is surjective when that fibre's
actual section algebra is etale over the native residue field. -/
theorem surjective_closedFiber_appTop_of_isProper_of_etale
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    let qA : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
    let : Algebra (IsLocalRing.ResidueField A) Γ(pullback f qA, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField A))).inv ≫
        (pullback.snd f qA).appTop).hom.toAlgebra
    Algebra.Etale (IsLocalRing.ResidueField A) Γ(pullback f qA, ⊤) →
      Function.Surjective (pullback.fst f qA).appTop := by
  intro qA hOldAlgebra hEtale
  have hFinite : Module.Finite (IsLocalRing.ResidueField A) Γ(pullback f qA, ⊤) :=
    Algebra.FormallyUnramified.finite_of_free (IsLocalRing.ResidueField A)
      Γ(pullback f qA, ⊤)
  obtain ⟨L, hLField, hLAlgebra, hLFinite, hLSeparable, hSplitL⟩ :=
    Algebra.IsFiniteSplit.exists_finite_separable_splittingField
      (IsLocalRing.ResidueField A) Γ(pullback f qA, ⊤)
  obtain ⟨B, hBRing, hBAlgebra, hBLocal, hBNoetherian, hBFaithful, hBLocalMap,
      e, he, hMaximal⟩ :=
    Algebra.Etale.exists_faithfullyFlat_local_residueField_extension A L
  have hResidueMap : algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) =
      IsLocalRing.ResidueField.map (algebraMap A B) := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.map_residue]
  let : Algebra L (IsLocalRing.ResidueField B) := e.symm.toRingHom.toAlgebra
  have : IsScalarTower (IsLocalRing.ResidueField A) L (IsLocalRing.ResidueField B) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply e.injective
    change e (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) x) =
      e (e.symm (algebraMap (IsLocalRing.ResidueField A) L x))
    have hePoint : e (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) x) = algebraMap (IsLocalRing.ResidueField A) L x := by
      rw [hResidueMap]
      exact RingHom.congr_fun he x
    exact hePoint.trans (e.apply_symm_apply _).symm
  have hSplitResidue : Algebra.IsFiniteSplit (IsLocalRing.ResidueField B)
      ((IsLocalRing.ResidueField B) ⊗[IsLocalRing.ResidueField A] Γ(pullback f qA, ⊤)) :=
    Algebra.IsFiniteSplit.of_algEquiv
      (Algebra.TensorProduct.cancelBaseChange (IsLocalRing.ResidueField A) L
        (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B) Γ(pullback f qA, ⊤))
  let g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let qB : Spec (CommRingCat.of (IsLocalRing.ResidueField B)) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
  let fB : pullback f g ⟶ Spec (CommRingCat.of B) := pullback.snd f g
  let pA : pullback f qA ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField A)) :=
    pullback.snd f qA
  let r : Spec (CommRingCat.of (IsLocalRing.ResidueField B)) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField A)) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)))
  let hNewAlgebra : Algebra (IsLocalRing.ResidueField B) Γ(pullback fB qB, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField B))).inv ≫
      (pullback.snd fB qB).appTop).hom.toAlgebra
  let hTensorTarget : Algebra (IsLocalRing.ResidueField B) Γ(pullback pA r, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField B))).inv ≫
      (pullback.snd pA r).appTop).hom.toAlgebra
  have hSquare : IsPullback (closedFiberBaseChangeMap (B := B) f)
      (pullback.snd fB qB) pA r := by
    dsimp only [r]
    rw [hResidueMap]
    exact isPullback_closedFiberBaseChangeMap (B := B) f
  let ξ : pullback fB qB ≅ pullback pA r := hSquare.isoPullback
  let eSections : Γ(pullback pA r, ⊤) ≃ₐ[IsLocalRing.ResidueField B]
      Γ(pullback fB qB, ⊤) := {
    toRingEquiv := (Scheme.Γ.mapIso ξ.op).commRingCatIsoToRingEquiv
    commutes' := fun b => by
      change (((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField B))).inv ≫
        (pullback.snd pA r).appTop) ≫ ξ.hom.appTop) b =
        ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField B))).inv ≫
          (pullback.snd fB qB).appTop) b
      congr 2
      rw [Category.assoc, ← Scheme.Hom.comp_appTop, hSquare.isoPullback_hom_snd]
  }
  let eTensor : (IsLocalRing.ResidueField B) ⊗[IsLocalRing.ResidueField A]
      Γ(pullback f qA, ⊤) ≃ₐ[IsLocalRing.ResidueField B] Γ(pullback pA r, ⊤) :=
    specPullbackSectionsTensorEquiv (A := IsLocalRing.ResidueField B) pA
  have hNewSplit : Algebra.IsFiniteSplit (IsLocalRing.ResidueField B)
      Γ(pullback fB qB, ⊤) :=
    Algebra.IsFiniteSplit.of_algEquiv (eTensor.trans eSections)
  have hNewSurjective : Function.Surjective (pullback.fst fB qB).appTop :=
    surjective_closedFiber_appTop_of_isProper_of_isFiniteSplit fB hNewSplit
  have hFpqc : Flat g ∧ Surjective g :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A B))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hBFaithful)
  have hFlat : Flat g := hFpqc.1
  have hSurjective : Surjective g := hFpqc.2
  have hClosed : IsClosedImmersion qA :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (IsLocalRing.residue A))
      IsLocalRing.residue_surjective
  apply surjective_appTop_of_affine_faithfullyFlat_baseChange (pullback.fst f qA) f g
  let t : pullback (pullback.fst f qA ≫ f) g ⟶ pullback f g :=
    pullback.map (pullback.fst f qA ≫ f) g f g (pullback.fst f qA)
      (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  let eFiber : pullback fB qB ≅ pullback (pullback.fst f qA ≫ f) g :=
    closedFiberBaseChangeIso (B := B) f hMaximal
  have hIso : IsIso eFiber.hom.appTop := (Scheme.Γ.mapIso eFiber.op).isIso_hom
  have hInjective : Function.Injective eFiber.hom.appTop :=
    (ConcreteCategory.bijective_of_isIso eFiber.hom.appTop).injective
  have hFactor : eFiber.hom ≫ t = pullback.fst fB qB :=
    closedFiberBaseChangeIso_hom_baseChange (B := B) f hMaximal
  change Function.Surjective t.appTop
  intro x
  obtain ⟨a, ha⟩ := hNewSurjective (eFiber.hom.appTop x)
  refine ⟨a, hInjective ?_⟩
  change (t.appTop ≫ eFiber.hom.appTop) a = eFiber.hom.appTop x
  rw [← Scheme.Hom.comp_appTop, hFactor]
  exact ha

end AlgebraicGeometry
