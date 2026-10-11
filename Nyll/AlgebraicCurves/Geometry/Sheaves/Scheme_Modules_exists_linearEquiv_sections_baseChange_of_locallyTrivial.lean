/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTildePullback
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.TensorProduct.Basic
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma

import Nyll.SchemeTheory.Modules.AffineSectionsBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.IsTensorProduct

/-!
# Extended sections of a locally trivial module

On an affine open and its affine base change, extending the section module gives
the sections of the pulled-back locally trivial module.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace AffineBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (A : Type u) [CommRing A] [Algebra R A]

/-- The family obtained by extending the base ring to A. -/
abbrev XA : Scheme.{u} := Limits.pullback c (specMap R A)

/-- The projection from the base changed family to the original family. -/
abbrev fst : XA c A ⟶ X := Limits.pullback.fst c (specMap R A)

/-- The structure morphism of the base changed family over Spec A. -/
abbrev snd : XA c A ⟶ Spec (.of A) := Limits.pullback.snd c (specMap R A)
variable (U : X.Opens) (hU : IsAffineOpen U)

theorem specMap_algebraMap_eq :
    letI := algebraOfHom c U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ c := by
  let := algebraOfHom c U
  have halg : (algebraMap R Γ(X, U)) = ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom :=
      rfl
  rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ←
      IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top (Spec (.of R))) hU (le_top : U ≤ c ⁻¹ᵁ
        ⊤)]

/-- Identify the inverse image of an affine open with the spectrum of its extended coordinate ring.
-/
def pullbackAffineOpenIsoSpecTensor :
    letI := algebraOfHom c U
    ((fst c A) ⁻¹ᵁ U).toScheme ≅ Spec (.of (Γ(X, U) ⊗[R] A)) :=
  letI := algebraOfHom c U
  (pullbackRestrictIsoRestrict (fst c A) U).symm
    ≪≫ pullbackSymmetry _ _
    ≪≫ pullbackRightPullbackFstIso c (specMap R A) U.ι
    ≪≫ asIso (pullback.map (U.ι ≫ c) (specMap R A)
        (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) (specMap R A)
        hU.isoSpec.hom (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, specMap_algebraMap_eq c U hU, ← hU.isoSpec_inv_ι_assoc,
            Iso.hom_inv_id_assoc])
        (by rw [Category.id_comp, Category.comp_id]))
    ≪≫ pullbackSpecIso R Γ(X, U) A

/-- The ring equivalence from the tensor product to sections on the inverse image of the affine
  open. -/
def sigma :
    letI := algebraOfHom c U
    (Γ(X, U) ⊗[R] A) ≃+* Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U
  ((Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[R] A))).symm
    ≪≫ Scheme.Γ.mapIso (pullbackAffineOpenIsoSpecTensor c A U hU).op
    ≪≫ ((fst c A) ⁻¹ᵁ U).topIso).commRingCatIsoToRingEquiv

theorem sigma_apply (x : letI := algebraOfHom c U; Γ(X, U) ⊗[R] A) :
    letI := algebraOfHom c U
    sigma c A U hU x = ((Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[R] A))).inv
      ≫ (pullbackAffineOpenIsoSpecTensor c A U hU).hom.appTop ≫ ((fst c A) ⁻¹ᵁ U).topIso.hom).hom x
          :=
  rfl

theorem iso_hom_comp_sndLeg :
    letI := algebraOfHom c U
    ((fst c A) ⁻¹ᵁ U).ι ≫ snd c A
      = (pullbackAffineOpenIsoSpecTensor c A U hU).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] Γ(X, U) ⊗[R] A))
            := by
  let := algebraOfHom c U
  rw [pullbackAffineOpenIsoSpecTensor, ← pullbackSpecIso_inv_snd R Γ(X, U) A]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc, pullbackRestrictIsoRestrict_inv_fst_assoc]

theorem iso_hom_comp_fstLeg :
    letI := algebraOfHom c U
    (pullbackAffineOpenIsoSpecTensor c A U hU).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X,
            U) ⊗[R] A))
      = ((fst c A) ∣_ U) ≫ hU.isoSpec.hom := by
  let := algebraOfHom c U
  rw [pullbackAffineOpenIsoSpecTensor, ← pullbackSpecIso_inv_fst R Γ(X, U) A]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc,
        pullbackSymmetry_hom_comp_fst_assoc]
  rfl

omit [CommRing R] in
theorem opens_ι_appTop_topIso_hom {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appTop ≫ V.topIso.hom = Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact (Y.presheaf.map_comp _ _).symm.trans (congrArg Y.presheaf.map (Subsingleton.elim _ _))

omit [CommRing R] in
theorem topIso_morphismRestrict_appTop_topIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) (W : Z.Opens) :
    W.topIso.inv ≫ (g ∣_ W).appTop ≫ (g ⁻¹ᵁ W).topIso.hom = g.app W := by
  rw [Scheme.Opens.topIso_inv, morphismRestrict_appTop, Scheme.Opens.topIso_hom]
  erw [Category.assoc, Scheme.Hom.naturality_assoc]
  erw [← Functor.map_comp, ← Functor.map_comp]
  exact (whisker_eq (g.app W)
    (congrArg Y.presheaf.map (Subsingleton.elim _ (𝟙 (op (g ⁻¹ᵁ W)))))).trans
      ((whisker_eq _ (Y.presheaf.map_id _)).trans (Category.comp_id _))

theorem sigma_tmul_one (s : Γ(X, U)) :
    letI := algebraOfHom c U
    sigma c A U hU (s ⊗ₜ[R] (1 : A)) = ((fst c A).app U).hom s := by
  let := algebraOfHom c U
  rw [sigma_apply]
  have hiL : s ⊗ₜ[R] (1 : A)
      = (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[R]
          A)).hom s := rfl
  rw [hiL, ← CommRingCat.comp_apply, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality,
      Category.assoc,
    ← Category.assoc _ _ (((fst c A) ⁻¹ᵁ U).topIso.hom), ← Scheme.Hom.comp_appTop,
    iso_hom_comp_fstLeg c A U hU, Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
  have hΓ : (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv ≫ (Scheme.ΓSpecIso Γ(X, U)).hom = 𝟙 _ :=
    Iso.inv_hom_id _
  simp only [← Category.assoc]
  rw [hΓ, Category.id_comp, Category.assoc, topIso_morphismRestrict_appTop_topIso]

theorem sigma_one_tmul (a : A) :
    letI := algebraOfHom c U
    sigma c A U hU ((1 : Γ(X, U)) ⊗ₜ[R] a)
      = ((XA c A).presheaf.map (homOfLE (le_top : (fst c A) ⁻¹ᵁ U ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd c A).appTop).hom a) := by
  let := algebraOfHom c U
  rw [sigma_apply]
  have hiR : (1 : Γ(X, U)) ⊗ₜ[R] a
      = (CommRingCat.ofHom (R := A) (S := Γ(X, U) ⊗[R] A)
          (Algebra.TensorProduct.includeRight : A →ₐ[R] Γ(X, U) ⊗[R] A)).hom a := rfl
  rw [hiR, ← CommRingCat.comp_apply, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality,
      Category.assoc,
    ← Category.assoc _ _ (((fst c A) ⁻¹ᵁ U).topIso.hom), ← Scheme.Hom.comp_appTop,
    ← iso_hom_comp_sndLeg c A U hU, Scheme.Hom.comp_appTop, Category.assoc,
    opens_ι_appTop_topIso_hom ((fst c A) ⁻¹ᵁ U)]
  rfl

theorem algebraMap_sndAlgebra (a : A) :
    (algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)).algebraMap a
      = ((XA c A).presheaf.map (homOfLE (le_top : (fst c A) ⁻¹ᵁ U ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd c A).appTop).hom a) := by
  rw [algebraMap_algebraOfHom]
  dsimp only [Scheme.Hom.appLE]
  rw [CommRingCat.comp_apply]
  rfl

/-- The algebra equivalence from scalar extension to sections on the base changed affine open. -/
def algEquiv :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    (A ⊗[R] Γ(X, U)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A Γ(X, U)).toRingEquiv.trans (sigma c A U
      hU))
    (fun a => by
      change sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) (algebraMap A (A ⊗[R] Γ(X, U))
          a)) = _
      rw [Algebra.TensorProduct.algebraMap_apply, show algebraMap A A a = a from rfl,
        Algebra.TensorProduct.comm_tmul, sigma_one_tmul, algebraMap_sndAlgebra])

theorem algEquiv_one_tmul (s : Γ(X, U)) :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    algEquiv c A U hU ((1 : A) ⊗ₜ[R] s) = ((fst c A).app U).hom s := by
  let := algebraOfHom c U; let := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  change sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) ((1 : A) ⊗ₜ[R] s)) = _
  rw [Algebra.TensorProduct.comm_tmul, sigma_tmul_one]

end AffineBaseChange
end AlgebraicGeometry.Scheme.TwoAffineOpenCover


open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj
          M)
      ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U)
    ∃ e : A ⊗[R] Γ(M, U) ≃ₗ[A]
        Γ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R
            A))).obj M,
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app U).hom m
              := by
  let p : Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A) ⟶ X :=
    Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)
  let V := p ⁻¹ᵁ U
  let B : Type u := Γ(X, U)
  let C : Type u := Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), V)
  let N : Type u := Γ(M, U)
  let P : Type u := Γ((Scheme.Modules.pullback p).obj M, V)
  let : Algebra R B := Scheme.TwoAffineOpenCover.algebraOfHom c U
  let : Algebra A C := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) V
  let : Algebra B C := (p.app U).hom.toAlgebra
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  let : Module R N := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
  let : Module A P := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
    ((Scheme.Modules.pullback p).obj M) V
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R B N := Scheme.TwoAffineOpenCover.isScalarTower_sections c M U
  have : IsScalarTower A C P := Scheme.TwoAffineOpenCover.isScalarTower_sections
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
    ((Scheme.Modules.pullback p).obj M) V
  let α : A ⊗[R] B ≃ₐ[A] C :=
    Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv c A U hU
  let δ : B →ₐ[R] C := (α.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
  have hδ (b : B) : δ b = algebraMap B C b :=
    Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv_one_tmul c A U hU b
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r =>
    (δ.commutes r).symm.trans (hδ (algebraMap R B r))
  have : Algebra.IsPushout R A B C :=
    ⟨IsBaseChange.of_equiv α.toLinearEquiv (fun b => by
      change α ((1 : A) ⊗ₜ[R] b) = (p.app U).hom b
      exact Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv_one_tmul c A U hU b)⟩
  have hV : IsAffineOpen V := by
    change IsAffine V.toScheme
    exact IsAffine.of_isIso
      (Scheme.TwoAffineOpenCover.AffineBaseChange.pullbackAffineOpenIsoSpecTensor c A U hU).hom
  obtain ⟨β, hβ⟩ := Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback
    p (show Scheme.Modules.IsInvertible M from ⟨htriv⟩) U hU hV
  refine ⟨(Algebra.IsPushout.cancelBaseChange R A B C N).symm.trans
    (β.restrictScalars A), ?_⟩
  intro m
  change β ((Algebra.IsPushout.cancelBaseChange R A B C N).symm ((1 : A) ⊗ₜ[R] m)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]
  exact hβ m

end
end Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
