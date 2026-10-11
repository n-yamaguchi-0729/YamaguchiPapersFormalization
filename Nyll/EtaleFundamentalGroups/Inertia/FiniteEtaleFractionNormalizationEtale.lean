/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.DVRGeometricInertiaEtale
import Nyll.EtaleFundamentalGroups.Inertia.FractionFieldSpecNormalization
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Extending a Galois cover of a DVR fraction field

The normalization of the actual finite-etale cover is étale when all its
closed geometric-point deck stabilizers are trivial. Its function field,
scalar tower, Galois extension, and normalization comparison are constructed
from the cover and its canonical structure morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- A Galois finite-etale fraction-field cover with trivial normalized
geometric-point stabilizers extends by its actual normalization over the DVR. -/
theorem etale_fractionCover_normalization_of_geometricInertia_trivial
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (Y : FiniteEtale (Spec (.of K))) (hY : IsGalois Y)
    (hfix : ∀ (z : Spec (.of (AlgebraicClosure (IsLocalRing.ResidueField R))) ⟶
        ((show Y.left ⟶ Spec (.of K) from Y.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K))).normalization),
      z ≫ ((show Y.left ⟶ Spec (.of K) from Y.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K))).fromNormalization =
          Spec.map (CommRingCat.ofHom
            ((algebraMap (IsLocalRing.ResidueField R)
              (AlgebraicClosure (IsLocalRing.ResidueField R))).comp
                (IsLocalRing.residue R))) →
      ∀ τ : Aut Y,
        z ≫ normalizationEndomorphism
          ((show Y.left ⟶ Spec (.of K) from Y.hom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K))) τ.hom.left
          (by
            have hw : τ.hom.left ≫ (show Y.left ⟶ Spec (.of K) from Y.hom) =
                (show Y.left ⟶ Spec (.of K) from Y.hom) := τ.hom.w
            exact (Category.assoc _ _ _).symm.trans
              (congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) hw)) = z →
          τ = 1) :
    Etale (((show Y.left ⟶ Spec (.of K) from Y.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))).fromNormalization) := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  let : IsNormalIntegral Y.left := isNormalIntegral_left_of_isConnected_finiteEtale Y
  let : IsAffine Y.left := isAffine_of_isAffineHom (show Y.left ⟶ Spec (.of K) from Y.hom)
  let g : Spec (.of K) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f : Y.left ⟶ Spec (.of R) := (show Y.left ⟶ Spec (.of K) from Y.hom) ≫ g
  let F := (Spec (.of K)).functionField
  let L := Y.left.functionField
  let : Algebra F L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra R F := affineMorphismFunctionFieldAlgebra R g
  let : Algebra R L := affineMorphismFunctionFieldAlgebra R f
  let : IsScalarTower R F L := finiteEtaleMorphism_functionField_isScalarTower R g Y
  have : IsFractionRing R F := affineMorphismFunctionFieldAlgebra_isFractionRing R K
  have : FiniteDimensional F L := finiteDimensional_functionField_of_finiteEtale_isConnected Y
  have : _root_.IsGalois F L := isGalois_functionField_of_isGalois_finiteEtale Y hY
  let e := affineMorphismFunctionFieldNormalizationIso R f
  let eGal := finiteEtaleAutOpFunctionFieldMulEquiv Y hY
  have hEtale : Algebra.Etale R (integralClosure R L) := by
    apply integralClosure_etale_of_dvr_of_geometricInertia_trivial R F L
    intro z hz σ hσ
    let ζ := z ≫ (specNormalizationIso R L).hom ≫ e.inv
    have hζ : ζ ≫ f.fromNormalization =
        Spec.map (CommRingCat.ofHom
          ((algebraMap (IsLocalRing.ResidueField R)
            (AlgebraicClosure (IsLocalRing.ResidueField R))).comp (IsLocalRing.residue R))) := by
      rw [← affineMorphismFunctionFieldNormalizationIso_hom_base R f]
      simp only [ζ, e, Category.assoc, Iso.inv_hom_id_assoc]
      exact (congrArg (fun k => z ≫ k) (specNormalizationIso_hom_base R L)).trans hz
    obtain ⟨τ, hτ⟩ := eGal.surjective σ
    have hτσ : finiteEtaleAutFunctionFieldAlgEquiv Y τ.unop = σ :=
      (finiteEtaleAutOpFunctionFieldMulEquiv_apply Y hY τ).symm.trans hτ
    have hτf : τ.unop.hom.left ≫ f = f := by
      have hw : τ.unop.hom.left ≫ (show Y.left ⟶ Spec (.of K) from Y.hom) =
          (show Y.left ⟶ Spec (.of K) from Y.hom) := τ.unop.hom.w
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ g) hw)
    have hτfix : ζ ≫ normalizationEndomorphism f τ.unop.hom.left hτf = ζ := by
      apply (affineMorphismFunctionFieldNormalizationIso_fixes_iff R f
        (show Y.left ≅ Y.left from
          (FiniteEtale.forget (Spec (.of K)) ⋙ Over.forget (Spec (.of K))).mapIso τ.unop)
        hτf ζ).mp
      rw [finiteEtaleMorphismFunctionFieldAlgEquiv_eq R g Y τ.unop, hτσ]
      have h := congrArg (fun k => k ≫ (specNormalizationIso R L).hom) hσ
      rw [Category.assoc, affineNormalizationDeck_specNormalizationIso_hom,
        ← Category.assoc] at h
      simpa only [ζ, e, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
    have hτone : τ.unop = 1 := hfix ζ hζ τ.unop hτfix
    calc
      σ = eGal τ := hτ.symm
      _ = eGal 1 := congrArg eGal (MulOpposite.unop_injective hτone)
      _ = 1 := map_one eGal
  have hSpec : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      ((RingHom.etale_algebraMap (R := R) (S := integralClosure R L)).mpr hEtale)
  change Etale f.fromNormalization
  rw [← affineMorphismFunctionFieldNormalizationIso_hom_base R f]
  infer_instance

end EtaleFundamentalGroups.Inertia
