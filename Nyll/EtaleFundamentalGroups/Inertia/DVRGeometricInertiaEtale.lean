/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.IntegralClosureGaloisAction
import Nyll.EtaleFundamentalGroups.Inertia.TrivialNormalizationInertiaEtale
import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteResidueGeometricPoint

/-!
# Fixed geometric-point inertia implies étaleness over a DVR

Every prime over the closed point is represented in the fixed algebraic
closure of the base residue field. The actual affine normalization comparison
then turns geometric fixed-point triviality into the ideal inertia condition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The actual affine normalization isomorphism commutes with its base map. -/
@[reassoc]
theorem specNormalizationIso_hom_base
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    (specNormalizationIso R B).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R B))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization := by
  apply spec_toNormalization_hom_ext R B
  rw [← Category.assoc, toNormalization_specNormalizationIso_hom,
    Scheme.Hom.toNormalization_fromNormalization, ← Spec.map_comp]
  rfl

/-- Triviality at all actual normalized geometric points over the fixed
algebraic closure of the closed residue field makes the normalization étale. -/
theorem integralClosure_etale_of_dvr_of_geometricInertia_trivial
    (R K L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hfix : ∀ (z : Spec (.of (AlgebraicClosure (IsLocalRing.ResidueField R))) ⟶
        (Spec.map (CommRingCat.ofHom (algebraMap R L))).normalization),
      z ≫ (Spec.map (CommRingCat.ofHom (algebraMap R L))).fromNormalization =
          Spec.map (CommRingCat.ofHom
            ((algebraMap (IsLocalRing.ResidueField R)
              (AlgebraicClosure (IsLocalRing.ResidueField R))).comp
                (IsLocalRing.residue R))) →
      ∀ σ : Gal(L/K),
        z ≫ affineNormalizationDeck R L (σ.restrictScalars R) = z → σ = 1) :
    Algebra.Etale R (integralClosure R L) := by
  let S := integralClosure R L
  let : Module.Finite R S := IsIntegralClosure.finite R K L S
  apply integralClosure_etale_of_dvr_of_inertia_eq_bot R K L
  let : MulSemiringAction Gal(L/K) S := IsIntegralClosure.MulSemiringAction R K L S
  intro Q hQ hOver
  have : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q
    (IsLocalRing.maximalIdeal R)
  obtain ⟨φ, hker, hbase⟩ := SchemeTheory.exists_finite_residue_geometricPoint R S Q
  let z := Spec.map (CommRingCat.ofHom φ) ≫ (specNormalizationIso R L).inv
  have hz : z ≫ (Spec.map (CommRingCat.ofHom (algebraMap R L))).fromNormalization =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (IsLocalRing.ResidueField R)
          (AlgebraicClosure (IsLocalRing.ResidueField R))).comp
            (IsLocalRing.residue R))) := by
    dsimp only [z]
    rw [← specNormalizationIso_hom_base R L, Category.assoc,
      Iso.inv_hom_id_assoc, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hbase
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro σ hσ
  apply hfix z hz σ
  apply (mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint
    R L φ (σ.restrictScalars R)).mp
  let : MulSemiringAction (L ≃ₐ[R] L) S := integralClosureAutAction R L
  apply Ideal.mem_inertia.mpr
  intro b
  have hsmul : σ • b = (σ.restrictScalars R) • b := by
    change (galRestrict R K L S σ) b =
      (((integralClosureAutHom R L).comp (AlgEquiv.restrictScalarsHom R)) σ) b
    exact congrArg (fun f : Gal(L/K) →* (S ≃ₐ[R] S) => f σ b)
      (galRestrict_integralClosure_eq R K L)
  rw [← hsmul, hker]
  exact Ideal.mem_inertia.mp hσ b

end EtaleFundamentalGroups.Inertia
