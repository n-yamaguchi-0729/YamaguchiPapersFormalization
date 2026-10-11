/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Descent.FiniteNormalizationSpreading
import SchemeTheory.Normalization.AffineFiniteEtale
import EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite normalization over a principal affine chart

The finite source over the principal localization is replaced by its actual
affine spectrum. The structure map supplies the algebra structures, and
the canonical source-normalization isomorphism preserves every base change.
The ring-level spreading theorem therefore applies to the original scheme
normalization, without a global normality assumption on the affine base.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- For a finite morphism over a principal localization, finite etaleness of
the actual normalization over every base local ring spreads globally when
the base is normal along the principal boundary. -/
theorem finiteEtale_normalization_of_principal_factorization
    (R : Type u) [CommRing R] [IsNoetherianRing R] (d : R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away d A]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsFinite g]
    (hnormal : ∀ (p : Ideal R) [p.IsPrime], d ∈ p →
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hlocal : ∀ p : PrimeSpectrum R,
      IsFiniteEtale (pullback.snd
        (g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))).fromNormalization
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)))))) :
    IsFiniteEtale
      (g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))).fromNormalization := by
  let : IsAffine Y := isAffine_of_isAffineHom g
  let B := Γ(Y, ⊤)
  let e : Y ≅ Spec B := Y.isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ g)
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have hgSpec : IsFinite (Spec.map φ) := hφ.symm ▸ (inferInstance : IsFinite (e.inv ≫ g))
  let : Module.Finite A B := (IsFinite.SpecMap_iff φ).mp hgSpec
  let f := g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
  let fB := affineStructureMap R B
  have hfB : fB = Spec.map φ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← Spec.map_comp]
    rfl
  have hfg : e.hom ≫ fB = f := by
    rw [hfB, hφ, ← Category.assoc, e.hom_inv_id_assoc]
  let en := Inertia.normalizationSourceIso f fB e hfg
  have hen : en.hom ≫ fB.fromNormalization = f.fromNormalization :=
    Inertia.normalizationSourceIso_hom_fromNormalization f fB e hfg
  have hBlocal (p : PrimeSpectrum R) :
      Module.Finite (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R B) ∧
        Algebra.Etale (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R B) := by
    let b := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)))
    let l := pullback.map f.fromNormalization b fB.fromNormalization b
      en.hom (𝟙 _) (𝟙 _) ((Category.comp_id _).trans hen.symm)
      ((Category.comp_id b).trans (Category.id_comp b).symm)
    have hl : l ≫ pullback.snd fB.fromNormalization b =
        pullback.snd f.fromNormalization b :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    have hcomp : IsFiniteEtale (l ≫ pullback.snd fB.fromNormalization b) :=
      hl.symm ▸ hlocal p
    let : IsFinite (l ≫ pullback.snd fB.fromNormalization b) := hcomp.toIsFinite
    let : Etale (l ≫ pullback.snd fB.fromNormalization b) := hcomp.toEtale
    have hBinv : IsFiniteEtale (inv l ≫ (l ≫ pullback.snd fB.fromNormalization b)) := ⟨⟩
    have hB : IsFiniteEtale (pullback.snd fB.fromNormalization b) :=
      IsIso.inv_hom_id_assoc l (pullback.snd fB.fromNormalization b) ▸ hBinv
    exact finite_etale_tensor_integralClosure_of_normalization_baseChange
      R B (Localization.AtPrime p.asIdeal) hB
  have hB := SchemeTheory.finite_etale_integralClosure_of_local_finite_etale
    d A B hnormal hBlocal
  let : IsFiniteEtale fB.fromNormalization :=
    (isFiniteEtale_specNormalization_iff R B).mpr hB
  have hcomp : IsFiniteEtale (en.hom ≫ fB.fromNormalization) :=
    ⟨⟩
  exact hen ▸ hcomp

end EtaleFundamentalGroups
