/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_etale_of_formallyUnramified_stalkMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.Algebraize

/-!
# exists etale of formally Unramified stalk Map
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.exists_etale_of_formallyUnramified_stalkMap

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe u

open TensorProduct IsLocalRing

namespace JacobianCriterionAux

section rank

variable {R B : Type*} [CommRing R] [CommRing B] [IsLocalRing B] [Algebra R B]

/-- Transport of the cotangent space along equality of ideals. -/
def cotangentEquivOfEq {S : Type*} [CommRing S] {I J : Ideal S} (h : I = J) :
    I.Cotangent ≃ₗ[S] J.Cotangent := h ▸ LinearEquiv.refl S I.Cotangent

theorem finrank_kaehlerDifferential_eq_finrank_cotangentSpace
    [Algebra.FormallySmooth R B] [Algebra.EssFiniteType R B]
    (hB : Function.Bijective (algebraMap R (ResidueField B))) :
    Module.finrank B Ω[B⁄R] = Module.finrank (ResidueField B) (CotangentSpace B) := by
  have hsurj : Function.Surjective (algebraMap B (ResidueField B)) :=
    Ideal.Quotient.mk_surjective
  let e : R ≃ₐ[R] ResidueField B := AlgEquiv.ofBijective (Algebra.ofId R (ResidueField B)) hB
  have : Algebra.FormallySmooth R (ResidueField B) := .of_equiv e
  have : Algebra.FormallyUnramified R (ResidueField B) := .of_equiv e
  have : Module.Free B Ω[B⁄R] := Module.free_of_flat_of_isLocalRing
  have hker : RingHom.ker (algebraMap B (ResidueField B)) = maximalIdeal B := Ideal.mk_ker
  have hφinj : Function.Injective (KaehlerDifferential.kerCotangentToTensor R B (ResidueField B)) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := R) (P := B)
      (A := ResidueField B) hsurj).mpr inferInstance
  have hφsurj : Function.Surjective
      (KaehlerDifferential.kerCotangentToTensor R B (ResidueField B)) := by
    rw [← LinearMap.range_eq_top,
      KaehlerDifferential.range_kerCotangentToTensor R B (ResidueField B) hsurj,
      Submodule.restrictScalars_eq_top_iff, LinearMap.ker_eq_top]
    ext x; exact Subsingleton.elim _ _
  let ψ : CotangentSpace B →ₗ[B] ResidueField B ⊗[B] Ω[B⁄R] :=
    KaehlerDifferential.kerCotangentToTensor R B (ResidueField B) ∘ₗ
      (cotangentEquivOfEq hker).symm.toLinearMap
  have hψ : Function.Bijective ψ :=
    ⟨hφinj.comp (cotangentEquivOfEq hker).symm.injective,
      hφsurj.comp (cotangentEquivOfEq hker).symm.surjective⟩
  let ψ' : CotangentSpace B ≃ₗ[ResidueField B] ResidueField B ⊗[B] Ω[B⁄R] :=
    LinearEquiv.ofBijective (ψ.extendScalarsOfSurjective hsurj) hψ
  rw [ψ'.finrank_eq, Module.finrank_baseChange]

theorem bijective_algebraMap_residueField_of_section {R₀ : Type*} [CommRing R₀] [Nontrivial R₀]
    (hR : IsField R) (s : B →+* R₀) (hs : Function.Surjective (s.comp (algebraMap R B))) :
    Function.Bijective (algebraMap R (ResidueField B)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h
    obtain ⟨t, ht⟩ := hR.mul_inv_cancel h
    have := congrArg (algebraMap R (ResidueField B)) ht
    rw [map_mul, hr, zero_mul, map_one] at this
    exact zero_ne_one this
  · intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, hr⟩ := hs (s b)
    refine ⟨r, ?_⟩
    rw [IsScalarTower.algebraMap_apply R B (ResidueField B)]
    change Ideal.Quotient.mk (maximalIdeal B) (algebraMap R B r) =
      Ideal.Quotient.mk (maximalIdeal B) b
    rw [Ideal.Quotient.eq]
    have hmem : algebraMap R B r - b ∈ RingHom.ker s := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hr
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top s) hmem

end rank

section core

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R B]
  [Algebra.EssFiniteType R A] [Algebra.EssFiniteType R B]
  [Algebra.FormallyUnramified A B]

theorem formallySmooth_of_formallyUnramified_of_finrank_eq
    (hA : Function.Bijective (algebraMap R (ResidueField A)))
    (hB : Function.Bijective (algebraMap R (ResidueField B)))
    (hdim : Module.finrank (ResidueField B) (CotangentSpace B) =
      Module.finrank (ResidueField A) (CotangentSpace A)) :
    Algebra.FormallySmooth A B := by
  have : Module.Free A Ω[A⁄R] := Module.free_of_flat_of_isLocalRing
  have : Module.Free B Ω[B⁄R] := Module.free_of_flat_of_isLocalRing
  have hrk : Module.finrank B Ω[B⁄R] = Module.finrank B (B ⊗[A] Ω[A⁄R]) := by
    rw [Module.finrank_baseChange, finrank_kaehlerDifferential_eq_finrank_cotangentSpace hA,
      finrank_kaehlerDifferential_eq_finrank_cotangentSpace hB, hdim]
  have husurj : Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
    rw [← LinearMap.range_eq_top,
      ← (KaehlerDifferential.exact_mapBaseChange_map R A B).linearMap_ker_eq, LinearMap.ker_eq_top]
    ext x; exact Subsingleton.elim _ _
  have huinj : Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
    obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrk
    have : Function.Injective (e.toLinearMap ∘ₗ KaehlerDifferential.mapBaseChange R A B) :=
      OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp husurj)
    rw [LinearMap.coe_comp] at this
    exact this.of_comp
  have hδ : Function.Injective (Algebra.H1Cotangent.δ R A B) := by
    rw [← LinearMap.ker_eq_bot, (Algebra.H1Cotangent.exact_map_δ R A B).linearMap_ker_eq,
      LinearMap.range_eq_bot]
    ext x; simp [Subsingleton.elim x 0]
  have hH1 : Subsingleton (Algebra.H1Cotangent A B) := by
    refine ⟨fun x y ↦ hδ (huinj ?_)⟩
    rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange R A B).apply_apply_eq_zero,
      (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B).apply_apply_eq_zero]
  have : Module.Free B Ω[B⁄A] := Module.Free.of_subsingleton B _
  exact ⟨inferInstance, hH1⟩

end core

end JacobianCriterionAux

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits JacobianCriterionAux

theorem isField_stalk_Spec_of_field {K : Type u} [Field K] (p : ↥(Spec (.of K))) :
    IsField ((Spec (.of K)).presheaf.stalk p) := by
  obtain rfl : p = closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) p (closedPoint K)
  exact (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)


theorem exists_etale_of_formallySmooth_of_formallyUnramified_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (hxV : x ∈ V) (hfp : (f.appLE U V hVU).hom.FinitePresentation)
    (H : (f.stalkMap x).hom.FormallySmooth) (H' : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f) := by
  algebraize [(f.appLE U V hVU).hom]
  let p := (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have h1 : Algebra.IsSmoothAt Γ(Y, U) q := (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mp H
  have h2 : Algebra.IsUnramifiedAt Γ(Y, U) q := by
    have : q.LiesOver p :=
      ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm⟩
    let := Localization.AtPrime.algebraOfLiesOver p q
    have hpq : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) := by
      rw [← RingHom.formallyUnramified_algebraMap]
      exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hxV)).mp H'
    have : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime p) :=
      .of_isLocalization p.primeCompl
    exact Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p) (Localization.AtPrime q)
  have h3 : Algebra.IsEtaleAt Γ(Y, U) q :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨h2, h1⟩
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U)) (A := Γ(X, V)) q
  have e : X.basicOpen r ≤ f ⁻¹ᵁ U := (X.basicOpen_le r).trans hVU
  refine ⟨X.basicOpen r, ?_, ?_⟩
  · rw [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen] at hrx
    let z : Spec Γ(X, V) := hV.isoSpec.hom ⟨x, hxV⟩
    have hx : hV.fromSpec z ∈ X.basicOpen r := hrx
    have heq : hV.fromSpec z = x := by
      change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨x, hxV⟩ = x
      rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]
      rfl
    exact heq ▸ hx
  · have hr' : (f.appLE U (X.basicOpen r) e).hom.Etale := by
      have := hV.isLocalization_basicOpen r
      rw [← RingHom.etale_algebraMap] at hr
      convert RingHom.Etale.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
      ext
      dsimp
      simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
        AlgEquiv.commutes]
      simp only [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply,
        Scheme.Hom.appLE_map]
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : Etale (f.resLE U (X.basicOpen r) e) := by
      have : IsAffine _ := hU
      have : IsAffine _ := hV.basicOpen r
      rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
      exact (RingHom.Etale.propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f U _ e)).mpr hr'
    infer_instance


theorem exists_etale_of_formallyUnramified_stalkMap_aux
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [Smooth sX] [Smooth sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ sX = 𝟙 _)
    (hfu : (f.stalkMap (σ.base (IsLocalRing.closedPoint K))).hom.FormallyUnramified)
    (hdim : Module.finrank
        (IsLocalRing.ResidueField (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint K))))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint K)))) =
      Module.finrank
        (IsLocalRing.ResidueField
          (Y.presheaf.stalk (f.base (σ.base (IsLocalRing.closedPoint K)))))
        (IsLocalRing.CotangentSpace
          (Y.presheaf.stalk (f.base (σ.base (IsLocalRing.closedPoint K)))))) :
    ∃ U : X.Opens, σ.base (IsLocalRing.closedPoint K) ∈ U ∧ Etale (U.ι ≫ f) := by
  let pK : Spec (.of K) := closedPoint K
  have hnt (S : Scheme.{u}) (z : S) : Nontrivial (S.presheaf.stalk z) := inferInstance
  have : Nontrivial ((Spec (.of K)).presheaf.stalk pK) := hnt (Spec (.of K)) pK
  subst hf
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sY
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f.base (σ.base (pK)))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have hfp : (f.appLE U V hVU).hom.FinitePresentation := by
    have h1 : ((f ≫ sY).appLE ⊤ V le_top).hom.FinitePresentation :=
      (f ≫ sY).finitePresentation_appLE (isAffineOpen_top _) hV _
    have h2 : (sY.appLE ⊤ U le_top).hom.FiniteType :=
      sY.finiteType_appLE (isAffineOpen_top _) hU _
    rw [← Scheme.Hom.appLE_comp_appLE f sY ⊤ U V le_top hVU, CommRingCat.hom_comp] at h1
    exact RingHom.FinitePresentation.of_comp_finiteType _ h1 h2
  refine exists_etale_of_formallySmooth_of_formallyUnramified_stalkMap f _ U hU V hV hVU hxV hfp
    ?_ hfu
  let iRA : Algebra ((Spec (.of K)).presheaf.stalk (sY.base (f.base (σ.base (pK)))))
      (Y.presheaf.stalk (f.base (σ.base (pK)))) :=
    (sY.stalkMap (f.base (σ.base (pK)))).hom.toAlgebra
  let iAB : Algebra (Y.presheaf.stalk (f.base (σ.base (pK))))
      (X.presheaf.stalk (σ.base (pK))) :=
    (f.stalkMap (σ.base (pK))).hom.toAlgebra
  let iRB : Algebra ((Spec (.of K)).presheaf.stalk (sY.base (f.base (σ.base (pK)))))
      (X.presheaf.stalk (σ.base (pK))) :=
    (sY.stalkMap (f.base (σ.base (pK))) ≫ f.stalkMap (σ.base (pK))).hom.toAlgebra
  have : IsScalarTower ((Spec (.of K)).presheaf.stalk (sY.base (f.base (σ.base (pK)))))
      (Y.presheaf.stalk (f.base (σ.base (pK))))
      (X.presheaf.stalk (σ.base (pK))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FormallySmooth
      ((Spec (.of K)).presheaf.stalk (sY.base (f.base (σ.base (pK)))))
      (Y.presheaf.stalk (f.base (σ.base (pK)))) :=
    (Scheme.Hom.mem_smoothLocus (f := sY)).mp (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)
  have : Algebra.FormallySmooth
      ((Spec (.of K)).presheaf.stalk (sY.base (f.base (σ.base (pK)))))
      (X.presheaf.stalk (σ.base (pK))) := by
    have h := (Scheme.Hom.mem_smoothLocus (f := f ≫ sY) (x := σ.base (pK))).mp
      (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)
    rw [Scheme.Hom.stalkMap_comp] at h
    exact h
  have : Algebra.EssFiniteType
      ((Spec (.of K)).presheaf.stalk (sY.base (f.base (σ.base (pK)))))
      (Y.presheaf.stalk (f.base (σ.base (pK)))) :=
    LocallyOfFiniteType.stalkMap sY _
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f.base (σ.base (pK))))
      (X.presheaf.stalk (σ.base (pK))) :=
    LocallyOfFiniteType.stalkMap f _
  have : Algebra.EssFiniteType
      ((Spec (.of K)).presheaf.stalk (sY.base (f.base (σ.base (pK)))))
      (X.presheaf.stalk (σ.base (pK))) :=
    Algebra.EssFiniteType.comp _ (Y.presheaf.stalk (f.base (σ.base (pK)))) _
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f.base (σ.base (pK))))
      (X.presheaf.stalk (σ.base (pK))) := hfu
  have hR := isField_stalk_Spec_of_field (K := K) (sY.base (f.base (σ.base pK)))
  have hsurj : Function.Surjective
      ((sY.stalkMap (f.base (σ.base pK)) ≫ f.stalkMap (σ.base pK)) ≫
        σ.stalkMap pK).hom := by
    have heq : (σ ≫ f ≫ sY).stalkMap pK =
        (sY.stalkMap (f.base (σ.base pK)) ≫ f.stalkMap (σ.base pK)) ≫
          σ.stalkMap pK := by
      rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
      rfl
    have hiso : IsIso ((σ ≫ f ≫ sY).stalkMap pK) := by
      have : IsIso (σ ≫ f ≫ sY) := by rw [hσ]; infer_instance
      exact ((isIso_iff_isIso_stalkMap _).mp this).2 _
    rw [← heq]
    exact (asIso ((σ ≫ f ≫ sY).stalkMap pK)).commRingCatIsoToRingEquiv.surjective
  have hB := bijective_algebraMap_residueField_of_section hR (σ.stalkMap pK).hom hsurj
  have hA := bijective_algebraMap_residueField_of_section hR
    (f.stalkMap (σ.base pK) ≫ σ.stalkMap (pK)).hom hsurj
  exact formallySmooth_of_formallyUnramified_of_finrank_eq hA hB hdim

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.exists_etale_of_formallyUnramified_stalkMap
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [Smooth sX] [Smooth sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ sX = 𝟙 _)
    (hfu : (f.stalkMap (σ.base (IsLocalRing.closedPoint K))).hom.FormallyUnramified)
    (hdim : Module.finrank
        (IsLocalRing.ResidueField (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint K))))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint K)))) =
      Module.finrank
        (IsLocalRing.ResidueField
          (Y.presheaf.stalk (f.base (σ.base (IsLocalRing.closedPoint K)))))
        (IsLocalRing.CotangentSpace
          (Y.presheaf.stalk (f.base (σ.base (IsLocalRing.closedPoint K)))))) :
    ∃ U : X.Opens, σ.base (IsLocalRing.closedPoint K) ∈ U ∧ Etale (U.ι ≫ f) := by
  exact AlgebraicGeometry.exists_etale_of_formallyUnramified_stalkMap_aux sX sY f hf σ hσ hfu hdim
end AlgebraicCurves.Geometry.Schemes.Proofs.exists_etale_of_formallyUnramified_stalkMap
end ProofImplementation
