/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_comap_injective_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Hom
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.IsTensorProduct

/-!
# Faithfully flat detection of ideal sheaves

Inverse image along a flat surjective scheme morphism is injective on ideal
sheaves. The comparison is checked on affine opens and localizations.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_comap_injective_of_flat_of_surjective

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Algebra
open _root_.Algebra
namespace IsPushout
open _root_.Algebra.IsPushout
open _root_.Algebra.IsPushout
open _root_.Algebra

theorem ker_algebraMap_eq_map_ker
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) = (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  let e : B ⊗[R] C ≃ₐ[B] P := Algebra.IsPushout.equiv R B C P
  have h1 : algebraMap B P = e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom := by
    ext b
    simp [e]
  rw [h1, RingHom.ker_comp_of_injective _ e.toRingEquiv.injective]
  let g : R →ₐ[R] C := Algebra.ofId R C
  have h2 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom.comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom := by
    ext b
    simp [g]
  have h3 : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom =
      (RingHom.ker (algebraMap R C)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    have := Algebra.TensorProduct.lTensor_ker (A := B) g hC
    simp only [AlgHom.ker_coe, AlgHom.coe_ideal_map, g, Algebra.toRingHom_ofId] at this
    exact this
  rw [h2, ← RingHom.comap_ker, h3]
  let r : B ⊗[R] R ≃ₐ[R] B := Algebra.TensorProduct.rid R R B
  have h4 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom =
      (r.toRingEquiv.symm : B →+* B ⊗[R] R) := by
    ext b
    apply r.toRingEquiv.injective
    simp [r]
  have h5 : (algebraMap R B) = (r.toRingEquiv : B ⊗[R] R →+* B).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    ext x
    simp [r, Algebra.smul_def]
  rw [h4, h5, ← Ideal.map_map, Ideal.comap_coe, Ideal.map_coe, Ideal.comap_symm]

end Algebra.IsPushout

namespace CommRingCat
open _root_.CommRingCat
open _root_.CommRingCat

theorem ker_eq_map_ker_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr)
    (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have hw : inl.hom.comp f.hom = inr.hom.comp g.hom := by
    simpa only [CommRingCat.hom_comp] using congr(($(h.w)).hom)
  have : IsScalarTower R C P := .of_algebraMap_eq' hw
  have : Algebra.IsPushout R B C P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.IsPushout.ker_algebraMap_eq_map_ker R B C P hg

end CommRingCat

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

theorem ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f I.subschemeι)
  have := CommRingCat.ker_eq_map_ker_of_isPushout H
    (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top X⟩)
  rw [← ker_subschemeι_app I ⟨⊤, isAffineOpen_top X⟩, comap, Scheme.Hom.ker_apply]
  exact this


theorem ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom := by
  suffices key : ∀ (U' : X.affineOpens) (V' : Y.affineOpens),
      U' = ⟨(U : X.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using U.2⟩ →
      V' = ⟨(V : Y.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using V.2⟩ →
      ∀ (e : (V' : Y.Opens) ≤ f ⁻¹ᵁ (U' : X.Opens)),
        (I.comap f).ideal V' = (I.ideal U').map (f.appLE U' V' e).hom from
    key U V (Subtype.ext (U : X.Opens).ι_image_top.symm)
      (Subtype.ext (V : Y.Opens).ι_image_top.symm) hVU
  rintro _ _ rfl rfl e
  have : IsAffine (U : X.Opens) := U.2
  have : IsAffine (V : Y.Opens) := V.2
  have h := ideal_comap_top (I.comap (U : X.Opens).ι) (f.resLE U V hVU)
  rw [← comap_comp, Scheme.Hom.resLE_comp_ι, comap_comp,
    ideal_comap_of_isOpenImmersion (I.comap f) (V : Y.Opens).ι,
    ideal_comap_of_isOpenImmersion I (U : X.Opens).ι] at h
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at h
  erw [CommRingCat.hom_id, Ideal.comap_id] at h
  erw [CommRingCat.hom_id, Ideal.comap_id] at h
  have hmap :
      (U : X.Opens).topIso.hom ≫ f.appLE U V hVU ≫ (V : Y.Opens).topIso.inv =
        f.appLE ((U : X.Opens).ι ''ᵁ ⊤) ((V : Y.Opens).ι ''ᵁ ⊤) e := by
    simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv]
    exact (congrArg
      (fun k : Γ(X, (U : X.Opens)) ⟶ Γ(Y, (V : Y.Opens).ι ''ᵁ ⊤) =>
        X.presheaf.map (eqToHom (U : X.Opens).ι_image_top.symm).op ≫ k)
      (Scheme.Hom.appLE_map f hVU (eqToHom (V : Y.Opens).ι_image_top).op)).trans
      (Scheme.Hom.map_appLE f _ (eqToHom (U : X.Opens).ι_image_top.symm).op)
  exact h.trans (congrArg
    (fun k : Γ(X, (U : X.Opens).ι ''ᵁ ⊤) ⟶ Γ(Y, (V : Y.Opens).ι ''ᵁ ⊤) =>
      Ideal.map k.hom
        (I.ideal ⟨(U : X.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using U.2⟩))
    hmap)

theorem ideal_comap_of_isAffineHom (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = (I.ideal U).map (f.app U).hom := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ideal_comap_of_le I f U ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ le_rfl

end AlgebraicGeometry.Scheme.IdealSheafData

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open _root_.AlgebraicGeometry
    Scheme_IdealSheafData_comap_injective_of_flat_of_surjective.AlgebraicGeometry in
with_weak_namespace Scheme_IdealSheafData_comap_injective_of_flat_of_surjective
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective
    {X Y : Scheme.{u}} (π : Y ⟶ X) [Flat π] [Surjective π] :
    Function.Injective fun I : X.IdealSheafData => I.comap π := by
  intro I J h
  change I.comap π = J.comap π at h
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  have hU : IsAffineOpen (U : X.Opens) := U.2
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let 𝔭 : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
  obtain ⟨y, hy⟩ := π.surjective (hU.fromSpec 𝔭)
  have hyU : y ∈ π ⁻¹ᵁ (U : X.Opens) := by
    change π y ∈ (U : X.Opens)
    rw [hy, ← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self 𝔭
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (π ⁻¹ᵁ (U : X.Opens)).isOpen
  have hφ : (π.appLE U V hVU).hom.Flat := Flat.flat_appLE π hU hV hVU
  let 𝔮 : PrimeSpectrum Γ(Y, V) := hV.primeIdealOf ⟨y, hyV⟩
  have h𝔮 : P = 𝔮.asIdeal.comap (π.appLE U V hVU).hom := by
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE (U : X.Opens) hU V hV hVU hyV
    have h2 : hU.primeIdealOf ⟨π y, hVU hyV⟩ = 𝔭 :=
      hU.fromSpec.isOpenEmbedding.injective (by rw [IsAffineOpen.fromSpec_primeIdealOf]; exact hy)
    exact (congrArg PrimeSpectrum.asIdeal (h1.trans h2)).symm
  have hIJ : (I.ideal U).map (π.appLE U V hVU).hom = (J.ideal U).map (π.appLE U V hVU).hom := by
    rw [← Scheme.IdealSheafData.ideal_comap_of_le I π U ⟨V, hV⟩ hVU,
      ← Scheme.IdealSheafData.ideal_comap_of_le J π U ⟨V, hV⟩ hVU, h]
  let ψ := Localization.localRingHom P 𝔮.asIdeal (π.appLE U V hVU).hom h𝔮
  have hψ : ψ.Flat := RingHom.Flat.localRingHom hφ 𝔮.asIdeal P h𝔮
  let := ψ.toAlgebra
  have : Module.Flat (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal) := hψ
  have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal)) :=
    show IsLocalHom ψ from inferInstance
  have : Module.FaithfullyFlat (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  suffices hloc : ((I.ideal U).map (algebraMap _ (Localization.AtPrime P))).map
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal)) =
      ((J.ideal U).map (algebraMap _ (Localization.AtPrime P))).map
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal)) by
    have := congrArg
      (Ideal.comap (algebraMap (Localization.AtPrime P) (Localization.AtPrime 𝔮.asIdeal))) hloc
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat,
      Ideal.comap_map_eq_self_of_faithfullyFlat] at this
  have hcomm : ψ.comp (algebraMap Γ(X, U) (Localization.AtPrime P)) =
      (algebraMap Γ(Y, V) (Localization.AtPrime 𝔮.asIdeal)).comp (π.appLE U V hVU).hom :=
    RingHom.ext fun x => Localization.localRingHom_to_map P 𝔮.asIdeal _ h𝔮 x
  rw [Ideal.map_map, Ideal.map_map, RingHom.algebraMap_toAlgebra, hcomm, ← Ideal.map_map,
    ← Ideal.map_map, hIJ]
end Scheme_IdealSheafData_comap_injective_of_flat_of_surjective
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
