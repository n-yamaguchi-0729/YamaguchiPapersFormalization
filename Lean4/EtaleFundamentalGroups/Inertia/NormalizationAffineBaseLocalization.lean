/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Affine.FlatBaseChangeSections
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Localization of an affine base commutes with relative normalization

The source is any qcqs morphism. Flat base change computes global sections
by a tensor product, and localization commutes with integral closure. These
identifications agree with the actual canonical normalizationPullback map.

The proof adapts the smooth base-change argument in Mathlib by Andrew Yang:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicGeometry/Normalization.lean
The algebraic input here is localization, not smoothness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Relative normalization commutes with a flat base change wherever the
actual map on affine sections is a localization. The source need only be qcqs. -/
theorem isIso_normalizationPullback_restrict_of_isLocalization
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    {U : S.Opens} {V : T.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) (M : Submonoid Γ(S, U)) :
    let : Algebra Γ(S, U) Γ(T, V) := (g.appLE U V hVU).hom.toAlgebra
    IsLocalization M Γ(T, V) →
      IsIso (morphismRestrict (f.normalizationPullback g)
        (pullback.snd f.fromNormalization g ⁻¹ᵁ V)) := by
  intro hRT hLoc
  let W := pullback.snd f.fromNormalization g ⁻¹ᵁ V
  apply (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr
  have hOpen : W =
      pullback.fst f.fromNormalization g ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) ⊓
        pullback.snd f.fromNormalization g ⁻¹ᵁ V := by
    dsimp only [W]
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]
  have hNormSection := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    hOpen
    hU hV (hU.preimage f.fromNormalization).isCompact
    (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← isIso_comp_left_iff (pushoutSection (IsPullback.of_hasPullback f.fromNormalization g)
    hVU le_rfl (UY := W) hOpen),
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  let : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(T, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    ((pullback.snd f g).app V).hom.toAlgebra
  let e := affinePullbackSectionsTensorEquiv f g hU hV hVU
  let ψ : Γ(T, V) ⊗[Γ(S, U)] integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(T, V)]
      integralClosure Γ(T, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization M)
  let j : Γ((pullback.snd f g).normalization, (pullback.snd f g).fromNormalization ⁻¹ᵁ V) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage,
        Scheme.Hom.normalizationPullback_snd])).op
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom
        (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by rw [Scheme.Hom.fromNormalization_app _ hU];
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp])
      (by simp only [Category.id_comp, Category.comp_id]) ≫
    (CommRingCat.isPushout_tensorProduct Γ(S, U) Γ(T, V)
      (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    j
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  apply pushout.hom_ext
  · dsimp only [φ]
    simp only [pushout.congrHom_hom,
      Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    apply (cancel_mono (inv j)).mp
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    apply (cancel_mono ((pullback.snd f g).normalizationObjIso hV).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [j]
    simp only [← Functor.map_inv, eqToHom_op, inv_eqToHom, Scheme.Hom.appLE_map_assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(T, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change (pullback.fst f g).appLE _ _ H x = _
      trans e (1 ⊗ₜ[Γ(S, U)] (x : Γ(X, f ⁻¹ᵁ U)))
      · exact (affinePullbackSectionsTensorEquiv_one_tmul f g hU hV hVU
          (x : Γ(X, f ⁻¹ᵁ U))).symm
      · rfl
  · dsimp only [φ]
    simp only [pushout.congrHom_hom,
      Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, IsPushout.inr_isoPushout_inv_assoc]
    apply (cancel_mono (inv j)).mp
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    apply (cancel_mono ((pullback.snd f g).normalizationObjIso hV).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [j]
    simp only [← Functor.map_inv, eqToHom_op, inv_eqToHom, Scheme.Hom.appLE_map_assoc,
      ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congrArg CommRingCat.ofHom ψ.comp_algebraMap.symm

/-- If an affine base change lies in one affine open and its actual section
map is a localization, the canonical normalization comparison is an isomorphism. -/
theorem isIso_normalizationPullback_of_affineLocalizationSections
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [IsAffine T]
    {U : S.Opens} (hU : IsAffineOpen U)
    (hTU : (⊤ : T.Opens) ≤ g ⁻¹ᵁ U) (M : Submonoid Γ(S, U)) :
    let : Algebra Γ(S, U) Γ(T, ⊤) := (g.appLE U ⊤ hTU).hom.toAlgebra
    IsLocalization M Γ(T, ⊤) → IsIso (f.normalizationPullback g) := by
  intro hRT hLoc
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms _) fun x ↦ ?_
  refine ⟨pullback.snd f.fromNormalization g ⁻¹ᵁ ⊤, trivial, ?_⟩
  exact isIso_normalizationPullback_restrict_of_isLocalization
    f g hU (isAffineOpen_top T) hTU M hLoc

end EtaleFundamentalGroups.Inertia
