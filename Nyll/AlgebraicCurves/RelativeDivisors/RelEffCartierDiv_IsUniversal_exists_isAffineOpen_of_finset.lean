/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_isAffineOpen_of_finset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isUniversal_empty
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isRepresentable_supportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor

/-!
# Rel Eff Cartier Div Is Universal exists is Affine Open of finset
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_IsUniversal_exists_isAffineOpen_of_finset
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
attribute [-simp] AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (IsOpenImmersion.lift Surjective SmoothOfRelativeDimension
  Scheme.Opens.range_ι Scheme.Hom IsAffine.of_isIso IsAffine Scheme Smooth IsOpenImmersion
  IsSeparated Scheme.Hom.one_le_finrank_iff_surjective IsAffineOpen Scheme.Opens
  IsOpenImmersion.lift_fac Scheme.Hom.comp_apply RelEffCartierDiv.empty RelEffCartierDiv
  RelEffCartierDiv.I RelEffCartierDiv.supportedIn RelEffCartierDiv.functor
  RelEffCartierDiv.isRepresentable_supportedIn)

namespace RelEffCartierDiv

export _root_.AlgebraicGeometry.RelEffCartierDiv (empty ext pullbackAlong I flat isFinite
  finrank_eq SupportedIn supportedInLocus mem_supportedInLocus_iff supportedIn_pullbackAlong_iff
  supportedIn functor IsUniversal isRepresentable_supportedIn)

namespace AffineCoverDiv

open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry


variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
  {Duniv : RelEffCartierDiv f r y}

/-- The representation of divisors supported in an open set by the corresponding universal
locus. -/
noncomputable def representableByLocus (hU : Duniv.IsUniversal) (U : 𝒞.Opens) :
    (RelEffCartierDiv.supportedIn f r U).toFunctor.RepresentableBy
      (Duniv.supportedInLocus U : Scheme.{u}) := by
  let W : Y.Opens := Duniv.supportedInLocus U
  have hrange : ∀ {T : Scheme.{u}} (x : (RelEffCartierDiv.supportedIn f r U).toFunctor.obj (op T)),
      Set.range ((hU.homEquiv T).symm x.1) ⊆ Set.range W.ι := by
    intro T x
    rw [Scheme.Opens.range_ι, ← supportedIn_pullbackAlong_iff Duniv U ((hU.homEquiv T).symm x.1)
      (hU.lift_comp x.1.2)]
    change (Duniv.pullbackAlong (hU.lift x.1.2) (hU.lift_comp x.1.2)).SupportedIn U
    rw [hU.pullbackAlong_lift]
    exact x.2
  refine
    { homEquiv := fun {T} =>
        { toFun := fun φ => ⟨hU.homEquiv T (φ ≫ W.ι), ?mem⟩
          invFun := fun x => IsOpenImmersion.lift W.ι ((hU.homEquiv T).symm x.1) (hrange x)
          left_inv := ?li
          right_inv := ?ri }
      homEquiv_comp := ?nat }
  case mem =>
    change (Duniv.pullbackAlong (φ ≫ W.ι) rfl).SupportedIn U
    rw [supportedIn_pullbackAlong_iff]
    rintro _ ⟨t, rfl⟩
    exact (φ t).2
  case li =>
    intro φ
    rw [← cancel_mono W.ι, IsOpenImmersion.lift_fac, Equiv.symm_apply_apply]
  case ri =>
    intro x
    apply Subtype.ext
    change hU.homEquiv T (IsOpenImmersion.lift W.ι _ _ ≫ W.ι) = x.1
    rw [IsOpenImmersion.lift_fac]
    exact (hU.homEquiv T).apply_symm_apply x.1
  case nat =>
    intro T T' φ g
    apply Subtype.ext
    change hU.homEquiv T ((φ ≫ g) ≫ W.ι) =
      (RelEffCartierDiv.functor f r).map φ.op (hU.homEquiv T' (g ≫ W.ι))
    rw [Category.assoc]
    exact hU.representableBy.homEquiv_comp φ (g ≫ W.ι)

theorem main [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (hU : Duniv.IsUniversal) (V : S.affineOpens) (F : Finset Y)
    (hF : ∀ p ∈ F, y p ∈ (V : S.Opens)) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ W ≤ y ⁻¹ᵁ (V : S.Opens) ∧ ∀ p ∈ F, p ∈ W := by
  classical
  have := Duniv.isFinite
  have := Duniv.flat
  let q : Duniv.I.subscheme ⟶ Y := Duniv.I.subschemeι ≫ pullback.snd f y
  have hfib : (q ⁻¹' (F : Set Y)).Finite := q.finite_preimage F.finite_toSet
  let G : Finset 𝒞 := (hfib.image fun z => pullback.fst f y (Duniv.I.subschemeι z)).toFinset
  have hG : ∀ x ∈ G, f x ∈ (V : S.Opens) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (Set.Finite.mem_toFinset _).mp hx
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact hF _ hz
  obtain ⟨U, hUaff, hUV, hGU⟩ := hcov V G hG
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · let ψ : S ⟶ Y := hU.lift (RelEffCartierDiv.empty f (𝟙 S))
    have hψ : ψ ≫ y = 𝟙 S := hU.lift_comp _
    have hyψ : y ≫ ψ = 𝟙 Y := by
      apply hU.hom_ext (φ := y ≫ ψ) (ψ := 𝟙 Y) (by rw [Category.assoc, hψ, Category.comp_id,
        Category.id_comp])
      exact congrArg RelEffCartierDiv.I
        (Subsingleton.elim (Duniv.pullbackAlong (y ≫ ψ) rfl) (Duniv.pullbackAlong (𝟙 Y) _))
    have : IsIso y := ⟨ψ, hyψ, hψ⟩
    exact ⟨y ⁻¹ᵁ (V : S.Opens), V.2.preimage_of_isIso y, le_rfl, fun p hp => hF p hp⟩
  · let W : Y.Opens := Duniv.supportedInLocus U
    have hFW : ∀ p ∈ F, p ∈ W := by
      intro p hp
      rw [mem_supportedInLocus_iff]
      intro z hz
      exact hGU _ ((Set.Finite.mem_toFinset _).mpr ⟨z,
        by change q z ∈ (F : Set Y); rw [hz]; exact hp, rfl⟩)
    have hWV : W ≤ y ⁻¹ᵁ (V : S.Opens) := by
      intro p hp
      have hsurj : Surjective q := by
        rw [← Scheme.Hom.one_le_finrank_iff_surjective]
        intro t
        change 1 ≤ (Duniv.I.subschemeι ≫ pullback.snd f y).finrank t
        rw [Duniv.finrank_eq]
        exact hr
      obtain ⟨z, rfl⟩ := hsurj.1 p
      have hzU : pullback.fst f y (Duniv.I.subschemeι z) ∈ U :=
        (mem_supportedInLocus_iff _ _ _).mp hp z rfl
      change y (q z) ∈ (V : S.Opens)
      have := hUV hzU
      change f (pullback.fst f y (Duniv.I.subschemeι z)) ∈ (V : S.Opens) at this
      rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    obtain ⟨X, hXaff, ⟨eX⟩⟩ := RelEffCartierDiv.isRepresentable_supportedIn f r V ⟨U, hUaff⟩ hUV
    have := hXaff hr
    let e : X ≅ (W : Scheme.{u}) := eX.uniqueUpToIso (representableByLocus hU U)
    have hWaff : IsAffineOpen W := IsAffine.of_isIso e.inv
    exact ⟨W, hWaff, hWV, hFW⟩

end AlgebraicGeometry.RelEffCartierDiv.AffineCoverDiv

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal.exists_isAffineOpen_of_finset
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {Duniv : RelEffCartierDiv f r y}
    (hU : Duniv.IsUniversal) (V : S.affineOpens) (F : Finset Y)
    (hF : ∀ p ∈ F, y p ∈ (V : S.Opens)) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ W ≤ y ⁻¹ᵁ (V : S.Opens) ∧ ∀ p ∈ F, p ∈ W :=
  AlgebraicGeometry.RelEffCartierDiv.AffineCoverDiv.main hcov hU V F hF
end RelEffCartierDiv_IsUniversal_exists_isAffineOpen_of_finset
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
attribute [-simp] AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
