/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal

/-!
# Vanishing of a pulled-back section at a field-valued point

An invertible-module section vanishes after pullback to a field-valued point exactly
when that point lies in the support of the zero-scheme ideal of the section.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace PointVanishing

variable {X : Scheme.{u}} {N : X.Modules}

/-- The local section obtained by evaluating a unit-module morphism on the scalar one. -/
abbrev sVal (t : 𝟙_ X.Modules ⟶ N) (W : X.Opens) : Γ(N, W) := t.app W (toUnitSection W 1)

lemma map_sVal (t : 𝟙_ X.Modules ⟶ N) {W V : X.Opens} (i : V ⟶ W) :
    N.presheaf.map i.op (sVal t W) = sVal t V := by
  have h := (NatTrans.naturality_apply t.mapPresheaf i.op (toUnitSection W 1)).symm
  have h1 : (𝟙_ X.Modules).presheaf.map i.op (toUnitSection W 1) = toUnitSection V 1 :=
    (X.presheaf.map i.op).hom.map_one
  rw [h1] at h
  exact h

lemma eq_smul_one (W : X.Opens) (x : Γ(𝟙_ X.Modules, W)) :
    x = ofUnitSection W x • toUnitSection W 1 :=
  (mul_one (ofUnitSection W x)).symm

lemma eq_zero_iff_sVal_eq_zero (t : 𝟙_ X.Modules ⟶ N) (W₀ : X.Opens) (hW₀ : W₀ = ⊤) :
    t = 0 ↔ sVal t W₀ = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Scheme.Modules.hom_ext
    intro W
    ext x
    have hle : W ≤ W₀ := hW₀ ▸ le_top
    rw [eq_smul_one W x, Hom.app_smul, Hom.zero_app]
    change ofUnitSection W x • sVal t W = 0
    rw [← map_sVal t (homOfLE hle), h, map_zero, smul_zero]

lemma coeff_eq_zero_iff (t : 𝟙_ X.Modules ⟶ N) (U : X.Opens)
    (τ : N.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff t U τ.hom = 0 ↔ restrictSection t U = 0 := by
  constructor
  · intro h
    have hr : τ.inv.app ⊤ (τ.hom.app ⊤ (restrictSection t U)) = restrictSection t U := by
      change ((τ.hom ≫ τ.inv).app ⊤) (restrictSection t U) = _
      rw [Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
      rfl
    have h0 : τ.hom.app ⊤ (restrictSection t U) = 0 := by
      have hinj := (ConcreteCategory.bijective_of_isIso (C := CommRingCat) U.topIso.hom).1
      have h' : U.topIso.hom (ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection t U))) =
          U.topIso.hom 0 := by
        rw [map_zero]; exact h
      exact hinj h'
    rw [← hr, h0, map_zero]
  · intro h
    change U.topIso.hom (ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection t U))) = 0
    rw [h, map_zero]
    exact map_zero _

variable {k : Type u} [Field k]

lemma closedPoint_mem_zeroLocus_span_singleton_iff (c : Γ(Spec (CommRingCat.of k), ⊤)) :
    IsLocalRing.closedPoint k ∈ (Spec (CommRingCat.of k)).zeroLocus (U := ⊤)
        ((Ideal.span {c} : Ideal Γ(Spec (CommRingCat.of k), ⊤)) : Set Γ(Spec (CommRingCat.of k),
            ⊤)) ↔
      c = 0 := by
  rw [Scheme.zeroLocus_span, Spec_zeroLocus]
  change IsLocalRing.closedPoint k ∈ PrimeSpectrum.zeroLocus _ ↔ _
  rw [PrimeSpectrum.mem_zeroLocus]
  change _ ⊆ ((IsLocalRing.maximalIdeal k : Ideal k) : Set k) ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  constructor
  · intro h
    have hm : (Scheme.ΓSpecIso (CommRingCat.of k)).hom c ∈
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv ⁻¹' ({c} : Set _) := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact CategoryTheory.Iso.hom_inv_id_apply _ c
    have h0 : (Scheme.ΓSpecIso (CommRingCat.of k)).hom c = 0 := (Ideal.mem_bot).mp (h hm)
    rw [← CategoryTheory.Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) c, h0, map_zero]
  · rintro rfl y hy
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    change y ∈ (⊥ : Ideal k)
    rw [Ideal.mem_bot, ← CategoryTheory.Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of
        k)) y, hy, map_zero]

lemma eq_zero_iff_closedPoint_mem_support {N : (Spec (CommRingCat.of k)).Modules}
    (hN : Scheme.Modules.IsInvertible N) (t : 𝟙_ _ ⟶ N) :
    t = 0 ↔ IsLocalRing.closedPoint k ∈ (zeroSchemeIdeal t).support := by
  obtain ⟨U, hxU, -, ⟨τ⟩⟩ := hN.exists_restrict_iso (V := ⊤) (x := IsLocalRing.closedPoint k)
      trivial
  have hU : U = ⟨⊤, isAffineOpen_top _⟩ :=
    Subtype.ext (eq_top_iff.mpr fun x _ => by
      obtain rfl := Subsingleton.elim x (IsLocalRing.closedPoint k); exact hxU)
  subst hU
  erw [Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := zeroSchemeIdeal t) (x := (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))) hxU,
    ((hN.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq t).2 _ τ).1]
  change t = 0 ↔ IsLocalRing.closedPoint k ∈ (Spec (CommRingCat.of k)).zeroLocus (U := ⊤)
    ((Ideal.span {coeff t ⊤ τ.hom} : Ideal Γ(Spec (CommRingCat.of k), ⊤)) : Set Γ(Spec
        (CommRingCat.of k), ⊤))
  rw [closedPoint_mem_zeroLocus_span_singleton_iff, coeff_eq_zero_iff,
    eq_zero_iff_sVal_eq_zero t ((⊤ : (Spec (CommRingCat.of k)).Opens).ι ''ᵁ ⊤)
        (Scheme.Opens.ι_image_top _)]
  exact Iff.rfl

theorem pullbackSection_eq_zero_iff_mem_support {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (z : Spec (CommRingCat.of k) ⟶ X) :
    pullbackSection z s = 0 ↔
      z.base (IsLocalRing.closedPoint k) ∈ (zeroSchemeIdeal s).support := by
  have hmem : z.base (IsLocalRing.closedPoint k) ∈ (zeroSchemeIdeal s).support ↔
      IsLocalRing.closedPoint k ∈ ((zeroSchemeIdeal s).comap z).support := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  rw [hmem, hM.comap_zeroSchemeIdeal z s]
  exact eq_zero_iff_closedPoint_mem_support (hM.pullback z) (pullbackSection z s)

end PointVanishing

end AlgebraicGeometry.Scheme.Modules

end

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support
    {k : Type u} [Field k] {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (z : Spec (CommRingCat.of k) ⟶ X) :
    Scheme.Modules.pullbackSection z s = 0 ↔
      z.base (IsLocalRing.closedPoint k) ∈ (Scheme.Modules.zeroSchemeIdeal s).support :=
  AlgebraicGeometry.Scheme.Modules.PointVanishing.pullbackSection_eq_zero_iff_mem_support hM s z
end Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
