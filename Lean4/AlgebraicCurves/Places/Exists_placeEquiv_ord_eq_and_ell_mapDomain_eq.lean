/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Index

/-!
# Exists placeEquiv ord eq and ell mapDomain eq

A base-field algebra equivalence transports places, preserves orders and residue degrees, and
identifies the corresponding Riemann spaces.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Exists_placeEquiv_ord_eq_and_ell_mapDomain_eq

universe u v w

noncomputable section

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace PlaceTransportGlue
open _root_.AlgebraicCurve

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F']
  [Algebra K F']


/-- The valuation subring transported by comap along the inverse algebra equivalence. -/
abbrev vsMap (σ : F ≃ₐ[K] F') (A : ValuationSubring F) : ValuationSubring F' :=
  A.comap (σ.symm : F' ≃ₐ[K] F).toAlgHom.toRingHom

theorem mem_vsMap_iff (σ : F ≃ₐ[K] F') (A : ValuationSubring F) (y : F') :
    y ∈ vsMap σ A ↔ σ.symm y ∈ A := Iff.rfl


/-- The ring equivalence from the original valuation subring to its transported valuation
subring. -/
def vsEquiv (σ : F ≃ₐ[K] F') (A : ValuationSubring F) : A ≃+* vsMap σ A where
  toFun x := ⟨σ x, by rw [mem_vsMap_iff, AlgEquiv.symm_apply_apply]; exact x.2⟩
  invFun y := ⟨σ.symm y, y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp] theorem coe_vsEquiv_apply (σ : F ≃ₐ[K] F') (A : ValuationSubring F) (x : A) :
    ((vsEquiv σ A x : vsMap σ A) : F') = σ x := rfl


/-- The place transported along the compatible base-field algebra equivalence. -/
def placeMap (σ : F ≃ₐ[K] F') (v : Place K F) : Place K F' where
  toValuationSubring := vsMap σ v.toValuationSubring
  algebraMap_mem' a := by
    rw [mem_vsMap_iff, AlgEquiv.commutes]
    exact v.algebraMap_mem' a
  ne_top' h := v.ne_top' <| by
    refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
    have hx : σ x ∈ vsMap σ v.toValuationSubring := h ▸ ValuationSubring.mem_top (σ x)
    rwa [mem_vsMap_iff, AlgEquiv.symm_apply_apply] at hx
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective (vsEquiv σ v.toValuationSubring : _ ≃+* _)
      (vsEquiv σ v.toValuationSubring).surjective

@[scoped simp] theorem placeMap_toValuationSubring (σ : F ≃ₐ[K] F') (v : Place K F) :
    (placeMap σ v).toValuationSubring = vsMap σ v.toValuationSubring := rfl

theorem mem_placeMap_iff (σ : F ≃ₐ[K] F') (v : Place K F) (y : F') :
    y ∈ (placeMap σ v).toValuationSubring ↔ σ.symm y ∈ v.toValuationSubring := Iff.rfl

theorem placeMap_symm_placeMap (σ : F ≃ₐ[K] F') (v : Place K F) : placeMap σ.symm
  (placeMap σ v) = v := by
  ext x
  rw [mem_placeMap_iff, mem_placeMap_iff, AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply]


/-- The equivalence between place sets induced by the base-field algebra equivalence. -/
def placeEquiv (σ : F ≃ₐ[K] F') : Place K F ≃ Place K F' where
  toFun := placeMap σ
  invFun := placeMap σ.symm
  left_inv v := placeMap_symm_placeMap σ v
  right_inv w := by simpa using placeMap_symm_placeMap σ.symm w

@[scoped simp] theorem placeEquiv_apply (σ : F ≃ₐ[K] F') (v : Place K F) : placeEquiv σ v =
  placeMap σ v := rfl
@[scoped simp] theorem placeEquiv_symm_apply (σ : F ≃ₐ[K] F') (w : Place K F') :
    (placeEquiv σ).symm w = placeMap σ.symm w := rfl

theorem coe_placeMap (σ : F ≃ₐ[K] F') (v : Place K F) :
    ((placeMap σ v).toValuationSubring : Set F') = σ '' (v.toValuationSubring : Set F) := by
  ext y
  simp only [SetLike.mem_coe, mem_placeMap_iff, Set.mem_image]
  constructor
  · intro hy; exact ⟨σ.symm y, hy, σ.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩; rwa [AlgEquiv.symm_apply_apply]


theorem ord_placeMap (σ : F ≃ₐ[K] F') (v : Place K F) (f : F) : (placeMap σ v).ord (σ f) =
  v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  set n := v.ord f with hn
  let e : v.toValuationSubring ≃+* (placeMap σ v).toValuationSubring :=
    vsEquiv σ v.toValuationSubring
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (placeMap σ v).toValuationSubring) : F') = σ ((u :
    v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((e π : (placeMap σ v).toValuationSubring) : F') = σ (π : F) := rfl
  have key : σ f = ((hu'.unit : (placeMap σ v).toValuationSubring) : F')
      * (((e π : (placeMap σ v).toValuationSubring) : F') ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [key, (placeMap σ v).ord_unit_smul_zpow hu'.unit hπ' n]


/-- The induced base-field algebra equivalence between the two residue fields. -/
def residueAlgEquiv (σ : F ≃ₐ[K] F') (v : Place K F) : v.ResidueField ≃ₐ[K]
  (placeMap σ v).ResidueField := by
  letI : Algebra K (vsMap σ v.toValuationSubring) := by
    change Algebra K (placeMap σ v).toValuationSubring
    infer_instance
  letI : Algebra K (IsLocalRing.ResidueField (vsMap σ v.toValuationSubring)) := by
    change Algebra K (placeMap σ v).ResidueField
    infer_instance
  letI : IsLocalHom (vsEquiv σ v.toValuationSubring).toRingHom :=
    IsLocalHom.of_surjective _ (vsEquiv σ v.toValuationSubring).surjective
  change v.ResidueField ≃ₐ[K] IsLocalRing.ResidueField (vsMap σ v.toValuationSubring)
  refine AlgEquiv.ofRingEquiv
    (f := IsLocalRing.ResidueField.mapEquiv (vsEquiv σ v.toValuationSubring)) fun a => ?_
  · have h3 : (vsEquiv σ v.toValuationSubring) (algebraMap K v.toValuationSubring a)
        = algebraMap K (vsMap σ v.toValuationSubring) a := by
      ext
      rw [coe_vsEquiv_apply, Place.coe_algebraMap, AlgEquiv.commutes]
      rfl
    change IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    change IsLocalRing.ResidueField.map (vsEquiv σ v.toValuationSubring).toRingHom
        (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.map_residue]
    exact congrArg _ h3

theorem deg_placeMap (σ : F ≃ₐ[K] F') (v : Place K F) : (placeMap σ v).deg = v.deg :=
  ((residueAlgEquiv σ v).toLinearEquiv.finrank_eq).symm

theorem mapDomain_placeEquiv_apply (σ : F ≃ₐ[K] F') (D : Divisor K F) (w : Place K F') :
    (Finsupp.mapDomain (placeEquiv σ) D) w = D ((placeEquiv σ).symm w) :=
  Finsupp.mapDomain_equiv_apply (f := placeEquiv σ) D w


/-- The linear equivalence of Riemann spaces induced by transport of the divisor and function. -/
def lSpaceEquiv (σ : F ≃ₐ[K] F') (D : Divisor K F) :
    LSpace D ≃ₗ[K] LSpace (Finsupp.mapDomain (placeEquiv σ) D) where
  toFun f := ⟨σ f, by
    rw [mem_riemannRochSpace_iff]
    intro w
    rcases eq_or_ne (f : F) 0 with h0 | h0
    · left; rw [h0, map_zero]
    right
    have hf := (mem_riemannRochSpace_iff.mp f.2) ((placeEquiv σ).symm w)
    rw [mapDomain_placeEquiv_apply]
    have hw : w = placeMap σ ((placeEquiv σ).symm w) := by
      rw [← placeEquiv_apply, Equiv.apply_symm_apply]
    rw [hw, ord_placeMap, ← hw]
    exact hf.resolve_left h0⟩
  invFun g := ⟨σ.symm g, by
    rw [mem_riemannRochSpace_iff]
    intro v
    rcases eq_or_ne (g : F') 0 with h0 | h0
    · left; rw [h0, map_zero]
    right
    have hg := (mem_riemannRochSpace_iff.mp g.2) (placeEquiv σ v)
    rw [mapDomain_placeEquiv_apply, Equiv.symm_apply_apply] at hg
    have h1 : (placeEquiv σ v).ord (g : F') = v.ord (σ.symm g) := by
      conv_lhs => rw [← σ.apply_symm_apply (g : F')]
      exact ord_placeMap σ v _
    rw [← h1]
    exact hg.resolve_left h0⟩
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem ell_mapDomain (σ : F ≃ₐ[K] F') (D : Divisor K F) : ell (Finsupp.mapDomain
  (placeEquiv σ) D) = ell D :=
  ((lSpaceEquiv σ D).finrank_eq).symm

theorem degree_mapDomain (σ : F ≃ₐ[K] F') (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain (placeEquiv σ) D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
        Divisor.degree_single,
        Divisor.degree_single, placeEquiv_apply, deg_placeMap]

theorem isPrincipal_mapDomain_iff (σ : F ≃ₐ[K] F') (D : Divisor K F) :
    Divisor.IsPrincipal (Finsupp.mapDomain (placeEquiv σ) D) ↔ Divisor.IsPrincipal D := by
  constructor
  · rintro ⟨g, hg, hD⟩
    refine ⟨σ.symm g, by simpa using hg, fun v => ?_⟩
    have h := hD (placeEquiv σ v)
    rw [mapDomain_placeEquiv_apply, Equiv.symm_apply_apply] at h
    rw [h, placeEquiv_apply]
    conv_lhs => rw [← σ.apply_symm_apply g]
    exact ord_placeMap σ v _
  · rintro ⟨f, hf, hD⟩
    refine ⟨σ f, by simpa using hf, fun w => ?_⟩
    rw [mapDomain_placeEquiv_apply, hD]
    have hw : w = placeMap σ ((placeEquiv σ).symm w) := by
      rw [← placeEquiv_apply, Equiv.apply_symm_apply]
    conv_rhs => rw [hw]
    exact (ord_placeMap σ _ f).symm

end AlgebraicCurve.PlaceTransportGlue

open AlgebraicCurve.PlaceTransportGlue in
theorem _root_.AlgebraicCurve.exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F']
      [Algebra K F']
    (σ : F ≃ₐ[K] F') :
    ∃ π : Place K F ≃ Place K F',
      (∀ v : Place K F, ((π v).toValuationSubring : Set F') = σ '' (v.toValuationSubring : Set F)) ∧
      (∀ (v : Place K F) (f : F), (π v).ord (σ f) = v.ord f) ∧
      (∀ v : Place K F, (π v).deg = v.deg) ∧
      (∀ D : Divisor K F, ell (Finsupp.mapDomain π D) = ell D) ∧
      (∀ D : Divisor K F, Divisor.degree (Finsupp.mapDomain π D) = Divisor.degree D) ∧
      (∀ D : Divisor K F, Divisor.IsPrincipal (Finsupp.mapDomain π D) ↔ Divisor.IsPrincipal D) :=
  ⟨placeEquiv σ, coe_placeMap σ, ord_placeMap σ, deg_placeMap σ, ell_mapDomain σ,
    degree_mapDomain σ,
    isPrincipal_mapDomain_iff σ⟩

end
end AlgebraicCurves.Places.Proofs.Exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
end ProofImplementation
