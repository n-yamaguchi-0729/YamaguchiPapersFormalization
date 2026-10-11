/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Place exists equiv comap eq and ord eq and deg eq of ring Equiv
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv

open AlgebraicCurve

noncomputable section

namespace PlaceTransport

variable {K K' F F' : Type} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F']

theorem symm_algebraMap (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) =
  algebraMap K' F' (e a))
    (a' : K') : φ.symm (algebraMap K' F' a') = algebraMap K F (e.symm a') := by
  apply φ.injective
  rw [RingEquiv.apply_symm_apply, hφ, RingEquiv.apply_symm_apply]

/-- The ring equivalence transporting a valuation ring along a field isomorphism. -/
def integersEquiv (φ : F ≃+* F') (A : ValuationSubring F) :
    A ≃+* (A.comap φ.symm.toRingHom : ValuationSubring F') where
  toFun x := ⟨φ x, by
    change φ.symm.toRingHom (φ x) ∈ A
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    exact x.2⟩
  invFun y := ⟨φ.symm y, y.2⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x)
  right_inv y := Subtype.ext (φ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul φ _ _)
  map_add' x y := Subtype.ext (map_add φ _ _)

@[scoped simp] theorem coe_integersEquiv_apply (φ : F ≃+* F') (A : ValuationSubring F) (x : A) :
    ((integersEquiv φ A x : (A.comap φ.symm.toRingHom : ValuationSubring F')) : F') = φ x := rfl

private def _root_.PlaceTransport.map (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K
  F a) = algebraMap K' F' (e a))
    (v : Place K F) : Place K' F' where
  toValuationSubring := v.toValuationSubring.comap φ.symm.toRingHom
  algebraMap_mem' a' := by
    change φ.symm.toRingHom (algebraMap K' F' a') ∈ v.toValuationSubring
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, symm_algebraMap e φ hφ]
    exact v.algebraMap_mem' _
  ne_top' h := v.ne_top' (by
    rw [eq_top_iff]
    intro f _
    have hf : φ f ∈ (v.toValuationSubring.comap φ.symm.toRingHom : ValuationSubring F') := by
      rw [h]; exact ValuationSubring.mem_top _
    have hf' : φ.symm.toRingHom (φ f) ∈ v.toValuationSubring := hf
    rwa [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at hf')
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective (integersEquiv φ v.toValuationSubring : _ ≃+* _)
      (integersEquiv φ v.toValuationSubring).surjective

open _root_.PlaceTransport
@[scoped simp] theorem map_toValuationSubring (e : K ≃+* K') (φ : F ≃+* F')
    (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (e a)) (v : Place K F) :
    (map e φ hφ v).toValuationSubring = v.toValuationSubring.comap φ.symm.toRingHom := rfl

theorem mem_map_iff (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap
  K' F' (e a))
    (v : Place K F) (f' : F') : f' ∈ (map e φ hφ v).toValuationSubring ↔ φ.symm f' ∈
      v.toValuationSubring :=
  Iff.rfl

/-- The equivalence of places induced by compatible isomorphisms of the base and function
fields. -/
def equiv (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (e
  a)) :
    Place K F ≃ Place K' F' where
  toFun := map e φ hφ
  invFun := map e.symm φ.symm (symm_algebraMap e φ hφ)
  left_inv v := by
    apply Place.ext
    ext f
    change φ.symm.symm.toRingHom f ∈ (map e φ hφ v).toValuationSubring ↔ f ∈ v.toValuationSubring
    rw [mem_map_iff]
    simp
  right_inv w := by
    apply Place.ext
    ext f'
    change φ.symm.toRingHom f' ∈ (map e.symm φ.symm (symm_algebraMap e φ hφ) w).toValuationSubring ↔
      f' ∈ w.toValuationSubring
    rw [mem_map_iff]
    simp

theorem ord_map (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K'
  F' (e a))
    (v : Place K F) (f : F) : (map e φ hφ v).ord (φ f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, Place.ord_zero, Place.ord_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  set n := v.ord f with hn
  set E := integersEquiv φ v.toValuationSubring with hE
  have hπ' : Irreducible (E π) := (MulEquiv.irreducible_iff E).mpr hπ
  have hu' : IsUnit (E (u : v.toValuationSubring)) := u.isUnit.map E
  have hcoeu : ((hu'.unit.val : (v.toValuationSubring.comap φ.symm.toRingHom : ValuationSubring
    F')) : F') =
      φ ((u : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((E π : (map e φ hφ v).toValuationSubring) : F') = φ (π : F) := rfl
  have key : φ f = ((hu'.unit.val : (v.toValuationSubring.comap φ.symm.toRingHom : ValuationSubring
    F')) : F')
      * (((E π : (map e φ hφ v).toValuationSubring) : F') ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [key, (map e φ hφ v).ord_unit_smul_zpow hu'.unit hπ' n]

theorem deg_map (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K'
  F' (e a))
    (v : Place K F) : (map e φ hφ v).deg = v.deg := by
  let E := integersEquiv φ v.toValuationSubring
  let j : v.ResidueField ≃+* (map e φ hφ v).ResidueField := IsLocalRing.ResidueField.mapEquiv E
  have hj : ∀ (r : K) (m : v.ResidueField), j (r • m) = e r • j m := by
    intro r m
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
      IsScalarTower.algebraMap_apply K' (map e φ hφ v).toValuationSubring (map e φ hφ
        v).ResidueField]
    change IsLocalRing.ResidueField.mapEquiv E (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change φ ((algebraMap K v.toValuationSubring r : v.toValuationSubring) : F) =
      ((algebraMap K' (map e φ hφ v).toValuationSubring (e r) : (map e φ hφ v).toValuationSubring)
        : F')
    rw [Place.coe_algebraMap, Place.coe_algebraMap, hφ]
  have h := lift_rank_eq_of_equiv_equiv (e : K → K') j.toAddEquiv e.bijective hj
  simp only [Cardinal.lift_id] at h
  unfold Place.deg Module.finrank
  rw [h]

end PlaceTransport

end

theorem _root_.AlgebraicCurve.Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
    {K K' F F' : Type} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F']
    (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (e a)) :
    ∃ Φ : Place K F ≃ Place K' F',
      (∀ v : Place K F, (Φ v).toValuationSubring = v.toValuationSubring.comap φ.symm.toRingHom) ∧
      (∀ (v : Place K F) (f : F), (Φ v).ord (φ f) = v.ord f) ∧
      (∀ v : Place K F, (Φ v).deg = v.deg) :=
  ⟨PlaceTransport.equiv e φ hφ, fun _ => rfl, fun v f => PlaceTransport.ord_map e φ hφ v f,
    fun v => PlaceTransport.deg_map e φ hφ v⟩
end AlgebraicCurves.Places.Proofs.Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
end ProofImplementation
