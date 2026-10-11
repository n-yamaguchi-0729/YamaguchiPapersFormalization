/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_natCard_stabilizer_pointEquivPlace_mul_natCard_ker_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Models.CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul

/-!
# Curve Model nat Card stabilizer point Equiv Place mul nat Card ker eq
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_natCard_stabilizer_pointEquivPlace_mul_natCard_ker_eq

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

namespace STABAuxFFX

theorem semilinearAut_ext {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (g g' : SemilinearAut K L) (h1 : ∀ z : L, g • z = g' • z)
    (h2 : SemilinearAut.baseAut g = SemilinearAut.baseAut g') : g = g' := by
  apply Subtype.ext
  apply Prod.ext
  · ext z
    exact h1 z
  · exact h2

theorem exists_germ {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (z : L) :
    ∃ (U : M.C.Opens) (_ : Nonempty (Scheme.Opens.toScheme U)) (f : Γ(M.C, U)),
      z = M.ffEquiv.symm (M.C.germToFunctionField U f) := by
  obtain ⟨U, hU, f, hf⟩ := TopCat.Presheaf.exists_germ_eq M.C.presheaf (M.ffEquiv z)
  have : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨genericPoint M.C, hU⟩⟩
  refine ⟨U, this, f, ?_⟩
  apply M.ffEquiv.injective
  rw [RingEquiv.apply_symm_apply]
  exact hf.symm

end STABAuxFFX

theorem _root_.AlgebraicCurve.CurveModel.natCard_stabilizer_pointEquivPlace_mul_natCard_ker_eq
    {k : Type u} [Field k] [IsAlgClosed k] {L : Type v} [Field L] [Algebra k L]
    (M : CurveModel k L)
    (F : Type v) [Field F] [Algebra k F] [Algebra F L] [IsScalarTower k F L] [FiniteDimensional F L]
    (G₀ : Type u) [Group G₀] [Finite G₀] (ρ : G₀ →* Aut M.C) (hρ : ∀ g : G₀, (ρ g).hom ≫ M.toBase =
      M.toBase)
    (θ : G₀ →* (L ≃ₐ[F] L)) (hθsurj : Function.Surjective θ)
    (hθ : ∀ (g : G₀) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((ρ g).inv ⁻¹ᵁ U))] (f : Γ(M.C, U)),
        θ g (M.ffEquiv.symm (M.C.germToFunctionField U f)) =
          M.ffEquiv.symm (M.C.germToFunctionField ((ρ g).inv ⁻¹ᵁ U) ((ρ g).inv.app U f)))
    (hθker : ∀ g : G₀, θ g = 1 ↔ ρ g = 1)
    (x : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    Nat.card {σ : L ≃ₐ[F] L // SemilinearAut.ofAlgAut (σ.restrictScalars k) • M.pointEquivPlace x =
      M.pointEquivPlace x} *
        Nat.card θ.ker =
      Nat.card {g : G₀ // x.1 ≫ (ρ g).hom = x.1} := by
  have key : ∀ g : G₀,
      SemilinearAut.ofAlgAut ((θ g).restrictScalars k) • M.pointEquivPlace x = M.pointEquivPlace x ↔
        x.1 ≫ (ρ g).hom = x.1 := by
    intro g
    have : IsIso (ρ g).inv := (show M.C ≅ M.C from ρ g).isIso_inv
    have hh : (ρ g).inv ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom ((1 : k ≃+* k) : k →+*
      k)) := by
      have h1 : Spec.map (CommRingCat.ofHom ((1 : k ≃+* k) : k →+* k)) = 𝟙 _ := by
        change Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
        rw [CommRingCat.ofHom_id]
        exact Spec.map_id _
      rw [h1, Category.comp_id]
      calc (ρ g).inv ≫ M.toBase = (ρ g).inv ≫ ((ρ g).hom ≫ M.toBase) := by rw [hρ g]
        _ = M.toBase := by exact (show M.C ≅ M.C from ρ g).inv_hom_id_assoc M.toBase
    obtain ⟨s, hs1, hs2, hs3⟩ :=
      AlgebraicCurve.CurveModel.exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul M 1 (ρ
        g).inv hh
    have hs : s = SemilinearAut.ofAlgAut ((θ g).restrictScalars k) := by
      apply STABAuxFFX.semilinearAut_ext
      · intro z
        obtain ⟨U, hU, f, rfl⟩ := STABAuxFFX.exists_germ M z
        have : Nonempty (Scheme.Opens.toScheme ((ρ g).inv ⁻¹ᵁ U)) := by
          refine ⟨⟨genericPoint M.C, ?_⟩⟩
          change (ρ g).inv.base (genericPoint M.C) ∈ U
          rw [genericPoint_eq_of_isOpenImmersion (ρ g).inv]
          exact ((genericPoint_spec M.C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
        rw [hs2 U f, SemilinearAut.ofAlgAut_smul]
        exact (hθ g U f).symm
      · rw [hs1, SemilinearAut.baseAut_ofAlgAut]
    let y : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
      ⟨x.1 ≫ (ρ g).hom, by rw [Category.assoc, hρ g]; exact x.2⟩
    have hy : y.1 ≫ (ρ g).inv = Spec.map (CommRingCat.ofHom ((1 : k ≃+* k) : k →+* k)) ≫ x.1 := by
      have h1 : Spec.map (CommRingCat.ofHom ((1 : k ≃+* k) : k →+* k)) = 𝟙 _ := by
        change Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
        rw [CommRingCat.ofHom_id]
        exact Spec.map_id _
      rw [h1, Category.id_comp]
      change (x.1 ≫ (ρ g).hom) ≫ (ρ g).inv = x.1
      erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hpl : M.pointEquivPlace y = s • M.pointEquivPlace x := hs3 x y hy
    rw [← hs, ← hpl]
    constructor
    · intro h
      have : y = x := M.pointEquivPlace.injective h
      exact congrArg Subtype.val this
    · intro h
      have : y = x := Subtype.ext h
      rw [this]
  let S : Subgroup G₀ :=
    { carrier := {g | x.1 ≫ (ρ g).hom = x.1}
      one_mem' := by
        change x.1 ≫ (ρ 1).hom = x.1
        rw [map_one]; exact Category.comp_id _
      mul_mem' := fun {a b} ha hb => by
        change x.1 ≫ (ρ (a * b)).hom = x.1
        erw [map_mul, Aut.Aut_mul_def, Iso.trans_hom, ← Category.assoc]
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        change x.1 ≫ (ρ a⁻¹).hom = x.1
        rw [map_inv, Aut.Aut_inv_def]
        change x.1 ≫ (ρ a).inv = x.1
        conv_lhs => rw [← ha]
        erw [Category.assoc, Iso.hom_inv_id, Category.comp_id] }
  have hSmem : ∀ g : G₀, g ∈ S ↔ x.1 ≫ (ρ g).hom = x.1 := fun g => Iff.rfl
  have hkerS : θ.ker ≤ S := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [hSmem, (hθker g).mp hg]
    exact Category.comp_id _
  let φ : S →* (L ≃ₐ[F] L) := θ.comp S.subtype
  have hkercard : Nat.card φ.ker = Nat.card θ.ker := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun g => ⟨g.1.1, by
          have := g.2; rw [MonoidHom.mem_ker] at this ⊢; exact this⟩
        invFun := fun g => ⟨⟨g.1, hkerS g.2⟩, by
          have := g.2; rw [MonoidHom.mem_ker] at this ⊢; exact this⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  have hrangecard : Nat.card (Set.range φ) =
      Nat.card {σ : L ≃ₐ[F] L //
        SemilinearAut.ofAlgAut (σ.restrictScalars k) • M.pointEquivPlace x = M.pointEquivPlace x}
          := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro σ
    constructor
    · rintro ⟨g, rfl⟩
      change SemilinearAut.ofAlgAut ((θ g.1).restrictScalars k) • M.pointEquivPlace x =
        M.pointEquivPlace x
      rw [key]
      exact g.2
    · intro hσ
      obtain ⟨g, rfl⟩ := hθsurj σ
      exact ⟨⟨g, (hSmem g).mpr ((key g).mp hσ)⟩, rfl⟩
  have hidx : φ.ker.index = Nat.card (Set.range φ) := Subgroup.index_ker φ
  have hmul : Nat.card φ.ker * φ.ker.index = Nat.card S := Subgroup.card_mul_index φ.ker
  have hS : Nat.card S = Nat.card {g : G₀ // x.1 ≫ (ρ g).hom = x.1} := rfl
  rw [← hS, ← hmul, hidx, hkercard, hrangecard, Nat.mul_comm]

end AlgebraicCurves.Models.Proofs.CurveModel_natCard_stabilizer_pointEquivPlace_mul_natCard_ker_eq
end ProofImplementation
