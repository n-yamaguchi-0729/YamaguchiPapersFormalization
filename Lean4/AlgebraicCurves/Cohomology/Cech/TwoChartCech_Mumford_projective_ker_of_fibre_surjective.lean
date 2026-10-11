/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_Mumford_projective_ker_of_fibre_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Cech.TwoChartCech
import Mathlib.RingTheory.Finiteness.Nakayama
import AlgebraicCurves.Geometry.Schemes.MumfordTruncation
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_projective_K0
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_bijective_kerMapBaseChange
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_bijective_cokerMapBaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
Projectivity and base change of a Cech kernel from surjectivity of the fibre kernel comparisons.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace TwoChartCech_Mumford_projective_ker_of_fibre_surjective

universe u v

open scoped TensorProduct

noncomputable section

section

open scoped TensorProduct

namespace TwoChartCech
open _root_.TwoChartCech
namespace Mumford
open _root_.TwoChartCech.Mumford
namespace FibreSurj
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech

variable {A : Type u} [CommRing A]

theorem subsingleton_of_forall_maximal_smul_top {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M]
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪 • (⊤ : Submodule A M) = ⊤) : Subsingleton M := by
  by_contra hM
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
  have hann : Module.annihilator A M ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have h1 : (1 : A) ∈ Module.annihilator A M := htop ▸ Submodule.mem_top
    exact hx ((one_smul A x).symm.trans (Module.mem_annihilator.mp h1 x))
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hann
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪
    (⊤ : Submodule A M) Module.Finite.fg_top (by rw [h 𝔪 h𝔪])
  have hrann : r ∈ Module.annihilator A M :=
    Module.mem_annihilator.mpr fun x => hr x Submodule.mem_top
  have h1 : (1 : A) ∈ 𝔪 := by
    have : (1 : A) = r - (r - 1) := by ring
    rw [this]; exact 𝔪.sub_mem (hle hrann) hr1
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

variable {C0 C1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
variable (d : C0 →ₗ[A] C1) [Module.Finite A (C1 ⧸ LinearMap.range d)]

theorem dK_surjective
    (hH1 : ∀ (K : Type u) [Field K] [Algebra A K], Function.Surjective (d.baseChange K)) :
    Function.Surjective (Mumford.dK d) := by
  let Q := (Fin (rank d) → A) ⧸ LinearMap.range (dK d)
  suffices hQ : Subsingleton Q by
    rw [← LinearMap.range_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mp hQ
  have : Module.Finite A Q := inferInstance
  refine subsingleton_of_forall_maximal_smul_top (A := A) fun 𝔪 h𝔪 => ?_
  have := h𝔪
  let : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hsurjK : Function.Surjective ((dK d).baseChange (A ⧸ 𝔪)) := by
    have : Subsingleton (((A ⧸ 𝔪) ⊗[A] C1) ⧸ LinearMap.range (d.baseChange (A ⧸ 𝔪))) :=
      Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr (hH1 _))
    have hsub : Subsingleton (((A ⧸ 𝔪) ⊗[A] (Fin (rank d) → A)) ⧸ LinearMap.range ((dK
      d).baseChange (A ⧸ 𝔪))) :=
      (bijective_cokerMapBaseChange d (A ⧸ 𝔪)).1.subsingleton
    exact LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp hsub)
  have hQ0 : ∀ z : (A ⧸ 𝔪) ⊗[A] Q, z = 0 := by
    intro z
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (A ⧸ 𝔪)
      (Submodule.mkQ_surjective (LinearMap.range (dK d))) z
    have hex := lTensor_exact (A ⧸ 𝔪) (LinearMap.exact_map_mkQ_range (dK d))
      (Submodule.mkQ_surjective _)
    refine (hex y).mpr ?_
    obtain ⟨x, hx⟩ := hsurjK y
    exact ⟨x, by rw [← hx, LinearMap.baseChange_eq_ltensor]⟩
  have : Subsingleton ((A ⧸ 𝔪) ⊗[A] Q) := ⟨fun a b => by rw [hQ0 a, hQ0 b]⟩
  have : Subsingleton (Q ⧸ 𝔪 • (⊤ : Submodule A Q)) :=
    (TensorProduct.quotTensorEquivQuotSMul Q 𝔪).symm.toEquiv.subsingleton
  exact Submodule.Quotient.subsingleton_iff.mp ‹_›

theorem kerMap_bijective :
    Function.Bijective (kerMap (dK d) d (ι0 d) (ι1 d) (comm d)) := by
  constructor
  · rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩ ⟨⟨⟨x', v'⟩, hxv'⟩, hv'⟩ h
    have hv0 : v = 0 := LinearMap.mem_ker.mp hv
    have hv0' : v' = 0 := LinearMap.mem_ker.mp hv'
    have hx : x = x' := congrArg Subtype.val h
    subst hv0; subst hv0'; subst hx
    rfl
  · rintro ⟨x, hx⟩
    refine ⟨⟨⟨(x, 0), (mem_K0_iff d _).mpr (by rw [LinearMap.mem_ker.mp hx, map_zero, add_zero])⟩,
      LinearMap.mem_ker.mpr rfl⟩, rfl⟩

/-- The kernel equivalence induced by projecting the enlarged source onto the original source. -/
def kerMapEquiv : LinearMap.ker (dK d) ≃ₗ[A] LinearMap.ker d :=
  LinearEquiv.ofBijective _ (kerMap_bijective d)

theorem subtype_comp_kerMap :
    (LinearMap.ker d).subtype ∘ₗ kerMap (dK d) d (ι0 d) (ι1 d) (comm d)
      = ι0 d ∘ₗ (LinearMap.ker (dK d)).subtype :=
  LinearMap.ext fun _ => rfl

end TwoChartCech.Mumford.FibreSurj

end

end

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.TwoChartCech TwoChartCech_Mumford_projective_ker_of_fibre_surjective.TwoChartCech
  _root_.TwoChartCech.Mumford
  TwoChartCech_Mumford_projective_ker_of_fibre_surjective.TwoChartCech.Mumford in
theorem _root_.TwoChartCech.Mumford.projective_ker_of_fibre_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {C0 C1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
    [Module.Flat A C0] [Module.Flat A C1] (d : C0 →ₗ[A] C1)
    [Module.Finite A (LinearMap.ker d)] [Module.Finite A (C1 ⧸ LinearMap.range d)]
    (hH1 : ∀ (K : Type u) [Field K] [Algebra A K], Function.Surjective (d.baseChange K)) :
    Module.Projective A (LinearMap.ker d) ∧
      (∀ (A' : Type u) [CommRing A'] [Algebra A A'], Function.Bijective
        (TwoChartCech.kerBaseChangeHom d A')) ∧
      ∀ (K : Type u) [Field K] [Algebra A K],
        Module.finrank K (K ⊗[A] LinearMap.ker d) = Module.finrank K (LinearMap.ker (d.baseChange
          K)) := by
  have hsurj : Function.Surjective (dK d) := FibreSurj.dK_surjective d hH1
  have : Module.Projective A (K0 d) := projective_K0 d
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (dK d) (LinearMap.id) hsurj
  let rK : K0 d →ₗ[A] LinearMap.ker (dK d) :=
    (LinearMap.id - s ∘ₗ dK d).codRestrict (LinearMap.ker (dK d)) fun z => LinearMap.mem_ker.mpr
      <| by
      rw [LinearMap.sub_apply, map_sub, LinearMap.comp_apply, ← LinearMap.comp_apply (dK d) s, hs,
        LinearMap.id_apply, LinearMap.id_apply, sub_self]
  have hrK : rK ∘ₗ (LinearMap.ker (dK d)).subtype = LinearMap.id := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    change z.1 - s (dK d z.1) = z.1
    rw [LinearMap.mem_ker.mp z.2, map_zero, sub_zero]
  have hsplit : (LinearMap.ker (dK d)).subtype ∘ₗ rK = LinearMap.id - s ∘ₗ dK d :=
    LinearMap.ext fun _ => rfl
  have hprojK : Module.Projective A (LinearMap.ker (dK d)) :=
    Module.Projective.of_split (LinearMap.ker (dK d)).subtype rK hrK
  have hproj : Module.Projective A (LinearMap.ker d) :=
    haveI := hprojK; Module.Projective.of_equiv (FibreSurj.kerMapEquiv d)
  have hbcK : ∀ (A' : Type u) [CommRing A'] [Algebra A A'],
      Function.Bijective (TwoChartCech.kerBaseChangeHom (dK d) A') := by
    intro A' _ _
    have key : ∀ w : A' ⊗[A] LinearMap.ker (dK d),
        (rK.baseChange A') ((LinearMap.ker (dK d)).subtype.baseChange A' w) = w := fun w => by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hrK, LinearMap.baseChange_id,
        LinearMap.id_apply]
    constructor
    · intro x y hxy
      have h' : ((LinearMap.ker (dK d)).subtype.baseChange A') x
          = ((LinearMap.ker (dK d)).subtype.baseChange A') y := congrArg Subtype.val hxy
      exact (key x).symm.trans ((congrArg (rK.baseChange A') h').trans (key y))
    · rintro ⟨z, hz⟩
      refine ⟨rK.baseChange A' z, Subtype.ext ?_⟩
      rw [TwoChartCech.kerBaseChangeHom_apply_coe, ← LinearMap.comp_apply, ←
        LinearMap.baseChange_comp, hsplit,
        LinearMap.baseChange_sub, LinearMap.sub_apply, LinearMap.baseChange_id, LinearMap.id_apply,
        LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.mem_ker.mp hz, map_zero,
          sub_zero]
  have hbc : ∀ (A' : Type u) [CommRing A'] [Algebra A A'],
      Function.Bijective (TwoChartCech.kerBaseChangeHom d A') := by
    intro A' _ _
    let e := FibreSurj.kerMapEquiv d
    have hsq : ⇑(TwoChartCech.kerBaseChangeHom d A') ∘ ⇑(e.toLinearMap.baseChange A')
        = ⇑(kerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A') ∘
          ⇑(TwoChartCech.kerBaseChangeHom (dK d) A') := by
      funext x
      apply Subtype.ext
      change ((LinearMap.ker d).subtype.baseChange A')
          ((kerMap (dK d) d (ι0 d) (ι1 d) (comm d)).baseChange A' x)
        = ((ι0 d).baseChange A') (((LinearMap.ker (dK d)).subtype.baseChange A') x)
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, FibreSurj.subtype_comp_kerMap,
        LinearMap.baseChange_comp, LinearMap.comp_apply]
    have h1 : (e.symm.toLinearMap.baseChange A') ∘ₗ (e.toLinearMap.baseChange A') = LinearMap.id
      := by
      rw [← LinearMap.baseChange_comp,
        show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from LinearMap.ext
          e.symm_apply_apply,
        LinearMap.baseChange_id]
    have h2 : (e.toLinearMap.baseChange A') ∘ₗ (e.symm.toLinearMap.baseChange A') = LinearMap.id
      := by
      rw [← LinearMap.baseChange_comp,
        show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from LinearMap.ext
          e.apply_symm_apply,
        LinearMap.baseChange_id]
    have he : Function.Bijective ⇑(e.toLinearMap.baseChange A') :=
      (LinearEquiv.ofLinearMap (e.toLinearMap.baseChange A') (e.symm.toLinearMap.baseChange A') h2
        h1 :
        A' ⊗[A] LinearMap.ker (dK d) ≃ₗ[A'] A' ⊗[A] LinearMap.ker d).bijective
    have hcomp : Function.Bijective (⇑(TwoChartCech.kerBaseChangeHom d A') ∘
      ⇑(e.toLinearMap.baseChange A')) := by
      rw [hsq]
      exact (bijective_kerMapBaseChange d A').comp (hbcK A')
    exact (Function.Bijective.of_comp_iff _ he).mp hcomp
  exact ⟨hproj, hbc, fun K _ _ => (LinearEquiv.ofBijective _ (hbc K)).finrank_eq⟩
end TwoChartCech_Mumford_projective_ker_of_fibre_surjective
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation

attribute [-simp] TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
