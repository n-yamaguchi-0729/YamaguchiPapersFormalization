/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_finite_integralClosure_sections_of_isIso_stalkMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Models.CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
import Nyll.AlgebraicCurves.Models.Range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Nyll.AlgebraicCurves.Models.CurveModel_isFinite_of_isIso_stalkMap

/-!
# Curve Model finite integral Closure sections of is Iso stalk Map
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_finite_integralClosure_sections_of_isIso_stalkMap
open _root_.AlgebraicCurve.CurveModel

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

noncomputable section

theorem _root_.AlgebraicCurve.CurveModel.finite_integralClosure_sections_of_isIso_stalkMap
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
      [IsIntegral C] [IsProper c]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C)))
    (U : C.Opens) (hUaff : IsAffineOpen U) [Nonempty U] :
    Module.Finite Γ(C, U) ↥(integralClosure Γ(C, U) C.functionField) := by
  have : IsFinite ν := AlgebraicCurve.CurveModel.isFinite_of_isIso_stalkMap k c M ν hν hbir
  obtain ⟨hgen, -⟩ :=
    apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
      k c M ν hν hbir
  have hηV : genericPoint M.C ∈ ν ⁻¹ᵁ U := by
    change ν.base (genericPoint M.C) ∈ U
    rw [hgen]
    exact ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hne : Nonempty (ν ⁻¹ᵁ U) := ⟨⟨genericPoint M.C, hηV⟩⟩
  let algV : Algebra Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField := (M.C.germToFunctionField (ν ⁻¹ᵁ
    U)).hom.toAlgebra
  have hVaff : IsAffineOpen (ν ⁻¹ᵁ U) := hUaff.preimage ν
  let φ : Γ(C, U) →+* Γ(M.C, ν ⁻¹ᵁ U) := (ν.app U).hom
  let algφ : Algebra Γ(C, U) Γ(M.C, ν ⁻¹ᵁ U) := φ.toAlgebra
  have hfin : Module.Finite Γ(C, U) Γ(M.C, ν ⁻¹ᵁ U) := IsFinite.finite_app ν U hUaff
  let θ : C.functionField ≃+* M.C.functionField :=
    ((C.presheaf.stalkCongr (.of_eq hgen.symm)) ≪≫ asIso (ν.stalkMap (genericPoint
      M.C))).commRingCatIsoToRingEquiv
  have hθ : ∀ s : Γ(C, U),
      θ (algebraMap Γ(C, U) C.functionField s) = algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField (φ
        s) := by
    intro s
    change ν.stalkMap (genericPoint M.C)
        (C.presheaf.stalkSpecializes (Inseparable.of_eq hgen.symm).specializes'
          (C.presheaf.germ U (genericPoint C)
            (((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
              (by simpa using ‹Nonempty U›)) s)) =
      M.C.presheaf.germ (ν ⁻¹ᵁ U) (genericPoint M.C) hηV (φ s)
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  have hcomp : (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField).comp φ =
      θ.toRingHom.comp (algebraMap Γ(C, U) C.functionField) :=
    RingHom.ext fun s => (hθ s).symm
  let ψ : Γ(M.C, ν ⁻¹ᵁ U) →ₐ[Γ(C, U)] C.functionField :=
    { toRingHom := θ.symm.toRingHom.comp (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField)
      commutes' := fun s => by
        change θ.symm (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField (φ s)) = _
        rw [← hθ, RingEquiv.symm_apply_apply] }
  have h1 : ∀ b, IsIntegral Γ(C, U) (ψ b) := fun b => (Algebra.IsIntegral.isIntegral b).map ψ
  have h2 : ∀ x : C.functionField, IsIntegral Γ(C, U) x → x ∈ ψ.range := by
    intro x hx
    have hx' : IsIntegral Γ(M.C, ν ⁻¹ᵁ U) (θ x) := hx.map_of_comp_eq φ θ.toRingHom hcomp
    have hmem : θ x ∈ (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField).range := by
      let := (AlgebraicCurve.baseToFunctionField M.toBase).toAlgebra
      have hrange := AlgebraicCurve.range_algebraMap_functionField_eq_iInf_of_isAffineOpen
        M.toBase (ν ⁻¹ᵁ U) hVaff
      rw [hrange]
      simp only [Subring.mem_iInf]
      intro v hv
      have hle : (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField).range ≤
        v.toValuationSubring.toSubring := by
        rw [hrange]; exact iInf₂_le v hv
      let ρ : Γ(M.C, ν ⁻¹ᵁ U) →+* ↥v.toValuationSubring :=
        (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField).codRestrict v.toValuationSubring.toSubring
          fun b => hle ⟨b, rfl⟩
      have hρ : (algebraMap ↥v.toValuationSubring M.C.functionField).comp ρ =
          (RingHom.id M.C.functionField).comp (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField) :=
        RingHom.ext fun _ => rfl
      have hxv : IsIntegral ↥v.toValuationSubring (θ x) := hx'.map_of_comp_eq ρ (RingHom.id
        M.C.functionField) hρ
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := M.C.functionField)).mp hxv
      rw [← hy]
      exact y.2
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, ?_⟩
    change θ.symm (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField b) = x
    rw [hb, RingEquiv.symm_apply_apply]
  have heq : Subalgebra.toSubmodule (integralClosure Γ(C, U) C.functionField) = LinearMap.range
    ψ.toLinearMap := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := h2 x hx
      exact ⟨b, hb⟩
    · rintro ⟨b, rfl⟩
      exact h1 b
  have hfr : Module.Finite Γ(C, U) ↥(LinearMap.range ψ.toLinearMap) := Module.Finite.range
    ψ.toLinearMap
  rw [← heq] at hfr
  exact hfr

end

end AlgebraicCurves.Models.Proofs.CurveModel_finite_integralClosure_sections_of_isIso_stalkMap
end ProofImplementation
