/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech

/-!
# Module Flat bijective ker Base Change Hom and nonempty homology base Change linear Equiv
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv

universe u uR uT uM

open TensorProduct

namespace LOCSOL

section FlatKer

variable {R : Type uR} [CommRing R] (T : Type uT) [CommRing T] [Algebra R T] [Module.Flat R T]
  {M N : Type uM} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem baseChange_subtype_injective (K : Submodule R M) :
    Function.Injective (K.subtype.baseChange T) := by
  intro x y h
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := T) K.subtype
    K.injective_subtype
  exact hinj h

theorem exists_baseChange_subtype_eq (f : M →ₗ[R] N) (y : T ⊗[R] M)
    (hy : f.baseChange T y = 0) :
    ∃ x : T ⊗[R] LinearMap.ker f, (LinearMap.ker f).subtype.baseChange T x = y := by
  have h := Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map f)
  exact (h y).mp hy

theorem kerBaseChangeHom_bijective (f : M →ₗ[R] N) :
    Function.Bijective (TwoChartCech.kerBaseChangeHom f T) := by
  constructor
  · intro x y h
    apply baseChange_subtype_injective T (LinearMap.ker f)
    rw [← TwoChartCech.kerBaseChangeHom_apply_coe, ← TwoChartCech.kerBaseChangeHom_apply_coe, h]
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_baseChange_subtype_eq T f y hy
    exact ⟨x, Subtype.ext (by rw [TwoChartCech.kerBaseChangeHom_apply_coe, hx])⟩

/-- The comparison equivalence between the base change of a kernel and the kernel after flat
base change. -/
noncomputable def kerEquiv (f : M →ₗ[R] N) :
    T ⊗[R] LinearMap.ker f ≃ₗ[T] LinearMap.ker (f.baseChange T) :=
  LinearEquiv.ofBijective _ (kerBaseChangeHom_bijective T f)

@[scoped simp] theorem kerEquiv_apply_coe (f : M →ₗ[R] N) (x : T ⊗[R] LinearMap.ker f) :
    (kerEquiv T f x : T ⊗[R] M) = (LinearMap.ker f).subtype.baseChange T x := by
  simp [kerEquiv, TwoChartCech.kerBaseChangeHom_apply_coe]

theorem baseChange_mkQ_eq_zero_iff {K : Type uM} [AddCommGroup K] [Module R K] (B : Submodule R K)
    (t : T ⊗[R] K) : (B.mkQ).baseChange T t = 0 ↔ ∃ b : T ⊗[R] B, B.subtype.baseChange T b = t := by
  have h := Module.Flat.lTensor_exact T (LinearMap.exact_subtype_mkQ B)
  exact h t

end FlatKer

end LOCSOL

attribute [local simp] LOCSOL.kerEquiv_apply_coe


open LOCSOL in
theorem _root_.Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
    {R : Type u} [CommRing R] (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T]
    {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P]
      [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : g ∘ₗ f = 0) :
    letI : AddCommGroup ↥(LinearMap.ker (g.baseChange T)) :=
      Submodule.addCommGroup (M := T ⊗[R] N) (LinearMap.ker (g.baseChange T))
    Function.Bijective (TwoChartCech.kerBaseChangeHom g T) ∧
    Nonempty
      (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[T]
        (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) ∧
    ((LinearMap.ker (g.baseChange T) ≤ LinearMap.range (f.baseChange T)) ↔
        Subsingleton (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker
          g).subtype))) ∧
    (Module.Finite R (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) →
        Module.Finite T (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) := by
  classical
  let iK' : AddCommGroup ↥(LinearMap.ker (g.baseChange T)) :=
    Submodule.addCommGroup (M := T ⊗[R] N) (LinearMap.ker (g.baseChange T))
  have hfK : ∀ m, f m ∈ LinearMap.ker g := fun m => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hfg, LinearMap.zero_apply]
  have hfB : ∀ m, f.codRestrict (LinearMap.ker g) hfK m ∈
      (LinearMap.range f).comap (LinearMap.ker g).subtype := fun m =>
    Submodule.mem_comap.mpr ⟨m, rfl⟩
  have hδ : Function.Surjective
      ((f.codRestrict (LinearMap.ker g) hfK).codRestrict _ hfB) := by
    rintro ⟨⟨y, hyK⟩, hyB⟩
    obtain ⟨m, hm⟩ := Submodule.mem_comap.mp hyB
    exact ⟨m, Subtype.ext (Subtype.ext hm)⟩
  have hfac : ((LinearMap.ker g).subtype ∘ₗ ((LinearMap.range f).comap (LinearMap.ker
    g).subtype).subtype) ∘ₗ
      ((f.codRestrict (LinearMap.ker g) hfK).codRestrict _ hfB) = f := by
    ext m
    rfl
  have hπ : Function.Surjective
      ((((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ).baseChange T) :=
    LinearMap.lTensor_surjective T (Submodule.mkQ_surjective _)
  have hΦ : Function.Surjective
      (((LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype).mkQ ∘ₗ
        (kerEquiv T g).toLinearMap) :=
    (Submodule.mkQ_surjective _).comp (kerEquiv T g).surjective
  have hker : LinearMap.ker ((((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ).baseChange
    T) =
      LinearMap.ker (((LinearMap.range (f.baseChange T)).comap
        (LinearMap.ker (g.baseChange T)).subtype).mkQ ∘ₗ (kerEquiv T g).toLinearMap) := by
    ext t
    rw [LinearMap.mem_ker, LinearMap.mem_ker, baseChange_mkQ_eq_zero_iff, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, kerEquiv_apply_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨c, rfl⟩ : ∃ c, ((f.codRestrict (LinearMap.ker g) hfK).codRestrict _ hfB).baseChange T
        c = b :=
        LinearMap.lTensor_surjective T hδ b
      refine ⟨c, ?_⟩
      symm
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
        ← LinearMap.baseChange_comp, hfac]
    · rintro ⟨c, hc⟩
      have h2 : (LinearMap.ker g).subtype.baseChange T
          ((((LinearMap.range f).comap (LinearMap.ker g).subtype).subtype.baseChange T)
            (((f.codRestrict (LinearMap.ker g) hfK).codRestrict _ hfB).baseChange T c)) =
          (LinearMap.ker g).subtype.baseChange T t := by
        rw [← hc, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
          ← LinearMap.baseChange_comp, hfac]
      exact ⟨_, baseChange_subtype_injective T _ h2⟩
  let e : T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[T]
      (↥(LinearMap.ker (g.baseChange T)) ⧸
        (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype) :=
    (LinearMap.quotKerEquivOfSurjective _ hπ).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective _ hΦ))
  refine ⟨kerBaseChangeHom_bijective T g, ⟨e⟩, ?_, fun hfin => ?_⟩
  · constructor
    · intro hle
      have : Subsingleton (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ a
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ b
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
        exact hle (x - y).2
      exact e.toEquiv.subsingleton
    · intro hs y hy
      have := hs
      have : Subsingleton (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype) :=
        e.symm.toEquiv.subsingleton
      have h0 : ((LinearMap.range (f.baseChange T)).comap
          (LinearMap.ker (g.baseChange T)).subtype).mkQ ⟨y, hy⟩ = 0 := Subsingleton.elim _ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
      exact h0
  · have := hfin
    exact Module.Finite.equiv e
end Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
