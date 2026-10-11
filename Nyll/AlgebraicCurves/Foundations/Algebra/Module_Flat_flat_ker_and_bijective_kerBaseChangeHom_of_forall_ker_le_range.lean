/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech

/-!
# Module Flat flat ker and bijective ker Base Change Hom of forall ker le range
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.FlatKernelBaseChange

universe u

open TensorProduct

namespace C1Body

open Function

section purity

variable {R : Type u} [CommRing R]
  {Z P Q : Type u} [AddCommGroup Z] [Module R Z] [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q]

theorem lTensor_injective_of_presentation (ι : Z →ₗ[R] P) (δ : P →ₗ[R] Q)
    (hι : Injective ι) (hex : Exact ι δ) (hδ : Surjective δ) [Module.Flat R Q]
    (K F N : Type u) [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup N] [Module R N] (κ : K →ₗ[R] F) (τ : F →ₗ[R] N) (hκ : Injective κ)
    (hκτ : Exact κ τ) (hτ : Surjective τ) :
    Injective (ι.lTensor N) := by
  have hf : Exact (ι.lTensor K) (δ.lTensor K) := lTensor_exact K hex hδ
  have hg : Exact (ι.lTensor F) (δ.lTensor F) := lTensor_exact F hex hδ
  have hf₂ : Surjective (δ.lTensor K) := LinearMap.lTensor_surjective K hδ
  have hg₁ : Injective (ι.lTensor F) := Module.Flat.lTensor_preserves_injective_linearMap ι hι
  have h₁ : (ι.lTensor F).comp (κ.rTensor Z) = (κ.rTensor P).comp (ι.lTensor K) :=
    TensorProduct.ext' fun _ _ => rfl
  have h₂ : (δ.lTensor F).comp (κ.rTensor P) = (κ.rTensor Q).comp (δ.lTensor K) :=
    TensorProduct.ext' fun _ _ => rfl
  have hi₃ : Injective (κ.rTensor Q) := Module.Flat.rTensor_preserves_injective_linearMap κ hκ
  have hπ₁ : Exact (κ.rTensor Z) (τ.rTensor Z) := rTensor_exact Z hκτ hτ
  have hπ₂ : Exact (κ.rTensor P) (τ.rTensor P) := rTensor_exact P hκτ hτ
  have hπ₁s : Surjective (τ.rTensor Z) := LinearMap.rTensor_surjective Z hτ
  have hG : (ι.lTensor N).comp (τ.rTensor Z) = (τ.rTensor P).comp (ι.lTensor F) :=
    TensorProduct.ext' fun _ _ => rfl
  have hι₃ : Exact (LinearMap.ker (κ.rTensor Q)).subtype (κ.rTensor Q) :=
    LinearMap.exact_subtype_ker_map _
  have hE : Exact (SnakeLemma.δ' (κ.rTensor Z) (κ.rTensor P) (κ.rTensor Q) (ι.lTensor K)
    (δ.lTensor K) hf
      (ι.lTensor F) (δ.lTensor F) hg h₁ h₂ (LinearMap.ker (κ.rTensor Q)).subtype hι₃
      (τ.rTensor Z) hπ₁ hf₂ hg₁) (ι.lTensor N) :=
    SnakeLemma.exact_δ'_left (κ.rTensor Z) (κ.rTensor P) (κ.rTensor Q) (ι.lTensor K) (δ.lTensor K)
      hf
      (ι.lTensor F) (δ.lTensor F) hg h₁ h₂ (LinearMap.ker (κ.rTensor Q)).subtype hι₃
      (τ.rTensor Z) hπ₁ (τ.rTensor P) hπ₂ hf₂ hg₁ (ι.lTensor N) hG hπ₁s
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := (hE x).mp hx
  have hk0 : k = 0 := by
    apply Subtype.ext
    have h0 : (κ.rTensor Q) k.1 = 0 := k.2
    exact hi₃ (h0.trans (map_zero _).symm)
  rw [← hk, hk0, map_zero]

theorem lTensor_injective_of_flat_right (ι : Z →ₗ[R] P) (δ : P →ₗ[R] Q)
    (hι : Injective ι) (hex : Exact ι δ) (hδ : Surjective δ) [Module.Flat R Q]
    (N : Type u) [AddCommGroup N] [Module R N] :
    Injective (ι.lTensor N) := by
  classical
  have hτ : Surjective (Finsupp.linearCombination R (id : N → N)) :=
    Finsupp.linearCombination_surjective R surjective_id
  have hκτ : Exact (LinearMap.ker (Finsupp.linearCombination R (id : N → N))).subtype
      (Finsupp.linearCombination R (id : N → N)) := LinearMap.exact_subtype_ker_map _
  exact lTensor_injective_of_presentation ι δ hι hex hδ
    (↥(LinearMap.ker (Finsupp.linearCombination R (id : N → N)))) (N →₀ R) N
    (LinearMap.ker (Finsupp.linearCombination R (id : N → N))).subtype
    (Finsupp.linearCombination R (id : N → N)) Subtype.val_injective hκτ hτ

end purity

section complex

variable {R : Type u} [CommRing R]
  (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)

/-- The kernel of the differential at the indicated degree. -/
abbrev Z (i : ℕ) : Submodule R (C i) := LinearMap.ker (d i)

/-- The differential with codomain restricted to the kernel of the next differential. -/
def δ (i : ℕ) : C i →ₗ[R] Z C d (i + 1) :=
  (d i).codRestrict _ (fun c => by
    change d (i + 1) (d i c) = 0
    rw [← LinearMap.comp_apply, hdd]; rfl)

theorem subtype_comp_δ (i : ℕ) : (Z C d (i + 1)).subtype ∘ₗ δ C d hdd i = d i :=
  LinearMap.subtype_comp_codRestrict _ _ _

theorem exact_subtype_δ (i : ℕ) : Exact (Z C d i).subtype (δ C d hdd i) := by
  rw [LinearMap.exact_iff, δ, LinearMap.ker_codRestrict, Submodule.range_subtype]

theorem δ_surjective (i : ℕ) (hex : LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) :
    Surjective (δ C d hdd i) := by
  intro z
  obtain ⟨c, hc⟩ := hex z.2
  exact ⟨c, Subtype.ext hc⟩

/-- Flatness of the kernel and injectivity of its inclusion after tensoring with any module. -/
def Inv (i : ℕ) : Prop :=
  Module.Flat R (Z C d i) ∧
    ∀ (N : Type u) [AddCommGroup N] [Module R N], Injective ((Z C d i).subtype.lTensor N)

theorem inv_of_subsingleton [∀ i, Module.Flat R (C i)] (i : ℕ) (h : Subsingleton (C i)) :
    Inv C d i := by
  have : Subsingleton (Z C d i) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  refine ⟨Module.Flat.of_linearEquiv (LinearEquiv.ofSubsingleton (Z C d i) (C i)), fun N _ _ => ?_⟩
  have hz : ∀ w : N ⊗[R] Z C d i, w = 0 := fun w => by
    induction w with
    | tmul a z => rw [Subsingleton.elim z 0, tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  intro x y _
  rw [hz x, hz y]

include hdd in
theorem step [∀ i, Module.Flat R (C i)] (i : ℕ)
    (hex : LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) (h : Inv C d (i + 1)) :
    Inv C d i := by
  have : Module.Flat R (Z C d (i + 1)) := h.1
  have hδ := δ_surjective C d hdd i hex
  have hexact := exact_subtype_δ C d hdd i
  have pure : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Injective ((Z C d i).subtype.lTensor N) := fun N _ _ =>
    lTensor_injective_of_flat_right _ _ Subtype.val_injective hexact hδ N
  refine ⟨?_, pure⟩
  refine (Module.Flat.iff_rTensor_preserves_injective_linearMap').mpr ?_
  intro N N' _ _ _ _ f hf
  have hcomp : ((Z C d i).subtype.lTensor N') ∘ₗ (f.rTensor (Z C d i)) =
      (f.rTensor (C i)) ∘ₗ ((Z C d i).subtype.lTensor N) :=
    TensorProduct.ext' fun _ _ => rfl
  have hinj : Injective (((Z C d i).subtype.lTensor N') ∘ (f.rTensor (Z C d i))) := by
    rw [← LinearMap.coe_comp, hcomp, LinearMap.coe_comp]
    exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp (pure N)
  exact hinj.of_comp

include hdd in
theorem inv_all [∀ i, Module.Flat R (C i)] (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) (i : ℕ) : Inv C d i := by
  suffices H : ∀ t i, n ≤ i + t → Inv C d i from H n i (Nat.le_add_left n i)
  intro t
  induction t with
  | zero => intro i hi; exact inv_of_subsingleton C d i (hbd i (by omega))
  | succ t ih =>
    intro i hi
    by_cases hni : n ≤ i
    · exact inv_of_subsingleton C d i (hbd i hni)
    · exact step C d hdd i (hex i) (ih (i + 1) (by omega))

include hdd in
theorem range_lTensor_subtype_eq [∀ i, Module.Flat R (C i)] (n : ℕ) (hbd : ∀ i, n ≤ i →
  Subsingleton (C i))
    (hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) (i : ℕ)
    (N : Type u) [AddCommGroup N] [Module R N] :
    LinearMap.range ((Z C d i).subtype.lTensor N) = LinearMap.ker ((d i).lTensor N) := by
  have hδ := δ_surjective C d hdd i (hex i)
  have hexact := exact_subtype_δ C d hdd i
  have h1 : LinearMap.ker ((δ C d hdd i).lTensor N) = LinearMap.range ((Z C d i).subtype.lTensor
    N) :=
    (LinearMap.exact_iff.mp (lTensor_exact N hexact hδ))
  have h2 : (d i).lTensor N = ((Z C d (i + 1)).subtype.lTensor N) ∘ₗ ((δ C d hdd i).lTensor N) := by
    rw [← LinearMap.lTensor_comp, subtype_comp_δ]
  rw [← h1, h2, LinearMap.ker_comp_of_ker_eq_bot]
  exact LinearMap.ker_eq_bot.mpr ((inv_all C d hdd n hbd hex (i + 1)).2 N)

end complex

end C1Body

open C1Body in
theorem _root_.Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range
    {R : Type u} [CommRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) :
    Module.Flat R (LinearMap.ker (d 0)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) := by
  have hinv := inv_all C d hdd n hbd hex
  have hbc : ∀ {M M' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
      (f : M →ₗ[R] M') (A : Type u) [CommRing A] [Algebra R A] (z : A ⊗[R] M),
      f.baseChange A z = f.lTensor A z := fun f A _ _ z =>
    congrFun (LinearMap.baseChange_eq_ltensor (A := A) (f := f)) z
  refine ⟨(hinv 0).1, fun A _ _ => ⟨?_, ?_⟩, fun A _ _ i => ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    have hx' : ((LinearMap.ker (d 0)).subtype.baseChange A) x = 0 := by
      rw [← TwoChartCech.kerBaseChangeHom_apply_coe, hx]; rfl
    rw [hbc] at hx'
    exact (hinv 0).2 A (hx'.trans (map_zero _).symm)
  · intro y
    have hy : (y : A ⊗[R] C 0) ∈ LinearMap.ker ((d 0).lTensor A) := by
      rw [LinearMap.mem_ker, ← hbc]; exact y.2
    rw [← range_lTensor_subtype_eq C d hdd n hbd hex 0 A] at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, Subtype.ext ?_⟩
    rw [TwoChartCech.kerBaseChangeHom_apply_coe, hbc, hx]
  · intro y hy
    have hy' : y ∈ LinearMap.ker ((d (i + 1)).lTensor A) := by
      rw [LinearMap.mem_ker, ← hbc]; exact hy
    rw [← range_lTensor_subtype_eq C d hdd n hbd hex (i + 1) A] at hy'
    obtain ⟨x, rfl⟩ := hy'
    obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective A (δ_surjective C d hdd i (hex i)) x
    refine ⟨w, ?_⟩
    rw [hbc, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, subtype_comp_δ]
end AlgebraicCurves.Foundations.Algebra.Proofs.FlatKernelBaseChange
end ProofImplementation
