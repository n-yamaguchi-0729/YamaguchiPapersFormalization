/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Ext
import AlgebraicCurves.Foundations.Algebra.Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
import AlgebraicCurves.Foundations.Algebra.Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit
import AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit

/-!
# Algebra exists alg Equiv tensor Product map eq of finite Presentation of is Direct Limit
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit

open scoped TensorProduct

universe u₀ u v w w₁ w₂

namespace AlgEquivSpreadDirected

open TensorProduct

variable {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))

/-- The structural algebra homomorphism from a stage of the directed system to its limit. -/
abbrev toR (i : ι) : G i →ₐ[R₀] R := IsScalarTower.toAlgHom R₀ (G i) R

section Maps

variable (M : Type w₁) [CommRing M] [Algebra R₀ M]

/-- Tensor the structural map of a stage with the identity of the second algebra. -/
abbrev mapT (i : ι) : G i ⊗[R₀] M →ₐ[R₀] R ⊗[R₀] M :=
  Algebra.TensorProduct.map (toR i) (AlgHom.id R₀ M)

/-- Tensor a transition map of the directed system with the identity of the second algebra. -/
abbrev stepT {i j : ι} (hij : i ≤ j) : G i ⊗[R₀] M →ₐ[R₀] G j ⊗[R₀] M :=
  Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ M)
include hR in
omit [Nonempty ι] [IsDirectedOrder ι] in
theorem mapT_stepT {i j : ι} (hij : i ≤ j) (x : G i ⊗[R₀] M) :
    mapT (R := R) M j (stepT f M hij x) = mapT M i x := by
  induction x using TensorProduct.inductionOn with
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul]
    exact congrArg (fun r : R => r ⊗ₜ[R₀] (AlgHom.id R₀ M b)) (hR.compatibility i j hij g)
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
omit [Nonempty ι] [IsDirectedOrder ι] in
theorem stepT_stepT {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : G i ⊗[R₀] M) :
    stepT f M hjk (stepT f M hij x) = stepT f M (hij.trans hjk) x := by
  induction x using TensorProduct.inductionOn with
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul]
    congr 1
    exact DirectedSystem.map_map (f := fun i j h => ⇑(f i j h)) hij hjk g
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
omit [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] in
theorem tmul_one_eq_algebraMap (i : ι) (g : G i) :
    g ⊗ₜ[R₀] (1 : M) = algebraMap (G i) (G i ⊗[R₀] M) g := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem tmul_one_eq_algebraMap_R (r : R) :
    r ⊗ₜ[R₀] (1 : M) = algebraMap R (R ⊗[R₀] M) r := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

end Maps

section Relevel

variable (A : Type w₁) [CommRing A] [Algebra R₀ A] (B : Type w₂) [CommRing B] [Algebra R₀ B]

/-- Transport an algebra homomorphism of tensor products to a later stage of the directed
system. -/
noncomputable def relevel {i j : ι} (hij : i ≤ j) (φ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B) :
    G j ⊗[R₀] A →ₐ[G j] G j ⊗[R₀] B :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := G j) (R := R₀) (A := G j) (B
    := B))
    ((stepT f B hij).comp ((φ.restrictScalars R₀).comp
      (Algebra.TensorProduct.includeRight (R := R₀) (A := G i) (B := A))))
    (fun _ _ => Commute.all _ _)
omit [Nonempty ι] [IsDirectedOrder ι] [DirectedSystem G fun i j h ↦ ⇑(f i j h)] in
theorem relevel_tmul {i j : ι} (hij : i ≤ j) (φ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B) (g : G j) (a :
  A) :
    relevel f A B hij φ (g ⊗ₜ[R₀] a) = (g ⊗ₜ[R₀] (1 : B)) * stepT f B hij (φ ((1 : G i) ⊗ₜ[R₀] a))
      :=
  Algebra.TensorProduct.lift_tmul _ _ _ g a
omit [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] in
theorem stage_tmul_one {i : ι} (φ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B) (g : G i) :
    φ (g ⊗ₜ[R₀] (1 : A)) = g ⊗ₜ[R₀] (1 : B) := by
  rw [tmul_one_eq_algebraMap, AlgHom.commutes, ← tmul_one_eq_algebraMap]
omit [DirectedSystem G fun i j h ↦ ⇑(f i j h)] [Nonempty ι] [IsDirectedOrder ι] in
theorem relevel_stepT {i j : ι} (hij : i ≤ j) (φ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B) (x : G i ⊗[R₀]
  A) :
    relevel f A B hij φ (stepT f A hij x) = stepT f B hij (φ x) := by
  let H₁ : G i ⊗[R₀] A →ₐ[R₀] G j ⊗[R₀] B := ((relevel f A B hij φ).restrictScalars R₀).comp (stepT
    f A hij)
  let H₂ : G i ⊗[R₀] A →ₐ[R₀] G j ⊗[R₀] B := (stepT f B hij).comp (φ.restrictScalars R₀)
  suffices hH : H₁ = H₂ from AlgHom.congr_fun hH x
  apply Algebra.TensorProduct.ext
  · ext g
    change relevel f A B hij φ (stepT f A hij (g ⊗ₜ[R₀] (1 : A))) = stepT f B hij (φ (g ⊗ₜ[R₀] (1 :
      A)))
    have hone : stepT f B hij (φ ((1 : G i) ⊗ₜ[R₀] (1 : A))) = 1 := by
      rw [stage_tmul_one, Algebra.TensorProduct.map_tmul, map_one, map_one]; rfl
    rw [stage_tmul_one]
    change relevel f A B hij φ (f i j hij g ⊗ₜ[R₀] AlgHom.id R₀ A 1) = f i j hij g ⊗ₜ[R₀] AlgHom.id
      R₀ B 1
    rw [map_one, map_one, relevel_tmul, hone, mul_one]
  · ext a
    change relevel f A B hij φ (stepT f A hij ((1 : G i) ⊗ₜ[R₀] a)) = stepT f B hij (φ ((1 : G i)
      ⊗ₜ[R₀] a))
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, relevel_tmul,
      show ((1 : G j) ⊗ₜ[R₀] (1 : B)) = 1 from rfl, one_mul]
include hR in
omit [Nonempty ι] [IsDirectedOrder ι] in
theorem square_relevel {i j : ι} (hij : i ≤ j) (φ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B)
    (e : R ⊗[R₀] A →ₐ[R] R ⊗[R₀] B)
    (hφ : ∀ x : G i ⊗[R₀] A, e (mapT A i x) = mapT B i (φ x)) :
    ∀ y : G j ⊗[R₀] A, e (mapT A j y) = mapT B j (relevel f A B hij φ y) := by
  let H₁ : G j ⊗[R₀] A →ₐ[R₀] R ⊗[R₀] B := (e.restrictScalars R₀).comp (mapT A j)
  let H₂ : G j ⊗[R₀] A →ₐ[R₀] R ⊗[R₀] B := (mapT B j).comp ((relevel f A B hij φ).restrictScalars
    R₀)
  suffices hH : H₁ = H₂ from fun y => AlgHom.congr_fun hH y
  have hone : stepT f B hij (φ ((1 : G i) ⊗ₜ[R₀] (1 : A))) = 1 := by
    rw [stage_tmul_one, Algebra.TensorProduct.map_tmul, map_one, map_one]; rfl
  apply Algebra.TensorProduct.ext
  · ext g
    change e (mapT A j (g ⊗ₜ[R₀] (1 : A))) = mapT B j (relevel f A B hij φ (g ⊗ₜ[R₀] (1 : A)))
    rw [relevel_tmul, hone, mul_one]
    change e (toR (R₀ := R₀) (R := R) j g ⊗ₜ[R₀] AlgHom.id R₀ A 1) = toR (R₀ := R₀) (R := R) j g
      ⊗ₜ[R₀] AlgHom.id R₀ B 1
    rw [map_one, map_one, tmul_one_eq_algebraMap_R A (toR (R₀ := R₀) (R := R) j g), AlgHom.commutes,
      ← tmul_one_eq_algebraMap_R B (toR (R₀ := R₀) (R := R) j g)]
  · ext a
    change e (mapT A j ((1 : G j) ⊗ₜ[R₀] a)) = mapT B j (relevel f A B hij φ ((1 : G j) ⊗ₜ[R₀] a))
    rw [relevel_tmul, show ((1 : G j) ⊗ₜ[R₀] (1 : B)) = 1 from rfl, one_mul, mapT_stepT f hR, ← hφ,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one, map_one]

end Relevel

include hR in
theorem exists_algEquiv
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FinitePresentation R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B] [Algebra.FinitePresentation R₀ B]
    (e : R ⊗[R₀] A ≃ₐ[R] R ⊗[R₀] B) :
    ∃ (i : ι) (e₀ : G i ⊗[R₀] A ≃ₐ[G i] G i ⊗[R₀] B),
      ∀ x : G i ⊗[R₀] A, e (mapT A i x) = mapT B i (e₀ x) := by
  classical
  obtain ⟨i₁, φ₀, hφ₀⟩ :=
    Algebra.exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit R₀ G f R hR A
      B (e : R ⊗[R₀] A →ₐ[R] R ⊗[R₀] B)
  obtain ⟨i₂, ψ₀, hψ₀⟩ :=
    Algebra.exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit R₀ G f R hR B
      A
      (e.symm : R ⊗[R₀] B →ₐ[R] R ⊗[R₀] A)
  obtain ⟨j₀, h₁, h₂⟩ := exists_ge_ge i₁ i₂
  let φ₁ := relevel f A B h₁ φ₀
  let ψ₁ := relevel f B A h₂ ψ₀
  have hφ₁ : ∀ y, e (mapT A j₀ y) = mapT B j₀ (φ₁ y) := square_relevel f hR A B h₁ φ₀ e hφ₀
  have hψ₁ : ∀ y, e.symm (mapT B j₀ y) = mapT A j₀ (ψ₁ y) := square_relevel f hR B A h₂ ψ₀ e.symm
    hψ₀
  have hcompA : ∀ x : G j₀ ⊗[R₀] A, mapT (R := R) A j₀ ((ψ₁.comp φ₁) x) = mapT A j₀ ((AlgHom.id (G
    j₀) _) x) := by
    intro x
    rw [AlgHom.comp_apply, ← hψ₁, ← hφ₁, AlgEquiv.symm_apply_apply, AlgHom.id_apply]
  have hcompB : ∀ y : G j₀ ⊗[R₀] B, mapT (R := R) B j₀ ((φ₁.comp ψ₁) y) = mapT B j₀ ((AlgHom.id (G
    j₀) _) y) := by
    intro y
    rw [AlgHom.comp_apply, ← hφ₁, ← hψ₁, AlgEquiv.apply_symm_apply, AlgHom.id_apply]
  obtain ⟨j₁, hj₁, hkA⟩ :=
    Algebra.exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit R₀ G f R hR A A
      (ψ₁.comp φ₁) (AlgHom.id _ _) hcompA
  obtain ⟨j₂, hj₂, hkB⟩ :=
    Algebra.exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit R₀ G f R hR B B
      (φ₁.comp ψ₁) (AlgHom.id _ _) hcompB
  obtain ⟨j, hj₁', hj₂'⟩ := exists_ge_ge j₁ j₂
  have h₀ : j₀ ≤ j := hj₁.trans hj₁'
  have hkA' : ∀ x : G j₀ ⊗[R₀] A, stepT f A h₀ (ψ₁ (φ₁ x)) = stepT f A h₀ x := by
    intro x
    have := congrArg (stepT f A hj₁') (hkA x)
    rw [AlgHom.comp_apply, AlgHom.id_apply, stepT_stepT, stepT_stepT] at this
    exact this
  have hkB' : ∀ y : G j₀ ⊗[R₀] B, stepT f B h₀ (φ₁ (ψ₁ y)) = stepT f B h₀ y := by
    intro y
    have h₀' : j₀ ≤ j := hj₂.trans hj₂'
    have := congrArg (stepT f B hj₂') (hkB y)
    rw [AlgHom.comp_apply, AlgHom.id_apply, stepT_stepT, stepT_stepT] at this
    exact this
  let φ₂ := relevel f A B h₀ φ₁
  let ψ₂ := relevel f B A h₀ ψ₁
  have hφ₂ : ∀ y, e (mapT A j y) = mapT B j (φ₂ y) := square_relevel f hR A B h₀ φ₁ e hφ₁
  have left_inv : ψ₂.comp φ₂ = AlgHom.id (G j) (G j ⊗[R₀] A) := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext a
      change ψ₂ (φ₂ ((1 : G j) ⊗ₜ[R₀] a)) = (1 : G j) ⊗ₜ[R₀] a
      rw [relevel_tmul, show ((1 : G j) ⊗ₜ[R₀] (1 : B)) = 1 from rfl, one_mul]
      change relevel f B A h₀ ψ₁ (stepT f B h₀ (φ₁ ((1 : G j₀) ⊗ₜ[R₀] a))) = _
      rw [relevel_stepT, hkA', Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have right_inv : φ₂.comp ψ₂ = AlgHom.id (G j) (G j ⊗[R₀] B) := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext b
      change φ₂ (ψ₂ ((1 : G j) ⊗ₜ[R₀] b)) = (1 : G j) ⊗ₜ[R₀] b
      rw [relevel_tmul, show ((1 : G j) ⊗ₜ[R₀] (1 : A)) = 1 from rfl, one_mul]
      change relevel f A B h₀ φ₁ (stepT f A h₀ (ψ₁ ((1 : G j₀) ⊗ₜ[R₀] b))) = _
      rw [relevel_stepT, hkB', Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  exact ⟨j, AlgEquiv.ofAlgHom φ₂ ψ₂ right_inv left_inv, hφ₂⟩

end AlgEquivSpreadDirected

theorem _root_.Algebra.exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R₀ : Type u₀) [CommRing R₀]
    (G : ι → Type v) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FinitePresentation R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B] [Algebra.FinitePresentation R₀ B]
    (e : R ⊗[R₀] A ≃ₐ[R] R ⊗[R₀] B) :
    ∃ (i : ι) (e₀ : G i ⊗[R₀] A ≃ₐ[G i] G i ⊗[R₀] B),
      ∀ x : G i ⊗[R₀] A,
        e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ A) x) =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (e₀ x) :=
            by
  classical
  exact AlgEquivSpreadDirected.exists_algEquiv f hR A B e
end Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
