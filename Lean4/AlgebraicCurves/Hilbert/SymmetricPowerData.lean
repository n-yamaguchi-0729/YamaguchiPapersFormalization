/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_SymmetricPower.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Finite fiber powers and symmetric power data

Constructs the permutation action on a finite fiber power and records symmetric power properties.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)

/-- The fiber product of r copies of C over the given field. -/
noncomputable abbrev finFibrePow : Scheme.{u} :=
  widePullback (Spec (CommRingCat.of k)) (fun _ : Fin r => C) (fun _ => c)

namespace finFibrePow

/-- The projection from the finite fiber power to its l-th factor. -/
noncomputable abbrev proj (l : Fin r) : finFibrePow c r ⟶ C :=
  WidePullback.π (fun _ : Fin r => c) l

/-- The structure morphism from the finite fiber power to the field spectrum. -/
noncomputable abbrev toBase : finFibrePow c r ⟶ Spec (CommRingCat.of k) :=
  WidePullback.base (fun _ : Fin r => c)
@[reassoc]
theorem proj_comp (l : Fin r) : proj c r l ≫ c = toBase c r :=
  WidePullback.π_arrow _ _

/-- The endomorphism that permutes the factors by the inverse permutation. -/
noncomputable def permHom (σ : Equiv.Perm (Fin r)) : finFibrePow c r ⟶ finFibrePow c r :=
  WidePullback.lift (toBase c r) (fun j => proj c r (σ⁻¹ j)) (fun _ => WidePullback.π_arrow _ _)
@[reassoc]
theorem permHom_proj (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    permHom c r σ ≫ proj c r j = proj c r (σ⁻¹ j) :=
  WidePullback.lift_π _ _ _ _ _
@[reassoc]
theorem permHom_toBase (σ : Equiv.Perm (Fin r)) : permHom c r σ ≫ toBase c r = toBase c r :=
  WidePullback.lift_base _ _ _ _

theorem permHom_one : permHom c r 1 = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.id_comp, inv_one, Equiv.Perm.one_apply]
  · rw [permHom_toBase, Category.id_comp]

theorem permHom_mul (σ τ : Equiv.Perm (Fin r)) :
    permHom c r (σ * τ) = permHom c r τ ≫ permHom c r σ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.assoc, permHom_proj, permHom_proj, mul_inv_rev,
      Equiv.Perm.mul_apply]
  · rw [permHom_toBase, Category.assoc, permHom_toBase, permHom_toBase]

/-- The automorphism of the fiber power induced by a permutation of its factors. -/
noncomputable def permAut (σ : Equiv.Perm (Fin r)) : Aut (finFibrePow c r) where
  hom := permHom c r σ
  inv := permHom c r σ⁻¹
  hom_inv_id := by rw [← permHom_mul, inv_mul_cancel, permHom_one]
  inv_hom_id := by rw [← permHom_mul, mul_inv_cancel, permHom_one]

/-- The symmetric group action on the finite fiber power. -/
noncomputable def permAct : Equiv.Perm (Fin r) →* Aut (finFibrePow c r) :=
  MonoidHom.mk' (permAut c r) (fun σ τ => by
    ext : 1
    change permHom c r (σ * τ) = (permAut c r τ).hom ≫ (permAut c r σ).hom
    exact permHom_mul c r σ τ)

theorem permAct_hom (σ : Equiv.Perm (Fin r)) : (permAct c r σ).hom = permHom c r σ := rfl

theorem permAct_inv (σ : Equiv.Perm (Fin r)) : (permAct c r σ).inv = permHom c r σ⁻¹ := rfl
@[reassoc]
theorem permAct_hom_proj (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (permAct c r σ).hom ≫ proj c r (σ i) = proj c r i := by
  rw [permAct_hom, permHom_proj, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
@[reassoc]
theorem permAct_hom_toBase (σ : Equiv.Perm (Fin r)) :
    (permAct c r σ).hom ≫ toBase c r = toBase c r := by
  rw [permAct_hom, permHom_toBase]

end finFibrePow

theorem le_preimage_of_comp_eq {X Y : Scheme.{u}} (g : X ⟶ X) (q : X ⟶ Y) (h : g ≫ q = q)
    (V : Y.Opens) : q ⁻¹ᵁ V ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, h]

end AlgebraicGeometry

namespace AlgebraicCurve

open AlgebraicGeometry

/-- A symmetric power with quotient, affine chart, and geometric property data. -/
structure SymmetricPowerPackage {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ) where
  /-- The scheme representing the symmetric power. -/
  Csym : Scheme.{u}
  /-- The structure morphism of the symmetric power over the field. -/
  csym : Csym ⟶ Spec (CommRingCat.of k)
  /-- The quotient morphism from the finite fiber power. -/
  π : finFibrePow c r ⟶ Csym
  /-- The quotient morphism preserves the structure morphism to the field. -/
  π_comp_csym : π ≫ csym = finFibrePow.toBase c r
  /-- The quotient morphism is invariant under permutation of the factors. -/
  permAct_comp_π : ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom ≫ π = π
  /-- The quotient morphism is finite. -/
  isFinite_π : IsFinite π
  /-- The quotient morphism is surjective on points. -/
  surjective_π : Surjective π
  /-- Two points have the same quotient image exactly when a permutation relates them. -/
  π_apply_eq_iff : ∀ x x' : ↥(finFibrePow c r),
    π.base x = π.base x' ↔ ∃ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom.base x = x'
  /-- The quotient induces an injective map on sections over each open set. -/
  app_injective : ∀ V : Csym.Opens, Function.Injective (π.app V)
  /-- The image on sections consists exactly of the permutation-invariant sections. -/
  range_app : ∀ V : Csym.Opens, Set.range (π.app V) =
    {s | ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
      (le_preimage_of_comp_eq _ _ (permAct_comp_π σ) V) s = s}
  /-- An affine open of the curve gives an affine chart on the symmetric power. -/
  exists_affine_chart : ∀ U : C.Opens, IsAffineOpen U →
    ∃ V : Csym.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = ⨅ l : Fin r, (finFibrePow.proj c r l) ⁻¹ᵁ U
  /-- The symmetric power scheme is integral. -/
  integral : IsIntegral Csym
  /-- The symmetric power is proper over the field. -/
  proper : IsProper csym
  /-- The symmetric power is smooth of relative dimension r over the field. -/
  smooth : SmoothOfRelativeDimension r csym

end AlgebraicCurve
