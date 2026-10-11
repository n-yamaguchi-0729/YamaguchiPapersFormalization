/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Algebra_DescentCofaces.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Algebra Descent Cofaces
-/

universe u

open TensorProduct CategoryTheory

noncomputable section

namespace Algebra.DescentCofaces

/-- Compare two iterated scalar extensions whose composite ring maps agree. -/
noncomputable def compareScalarExtensions
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g₁ g₂ : S →+* T) (h : g₁.comp f = g₂.comp f)
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars g₁).obj ((ModuleCat.extendScalars f).obj M) ⟶
      (ModuleCat.extendScalars g₂).obj ((ModuleCat.extendScalars f).obj M) :=
  (ModuleCat.extendScalarsComp f g₁).inv.app M ≫
    eqToHom (congrArg (fun φ : R →+* T => (ModuleCat.extendScalars φ).obj M) h) ≫
    (ModuleCat.extendScalarsComp f g₂).hom.app M

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The double tensor product of the algebra, regarded as a commutative ring object. -/
abbrev R₂ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] B)

/-- The triple tensor product of the algebra, regarded as a commutative ring object. -/
abbrev R₃ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] (B ⊗[A] B))

/-- The inclusion into the first factor of the double tensor product. -/
def i₁ : CommRingCat.of B ⟶ R₂ A B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- The inclusion into the second factor of the double tensor product. -/
def i₂ : CommRingCat.of B ⟶ R₂ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom

/-- The map inserting one in the third factor of the triple tensor product. -/
def c₁₂ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := B))).toRingHom

/-- The map inserting one in the first factor of the triple tensor product. -/
def c₂₃ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B ⊗[A] B)).toRingHom

/-- The map inserting one in the middle factor of the triple tensor product. -/
def c₁₃ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B))).toRingHom

@[simp] theorem i₁_apply (b : B) : (i₁ A B).hom b = b ⊗ₜ 1 := rfl
@[simp] theorem i₂_apply (b : B) : (i₂ A B).hom b = 1 ⊗ₜ b := rfl
@[simp] theorem c₁₂_tmul (b b' : B) : (c₁₂ A B).hom (b ⊗ₜ b') = b ⊗ₜ (b' ⊗ₜ 1) := rfl
@[simp] theorem c₂₃_tmul (b b' : B) : (c₂₃ A B).hom (b ⊗ₜ b') = 1 ⊗ₜ (b ⊗ₜ b') := rfl
@[simp] theorem c₁₃_tmul (b b' : B) : (c₁₃ A B).hom (b ⊗ₜ b') = b ⊗ₜ (1 ⊗ₜ b') := rfl

theorem i₁_c₁₂ : i₁ A B ≫ c₁₂ A B = i₁ A B ≫ c₁₃ A B := rfl
theorem i₂_c₁₂ : i₂ A B ≫ c₁₂ A B = i₁ A B ≫ c₂₃ A B := rfl
theorem i₂_c₁₃ : i₂ A B ≫ c₁₃ A B = i₂ A B ≫ c₂₃ A B := rfl

theorem algebraMap_i₁_eq_i₂ :
    CommRingCat.ofHom (algebraMap A B) ≫ i₁ A B = CommRingCat.ofHom (algebraMap A B) ≫ i₂ A B := by
  ext a
  change algebraMap A B a ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] algebraMap A B a
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem i₁_comp_algebraMap_eq :
    (i₁ A B).hom.comp (algebraMap A B) = (i₂ A B).hom.comp (algebraMap A B) :=
  congrArg CommRingCat.Hom.hom (algebraMap_i₁_eq_i₂ A B)

/-- The canonical descent comparison between the two scalar extensions of a base module. -/
def canonical (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (i₁ A B).hom).obj ((ModuleCat.extendScalars (algebraMap A B)).obj M) ⟶
      (ModuleCat.extendScalars (i₂ A B).hom).obj ((ModuleCat.extendScalars (algebraMap A B)).obj M)
        :=
  compareScalarExtensions (algebraMap A B) (i₁ A B).hom (i₂ A B).hom
    (i₁_comp_algebraMap_eq A B) M


variable {A B} in
/-- Transport a descent morphism to the triple tensor product along a coface map. -/
def T (N : ModuleCat.{u} B) (c : R₂ A B ⟶ R₃ A B)
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B).hom).obj
      N) :
    (ModuleCat.extendScalars (i₁ A B ≫ c).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B ≫
      c).hom).obj N :=
  (ModuleCat.extendScalarsComp (i₁ A B).hom c.hom).hom.app N ≫
    (ModuleCat.extendScalars c.hom).map φ' ≫
    (ModuleCat.extendScalarsComp (i₂ A B).hom c.hom).inv.app N

variable {A B} in
/-- The cocycle condition for the three transported descent morphisms. -/
def Cocycle (N : ModuleCat.{u} B)
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B).hom).obj
      N) : Prop :=
  T N (c₁₂ A B) φ' ≫ T N (c₂₃ A B) φ' = T N (c₁₃ A B) φ'

end Algebra.DescentCofaces

end
