/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.RecoveredCoefficientTransitions
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.SchemePairDescent
import Nyll.SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Overlap Transition Descent

Actual recovered overlap transitions descend together to one finite
coefficient stage, retaining both structure maps and the recovery equation.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
namespace EtaleFundamentalGroups

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
variable (S : Scheme.{u}) [QuasiSeparatedSpace S] (f : S ⟶ Spec (CommRingCat.of k))
variable (𝒰 : S.OpenCover) [Finite 𝒰.I₀] [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]
variable (M : ∀ i : 𝒰.I₀, Over (𝒰.X i)) [∀ i : 𝒰.I₀, IsFiniteEtale (M i).hom]
variable (Z : Over (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))
variable (e : ∀ i : 𝒰.I₀,
  (Over.pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (𝒰.f i ≫ f))).obj (M i) ≅
      (Over.pullback ((constantFieldOpenCover k L S f 𝒰).f i)).obj Z)

local notation "φ" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "A" => (fun ij : 𝒰.I₀ × 𝒰.I₀ ↦
  pullback (Comma.hom (M (Prod.fst ij)) ≫ 𝒰.f (Prod.fst ij)) (𝒰.f (Prod.snd ij)))
local notation "p" => (fun ij : 𝒰.I₀ × 𝒰.I₀ ↦
  pullback.fst (Comma.hom (M (Prod.fst ij)) ≫ 𝒰.f (Prod.fst ij)) (𝒰.f (Prod.snd ij)) ≫
    (Comma.hom (M (Prod.fst ij)) ≫ 𝒰.f (Prod.fst ij)))

/-- Actual recovered overlap transitions descend together to one finite
coefficient stage, retaining both structure maps and the recovery equation. -/
theorem exists_finiteIntermediateField_overlap_transitions :
    ∃ s : Finset L, FiniteDimensional k (IntermediateField.adjoin k (s : Set L)) ∧
      ∃ g : ∀ ij : 𝒰.I₀ × 𝒰.I₀,
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) (p ij ≫ f) ⟶
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) (p (ij.2, ij.1) ≫ f),
        ∀ ij : 𝒰.I₀ × 𝒰.I₀,
          g ij ≫ pullback.fst _ (p (ij.2, ij.1) ≫ f) = pullback.fst _ (p ij ≫ f) ∧
          g ij ≫ pullback.snd _ (p (ij.2, ij.1) ≫ f) ≫ p (ij.2, ij.1) =
            pullback.snd _ (p ij ≫ f) ≫ p ij ∧
          (constantFieldInverseLimitCone k L (A ij) (p ij ≫ f)).π.app (op s) ≫ g ij =
            recoveredCoefficientTransition k L S f 𝒰 M Z e ij.1 ij.2 ≫
              (constantFieldInverseLimitCone k L (A (ij.2, ij.1))
                (p (ij.2, ij.1) ≫ f)).π.app (op s) := by
  let : ∀ i : 𝒰.I₀, IsAffine (M i).left := fun i ↦
    isAffine_of_isAffineHom (Y := 𝒰.X i) (M i).hom
  let : ∀ ij : 𝒰.I₀ × 𝒰.I₀, CompactSpace (A ij) := fun ij ↦
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2))
  let : ∀ ij : 𝒰.I₀ × 𝒰.I₀, QuasiSeparatedSpace (A ij) := fun ij ↦
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2))
  let : ∀ ij : 𝒰.I₀ × 𝒰.I₀, LocallyOfFinitePresentation (p (ij.2, ij.1)) :=
    fun ij ↦ inferInstance
  exact exists_finiteIntermediateField_schemePairHom_family k L S f
    A (fun ij ↦ A (ij.2, ij.1)) p (fun ij ↦ p (ij.2, ij.1))
    (fun ij ↦ recoveredCoefficientTransition k L S f 𝒰 M Z e ij.1 ij.2)
    (fun ij ↦ recoveredCoefficientTransition_original k L S f 𝒰 M Z e ij.1 ij.2)
    (fun ij ↦ recoveredCoefficientTransition_coefficient k L S f 𝒰 M Z e ij.1 ij.2)

end EtaleFundamentalGroups
