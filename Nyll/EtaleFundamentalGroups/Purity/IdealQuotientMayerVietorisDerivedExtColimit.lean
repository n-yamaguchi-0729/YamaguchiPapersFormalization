/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.IdealQuotientMayerVietorisDerivedExtPowers
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Filtered colimits of derived-Ext Mayer--Vietoris sequences

An objectwise exact diagram of finite composable sequences determines an
exact short complex of functors on every adjacent three-term window.  Exact
filtered colimits then give the corresponding exact short complex of
colimit objects.  The final section applies this construction to the
derived-Ext Mayer--Vietoris diagram along simultaneous ideal powers.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe w v u

section AdjacentWindow

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type*} [Category D]
variable {n : ℕ}

/-- The adjacent three-term window beginning at `k` in an objectwise exact
diagram of `n` composable arrows, regarded as a short complex in the functor
category. -/
def exactComposableArrowsDiagramAdjacentShortComplex
    (Q : D ⥤ ComposableArrows C n) (hQ : ∀ d, (Q.obj d).Exact)
    (k : ℕ) (hk : k + 2 ≤ n) : ShortComplex (D ⥤ C) where
  X₁ := Q ⋙ (evaluation (Fin (n + 1)) C).obj ⟨k, by omega⟩
  X₂ := Q ⋙ (evaluation (Fin (n + 1)) C).obj ⟨k + 1, by omega⟩
  X₃ := Q ⋙ (evaluation (Fin (n + 1)) C).obj ⟨k + 2, by omega⟩
  f :=
    { app := fun d => (Q.obj d).map' k (k + 1)
      naturality := fun _ _ φ =>
        (ComposableArrows.naturality' (Q.map φ) k (k + 1)).symm }
  g :=
    { app := fun d => (Q.obj d).map' (k + 1) (k + 2)
      naturality := fun _ _ φ =>
        (ComposableArrows.naturality' (Q.map φ) (k + 1) (k + 2)).symm }
  zero := by
    ext d
    exact (hQ d).toIsComplex.zero k hk

/-- Objectwise exactness of the finite sequences produces exactness of every
adjacent short complex in the functor category. -/
theorem exactComposableArrowsDiagramAdjacentShortComplex_exact
    (Q : D ⥤ ComposableArrows C n) (hQ : ∀ d, (Q.obj d).Exact)
    (k : ℕ) (hk : k + 2 ≤ n) :
    (exactComposableArrowsDiagramAdjacentShortComplex Q hQ k hk).Exact := by
  let E : D → ((D ⥤ C) ⥤ C) := fun d => (evaluation D C).obj d
  have hE : JointlyReflectIsomorphisms E :=
    { isIso := fun f =>
        (NatTrans.isIso_iff_isIso_app f).2 (fun d => by
          change IsIso ((E d).map f)
          infer_instance) }
  rw [hE.exact_iff]
  intro d
  exact (hQ d).exact k hk

end AdjacentWindow

section ExactColimit

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type*} [Category D]
variable [HasColimitsOfShape D C] [HasExactColimitsOfShape D C]

/-- The short complex obtained by applying the chosen colimit functor to all
three terms and both maps of a short complex of diagrams. -/
def shortComplexExactColimit (S : ShortComplex (D ⥤ C)) : ShortComplex C :=
  colim.mapShortComplex S
    (colimit.isColimit S.X₁)
    (colimit.cocone S.X₂)
    (colimit.cocone S.X₃)
    (colim.map S.f)
    (colim.map S.g)
    (fun d => colimit.ι_map S.f d)
    (fun d => colimit.ι_map S.g d)

/-- Exact colimits preserve exactness of the standard colimit short
complex. This is the direct `colim.exact_mapShortComplex` interface used by
the Mayer--Vietoris powers diagram. -/
theorem shortComplexExactColimit_exact
    (S : ShortComplex (D ⥤ C)) (hS : S.Exact) :
    (shortComplexExactColimit S).Exact := by
  apply colim.exact_mapShortComplex (S := S) hS
    (colimit.isColimit S.X₁)
    (colimit.isColimit S.X₂)
    (colimit.isColimit S.X₃)

end ExactColimit

section IdealPowersColimit

variable {R : Type u} [CommRing R]

/-- An adjacent three-term window in the six-term derived-Ext
Mayer--Vietoris diagram along simultaneous powers of `I` and `J`. -/
def idealQuotientMayerVietorisDerivedExtPowersAdjacentShortComplex
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)
    (k : ℕ) (hk : k + 2 ≤ 5) :
    ShortComplex ((ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  exactComposableArrowsDiagramAdjacentShortComplex
    (idealQuotientMayerVietorisDerivedExtPowersDiagram I J M n₀ n₁ h)
    (idealQuotientMayerVietorisDerivedExtPowersDiagram_obj_exact
      I J M n₀ n₁ h)
    k hk

/-- Every adjacent three-term window of the powers-derived-Ext diagram is
exact in the functor category. -/
theorem idealQuotientMayerVietorisDerivedExtPowersAdjacentShortComplex_exact
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)
    (k : ℕ) (hk : k + 2 ≤ 5) :
    (idealQuotientMayerVietorisDerivedExtPowersAdjacentShortComplex
      I J M n₀ n₁ h k hk).Exact :=
  exactComposableArrowsDiagramAdjacentShortComplex_exact
    (idealQuotientMayerVietorisDerivedExtPowersDiagram I J M n₀ n₁ h)
    (idealQuotientMayerVietorisDerivedExtPowersDiagram_obj_exact
      I J M n₀ n₁ h)
    k hk

/-- The chosen filtered colimits of an adjacent three-term window in the
powers-derived-Ext diagram. -/
def idealQuotientMayerVietorisDerivedExtPowersAdjacentColimitShortComplex
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)
    (k : ℕ) (hk : k + 2 ≤ 5) :
    ShortComplex AddCommGrpCat.{u} :=
  shortComplexExactColimit
    (idealQuotientMayerVietorisDerivedExtPowersAdjacentShortComplex
      I J M n₀ n₁ h k hk)

/-- Filtered colimits preserve exactness of every adjacent three-term
window in the powers-derived-Ext Mayer--Vietoris diagram. -/
theorem
    idealQuotientMayerVietorisDerivedExtPowersAdjacentColimitShortComplex_exact
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)
    (k : ℕ) (hk : k + 2 ≤ 5) :
    (idealQuotientMayerVietorisDerivedExtPowersAdjacentColimitShortComplex
      I J M n₀ n₁ h k hk).Exact := by
  let : AB5OfSize.{0, 0} AddCommGrpCat.{u} :=
    AB5OfSize_shrink AddCommGrpCat.{u}
  exact shortComplexExactColimit_exact _
    (idealQuotientMayerVietorisDerivedExtPowersAdjacentShortComplex_exact
      I J M n₀ n₁ h k hk)

end IdealPowersColimit

end EtaleFundamentalGroups

end
