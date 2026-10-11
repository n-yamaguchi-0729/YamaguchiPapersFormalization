/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Classical.CoefficientSheaves
import EtaleCohomology.Classical.ModuleCohomology
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Coefficient-linear long exact sequences

The connecting morphism is mathlib's Ext connecting homomorphism. Its linearity
follows from naturality under scalar multiplication on the short exact sequence.
Exactness is inherited from the existing classical cohomology long exact sequence,
using the proved exactness of the coefficient-forgetting functor.
-/


noncomputable section

universe u v w t h

open CategoryTheory CategoryTheory.Limits

namespace EtaleCohomology.Classical

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type t} [CommRing R]
variable [HasSheafify J (ModuleCat.{max t w} R)] [HasSheafify J AddCommGrpCat.{max t w}]
variable [HasExt.{h} (Sheaf J AddCommGrpCat.{max t w})]

/-- Scalar multiplication acts on the entire underlying short complex. -/
def coefficientActionShortComplex (S : ShortComplex (Sheaf J (ModuleCat.{max t w} R)))
    (r : R) :
    S.map (forgetCoefficients.{u, v, max t w, t} (J := J)) ⟶
      S.map (forgetCoefficients.{u, v, max t w, t} (J := J)) where
  τ₁ := coefficientAction S.X₁ r
  τ₂ := coefficientAction S.X₂ r
  τ₃ := coefficientAction S.X₃ r
  comm₁₂ := coefficientAction_naturality S.f r
  comm₂₃ := coefficientAction_naturality S.g r

variable {S : ShortComplex (Sheaf J (ModuleCat.{max t w} R))} (hS : S.ShortExact)

/-- The connecting homomorphism, with its canonical coefficient linearity. -/
def connecting (n : ℕ) :
    cohomology.{u, v, max t w, t, h} S.X₃ n →ₗ[R]
      cohomology.{u, v, max t w, t, h} S.X₁ (n + 1) where
  toFun := Sheaf.H.δ.{h, max t w, v, u}
    (forgetCoefficients_shortExact R J hS) n (n + 1) rfl
  map_add' := (Sheaf.H.δ.{h, max t w, v, u}
    (forgetCoefficients_shortExact R J hS) n (n + 1) rfl).map_add
  map_smul' r x := by
    change ((forgetCoefficients.{u, v, max t w, t} (J := J)).obj S.X₃).H n at x
    exact Sheaf.H.δ_naturality.{h, max t w, v, u} n (n + 1) rfl
      (forgetCoefficients_shortExact R J hS) (forgetCoefficients_shortExact R J hS)
      (coefficientActionShortComplex S r) x

/-- The underlying function of the connecting map is mathlib's classical boundary map. -/
lemma connecting_apply (n : ℕ)
    (x : cohomology.{u, v, max t w, t, h} S.X₃ n) :
    connecting.{u, v, w, t, h} hS n x =
      Sheaf.H.δ.{h, max t w, v, u}
        (forgetCoefficients_shortExact R J hS) n (n + 1) rfl x := rfl

/-- Naturality of the coefficient-linear connecting map. -/
lemma connecting_naturality
    {S₁ S₂ : ShortComplex (Sheaf J (ModuleCat.{max t w} R))}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (n : ℕ)
    (x : cohomology.{u, v, max t w, t, h} S₁.X₃ n) :
    connecting.{u, v, w, t, h} h₂ n
        (cohomologyMap.{u, v, max t w, t, h} f.τ₃ n x) =
      cohomologyMap.{u, v, max t w, t, h} f.τ₁ (n + 1)
        (connecting.{u, v, w, t, h} h₁ n x) := by
  simp only [connecting_apply, cohomologyMap_apply]
  -- Explicit components keep comparison with the boundary map local.
  let g : S₁.map (forgetCoefficients.{u, v, max t w, t} (J := J)) ⟶
      S₂.map (forgetCoefficients.{u, v, max t w, t} (J := J)) :=
    { τ₁ := (forgetCoefficients.{u, v, max t w, t} (J := J)).map f.τ₁
      τ₂ := (forgetCoefficients.{u, v, max t w, t} (J := J)).map f.τ₂
      τ₃ := (forgetCoefficients.{u, v, max t w, t} (J := J)).map f.τ₃
      comm₁₂ := by
        change (forgetCoefficients.{u, v, max t w, t} (J := J)).map f.τ₁ ≫
            (forgetCoefficients.{u, v, max t w, t} (J := J)).map S₂.f =
          (forgetCoefficients.{u, v, max t w, t} (J := J)).map S₁.f ≫
            (forgetCoefficients.{u, v, max t w, t} (J := J)).map f.τ₂
        rw [← Functor.map_comp, ← Functor.map_comp, f.comm₁₂]
      comm₂₃ := by
        change (forgetCoefficients.{u, v, max t w, t} (J := J)).map f.τ₂ ≫
            (forgetCoefficients.{u, v, max t w, t} (J := J)).map S₂.g =
          (forgetCoefficients.{u, v, max t w, t} (J := J)).map S₁.g ≫
            (forgetCoefficients.{u, v, max t w, t} (J := J)).map f.τ₃
        rw [← Functor.map_comp, ← Functor.map_comp, f.comm₂₃] }
  exact Sheaf.H.δ_naturality.{h, max t w, v, u} n (n + 1) rfl
    (forgetCoefficients_shortExact R J h₁) (forgetCoefficients_shortExact R J h₂)
    g x

include hS in
/-- Exactness at the middle coefficient sheaf in every degree. -/
lemma cohomology_exact (n : ℕ) :
    Function.Exact (cohomologyMap.{u, v, max t w, t, h} S.f n)
      (cohomologyMap.{u, v, max t w, t, h} S.g n) :=
  (ShortComplex.ab_exact_iff_function_exact.{h} _).mp
    (Sheaf.H.longSequence_exact₂'.{h, max t w, v, u}
      (forgetCoefficients_shortExact R J hS) n)

/-- Exactness at the source of the connecting map. -/
lemma cohomology_exact_connecting (n : ℕ) :
    Function.Exact (cohomologyMap.{u, v, max t w, t, h} S.g n)
      (connecting.{u, v, w, t, h} hS n) :=
  (ShortComplex.ab_exact_iff_function_exact.{h} _).mp
    (Sheaf.H.longSequence_exact₃'.{h, max t w, v, u}
      (forgetCoefficients_shortExact R J hS) n (n + 1) rfl)

/-- Exactness at the target of the connecting map. -/
lemma connecting_exact_cohomology (n : ℕ) :
    Function.Exact (connecting.{u, v, w, t, h} hS n)
      (cohomologyMap.{u, v, max t w, t, h} S.f (n + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact.{h} _).mp
    (Sheaf.H.longSequence_exact₁'.{h, max t w, v, u}
      (forgetCoefficients_shortExact R J hS) n (n + 1) rfl)

end EtaleCohomology.Classical
