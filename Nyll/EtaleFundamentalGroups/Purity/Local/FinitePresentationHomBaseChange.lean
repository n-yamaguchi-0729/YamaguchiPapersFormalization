/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-!
# Flat base change for `Hom` from a finitely presented module

For a flat algebra `S / R`, the canonical map

`Hom_R(M, N) → Hom_S(S ⊗ M, S ⊗ N)`

is a base-change map when `M` is finitely presented. The finite-presentation
result follows from `Module.FinitePresentation.isBaseChange_map`; the
finite-free case and precomposition compatibility are recorded here for
downstream use.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v

open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M N P : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- Base change of a linear map commutes with precomposition.  This is the
commutative square used in both the finite-presentation `Hom` comparison and
the later `Ext¹` comparison. -/
theorem linearMap_baseChangeHom_comp_lcomp (p : P →ₗ[R] M) :
    (LinearMap.baseChangeHom R S P N).comp (LinearMap.lcomp R N p) =
      ((LinearMap.lcomp S (S ⊗[R] N) (p.baseChange S)).restrictScalars R).comp
        (LinearMap.baseChangeHom R S M N) := by
  ext f x
  simp [LinearMap.lcomp_apply]

/-- The canonical `Hom` comparison is a base change when its first variable
is finite free. -/
theorem linearMap_baseChangeHom_isBaseChange_of_free_finite
    [Module.Free R M] [Module.Finite R M] :
    IsBaseChange S (LinearMap.baseChangeHom R S M N) := by
  let ιM : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  let ιN : N →ₗ[R] S ⊗[R] N := TensorProduct.mk R S N 1
  have hM : IsBaseChange S ιM :=
    TensorProduct.isBaseChange (R := R) (M := M) (S := S)
  have hN : IsBaseChange S ιN :=
    TensorProduct.isBaseChange (R := R) (M := N) (S := S)
  have hbc : IsBaseChange S (IsBaseChange.linearMapLeftRightHom hM ιN) :=
    hM.linearMapLeftRight hN
  have heq : IsBaseChange.linearMapLeftRightHom hM ιN =
      LinearMap.baseChangeHom R S M N := by
    apply LinearMap.ext
    intro f
    apply hM.algHom_ext
    intro m
    change (hM.linearMapLeftRightHom ιN f) (ιM m) = ιN (f m)
    exact IsBaseChange.linearMapLeftRightHom_comp_apply hM ιN f m
  rwa [heq] at hbc

/-- For a flat algebra, the canonical `Hom` comparison is a base change when
the first variable is finitely presented. -/
theorem linearMap_baseChangeHom_isBaseChange_of_finitePresentation_of_flat
    [Small.{v} R] [Module.Flat R S] [Module.FinitePresentation R M] :
    IsBaseChange S (LinearMap.baseChangeHom R S M N) := by
  exact Module.FinitePresentation.isBaseChange_map R M N S

end EtaleFundamentalGroups

end
