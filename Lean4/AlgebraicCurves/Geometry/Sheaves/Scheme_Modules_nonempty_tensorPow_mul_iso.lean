/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow

/-!
# Scheme Modules nonempty tensor Pow mul iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_tensorPow_mul_iso

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

namespace TensorPowMulSol

/--
The canonical isomorphism expressing a tensor power of a sum as the tensor product of the two
powers.
-/
noncomputable def tensorPowAdd {X : Scheme.{u}} (L : X.Modules) (a : ℕ) :
    (b : ℕ) → (L.tensorPow (a + b) ≅ L.tensorPow a ⊗ L.tensorPow b)
  | 0 => (ρ_ _).symm
  | b + 1 => (tensorPowAdd L a b ⊗ᵢ Iso.refl L) ≪≫ α_ _ _ _

/--
The canonical isomorphism expressing the tensor power with exponent `a * b` as the `b`th power
of the `a`th power.
-/
noncomputable def tensorPowMul {X : Scheme.{u}} (L : X.Modules) (a : ℕ) :
    (b : ℕ) → (L.tensorPow (a * b) ≅ (L.tensorPow a).tensorPow b)
  | 0 => Iso.refl _
  | b + 1 => tensorPowAdd L (a * b) a ≪≫ (tensorPowMul L a b ⊗ᵢ Iso.refl _)

end TensorPowMulSol

theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_tensorPow_mul_iso {X : Scheme.{u}} (L :
  X.Modules) (a b : ℕ) :
    Nonempty (L.tensorPow (a * b) ≅ (L.tensorPow a).tensorPow b) :=
  ⟨TensorPowMulSol.tensorPowMul L a b⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_tensorPow_mul_iso
end ProofImplementation
