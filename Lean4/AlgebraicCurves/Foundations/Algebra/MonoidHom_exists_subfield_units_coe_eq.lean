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

import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Group.Units.Hom

/-!
# Monoid Hom exists subfield units coe eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.MonoidHom_exists_subfield_units_coe_eq

theorem _root_.MonoidHom.exists_subfield_units_coe_eq
    {G : Type*} [Group G] {L : Type*} [Field L] (K : Subfield L)
    (F : G →* G →* Lˣ) (hF : ∀ α β : G, ((F α β : Lˣ) : L) ∈ K) :
    ∃ F' : G →* G →* (↥K)ˣ, ∀ α β : G, (((F' α β : (↥K)ˣ) : ↥K) : L) = F α β := by
  have hinv : ∀ α β : G, ((F α β : Lˣ) : L)⁻¹ ∈ K := fun α β => K.inv_mem (hF α β)
  let u : G → G → (↥K)ˣ := fun α β =>
    ⟨⟨(F α β : L), hF α β⟩, ⟨((F α β : Lˣ) : L)⁻¹, hinv α β⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have hu : ∀ α β, (((u α β : (↥K)ˣ) : ↥K) : L) = F α β := fun _ _ => rfl
  refine ⟨{ toFun := fun α => { toFun := u α, map_one' := ?_, map_mul' := ?_ }
            map_one' := ?_
            map_mul' := ?_ }, hu⟩
  · ext; simp [u]
  · intro β₁ β₂; ext; simp [u, Units.val_mul]
  · ext β; simp [u]
  · intro α₁ α₂; ext β; simp [u, Units.val_mul]
end AlgebraicCurves.Foundations.Algebra.Proofs.MonoidHom_exists_subfield_units_coe_eq
end ProofImplementation
