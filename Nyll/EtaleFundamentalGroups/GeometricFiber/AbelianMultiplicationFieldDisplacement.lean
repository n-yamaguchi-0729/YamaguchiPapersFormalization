/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationAlgebraicPoints

/-!
# Field Galois displacement of actual algebraic division points

The coefficient-field action on an actual division point agrees with the
action on the geometric fibre. Consequently its displacement is the actual
multiplication-monodromy torsion point. No comparison of actions is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
  {L : Type} [Field L] [Algebra K L]
  {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [IsScalarTower K L Ω] [IsSepClosed Ω] [IsSepClosure L Ω]

omit [IsAlgClosed K] in
/-- Coefficient Galois action is the actual fibre action on the algebraic
point underlying a multiplication-cover fibre element. -/
theorem multiplicationFiberAlgPoint_field_smul
    (j : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f)
    (n : ℕ+) (σ : Ω ≃ₐ[L] Ω)
    (z : (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j.1)).obj
        (G.multiplicationCover hc n)) :
    let ξ := AlgPoints.mapPoint (IsScalarTower.toAlgHom K L Ω) j
    let η := Spec.map (CommRingCat.ofHom (algebraMap L Ω))
    let g := FiniteEtale.fundamentalGroupHom j.1 η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[L] Ω) σ)
    (σ.restrictScalars K) • G.multiplicationFiberAlgPoint hc ξ n z =
      G.multiplicationFiberAlgPoint hc ξ n (g • z) := by
  intro ξ η g
  have hfield := FiniteEtale.fundamentalGroupHom_field_fiberLift j.1
    (G.multiplicationCover hc n) σ z
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      (G.multiplicationFiberPoint hc (η ≫ j.1) n z).1 =
    (G.multiplicationFiberPoint hc (η ≫ j.1) n (g • z)).1
  exact hfield.symm

/-- The Galois displacement of an actual algebraic division point is the
base change of its actual multiplication-monodromy torsion point. -/
theorem multiplicationFiberAlgPoint_field_displacement
    (j : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f)
    (n : ℕ+)
    (τ : FiniteEtale.fiber
        (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j.1) ≅
      FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (σ : Ω ≃ₐ[L] Ω)
    (z : (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j.1)).obj
        (G.multiplicationCover hc n)) :
    let ξ := AlgPoints.mapPoint (IsScalarTower.toAlgHom K L Ω) j
    let η := Spec.map (CommRingCat.ofHom (algebraMap L Ω))
    let g := FiniteEtale.fundamentalGroupHom j.1 η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[L] Ω) σ)
    (σ.restrictScalars K) • G.multiplicationFiberAlgPoint hc ξ n z -
        G.multiplicationFiberAlgPoint hc ξ n z =
      AlgPoints.map (Algebra.ofId K Ω)
        (G.multiplicationMonodromy hc n (continuousConjAut τ g)).1 := by
  intro ξ η g
  let Q := G.multiplicationFiberAlgPoint hc ξ n z
  let t := AlgPoints.map (Algebra.ofId K Ω)
    (G.multiplicationMonodromy hc n (continuousConjAut τ g)).1
  calc
    (σ.restrictScalars K) • Q - Q =
        G.multiplicationFiberAlgPoint hc ξ n (g • z) - Q :=
      congrArg (fun P : G.AlgPoints hc Ω => P - Q)
        (G.multiplicationFiberAlgPoint_field_smul hc j n σ z)
    _ = (Q + t) - Q :=
      congrArg (fun P : G.AlgPoints hc Ω => P - Q)
        (G.multiplicationFiberAlgPoint_smul hc ξ n τ g z)
    _ = t := add_sub_cancel_left Q t

end GoodReductionJacobian.RelativeGroupLaw
