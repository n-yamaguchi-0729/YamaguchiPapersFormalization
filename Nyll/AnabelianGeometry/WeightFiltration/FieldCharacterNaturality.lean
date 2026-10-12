/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.CohomologyPullbackCharacters
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFundamentalGroupConjugacy

/-!
# Actual finite H¹ characters under a field extension

The canonical scheme pullback and restriction of field automorphisms agree
on cohomology characters. The inner conjugator in the geometric-fiber
comparison disappears because the coefficient group is commutative.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups.Cohomology JacobianVarieties.Kummer

namespace AnabelianGeometry.WeightFiltration

variable (k E Ω : Type) [Field k] [Field E] [Field Ω]
  [Algebra k E] [Algebra E Ω] [Algebra k Ω] [IsScalarTower k E Ω]
  [IsSepClosure k Ω] [IsSepClosure E Ω] [IsSepClosed Ω]

/-- Pullback on actual field H¹ is scalar restriction on absolute Galois
characters, including the canonical geometric-fiber comparisons. -/
theorem h1Character_fieldPullback
    (A : AddCommGrpCat.{0}) [Finite A]
    (a : Sheaf.H.{0} ((constantSheaf (Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{0}).obj A) 1) (σ : Ω ≃ₐ[E] Ω) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    h1Character A ((Spec.map (CommRingCat.ofHom (algebraMap E Ω))))
        (constantCohomologyPullback ((Spec.map (CommRingCat.ofHom (algebraMap k E)))) A 1 a)
        (FiniteEtale.absoluteGaloisToFiberAutMulEquiv E Ω inferInstance σ) =
      h1Character A ((Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) a
        (FiniteEtale.absoluteGaloisToFiberAutMulEquiv k Ω inferInstance
          (σ.restrictScalars k)) := by
  intro htop
  let g := FiniteEtale.absoluteGaloisToFiberAutMulEquiv E Ω inferInstance σ
  let b := FiniteEtale.fundamentalGroupHom ((Spec.map (CommRingCat.ofHom (algebraMap k E))))
    ((Spec.map (CommRingCat.ofHom (algebraMap E Ω)))) g
  let p := FiniteEtale.fieldBasePointFiberIso k E Ω
  let χ := h1Character A ((Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) a
  let c := FiniteEtale.fieldFundamentalGroupComparisonAut k E Ω
  have hb := congrArg (fun ψ => ψ b)
    (h1Character_basePoint A
      ((Spec.map (CommRingCat.ofHom (algebraMap E Ω))) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k E))))
      ((Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) p a)
  change χ (p.conjAut b) =
    h1Character A ((Spec.map (CommRingCat.ofHom (algebraMap E Ω))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))) a b at hb
  rw [h1Character_constantCohomologyPullback]
  change h1Character A ((Spec.map (CommRingCat.ofHom (algebraMap E Ω))) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k E)))) a b = _
  rw [← hb]
  calc
    χ (p.conjAut b) = χ (FiniteEtale.fieldFundamentalGroupHom k E Ω inferInstance g) := by
      rw [FiniteEtale.fieldFundamentalGroupHom_eq_conj_fundamentalGroupHom]
      change χ (p.conjAut b) = χ (MulAut.conj c (p.conjAut b))
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv,
        mul_comm (χ c) (χ (p.conjAut b)), mul_assoc, mul_inv_cancel, mul_one]
    _ = _ := congrArg χ (FiniteEtale.fieldFundamentalGroupHom_toAutMulEquiv k E Ω σ)

end AnabelianGeometry.WeightFiltration
