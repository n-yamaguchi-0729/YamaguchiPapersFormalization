/-
The semilinear residue-evaluation proof below is adapted from
JacobianVarieties/WeilPairing/DivisorialWeilPairingData_pair_semilinearSmul.lean.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Upstream source:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Local adaptation and maintenance: Naganori Yamaguchi
(https://github.com/n-yamaguchi-0729), assisted by OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra

/-! # Semilinear compatibility of residue and divisor evaluation -/

noncomputable section

namespace AlgebraicCurve.SemilinearAut

open IsLocalRing
open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (g : SemilinearAut K F) (v : Place K F)

private theorem mem_smul_toValuationSubring_iff (f : F) :
    g • f ∈ (g • v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [smul_toValuationSubring]
  constructor
  · intro h
    have h1 := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      (g := g) (S := v.toValuationSubring) (x := g • f)).mp h
    rwa [inv_smul_smul] at h1
  · intro h
    exact ValuationSubring.smul_mem_pointwise_smul g f v.toValuationSubring h

private theorem isRational_smul (hv : v.IsRational) : (g • v).IsRational := by
  intro x
  obtain ⟨a, ha⟩ := hv ((smulResidueRingEquiv g v).symm x)
  exact ⟨baseAut g a, by
    rw [← smulResidueRingEquiv_algebraMap g v a, ha, RingEquiv.apply_symm_apply]⟩

private theorem residue_smul {f : F} (hf : f ∈ v.toValuationSubring) :
    residue (g • v).toValuationSubring
        (⟨g • f, (mem_smul_toValuationSubring_iff g v f).mpr hf⟩ :
          (g • v).toValuationSubring)
      = smulResidueRingEquiv g v (residue v.toValuationSubring ⟨f, hf⟩) := by
  change _ = IsLocalRing.ResidueField.mapEquiv
      (smulValuationSubringEquiv g v.toValuationSubring)
      (residue v.toValuationSubring ⟨f, hf⟩)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg _ (Subtype.ext rfl)

private theorem evalAt_smul (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    (g • v).evalAt (g • f) = baseAut g (v.evalAt f) := by
  have hv' : (g • v).IsRational := isRational_smul g v hv
  have hmem : g • f ∈ (g • v).toValuationSubring :=
    (mem_smul_toValuationSubring_iff g v f).mpr hf
  apply (g • v).algebraMap_residueField_injective
  rw [(g • v).algebraMap_evalAt hv' hmem, residue_smul g v hf, ← v.algebraMap_evalAt hv hf]
  exact smulResidueRingEquiv_algebraMap g v (v.evalAt f)

/-- Rational divisor evaluation commutes with the actual semilinear action. -/
theorem evalFun_smul {f : F} (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hmem : ∀ v ∈ D.support, f ∈ v.toValuationSubring) :
    Divisor.evalFun (g • f) (g • D) = baseAut g (Divisor.evalFun f D) := by
  classical
  have hL : Divisor.evalFun (g • f) (g • D)
      = ∏ w ∈ D.support, (g • w).evalAt (g • f) ^ D w := by
    rw [show Divisor.evalFun (g • f) (g • D)
        = (g • D).prod (fun w n => w.evalAt (g • f) ^ n) from rfl,
      divisor_smul_def, Finsupp.prod_mapDomain_index_inj (MulAction.injective g)]
    rfl
  have hR : baseAut g (Divisor.evalFun f D)
      = ∏ w ∈ D.support, baseAut g (w.evalAt f ^ D w) := by
    rw [Divisor.evalFun_def, map_prod]
  rw [hL, hR]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [evalAt_smul g w (hrat w hw) (hmem w hw), map_zpow₀]

end AlgebraicCurve.SemilinearAut
