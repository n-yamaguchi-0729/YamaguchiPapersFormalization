/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions

/-!
# OModule Presheaf eq zero of forall res basic Open eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace G4T
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

universe u

section PModQC
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem eq_zero_of_forall_res_basicOpen_eq_zero {F : OModulePresheaf π} (hF :
  OModulePresheaf.IsQuasicoherent F)
    (U : V.affineOpens) {ι : Type*} [Finite ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1)
    (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose n hn using fun j => (hF U (h j)).2 x (hx j)
  have hspan : Ideal.span (Set.range fun j => (h j) ^ (n j + 1)) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    exact (hcov.trans (iSup_mono fun j =>
        (V.basicOpen_pow (h j) (n j).succ_pos).ge)).trans
      (iSup_le fun j => le_iSup_of_le ⟨_, j, rfl⟩ le_rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : Γ(V, U.1)) ∈ Ideal.span _ from hspan ▸ Submodule.mem_top)
  calc x = (1 : Γ(V, U.1)) • x := (one_smul _ x).symm
    _ = (∑ j, c j * (h j) ^ (n j + 1)) • x := by rw [hc]
    _ = ∑ j, c j • ((h j) ^ (n j + 1) • x) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = 0 := Finset.sum_eq_zero fun j _ => by
        rw [pow_succ', mul_smul, hn j, smul_zero, smul_zero]

end PModQC

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero {R : Type
  u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (hF :
  F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Finite ι] (h : ι → Γ(V, U.1)) (hcov : U.1 ≤
  ⨆ j, V.basicOpen (h j)) (x : F.obj U.1) (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 :=
  AlgebraicGeometry.OModulePresheaf.G4T.eq_zero_of_forall_res_basicOpen_eq_zero hF U h hcov x hx
end OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
