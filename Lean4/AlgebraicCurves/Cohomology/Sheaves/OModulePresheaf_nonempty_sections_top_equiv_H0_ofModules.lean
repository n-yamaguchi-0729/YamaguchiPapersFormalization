/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules

/-!
# OModule Presheaf nonempty sections top equiv H0 of Modules
-/

section ProofImplementation


namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.GlobalSectionsH0

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace AC3Aux

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (M :
  V.Modules)
  (K : V.OrderedAffineCover)

/-- The constant zero-simplex at the given cover index. -/
def chain0 (i : K.ι) : K.Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by omega)⟩

theorem idx0_eq (t : K.Idx 0) : t = chain0 K (t.1 0) := by
  apply Subtype.ext
  funext j
  change t.1 j = t.1 0
  exact congrArg t.1 (Fin.eq_zero j)

theorem U_le_inter_chain0 (i : K.ι) : K.U i ≤ K.inter (chain0 K i) :=
  le_iInf fun _ => le_refl _

theorem inter_le_U (t : K.Idx 0) : K.inter t ≤ K.U (t.1 0) := K.inter_le t 0

/-- The ordered one-simplex associated to two increasing cover indices. -/
def chain1 {i j : K.ι} (h : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr (fun k => by fin_cases k; simpa using h)⟩

theorem inf_le_inter_chain1 {i j : K.ι} (h : i < j) : K.U i ⊓ K.U j ≤ K.inter (chain1 K h) := by
  apply le_iInf
  intro k
  fin_cases k
  · exact inf_le_left
  · exact inf_le_right

/-- The module presheaf of sections of the given sheaf of modules. -/
abbrev F : OModulePresheaf π := OModulePresheaf.ofModules π M

theorem res_mem_H0 (x : (F π M).obj ⊤) : (fun s : K.Idx 0 => (F π M).res (le_top : K.inter s ≤ ⊤)
  x) ∈ (F π M).H0 K := by
  rw [LinearMap.mem_ker]
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    OModulePresheaf.res_res]
  exact add_neg_cancel _

/-- The linear map sending a global section to its Čech zero-cocycle. -/
def toH0 : (F π M).obj ⊤ →ₗ[R] (F π M).H0 K :=
  LinearMap.codRestrict ((F π M).H0 K) (LinearMap.pi fun s : K.Idx 0 => (F π M).res (le_top :
    K.inter s ≤ ⊤))
    (res_mem_H0 π M K)

theorem toH0_apply (x : (F π M).obj ⊤) (s : K.Idx 0) : (toH0 π M K x : (F π M).cochain K 0) s = (F
  π M).res le_top x := rfl

/-- The underlying sheaf of abelian groups of the given sheaf of modules. -/
def shf : TopCat.Sheaf Ab V.toTopCat := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩

theorem toH0_injective : Function.Injective (toH0 π M K) := by
  intro x y hxy
  apply TopCat.Sheaf.eq_of_locally_eq' (shf M) K.U ⊤ (fun i => homOfLE le_top) (K.iSup_eq_top ▸
    le_refl _)
  intro i
  change (F π M).res (le_top : K.U i ≤ ⊤) x = (F π M).res le_top y
  have := congrArg (fun c : (F π M).H0 K => (F π M).res (U_le_inter_chain0 K i) ((c : (F π
    M).cochain K 0) (chain0 K i))) hxy
  simp only [toH0_apply, OModulePresheaf.res_res] at this
  exact this

theorem toH0_surjective : Function.Surjective (toH0 π M K) := by
  intro c
  let sf : ∀ i : K.ι, (F π M).obj (K.U i) := fun i => (F π M).res (U_le_inter_chain0 K i) ((c : (F
    π M).cochain K 0) (chain0 K i))
  have hsf : ∀ i, sf i = (F π M).res (U_le_inter_chain0 K i) ((c : (F π M).cochain K 0) (chain0 K
    i)) := fun _ => rfl
  have hker : ∀ s : K.Idx 1, (F π M).d K 0 (c : (F π M).cochain K 0) s = 0 := fun s => by
    have := c.2; rw [LinearMap.mem_ker] at this; exact congrFun this s
  have key : ∀ (W : V.Opens) (t : K.Idx 0) (i₀ : K.ι) (ht : t = chain0 K i₀) (hle : W ≤ K.inter t)
      (hle' : W ≤ K.inter (chain0 K i₀)),
      (F π M).res hle ((c : (F π M).cochain K 0) t) = (F π M).res hle' ((c : (F π M).cochain K 0)
        (chain0 K i₀)) := by
    intro W t i₀ ht hle hle'; subst ht; rfl
  have hcompat_lt : ∀ {i j : K.ι} (h : i < j),
      (F π M).res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (sf i) = (F π M).res (inf_le_right : K.U i
        ⊓ K.U j ≤ K.U j) (sf j) := by
    intro i j h
    have h0 := hker (chain1 K h)
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at h0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h0
    rw [add_neg_eq_zero] at h0
    have hf0 : K.face (chain1 K h) 0 = chain0 K j := by
      apply Subtype.ext; funext k; change ![i, j] (Fin.succAbove 0 k) = j
      rw [Fin.eq_zero k]; rfl
    have hf1 : K.face (chain1 K h) 1 = chain0 K i := by
      apply Subtype.ext; funext k; change ![i, j] (Fin.succAbove 1 k) = i
      rw [Fin.eq_zero k]; rfl
    have h1 := congrArg ((F π M).res (inf_le_inter_chain1 K h)) h0
    rw [OModulePresheaf.res_res, OModulePresheaf.res_res] at h1
    rw [hsf, hsf, OModulePresheaf.res_res, OModulePresheaf.res_res]
    rw [key _ _ j hf0 _ ((inf_le_right).trans (U_le_inter_chain0 K j)),
      key _ _ i hf1 _ ((inf_le_left).trans (U_le_inter_chain0 K i))] at h1
    exact h1.symm
  have hcompat : TopCat.Presheaf.IsCompatible (shf M).obj K.U sf := by
    intro i j
    change (F π M).res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (sf i) = (F π M).res (inf_le_right :
      K.U i ⊓ K.U j ≤ K.U j) (sf j)
    rcases lt_trichotomy i j with hij | hij | hji
    · exact hcompat_lt hij
    · subst hij; rfl
    · have := hcompat_lt hji
      have e1 : ∀ (k : K.ι) (hk : K.U i ⊓ K.U j ≤ K.U k) (hk' : K.U j ⊓ K.U i ≤ K.U k) (z : (F π
        M).obj (K.U k)),
          (F π M).res hk z = (F π M).res (le_of_eq (inf_comm (K.U i) (K.U j))) ((F π M).res hk' z)
            := by
        intro k hk hk' z; rw [OModulePresheaf.res_res]
      rw [e1 i inf_le_left inf_le_right, e1 j inf_le_right inf_le_left, this]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (shf M) K.U ⊤ (fun i => homOfLE le_top)
    (K.iSup_eq_top ▸ le_refl _) sf hcompat
  change (F π M).obj ⊤ at s
  refine ⟨s, ?_⟩
  apply Subtype.ext
  funext t
  rw [toH0_apply, idx0_eq K t]
  have hst : (F π M).res (le_top : K.U (t.1 0) ≤ ⊤) s = sf (t.1 0) := hs (t.1 0)
  have e2 : (F π M).res (le_top : K.inter (chain0 K (t.1 0)) ≤ ⊤) s =
      (F π M).res (inter_le_U K (chain0 K (t.1 0))) ((F π M).res (le_top : K.U (t.1 0) ≤ ⊤) s) :=
    ((F π M).res_res (inter_le_U K (chain0 K (t.1 0))) le_top s).symm
  rw [e2, hst, hsf]
  exact ((F π M).res_res (inter_le_U K (chain0 K (t.1 0))) (U_le_inter_chain0 K (t.1 0)) _).trans
    ((F π M).res_refl_apply _ _)

end AC3Aux

end

open AC3Aux in
theorem _root_.AlgebraicGeometry.OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (M : V.Modules) (K : V.OrderedAffineCover) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Nonempty (Γ(M, ⊤) ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K) := by
  exact ⟨LinearEquiv.ofBijective (toH0 π M K) ⟨toH0_injective π M K, toH0_surjective π M K⟩⟩
end AlgebraicCurves.Cohomology.Sheaves.Proofs.GlobalSectionsH0
end ProofImplementation
