/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_AffSES_exists_connectingHom

/-!
# OModule Presheaf Aff SES injective inc HSucc Map of forall subsingleton HSucc of
surjective proj H0Map
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.InjectiveCohomology

open AlgebraicGeometry

universe u

namespace RM3SOL

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
  {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)

theorem injective_HSuccMap_succ (i : ℕ) [Subsingleton (F₃.HSucc K i)] :
    Function.Injective (S.inc.HSuccMap K (i + 1)) := by
  obtain ⟨δ₀, δ, -, -, -, h4⟩ := S.exists_connectingHom K
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := h4 i hx
  rw [Subsingleton.elim y 0, map_zero]
  exact Submodule.zero_mem _

theorem cochainMap_inc_injective (i : ℕ) : Function.Injective (S.inc.cochainMap K i) := by
  intro f g h
  funext s
  apply S.injective (K.affineInter π s)
  have := congr_fun h s
  rwa [AffHom.cochainMap_apply, AffHom.cochainMap_apply] at this

theorem cochainMap_proj_inc (i : ℕ) (f : F₁.cochain K i) :
    S.proj.cochainMap K i (S.inc.cochainMap K i f) = 0 := by
  funext s
  rw [AffHom.cochainMap_apply, AffHom.cochainMap_apply, Pi.zero_apply, ← LinearMap.mem_ker, ←
    S.exact]
  exact ⟨f s, rfl⟩

theorem exists_cochainMap_inc_eq (i : ℕ) (g : F₂.cochain K i) (hg : S.proj.cochainMap K i g = 0) :
    ∃ f : F₁.cochain K i, S.inc.cochainMap K i f = g := by
  have h : ∀ s : K.Idx i, ∃ x : F₁.obj (K.inter s), S.inc.app (K.affineInter π s) x = g s := by
    intro s
    have hs : g s ∈ LinearMap.ker (S.proj.app (K.affineInter π s)) := by
      rw [LinearMap.mem_ker, ← AffHom.cochainMap_apply, hg, Pi.zero_apply]
    rw [← S.exact] at hs
    exact hs
  choose f hf using h
  exact ⟨f, funext fun s => by rw [AffHom.cochainMap_apply, hf]⟩

theorem injective_HSuccMap_zero (hs : Function.Surjective (S.proj.H0Map K)) :
    Function.Injective (S.inc.HSuccMap K 0) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [LinearMap.mem_ker, Submodule.mkQ_apply, AffHom.HSuccMap_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at hx
  obtain ⟨y, hy⟩ := hx
  rw [Submodule.subtype_apply, AffHom.kerMap_coe] at hy
  have hp : S.proj.cochainMap K 0 y ∈ F₃.H0 K := by
    change F₃.d K 0 (S.proj.cochainMap K 0 y) = 0
    rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply, hy,
      cochainMap_proj_inc]
  obtain ⟨y', hy'⟩ := hs ⟨_, hp⟩
  have hy'v : S.proj.cochainMap K 0 (y'.1) = S.proj.cochainMap K 0 y := by
    have := congr_arg Subtype.val hy'
    rwa [AffHom.kerMap_coe] at this
  obtain ⟨w, hw⟩ := exists_cochainMap_inc_eq S K 0 (y - y'.1) (by rw [map_sub, hy'v, sub_self])
  have hdw : S.inc.cochainMap K 1 (F₁.d K 0 w) = S.inc.cochainMap K 1 z.1 := by
    rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hw, map_sub, hy,
      LinearMap.mem_ker.1 y'.2, sub_zero]
  have := cochainMap_inc_injective S K 1 hdw
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact ⟨w, by rw [Submodule.subtype_apply]; exact this⟩

end RM3SOL

end AlgebraicCurves.Cohomology.Sheaves.Proofs.InjectiveCohomology

section
universe u
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs.InjectiveCohomology
namespace AlgebraicGeometry.OModulePresheaf

theorem AffSES.injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₃ : ∀ i : ℕ, Subsingleton (F₃.HSucc K i))
    (hsurj : Function.Surjective (S.proj.H0Map K)) :
    ∀ i : ℕ, Function.Injective (S.inc.HSuccMap K i) := by
  intro i
  cases i with
  | zero => exact RM3SOL.injective_HSuccMap_zero S K hsurj
  | succ i => have := h₃ i; exact RM3SOL.injective_HSuccMap_succ S K i
end AlgebraicGeometry.OModulePresheaf
end
end ProofImplementation
