/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.TensorSections

/-!
# Scheme Modules is Iso of is Frame On of i Sup eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace N2P4

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {P Q : X.Modules}

theorem map_map (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M,
  V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem app_map (μ : P ⟶ Q) {V W : X.Opens} (h : W ≤ V) (x : Γ(P, V)) :
    μ.app W (P.presheaf.map (homOfLE h).op x) = Q.presheaf.map (homOfLE h).op (μ.app V x) := by
  have := (μ.mapPresheaf).naturality (homOfLE h).op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(P, V) → Γ(Q, W))) this) x

theorem app_injective_of_le (μ : P ⟶ Q) {V : X.Opens} (p : Γ(P, V)) (q : Γ(Q, V))
    (hp : IsFrameOn p V) (hq : IsFrameOn q V) (hμ : μ.app V p = q) {W : X.Opens} (hW : W ≤ V) :
    Function.Injective (μ.app W) := by
  intro x x' hxx'
  obtain ⟨g, rfl⟩ := (hp hW hW).2 x
  obtain ⟨g', rfl⟩ := (hp hW hW).2 x'
  simp only [Scheme.Modules.Hom.app_smul, app_map, hμ] at hxx'
  have := (hq hW hW).1 hxx'
  rw [this]

theorem isIso_of_frames (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  let Wi : ι → X.Opens := fun i => W ⊓ 𝒱 i
  have hcovW : W ≤ ⨆ i, Wi i := by
    intro x hx
    have hx' : x ∈ (⨆ i, 𝒱 i : X.Opens) := by rw [hcov]; trivial
    rw [Opens.mem_iSup] at hx' ⊢
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, ⟨hx, hi⟩⟩
  let FP : TopCat.Sheaf Ab X.carrier := ⟨P.presheaf, P.isSheaf⟩
  let FQ : TopCat.Sheaf Ab X.carrier := ⟨Q.presheaf, Q.isSheaf⟩
  have hinjW : ∀ {W' : X.Opens} (i : ι), W' ≤ 𝒱 i → Function.Injective (μ.app W') :=
    fun i h => app_injective_of_le μ (p i) (q i) (hp i) (hq i) (hμ i) h
  constructor
  · intro x x' h
    apply FP.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcovW
    intro i
    apply hinjW i inf_le_right
    change μ.app (Wi i) (P.presheaf.map (homOfLE inf_le_left).op x) =
      μ.app (Wi i) (P.presheaf.map (homOfLE inf_le_left).op x')
    rw [app_map, app_map]
    exact congrArg _ h
  · intro y
    have hloc : ∀ i, ∃ x : Γ(P, Wi i), μ.app (Wi i) x = Q.presheaf.map (homOfLE inf_le_left).op y
      := by
      intro i
      obtain ⟨g, hg⟩ := (hq i (inf_le_right : Wi i ≤ 𝒱 i) inf_le_right).2
        (Q.presheaf.map (homOfLE inf_le_left).op y)
      refine ⟨g • P.presheaf.map (homOfLE (inf_le_right : Wi i ≤ 𝒱 i)).op (p i), ?_⟩
      rw [Scheme.Modules.Hom.app_smul, app_map, hμ i]
      exact hg
    choose x hx using hloc
    have hcomp : TopCat.Presheaf.IsCompatible FP.1 Wi x := by
      intro i j
      apply hinjW i (inf_le_left.trans inf_le_right)
      change μ.app (Wi i ⊓ Wi j) (P.presheaf.map (homOfLE inf_le_left).op (x i)) =
        μ.app (Wi i ⊓ Wi j) (P.presheaf.map (homOfLE inf_le_right).op (x j))
      rw [app_map, app_map, hx i, hx j, map_map, map_map]
    obtain ⟨s, hs, -⟩ := FP.existsUnique_gluing' Wi W (fun i => homOfLE inf_le_left) hcovW x hcomp
    refine ⟨show Γ(P, W) from s, ?_⟩
    apply FQ.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcovW
    intro i
    change Q.presheaf.map (homOfLE inf_le_left).op (μ.app W s) = Q.presheaf.map (homOfLE
      inf_le_left).op y
    rw [← app_map, ← hx i]
    exact congrArg _ (hs i)

end N2P4

open AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top {X : Scheme.{u}}
  {P Q : X.Modules} (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, Scheme.Modules.IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, Scheme.Modules.IsFrameOn (q i) (𝒱
      i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ :=
  N2P4.isIso_of_frames μ 𝒱 hcov p q hp hq hμ
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
end ProofImplementation
