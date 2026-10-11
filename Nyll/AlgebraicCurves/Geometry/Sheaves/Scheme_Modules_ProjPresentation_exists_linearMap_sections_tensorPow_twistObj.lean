/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_tensorPowSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_tensorPowSection_smul

/-!
# Scheme Modules Proj Presentation exists linear Map sections tensor Pow twist Obj
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj

universe u

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace S1Sketch

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

/-- Restricts a module section along an inclusion of open subsets. -/
noncomputable abbrev rM (M : X.Modules) {W W' : X.Opens} (h : W ≤ W') : Γ(M, W') → Γ(M, W) :=
  fun x => M.presheaf.map (homOfLE h).op x

/-- Restricts a structure-sheaf section along an inclusion of open subsets. -/
noncomputable abbrev rO {W W' : X.Opens} (h : W ≤ W') : Γ(X, W') → Γ(X, W) :=
  fun a => X.presheaf.map (homOfLE h).op a

theorem rM_rM (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (h₁ : W₁ ≤ W₂) (h₂ : W₂ ≤ W₃) (x : Γ(M, W₃)) :
    rM M h₁ (rM M h₂ x) = rM M (h₁.trans h₂) x := by
  change (M.presheaf.map _ ≫ M.presheaf.map _) x = _
  rw [← M.presheaf.map_comp]
  rfl

theorem rM_irrel (M : X.Modules) {W₁ W₂ : X.Opens} (h h' : W₁ ≤ W₂) (x : Γ(M, W₂)) : rM M h x = rM
  M h' x := rfl

theorem rM_refl (M : X.Modules) {W : X.Opens} (h : W ≤ W) (x : Γ(M, W)) : rM M h x = x := by
  change (M.presheaf.map (homOfLE h).op) x = x
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op W)), M.presheaf.map_id]
  rfl

theorem rM_smul (M : X.Modules) {W W' : X.Opens} (h : W ≤ W') (a : Γ(X, W')) (x : Γ(M, W')) :
    rM M h (a • x) = rO h a • rM M h x :=
  Scheme.Modules.map_smul M (homOfLE h) a x

theorem rM_add (M : X.Modules) {W W' : X.Opens} (h : W ≤ W') (x y : Γ(M, W')) :
    rM M h (x + y) = rM M h x + rM M h y := map_add _ _ _

theorem rM_bijective_of_ge (M : X.Modules) {W W' : X.Opens} (h : W ≤ W') (h' : W' ≤ W) :
    Function.Bijective (rM M h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨rM M h', fun x => ?_, fun x => ?_⟩
  · show rM M h' (rM M h x) = x
    rw [rM_rM, rM_refl]
  · show rM M h (rM M h' x) = x
    rw [rM_rM, rM_refl]

theorem rO_rO {W₁ W₂ W₃ : X.Opens} (h₁ : W₁ ≤ W₂) (h₂ : W₂ ≤ W₃) (a : Γ(X, W₃)) :
    rO h₁ (rO h₂ a) = rO (h₁.trans h₂) a := by
  change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
  rw [← X.presheaf.map_comp]
  rfl

theorem rO_irrel {W₁ W₂ : X.Opens} (h h' : W₁ ≤ W₂) (a : Γ(X, W₂)) : rO h a = rO h' a := rfl

theorem rO_pow {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) (a : Γ(X, W₂)) (n : ℕ) : rO h (a ^ n) = rO h a ^ n
  := by
  change (X.presheaf.map (homOfLE h).op) (a ^ n) = ((X.presheaf.map (homOfLE h).op) a) ^ n
  exact map_pow _ a n

theorem rO_mul {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) (a b : Γ(X, W₂)) : rO h (a * b) = rO h a * rO h b :=
  by
  change (X.presheaf.map (homOfLE h).op) (a * b) = (X.presheaf.map (homOfLE h).op) a *
    (X.presheaf.map (homOfLE h).op) b
  exact map_mul _ a b

/-- The unique scalar coefficient of a section with respect to a frame on the given open subset. -/
noncomputable def coef {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {W : X.Opens} (hWU : W ≤
  U) (hWV : W ≤ V)
    (x : Γ(M, W)) : Γ(X, W) :=
  Classical.choose (hs.existsUnique hWU hWV x).exists

theorem coef_smul {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U)
  (hWV : W ≤ V)
    (x : Γ(M, W)) : coef hs hWU hWV x • rM M hWU s = x :=
  Classical.choose_spec (hs.existsUnique hWU hWV x).exists

theorem coef_unique {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U)
  (hWV : W ≤ V)
    (x : Γ(M, W)) (g : Γ(X, W)) (hg : g • rM M hWU s = x) : g = coef hs hWU hWV x :=
  (hs.existsUnique hWU hWV x).unique hg (coef_smul hs hWU hWV x)

theorem coef_eq_iff {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U)
  (hWV : W ≤ V)
    (x : Γ(M, W)) (g : Γ(X, W)) : coef hs hWU hWV x = g ↔ g • rM M hWU s = x :=
  ⟨fun h => h ▸ coef_smul hs hWU hWV x, fun h => (coef_unique hs hWU hWV x g h).symm⟩

theorem coef_add {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U)
  (hWV : W ≤ V)
    (x y : Γ(M, W)) : coef hs hWU hWV (x + y) = coef hs hWU hWV x + coef hs hWU hWV y := by
  rw [coef_eq_iff, add_smul, coef_smul, coef_smul]

theorem coef_mul_smul {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {W : X.Opens} (hWU : W ≤
  U) (hWV : W ≤ V)
    (a : Γ(X, W)) (x : Γ(M, W)) : coef hs hWU hWV (a • x) = a * coef hs hWU hWV x := by
  rw [coef_eq_iff, mul_smul, coef_smul]

theorem rO_coef {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {W W' : X.Opens} (hWU : W' ≤ U)
  (hWV : W' ≤ V)
    (h : W ≤ W') (x : Γ(M, W')) :
    rO h (coef hs hWU hWV x) = coef hs (h.trans hWU) (h.trans hWV) (rM M h x) := by
  apply coef_unique
  rw [← rM_rM M h hWU s, ← rM_smul, coef_smul]

theorem coef_eq_mul_coef {U U' V V' : X.Opens} {s : Γ(M, U)} {s' : Γ(M, U')} (hs : IsFrameOn s V)
  (hs' : IsFrameOn s' V')
    {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (hWU' : W ≤ U') (hWV' : W ≤ V') (u : Γ(X, W))
    (hu : rM M hWU' s' = u • rM M hWU s) (x : Γ(M, W)) :
    coef hs hWU hWV x = coef hs' hWU' hWV' x * u := by
  rw [coef_eq_iff, mul_smul, ← hu, coef_smul]

end S1Sketch

namespace S1Sketch

open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} {L :
  X.Modules}
  (𝔓 : L.ProjPresentation f N) (m : ℕ)

/-- The inverse image of a standard projective chart under the projective presentation. -/
noncomputable abbrev Uc (i : Fin (N + 1)) : X.Opens := pullbackChart 𝔓.toProj i

theorem isFrameOn_σ (i : Fin (N + 1)) : IsFrameOn (𝔓.σ i) (Uc 𝔓 i) :=
  fun W _hWU hWV => 𝔓.frame i W hWV

/-- The tensor power of the global section providing the frame on the chosen projective chart. -/
noncomputable abbrev τ (i : Fin (N + 1)) : Γ(L.tensorPow m, ⊤) := tensorPowSection (𝔓.σ i) m

theorem isFrameOn_τ (i : Fin (N + 1)) : IsFrameOn (τ 𝔓 m i) (Uc 𝔓 i) :=
  (isFrameOn_σ 𝔓 i).tensorPowSection m

theorem σ_rel (i j : Fin (N + 1)) :
    rM L (le_top : Uc 𝔓 i ≤ ⊤) (𝔓.σ j) = frameUnit 𝔓.toProj i j • rM L (le_top : Uc 𝔓 i ≤ ⊤) (𝔓.σ
      i) :=
  (𝔓.app_ratio_smul i j).symm

theorem τ_rel (i j : Fin (N + 1)) :
    rM (L.tensorPow m) (le_top : Uc 𝔓 i ≤ ⊤) (τ 𝔓 m j) =
      frameUnit 𝔓.toProj i j ^ m • rM (L.tensorPow m) (le_top : Uc 𝔓 i ≤ ⊤) (τ 𝔓 m i) := by
  change (L.tensorPow m).presheaf.map (homOfLE le_top).op (tensorPowSection (𝔓.σ j) m) =
    frameUnit 𝔓.toProj i j ^ m • (L.tensorPow m).presheaf.map (homOfLE le_top).op (tensorPowSection
      (𝔓.σ i) m)
  rw [map_tensorPowSection, map_tensorPowSection, ← tensorPowSection_smul]
  exact congrArg (fun s => tensorPowSection s m) (σ_rel 𝔓 i j)

theorem τ_rel_on (i j : Fin (N + 1)) {W : X.Opens} (hW : W ≤ Uc 𝔓 i) :
    rM (L.tensorPow m) (le_top : W ≤ ⊤) (τ 𝔓 m j) =
      rO hW (frameUnit 𝔓.toProj i j) ^ m • rM (L.tensorPow m) (le_top : W ≤ ⊤) (τ 𝔓 m i) := by
  rw [← rM_rM (L.tensorPow m) hW le_top (τ 𝔓 m j), τ_rel, rM_smul, rO_pow, rM_rM]

/-- The local coefficient of a tensor-power section on the intersection with a projective chart. -/
noncomputable def gcoef (U : X.Opens) (x : Γ(L.tensorPow m, U)) (i : Fin (N + 1)) : Γ(X, U ⊓ Uc 𝔓
  i) :=
  coef (isFrameOn_τ 𝔓 m i) (le_top : U ⊓ Uc 𝔓 i ≤ ⊤) inf_le_right (rM (L.tensorPow m) inf_le_left x)

theorem gcoef_spec (U : X.Opens) (x : Γ(L.tensorPow m, U)) (i : Fin (N + 1)) :
    gcoef 𝔓 m U x i • rM (L.tensorPow m) (le_top : U ⊓ Uc 𝔓 i ≤ ⊤) (τ 𝔓 m i) = rM (L.tensorPow m)
      inf_le_left x :=
  coef_smul _ _ _ _

theorem rO_gcoef_eq (U : X.Opens) (x : Γ(L.tensorPow m, U)) (i j : Fin (N + 1)) {W : X.Opens}
    (hi : W ≤ U ⊓ Uc 𝔓 i) (hj : W ≤ U ⊓ Uc 𝔓 j) :
    rO hi (gcoef 𝔓 m U x i) = rO (hi.trans inf_le_right) (frameUnit 𝔓.toProj i j) ^ m * rO hj
      (gcoef 𝔓 m U x j) := by
  rw [gcoef, gcoef, rO_coef, rO_coef, rM_rM, rM_rM, mul_comm]
  exact coef_eq_mul_coef (isFrameOn_τ 𝔓 m i) (isFrameOn_τ 𝔓 m j) _ _ _ _ _
    (τ_rel_on 𝔓 m i j (hi.trans inf_le_right)) _

theorem gcoef_compat (U : X.Opens) (x : Γ(L.tensorPow m, U)) : TwistCompat 𝔓.toProj m U (gcoef 𝔓 m
  U x) :=
  fun i j => rO_gcoef_eq 𝔓 m U x i j _ _

theorem gcoef_add (U : X.Opens) (x y : Γ(L.tensorPow m, U)) (i : Fin (N + 1)) :
    gcoef 𝔓 m U (x + y) i = gcoef 𝔓 m U x i + gcoef 𝔓 m U y i := by
  rw [gcoef, rM_add, coef_add]; rfl

theorem gcoef_smul (U : X.Opens) (a : Γ(X, U)) (x : Γ(L.tensorPow m, U)) (i : Fin (N + 1)) :
    gcoef 𝔓 m U (a • x) i = rO inf_le_left a * gcoef 𝔓 m U x i := by
  rw [gcoef, rM_smul, coef_mul_smul]; rfl

/-- The linear map from tensor-power sections to compatible twist sections given by their chart
coefficients. -/
noncomputable def eMap (U : X.Opens) : Γ(L.tensorPow m, U) →ₗ[Γ(X, U)] twistObj f 𝔓.toProj m U where
  toFun x := ⟨gcoef 𝔓 m U x, gcoef_compat 𝔓 m U x⟩
  map_add' x y := twistObj.ext (funext fun i => by
    change gcoef 𝔓 m U (x + y) i = gcoef 𝔓 m U x i + gcoef 𝔓 m U y i
    exact gcoef_add 𝔓 m U x y i)
  map_smul' a x := twistObj.ext (funext fun i => by
    change gcoef 𝔓 m U (a • x) i = restrictFun inf_le_left a * gcoef 𝔓 m U x i
    exact gcoef_smul 𝔓 m U a x i)

@[scoped simp] theorem eMap_val (U : X.Opens) (x : Γ(L.tensorPow m, U)) : (eMap 𝔓 m U x).val =
  gcoef 𝔓 m U x := rfl

theorem eMap_res (U U' : X.Opens) (h : U ≤ U') (x : Γ(L.tensorPow m, U')) :
    eMap 𝔓 m U (rM (L.tensorPow m) h x) = twistRes f 𝔓.toProj m h (eMap 𝔓 m U' x) := by
  refine twistObj.ext (funext fun i => ?_)
  rw [twistRes_val]
  change gcoef 𝔓 m U (rM (L.tensorPow m) h x) i = rO _ (gcoef 𝔓 m U' x i)
  rw [gcoef, gcoef, rO_coef, rM_rM, rM_rM]

theorem eMap_bijective (U : X.Opens) (i₀ : Fin (N + 1)) (hU : U ≤ Uc 𝔓 i₀) : Function.Bijective
  (eMap 𝔓 m U) := by
  have hUU : U ≤ U ⊓ Uc 𝔓 i₀ := le_inf le_rfl hU
  have hres := rM_bijective_of_ge (L.tensorPow m) (inf_le_left : U ⊓ Uc 𝔓 i₀ ≤ U) hUU
  constructor
  · intro x y hxy
    have h0 : gcoef 𝔓 m U x i₀ = gcoef 𝔓 m U y i₀ := by
      have := congrArg (fun t => twistObj.val t i₀) hxy
      simpa using this
    apply hres.1
    show rM (L.tensorPow m) inf_le_left x = rM (L.tensorPow m) inf_le_left y
    rw [← gcoef_spec 𝔓 m U x i₀, ← gcoef_spec 𝔓 m U y i₀, h0]
  · intro t
    refine ⟨rM (L.tensorPow m) hUU (t.val i₀ • rM (L.tensorPow m) (le_top : U ⊓ Uc 𝔓 i₀ ≤ ⊤) (τ 𝔓 m
      i₀)), ?_⟩
    refine twistObj.ext (funext fun i => ?_)
    change gcoef 𝔓 m U _ i = t.val i
    have hW : U ⊓ Uc 𝔓 i ≤ (U ⊓ Uc 𝔓 i) ⊓ Uc 𝔓 i₀ := le_inf le_rfl (inf_le_left.trans hU)
    have hinj := (rM_bijective_of_ge (L.tensorPow m) (inf_le_left : (U ⊓ Uc 𝔓 i) ⊓ Uc 𝔓 i₀ ≤ U ⊓ Uc
      𝔓 i) hW).1
    symm
    apply coef_unique
    apply hinj
    change rM (L.tensorPow m) inf_le_left (t.val i • rM (L.tensorPow m) le_top (τ 𝔓 m i)) =
      rM (L.tensorPow m) inf_le_left (rM (L.tensorPow m) inf_le_left
        (rM (L.tensorPow m) hUU (t.val i₀ • rM (L.tensorPow m) le_top (τ 𝔓 m i₀))))
    have h₁ : (U ⊓ Uc 𝔓 i) ⊓ Uc 𝔓 i₀ ≤ U ⊓ Uc 𝔓 i := inf_le_left
    have h₂ : (U ⊓ Uc 𝔓 i) ⊓ Uc 𝔓 i₀ ≤ U ⊓ Uc 𝔓 i₀ := le_inf (inf_le_left.trans inf_le_left)
      inf_le_right
    have hWi : (U ⊓ Uc 𝔓 i) ⊓ Uc 𝔓 i₀ ≤ Uc 𝔓 i := inf_le_left.trans inf_le_right
    have e1 : rM (L.tensorPow m) h₁ (t.val i • rM (L.tensorPow m) le_top (τ 𝔓 m i)) =
        rO h₁ (t.val i) • rM (L.tensorPow m) (le_top : (U ⊓ Uc 𝔓 i) ⊓ Uc 𝔓 i₀ ≤ ⊤) (τ 𝔓 m i) := by
      rw [rM_smul, rM_rM]
    have e2 : rM (L.tensorPow m) h₁ (rM (L.tensorPow m) inf_le_left
        (rM (L.tensorPow m) hUU (t.val i₀ • rM (L.tensorPow m) le_top (τ 𝔓 m i₀)))) =
        rO h₂ (t.val i₀) • rM (L.tensorPow m) (le_top : (U ⊓ Uc 𝔓 i) ⊓ Uc 𝔓 i₀ ≤ ⊤) (τ 𝔓 m i₀) := by
      rw [rM_rM, rM_rM, rM_smul, rM_rM]
    have e3 := τ_rel_on 𝔓 m i i₀ hWi
    have hc' : rO h₁ (t.val i) = rO hWi (frameUnit 𝔓.toProj i i₀) ^ m * rO h₂ (t.val i₀) :=
      t.compat i i₀
    rw [e1, e2, e3, ← mul_smul, hc', mul_comm]

theorem main :
    ∃ e : ∀ U : X.Opens, Γ(L.tensorPow m, U) →ₗ[Γ(X, U)] twistObj f 𝔓.toProj m U,
      (∀ (U : X.Opens) (x : Γ(L.tensorPow m, U)) (i : Fin (N + 1)),
          ((e U x).val i) •
              (L.tensorPow m).presheaf.map (homOfLE (le_top : U ⊓ pullbackChart 𝔓.toProj i ≤ ⊤)).op
                (tensorPowSection (𝔓.σ i) m) =
            (L.tensorPow m).presheaf.map (homOfLE (inf_le_left : U ⊓ pullbackChart 𝔓.toProj i ≤
              U)).op x) ∧
      (∀ (U U' : X.Opens) (h : U ≤ U') (x : Γ(L.tensorPow m, U')),
          e U ((L.tensorPow m).presheaf.map (homOfLE h).op x) = twistRes f 𝔓.toProj m h (e U' x)) ∧
      (∀ (U : X.Opens) (i : Fin (N + 1)), U ≤ pullbackChart 𝔓.toProj i → Function.Bijective (e U))
        :=
  ⟨eMap 𝔓 m, fun U x i => gcoef_spec 𝔓 m U x i, fun U U' h x => eMap_res 𝔓 m U U' h x,
    fun U i hU => eMap_bijective 𝔓 m U i hU⟩

end S1Sketch

end Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry

universe u

open CategoryTheory Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj in
open S1Sketch in
theorem Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} {L :
      X.Modules}
    (𝔓 : L.ProjPresentation f N) (m : ℕ) :
    ∃ e : ∀ U : X.Opens, Γ(L.tensorPow m, U) →ₗ[Γ(X, U)] ProjSpace.twistObj f 𝔓.toProj m U,
      (∀ (U : X.Opens) (x : Γ(L.tensorPow m, U)) (i : Fin (N + 1)),
          ((e U x).val i) •
              (L.tensorPow m).presheaf.map (homOfLE (le_top : U ⊓ ProjSpace.pullbackChart 𝔓.toProj
                i ≤ ⊤)).op
                (Scheme.Modules.tensorPowSection (𝔓.σ i) m) =
            (L.tensorPow m).presheaf.map (homOfLE (inf_le_left : U ⊓ ProjSpace.pullbackChart
              𝔓.toProj i ≤ U)).op x) ∧
      (∀ (U U' : X.Opens) (h : U ≤ U') (x : Γ(L.tensorPow m, U')),
          e U ((L.tensorPow m).presheaf.map (homOfLE h).op x) = ProjSpace.twistRes f 𝔓.toProj m h
            (e U' x)) ∧
      (∀ (U : X.Opens) (i : Fin (N + 1)), U ≤ ProjSpace.pullbackChart 𝔓.toProj i →
        Function.Bijective (e U)) :=
  main 𝔓 m
end AlgebraicGeometry
end ProofImplementation
