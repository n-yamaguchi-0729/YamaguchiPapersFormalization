/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensorPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.SchemeTheory.Modules.ProjectivePresentationFromFrames
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_tensorSections

/-!
# Scheme Modules Finite By Sections tensor Pow
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_FiniteBySections_tensorPow

universe u

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace Veronese
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- Restricts a global module section to the specified open subset. -/
abbrev resTop (M : X.Modules) (s : Γ(M, ⊤)) (V : X.Opens) : Γ(M, V) :=
  M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s

theorem resTop_map {M : X.Modules} (s : Γ(M, ⊤)) {V W : X.Opens} (h : W ≤ V) :
    M.presheaf.map (homOfLE h).op (resTop M s V) = resTop M s W := by
  simp only [resTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem isFrameOn_top_iff {M : X.Modules} (s : Γ(M, ⊤)) (V : X.Opens) :
    IsFrameOn s V ↔ ∀ W : X.Opens, W ≤ V →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s :
        Γ(M, W)) :=
  ⟨fun h _W hWV => h le_top hWV, fun h W _ hWV => h W hWV⟩

section Word

variable {M : X.Modules} {U : X.Opens}

/-- The tensor product of a finite ordered list of sections, with the unit section for the empty
list. -/
def wordSection : (n : ℕ) → (Fin n → Γ(M, U)) → Γ(M.tensorPow n, U)
  | 0, _ => unitSection U
  | n + 1, s => tensorSections (L := M.tensorPow n) (M := M)
      (wordSection n (fun k => s k.castSucc)) (s (Fin.last n))

theorem wordSection_zero (s : Fin 0 → Γ(M, U)) : wordSection 0 s = unitSection U := rfl

theorem wordSection_succ (n : ℕ) (s : Fin (n + 1) → Γ(M, U)) :
    wordSection (n + 1) s = tensorSections (L := M.tensorPow n) (M := M)
      (wordSection n (fun k => s k.castSucc)) (s (Fin.last n)) := rfl

theorem map_wordSection {V : X.Opens} (h : V ≤ U) :
    ∀ (n : ℕ) (s : Fin n → Γ(M, U)),
      (M.tensorPow n).presheaf.map (homOfLE h).op (wordSection n s)
        = wordSection n (fun k => M.presheaf.map (homOfLE h).op (s k))
  | 0, s => by
      rw [wordSection_zero, wordSection_zero]
      exact map_unitSection (homOfLE h)
  | n + 1, s => by
      rw [wordSection_succ, wordSection_succ]
      rw [show (M.tensorPow (n + 1)).presheaf.map (homOfLE h).op
          (tensorSections (L := M.tensorPow n) (M := M) (wordSection n fun k => s k.castSucc) (s
            (Fin.last n)))
          = tensorSections (L := M.tensorPow n) (M := M)
              ((M.tensorPow n).presheaf.map (homOfLE h).op (wordSection n fun k => s k.castSucc))
              (M.presheaf.map (homOfLE h).op (s (Fin.last n))) from
        map_homOfLE_tensorSections (L := M.tensorPow n) (M := M) h _ _]
      rw [map_wordSection h n]

theorem wordSection_smul :
    ∀ (n : ℕ) (g : Fin n → Γ(X, U)) (s : Fin n → Γ(M, U)),
      wordSection n (fun k => g k • s k) = (∏ k, g k) • wordSection n s
  | 0, g, s => by
      change unitSection U = (∏ k : Fin 0, g k) • unitSection U
      rw [Fin.prod_univ_zero]
      exact (one_smul Γ(X, U) (unitSection U)).symm
  | n + 1, g, s => by
      rw [wordSection_succ, wordSection_succ, Fin.prod_univ_castSucc]
      rw [show (fun k : Fin n => (fun k => g k • s k) k.castSucc) = fun k => g k.castSucc • s
        k.castSucc from rfl,
        wordSection_smul n, tensorSections_smul_left, tensorSections_smul_right, smul_smul,
          mul_comm]
      rfl

theorem isFrameOn_wordSection {V : X.Opens} :
    ∀ (n : ℕ) (s : Fin n → Γ(M, U)), (∀ k, IsFrameOn (s k) V) → IsFrameOn (wordSection n s) V
  | 0, s, _ => by rw [wordSection_zero]; exact isFrameOn_unitSection V
  | n + 1, s, hs => by
      rw [wordSection_succ]
      exact (isFrameOn_wordSection n _ (fun k => hs k.castSucc)).tensorSections (hs (Fin.last n))

end Word

section Frames

variable {M : X.Modules} {U : X.Opens} {s t : Γ(M, U)} {V : X.Opens}

theorem exists_coef (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (m : Γ(M, W)) :
    ∃ g : Γ(X, W), g • M.presheaf.map (homOfLE hWU).op s = m :=
  (h hWU hWV).2 m

theorem isUnit_of_frame_eq_smul (hs : IsFrameOn s V) (ht : IsFrameOn t V) {W : X.Opens} (hWU : W ≤
  U) (hWV : W ≤ V)
    (g : Γ(X, W)) (hg : M.presheaf.map (homOfLE hWU).op t = g • M.presheaf.map (homOfLE hWU).op s)
      : IsUnit g := by
  obtain ⟨g', hg'⟩ := (ht hWU hWV).2 (M.presheaf.map (homOfLE hWU).op s)
  simp only at hg'
  rw [hg, ← mul_smul] at hg'
  have h1 : g' * g = 1 := (hs hWU hWV).1 (hg'.trans (one_smul _ _).symm)
  exact isUnit_iff_exists_inv'.mpr ⟨g', h1⟩

theorem isFrameOn_of_eq_unit_smul (hs : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V)
    (u : Γ(X, W)) (hu : IsUnit u)
    (ht : M.presheaf.map (homOfLE hWU).op t = u • M.presheaf.map (homOfLE hWU).op s) : IsFrameOn t
      W := by
  intro W' hW'U hW'W
  have ht' : M.presheaf.map (homOfLE hW'U).op t
      = X.presheaf.map (homOfLE hW'W).op u • M.presheaf.map (homOfLE hW'U).op s := by
    have := congrArg (M.presheaf.map (homOfLE hW'W).op) ht
    rw [Modules.map_smul] at this
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at this
    exact this
  set v := X.presheaf.map (homOfLE hW'W).op u with hv
  have hv' : IsUnit v := hu.map _
  obtain ⟨vinv, hv1, hv2⟩ : ∃ vinv, v * vinv = 1 ∧ vinv * v = 1 :=
    ⟨((hv'.unit⁻¹ : Γ(X, W')ˣ) : Γ(X, W')), hv'.mul_val_inv, hv'.val_inv_mul⟩
  have hb : Function.Bijective (fun g : Γ(X, W') => g * v) := by
    refine ⟨fun a c h => ?_, fun y => ⟨y * vinv, ?_⟩⟩
    · have := congr_arg (· * vinv) h
      simpa only [mul_assoc, hv1, mul_one] using this
    · simp only [mul_assoc, hv2, mul_one]
  have key : (fun g : Γ(X, W') => g • M.presheaf.map (homOfLE hW'U).op t)
      = (fun g : Γ(X, W') => g • M.presheaf.map (homOfLE hW'U).op s) ∘ fun g => g * v := by
    funext g
    simp only [Function.comp_apply, ht', mul_smul]
  change Function.Bijective fun g : Γ(X, W') => g • M.presheaf.map (homOfLE hW'U).op t
  rw [key]
  exact (hs hW'U (hW'W.trans hWV)).comp hb

end Frames

section Main

variable {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) (b : ℕ)

local notation "𝒜" n' => MvPolynomial.homogeneousSubmodule (Fin (n' + 1)) R

/-- The preimage of a coordinate basic open under the given projective presentation. -/
abbrev chart (i : Fin (N + 1)) : X.Opens :=
  𝔓.toProj ⁻¹ᵁ Proj.basicOpen (𝒜 N) (MvPolynomial.X i)

/-- The product of coordinate variables indexed by a word of the given length. -/
abbrev wordMonomial (w : Fin b → Fin (N + 1)) : MvPolynomial (Fin (N + 1)) R := ∏ k, MvPolynomial.X
  (w k)

theorem wordMonomial_mem (w : Fin b → Fin (N + 1)) : wordMonomial b w ∈ (𝒜 N) b := by
  have h := SetLike.prod_mem_graded (A := 𝒜 N) (F := (Finset.univ : Finset (Fin b))) (i := fun _ =>
    1)
    (g := fun k => MvPolynomial.X (w k)) (fun k _ => ProjSpace.X_mem_one R N (w k))
  simpa using h

/-- The preimage of the basic open of a word monomial under the projective presentation. -/
abbrev Uw (w : Fin b → Fin (N + 1)) : X.Opens :=
  𝔓.toProj ⁻¹ᵁ Proj.basicOpen (𝒜 N) (wordMonomial b w)
omit 𝔓 in
theorem prod_not_mem_of_forall {A : Type*} [CommRing A] {I : Ideal A} (hI : I.IsPrime) {ι : Type*}
  (F : Finset ι)
    (g : ι → A) (h : ∀ k ∈ F, g k ∉ I) : ∏ k ∈ F, g k ∉ I := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      exact fun h1 => hI.ne_top ((Ideal.eq_top_iff_one I).mpr h1)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro hmul
      rcases hI.mem_or_mem hmul with h1 | h2
      · exact h a (Finset.mem_insert_self a s) h1
      · exact ih (fun k hk => h k (Finset.mem_insert_of_mem hk)) h2

theorem basicOpen_wordMonomial_le (w : Fin b → Fin (N + 1)) (k : Fin b) :
    Proj.basicOpen (𝒜 N) (wordMonomial b w) ≤ Proj.basicOpen (𝒜 N) (MvPolynomial.X (w k)) := by
  intro x hx
  have hx' : wordMonomial b w ∉ x.asHomogeneousIdeal := (Proj.mem_basicOpen (𝒜 N) _ _).mp hx
  refine (Proj.mem_basicOpen (𝒜 N) _ _).mpr fun hk => hx' ?_
  change (∏ k', MvPolynomial.X (w k') : MvPolynomial (Fin (N + 1)) R) ∈ x.asHomogeneousIdeal
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  exact Ideal.mul_mem_right _ x.asHomogeneousIdeal.toIdeal hk

theorem Uw_le_chart (w : Fin b → Fin (N + 1)) (k : Fin b) : Uw 𝔓 b w ≤ chart 𝔓 (w k) :=
  fun _x hx => basicOpen_wordMonomial_le b w k hx

/-- The global tensor-power section indexed by the coordinate sections of a word. -/
abbrev τ (w : Fin b → Fin (N + 1)) : Γ(M.tensorPow b, ⊤) := wordSection b (fun k => 𝔓.σ (w k))

theorem isFrameOn_σ (i : Fin (N + 1)) : IsFrameOn (𝔓.σ i) (chart 𝔓 i) :=
  fun W _ hWV => 𝔓.frame i W hWV

theorem isFrameOn_τ (w : Fin b → Fin (N + 1)) : IsFrameOn (τ 𝔓 b w) (Uw 𝔓 b w) :=
  isFrameOn_wordSection b _ fun k => (isFrameOn_σ 𝔓 (w k)).mono (Uw_le_chart 𝔓 b w k)

theorem iSup_chart : ⨆ i, chart 𝔓 i = ⊤ := by
  have h : ⨆ i : Fin (N + 1), Proj.basicOpen (𝒜 N) (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top (𝒜 N) (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X R
      N)
  apply top_unique
  intro x _
  have hx : 𝔓.toProj.base x ∈ (⊤ : (Proj (𝒜 N)).Opens) := trivial
  rw [← h] at hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

variable (hb : 0 < b)
include hb

theorem Uw_const (i : Fin (N + 1)) : Uw 𝔓 b (fun _ => i) = chart 𝔓 i := by
  change 𝔓.toProj ⁻¹ᵁ _ = 𝔓.toProj ⁻¹ᵁ _
  congr 1
  rw [show wordMonomial b (fun _ : Fin b => i) = MvPolynomial.X i ^ b
    by simp [wordMonomial, Finset.prod_const]]
  exact Proj.basicOpen_pow (𝒜 N) _ b hb

theorem iSup_Uw : ⨆ w : Fin b → Fin (N + 1), Uw 𝔓 b w = ⊤ := by
  apply top_unique
  rw [← iSup_chart 𝔓]
  refine iSup_le fun i => ?_
  rw [← Uw_const 𝔓 b hb i]
  exact le_iSup (fun w : Fin b → Fin (N + 1) => Uw 𝔓 b w) (fun _ => i)

theorem isAffineOpen_Uw [IsAffineHom 𝔓.toProj] (w : Fin b → Fin (N + 1)) : IsAffineOpen (Uw 𝔓 b w)
  := by
  have haff : IsAffineOpen (Proj.basicOpen (𝒜 N) (wordMonomial b w)) := by
    rw [← Proj.opensRange_awayι (𝒜 N) (wordMonomial b w) (wordMonomial_mem b w) hb]
    exact isAffineOpen_opensRange _
  exact haff.preimage 𝔓.toProj
omit hb in
theorem mem_chart_of_isFrameOn_τ (w : Fin b → Fin (N + 1)) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (hτ : IsFrameOn (τ 𝔓 b w) U) (k : Fin b) : x ∈ chart 𝔓 (w k) := by
  have hxX : x ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_chart 𝔓] at hxX
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxX
  let W : X.Opens := U ⊓ chart 𝔓 j
  have hxW : x ∈ W := ⟨hxU, hj⟩
  have hσj : IsFrameOn (𝔓.σ j) W := (isFrameOn_σ 𝔓 j).mono inf_le_right
  choose g hg using fun k' => exists_coef hσj (le_top : W ≤ ⊤) le_rfl (resTop M (𝔓.σ (w k')) W)
  have hτW : resTop (M.tensorPow b) (τ 𝔓 b w) W
      = (∏ k', g k') • resTop (M.tensorPow b) (wordSection b fun _ : Fin b => 𝔓.σ j) W := by
    rw [resTop, resTop, map_wordSection, map_wordSection]
    rw [← wordSection_smul]
    congr 1
    funext k'
    exact (hg k').symm
  have hfrj : IsFrameOn (wordSection b fun _ : Fin b => 𝔓.σ j) W :=
    isFrameOn_wordSection b _ fun _ => hσj
  have hunit : IsUnit (∏ k', g k') :=
    isUnit_of_frame_eq_smul hfrj (hτ.mono inf_le_left) (le_top : W ≤ ⊤) le_rfl _ hτW
  have hgk : IsUnit (g k) :=
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem g (Finset.mem_univ k)) hunit
  have hσk : IsFrameOn (𝔓.σ (w k)) W :=
    isFrameOn_of_eq_unit_smul hσj (le_top : W ≤ ⊤) le_rfl (g k) hgk (hg k).symm
  exact (𝔓.mem_preimage_basicOpen_iff (w k) x).mpr ⟨W, hxW, fun V hV => hσk le_top hV⟩

theorem finiteBySections_tensorPow [IsProper f] (hfin : IsFinite 𝔓.toProj) :
    (M.tensorPow b).FiniteBySections f := by
  classical
  set N' : ℕ := (N + 1) ^ b - 1 with hN'
  have hN'1 : N' + 1 = (N + 1) ^ b := Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.succ_pos N))
  let e : Fin (N' + 1) ≃ (Fin b → Fin (N + 1)) := (finCongr hN'1).trans finFunctionFinEquiv.symm
  obtain ⟨𝔔, hσ, hU⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top f (M.tensorPow b) N'
    (fun j => τ 𝔓 b (e j)) (fun j => Uw 𝔓 b (e j))
    (by
      rw [← top_le_iff, ← iSup_Uw 𝔓 b hb]
      refine iSup_le fun w => ?_
      have := le_iSup (fun j => Uw 𝔓 b (e j)) (e.symm w)
      rwa [Equiv.apply_symm_apply] at this)
    (fun j V hV => (isFrameOn_τ 𝔓 b (e j)) le_top hV)
  refine ⟨N', 𝔔, ?_⟩
  have : IsAffineHom 𝔓.toProj := inferInstance
  have hchart : ∀ j : Fin (N' + 1),
      𝔔.toProj ⁻¹ᵁ Proj.basicOpen (𝒜 N') (MvPolynomial.X j) = Uw 𝔓 b (e j) := by
    intro j
    refine le_antisymm (fun x hx => ?_) (hU j)
    obtain ⟨U, hxU, hfr⟩ := (𝔔.mem_preimage_basicOpen_iff j x).mp hx
    have hτ : IsFrameOn (τ 𝔓 b (e j)) U := by
      rw [isFrameOn_top_iff]
      intro W hW
      have := hfr W hW
      rwa [hσ] at this
    have hmem : ∀ k, x ∈ chart 𝔓 (e j k) := fun k => mem_chart_of_isFrameOn_τ 𝔓 b (e j) x U hxU hτ k
    change 𝔓.toProj.base x ∈ Proj.basicOpen (𝒜 N) (wordMonomial b (e j))
    have hmem' : ∀ k, MvPolynomial.X (e j k) ∉ (𝔓.toProj.base x).asHomogeneousIdeal := fun k => by
      have := hmem k
      exact (Proj.mem_basicOpen (𝒜 N) _ _).mp this
    refine (Proj.mem_basicOpen (𝒜 N) _ _).mpr ?_
    exact prod_not_mem_of_forall (I := (𝔓.toProj.base x).asHomogeneousIdeal.toIdeal) (𝔓.toProj.base
      x).isPrime
      Finset.univ (fun k => MvPolynomial.X (e j k)) (fun k _ => hmem' k)
  have haff : IsAffineHom 𝔔.toProj := by
    let Uc : Fin (N' + 1) → (Proj (𝒜 N')).affineOpens := fun j =>
      ⟨Proj.basicOpen (𝒜 N') (MvPolynomial.X j), by
        rw [← Proj.opensRange_awayι (𝒜 N') (MvPolynomial.X j) (ProjSpace.X_mem_one R N' j) one_pos]
        exact isAffineOpen_opensRange _⟩
    have hUc : ⨆ j, (Uc j : (Proj (𝒜 N')).Opens) = ⊤ :=
      Proj.iSup_basicOpen_eq_top (𝒜 N') (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X
        R N')
    refine isAffineHom_of_forall_exists_isAffineOpen 𝔔.toProj fun x => ?_
    have hx : x ∈ (⊤ : (Proj (𝒜 N')).Opens) := trivial
    rw [← hUc] at hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    refine ⟨Uc j, hj, (Uc j).2, ?_⟩
    change IsAffineOpen (𝔔.toProj ⁻¹ᵁ Proj.basicOpen (𝒜 N') (MvPolynomial.X j))
    rw [hchart j]
    exact isAffineOpen_Uw 𝔓 b hb (e j)
  have hsep : IsSeparated (ProjSpace.π R N') := inferInstance
  have hprop : IsProper 𝔔.toProj := by
    have : IsProper (𝔔.toProj ≫ ProjSpace.π R N') := by rw [𝔔.toProj_π]; infer_instance
    exact IsProper.of_comp 𝔔.toProj (ProjSpace.π R N')
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hprop, haff⟩

end Main

end AlgebraicGeometry.Scheme.Modules.Veronese

end

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.FiniteBySections.tensorPow
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    {M : X.Modules} (hM : M.FiniteBySections f) {b : ℕ} (hb : 0 < b) :
    (M.tensorPow b).FiniteBySections f := by
  obtain ⟨N, 𝔓, hfin⟩ := hM
  exact Scheme.Modules.Veronese.finiteBySections_tensorPow 𝔓 b hb hfin
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_FiniteBySections_tensorPow
end ProofImplementation

attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
