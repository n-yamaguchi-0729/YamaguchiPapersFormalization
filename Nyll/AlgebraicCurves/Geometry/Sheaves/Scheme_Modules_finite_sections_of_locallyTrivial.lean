/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Span
import Nyll.SchemeTheory.Modules.LocallyTrivialSectionsLocalization

/-!
# Finite section modules of locally trivial sheaves

Local trivializations on basic opens and a finite affine cover provide finite generation
of module sections over an affine open.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_finite_sections_of_locallyTrivial

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

/-- The surjectivity and torsion conditions for restricting sections to a basic open. -/
def LocProp {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) (g : Γ(X, V)) : Prop :=
  (∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, V)),
      M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
        = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
    ∧ (∀ y : Γ(M, V), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
        ∃ n : ℕ, (g ^ n : Γ(X, V)) • y = 0)

namespace LocTriv

variable {X : Scheme.{u}} (M : X.Modules)

/-- Restriction of module sections along an inclusion of opens. -/
noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map
    (homOfLE h).op y

/-- Restriction of ring sections along an inclusion of opens. -/
noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) := fun g => X.presheaf.map
    (homOfLE h).op g

theorem rM_rM {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

omit M in
theorem rO_rO {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (g : Γ(X, V₁)) :
    rO h₃₂ (rO h₂₁ g) = rO (h₃₂.trans h₂₁) g := by
  change (X.presheaf.map (homOfLE h₂₁).op ≫ X.presheaf.map (homOfLE h₃₂).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rM_self {V : X.Opens} (h : V ≤ V) (y : Γ(M, V)) : rM M h y = y := by
  change (M.presheaf.map (homOfLE h).op) y = y
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, M.presheaf.map_id]; rfl

omit M in
theorem rO_self {V : X.Opens} (h : V ≤ V) (g : Γ(X, V)) : rO h g = g := by
  change (X.presheaf.map (homOfLE h).op).hom g = g
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, X.presheaf.map_id]; rfl

theorem rM_smul {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (y : Γ(M, W)) :
    rM M h (g • y) = rO h g • rM M h y := M.map_smul _ _ _

section Transport

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem hat_eq {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWV]

theorem le_hat {W : X.Opens} (hWV : W ≤ V) : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ W := (hat_eq V hWV).ge
theorem hat_le {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W ≤ W := (hat_eq V hWV).le

/-- The section map induced by the chosen local trivialization. -/
noncomputable def eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.hom.app (V.ι ⁻¹ᵁ W)).hom m

/-- The inverse section map induced by the chosen local trivialization. -/
noncomputable def eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.inv.app (V.ι ⁻¹ᵁ W)).hom a

theorem eInv_eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eInv M V e W (eApp M V e W m) = m :=
  by
  change (e.hom.app (V.ι ⁻¹ᵁ W) ≫ e.inv.app (V.ι ⁻¹ᵁ W)).hom m = m
  have hc : e.hom.app (V.ι ⁻¹ᵁ W) ≫ e.inv.app (V.ι ⁻¹ᵁ W) =
      Modules.Hom.app (X := V.toScheme) (𝟙 (M.restrict V.ι)) (V.ι ⁻¹ᵁ W) :=
    (Modules.Hom.comp_app (U := V.ι ⁻¹ᵁ W) e.hom e.inv).symm.trans
      (congrArg (fun φ : M.restrict V.ι ⟶ M.restrict V.ι => Modules.Hom.app (X := V.toScheme) φ (V.ι
          ⁻¹ᵁ W)) e.hom_inv_id)
  exact ConcreteCategory.congr_hom
    (hc.trans (Modules.Hom.id_app (U := V.ι ⁻¹ᵁ W) (M.restrict V.ι))) m

theorem eApp_eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eApp M V e W (eInv M V e W a) = a :=
  by
  change (e.inv.app (V.ι ⁻¹ᵁ W) ≫ e.hom.app (V.ι ⁻¹ᵁ W)).hom a = a
  have hc : e.inv.app (V.ι ⁻¹ᵁ W) ≫ e.hom.app (V.ι ⁻¹ᵁ W) =
      Modules.Hom.app (X := V.toScheme) (𝟙 (SheafOfModules.unit V.toScheme.ringCatSheaf)) (V.ι ⁻¹ᵁ
          W) :=
    (Modules.Hom.comp_app (U := V.ι ⁻¹ᵁ W) e.inv e.hom).symm.trans
      (congrArg (fun φ : SheafOfModules.unit V.toScheme.ringCatSheaf ⟶
        SheafOfModules.unit V.toScheme.ringCatSheaf => Modules.Hom.app (X := V.toScheme) φ (V.ι ⁻¹ᵁ
            W)) e.inv_hom_id)
  exact ConcreteCategory.congr_hom
    (hc.trans (Modules.Hom.id_app (U := V.ι ⁻¹ᵁ W)
      (SheafOfModules.unit V.toScheme.ringCatSheaf))) a

theorem eApp_zero (W : X.Opens) : eApp M V e W 0 = 0 := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_zero

theorem eApp_injective (W : X.Opens) : Function.Injective (eApp M V e W) :=
  Function.LeftInverse.injective (eInv_eApp M V e W)

theorem restrict_smul_eq (W' : V.toScheme.Opens) (b : Γ(V.toScheme, W')) (m : Γ(M.restrict V.ι, W'))
  :
    (HSMul.hSMul (α := Γ(V.toScheme, W')) (β := Γ(M.restrict V.ι, W')) b m : Γ(M, V.ι ''ᵁ W'))
      = HSMul.hSMul (α := Γ(X, V.ι ''ᵁ W')) (β := Γ(M, V.ι ''ᵁ W')) ((Scheme.Hom.appIso V.ι W').inv
          b) m := rfl

theorem eApp_smul (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (a • m) = a * eApp M V e W m := by
  have hinv : (Scheme.Hom.appIso V.ι (V.ι ⁻¹ᵁ W)).inv a = a := by
    rw [Scheme.Opens.ι_appIso]; rfl
  have h := Hom.app_smul e.hom (U := V.ι ⁻¹ᵁ W) a m
  have hl := restrict_smul_eq M V (V.ι ⁻¹ᵁ W) a m
  rw [hinv] at hl
  unfold eApp
  rw [← hl]
  exact h.trans rfl

omit M e in
theorem unit_map_eq {W₁' W₂' : V.toScheme.Opens} (i : W₂' ⟶ W₁') (a : Γ(X, V.ι ''ᵁ W₁')) :
    ((Scheme.Modules.presheaf (SheafOfModules.unit V.toScheme.ringCatSheaf)).map i.op) a
      = (X.presheaf.map ((Scheme.Hom.opensFunctor V.ι).map i).op).hom a := rfl

theorem eApp_res {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W₁)) :
    eApp M V e W₂ (rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) m)
      = rO (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (eApp M V e W₁ m) := by
  have hnat := e.hom.mapPresheaf.naturality (homOfLE (Scheme.Hom.preimage_mono V.ι h)).op
  have hx := ConcreteCategory.congr_hom hnat m
  have e1 : (Scheme.Hom.opensFunctor V.ι).map (homOfLE (Scheme.Hom.preimage_mono V.ι h))
      = homOfLE (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) := Subsingleton.elim _
          _
  rw [restrict_map, e1] at hx
  exact hx

end Transport

section StepA

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- The local trivialization transported to an open contained in its domain. -/
noncomputable def ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : Γ(X, W) :=
  rO (le_hat V hWV) (eApp M V e W (rM M (hat_le V hWV) m))

/-- The inverse local trivialization transported to an open contained in its domain. -/
noncomputable def ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : Γ(M, W) :=
  rM M (le_hat V hWV) (eInv M V e W (rO (hat_le V hWV) a))

theorem rM_roundtrip {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : rM M (le_hat V hWV) (rM M (hat_le V
  hWV) m) = m := by
  rw [rM_rM, rM_self]
theorem rM_roundtrip' {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rM M (hat_le V hWV) (rM M (le_hat V hWV) m) = m := by
  rw [rM_rM, rM_self]
omit M e in
theorem rO_roundtrip {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : rO (le_hat V hWV) (rO (hat_le V
  hWV) a) = a := by
  rw [rO_rO, rO_self]
omit M e in
theorem rO_roundtrip' {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rO (hat_le V hWV) (rO (le_hat V hWV) a) = a := by
  rw [rO_rO, rO_self]

theorem ψ_ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : ψ M V e hWV (ψinv M V e hWV a) = a := by
  simp only [ψ, ψinv]
  rw [rM_roundtrip' M V hWV, eApp_eInv, rO_roundtrip V hWV]

theorem ψinv_ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : ψinv M V e hWV (ψ M V e hWV m) = m := by
  simp only [ψ, ψinv]
  rw [rO_roundtrip' V hWV, eInv_eApp, rM_roundtrip M V hWV]

theorem ψ_injective {W : X.Opens} (hWV : W ≤ V) : Function.Injective (ψ M V e hWV) :=
  Function.LeftInverse.injective (ψinv_ψ M V e hWV)

theorem ψ_zero {W : X.Opens} (hWV : W ≤ V) : ψ M V e hWV 0 = 0 := by
  simp only [ψ]
  change rO (le_hat V hWV) (eApp M V e W ((M.presheaf.map _) 0)) = 0
  rw [map_zero, eApp_zero]; exact map_zero _

theorem ψ_smul {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) (m : Γ(M, W)) :
    ψ M V e hWV (a • m) = a * ψ M V e hWV m := by
  simp only [ψ]
  rw [rM_smul, eApp_smul]
  change (X.presheaf.map _).hom (_ * _) = a * _
  rw [map_mul]
  congr 1
  exact rO_roundtrip V hWV a

theorem ψ_res {W₁ W₂ : X.Opens} (h₁ : W₁ ≤ V) (h : W₂ ≤ W₁) (m : Γ(M, W₁)) :
    ψ M V e (h.trans h₁) (rM M h m) = rO h (ψ M V e h₁ m) := by
  simp only [ψ]
  have lhs : rM M (hat_le V (h.trans h₁)) (rM M h m)
      = rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (rM M (hat_le V h₁) m) :=
          by
    rw [rM_rM, rM_rM]
  rw [lhs, eApp_res M V e h, rO_rO, rO_rO]

include V e in
theorem locProp {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ V) (g : Γ(X, W)) : LocProp M W g :=
  by
  have := hW.isLocalization_basicOpen g
  have hDV : X.basicOpen g ≤ V := (X.basicOpen_le g).trans hWV
  constructor
  · intro x
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hax⟩ := IsLocalization.surj (Submonoid.powers g) (ψ M V e hDV x)
    refine ⟨n, ψinv M V e hWV a, ψ_injective M V e hDV ?_⟩
    change ψ M V e hDV (rM M (X.basicOpen_le g) (ψinv M V e hWV a)) = ψ M V e hDV (rO
        (X.basicOpen_le g) (g ^ n) • x)
    rw [ψ_res M V e hWV (X.basicOpen_le g), ψ_ψinv, ψ_smul, mul_comm]
    exact hax.symm
  · intro y hy
    have h0 : algebraMap Γ(X, W) Γ(X, X.basicOpen g) (ψ M V e hWV y) = 0 := by
      change rO (X.basicOpen_le g) (ψ M V e hWV y) = 0
      rw [← ψ_res M V e hWV (X.basicOpen_le g)]
      change ψ M V e hDV (M.presheaf.map (homOfLE (X.basicOpen_le g)).op y) = 0
      rw [hy, ψ_zero]
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers g)] at h0
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := h0
    refine ⟨n, ψ_injective M V e hWV ?_⟩
    rw [ψ_smul, ψ_zero]
    exact hn

end StepA

end LocTriv

open LocTriv in
theorem finite_sections_of_locallyTrivial'
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) := by
  classical
  have hbasis : ∀ x : U.1, ∃ (h : Γ(X, U.1)) (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
      V.toScheme.ringCatSheaf),
      (x : X) ∈ X.basicOpen h ∧ X.basicOpen h ≤ V := by
    intro x
    obtain ⟨V, hxV, ⟨e⟩⟩ := htriv x
    obtain ⟨h, hhV, hxh⟩ := U.2.exists_basicOpen_le ⟨(x : X), hxV⟩ x.2
    exact ⟨h, V, (restrictFunctorIsoPullback V.ι).app M ≪≫ e, hxh, hhV⟩
  choose hOf VOf eOf hxh hhV using hbasis
  have hcov : (U.1 : Set X) ⊆ ⋃ x : U.1, (X.basicOpen (hOf x) : Set X) := fun p hp =>
    Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxh ⟨p, hp⟩⟩
  obtain ⟨t, ht⟩ := U.2.isCompact.elim_finite_subcover (fun x : U.1 => (X.basicOpen (hOf x) : Set
      X))
    (fun x => (X.basicOpen (hOf x)).isOpen) hcov
  have hspan : Ideal.span ((fun x : U.1 => hOf x) '' (↑t : Set _)) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro p hp
    have := ht hp
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hpx⟩ := this
    exact Opens.mem_iSup.mpr ⟨⟨hOf x, Set.mem_image_of_mem _ (Finset.mem_coe.mpr hxt)⟩, hpx⟩
  have hDV : ∀ x, X.basicOpen (hOf x) ≤ VOf x := fun x => hhV x
  let u : ∀ x : U.1, Γ(M, X.basicOpen (hOf x)) := fun x => ψinv M (VOf x) (eOf x) (hDV x) 1
  have hu : ∀ x (z : Γ(M, X.basicOpen (hOf x))), z = ψ M (VOf x) (eOf x) (hDV x) z • u x := by
    intro x z
    apply ψ_injective M (VOf x) (eOf x) (hDV x)
    rw [ψ_smul, ψ_ψinv, mul_one]
  have hloc := fun x => isLocalization_basicOpen_of_locallyTrivial M htriv U (hOf x)
  have step : ∀ x : U.1, ∃ (n : ℕ) (y : Γ(M, U.1)),
      rM M (X.basicOpen_le (hOf x)) y = rO (X.basicOpen_le (hOf x)) (hOf x ^ n) • u x :=
    fun x => (hloc x).1 (u x)
  choose n y hy using step
  have key : ∀ (m : Γ(M, U.1)) (x : U.1), ∃ e : ℕ,
      (hOf x ^ e : Γ(X, U.1)) • m ∈ Submodule.span Γ(X, U.1) ({y x} : Set Γ(M, U.1)) := by
    intro m x
    have := U.2.isLocalization_basicOpen (hOf x)
    have hle : X.basicOpen (hOf x) ≤ U.1 := X.basicOpen_le (hOf x)
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hab⟩ := IsLocalization.surj (Submonoid.powers (hOf x))
      (ψ M (VOf x) (eOf x) (hDV x) (rM M hle m))
    have hab' : ψ M (VOf x) (eOf x) (hDV x) (rM M hle m) * rO hle (hOf x ^ k) = rO hle b := hab
    have hzero : rM M hle ((hOf x ^ (k + n x) : Γ(X, U.1)) • m - b • y x) = 0 := by
      change (M.presheaf.map (homOfLE hle).op) (_ - _) = 0
      rw [map_sub]
      change rM M hle ((hOf x ^ (k + n x) : Γ(X, U.1)) • m) - rM M hle (b • y x) = 0
      rw [rM_smul, rM_smul, hy, hu x (rM M hle m), ← mul_smul, ← mul_smul, ← sub_smul]
      have hcoef : rO hle (hOf x ^ (k + n x)) * ψ M (VOf x) (eOf x) (hDV x) (rM M hle m)
          = rO hle b * rO hle (hOf x ^ n x) := by
        rw [← hab']
        simp only [rO, map_pow, map_mul, pow_add]
        ring
      rw [hcoef, sub_self, zero_smul]
    obtain ⟨N, hN⟩ := (hloc x).2 _ hzero
    rw [smul_sub, sub_eq_zero] at hN
    refine ⟨N + (k + n x), ?_⟩
    rw [pow_add, mul_smul, hN, ← mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  refine Module.finite_def.mpr ⟨t.image y, ?_⟩
  rw [eq_top_iff]
  intro m _
  choose e he using key m
  obtain ⟨emax, hemax⟩ : ∃ N : ℕ, ∀ x ∈ t, e x ≤ N := ⟨t.sup e, fun x hx => Finset.le_sup (f := e)
      hx⟩
  have hmono : ∀ x ∈ t, (hOf x ^ emax : Γ(X, U.1)) • m ∈ Submodule.span Γ(X, U.1) (↑(t.image y) :
      Set Γ(M, U.1)) := by
    intro x hx
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hemax x hx)
    rw [hd, add_comm, pow_add, mul_smul]
    refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (he x))
    rw [Finset.coe_image, Set.singleton_subset_iff]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hx)
  have hspan' : Ideal.span ((fun x : U.1 => hOf x ^ emax) '' (↑t : Set _)) = ⊤ := by
    have := Ideal.span_pow_eq_top (α := Γ(X, U.1)) ((fun x : U.1 => hOf x) '' (↑t : Set _)) hspan
        emax
    rwa [Set.image_image] at this
  have h1 : (1 : Γ(X, U.1)) ∈ Ideal.span ((fun x : U.1 => hOf x ^ emax) '' (↑t : Set _)) := by
    rw [hspan']; trivial
  rw [← one_smul Γ(X, U.1) m]
  refine Submodule.span_induction (p := fun r _ => r • m ∈ Submodule.span Γ(X, U.1) (↑(t.image y) :
      Set Γ(M, U.1)))
    ?_ ?_ ?_ ?_ h1
  · rintro _ ⟨x, hx, rfl⟩
    change (hOf x ^ emax) • m ∈ _
    exact hmono x (Finset.mem_coe.mp hx)
  · change (0 : Γ(X, U.1)) • m ∈ _
    rw [zero_smul]; exact Submodule.zero_mem _
  · intro r s _ _ hr hs
    change (r + s) • m ∈ _
    rw [add_smul]; exact Submodule.add_mem _ hr hs
  · intro c r _ hr
    change (c • r) • m ∈ _
    rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ _ hr

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) :=
  AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial' M htriv U
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_finite_sections_of_locallyTrivial
end ProofImplementation
