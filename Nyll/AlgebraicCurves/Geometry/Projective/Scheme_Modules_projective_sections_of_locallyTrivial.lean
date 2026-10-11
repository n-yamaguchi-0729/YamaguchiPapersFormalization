/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Flat.Localization
import Nyll.SchemeTheory.Modules.LocallyTrivialSectionsLocalization
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finite_sections_of_locallyTrivial
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_finitePresentation_of_rankAtStalk_eq

/-!
Projectivity of sections of locally trivial scheme modules on affine open subsets.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace Scheme_Modules_projective_sections_of_locallyTrivial

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
namespace SectProj
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace LocTriv

variable {X : Scheme.{u}} (M : X.Modules)

/-- Restriction of module sections to a smaller open. -/
noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y =>
    M.presheaf.map (homOfLE h).op y

/-- Restriction of structure sheaf sections to a smaller open. -/
noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) := fun g =>
    X.presheaf.map (homOfLE h).op g

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

/-- The local trivialization applied to module sections over the image open. -/
noncomputable def eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.hom.app (V.ι ⁻¹ᵁ W)).hom m

/-- The inverse local trivialization applied to structure sheaf sections over the image open. -/
noncomputable def eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.inv.app (V.ι ⁻¹ᵁ W)).hom a

theorem eInv_eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eInv M V e W (eApp M V e W m) =
    m := by
  have happ : e.hom.app (V.ι ⁻¹ᵁ W) ≫ e.inv.app (V.ι ⁻¹ᵁ W) = 𝟙 _ :=
    (Modules.Hom.comp_app _ _).symm.trans
      ((congrArg (fun φ : M.restrict V.ι ⟶ M.restrict V.ι => φ.app (V.ι ⁻¹ᵁ W))
        e.hom_inv_id).trans (Modules.Hom.id_app _))
  exact ConcreteCategory.congr_hom happ m

theorem eApp_eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eApp M V e W (eInv M V e W a) =
    a := by
  have happ : e.inv.app (V.ι ⁻¹ᵁ W) ≫ e.hom.app (V.ι ⁻¹ᵁ W) = 𝟙 _ :=
    (Modules.Hom.comp_app _ _).symm.trans
      ((congrArg (fun φ : (SheafOfModules.unit V.toScheme.ringCatSheaf : V.toScheme.Modules) ⟶
        (SheafOfModules.unit V.toScheme.ringCatSheaf : V.toScheme.Modules) =>
          Scheme.Modules.Hom.app φ (V.ι ⁻¹ᵁ W))
        e.inv_hom_id).trans (Modules.Hom.id_app _))
  exact ConcreteCategory.congr_hom happ a

theorem eApp_zero (W : X.Opens) : eApp M V e W 0 = 0 := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_zero

theorem eApp_injective (W : X.Opens) : Function.Injective (eApp M V e W) :=
  Function.LeftInverse.injective (eInv_eApp M V e W)

theorem restrict_smul_eq (W' : V.toScheme.Opens) (b : Γ(V.toScheme, W')) (m : Γ(M.restrict V.ι,
    W')) :
    (HSMul.hSMul (α := Γ(V.toScheme, W')) (β := Γ(M.restrict V.ι, W')) b m : Γ(M, V.ι ''ᵁ W'))
      = HSMul.hSMul (α := Γ(X, V.ι ''ᵁ W')) (β := Γ(M, V.ι ''ᵁ W')) ((Scheme.Hom.appIso V.ι
        W').inv b) m := rfl

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
      = homOfLE (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) :=
        Subsingleton.elim _ _
  rw [restrict_map, e1] at hx
  exact hx

end Transport

section StepA

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- The local trivialization transported to an open contained in its domain. -/
noncomputable def ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : Γ(X, W) :=
  rO (le_hat V hWV) (eApp M V e W (rM M (hat_le V hWV) m))

/-- The inverse trivialization transported to an open contained in its domain. -/
noncomputable def ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : Γ(M, W) :=
  rM M (le_hat V hWV) (eInv M V e W (rO (hat_le V hWV) a))

theorem rM_roundtrip {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : rM M (le_hat V hWV) (rM M
    (hat_le V hWV) m) = m := by
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
      = rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (rM M (hat_le V h₁) m)
        := by
    rw [rM_rM, rM_rM]
  rw [lhs, eApp_res M V e h, rO_rO, rO_rO]

end StepA

end LocTriv

section Loc

open LocTriv

variable {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (f : Γ(X, U.1))
  (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
  (hfV : X.basicOpen f ≤ V)

theorem ψ_add {W : X.Opens} (hWV : W ≤ V) (m m' : Γ(M, W)) :
    ψ M V e hWV (m + m') = ψ M V e hWV m + ψ M V e hWV m' := by
  simp only [ψ, rM, rO, eApp, map_add]
  first
    | rfl
    | erw [AddMonoidHom.map_add, RingHom.map_add]

/-- The linear map to basic open sections obtained by restriction and local trivialization. -/
noncomputable def gψ : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(X, X.basicOpen f) where
  toFun m := ψ M V e hfV (rM M (X.basicOpen_le f) m)
  map_add' m m' := by
    simp only [rM, map_add]
    exact ψ_add M V e hfV _ _
  map_smul' a m := by
    rw [rM_smul, ψ_smul, Algebra.smul_def]
    rfl

theorem gψ_apply (m : Γ(M, U.1)) : gψ M U f V e hfV m = ψ M V e hfV (rM M (X.basicOpen_le f) m)
    := rfl

include hfV in
theorem isLocalizedModule_gψ
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf)) :
    IsLocalizedModule (Submonoid.powers f) (gψ M U f V e hfV) where
  map_units s := by
    have := U.2.isLocalization_basicOpen f
    exact IsLocalizedModule.map_units (Algebra.linearMap Γ(X, U.1) Γ(X, X.basicOpen f)) s
  surj b := by
    obtain ⟨n, y, hy⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv U f).1 (ψinv M V e
      hfV b)
    refine ⟨(y, ⟨f ^ n, n, rfl⟩), ?_⟩
    change (f ^ n : Γ(X, U.1)) • b = ψ M V e hfV (rM M (X.basicOpen_le f) y)
    change (f ^ n : Γ(X, U.1)) • b = ψ M V e hfV (M.presheaf.map (homOfLE (X.basicOpen_le f)).op y)
    rw [hy, ψ_smul, ψ_ψinv, Algebra.smul_def]
    rfl
  exists_of_eq {m m'} h := by
    have h' : rM M (X.basicOpen_le f) m = rM M (X.basicOpen_le f) m' := ψ_injective M V e hfV h
    have h0 : M.presheaf.map (homOfLE (X.basicOpen_le f)).op (m - m') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h'
    obtain ⟨n, hn⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv U f).2 _ h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hn
    exact hn

end Loc

open LocTriv in
theorem projective_sections
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) :
    Module.Projective Γ(X, U.1) Γ(M, U.1) := by
  classical
  have hfin : Module.Finite Γ(X, U.1) Γ(M, U.1) := finite_sections_of_locallyTrivial M htriv U
  let s : Set Γ(X, U.1) := {f | ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
    V.toScheme.ringCatSheaf),
    X.basicOpen f ≤ V}
  have hspan : Ideal.span s = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro p hp
    obtain ⟨V, hxV, ⟨e⟩⟩ := htriv p
    obtain ⟨h, hhV, hph⟩ := U.2.exists_basicOpen_le ⟨p, hxV⟩ hp
    exact Opens.mem_iSup.mpr ⟨⟨h, V, (restrictFunctorIsoPullback V.ι).app M ≪≫ e, hhV⟩, hph⟩
  have hdata : ∀ r : s, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
    V.toScheme.ringCatSheaf),
      X.basicOpen r.1 ≤ V := fun r => r.2
  choose V e hle using hdata
  have hloc : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (gψ M U r.1 (V r) (e r) (hle r)) :=
    fun r => isLocalizedModule_gψ M U r.1 (V r) (e r) (hle r) htriv
  have hflat : Module.Flat Γ(X, U.1) Γ(M, U.1) :=
    Module.flat_of_isLocalized_span (R := Γ(X, U.1)) Γ(X, U.1) Γ(M, U.1) s hspan
      (fun r => Γ(X, X.basicOpen r.1)) (fun r => gψ M U r.1 (V r) (e r) (hle r)) fun r => by
        have := U.2.isLocalization_basicOpen r.1
        exact IsLocalization.flat Γ(X, X.basicOpen r.1) (Submonoid.powers r.1)
  have hrank : ∀ p : PrimeSpectrum Γ(X, U.1), Module.rankAtStalk Γ(M, U.1) p = 1 := by
    intro p
    have hns : ¬ (s ⊆ p.asIdeal) := fun hsub =>
      p.isPrime.ne_top (top_le_iff.mp (hspan ▸ Ideal.span_le.mpr hsub))
    obtain ⟨f, hfs, hfp⟩ := Set.not_subset.mp hns
    have := U.2.isLocalization_basicOpen f
    have := hloc ⟨f, hfs⟩
    have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f))) := by
      rw [PrimeSpectrum.localization_away_comap_range Γ(X, X.basicOpen f) f]
      exact hfp
    obtain ⟨q, rfl⟩ := hmem
    have : Nontrivial Γ(X, X.basicOpen f) := PrimeSpectrum.nontrivial q
    rw [← Module.rankAtStalk_baseChange,
      Module.rankAtStalk_eq_of_equiv
        (IsLocalizedModule.isBaseChange (Submonoid.powers f) Γ(X, X.basicOpen f)
          (gψ M U f (V ⟨f, hfs⟩) (e ⟨f, hfs⟩) (hle ⟨f, hfs⟩))).equiv,
      Module.rankAtStalk_self]
    rfl
  have := Module.finitePresentation_of_rankAtStalk_eq (R := Γ(X, U.1)) Γ(M, U.1) 1 hrank
  exact Module.Flat.projective_of_finitePresentation

end AlgebraicGeometry.Scheme.Modules.SectProj

theorem _root_.AlgebraicGeometry.Scheme.Modules.projective_sections_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) :
    Module.Projective Γ(X, U.1) Γ(M, U.1) :=
  AlgebraicGeometry.Scheme.Modules.SectProj.projective_sections M htriv U
end AlgebraicCurves.Geometry.Projective.Proofs.Scheme_Modules_projective_sections_of_locallyTrivial
end ProofImplementation
