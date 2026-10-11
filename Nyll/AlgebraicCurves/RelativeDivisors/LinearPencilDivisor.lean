/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The finite-flat zero-scheme argument adapts the following Anthropic FLT source:
Copyright 2026 Anthropic, PBC. Released under Apache 2.0.
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal.lean
Upstream NOTICE and ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.SchemeTheory.Modules.FlatSectionsBaseChange
import Nyll.AlgebraicCurves.RelativeDivisors.LinearPencilSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isInvertible_zeroSchemeIdeal_and_flat
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!+# Effective divisors in a linear pencil

Flat base change preserves independence of the actual global sections of an
invertible module. Thus every field-valued fibre of the pencil is nonzero.
The actual zero scheme is finite and flat over the affine line, and its rank
is constant. This constructs an effective relative Cartier divisor and
computes its zero ideal on every rational parameter fibre.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.LinearPencil

open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
open AlgebraicGeometry.Scheme.Modules.GlueSect

/-- The actual module morphism associated to the section of the pencil. -/
def pencilMorphism {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (v : Fin 2 → Γ(M, ⊤)) :
    𝟙_ (pullback c lineMap).Modules ⟶
      (Scheme.Modules.pullback (pullback.fst c lineMap)).obj M :=
  homOfGsec (pencilSection c M (v 0) (v 1))

theorem pencilMorphism_apply_one {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (v : Fin 2 → Γ(M, ⊤)) :
    (pencilMorphism c M v).app ⊤ (toUnitSection ⊤ 1) =
      pencilSection c M (v 0) (v 1) :=
  gsec_homOfGsec _

/-- Restriction of the actual zero ideal to a rational fibre of the pencil. -/
theorem zeroSchemeIdeal_pencilMorphism_fibre
    {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (hM : IsInvertible M)
    (v : Fin 2 → Γ(M, ⊤)) (a : K) :
    (zeroSchemeIdeal (pencilMorphism c M v)).comap (fibre c a) =
      zeroSchemeIdeal (homOfGsec
        ((1 - c.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) • v 0 +
          c.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) • v 1)) := by
  let e := fibreModuleIso c a M
  have hsec : pullbackSection (fibre c a) (pencilMorphism c M v) ≫ e.hom =
      homOfGsec
        ((1 - c.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) • v 0 +
          c.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) • v 1) := by
    apply hom_ext_of_gsec_eq
    rw [gsec_homOfGsec]
    change e.hom.app ⊤ (gsec (pullbackSection (fibre c a) (pencilMorphism c M v))) = _
    rw [gsec_pullbackSection, gsec_def, pencilMorphism_apply_one]
    exact section_fibre c a M (v 0) (v 1)
  rw [(hM.pullback (pullback.fst c lineMap)).comap_zeroSchemeIdeal]
  rw [← zeroSchemeIdeal_comp_eq_of_isIso _ e.hom, hsec]

private theorem independent_pullback
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
    [QuasiCompact c] [IsSeparated c]
    (c' : X' ⟶ Spec (CommRingCat.of L)) (p : X' ⟶ X)
    (hp : IsPullback p c' c (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (M : X.Modules) (hM : IsInvertible M) :
    let : Algebra K Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop).hom.toAlgebra
    let : Module K Γ(M, ⊤) := Module.compHom _ (algebraMap K Γ(X, ⊤))
    let : Algebra L Γ(X', ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ c'.appTop).hom.toAlgebra
    let : Module L Γ((Scheme.Modules.pullback p).obj M, ⊤) :=
      Module.compHom _ (algebraMap L Γ(X', ⊤))
    ∀ (v : Fin 2 → Γ(M, ⊤)), LinearIndependent K v →
      LinearIndependent L (M := Γ((Scheme.Modules.pullback p).obj M, ⊤))
        (fun i => (pullbackLocalSection p (v i) :
        Γ((Scheme.Modules.pullback p).obj M, ⊤))) := by
  intro algK modK algL modL v hv
  obtain ⟨β, hβ⟩ := hM.exists_tensorProduct_linearEquiv_sections_pullback_of_flat
    L c c' p hp M
  have h := (Module.Flat.linearIndependent_one_tmul (S := L) hv).map'
    β.toLinearMap (LinearMap.ker_eq_bot.mpr β.injective)
  have heq : (fun i => β ((1 : L) ⊗ₜ[K] v i)) =
      (fun i => pullbackLocalSection p (v i)) := by
    funext i
    exact hβ (v i)
  exact heq ▸ h

private theorem combination_ne_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : Fin 2 → V) (hv : LinearIndependent K v) (a : K) :
    (1 - a) • v 0 + a • v 1 ≠ 0 := by
  intro hz
  have hcoeff := (Fintype.linearIndependent_iff.mp hv)
    ![1 - a, a] (by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] using hz)
  have h0 : 1 - a = 0 := hcoeff 0
  have h1 : a = 0 := hcoeff 1
  rw [h1, sub_zero] at h0
  exact one_ne_zero h0

/-- Every field-valued fibre of an independent pencil has a nonzero section. -/
theorem pencilSection_fibre_ne_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) [QuasiCompact c] [IsSeparated c]
    (M : X.Modules) (hM : IsInvertible M) :
    let : Algebra K Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop).hom.toAlgebra
    let : Module K Γ(M, ⊤) := Module.compHom _ (algebraMap K Γ(X, ⊤))
    ∀ (v : Fin 2 → Γ(M, ⊤)), LinearIndependent K v →
      ∀ (k : Type u) [Field k]
        (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Polynomial K))),
      pullbackLocalSection (mapOnProdOver c x rfl)
        (pencilSection c M (v 0) (v 1)) ≠ 0 := by
  intro algK modK v hv k _ x
  let ρ : CommRingCat.of K ⟶ CommRingCat.of k := Spec.preimage (x ≫ lineMap)
  let : Algebra K k := ρ.hom.toAlgebra
  have hρ : Spec.map (CommRingCat.ofHom (algebraMap K k)) = x ≫ lineMap :=
    Spec.map_preimage (x ≫ lineMap)
  let Y := pullback c (x ≫ lineMap)
  let c' : Y ⟶ Spec (CommRingCat.of k) := pullback.snd c (x ≫ lineMap)
  let F : Y ⟶ pullback c lineMap := mapOnProdOver c x rfl
  let p : Y ⟶ X := F ≫ pullback.fst c lineMap
  have hp : IsPullback p c' c (Spec.map (CommRingCat.ofHom (algebraMap K k))) := by
    change IsPullback (mapOnProdOver c x rfl ≫ pullback.fst c lineMap)
      (pullback.snd c (x ≫ lineMap)) c _
    rw [mapOnProdOver_fst, hρ]
    exact IsPullback.of_hasPullback c (x ≫ lineMap)
  let algk : Algebra k Γ(Y, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c'.appTop).hom.toAlgebra
  let V : Y.Modules := (Scheme.Modules.pullback p).obj M
  let modk : Module k Γ(V, ⊤) := Module.compHom _ (algebraMap k Γ(Y, ⊤))
  let w : Fin 2 → Γ(V, ⊤) := fun i => pullbackLocalSection p (v i)
  have hw : LinearIndependent k w := independent_pullback c c' p hp M hM v hv
  let a : k := (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (x.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv Polynomial.X))
  have hparameter : F.appTop (parameter c) = algebraMap k Γ(Y, ⊤) a := by
    change ((pullback.snd c lineMap).appTop ≫ F.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv Polynomial.X) =
      c'.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
    rw [← Scheme.Hom.comp_appTop]
    change (mapOnProdOver c x rfl ≫ pullback.snd c lineMap).appTop _ = _
    rw [mapOnProdOver_snd, Scheme.Hom.comp_appTop]
    change c'.appTop _ = c'.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
    exact congrArg c'.appTop (Iso.inv_hom_id_apply _ _).symm
  have hcomb := combination_ne_zero w hw a
  change (algebraMap k Γ(Y, ⊤) (1 - a)) • w 0 +
    (algebraMap k Γ(Y, ⊤) a) • w 1 ≠ 0 at hcomb
  rw [map_sub, map_one, ← hparameter] at hcomb
  intro hz
  have hcalc := pencilSection_pullback c F M (v 0) (v 1)
  change ((pullbackComp F (pullback.fst c lineMap)).hom.app M).app ⊤
    (pullbackLocalSection F (pencilSection c M (v 0) (v 1))) =
      (1 - F.appTop (parameter c)) • w 0 + F.appTop (parameter c) • w 1 at hcalc
  rw [hz] at hcalc
  exact hcomb (hcalc.symm.trans
    (((pullbackComp F (pullback.fst c lineMap)).hom.app M).app ⊤).hom.map_zero)

open AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal.ZDHeadG in
private theorem exists_divisor_of_fibre_divisors
    {C S T : Scheme.{u}} {c : C ⟶ S} [IsProper c]
    [SmoothOfRelativeDimension 1 c] (g : T ⟶ S)
    [IsLocallyNoetherian T] [ConnectedSpace T]
    {M : (pullback c g).Modules} (hM : IsInvertible M)
    (s : 𝟙_ (pullback c g).Modules ⟶ M)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ T),
      ∃ (r : ℕ) (D : RelEffCartierDiv c r (x ≫ g)),
        D.I = (zeroSchemeIdeal s).comap (mapOnProdOver c x rfl)) :
    ∃ (r : ℕ) (D : RelEffCartierDiv c r g),
      D.I = zeroSchemeIdeal s ∧
      ∃ e : M ≅ D.lineBundle, s ≫ e.hom = D.I.invModuleSection := by
  classical
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  let Z := zeroSchemeIdeal s
  have hgeo : ∀ t : T, ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (x : Spec (CommRingCat.of k) ⟶ T) (pt : Spec (CommRingCat.of k)), x pt = t := by
    intro t
    let k := AlgebraicClosure (T.residueField t)
    exact ⟨k, inferInstance, inferInstance,
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) k)) ≫
        T.fromSpecResidueField t, IsLocalRing.closedPoint k,
      (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)⟩
  have hinv : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ T),
      (Z.comap (pullback.fst (pullback.snd c g) x)).IsInvertible := by
    intro k _ _ x
    obtain ⟨r, D, hD⟩ := hfib k x
    have hDx : (Z.comap (mapOnProdOver c x rfl)).IsInvertible := hD ▸ D.isInvertible_I
    rw [← pullbackLeftPullbackSndIso_hom_comp_eq
      c g x (mapOnProdOver c x rfl) (mapOnProdOver_fst c x rfl)
      (mapOnProdOver_snd c x rfl), Scheme.IdealSheafData.comap_comp]
    exact isInvertible_comap_of_isIso hDx _
  obtain ⟨hZ, hflat⟩ := hM.isInvertible_zeroSchemeIdeal_and_flat (pullback.snd c g) s hinv
  have : Flat (Z.subschemeι ≫ pullback.snd c g) := hflat
  have : LocallyQuasiFinite (Z.subschemeι ≫ pullback.snd c g) := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro t
    obtain ⟨k, _, _, x, pt, hpt⟩ := hgeo t
    obtain ⟨r, D, hD⟩ := hfib k x
    have : IsFinite ((Z.comap (mapOnProdOver c x rfl)).subschemeι ≫
        pullback.snd c (x ≫ g)) := hD ▸ D.isFinite
    have : Finite (Z.comap (mapOnProdOver c x rfl)).subscheme :=
      finite_of_isFinite ((Z.comap (mapOnProdOver c x rfl)).subschemeι ≫
        pullback.snd c (x ≫ g))
    have : Finite ↥(Limits.pullback (mapOnProdOver c x rfl) Z.subschemeι) :=
      Finite.of_injective
        (fun z : ↥(Limits.pullback (mapOnProdOver c x rfl) Z.subschemeι) =>
          (Z.comapIso (mapOnProdOver c x rfl)).inv z)
        (Z.comapIso (mapOnProdOver c x rfl)).inv.injective
    exact finite_preimage_singleton_of_isPullback
      (isPullback_snd_comap
        c g x (mapOnProdOver c x rfl) (mapOnProdOver_fst c x rfl)
        (mapOnProdOver_snd c x rfl) Z) ⟨pt, hpt⟩
  have : IsFinite (Z.subschemeι ≫ pullback.snd c g) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  let r := (Z.subschemeι ≫ pullback.snd c g).finrank (Classical.arbitrary T)
  let D : RelEffCartierDiv c r g :=
    ⟨Z, inferInstance, inferInstance, inferInstance, fun t =>
      (Z.subschemeι ≫ pullback.snd c g).isLocallyConstant_finrank.apply_eq_of_preconnectedSpace
        t (Classical.arbitrary T)⟩
  obtain ⟨e, he⟩ := hM.exists_iso_invModule_zeroSchemeIdeal s hZ
  exact ⟨r, D, rfl, e, he⟩

/-- The zero scheme of an independent pencil on a smooth proper geometrically
irreducible curve is an effective relative Cartier divisor of a single degree.
The statement applies over every field, in every characteristic. -/
theorem exists_pencilDivisor
    {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    (M : X.Modules) (hM : IsInvertible M) :
    let : Algebra K Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop).hom.toAlgebra
    let : Module K Γ(M, ⊤) := Module.compHom _ (algebraMap K Γ(X, ⊤))
    ∀ (v : Fin 2 → Γ(M, ⊤)), LinearIndependent K v →
      ∃ (r : ℕ) (D : RelEffCartierDiv c r lineMap),
        D.I = zeroSchemeIdeal (pencilMorphism c M v) ∧
        ∃ e : (Scheme.Modules.pullback (pullback.fst c lineMap)).obj M ≅ D.lineBundle,
          pencilMorphism c M v ≫ e.hom = D.I.invModuleSection := by
  intro algK modK v hv
  have hN : IsInvertible ((Scheme.Modules.pullback (pullback.fst c lineMap)).obj M) :=
    hM.pullback (pullback.fst c lineMap)
  apply exists_divisor_of_fibre_divisors lineMap hN (pencilMorphism c M v)
  intro k _ _ x
  let F : pullback c (x ≫ lineMap) ⟶ pullback c lineMap := mapOnProdOver c x rfl
  have hnonzero : pullbackSection F (pencilMorphism c M v) ≠ 0 := by
    intro hz
    have h := congrArg gsec hz
    rw [gsec_pullbackSection, gsec_def, pencilMorphism_apply_one] at h
    apply pencilSection_fibre_ne_zero c M hM v hv k x
    exact h.trans (show gsec (0 : 𝟙_ (pullback c (x ≫ lineMap)).Modules ⟶
      (Scheme.Modules.pullback F).obj
        ((Scheme.Modules.pullback (pullback.fst c lineMap)).obj M)) = 0 from rfl)
  obtain ⟨r, D, hD⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
    (x ≫ lineMap) (hN.pullback F) (pullbackSection F (pencilMorphism c M v)) hnonzero
  refine ⟨r, D, ?_⟩
  exact hD.trans (hN.comap_zeroSchemeIdeal F (pencilMorphism c M v)).symm

end AlgebraicGeometry.LinearPencil
