/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Opposites
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring.Basic
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.JacobianVarieties.Picard.existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen

/-!
# Lifting pushforward bases to dual-number thickenings

Lift a basis of the structure-sheaf pushforward through a cartesian dual-number thickening.
The proof uses the unique constant and infinitesimal decomposition on affine opens.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DualThickeningBasis
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Spec.map_comp
  Scheme.Hom.map_appLE
  Surjective
  Scheme.Modules.pushforward
  Scheme.Hom
  Scheme.Hom.appLE_comp_appLE
  Spec
  Spec.map
  Scheme
  Scheme.Hom.comp_appLE
  IsClosedImmersion.spec_of_surjective
  Scheme.Hom.preimage_mono
  IsClosedImmersion
  Spec.map_id
  IsAffineOpen
  Scheme.Modules
  Scheme.Hom.appLE_map
  Scheme.Hom.app_eq_appLE
  Scheme.Hom.comp_preimage
  IsAffineHom
  Scheme.Hom.comp_apply
  Scheme.ΓSpecIso
  RelPicard.baseChangeSnd
  RelPicard.baseChangeSnd_id
  RelPicard.baseChangeSnd_comp
  Scheme.TwoAffineOpenCover
  RelPicard.LFP.stageHom
  RelPicard.existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen
  Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  dualNumberThickening
  baseChangeSnd
  baseChangeSnd_id
  baseChangeSnd_comp
  LFP.stageHom
  existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen)

namespace ThickeningAux

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (A : Type u) [CommRing
  A] [Algebra R A]

/-- The projection from the dual-number thickening to the original base change. -/
noncomputable abbrev thick : Limits.pullback c (specMap R (DualNumber A)) ⟶ Limits.pullback c
  (specMap R A) :=
  RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A (DualNumber A)))

/-- The zero section of the dual-number thickening. -/
noncomputable abbrev zeroSec : Limits.pullback c (specMap R A) ⟶ Limits.pullback c (specMap R
  (DualNumber A)) :=
  RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (TrivSqZeroExt.fstHom R A A))

theorem zeroSec_thick : zeroSec c A ≫ thick c A = 𝟙 _ := by
  rw [zeroSec, thick, RelPicard.baseChangeSnd_comp, ← RelPicard.baseChangeSnd_id c (specMap R A)]
  congr 1
  apply Subtype.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem surjective_spec_fst : Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R A
  A).toRingHom)) := by
  refine ⟨fun x => ⟨(Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A)))).base x, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, ← Spec.map_comp]
  change PrimeSpectrum.comap _ x = x
  ext z
  change (TrivSqZeroExt.inl (TrivSqZeroExt.fst z) : DualNumber A) ∈ x.asIdeal ↔ z ∈ x.asIdeal
  have hnil : (TrivSqZeroExt.inr (TrivSqZeroExt.snd z) : DualNumber A) ∈ x.asIdeal := by
    apply x.isPrime.mem_of_pow_mem 2
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
    exact x.asIdeal.zero_mem
  have hz : z = TrivSqZeroExt.inl (TrivSqZeroExt.fst z) + TrivSqZeroExt.inr (TrivSqZeroExt.snd z) :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq z).symm
  constructor
  · intro h; rw [hz]; exact x.asIdeal.add_mem h hnil
  · intro h
    have := x.asIdeal.sub_mem h hnil
    have e : z - TrivSqZeroExt.inr (TrivSqZeroExt.snd z) = TrivSqZeroExt.inl (TrivSqZeroExt.fst z)
      := by
      rw [sub_eq_iff_eq_add]; exact hz
    rwa [e] at this

theorem isPullback_zeroSec :
    IsPullback (Limits.pullback.snd c (specMap R A)) (zeroSec c A)
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R A A).toRingHom))
      (Limits.pullback.snd c (specMap R (DualNumber A))) := by
  apply IsPullback.flip
  refine IsPullback.of_right (h₁₂ := Limits.pullback.fst c (specMap R (DualNumber A))) (v₁₃ := c)
    (h₂₂ := specMap R (DualNumber A)) ?_ ?_ (IsPullback.of_hasPullback _ _)
  · have h1 : zeroSec c A ≫ Limits.pullback.fst c (specMap R (DualNumber A)) = Limits.pullback.fst
      c (specMap R A) :=
      baseChangeSnd_fst c _
    have h2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R A A).toRingHom) ≫ specMap R
      (DualNumber A) =
        specMap R A := (RelPicard.LFP.stageHom R (TrivSqZeroExt.fstHom R A A)).2
    rw [h1, h2]
    exact IsPullback.of_hasPullback _ _
  · exact Limits.pullback.lift_snd _ _ _

scoped instance surjective_zeroSec : Surjective (zeroSec c A) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_zeroSec c A) (surjective_spec_fst
    (R := R) A)

scoped instance isClosedImmersion_zeroSec : IsClosedImmersion (zeroSec c A) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_zeroSec c A)
    (IsClosedImmersion.spec_of_surjective _ (fun a => ⟨TrivSqZeroExt.inl a, TrivSqZeroExt.fst_inl A
      a⟩))

theorem thick_zeroSec_apply (x : ↥(Limits.pullback c (specMap R A))) :
    (thick c A).base ((zeroSec c A).base x) = x := by
  rw [← Scheme.Hom.comp_apply, zeroSec_thick]; rfl

theorem zeroSec_thick_apply (y : ↥(Limits.pullback c (specMap R (DualNumber A)))) :
    (zeroSec c A).base ((thick c A).base y) = y := by
  obtain ⟨x, rfl⟩ := (zeroSec c A).surjective y
  rw [thick_zeroSec_apply]

theorem thick_preimage_zeroSec_preimage (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) :
    thick c A ⁻¹ᵁ (zeroSec c A ⁻¹ᵁ W) = W := by
  ext y
  change (zeroSec c A).base ((thick c A).base y) ∈ W ↔ y ∈ W
  rw [zeroSec_thick_apply]

theorem isAffineOpen_zeroSec_preimage {W : (Limits.pullback c (specMap R (DualNumber A))).Opens}
    (hW : IsAffineOpen W) :
    IsAffineOpen (zeroSec c A ⁻¹ᵁ W) := hW.preimage _

theorem exists_basis_of_dualNumber_decomp
    {P Pε Q Qε : Type*} [CommRing P] [CommRing Pε] [CommRing Q] [CommRing Qε]
    (σ : P →+* Pε) (σ' : Q →+* Qε) (φ : P →+* Q) (φε : Pε →+* Qε)
    (hcomm : ∀ x, φε (σ x) = σ' (φ x)) (εP : Pε) (εQ : Qε) (hε : φε εP = εQ)
    (hX : ∀ u : Pε, ∃ a b : P, u = σ a + εP * σ b)
    (hYex : ∀ y : Qε, ∃ a b : Q, y = σ' a + εQ * σ' b)
    (hYuniq : ∀ a b : Q, σ' a + εQ * σ' b = 0 → a = 0 ∧ b = 0)
    {d : ℕ} :
    let _ : Algebra P Q := φ.toAlgebra
    let _ : Algebra Pε Qε := φε.toAlgebra
    ∀ (bₐ : Module.Basis (Fin d) P Q),
      ∃ b : Module.Basis (Fin d) Pε Qε, ∀ i, b i = σ' (bₐ i) := by
  intro algQ algQε bₐ
  have smulQ : ∀ (p : P) (q : Q), p • q = φ p * q := fun _ _ => rfl
  have smulQε : ∀ (p : Pε) (q : Qε), p • q = φε p * q := fun _ _ => rfl
  have expand : ∀ a : Q, σ' a = ∑ i, (σ (bₐ.repr a i)) • σ' (bₐ i) := by
    intro a
    conv_lhs => rw [← bₐ.sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smulQ, map_mul, smulQε, hcomm]
  have hli : LinearIndependent Pε (fun i => σ' (bₐ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a b hab using fun i => hX (g i)
    have hsum : ∑ i, g i • σ' (bₐ i) = σ' (∑ i, a i • bₐ i) + εQ * σ' (∑ i, b i • bₐ i) := by
      rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smulQε, hab i, map_add, map_mul, hcomm, hcomm, hε, smulQ, smulQ, map_mul, map_mul]
      ring
    rw [hsum] at hg
    obtain ⟨h1, h2⟩ := hYuniq _ _ hg
    have ha : a i = 0 := (Fintype.linearIndependent_iff.mp bₐ.linearIndependent a h1) i
    have hb : b i = 0 := (Fintype.linearIndependent_iff.mp bₐ.linearIndependent b h2) i
    rw [hab i, ha, hb, map_zero, mul_zero, add_zero]
  have hsp : ⊤ ≤ Submodule.span Pε (Set.range fun i => σ' (bₐ i)) := by
    rintro y -
    obtain ⟨a, b, rfl⟩ := hYex y
    refine Submodule.add_mem _ ?_ ?_
    · rw [expand a]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [expand b, Finset.mul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smulQε, ← mul_assoc, ← hε, ← map_mul, ← smulQε]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

section Geom

variable {C' : Scheme.{u}} (c' : C' ⟶ Spec (.of R))

theorem preimage_thick_eq {f₀ : Limits.pullback c' (specMap R A) ⟶ Limits.pullback c (specMap R A)}
    {fε₀ : Limits.pullback c' (specMap R (DualNumber A)) ⟶ Limits.pullback c (specMap R (DualNumber
      A))}
    (hw : fε₀ ≫ thick c A = thick c' A ≫ f₀) (U : (Limits.pullback c (specMap R A)).Opens) :
    fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ U) = thick c' A ⁻¹ᵁ (f₀ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hw]

/-- Pull a section to the thickening using the cartesian preimage identity. -/
noncomputable def liftSec {f₀ : Limits.pullback c' (specMap R A) ⟶ Limits.pullback c (specMap R A)}
    {fε₀ : Limits.pullback c' (specMap R (DualNumber A)) ⟶ Limits.pullback c (specMap R (DualNumber
      A))}
    (hw : fε₀ ≫ thick c A = thick c' A ≫ f₀) (U : (Limits.pullback c (specMap R A)).Opens)
    (x : Γ(Limits.pullback c' (specMap R A), f₀ ⁻¹ᵁ U)) :
    Γ(Limits.pullback c' (specMap R (DualNumber A)), fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ U)) :=
  ((thick c' A).appLE (f₀ ⁻¹ᵁ U) (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ U)) (preimage_thick_eq c A c' hw
    U).le).hom x

theorem liftSec_restrict {f₀ : Limits.pullback c' (specMap R A) ⟶ Limits.pullback c (specMap R A)}
    {fε₀ : Limits.pullback c' (specMap R (DualNumber A)) ⟶ Limits.pullback c (specMap R (DualNumber
      A))}
    (hw : fε₀ ≫ thick c A = thick c' A ≫ f₀) {U W : (Limits.pullback c (specMap R A)).Opens} (hWU :
      W ≤ U)
    (x : Γ(Limits.pullback c' (specMap R A), f₀ ⁻¹ᵁ U)) :
    (Limits.pullback c' (specMap R (DualNumber A))).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono fε₀ (Scheme.Hom.preimage_mono (thick c A) hWU))).op
          (liftSec c A c' hw U x) =
      liftSec c A c' hw W ((Limits.pullback c' (specMap R A)).presheaf.map (homOfLE
        (Scheme.Hom.preimage_mono f₀ hWU)).op x) := by
  unfold liftSec
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

theorem exists_basis_thick_preimage
    {f₀ : Limits.pullback c' (specMap R A) ⟶ Limits.pullback c (specMap R A)} [IsAffineHom f₀]
    {fε₀ : Limits.pullback c' (specMap R (DualNumber A)) ⟶ Limits.pullback c (specMap R (DualNumber
      A))}
    (hw : fε₀ ≫ thick c A = thick c' A ≫ f₀)
    (hover : fε₀ ≫ Limits.pullback.snd c (specMap R (DualNumber A)) = Limits.pullback.snd c'
      (specMap R (DualNumber A)))
    {d : ℕ} (U W : (Limits.pullback c (specMap R A)).Opens) (hWU : W ≤ U) (hWaff : IsAffineOpen W)
    (e : Fin d → Γ(Limits.pullback c' (specMap R A), f₀ ⁻¹ᵁ U))
    (bₐ : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R A), W) Γ((Scheme.Modules.pushforward
      f₀).obj (𝟙_ _), W))
    (hbₐ : ∀ i, bₐ i = (Limits.pullback c' (specMap R A)).presheaf.map (homOfLE
      (Scheme.Hom.preimage_mono f₀ hWU)).op (e i))
    (hWε : thick c A ⁻¹ᵁ W ≤ thick c A ⁻¹ᵁ U) :
    ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), thick c A ⁻¹ᵁ W)
        Γ((Scheme.Modules.pushforward fε₀).obj (𝟙_ _), thick c A ⁻¹ᵁ W),
      ∀ i, b i = ((Scheme.Modules.pushforward fε₀).obj (𝟙_ _)).presheaf.map (homOfLE hWε).op
        (show Γ((Scheme.Modules.pushforward fε₀).obj (𝟙_ _), thick c A ⁻¹ᵁ U) from liftSec c A c'
          hw U (e i)) := by
  have hpre : fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W) = thick c' A ⁻¹ᵁ (f₀ ⁻¹ᵁ W) := preimage_thick_eq c A c' hw W
  let σ : Γ(Limits.pullback c (specMap R A), W) →+* Γ(Limits.pullback c (specMap R (DualNumber A)),
    thick c A ⁻¹ᵁ W) :=
    ((thick c A).appLE W (thick c A ⁻¹ᵁ W) le_rfl).hom
  let σ' : Γ(Limits.pullback c' (specMap R A), f₀ ⁻¹ᵁ W) →+*
      Γ(Limits.pullback c' (specMap R (DualNumber A)), fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) :=
    ((thick c' A).appLE (f₀ ⁻¹ᵁ W) (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) hpre.le).hom
  let φ : Γ(Limits.pullback c (specMap R A), W) →+* Γ(Limits.pullback c' (specMap R A), f₀ ⁻¹ᵁ W)
    := (f₀.app W).hom
  let φε : Γ(Limits.pullback c (specMap R (DualNumber A)), thick c A ⁻¹ᵁ W) →+*
      Γ(Limits.pullback c' (specMap R (DualNumber A)), fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) := (fε₀.app
        (thick c A ⁻¹ᵁ W)).hom
  let iX := algebraOfHom (Limits.pullback.snd c (specMap R (DualNumber A))) (thick c A ⁻¹ᵁ W)
  let iY := algebraOfHom (Limits.pullback.snd c' (specMap R (DualNumber A))) (fε₀ ⁻¹ᵁ (thick c A
    ⁻¹ᵁ W))
  let εP : Γ(Limits.pullback c (specMap R (DualNumber A)), thick c A ⁻¹ᵁ W) := algebraMap
    (DualNumber A) _ DualNumber.eps
  let εQ : Γ(Limits.pullback c' (specMap R (DualNumber A)), fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) :=
    algebraMap (DualNumber A) _ DualNumber.eps
  have key : ∀ {S T : Scheme.{u}} {g₁ g₂ : S ⟶ T} (_ : g₁ = g₂) {U' : T.Opens} {V' : S.Opens}
      (e₁ : V' ≤ g₁ ⁻¹ᵁ U') (e₂ : V' ≤ g₂ ⁻¹ᵁ U'), g₁.appLE U' V' e₁ = g₂.appLE U' V' e₂ := by
    rintro _ _ _ _ rfl _ _ _ _; rfl
  have hcomm : ∀ x, φε (σ x) = σ' (φ x) := by
    intro x
    change ((thick c A).appLE W (thick c A ⁻¹ᵁ W) le_rfl ≫ fε₀.app (thick c A ⁻¹ᵁ W)).hom x =
      (f₀.app W ≫ (thick c' A).appLE (f₀ ⁻¹ᵁ W) (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) hpre.le).hom x
    have hmap :
        (thick c A).appLE W (thick c A ⁻¹ᵁ W) le_rfl ≫ fε₀.app (thick c A ⁻¹ᵁ W) =
          f₀.app W ≫ (thick c' A).appLE (f₀ ⁻¹ᵁ W) (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) hpre.le := by
      calc
        _ = (thick c A).appLE W (thick c A ⁻¹ᵁ W) le_rfl ≫
            fε₀.appLE (thick c A ⁻¹ᵁ W) (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) le_rfl :=
          congrArg ((thick c A).appLE W (thick c A ⁻¹ᵁ W) le_rfl ≫ ·)
            (Scheme.Hom.app_eq_appLE fε₀)
        _ = (fε₀ ≫ thick c A).appLE W (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W))
            (by intro x hx; exact hx) :=
          Scheme.Hom.appLE_comp_appLE fε₀ (thick c A) W (thick c A ⁻¹ᵁ W)
            (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) le_rfl le_rfl
        _ = (thick c' A ≫ f₀).appLE W (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W))
            (by rw [Scheme.Hom.comp_preimage]; exact hpre.le) := key hw _ _
        _ = _ := Scheme.Hom.comp_appLE (thick c' A) f₀ W
          (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) (by rw [Scheme.Hom.comp_preimage]; exact hpre.le)
    exact congrArg
      (fun k : Γ(Limits.pullback c (specMap R A), W) ⟶
          Γ(Limits.pullback c' (specMap R (DualNumber A)), fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) => k.hom x)
            hmap
  have hε : φε εP = εQ := by
    change ((Limits.pullback.snd c (specMap R (DualNumber A))).appLE ⊤ (thick c A ⁻¹ᵁ W) le_top ≫
        fε₀.app (thick c A ⁻¹ᵁ W)).hom ((Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom
          DualNumber.eps) =
      ((Limits.pullback.snd c' (specMap R (DualNumber A))).appLE ⊤ (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W))
        le_top).hom
        ((Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom DualNumber.eps)
    have hmap :
        (Limits.pullback.snd c (specMap R (DualNumber A))).appLE ⊤ (thick c A ⁻¹ᵁ W)
            (by intro x hx; trivial) ≫ fε₀.app (thick c A ⁻¹ᵁ W) =
          (Limits.pullback.snd c' (specMap R (DualNumber A))).appLE ⊤
            (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) (by intro x hx; trivial) := by
      calc
        _ = (Limits.pullback.snd c (specMap R (DualNumber A))).appLE ⊤ (thick c A ⁻¹ᵁ W)
              (by intro x hx; trivial) ≫
            fε₀.appLE (thick c A ⁻¹ᵁ W) (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) le_rfl :=
          congrArg
            ((Limits.pullback.snd c (specMap R (DualNumber A))).appLE ⊤ (thick c A ⁻¹ᵁ W)
              (by intro x hx; trivial) ≫ ·) (Scheme.Hom.app_eq_appLE fε₀)
        _ = (fε₀ ≫ Limits.pullback.snd c (specMap R (DualNumber A))).appLE ⊤
            (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) (by intro x hx; trivial) :=
          Scheme.Hom.appLE_comp_appLE fε₀ (Limits.pullback.snd c (specMap R (DualNumber A)))
            ⊤ (thick c A ⁻¹ᵁ W) (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W))
            (by intro x hx; trivial) le_rfl
        _ = _ := key hover _ _
    exact congrArg
      (fun k : Γ(Spec (.of (DualNumber A)), ⊤) ⟶
          Γ(Limits.pullback c' (specMap R (DualNumber A)), fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) =>
        k.hom ((Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom DualNumber.eps)) hmap
  have hX : ∀ u, ∃ a b, u = σ a + εP * σ b := by
    intro u
    obtain ⟨ab, hab, -⟩ :=
      AlgebraicGeometry.RelPicard.existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen
        c A W hWaff (thick c A ⁻¹ᵁ W) rfl u
    exact ⟨ab.1, ab.2, hab⟩
  have hY := AlgebraicGeometry.RelPicard.existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen
      c' A (f₀ ⁻¹ᵁ W) (hWaff.preimage f₀) (fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W)) hpre.symm
  have hYex : ∀ y, ∃ a b, y = σ' a + εQ * σ' b := by
    intro y
    obtain ⟨ab, hab, -⟩ := hY y
    exact ⟨ab.1, ab.2, hab⟩
  have hYuniq : ∀ a b, σ' a + εQ * σ' b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h0 : (0 : Γ(Limits.pullback c' (specMap R (DualNumber A)), fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W))) =
        σ' (0 : Γ(Limits.pullback c' (specMap R A), f₀ ⁻¹ᵁ W) × Γ(Limits.pullback c' (specMap R A),
          f₀ ⁻¹ᵁ W)).1 +
          εQ * σ' (0 : Γ(Limits.pullback c' (specMap R A), f₀ ⁻¹ᵁ W) × Γ(Limits.pullback c'
            (specMap R A), f₀ ⁻¹ᵁ W)).2 := by
      change (0 : Γ(Limits.pullback c' (specMap R (DualNumber A)),
        fε₀ ⁻¹ᵁ (thick c A ⁻¹ᵁ W))) = σ' 0 + εQ * σ' 0
      rw [map_zero, mul_zero, add_zero]
    have := (hY 0).unique (y₁ := (a, b)) (y₂ := (0, 0)) hab.symm h0
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨b, hb⟩ := exists_basis_of_dualNumber_decomp σ σ' φ φε hcomm εP εQ hε hX hYex hYuniq bₐ
  refine ⟨b, fun i => ?_⟩
  exact (hb i).trans ((congrArg σ' (hbₐ i)).trans (liftSec_restrict c A c' hw hWU (e i)).symm)

end Geom

end AlgebraicGeometry.RelPicard.ThickeningAux

end JacobianVarieties.Picard.Proofs.DualThickeningBasis

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs.DualThickeningBasis
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.JacobianVarieties.Picard.Proofs.DualThickeningBasis.AlgebraicGeometry.RelPicard in
attribute [local instance] ThickeningAux.surjective_zeroSec
open _root_.JacobianVarieties.Picard.Proofs.DualThickeningBasis.AlgebraicGeometry.RelPicard in
attribute [local instance] ThickeningAux.isClosedImmersion_zeroSec





open _root_.JacobianVarieties.Picard.Proofs.DualThickeningBasis.AlgebraicGeometry.RelPicard in
open ThickeningAux in
theorem exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} (c : C ⟶ Spec (.of R)) (c' : C' ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (𝒲 : C'.TwoAffineOpenCover)
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))
    [IsAffineHom f.hom]
    (hsq : IsPullback fε.hom (dualNumberThickening A 𝒲 c').hom (dualNumberThickening A 𝒱 c).hom
      f.hom)
    (d : ℕ) (U : (Limits.pullback c (specMap R A)).Opens)
    (Uε : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hUε : Uε = (dualNumberThickening A
      𝒱 c).hom ⁻¹ᵁ U)
    (e : Fin d → Γ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _), U))
    (he : ∀ (W : (Limits.pullback c (specMap R A)).Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R A), W)
          Γ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e
          i)) :
    ∃ eε : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), Uε),
      ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ Uε),
        ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
            Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
          ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op
            (eε i) := by
  have hσ : (dualNumberThickening A 𝒱 c).hom = thick c A := rfl
  have hw : fε.hom ≫ thick c A = thick c' A ≫ f.hom := hsq.w
  have hover : fε.hom ≫ Limits.pullback.snd c (specMap R (DualNumber A)) =
      Limits.pullback.snd c' (specMap R (DualNumber A)) := by
    rw [fε.comm]
    change _ ≫ Spec.map (𝟙 _) = _
    rw [Spec.map_id, Category.comp_id]
  subst hUε
  rw [hσ]
  refine ⟨fun i => (show Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), thick c A ⁻¹ᵁ U) from
    liftSec c A c' hw U (show Γ(Limits.pullback c' (specMap R A), f.hom ⁻¹ᵁ U) from e i)), ?_⟩
  apply AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen
  intro W hW hWaff
  have hW' : thick c A ⁻¹ᵁ (zeroSec c A ⁻¹ᵁ W) = W := thick_preimage_zeroSec_preimage c A W
  have hW'aff : IsAffineOpen (zeroSec c A ⁻¹ᵁ W) := isAffineOpen_zeroSec_preimage c A hWaff
  have hW'U : zeroSec c A ⁻¹ᵁ W ≤ U := by
    intro x hx
    have h2 : (zeroSec c A).base x ∈ thick c A ⁻¹ᵁ U := hW hx
    change (thick c A).base ((zeroSec c A).base x) ∈ U at h2
    rwa [thick_zeroSec_apply] at h2
  obtain ⟨bₐ, hbₐ⟩ := he _ hW'U
  revert hW
  rw [← hW']
  intro hW
  exact exists_basis_thick_preimage c A c' hw hover U (zeroSec c A ⁻¹ᵁ W) hW'U hW'aff
    (fun i => (show Γ(Limits.pullback c' (specMap R A), f.hom ⁻¹ᵁ U) from e i)) bₐ hbₐ hW
end AlgebraicGeometry.RelPicard
end ProofImplementation
