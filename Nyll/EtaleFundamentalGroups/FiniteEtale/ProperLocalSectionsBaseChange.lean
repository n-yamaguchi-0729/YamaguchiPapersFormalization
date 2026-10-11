/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullbackLocalSection_of_forall_subsingleton_HSucc.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperLocalH0BaseChange
import Nyll.AlgebraicCurves.Cohomology.Scheme_Modules_finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullbackLocalSection_of_forall_subsingleton_HSucc
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.SchemeTheory.Modules.Invertible

/-!
# Actual section base change for proper geometrically reduced local families

The closed-fibre theorem supplies finite projectivity and kernel base change
without a reduced-base or higher-cohomology-vanishing assumption. The final
section/cochain construction is adapted from the attributed FLT source above.
It retains the exact formula on pure tensors of actual global sections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

open AlgebraicCurves.Cohomology.Proofs.ProjectiveSectionsBaseChange.P2mSectionsBaseChangeH0
open Scheme.TwoAffineOpenCover
open OModulePresheaf

/-- Étaleness of closed-fibre sections gives finite projective global sections
and arbitrary base change, with the actual pullback-unit formula. -/
theorem finite_projective_sections_and_baseChange_of_proper_flat_of_etale_closedFiber
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f]
    (hEtaleFiber : (pullback.snd f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop.hom.Etale) :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let : Module R Γ(M, ⊤) := moduleSectionsOfHom f M ⊤
    (Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        let : Module A Γ((Scheme.Modules.pullback
            (pullback.fst f (specMap R A))).obj M, ⊤) :=
          moduleSectionsOfHom (pullback.snd f (specMap R A))
            ((Scheme.Modules.pullback (pullback.fst f (specMap R A))).obj M) ⊤
        ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
            Γ((Scheme.Modules.pullback (pullback.fst f (specMap R A))).obj M, ⊤),
          ∀ (a : A) (s : Γ(M, ⊤)), e (a ⊗ₜ[R] s) =
            a • (show Γ((Scheme.Modules.pullback
                (pullback.fst f (specMap R A))).obj M, ⊤) from
              pullbackLocalSection (pullback.fst f (specMap R A)) s) := by
  intro M hRΓ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := coverOfCompact X
  let F := OModulePresheaf.ofModules f M
  have htriv := (Scheme.Modules.isInvertible_unit X).exists_trivialization
  obtain ⟨hfin, hproj, hbij⟩ :=
    finite_projective_H0_and_bijective_baseChange_of_proper_flat_of_etale_closedFiber
      f 𝒰 hEtaleFiber
  let ε₀ : Γ(M, ⊤) ≃ₗ[R] F.H0 𝒰 := sectionsEquivH0 f M 𝒰
  have : Module.Finite R (F.H0 𝒰) := hfin
  have : Module.Projective R (F.H0 𝒰) := hproj
  refine ⟨⟨Module.Finite.equiv ε₀.symm, Module.Projective.of_equiv ε₀.symm⟩, ?_⟩
  intro A _ _ hAΓ
  let p₁ := Limits.pullback.fst f (specMap R A)
  let p₂ := Limits.pullback.snd f (specMap R A)
  let MA : (Limits.pullback f (specMap R A)).Modules := (Scheme.Modules.pullback p₁).obj M
  let FA := OModulePresheaf.ofModules p₂ MA
  obtain ⟨E, hEd, hEf⟩ := OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial f 𝒰 M
    htriv A
  let e1 : Γ(MA, ⊤) ≃ₗ[A] FA.H0 (𝒰.baseChange f A) := sectionsEquivH0 p₂ MA (𝒰.baseChange f A)
  let e2 : LinearMap.ker ((F.d 𝒰 0).baseChange A) ≃ₗ[A] FA.H0 (𝒰.baseChange f A) :=
    kerEquivOfEquiv ((F.d 𝒰 0).baseChange A) (FA.d (𝒰.baseChange f A) 0) (E 0) (E 1) (hEd 0)
  let e3 : A ⊗[R] F.H0 𝒰 ≃ₗ[A] LinearMap.ker ((F.d 𝒰 0).baseChange A) :=
    LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (F.d 𝒰 0) A) (hbij A)
  let e0 : A ⊗[R] Γ(M, ⊤) ≃ₗ[A] A ⊗[R] F.H0 𝒰 := ε₀.baseChange R A _ _
  let e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A] Γ(MA, ⊤) := e0.trans (e3.trans (e2.trans e1.symm))
  have key : ∀ m : Γ(M, ⊤), e1 (unitApp p₁ M ⊤ m) = e2 (e3 ((1 : A) ⊗ₜ[R] ε₀ m)) := by
    intro m
    apply Subtype.ext
    rw [coe_kerEquivOfEquiv]
    change ((e1 _ : FA.H0 (𝒰.baseChange f A)) : FA.cochain (𝒰.baseChange f A) 0) =
      E 0 ((TwoChartCech.kerBaseChangeHom (F.d 𝒰 0) A ((1 : A) ⊗ₜ[R] ε₀ m) : A ⊗[R] F.cochain 𝒰 0))
    dsimp only [e1]
    rw [TwoChartCech.kerBaseChangeHom_apply_coe, LinearMap.baseChange_tmul, Submodule.subtype_apply,
      coe_sectionsEquivH0]
    funext s
    rw [hEf 0 1 (toCochain f M 𝒰 m) s, one_smul]
    have h2 := unitApp_map p₁ M (homOfLE (le_top : 𝒰.inter s ≤ ⊤))
      (homOfLE (le_top : p₁ ⁻¹ᵁ 𝒰.inter s ≤ p₁ ⁻¹ᵁ ⊤)) m
    change MA.presheaf.map (homOfLE (le_top : (𝒰.baseChange f A).inter s ≤ ⊤)).op (unitApp p₁ M ⊤ m)
      = FA.res (𝒰.baseChange_inter_le f A s)
        (unitApp p₁ M (𝒰.inter s) (M.presheaf.map (homOfLE (le_top : 𝒰.inter s ≤ ⊤)).op m))
    rw [h2, OModulePresheaf.ofModules_res_apply]
    exact (map_map MA _ _ _ _).symm
  have key1 : ∀ m : Γ(M, ⊤), e ((1 : A) ⊗ₜ[R] m) = unitApp p₁ M ⊤ m := by
    intro m
    have h0 : e0 ((1 : A) ⊗ₜ[R] m) = (1 : A) ⊗ₜ[R] ε₀ m :=
      by simp only [e0, LinearEquiv.baseChange_tmul]
    exact (congrArg (fun z => e1.symm (e2 (e3 z))) h0).trans
      ((congrArg e1.symm (key m).symm).trans
        (e1.symm_apply_apply (show Γ(MA, ⊤) from unitApp p₁ M ⊤ m)))
  have key2 : ∀ (a : A) (m : Γ(M, ⊤)), e (a ⊗ₜ[R] m) = a • (show Γ(MA, ⊤) from unitApp p₁ M ⊤ m) :=
    by
    intro a m
    have hsm : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) :=
      by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsm, e.map_smul, key1]
  exact ⟨e, fun a m => key2 a m⟩

/-- For the actual structure sheaf, proper flat geometrically reduced families
over a Noetherian local ring have finite projective global sections and an
arbitrary base-change equivalence with the actual pullback-unit formula. -/
theorem finite_projective_sections_and_baseChange_of_proper_flat_geometricallyReduced_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [GeometricallyReduced f] :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let : Module R Γ(M, ⊤) := moduleSectionsOfHom f M ⊤
    (Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        let : Module A Γ((Scheme.Modules.pullback
            (pullback.fst f (specMap R A))).obj M, ⊤) :=
          moduleSectionsOfHom (pullback.snd f (specMap R A))
            ((Scheme.Modules.pullback (pullback.fst f (specMap R A))).obj M) ⊤
        ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
            Γ((Scheme.Modules.pullback (pullback.fst f (specMap R A))).obj M, ⊤),
          ∀ (a : A) (s : Γ(M, ⊤)), e (a ⊗ₜ[R] s) =
            a • (show Γ((Scheme.Modules.pullback
                (pullback.fst f (specMap R A))).obj M, ⊤) from
              pullbackLocalSection (pullback.fst f (specMap R A)) s) := by
  exact finite_projective_sections_and_baseChange_of_proper_flat_of_etale_closedFiber f
    (finite_etale_appTop_of_isProper_of_geometricallyReduced_overField
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).2

end AlgebraicGeometry.Scheme.Modules
