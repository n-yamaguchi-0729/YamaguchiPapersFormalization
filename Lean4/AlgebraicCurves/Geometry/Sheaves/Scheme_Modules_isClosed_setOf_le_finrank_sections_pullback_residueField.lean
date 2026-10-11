/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Spectrum.Prime.Module
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import SchemeTheory.Cohomology.Sheaves.CoherentBaseChange
import SchemeTheory.Cohomology.Cech.TwoChartCech
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
import AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique

/-!
# Upper semicontinuity of the dimension of sections

Degree-zero Cech cohomology computes global sections and supplies the base-change
comparison used in the final statement.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  TensorProduct

namespace P2mSemicontH0

section FibreDim

variable {R : Type u} [CommRing R]

/-- The dimension of the residue-field fibre of a module. -/
noncomputable abbrev fibreDim (Q : Type u) [AddCommGroup Q] [Module R Q]
    (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] Q)

variable {Q : Type u} [AddCommGroup Q] [Module R Q]

/-- Base change identifies the cokernel of a linear map with the cokernel after base change. -/
noncomputable def baseChangeCokerEquiv {P : Type u} [AddCommGroup P] [Module R P]
    (φ : P →ₗ[R] Q) (A : Type u) [CommRing A] [Algebra R A] :
    ((A ⊗[R] Q) ⧸ LinearMap.range (φ.baseChange A)) ≃ₗ[A]
      A ⊗[R] (Q ⧸ LinearMap.range φ) := by
  have hex : Function.Exact φ (LinearMap.range φ).mkQ := LinearMap.exact_map_mkQ_range φ
  have hsurj : Function.Surjective (LinearMap.range φ).mkQ := Submodule.mkQ_surjective _
  have hexA : Function.Exact (φ.baseChange A) ((LinearMap.range φ).mkQ.baseChange A) := by
    have h := lTensor_exact A hex hsurj
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h
  exact hexA.linearEquivOfSurjective (LinearMap.baseChange_surjective A hsurj)

theorem fibreDim_le_card {ι : Type u} [Fintype ι] (φ : (ι → R) →ₗ[R] Q) (𝔮 : PrimeSpectrum R)
    (h : Subsingleton (𝔮.asIdeal.ResidueField ⊗[R] (Q ⧸ LinearMap.range φ))) :
    fibreDim Q 𝔮 ≤ Fintype.card ι := by
  have : Nontrivial R := ⟨⟨0, 1, fun h => 𝔮.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ 𝔮.asIdeal.zero_mem))⟩⟩
  set K := 𝔮.asIdeal.ResidueField
  have hrange : LinearMap.range (φ.baseChange K) = ⊤ := by
    rw [← Submodule.Quotient.subsingleton_iff]
    exact (baseChangeCokerEquiv φ K).toEquiv.subsingleton
  have hsurj : Function.Surjective (φ.baseChange K) := LinearMap.range_eq_top.mp hrange
  calc fibreDim Q 𝔮 ≤ Module.finrank K (K ⊗[R] (ι → R)) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = Fintype.card ι := by
        rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card]

theorem exists_family_card_eq (𝔭 : PrimeSpectrum R) [Module.Finite R Q] :
    ∃ (ι : Type u) (_ : Fintype ι) (q : ι → Q),
      Fintype.card ι = fibreDim Q 𝔭 ∧
        Subsingleton (𝔭.asIdeal.ResidueField ⊗[R]
          (Q ⧸ LinearMap.range (Fintype.linearCombination R q))) := by
  set K := 𝔭.asIdeal.ResidueField
  have hspan : Submodule.span K (Set.range (TensorProduct.mk R K Q 1)) = ⊤ := by
    have h := (Submodule.baseChange_eq_span (p := (⊤ : Submodule R Q)) (A := K)).symm.trans
      (Submodule.baseChange_top (R := R) (M := Q) (A := K))
    rwa [Submodule.map_coe, Submodule.top_coe, Set.image_univ] at h
  obtain ⟨ι, a, -, hspan', hli⟩ := exists_linearIndependent' (K := K) (TensorProduct.mk R K Q 1)
  rw [hspan] at hspan'
  let b : Module.Basis ι K (K ⊗[R] Q) := Module.Basis.mk hli hspan'.ge
  have : IsNoetherian K (K ⊗[R] Q) := IsNoetherian.iff_fg.2 inferInstance
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  refine ⟨ι, inferInstance, a, (Module.finrank_eq_card_basis b).symm, ?_⟩
  classical
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R a
  have hrange : LinearMap.range (φ.baseChange K) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨1 ⊗ₜ[R] Pi.single i 1, ?_⟩
    rw [LinearMap.baseChange_tmul, Module.Basis.coe_mk]
    change (1 : K) ⊗ₜ[R] φ (Pi.single i 1) = (1 : K) ⊗ₜ[R] a i
    rw [Fintype.linearCombination_apply_single, one_smul]
  have : Subsingleton ((K ⊗[R] Q) ⧸ LinearMap.range (φ.baseChange K)) :=
    Submodule.Quotient.subsingleton_iff.mpr hrange
  exact (baseChangeCokerEquiv φ K).symm.toEquiv.subsingleton

theorem isClosed_setOf_le_fibreDim [Module.Finite R Q] (m : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R | m ≤ fibreDim Q 𝔭} := by
  rw [← isOpen_compl_iff]
  have hset : {𝔭 : PrimeSpectrum R | m ≤ fibreDim Q 𝔭}ᶜ = {𝔭 | fibreDim Q 𝔭 < m} := by
    ext 𝔭; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hset, isOpen_iff_forall_mem_open]
  intro 𝔭 h𝔭
  obtain ⟨ι, _, q, hcard, hsub⟩ := exists_family_card_eq (Q := Q) 𝔭
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R q
  let Q' := Q ⧸ LinearMap.range φ
  refine ⟨(Module.support R Q')ᶜ, ?_, Module.isClosed_support.isOpen_compl, ?_⟩
  · intro 𝔮 h𝔮
    have h𝔮' : Subsingleton (𝔮.asIdeal.ResidueField ⊗[R] Q') := by
      rw [Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
        not_nontrivial_iff_subsingleton] at h𝔮
      exact h𝔮
    calc fibreDim Q 𝔮 ≤ Fintype.card ι := fibreDim_le_card φ 𝔮 h𝔮'
      _ = fibreDim Q 𝔭 := hcard
      _ < m := h𝔭
  · rw [Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
    exact hsub

end FibreDim

section TwoTerm

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)

theorem fibreH0_add_finrank (𝔭 : PrimeSpectrum R) :
    G.fibreH0 𝔭 + Module.finrank R G.C1 =
      Module.finrank R G.C0 + fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭 := by
  have : Nontrivial R := ⟨⟨0, 1, fun h => 𝔭.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ 𝔭.asIdeal.zero_mem))⟩⟩
  set K := 𝔭.asIdeal.ResidueField
  set dK := G.d.baseChange K
  have h1 : Module.finrank K (LinearMap.range dK) + Module.finrank K (LinearMap.ker dK) =
      Module.finrank K (K ⊗[R] G.C0) := LinearMap.finrank_range_add_finrank_ker dK
  have h2 : Module.finrank K (K ⊗[R] G.C0) = Module.finrank R G.C0 := Module.finrank_baseChange
  have h3 : Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range dK) +
      Module.finrank K (LinearMap.range dK) = Module.finrank K (K ⊗[R] G.C1) :=
    Submodule.finrank_quotient_add_finrank _
  have h4 : Module.finrank K (K ⊗[R] G.C1) = Module.finrank R G.C1 := Module.finrank_baseChange
  have h5 : Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range dK) =
      fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭 := (baseChangeCokerEquiv G.d K).finrank_eq
  have h0 : G.fibreH0 𝔭 = Module.finrank K (LinearMap.ker dK) := rfl
  omega

theorem isClosed_setOf_le_fibreH0 (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭} := by
  have hset : {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭} =
      {𝔭 | n + Module.finrank R G.C1 - Module.finrank R G.C0 ≤
        fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭} := by
    ext 𝔭
    simp only [Set.mem_ofPred_eq]
    have := fibreH0_add_finrank G 𝔭
    omega
  rw [hset]
  exact isClosed_setOf_le_fibreDim _

end TwoTerm

section Cover

/-- A finite ordered affine cover obtained from the canonical affine cover. -/
def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Cover

section H0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

/-- The degree-zero Cech cochain obtained by restricting a global section. -/
def toCochain :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) →ₗ[R] (OModulePresheaf.ofModules π M).cochain K 0 :=
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearMap.pi fun s => (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)

theorem toCochain_apply' (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)
      (show (OModulePresheaf.ofModules π M).obj ⊤ from x) := rfl

theorem d_toCochain (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x) = 0 := by
  funext s
  change ((OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x)) s =
    (0 : Γ(M, K.inter s))
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, toCochain_apply']
  have hres (j : Fin 2) := (OModulePresheaf.ofModules π M).res_res
    (K.inter_le_inter_face s j) (le_top : K.inter (K.face s j) ≤ ⊤)
    (show (OModulePresheaf.ofModules π M).obj ⊤ from x)
  exact (congrArg₂ (fun a b : Γ(M, K.inter s) => a + -b) (hres 0) (hres 1)).trans
    (add_neg_cancel ((OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤) x))

theorem toCochain_mem (x : Γ(M, ⊤)) : toCochain π M K x ∈ (OModulePresheaf.ofModules π M).H0 K :=
  d_toCochain π M K x

theorem toCochain_injective : Function.Injective (toCochain π M K) := by
  intro x y hxy
  obtain ⟨z, -, huniq⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K _).mp
    (d_toCochain π M K x)
  exact (huniq x fun s => rfl).trans (huniq y fun s => by rw [hxy]; rfl).symm

theorem exists_toCochain_eq (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hc : c ∈ (OModulePresheaf.ofModules π M).H0 K) : ∃ x : Γ(M, ⊤), toCochain π M K x = c := by
  obtain ⟨x, hx, -⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K c).mp hc
  exact ⟨x, funext fun s => (hx s).symm⟩

/-- Degree-zero Cech cocycles identify with global sections of the module. -/
def H0Equiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    (OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] Γ(M, ⊤) :=
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  (LinearEquiv.ofBijective (LinearMap.codRestrict ((OModulePresheaf.ofModules π M).H0 K)
      (toCochain π M K) (toCochain_mem π M K))
    ⟨fun x y h => toCochain_injective π M K (congrArg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := exists_toCochain_eq π M K c hc
      exact ⟨x, rfl⟩⟩).symm

end H0

section Main

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem main
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit
        U.toScheme.ringCatSheaf))
    (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
            𝔭.asIdeal.ResidueField))).obj M) ⊤
      n ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
            𝔭.asIdeal.ResidueField))).obj M, ⊤)} := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := coverOfCompact X
  obtain ⟨G, ι0, ι1, comm, hbij⟩ :=
    OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules f M htriv 𝒰
  have key : ∀ 𝔭 : PrimeSpectrum R,
      (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj
          M) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj
          M, ⊤))
        = G.fibreH0 𝔭 := by
    intro 𝔭
    let K := 𝔭.asIdeal.ResidueField
    let p₁ := Limits.pullback.fst f (specMap R K)
    let p₂ := Limits.pullback.snd f (specMap R K)
    let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ ((Scheme.Modules.pullback p₁).obj M) ⊤
    obtain ⟨⟨⟨e1⟩, -⟩, -⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial f 𝒰
      M htriv K
    let e2 := H0Equiv p₂ ((Scheme.Modules.pullback p₁).obj M) (𝒰.baseChange f K)
    let e3 := LinearEquiv.ofBijective
      (TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm K)
        (hbij K)
    exact (e2.symm.trans (e1.trans e3.symm)).finrank_eq
  have hset : {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj
          M) ⊤
      n ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj
          M, ⊤)}
      = {𝔭 | n ≤ G.fibreH0 𝔭} := by
    ext 𝔭
    simp only [Set.mem_ofPred_eq]
    rw [← key 𝔭]
  rw [hset]
  exact isClosed_setOf_le_fibreH0 G n

end Main

end P2mSemicontH0

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_finrank_sections_pullback_residueField
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit
        U.toScheme.ringCatSheaf))
    (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
            𝔭.asIdeal.ResidueField))).obj M) ⊤
      n ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R
            𝔭.asIdeal.ResidueField))).obj M, ⊤)} :=
  P2mSemicontH0.main f M htriv n
end Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
attribute [-instance] ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
attribute [-simp] DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
