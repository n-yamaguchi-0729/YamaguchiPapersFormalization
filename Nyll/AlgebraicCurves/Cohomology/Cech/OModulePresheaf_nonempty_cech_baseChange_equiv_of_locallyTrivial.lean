/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_d_comp_d

/-!
Čech cohomology base-change equivalences for locally trivial module presheaves.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace LinearMap
open _root_.LinearMap
namespace HomologyTransport
open _root_.LinearMap

variable {S : Type u} [CommRing S]
variable {P₀ P₁ P₂ Q₀ Q₁ Q₂ : Type u}
  [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂]
  [AddCommGroup Q₀] [Module S Q₀] [AddCommGroup Q₁] [Module S Q₁] [AddCommGroup Q₂] [Module S Q₂]
variable (e₀ : P₀ ≃ₗ[S] Q₀) (e₁ : P₁ ≃ₗ[S] Q₁) (e₂ : P₂ ≃ₗ[S] Q₂)
variable (f : P₀ →ₗ[S] P₁) (g : P₁ →ₗ[S] P₂) (f' : Q₀ →ₗ[S] Q₁) (g' : Q₁ →ₗ[S] Q₂)
variable (hf : e₁.toLinearMap ∘ₗ f = f' ∘ₗ e₀.toLinearMap) (hg : e₂.toLinearMap ∘ₗ g = g' ∘ₗ
  e₁.toLinearMap)

include hf in
theorem apply_f (x : P₀) : e₁ (f x) = f' (e₀ x) := by
  exact LinearMap.congr_fun hf x

include hf in
theorem comap_ker : (LinearMap.ker f').comap e₀.toLinearMap = LinearMap.ker f := by
  ext x
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearMap.mem_ker]
  rw [← apply_f e₀ e₁ f f' hf, map_eq_zero_iff _ e₁.injective]

/-- The equivalence of kernels induced by a commutative square of linear equivalences. -/
def kerEquiv : LinearMap.ker f ≃ₗ[S] LinearMap.ker f' :=
  (LinearEquiv.ofEq _ _ (comap_ker e₀ e₁ f f' hf).symm).trans (e₀.ofSubmodule' (LinearMap.ker f'))

theorem kerEquiv_apply_coe (x : LinearMap.ker f) : (kerEquiv e₀ e₁ f f' hf x : Q₀) = e₀ x := rfl

include hf hg in
theorem comap_kerEquiv_comap_range :
    ((LinearMap.range f').comap (LinearMap.ker g').subtype).comap (kerEquiv e₁ e₂ g g'
      hg).toLinearMap
      = (LinearMap.range f).comap (LinearMap.ker g).subtype := by
  ext z
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, Submodule.coe_subtype, LinearMap.mem_range,
    kerEquiv_apply_coe]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e₀.symm y, e₁.injective ?_⟩
    rw [apply_f e₀ e₁ f f' hf, e₀.apply_symm_apply, hy]
  · rintro ⟨x, hx⟩
    exact ⟨e₀ x, by rw [← apply_f e₀ e₁ f f' hf, hx]⟩

include hf hg in
theorem map_kerEquiv_comap_range :
    ((LinearMap.range f).comap (LinearMap.ker g).subtype).map (kerEquiv e₁ e₂ g g' hg).toLinearMap
      = (LinearMap.range f').comap (LinearMap.ker g').subtype := by
  rw [← comap_kerEquiv_comap_range e₀ e₁ e₂ f g f' g' hf hg]
  exact Submodule.map_comap_eq_of_surjective (kerEquiv e₁ e₂ g g' hg).surjective _

end LinearMap.HomologyTransport

namespace LinearMap
open _root_.LinearMap
namespace FlatKerBC
open _root_.LinearMap

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {M₀ M₁ M₂ : Type u} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]
variable (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)

theorem subtype_baseChange_injective [Module.Flat R A] :
    Function.Injective ((LinearMap.ker g).subtype.baseChange A) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := A) (LinearMap.ker g).subtype
    (LinearMap.ker g).injective_subtype

theorem range_subtype_baseChange [Module.Flat R A] :
    LinearMap.range ((LinearMap.ker g).subtype.baseChange A) = LinearMap.ker (g.baseChange A) := by
  have hexact : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  have hexA : Function.Exact ((LinearMap.ker g).subtype.baseChange A) (g.baseChange A) := by
    have := Module.Flat.lTensor_exact A hexact
    intro y; exact this y
  exact hexA.linearMap_ker_eq.symm

/-- The canonical equivalence between the base change of a kernel and the base-changed kernel. -/
def theta [Module.Flat R A] : A ⊗[R] LinearMap.ker g ≃ₗ[A] LinearMap.ker (g.baseChange A) :=
  (LinearEquiv.ofInjective _ (subtype_baseChange_injective A g)).trans
    (LinearEquiv.ofEq _ _ (range_subtype_baseChange A g))

theorem theta_apply_coe [Module.Flat R A] (z : A ⊗[R] LinearMap.ker g) :
    (theta A g z : A ⊗[R] M₁) = ((LinearMap.ker g).subtype.baseChange A) z := rfl

variable (hgf : g ∘ₗ f = 0)

/-- The first differential with codomain restricted to the kernel of the next differential. -/
def toKer : M₀ →ₗ[R] LinearMap.ker g :=
  LinearMap.codRestrict (LinearMap.ker g) f fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hgf, LinearMap.zero_apply]

theorem subtype_comp_toKer : (LinearMap.ker g).subtype ∘ₗ toKer f g hgf = f := rfl

theorem range_toKer : LinearMap.range (toKer f g hgf) = (LinearMap.range f).comap (LinearMap.ker
  g).subtype := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨y, hy⟩ ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

include hgf in
theorem comap_theta [Module.Flat R A] :
    ((LinearMap.range (f.baseChange A)).comap (LinearMap.ker (g.baseChange A)).subtype).comap
        (theta A g).toLinearMap
      = LinearMap.range ((toKer f g hgf).baseChange A) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, subtype_baseChange_injective A g ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_toKer, hx]
    rfl
  · rintro _ ⟨x, rfl⟩
    change (((theta A g) ((toKer f g hgf).baseChange A x) : LinearMap.ker (g.baseChange A)) : A
      ⊗[R] M₁)
      ∈ LinearMap.range (f.baseChange A)
    rw [theta_apply_coe, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_toKer]
    exact LinearMap.mem_range_self _ x

include hgf in
theorem nonempty_quotEquiv :
    Nonempty (((A ⊗[R] LinearMap.ker g) ⧸ LinearMap.range ((toKer f g hgf).baseChange A))
      ≃ₗ[A] A ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype)) := by
  have hr : LinearMap.range (toKer f g hgf) = (LinearMap.range f).comap (LinearMap.ker g).subtype :=
    range_toKer f g hgf
  have hexact : Function.Exact (toKer f g hgf) ((LinearMap.range f).comap (LinearMap.ker
    g).subtype).mkQ := by
    rw [← hr]; exact LinearMap.exact_map_mkQ_range _
  have hsurj : Function.Surjective ((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ :=
    Submodule.mkQ_surjective _
  have hexA : Function.Exact ((toKer f g hgf).baseChange A)
      (((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ.baseChange A) := by
    have := lTensor_exact A hexact hsurj
    intro y; exact this y
  have hsurjA : Function.Surjective (((LinearMap.range f).comap (LinearMap.ker
    g).subtype).mkQ.baseChange A) := by
    have := LinearMap.lTensor_surjective A hsurj
    intro y; exact this y
  exact ⟨hexA.linearEquivOfSurjective hsurjA⟩

end LinearMap.FlatKerBC

end

open LinearMap.HomologyTransport LinearMap.FlatKerBC in
theorem _root_.AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    (Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π
      (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
              (𝒰.baseChange π A)
        ≃ₗ[A] LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 0).baseChange A)) ∧
      ∀ i : ℕ, ∃ φ : LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)
        →ₗ[A]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc
              (𝒰.baseChange π A) i,
        Function.Surjective φ ∧
          LinearMap.ker φ = (LinearMap.range (((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange
            A)).comap
            (LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)).subtype) ∧
    (Module.Flat R A →
      Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π
        (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
              (𝒰.baseChange π A)
          ≃ₗ[A] A ⊗[R] (OModulePresheaf.ofModules π M).H0 𝒰) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π
        (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc
              (𝒰.baseChange π A) i
          ≃ₗ[A] A ⊗[R] (OModulePresheaf.ofModules π M).HSucc 𝒰 i)) := by
  obtain ⟨E, hEd, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial π 𝒰 M
      htriv A
  have h0 : Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π
    (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
              (𝒰.baseChange π A)
        ≃ₗ[A] LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 0).baseChange A)) :=
    ⟨(kerEquiv (E 0) (E 1) _ _ (hEd 0)).symm⟩
  have h1 : ∀ i : ℕ, ∃ φ : LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i +
    1)).baseChange A) →ₗ[A]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc
              (𝒰.baseChange π A) i,
        Function.Surjective φ ∧
          LinearMap.ker φ = (LinearMap.range (((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange
            A)).comap
            (LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)).subtype
              := by
    intro i
    let κ := kerEquiv (E (i + 1)) (E (i + 2)) _ _ (hEd (i + 1))
    refine ⟨(Submodule.mkQ _) ∘ₗ κ.toLinearMap, ?_, ?_⟩
    · exact (Submodule.mkQ_surjective _).comp κ.surjective
    · rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      exact comap_kerEquiv_comap_range (E i) (E (i + 1)) (E (i + 2)) _ _ _ _ (hEd i) (hEd (i + 1))
  refine ⟨⟨h0, h1⟩, fun hflat => ?_⟩
  have := hflat
  have hdd : ∀ i : ℕ, (OModulePresheaf.ofModules π M).d 𝒰 (i + 1) ∘ₗ (OModulePresheaf.ofModules
    π M).d 𝒰 i = 0 :=
    fun i => AlgebraicGeometry.OModulePresheaf.d_comp_d _ 𝒰 i
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨e'⟩ := h0
    exact ⟨e' ≪≫ₗ (theta A ((OModulePresheaf.ofModules π M).d 𝒰 0)).symm⟩
  · let κ := kerEquiv (E (i + 1)) (E (i + 2)) (((OModulePresheaf.ofModules π M).d 𝒰 (i +
      1)).baseChange A)
      _ (hEd (i + 1))
    let Φ := (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1))).trans κ
    have hΦ : (LinearMap.range ((toKer ((OModulePresheaf.ofModules π M).d 𝒰 i)
          ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)) (hdd i)).baseChange A)).map Φ.toLinearMap
        = (LinearMap.range ((OModulePresheaf.ofModules (Limits.pullback.snd π
          (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d
              (𝒰.baseChange π A) i)).comap
          (LinearMap.ker ((OModulePresheaf.ofModules (Limits.pullback.snd π
            (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d
              (𝒰.baseChange π A) (i + 1))).subtype := by
      rw [← map_kerEquiv_comap_range (E i) (E (i + 1)) (E (i + 2)) _ _ _ _ (hEd i) (hEd (i + 1)),
        ← comap_theta A ((OModulePresheaf.ofModules π M).d 𝒰 i) ((OModulePresheaf.ofModules π
          M).d 𝒰 (i + 1)) (hdd i)]
      change Submodule.map (κ.toLinearMap ∘ₗ (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i +
        1))).toLinearMap) _ = _
      rw [Submodule.map_comp, Submodule.map_comap_eq_of_surjective
        (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1))).surjective]
    obtain ⟨e₁⟩ := nonempty_quotEquiv A ((OModulePresheaf.ofModules π M).d 𝒰 i)
      ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)) (hdd i)
    let e₂ := Submodule.Quotient.equiv _ _ Φ hΦ
    exact ⟨e₂.symm ≪≫ₗ e₁⟩
end OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
