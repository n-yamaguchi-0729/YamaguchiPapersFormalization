/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_exists_fibreH0Family.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Cohomology.Sheaves.CoherentBaseChangeFamily
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_finrank_ker_baseChange_eq_of_field_extension
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_nonempty_kerBaseChangeTowerEquiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
Fibre dimension data for a finite two-term kernel after pullback to a scheme over the base ring.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_exists_fibreH0Family

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

namespace TwoChartCech
open _root_.TwoChartCech
open _root_.TwoChartCech
namespace Family

/-- The base change of a finite free two term complex to an algebra over the original ring. -/
def baseChangeTTC {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
    (S : Type u) [CommRing S] [Algebra R S] : CoherentBaseChange.TwoTermComplex.{u, u} S :=
  haveI : Module.Finite S (S ⊗[R] G.C0) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R G.C0))
  haveI : Module.Finite S (S ⊗[R] G.C1) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R G.C1))
  { C0 := S ⊗[R] G.C0, C1 := S ⊗[R] G.C1, d := G.d.baseChange S }

/-- The algebra structure on an open section ring induced by the morphism to the affine base. -/
@[reducible] def algebraOfHom' {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R))
  (U : T.Opens) :
    Algebra R Γ(T, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

theorem specMap_algebraMap_eq {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (U
    : T.Opens)
    (hU : IsAffineOpen U) :
    letI := algebraOfHom' f U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, U))) = hU.fromSpec ≫ f := by
  let := algebraOfHom' f U
  have halg : (algebraMap R Γ(T, U)) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom :=
    rfl
  rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ←
    IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU (le_top : U ≤ f ⁻¹ᵁ
      ⊤)]

theorem base_eq_comap {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (U :
    T.Opens)
    (hU : IsAffineOpen U) (x : U) :
    letI := algebraOfHom' f U
    f.base x.1 = PrimeSpectrum.comap (algebraMap R Γ(T, U)) (hU.primeIdealOf x) := by
  let := algebraOfHom' f U
  have h1 : f.base x.1 = (hU.fromSpec ≫ f).base (hU.primeIdealOf x) := by
    rw [Scheme.Hom.comp_base]
    erw [TopCat.comp_app, hU.fromSpec_primeIdealOf x]
  rw [h1, ← specMap_algebraMap_eq f U hU]
  rfl

end Family

open Family

private theorem nativeSpecPrime {R : Type u} [CommRing R] (p : Spec (.of R)) :
    p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime

attribute [local instance] nativeSpecPrime

theorem exists_fibreH0Family'
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) :
    ∃ F : CoherentBaseChange.FibreH0Family T,
      ∀ x : T, F.h0 x = Module.finrank (f.base x).asIdeal.ResidueField
        (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField)) := by
  obtain ⟨G, ι0, ι1, comm, hG⟩ := exists_twoTermComplex_kerMapBaseChange_bijective d
  refine ⟨{ G := fun U hU => letI := algebraOfHom' f U; baseChangeTTC G Γ(T, U)
            h0 := fun x => Module.finrank (f.base x).asIdeal.ResidueField
              (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))
            hglue := ?_ }, fun x => rfl⟩
  intro U hU x
  let := algebraOfHom' f U
  let 𝔮 : PrimeSpectrum Γ(T, U) := hU.primeIdealOf x
  let 𝔭 : PrimeSpectrum R := f.base x.1
  have hpq : 𝔭.asIdeal = Ideal.comap (algebraMap R Γ(T, U)) 𝔮.asIdeal := by
    change (f.base x.1).asIdeal = _
    rw [base_eq_comap f U hU x]; rfl
  let φ : 𝔭.asIdeal.ResidueField →ₐ[R] 𝔮.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ 𝔭.asIdeal 𝔮.asIdeal (Algebra.ofId R Γ(T, U)) hpq
  let : Algebra 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  have : IsScalarTower R 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  rw [finrank_ker_baseChange_eq_of_field_extension d 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField]
  rw [← (LinearEquiv.ofBijective _ (hG 𝔮.asIdeal.ResidueField)).finrank_eq]
  obtain ⟨e, -⟩ := nonempty_kerBaseChangeTowerEquiv G.d Γ(T, U) 𝔮.asIdeal.ResidueField
  rw [← e.finrank_eq]
  rfl

end TwoChartCech

end
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_exists_fibreH0Family

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
theorem TwoChartCech.exists_fibreH0Family
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) :
    ∃ F : CoherentBaseChange.FibreH0Family T,
      ∀ x : T, letI := (f.base x).isPrime; F.h0 x =
        Module.finrank (f.base x).asIdeal.ResidueField
          (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField)) := by
  obtain ⟨F, hF⟩ :=
    TwoChartCech_exists_fibreH0Family.TwoChartCech.exists_fibreH0Family'
      (R := R) (C0 := C0) (C1 := C1) (d := d) (T := T) (f := f)
  refine ⟨F, fun x => ?_⟩
  exact hF x
end ProofImplementation
