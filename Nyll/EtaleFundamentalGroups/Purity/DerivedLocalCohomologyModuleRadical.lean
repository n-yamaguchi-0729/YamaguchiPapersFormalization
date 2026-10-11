/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyInjectiveComplex
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionComplexZero
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionFunctor
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Linear radical invariance of local cohomology

Ideals with the same radical define the same torsion submodule. Comparing
these submodules before applying a common injective resolution gives an
isomorphism on homology that retains its scalar action.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

open CategoryTheory

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
private theorem primaryComponent_le_of_pow_le
    (M : ModuleCat.{u} R) {I J : Ideal R} {k : ℕ} (hk : J ^ k ≤ I) :
    Ideal.primaryComponent M I ≤ Ideal.primaryComponent M J := by
  intro z hz
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (M := M) (I := I) z).mp hz
  apply (Ideal.primaryComponent_mem (M := M) (I := J) z).mpr
  refine ⟨k * n, ?_⟩
  apply (Submodule.mem_torsionBySet_iff ((J ^ (k * n) : Ideal R) : Set R) z).mpr
  intro a
  have hle : J ^ (k * n) ≤ I ^ n := by
    rw [pow_mul]
    exact pow_le_pow_left' hk n
  exact (Submodule.mem_torsionBySet_iff ((I ^ n : Ideal R) : Set R) z).mp hn
    ⟨a, hle a.property⟩

/-- Power torsion agrees as a submodule for ideals with the same radical. -/
theorem primaryComponent_eq_of_sameRadical
    (M : ModuleCat.{u} R) {I J : Ideal R} (hIJ : I.radical = J.radical) :
    Ideal.primaryComponent M I = Ideal.primaryComponent M J := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (show J ≤ I.radical by rw [hIJ]; exact Ideal.le_radical)
    (IsNoetherian.noetherian J)
  obtain ⟨l, hl⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (show I ≤ J.radical by rw [← hIJ]; exact Ideal.le_radical)
    (IsNoetherian.noetherian I)
  exact le_antisymm (primaryComponent_le_of_pow_le M hk)
    (primaryComponent_le_of_pow_le M hl)

private def submoduleEqualityIso (M : ModuleCat.{u} R)
    (N P : Submodule R M) (h : N = P) : ModuleCat.of R N ≅ ModuleCat.of R P where
  hom := ModuleCat.ofHom (Submodule.inclusion h.le)
  inv := ModuleCat.ofHom (Submodule.inclusion h.ge)
  hom_inv_id := by
    ext z
    rfl
  inv_hom_id := by
    ext z
    rfl

private def primaryComponentIsoOfSameRadical
    (M : ModuleCat.{u} R) {I J : Ideal R} (hIJ : I.radical = J.radical) :
    ModuleCat.of R (Ideal.primaryComponent M I) ≅
      ModuleCat.of R (Ideal.primaryComponent M J) :=
  submoduleEqualityIso M _ _ (primaryComponent_eq_of_sameRadical M hIJ)

omit [IsNoetherianRing R] in
private theorem submoduleEqualityIso_naturality
    (M N : ModuleCat.{u} R) (A B : Submodule R M) (C D : Submodule R N)
    (hAB : A = B) (hCD : C = D) (f : M →ₗ[R] N)
    (hAC : ∀ z : A, f z ∈ C) (hBD : ∀ z : B, f z ∈ D) :
    ModuleCat.ofHom ((f.domRestrict A).codRestrict C hAC) ≫
        (submoduleEqualityIso N C D hCD).hom =
      (submoduleEqualityIso M A B hAB).hom ≫
        ModuleCat.ofHom ((f.domRestrict B).codRestrict D hBD) := by
  ext z
  rfl

/-- The identity on torsion elements gives a natural linear comparison. -/
def idealPowerTorsionFunctorIsoOfSameRadical
    {I J : Ideal R} (hIJ : I.radical = J.radical) :
    idealPowerTorsionFunctor I ≅ idealPowerTorsionFunctor J :=
  NatIso.ofComponents (fun M => primaryComponentIsoOfSameRadical M hIJ)
    (by
      intro M N f
      exact submoduleEqualityIso_naturality M N _ _ _ _
        (primaryComponent_eq_of_sameRadical M hIJ)
        (primaryComponent_eq_of_sameRadical N hIJ) f.hom
        (fun z => Ideal.primaryComponent_map_mem I f.hom z)
        (fun z => Ideal.primaryComponent_map_mem J f.hom z))

/-- Comparing torsion term by term gives an actual isomorphism of complexes. -/
def idealPowerTorsionComplexIsoOfSameRadical
    {I J : Ideal R} (hIJ : I.radical = J.radical)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    idealPowerTorsionComplex I K ≅ idealPowerTorsionComplex J K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (idealPowerTorsionFunctorIsoOfSameRadical hIJ).app (K.X n))
    (fun i j _ => ((idealPowerTorsionFunctorIsoOfSameRadical hIJ).hom.naturality (K.d i j)).symm)

/-- Radical invariance for the canonical local-cohomology module, retaining
its full linear structure. -/
def derivedLocalCohomologyModuleLinearEquivOfSameRadical
    {I J : Ideal R} (hIJ : I.radical = J.radical)
    (M : ModuleCat.{u} R) (n : ℕ) :
    derivedLocalCohomologyModule I M n ≃ₗ[R] derivedLocalCohomologyModule J M n := by
  let T := injectiveResolution M
  let e := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
    (idealPowerTorsionComplexIsoOfSameRadical hIJ T.cocomplex)
  have hI : (derivedLocalCohomologyInjectiveComplex I T).homology n ≅
      derivedLocalCohomologyModule I M n := by
    cases n with
    | zero => exact derivedLocalCohomologyInjectiveComplexHomologyIsoZero I T
    | succ n => exact derivedLocalCohomologyInjectiveComplexHomologyIsoSucc I T n
  have hJ : (derivedLocalCohomologyInjectiveComplex J T).homology n ≅
      derivedLocalCohomologyModule J M n := by
    cases n with
    | zero => exact derivedLocalCohomologyInjectiveComplexHomologyIsoZero J T
    | succ n => exact derivedLocalCohomologyInjectiveComplexHomologyIsoSucc J T n
  exact (hI.symm ≪≫ e ≪≫ hJ).toLinearEquiv

end EtaleFundamentalGroups.Purity

end
