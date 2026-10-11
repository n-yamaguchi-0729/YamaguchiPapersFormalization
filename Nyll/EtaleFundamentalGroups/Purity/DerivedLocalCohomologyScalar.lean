/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Scalar endomorphisms and torsion in derived local cohomology

Scalars act on each derived-Ext group in the ideal-powers diagram and commute
with its transition maps.  Their induced colimit endomorphisms describe the
scalar action without installing another module structure on the underlying
additive-group colimit.

An element of an ideal annihilates Ext out of the quotient by that ideal.
Consequently every local-cohomology class is annihilated by all members of
some power of its support ideal.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- Every member of `J` annihilates derived Ext out of `R / J`. -/
theorem derivedExt_quotient_smul_eq_zero
    (J : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (a : R) (ha : a ∈ J)
    (α : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ J)) M i) :
    a • α = 0 := by
  have h : a • 𝟙 (ModuleCat.of R (R ⧸ J)) = 0 := by
    ext
    simp only [LinearMap.comp_apply, ModuleCat.hom_smul, ModuleCat.hom_id,
      ModuleCat.hom_zero, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.zero_apply]
    calc
      a • (Submodule.mkQ J) 1 =
          (Submodule.mkQ J) (a • (1 : R)) :=
        (map_smul (Submodule.mkQ J) a (1 : R)).symm
      _ = 0 := by
        simpa only [smul_eq_mul, mul_one, Submodule.mkQ_apply,
          Ideal.Quotient.mk_eq_mk] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr ha : Ideal.Quotient.mk J a = 0)
  calc
    a • α =
        (CategoryTheory.Abelian.Ext.mk₀
          (a • 𝟙 (ModuleCat.of R (R ⧸ J)))).comp α (zero_add i) := by
      rw [CategoryTheory.Abelian.Ext.mk₀_smul,
        CategoryTheory.Abelian.Ext.smul_comp,
        CategoryTheory.Abelian.Ext.mk₀_id_comp]
    _ = 0 := by
      rw [h, CategoryTheory.Abelian.Ext.mk₀_zero,
        CategoryTheory.Abelian.Ext.zero_comp]

/-- Scalar multiplication is a natural endomorphism of the powers diagram. -/
def derivedLocalCohomologyPowersScalarMap
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) (a : R) :
    derivedLocalCohomologyPowersDiagram I M i ⟶
      derivedLocalCohomologyPowersDiagram I M i where
  app n := AddCommGrpCat.ofHom
    { toFun := fun α : CategoryTheory.Abelian.Ext.{u}
        (ModuleCat.of R (R ⧸ I ^ unop (unop n))) M i ↦ a • α
      map_zero' := smul_zero a
      map_add' := smul_add a }
  naturality {j k} f := by
    ext α
    let α' : CategoryTheory.Abelian.Ext.{u}
        (ModuleCat.of R (R ⧸ I ^ unop (unop j))) M i := α
    let q : ModuleCat.of R (R ⧸ I ^ unop (unop k)) ⟶
        ModuleCat.of R (R ⧸ I ^ unop (unop j)) :=
      (localCohomology.ringModIdeals
        (localCohomology.idealPowersDiagram I)).map f.unop
    change
      a • ((CategoryTheory.Abelian.Ext.mk₀ q).comp α' (zero_add i)) =
        (CategoryTheory.Abelian.Ext.mk₀ q).comp (a • α') (zero_add i)
    exact
      (CategoryTheory.Abelian.Ext.comp_smul
        (CategoryTheory.Abelian.Ext.mk₀ q) α' (zero_add i) a).symm

/-- The scalar endomorphism induced on derived local cohomology. -/
def derivedLocalCohomologyScalarMap
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) (a : R) :
    derivedLocalCohomology I M i ⟶ derivedLocalCohomology I M i :=
  colim.map (derivedLocalCohomologyPowersScalarMap I M i a)

/-- The scalar endomorphism acts on a colimit representative by its usual
scalar action in derived Ext. -/
theorem derivedLocalCohomologyScalarMap_ι_apply
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) (a : R) (n : ℕ)
    (α : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) M i) :
    derivedLocalCohomologyScalarMap I M i a
        (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
          (op (op n)) α) =
      colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
        (op (op n)) (a • α) := by
  have h :=
    congrArg
      (fun f :
          (derivedLocalCohomologyPowersDiagram I M i).obj (op (op n)) ⟶
            derivedLocalCohomology I M i ↦ f α)
      (colimit.ι_map
        (derivedLocalCohomologyPowersScalarMap I M i a) (op (op n)))
  exact h

/-- Each local-cohomology class is annihilated by a power of the support
ideal.  The exponent can depend on the class. -/
theorem derivedLocalCohomology_exists_idealPower_scalarMap_eq_zero
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (z : derivedLocalCohomology I M i) :
    ∃ n : ℕ, ∀ a : R, a ∈ I ^ n →
      derivedLocalCohomologyScalarMap I M i a z = 0 := by
  let : PreservesFilteredColimitsOfSize.{0, 0}
      (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨k, α, hα⟩ :=
    Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I M i) z
  rcases k with ⟨⟨n⟩⟩
  refine ⟨n, ?_⟩
  intro a ha
  rw [← hα]
  let ι : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) M i →+ derivedLocalCohomology I M i :=
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M i) (op (op n))).hom
  change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M i at α
  exact (derivedLocalCohomologyScalarMap_ι_apply I M i a n α).trans
    ((congrArg ι
      (derivedExt_quotient_smul_eq_zero (I ^ n) M i a ha α)).trans
        (map_zero ι))

/-- In particular, a member of the support ideal acts locally nilpotently. -/
theorem derivedLocalCohomology_exists_pow_scalarMap_eq_zero
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (a : R) (ha : a ∈ I) (z : derivedLocalCohomology I M i) :
    ∃ n : ℕ, derivedLocalCohomologyScalarMap I M i (a ^ n) z = 0 := by
  obtain ⟨n, hn⟩ :=
    derivedLocalCohomology_exists_idealPower_scalarMap_eq_zero I M i z
  exact ⟨n, hn (a ^ n) (Ideal.pow_mem_pow ha n)⟩

/-- The unit scalar induces the identity endomorphism. -/
theorem derivedLocalCohomologyScalarMap_one
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    derivedLocalCohomologyScalarMap I M i 1 =
      𝟙 (derivedLocalCohomology I M i) := by
  apply colimit.hom_ext (F := derivedLocalCohomologyPowersDiagram I M i)
  rintro ⟨⟨n⟩⟩
  ext α
  let ι : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) M i →+ derivedLocalCohomology I M i :=
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M i) (op (op n))).hom
  change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M i at α
  change
    derivedLocalCohomologyScalarMap I M i 1
        (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
          (op (op n)) α) =
      colimit.ι (derivedLocalCohomologyPowersDiagram I M i) (op (op n)) α
  exact (derivedLocalCohomologyScalarMap_ι_apply I M i 1 n α).trans
    (congrArg ι
      (one_smul R α))

/-- Scalar multiplication on the colimit respects multiplication in `R`. -/
theorem derivedLocalCohomologyScalarMap_mul
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) (a b : R) :
    derivedLocalCohomologyScalarMap I M i (a * b) =
      derivedLocalCohomologyScalarMap I M i b ≫
        derivedLocalCohomologyScalarMap I M i a := by
  apply colimit.hom_ext (F := derivedLocalCohomologyPowersDiagram I M i)
  rintro ⟨⟨n⟩⟩
  ext α
  let ι : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) M i →+ derivedLocalCohomology I M i :=
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M i) (op (op n))).hom
  change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M i at α
  change
    derivedLocalCohomologyScalarMap I M i (a * b)
        (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
          (op (op n)) α) =
      derivedLocalCohomologyScalarMap I M i a
        (derivedLocalCohomologyScalarMap I M i b
          (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
            (op (op n)) α))
  exact (derivedLocalCohomologyScalarMap_ι_apply I M i (a * b) n α).trans
    ((congrArg ι
      (smul_smul a b α).symm).trans
        ((derivedLocalCohomologyScalarMap_ι_apply I M i a n (b • α)).symm.trans
          (congrArg (derivedLocalCohomologyScalarMap I M i a)
            (derivedLocalCohomologyScalarMap_ι_apply I M i b n α).symm)))

/-- An injective scalar from the support ideal forces local cohomology to
vanish: its powers are injective, whereas every class is killed by a power. -/
theorem derivedLocalCohomology_isZero_of_scalarMap_injective
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (a : R) (ha : a ∈ I)
    (hinj : Function.Injective
      (ConcreteCategory.hom (derivedLocalCohomologyScalarMap I M i a))) :
    IsZero (derivedLocalCohomology I M i) := by
  have hpow : ∀ n : ℕ, ∀ z : derivedLocalCohomology I M i,
      derivedLocalCohomologyScalarMap I M i (a ^ n) z = 0 → z = 0 := by
    intro n
    induction n with
    | zero =>
        intro z hz
        rw [pow_zero, derivedLocalCohomologyScalarMap_one] at hz
        exact hz
    | succ n ih =>
        intro z hz
        rw [pow_succ, derivedLocalCohomologyScalarMap_mul] at hz
        change
          derivedLocalCohomologyScalarMap I M i (a ^ n)
            (derivedLocalCohomologyScalarMap I M i a z) = 0 at hz
        apply hinj
        exact (ih (derivedLocalCohomologyScalarMap I M i a z) hz).trans
          (map_zero (ConcreteCategory.hom
            (derivedLocalCohomologyScalarMap I M i a))).symm
  have hz : ∀ z : derivedLocalCohomology I M i, z = 0 := by
    intro z
    obtain ⟨n, hn⟩ :=
      derivedLocalCohomology_exists_pow_scalarMap_eq_zero I M i a ha z
    exact hpow n z hn
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    ⟨fun z w ↦ (hz z).trans (hz w).symm⟩

end EtaleFundamentalGroups

end
