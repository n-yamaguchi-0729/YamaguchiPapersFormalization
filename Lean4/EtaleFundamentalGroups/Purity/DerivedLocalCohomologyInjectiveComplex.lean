/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import EtaleFundamentalGroups.Purity.IdealPowerTorsionFunctor
import EtaleFundamentalGroups.Purity.InjectiveResolutionExtLinear
import EtaleFundamentalGroups.Purity.ResidueFieldHullSocle
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The Ext-colimit and the torsion complex of an injective resolution

A cocycle from `R / I^k` evaluates at one to an ideal-power torsion
cocycle. This respects coboundaries and the transition maps in the
Ext-colimit. Conversely every torsion cocycle admits such a representative,
and a torsion boundary becomes an Ext boundary at a sufficiently large
power of the ideal.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]
variable {M : ModuleCat.{u} R}

private abbrev torsionShortComplex
    (I : Ideal R) (J : InjectiveResolution M) (n : ℕ) :=
  (derivedLocalCohomologyInjectiveComplex I J).sc' n (n + 1) (n + 2)

private abbrev torsionCocycleQuotient
    (I : Ideal R) (J : InjectiveResolution M) (n : ℕ) :=
  (LinearMap.ker (torsionShortComplex I J n).g.hom) ⧸
    LinearMap.range (torsionShortComplex I J n).moduleCatToCycles

private def quotientHomToPowerTorsion
    (I : Ideal R) (V : ModuleCat.{u} R) (k : ℕ) :
    (ModuleCat.of R (R ⧸ I ^ k) ⟶ V) →ₗ[R] Ideal.primaryComponent V I where
  toFun f := ⟨f (Ideal.Quotient.mk (I ^ k) 1),
    (Ideal.primaryComponent_mem (M := V) (I := I) _).mpr
      ⟨k, (quotientHomEquivTorsionBySet (I ^ k) f.hom).property⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private def quotientCyclesToPowerTorsionCycles
    (I : Ideal R) (J : InjectiveResolution M) (n k : ℕ) :
    LinearMap.ker (injectiveResolutionLinearCoyonedaShortComplexSucc J
      (ModuleCat.of R (R ⧸ I ^ k)) n).g.hom →ₗ[R]
        LinearMap.ker (torsionShortComplex I J n).g.hom where
  toFun f := ⟨quotientHomToPowerTorsion I (J.cocomplex.X (n + 1)) k f.1, by
    apply Subtype.ext
    exact ConcreteCategory.congr_hom f.2 (Ideal.Quotient.mk (I ^ k) 1)⟩
  map_add' f g := Subtype.ext (Subtype.ext rfl)
  map_smul' a f := Subtype.ext (Subtype.ext rfl)

private def quotientCocyclesToTorsionCocycleQuotient
    (I : Ideal R) (J : InjectiveResolution M) (n k : ℕ) :
    ((LinearMap.ker (injectiveResolutionLinearCoyonedaShortComplexSucc J
      (ModuleCat.of R (R ⧸ I ^ k)) n).g.hom) ⧸
        LinearMap.range (injectiveResolutionLinearCoyonedaShortComplexSucc J
          (ModuleCat.of R (R ⧸ I ^ k)) n).moduleCatToCycles) →ₗ[R]
      torsionCocycleQuotient I J n :=
  Submodule.mapQ _ _ (quotientCyclesToPowerTorsionCycles I J n k) (by
    rintro f ⟨g, rfl⟩
    exact ⟨quotientHomToPowerTorsion I (J.cocomplex.X n) k g,
      Subtype.ext (Subtype.ext rfl)⟩)

private def extToTorsionCocycleQuotient
    (I : Ideal R) (J : InjectiveResolution M) (n k : ℕ) :
    Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ k)) M (n + 1) →ₗ[R]
      torsionCocycleQuotient I J n :=
  (quotientCocyclesToTorsionCocycleQuotient I J n k).comp
    (injectiveResolutionCocycleQuotientEquivExtSucc J
      (ModuleCat.of R (R ⧸ I ^ k)) n).symm.toLinearMap

private theorem extToTorsionCocycleQuotient_extMk
    (I : Ideal R) (J : InjectiveResolution M) (n k : ℕ)
    (f : ModuleCat.of R (R ⧸ I ^ k) ⟶ J.cocomplex.X (n + 1))
    (hf : f ≫ J.cocomplex.d (n + 1) (n + 2) = 0) :
    extToTorsionCocycleQuotient I J n k (J.extMk f (n + 2) (by omega) hf) =
      Submodule.Quotient.mk (quotientCyclesToPowerTorsionCycles I J n k ⟨f, hf⟩) := by
  change quotientCocyclesToTorsionCocycleQuotient I J n k
    ((injectiveResolutionCocycleQuotientEquivExtSucc J
      (ModuleCat.of R (R ⧸ I ^ k)) n).symm
        (J.extMk f (n + 2) (by omega) hf)) = _
  rw [injectiveResolutionCocycleQuotientEquivExtSucc_symm_extMk]
  rfl

private def torsionCocycleQuotientCocone
    (I : Ideal R) (J : InjectiveResolution M) (n : ℕ) :
    Cocone (derivedLocalCohomologyPowersDiagram I M (n + 1)) where
  pt := AddCommGrpCat.of (torsionCocycleQuotient I J n)
  ι :=
    { app := fun k => AddCommGrpCat.ofHom
        (extToTorsionCocycleQuotient I J n (unop (unop k))).toAddMonoidHom
      naturality := by
        intro j k g
        ext α
        let q : ModuleCat.of R (R ⧸ I ^ unop (unop k)) ⟶
            ModuleCat.of R (R ⧸ I ^ unop (unop j)) :=
          (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).map g.unop
        change extToTorsionCocycleQuotient I J n (unop (unop k))
            ((Abelian.Ext.mk₀ q).comp α (zero_add (n + 1))) =
          extToTorsionCocycleQuotient I J n (unop (unop j)) α
        obtain ⟨f, hf, rfl⟩ := J.extMk_surjective α (n + 2) (by omega)
        change (ModuleCat.of R (R ⧸ I ^ unop (unop j)) ⟶
          J.cocomplex.X (n + 1)) at f
        refine (congrArg (extToTorsionCocycleQuotient I J n (unop (unop k)))
          (J.mk₀_comp_extMk f (n + 2) (by omega) hf q)).trans ?_
        refine (extToTorsionCocycleQuotient_extMk I J n (unop (unop k)) (q ≫ f)
          (by
            exact (Category.assoc q f (J.cocomplex.d (n + 1) (n + 2))).trans
              ((congrArg (fun k => q ≫ k) hf).trans (Limits.comp_zero)))).trans
            (Eq.trans ?_ (extToTorsionCocycleQuotient_extMk I J n
              (unop (unop j)) f hf).symm)
        apply congrArg Submodule.Quotient.mk
        exact Subtype.ext (Subtype.ext rfl) }

private def localCohomologyToTorsionCocycleQuotientAddHom
    (I : Ideal R) (J : InjectiveResolution M) (n : ℕ) :
    derivedLocalCohomology I M (n + 1) ⟶
      AddCommGrpCat.of (torsionCocycleQuotient I J n) :=
  colimit.desc (derivedLocalCohomologyPowersDiagram I M (n + 1))
    (torsionCocycleQuotientCocone I J n)

private theorem localCohomologyToTorsionCocycleQuotientAddHom_ι
    (I : Ideal R) (J : InjectiveResolution M) (n k : ℕ)
    (α : Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ k)) M (n + 1)) :
    localCohomologyToTorsionCocycleQuotientAddHom I J n
        (colimit.ι (derivedLocalCohomologyPowersDiagram I M (n + 1)) (op (op k)) α) =
      extToTorsionCocycleQuotient I J n k α :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (torsionCocycleQuotientCocone I J n) (op (op k))) α

private def localCohomologyToTorsionCocycleQuotient
    (I : Ideal R) (J : InjectiveResolution M) (n : ℕ) :
    derivedLocalCohomologyModule I M (n + 1) →ₗ[R]
      torsionCocycleQuotient I J n where
  toFun := localCohomologyToTorsionCocycleQuotientAddHom I J n
  map_add' := (localCohomologyToTorsionCocycleQuotientAddHom I J n).hom.map_add
  map_smul' a z := by
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    obtain ⟨k, α, hα⟩ :=
      Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I M (n + 1)) z
    rcases k with ⟨⟨k⟩⟩
    change localCohomologyToTorsionCocycleQuotientAddHom I J n
        (derivedLocalCohomologyScalarMap I M (n + 1) a z) =
      a • localCohomologyToTorsionCocycleQuotientAddHom I J n z
    rw [← hα]
    change Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ k)) M (n + 1) at α
    exact (congrArg (localCohomologyToTorsionCocycleQuotientAddHom I J n)
      (derivedLocalCohomologyScalarMap_ι_apply I M (n + 1) a k α)).trans
        ((localCohomologyToTorsionCocycleQuotientAddHom_ι I J n k (a • α)).trans
          ((map_smul (extToTorsionCocycleQuotient I J n k) a α).trans
            (congrArg (fun z : torsionCocycleQuotient I J n => a • z)
              (localCohomologyToTorsionCocycleQuotientAddHom_ι I J n k α).symm)))

private theorem localCohomologyToTorsionCocycleQuotient_surjective
    (I : Ideal R) (J : InjectiveResolution M) (n : ℕ) :
    Function.Surjective (localCohomologyToTorsionCocycleQuotient I J n) := by
  intro z
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (torsionShortComplex I J n).moduleCatToCycles) z
  let z₀ : Ideal.primaryComponent (J.cocomplex.X (n + 1)) I := z.1
  obtain ⟨k, hk⟩ := (Ideal.primaryComponent_mem (M := J.cocomplex.X (n + 1))
    (I := I) (z₀ : J.cocomplex.X (n + 1))).mp z₀.property
  let zk : Submodule.torsionBySet R (J.cocomplex.X (n + 1))
      ((I ^ k : Ideal R) : Set R) := ⟨z₀, hk⟩
  let f : ModuleCat.of R (R ⧸ I ^ k) ⟶ J.cocomplex.X (n + 1) :=
    ModuleCat.ofHom ((quotientHomEquivTorsionBySet (I ^ k)).symm zk)
  have hf : f ≫ J.cocomplex.d (n + 1) (n + 2) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    change J.cocomplex.d (n + 1) (n + 2)
      ((quotientHomEquivTorsionBySet (I ^ k)).symm zk (Ideal.Quotient.mk (I ^ k) a)) = 0
    rw [quotientHomEquivTorsionBySet_symm_apply_mk, map_smul]
    have hz : J.cocomplex.d (n + 1) (n + 2) (z₀ : J.cocomplex.X (n + 1)) = 0 :=
      congr_arg Subtype.val z.2
    rw [hz, smul_zero]
  refine ⟨derivedLocalCohomologyModuleι I M (n + 1) k
    (J.extMk f (n + 2) (by omega) hf), ?_⟩
  change localCohomologyToTorsionCocycleQuotientAddHom I J n
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M (n + 1)) (op (op k))
      (J.extMk f (n + 2) (by omega) hf)) = Submodule.Quotient.mk z
  refine (localCohomologyToTorsionCocycleQuotientAddHom_ι I J n k
    (J.extMk f (n + 2) (by omega) hf)).trans
      ((extToTorsionCocycleQuotient_extMk I J n k f hf).trans ?_)
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  apply Subtype.ext
  change (quotientHomEquivTorsionBySet (I ^ k)).symm zk
    (Ideal.Quotient.mk (I ^ k) 1) = (z₀ : J.cocomplex.X (n + 1))
  rw [quotientHomEquivTorsionBySet_symm_apply_mk, one_smul]

private theorem localCohomologyToTorsionCocycleQuotient_injective
    (I : Ideal R) (J : InjectiveResolution M) (n : ℕ) :
    Function.Injective (localCohomologyToTorsionCocycleQuotient I J n) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨k, α, hα⟩ :=
    Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I M (n + 1)) z
  rcases k with ⟨⟨k⟩⟩
  obtain ⟨f, hf, rfl⟩ := J.extMk_surjective α (n + 2) (by omega)
  rw [← hα] at hz
  change localCohomologyToTorsionCocycleQuotientAddHom I J n
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M (n + 1)) (op (op k))
      (J.extMk f (n + 2) (by omega) hf)) = 0 at hz
  change ModuleCat.of R (R ⧸ I ^ k) ⟶ J.cocomplex.X (n + 1) at f
  have hzero := (extToTorsionCocycleQuotient_extMk I J n k f hf).symm.trans
    ((localCohomologyToTorsionCocycleQuotientAddHom_ι I J n k
      (J.extMk f (n + 2) (by omega) hf)).symm.trans hz)
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
  let y₀ : Ideal.primaryComponent (J.cocomplex.X n) I := y
  obtain ⟨l, hl⟩ := (Ideal.primaryComponent_mem (M := J.cocomplex.X n)
    (I := I) (y₀ : J.cocomplex.X n)).mp y₀.property
  let p : ℕ := max k l
  let t : op (op k) ⟶ op (op p) := (homOfLE (Nat.le_max_left k l)).op.op
  let q : ModuleCat.of R (R ⧸ I ^ p) ⟶ ModuleCat.of R (R ⧸ I ^ k) :=
    (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).map t.unop
  have hyp : (y₀ : J.cocomplex.X n) ∈ Submodule.torsionBySet R (J.cocomplex.X n)
      ((I ^ p : Ideal R) : Set R) := by
    apply (Submodule.mem_torsionBySet_iff ((I ^ p : Ideal R) : Set R)
      (y₀ : J.cocomplex.X n)).mpr
    intro a
    exact (Submodule.mem_torsionBySet_iff ((I ^ l : Ideal R) : Set R)
      (y₀ : J.cocomplex.X n)).mp hl
      ⟨a, Ideal.pow_le_pow_right (Nat.le_max_right k l) a.property⟩
  let yp : Submodule.torsionBySet R (J.cocomplex.X n) ((I ^ p : Ideal R) : Set R) :=
    ⟨y₀, hyp⟩
  let g : ModuleCat.of R (R ⧸ I ^ p) ⟶ J.cocomplex.X n :=
    ModuleCat.ofHom ((quotientHomEquivTorsionBySet (I ^ p : Ideal R)).symm yp)
  have hboundary : J.cocomplex.d n (n + 1) (y₀ : J.cocomplex.X n) =
      f (Ideal.Quotient.mk (I ^ k) 1) :=
    congr_arg
      (fun c : LinearMap.ker (torsionShortComplex I J n).g.hom =>
        ((show Ideal.primaryComponent (J.cocomplex.X (n + 1)) I from c.1) :
          J.cocomplex.X (n + 1))) hy
  have hg : g ≫ J.cocomplex.d n (n + 1) = q ≫ f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    change J.cocomplex.d n (n + 1)
        ((quotientHomEquivTorsionBySet (I ^ p)).symm yp (Ideal.Quotient.mk (I ^ p) a)) =
      f (Ideal.Quotient.mk (I ^ k) a)
    rw [quotientHomEquivTorsionBySet_symm_apply_mk, map_smul, hboundary,
      ← f.hom.map_smul]
    congr 1
    change Ideal.Quotient.mk (I ^ k) (a * 1) = Ideal.Quotient.mk (I ^ k) a
    rw [mul_one]
  have htransition : (derivedLocalCohomologyPowersDiagram I M (n + 1)).map t
      (J.extMk f (n + 2) (by omega) hf) = 0 := by
    change (Abelian.Ext.mk₀ q).comp (J.extMk f (n + 2) (by omega) hf)
      (zero_add (n + 1)) = 0
    exact (J.mk₀_comp_extMk f (n + 2) (by omega) hf q).trans
      ((J.extMk_eq_zero_iff (q ≫ f) (n + 2) (by omega)
        (by
            exact (Category.assoc q f (J.cocomplex.d (n + 1) (n + 2))).trans
              ((congrArg (fun k => q ≫ k) hf).trans (Limits.comp_zero))) n rfl).mpr ⟨g, hg⟩)
  have hι := ConcreteCategory.congr_hom
    (colimit.w (derivedLocalCohomologyPowersDiagram I M (n + 1)) t)
      (J.extMk f (n + 2) (by omega) hf)
  change colimit.ι (derivedLocalCohomologyPowersDiagram I M (n + 1)) (op (op p))
      ((derivedLocalCohomologyPowersDiagram I M (n + 1)).map t
        (J.extMk f (n + 2) (by omega) hf)) =
    colimit.ι (derivedLocalCohomologyPowersDiagram I M (n + 1)) (op (op k))
      (J.extMk f (n + 2) (by omega) hf) at hι
  rw [htransition, map_zero, hα] at hι
  exact hι.symm

/-- Positive homology of the torsion complex of an injective resolution
is the original derived-Ext colimit, with its canonical module structure. -/
def derivedLocalCohomologyInjectiveComplexHomologyIsoSucc
    (I : Ideal R) (J : InjectiveResolution M) (n : ℕ) :
    (derivedLocalCohomologyInjectiveComplex I J).homology (n + 1) ≅
      derivedLocalCohomologyModule I M (n + 1) :=
  (derivedLocalCohomologyInjectiveComplex I J).homologyIsoSc'
      n (n + 1) (n + 2)
      ((ComplexShape.up ℕ).prev_eq' (ComplexShape.up_mk n (n + 1) rfl))
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (n + 1) (n + 2) (by omega))) ≪≫
    (torsionShortComplex I J n).moduleCatHomologyIso ≪≫
    (LinearEquiv.ofBijective (localCohomologyToTorsionCocycleQuotient I J n)
      ⟨localCohomologyToTorsionCocycleQuotient_injective I J n,
        localCohomologyToTorsionCocycleQuotient_surjective I J n⟩).symm.toModuleIso

end EtaleFundamentalGroups.Purity

end
