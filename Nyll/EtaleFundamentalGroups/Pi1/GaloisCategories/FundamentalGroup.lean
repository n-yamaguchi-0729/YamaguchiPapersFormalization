/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright or Authors header. Its copyright holder
requires review. The Authors line above is retained from the previous NYLL
integration and is not a verbatim attribution from the cited upstream file.
-/
/-
Adapted pi1 source, including toolchain and proof repairs.
Reference revision (historical copy revision unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/CategoryTheory/Galois/IsFundamentalGroup.lean
-/

module

public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup

/-!
# Fundamental-group kernels in Galois categories

The kernel of the natural action on a fiber functor is the intersection of its
point stabilizers.
-/

@[expose] public section

open CategoryTheory

@[simp]
lemma CategoryTheory.Aut.one_hom {C : Type*} [Category C] (X : C) :
    (1 : Aut X).asIso.hom = (1 : End X).asHom := rfl

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category C] (F : C ⥤ FintypeCat)

variable (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)] [IsNaturalSMul F G]

lemma ker_toAut : (toAut F G).ker = ⨅ (X : C) (x : F.obj X), MulAction.stabilizer G x := by
  ext g : 1
  simp only [MonoidHom.mem_ker, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  constructor
  · intro h X x
    exact congrArg (fun a : Aut F => a.asIso.hom.app X x) h
  · intro h
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply FintypeCat.hom_ext
    intro x
    exact h X x

variable [GaloisCategory C] [FiberFunctor F]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ X, ContinuousSMul G (F.obj X)]

end CategoryTheory.PreGaloisCategory
