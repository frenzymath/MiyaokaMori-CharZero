import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDual
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerFiniteFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrames
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.Pi

/-!
# Module sheaves with a global finite frame, and their local functionals

A finite frame `e : I → Γ(G, ⊤)` of `G` on `⊤` (`MiyaokaMori.DualPullback.IsFrameOn G e`, the one
finite-family frame notion of the library: on every open `V` the sections of `G` are uniquely
`∑ᵢ rᵢ • eᵢ|_V`) gives a basis `he.basisOn V` of `Γ(G, V)` over `Γ(X, V)` for every open `V`,
compatible with restriction (restriction sends the `i`-th basis vector over `U` to the `i`-th basis
vector over `V`, `IsFrameOn.basisOn_restrict`). For such `G`, a compatible family of local
functionals on `G` over `U` (`LocalDualSections X G U`) is determined by, and can be prescribed as,
its top-level functional on `Γ(G, U)`:
`FrameDual.evalTopEquiv he U : LocalDualSections X G U ≃ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(G, U)`.
Proof: write a section over `V ≤ U` in the basis over `V`, whose vectors are the restrictions of
the basis over `U`; compatibility of the family then expresses every value through the top-level
values on the basis (`evalTop_injective`); conversely `t ↦ ∑ᵢ coordᵢ(t) · (f (bᵢ))|_V` is a
compatible family with top-level functional `f` (`evalTop_surjective`), using that coordinates
commute with restriction (`coord_restrict`).

The free sheaf `SheafOfModules.free (ULift (Fin r))` has such a frame (`freeIsFrameOn`): its
standard basis over `⊤` (`MiyaokaMori.ExteriorPowerFiniteFree.finiteFreeSectionBasis`), whose
restrictions are the standard bases over every open (`finiteFreeSectionBasis_restrict`).

A compatible family of bases of `Γ(G, V)` over every open `V` is the same as a frame on `⊤`: a frame
on `⊤` *is* a compatible family of bases (`IsFrameOn.basisOn`), and a compatible family of bases is a
frame (its basis over `⊤`). Everything below is therefore stated for `he : IsFrameOn G e` with
`e : I → Γ(G, ⊤)`.

Used by `ExteriorDualComparisonIsoFree`. Sources: Stacks Project `modules.tex`, Tag 01CM (internal
Hom) and free modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

set_option backward.isDefEq.respectTransparency false

namespace MiyaokaMori.DualPullback

variable {X : Scheme.{u}} {G : X.Modules} {I : Type u} [Fintype I] {e : I → Γ(G, ⊤)}

open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

/-- The basis of `Γ(G, V)` over `Γ(X, V)` given by a frame of `G` on `⊤`: `rᵢ ↦ ∑ᵢ rᵢ • eᵢ|_V`. -/
def IsFrameOn.basisOn (he : IsFrameOn G e) (V : X.Opens) : Module.Basis I Γ(X, V) Γ(G, V) :=
  Module.Basis.ofEquivFun (frameEquiv he (le_top : V ≤ ⊤)).symm

theorem IsFrameOn.basisOn_apply (he : IsFrameOn G e) (V : X.Opens) (i : I) :
    he.basisOn V i = res G le_top (e i) := by
  classical
  rw [IsFrameOn.basisOn, Module.Basis.coe_ofEquivFun]
  change frameEquiv he (le_top : V ≤ ⊤) (Function.update (0 : I → Γ(X, V)) i 1) = _
  rw [← frameMap_single e le_top i]
  rfl

/-- Restriction sends the `i`-th basis vector over `U` to the `i`-th basis vector over `V`. -/
theorem IsFrameOn.basisOn_restrict (he : IsFrameOn G e) {U V : X.Opens} (j : V ⟶ U) (i : I) :
    G.presheaf.map j.op (he.basisOn U i) = he.basisOn V i := by
  rw [he.basisOn_apply, he.basisOn_apply]
  exact res_res G (leOfHom j) le_top (e i)

/-- Coordinates commute with restriction. -/
theorem IsFrameOn.coord_restrict (he : IsFrameOn G e) {U V : X.Opens} (j : V ⟶ U) (i : I)
    (t : Γ(G, U)) :
    (he.basisOn V).coord i (G.presheaf.map j.op t) =
      X.presheaf.map j.op ((he.basisOn U).coord i t) := by
  conv_lhs => rw [← (he.basisOn U).sum_repr t]
  rw [map_sum]
  simp only [Scheme.Modules.map_smul, he.basisOn_restrict]
  rw [Module.Basis.coord_apply, Module.Basis.repr_sum_self]
  rfl

end MiyaokaMori.DualPullback

namespace AlgebraicGeometry.Scheme.Modules

open MiyaokaMori.DualPullback

variable {X : Scheme.{u}}

namespace FrameDual

variable {G : X.Modules} {I : Type u} [Fintype I] {e : I → Γ(G, ⊤)} (he : IsFrameOn G e)

/-- The top-level functional of a compatible family. -/
def evalTop (U : X.Opens) :
    LocalDualSections X G U →ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(G, U) where
  toFun φ := φ.1 (Over.mk (𝟙 U))
  map_add' φ ψ := rfl
  map_smul' r φ := by
    apply LinearMap.ext
    intro t
    have h : X.presheaf.map (Over.mk (𝟙 U)).hom.op r = r := by
      change X.presheaf.map (𝟙 U).op r = r
      rw [op_id, X.presheaf.map_id]
      rfl
    exact congrArg (fun z ↦ z • φ.1 (Over.mk (𝟙 U)) t) h

theorem evalTop_apply (U : X.Opens) (φ : LocalDualSections X G U) (t : Γ(G, U)) :
    evalTop U φ t = φ.1 (Over.mk (𝟙 U)) t := rfl

include he in
/-- A compatible family is determined by its top-level functional. -/
theorem evalTop_injective (U : X.Opens) : Function.Injective (evalTop (G := G) U) := by
  intro φ ψ h
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro t
  have hcomp : ∀ (χ : LocalDualSections X G U) (x : Γ(G, U)),
      χ.1 V (G.presheaf.map V.hom.op x) = X.presheaf.map V.hom.op (χ.1 (Over.mk (𝟙 U)) x) :=
    fun χ x ↦ χ.2 V (Over.mk (𝟙 U)) (Over.homMk V.hom) x
  conv_lhs => rw [← (he.basisOn V.left).sum_repr t]
  conv_rhs => rw [← (he.basisOn V.left).sum_repr t]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.map_smul, LinearMap.map_smul, ← he.basisOn_restrict V.hom i, hcomp φ, hcomp ψ]
  exact congrArg _ (congrArg _ (LinearMap.congr_fun h (he.basisOn U i)))

/-- The compatible family with prescribed top-level functional `f`. -/
def ofTop (U : X.Opens) (f : Module.Dual Γ(X, U) Γ(G, U)) : LocalDualSections X G U :=
  ⟨fun V ↦ ∑ i, X.presheaf.map V.hom.op (f (he.basisOn U i)) • (he.basisOn V.left).coord i, by
    intro V W j x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change X.presheaf.map V.hom.op (f (he.basisOn U i)) *
        (he.basisOn V.left).coord i (G.presheaf.map j.left.op x) =
      X.presheaf.map j.left.op (X.presheaf.map W.hom.op (f (he.basisOn U i)) *
        (he.basisOn W.left).coord i x)
    rw [map_mul, he.coord_restrict, ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp,
      ← op_comp, Over.w j]⟩

theorem ofTop_val (U : X.Opens) (f : Module.Dual Γ(X, U) Γ(G, U)) (V : Over U) (t : Γ(G, V.left)) :
    (ofTop he U f).1 V t =
      ∑ i, X.presheaf.map V.hom.op (f (he.basisOn U i)) * (he.basisOn V.left).coord i t := by
  simp only [ofTop, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem evalTop_ofTop (U : X.Opens) (f : Module.Dual Γ(X, U) Γ(G, U)) :
    evalTop U (ofTop he U f) = f := by
  apply LinearMap.ext
  intro t
  rw [evalTop_apply, ofTop_val]
  conv_rhs => rw [← (he.basisOn U).sum_repr t]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change X.presheaf.map (𝟙 U).op (f (he.basisOn U i)) * (he.basisOn U).coord i t =
    f (_ • he.basisOn U i)
  rw [op_id, X.presheaf.map_id, _root_.map_smul, Module.Basis.coord_apply]
  change f (he.basisOn U i) * (he.basisOn U).repr t i = (he.basisOn U).repr t i * f (he.basisOn U i)
  rw [mul_comm]

include he in
theorem evalTop_surjective (U : X.Opens) : Function.Surjective (evalTop (G := G) U) :=
  fun f ↦ ⟨ofTop he U f, evalTop_ofTop he U f⟩

/-- Compatible families of local functionals on `G` over `U` are the functionals on `Γ(G, U)`. -/
def evalTopEquiv (U : X.Opens) :
    LocalDualSections X G U ≃ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(G, U) :=
  LinearEquiv.ofBijective (evalTop U) ⟨evalTop_injective he U, evalTop_surjective he U⟩

theorem evalTopEquiv_apply (U : X.Opens) (φ : LocalDualSections X G U) (t : Γ(G, U)) :
    evalTopEquiv he U φ t = φ.1 (Over.mk (𝟙 U)) t := rfl

end FrameDual

/-! ### The free sheaf of finite rank

The product decomposition of the free sheaf, its section isomorphism and the standard basis of its
sections are those of `MiyaokaMori.ExteriorPowerFiniteFree` (`finiteFreeProductIso`,
`finiteFreeSectionsIso`, `finiteFreeSectionBasis`). Only the compatibility of the standard basis with
restriction is proved here. -/

namespace FreeSectionBasis

variable (X : Scheme.{u}) (r : ℕ)

open MiyaokaMori.ExteriorPowerFiniteFree

/- Same local instance as in `MiyaokaMori.ExteriorPowerFiniteFree` (the ring of the basis
`finiteFreeSectionBasis` is spelled `X.ringCatSheaf.obj.obj (op U)` there). -/
local instance freeSectionBasisSectionCommRing (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- The standard basis vectors of the free sheaf of rank `r` have Kronecker coordinates. -/
theorem finiteFreeSectionsIso_finiteFreeSectionBasis (U : X.Opens) (i k : Fin r) :
    (finiteFreeSectionsIso X (ULift.{u} (Fin r)) U).hom.hom (finiteFreeSectionBasis X r U i)
        (ULift.up k) = if i = k then 1 else 0 := by
  rw [← finiteFreeSectionBasis_coord, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

/-- Restriction sends the standard basis vectors of the sections of the free sheaf of rank `r`
over `U` to those over `V`. -/
theorem finiteFreeSectionBasis_restrict {U V : X.Opens} (j : V ⟶ U) (i : Fin r) :
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.presheaf.map j.op
        (finiteFreeSectionBasis X r U i) = finiteFreeSectionBasis X r V i := by
  refine (finiteFreeSectionBasis X r V).ext_elem fun k ↦ ?_
  have e1 : (finiteFreeSectionBasis X r V).repr
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.presheaf.map j.op
        (finiteFreeSectionBasis X r U i)) k =
      X.presheaf.map j.op ((finiteFreeSectionsIso X (ULift.{u} (Fin r)) U).hom.hom
        (finiteFreeSectionBasis X r U i) (ULift.up k)) :=
    (finiteFreeSectionBasis_coord X r V _ k).trans
      (finiteFreeSectionsIso_restrict X (ULift.{u} (Fin r)) j _ (ULift.up k))
  have e2 : (finiteFreeSectionBasis X r V).repr (finiteFreeSectionBasis X r V i) k =
      if i = k then 1 else 0 := by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
  rw [e1, e2, finiteFreeSectionsIso_finiteFreeSectionBasis]
  split_ifs <;> simp

end FreeSectionBasis

/-- The standard basis of the global sections of the free sheaf of rank `r`, indexed by
`ULift (Fin r)` (the index type of the free sheaf). -/
def freeStandardFrame (X : Scheme.{u}) (r : ℕ) :
    ULift.{u} (Fin r) → Γ(SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)), ⊤) :=
  fun i ↦ MiyaokaMori.ExteriorPowerFiniteFree.finiteFreeSectionBasis X r ⊤ i.down

/-- The free sheaf of rank `r` has a finite frame on `⊤`: its standard basis. -/
theorem freeIsFrameOn (X : Scheme.{u}) (r : ℕ) :
    IsFrameOn (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) (freeStandardFrame X r) := by
  intro W hW
  let B := (MiyaokaMori.ExteriorPowerFiniteFree.finiteFreeSectionBasis X r W).reindex
    (Equiv.ulift.{u, 0} (α := Fin r)).symm
  have h : ⇑(frameMap (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
      (freeStandardFrame X r) hW) = ⇑B.equivFun.symm := by
    funext c
    rw [frameMap_apply, Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    change (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.presheaf.map
        (CategoryTheory.homOfLE hW).op (MiyaokaMori.ExteriorPowerFiniteFree.finiteFreeSectionBasis X r ⊤ i.down) = _
    rw [FreeSectionBasis.finiteFreeSectionBasis_restrict X r (CategoryTheory.homOfLE hW) i.down,
      Module.Basis.reindex_apply]
    rfl
  rw [h]
  exact B.equivFun.symm.bijective

end AlgebraicGeometry.Scheme.Modules
