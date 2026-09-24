import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafAsCokernel
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Local properties of the quotient sheaf

Two local properties of the quotient sheaf `F/G` (needed for the line bundle `O_X(D)` of a Cartier
divisor):

* `TopCat.Sheaf.quotientπ_exists_local`: the quotient map `π : F ⟶ F/G` is locally surjective —
  every section `s ∈ (F/G)(W)` has, near every point `x ∈ W`, a neighbourhood `U` and `g ∈ F(U)` with
  `π(g) = s|_U`. (Through `CommGrpCat ≌ AddCommGrpCat`, `π` is `cokernel.π` in the abelian category
  `Sheaf(X, AddCommGrpCat)`, hence an epimorphism, and epimorphisms of sheaves are locally
  surjective.)
* `TopCat.Sheaf.exists_local_preimage_of_quotientπ_eq_one`: the kernel of `π` lies locally in the
  image of `i` — if `a ∈ F(U)` satisfies `π(a) = 1`, then near every point there are `V` and
  `b ∈ G(V)` with `i(b) = a|_V`. (Factor `i` as `G ↠ im i ↪ F`: the monomorphism `im i ↪ F` is the
  kernel of `cokernel.π i`, kernels are computed sectionwise (the sections functor preserves
  limits), so `a` comes globally from `(im i)(U)`; then `G ↠ im i` is an epimorphism, i.e. locally
  surjective.)
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

/-- The functor "sections over the open set `U`", `Sheaf(T, AddCommGrpCat) ⥤ AddCommGrpCat`. -/

abbrev sectionsFunctor (T : TopCat.{u}) (U : (Opens T)ᵒᵖ) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⋙
    (evaluation ((Opens T)ᵒᵖ) AddCommGrpCat.{u}).obj U

instance sectionsFunctor_preservesZeroMorphisms (T : TopCat.{u}) (U : (Opens T)ᵒᵖ) :
    (sectionsFunctor T U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

section AddCommGrp

variable {T : TopCat.{u}}
  {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}

/-- Kernels are computed sectionwise: if `a ∈ F(U)` is sent to `0` by `cokernel.π φ`, then `a` comes
from `ker (cokernel.π φ) (U)`. -/

theorem exists_sections_kernel_of_cokernelπ_eq_zero (φ : G ⟶ F) (U : (Opens T)ᵒᵖ)
    (a : F.val.obj U) (ha : (cokernel.π φ).hom.app U a = 0) :
    ∃ b : (kernel (cokernel.π φ)).val.obj U,
      (kernel.ι (cokernel.π φ)).hom.app U b = a := by
  have hlim := isLimitOfHasKernelOfPreservesLimit (sectionsFunctor T U) (cokernel.π φ)
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk ((sectionsFunctor T U).map (kernel.ι (cokernel.π φ)))
      ((sectionsFunctor T U).map (cokernel.π φ))
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hlim
  exact (ShortComplex.ab_exact_iff S).mp hS a ha

/-- `cokernel.π φ` is locally surjective (epimorphisms of sheaves are locally surjective). -/

theorem cokernelπ_exists_local (φ : G ⟶ F) (W : Opens T)
    (s : (cokernel φ).val.obj (op W)) (x : T) (hx : x ∈ W) :
    ∃ (U : Opens T) (_ : x ∈ U) (hUW : U ≤ W) (g : F.val.obj (op U)),
      (cokernel φ).val.map (homOfLE hUW).op s = (cokernel.π φ).hom.app (op U) g := by
  have hls : TopCat.Presheaf.IsLocallySurjective (cokernel.π φ).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (cokernel.π φ)).mpr coequalizer.π_epi
  obtain ⟨U, hUW, ⟨g, hg⟩, hxU⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (cokernel.π φ).hom).mp hls W s x hx
  exact ⟨U, hxU, hUW, g, hg.symm⟩

/-- The kernel of `cokernel.π φ` lies locally in the image of `φ`. -/

theorem exists_local_preimage_of_cokernelπ_eq_zero (φ : G ⟶ F) (W : Opens T)
    (a : F.val.obj (op W)) (ha : (cokernel.π φ).hom.app (op W) a = 0) (x : T) (hx : x ∈ W) :
    ∃ (V : Opens T) (_ : x ∈ V) (hVW : V ≤ W) (b : G.val.obj (op V)),
      φ.hom.app (op V) b = F.val.map (homOfLE hVW).op a := by
  obtain ⟨c, hc⟩ := exists_sections_kernel_of_cokernelπ_eq_zero φ (op W) a ha
  have hep : Epi (Abelian.factorThruImage φ) := inferInstance
  have hls : TopCat.Presheaf.IsLocallySurjective (Abelian.factorThruImage φ).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (Abelian.factorThruImage φ)).mpr hep
  obtain ⟨V, hVW, ⟨b, hb⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (Abelian.factorThruImage φ).hom).mp hls W c x hx
  refine ⟨V, hxV, hVW, b, ?_⟩
  have hnat := ConcreteCategory.congr_hom
    ((Abelian.image.ι φ).hom.naturality (homOfLE hVW).op) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hc] at hnat
  have hfac : φ.hom.app (op V) b =
      (Abelian.image.ι φ).hom.app (op V) ((Abelian.factorThruImage φ).hom.app (op V) b) := by
    conv_lhs => rw [← Abelian.image.fac φ]
    rfl
  rw [hfac, hb]
  exact hnat

end AddCommGrp

section CommGrp

variable {T : TopCat.{u}} {F G : TopCat.Sheaf CommGrpCat.{u} T}

/-- The quotient map `π : F ⟶ F/G` is locally surjective: every `s ∈ (F/G)(W)` is locally represented
by a section of `F`. -/

theorem quotientπ_exists_local (i : G ⟶ F) (W : Opens T)
    (s : (TopCat.Sheaf.quotient i).val.obj (op W)) (x : T) (hx : x ∈ W) :
    ∃ (U : Opens T) (_ : x ∈ U) (hUW : U ≤ W) (g : F.val.obj (op U)),
      (TopCat.Sheaf.quotient i).val.map (homOfLE hUW).op s =
        (TopCat.Sheaf.quotientπ i).hom.app (op U) g :=
  cokernelπ_exists_local
    ((sheafCompose (Opens.grothendieckTopology T)
      commGroupAddCommGroupEquivalence.functor).map i) W s x hx

/-- The kernel of the quotient map lies locally in the image of `i`. -/

theorem exists_local_preimage_of_quotientπ_eq_one (i : G ⟶ F) (W : Opens T)
    (a : F.val.obj (op W))
    (ha : (TopCat.Sheaf.quotientπ i).hom.app (op W) a = 1) (x : T) (hx : x ∈ W) :
    ∃ (V : Opens T) (_ : x ∈ V) (hVW : V ≤ W) (b : G.val.obj (op V)),
      i.hom.app (op V) b = F.val.map (homOfLE hVW).op a :=
  exists_local_preimage_of_cokernelπ_eq_zero
    ((sheafCompose (Opens.grothendieckTopology T)
      commGroupAddCommGroupEquivalence.functor).map i) W a ha x hx

end CommGrp

end TopCat.Sheaf

end
