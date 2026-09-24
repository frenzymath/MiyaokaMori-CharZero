import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.QcPullbackAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AffineAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization

/-! # The relative Spec of a quasi-coherent algebra

The relative Spec: a quasi-coherent `O_X`-algebra `A` gives an affine scheme `Spec_X A` over `X`.
`Scheme.relativeSpec A` is defined as `A.toAffineAlgebra.relativeSpec` (Mathlib's `RelativeGluingData`
on the affine Zariski site). `ringPresheaf` is the presheaf of section rings and is used by
`relativeSpec.structureRingMap`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

/-- The presheaf of commutative rings `U ↦ A.sectionsRing U` of a quasi-coherent algebra `A` (a commutative
monoid object of `X.Modules`), with the restriction ring homomorphisms; the underlying presheaf of abelian
groups is the presheaf of sections of `A.carrier`. -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.ringPresheaf {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) : TopCat.Presheaf CommRingCat.{u} X.carrier where
  obj U := CommRingCat.of (A.sectionsRing U.unop)
  map f := CommRingCat.ofHom (A.sectionsRestrict (CategoryTheory.leOfHom f.unop))
  map_id U := by
    ext a
    exact congrArg (fun φ => φ.hom a) (A.carrier.val.map_id U)
  map_comp f g := by
    ext a
    exact congrArg (fun φ => φ.hom a) (A.carrier.val.map_comp f g)

/-- The structure map `O_X → A` on the affine site; on each affine open it is `sectionsUnit`
(`r ↦ r · 1_A`). -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.affineUnit {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) :
    (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶
      (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ A.ringPresheaf where
  app U := CommRingCat.ofHom (A.sectionsUnit U.unop.toOpens)
  naturality U V f := by
    ext r
    exact _root_.PresheafOfModules.naturality_apply A.one.val
      ((AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).op.map f) r

/-- The affine-local characterization of quasi-coherence: for an affine open `U` and `f ∈ Γ(U)`,
`A(D(f)) = A(U)_{α(f)}` (Stacks 01I8/01IA). Route: `A.carrier` quasi-coherent ⇒ `A.carrier|_U ≅ M^~`
(`M = A(U)`), `M^~(D(f)) = M_f`; the ring and module structures on `A(U)` are compatible (the scalar
multiplication of the algebra structure given by `sectionsUnit` is the `O(U)`-module structure). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.unit_coequifibered {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) : A.affineUnit.Coequifibered := by
  rw [AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  haveI := A.quasicoherent
  intro U f
  have hUaff : AlgebraicGeometry.IsAffineOpen U.toOpens := U.2
  have hV : X.basicOpen f ≤ U.toOpens := X.basicOpen_le f
  letI : Algebra (A.sectionsRing U.toOpens) (A.sectionsRing (X.basicOpen f)) :=
    (A.sectionsRestrict hV).toAlgebra
  show IsLocalization.Away (A.sectionsUnit U.toOpens f) (A.sectionsRing (X.basicOpen f))
  have halg : ∀ a : A.sectionsRing U.toOpens,
      algebraMap (A.sectionsRing U.toOpens) (A.sectionsRing (X.basicOpen f)) a =
        A.sectionsRestrict hV a := fun _ => rfl
  have hres : ∀ r : Γ(X, U.toOpens),
      A.sectionsRestrict hV (A.sectionsUnit U.toOpens r) =
        A.sectionsUnit (X.basicOpen f) ((X.presheaf.map (CategoryTheory.homOfLE hV).op).hom r) := by
    intro r
    have hn := _root_.PresheafOfModules.naturality_apply A.one.val (CategoryTheory.homOfLE hV).op r
    have h1 : ((CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules).val.map
          (CategoryTheory.homOfLE hV).op).hom r =
        (X.presheaf.map (CategoryTheory.homOfLE hV).op).hom r := rfl
    rw [h1] at hn
    exact hn.symm
  refine (_root_.isLocalization_iff (Submonoid.powers _) _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨-, n, rfl⟩
    rw [halg, map_pow, hres]
    exact IsUnit.pow n (RingHom.isUnit_map (A.sectionsUnit (X.basicOpen f))
      (X.toRingedSpace.isUnit_res_basicOpen f))
  · intro z
    obtain ⟨n, t, ht⟩ := AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map_basicOpen
      A.carrier hUaff f z
    have key : z * A.sectionsRestrict hV ((A.sectionsUnit U.toOpens f) ^ n) =
        A.sectionsRestrict hV t := by
      rw [map_pow, hres, _root_.mul_comm, ← map_pow, A.smul_eq_sectionsUnit_mul]
      exact ht.symm
    exact ⟨⟨t, ⟨_, n, rfl⟩⟩, key⟩
  · intro x y hxy
    rw [halg, halg] at hxy
    have h0 : A.sectionsRestrict hV (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨n, hn⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero
        A.carrier hUaff f (x - y) h0
    have key : (A.sectionsUnit U.toOpens f) ^ n * x = (A.sectionsUnit U.toOpens f) ^ n * y := by
      rw [← _root_.sub_eq_zero, ← mul_sub, ← map_pow, A.smul_eq_sectionsUnit_mul]
      exact hn
    exact ⟨⟨_, n, rfl⟩, key⟩

/-- The affine algebra of a quasi-coherent algebra (presheaf of rings on the affine site + structure map +
compatibility with localization). -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.toAffineAlgebra
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) : X.AffineAlgebra where
  ring := (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ A.ringPresheaf
  unit := A.affineUnit
  coequifibered := A.unit_coequifibered

/-- `Spec_X A`: `AffineAlgebra.relativeSpec` (Mathlib's `RelativeGluingData` gluing the `Spec A(U)` over the
affine site). -/
noncomputable def AlgebraicGeometry.Scheme.relativeSpec {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) : CategoryTheory.Over X :=
  A.toAffineAlgebra.relativeSpec

end
