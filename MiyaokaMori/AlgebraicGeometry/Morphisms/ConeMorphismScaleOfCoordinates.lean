import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.SeedBundlePullback
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetConeCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ConeMorphismScaleOfCoordinatesCone

/-! # A cone morphism is determined by its coordinates up to a unit

Statement: let `ȷ` be a based jet over `ρ`, `V ⊂ C̃` an open subset, `W = p_κ^{-1}(V) ⊂ C̃_(κ)(L)`, and
`u` a unit on `W`. If for every `ℓ` the restriction to `W` of the `ℓ`-th cone coordinate of `ȷ` equals
`u` times the restriction to `W` of the seed section `p_κ^*ρ^*f_ℓ`, then `ȷ = u·(s∘ρ∘p_κ)` on `W`, i.e.
`W.ι ≫ ȷ.hom = TwistedCone.scale f u (W.ι ≫ p_κ ≫ ρ ≫ s)`.

Proof:
1. Both sides are morphisms `W → 𝒵` whose composites with `𝒵 → C` equal `W.ι ≫ p_κ ≫ ρ` (the left by
   `ȷ.over`, the right by `TwistedCone.scale_proj` and `(MMSetup.seed f).2 : s ≫ p_𝒵 = 𝟙`). The embedding
   `coneι : 𝒵 ↪ Tot(A^{⊕(N+1)})` of the cone is a closed immersion, hence a monomorphism
   (`twistedAffineCone.isClosedImmersion_ι`), so it suffices to compare the composites with `coneι`.
2. The correspondence `totalSpaceHomEquiv` between sections and morphisms is a bijection: a morphism
   `(W, W.ι ≫ p_κ ≫ ρ) → Tot(A^{⊕(N+1)})` in `Over C` is determined by a section in
   `Γ(W, (W.ι ≫ p_κ ≫ ρ)^*A^{⊕(N+1)})`; `A^{⊕(N+1)}` is a biproduct, so a section is determined by its
   `N+1` coordinates (images under `biproduct.π`). Hence it suffices to compare coordinatewise.
3. Coordinates of the left side: `totalSpaceHomEquiv` is natural in `T` (precomposition with the
   morphism `W.ι : (W, …) → (C̃_(κ)(L), p_κ ≫ ρ)` of `Over C` corresponds to pulling back sections along
   `W.ι`, up to the canonical isomorphism `pullbackComp`); hence the `ℓ`-th coordinate of
   `W.ι ≫ ȷ.hom ≫ coneι` is `ι_W^*(BasedJet.coneCoordinate ȷ ℓ)` (by definition, `coneCoordinate` is
   "apply `totalSpaceHomEquiv`, take the `ℓ`-th projection, transport along `pullbackComp` and the
   `eqToHom` of `OX_toModules`").
4. Coordinates of the right side: by the definition of `twistedAffineCone.scale` and
   `IsClosedImmersion.lift_fac`, the section corresponding to `scale u g ≫ coneι` is `u •` (the section
   corresponding to `g ≫ coneι`); scalar multiplication commutes with `biproduct.π` and `pullbackComp`,
   so the `ℓ`-th coordinate is `u •` (the `ℓ`-th coordinate of `g`). Here `g = W.ι ≫ p_κ ≫ ρ ≫ s`, and
   `s = seedSection` is obtained by applying `totalSpaceSectionEquiv` to `Σ_i ι_i(f_i)`, whose `ℓ`-th
   coordinate is `f_ℓ = D.coord ℓ`; by the naturality of step 3, the `ℓ`-th coordinate of `g` is
   `(W.ι ≫ p_κ ≫ ρ)^*f_ℓ = ι_W^*p_κ^*(seedCoordPullback f ρ (D.coord ℓ))` (up to the same canonical
   isomorphisms).
5. By hypothesis the `ℓ`-th coordinates of the two sides agree for all `ℓ`; by step 2 the two morphisms
   are equal.

Reference: the scalar jets of §3 of the paper (`ȷ = u·(s∘ρ∘p_L)`).

The categorical part lives in two auxiliary modules: `ConeMorphismScaleOfCoordinatesHelpers`
(compatibility of the pullback of sections with `pullbackComp` / `pullbackId` / `pullbackCongr`, the
`Over.mk b` version of `totalSpaceHomEquiv_naturality_coordinate`, the `ℓ`-th coordinate of the seed
section is `f_ℓ`, and the coordinate transport lemma `sectionPullbackAlong_coord_transport`) and
`ConeMorphismScaleOfCoordinatesCone` (the general version `twistedAffineCone.comp_eq_scale_of_coordinates`
for twisted affine cones). This file only instantiates: it unfolds `BasedJet.coneCoordinate` /
`seedCoordPullback` (definitional equalities), transports the coordinates and applies the general version.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section


/-- If the `ℓ`-th cone coordinate of the based jet `J`, restricted to `W = p_κ⁻¹U`, is the unit `u` times
the pulled-back seed coordinate `p_κ^*ρ^*f_ℓ` for every `ℓ`, then on `W` the jet is `u` times the seed
section: `W.ι ≫ J.hom = TwistedCone.scale f u (W.ι ≫ p_κ ≫ ρ ≫ s)`. -/
theorem BasedJet.restrict_eq_scale_of_coneCoordinate {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (U : ρ.source.toScheme.Opens)
    (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤)ˣ)
    (hcoord : ∀ ℓ,
      (sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι (BasedJet.coneCoordinate J ℓ) :
        (((AlgebraicGeometry.Scheme.Modules.pullback ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
            (seedBundlePullback f ρ).toModules)).val.obj (Opposite.op ⊤) : Type u))
        = (show ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from
            (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤))) •
          sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι
            (sectionPullbackAlong (jetNeighborhood.proj L κ)
              (seedCoordPullback f ρ (D.coord ℓ)))) :
    ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ J.hom
      = TwistedCone.scale f u
          (((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ jetNeighborhood.proj L κ ≫ ρ.hom
            ≫ (MMSetup.seed f).1) := by
  -- notation: A = seedLineBundle, p = p_κ, q = p ≫ ρ, W = p⁻¹U, ι_Z = the cone's closed immersion
  have hvan := seedSection_equations_vanish X.embedding D.E f D.coord D.hcoord
  -- the `Over`-morphism `T → Tot(A^{⊕(N+1)})` used in the definition of `coneCoordinate`
  let m : CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom) ⟶
      AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1)) :=
    CategoryTheory.Over.homMk
      (J.hom ≫ twistedAffineCone.ι (seedLineBundle X.embedding f) X.embDim D.E.deg D.E.F D.E.homogeneous)
      ((CategoryTheory.Category.assoc _ _ _).trans J.over)
  -- unpack `coneCoordinate` and `seedCoordPullback`, then transport the coordinate identity
  have hcoord' : ∀ ℓ, sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι
      ((((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ ≫ ρ.hom)).map
          (biproduct.π (fun _ : Fin (X.embDim + 1) => seedLineBundle X.embedding f) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv
          (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))
          (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom)) m))
      = (show ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from
          (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤))) •
        sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι
          (sectionPullbackAlong (jetNeighborhood.proj L κ ≫ ρ.hom) (D.coord ℓ)) := by
    intro ℓ
    refine sectionPullbackAlong_coord_transport ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι (jetNeighborhood.proj L κ) ρ.hom
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map (CategoryTheory.eqToHom (X.OX_toModules 1).symm))
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map (CategoryTheory.eqToHom (X.OX_toModules 1)))
      ?_ u _ (D.coord ℓ) (hcoord ℓ)
    rw [← CategoryTheory.Functor.map_comp, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl,
      CategoryTheory.Functor.map_id]
  have key := twistedAffineCone.comp_eq_scale_of_coordinates (seedLineBundle X.embedding f) X.embDim
    D.E.deg D.E.F D.E.homogeneous D.coord hvan (jetNeighborhood.proj L κ ≫ ρ.hom) J.hom m rfl
    ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι u hcoord'
  rw [← CategoryTheory.Category.assoc (jetNeighborhood.proj L κ) ρ.hom (MMSetup.seed f).1]
  exact key

end
