import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlas
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradingSubmodule
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Pullback of a weighted polynomial atlas

If the graded quasi-coherent algebra `S` carries a weighted polynomial atlas of weights `w`, then
for every morphism of schemes `g` the pullback `S.pullback g` (pulled back piece by piece) also
carries a weighted polynomial atlas of weights `w`.

Proof:
1. Refine the affine charts `U_i` of the given atlas by the affine opens contained in `g⁻¹(U_i)`;
   these cover the source and serve as the charts of the pulled-back atlas.
2. For each refined chart `W ⊆ g⁻¹(U_i)` and each degree `m`, Stacks 01I9
   (`Scheme.Modules.isIso_transpose_pullbackSectionsNative`) gives the canonical isomorphism
   `Γ(W) ⊗_{Γ(U_i)} Γ(U_i, S_m) ≅ Γ(W, (g^*S)_m)`.
3. Take the direct sum over `m` and use the monoidal structure of the pullback functor together with
   the naturality of `S.mul`, `S.one` to show that this isomorphism is compatible with the
   multiplication and the structure map of the sections rings; the `equiv i` of the given atlas
   replaces the second tensor factor by `MvPolynomial σ Γ(U_i)`.
4. Composing with Mathlib's `MvPolynomial.algebraTensorAlgEquiv` gives
   `Γ((g^*S)(W)) ≃+* MvPolynomial σ Γ(W)`. The degreewise isomorphisms of 01I9, the `equiv_grading`
   of the given atlas and the fact that base change of polynomials preserves weighted degree give
   `equiv_grading`; the computation of the pure tensors `r ⊗ 1` and `equiv_unit` of the given atlas
   give `equiv_unit`. Assembling the covering field yields the atlas.

Structure of the file:
* §0 (namespace `Modules`): `pullbackSectionsOn_unit` — the pullback of sections of the unit object
  is `ε` applied to `g^♯` (`ε = pullbackUnitIso.inv`, the adjunction description of Mathlib's
  `pullbackObjUnitToUnit`).
* §1: the piecewise pullback of sections `pullbackPiece`, compatible with `S.one`
  (`pullbackPiece_one_app`) and `S.mul` (`pullbackPiece_sectionsGMul`, via `μ = δ⁻¹` and
  `pullbackTensorObjHom_app_unit_tensorSections`), assembled into the ring homomorphism
  `Φ = pullbackSectionsRingHom : S(U) →+* (g^*S)(W)`.
* §2: the base change map `Ψ = pullbackTensorAlgHom : Γ(W) ⊗_{Γ(U)} S(U) →ₐ[Γ(W)] (g^*S)(W)`
  (`AlgHom.liftEquiv`); its bijectivity `pullbackTensorAlgHom_bijective` is piecewise 01I9
  (`pieceBaseChangeMap_bijective`) together with `TensorProduct.directSumRight` and the agreement of
  the two `Γ(U)`-module structures on the sections ring (`sectionsRingPieceEquiv`, `pieceSmulHom_eq`).
* §3: the general lemma `GradedRingHom.mem_iff_of_injective` — an injective graded ring homomorphism
  reflects the grading.
* §4: the chart isomorphism `pullbackAtlasEquiv = algebraTensorAlgEquiv ∘ congr(atlas iso) ∘ Ψ⁻¹`,
  with the bijectivity of `Ψ` as an explicit hypothesis `hΨ`; `equiv_grading` only needs that the
  preimage of a weighted homogeneous polynomial lies in the `m`-th piece
  (`pullbackAtlasEquiv_symm_mem`, by `IsWeightedHomogeneous.induction_on`) together with §3.
  The chart index is `Σ i, {W' affine // W' ≤ g⁻¹(chart i)}`, and the covering comes from
  `Scheme.isBasis_affineOpens`.

References: Stacks 01I9; Mathlib `MvPolynomial.algebraTensorAlgEquiv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X)

/-- `θ := (pullbackUnitIso g).hom` sends `η_{O_X}(r)` to `g^♯ r` (the sections form of Mathlib's
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`). -/
theorem pullbackUnitIso_hom_app_pullbackUnitHom (U : X.Opens) (r : Γ(X, U)) :
    (pullbackUnitIso g).hom.app (g ⁻¹ᵁ U) (pullbackUnitHom g (𝟙_ X.Modules) U r) =
      (g.app U).hom r := by
  have : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction g).isRightAdjoint
  have h := congrArg (fun φ : (𝟙_ X.Modules) ⟶ (pushforward g).obj (𝟙_ V.Modules) => φ.app U r)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      g.toRingCatSheafHom)
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- **The pullback of sections of the unit object is `ε` applied to `g^♯`**:
`(η_{O_X} r)|_W = ε_W (g.appLE r)`. -/
theorem pullbackSectionsOn_unit (U : X.Opens) (W : V.Opens) (h : W ≤ g ⁻¹ᵁ U) (r : Γ(X, U)) :
    pullbackSectionsOn g (𝟙_ X.Modules) U W h r =
      (CategoryTheory.Functor.LaxMonoidal.ε (pullback g)).app W ((g.appLE U W h).hom r) := by
  rw [pullback_ε_eq]
  have h1 : pullbackUnitHom g (𝟙_ X.Modules) U r =
      (pullbackUnitIso g).inv.app (g ⁻¹ᵁ U) ((g.app U).hom r) := by
    rw [← pullbackUnitIso_hom_app_pullbackUnitHom g U r]
    exact (congrArg (fun φ => φ.app (g ⁻¹ᵁ U) (pullbackUnitHom g (𝟙_ X.Modules) U r))
      (pullbackUnitIso g).hom_inv_id).symm
  refine (congrArg (fun z => ((pullback g).obj (𝟙_ X.Modules)).presheaf.map (homOfLE h).op z)
    h1).trans ?_
  exact (app_map (pullbackUnitIso g).inv h ((g.app U).hom r)).symm

end AlgebraicGeometry.Scheme.Modules

/-- `DirectSum.lmap` of componentwise bijections is bijective. -/
theorem DirectSum.lmap_bijective_of_bijective {ι R : Type*} [Semiring R] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (M i)]
    [∀ i, Module R (N i)] (f : ∀ i, M i →ₗ[R] N i) (hf : ∀ i, Function.Bijective (f i)) :
    Function.Bijective (DirectSum.lmap f) := by
  constructor
  · intro x y hxy
    ext i
    exact (hf i).1 (congrArg (fun z => z i) hxy)
  · intro y
    refine ⟨DirectSum.lmap (fun i => (LinearEquiv.ofBijective (f i) (hf i)).symm.toLinearMap) y, ?_⟩
    ext i
    exact (LinearEquiv.ofBijective (f i) (hf i)).apply_symm_apply (y i)

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X) (S : X.GradedQCAlgebra)
variable (U : X.Opens) (W : V.Opens) (h : W ≤ g ⁻¹ᵁ U)

/-! ## 1. The piecewise pullback of sections `Γ(U, S_m) → Γ(W, (g^*S)_m)` and its ring homomorphism -/

/-- Pullback followed by restriction of sections of the `m`-th piece (`pullbackSectionsOn`), typed
as the `m`-th piece of the pulled-back algebra. -/
def pullbackPiece (m : ℕ) : S.sectionsPiece U m →+ (S.pullback g).sectionsPiece W m :=
  AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn g (S.part m) U W h

theorem pullbackPiece_apply (m : ℕ) (a : S.sectionsPiece U m) :
    S.pullbackPiece g U W h m a =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn g (S.part m) U W h a := rfl

/-- **Compatibility of pullback with the unit**: the pullback to `W` of the value of `S.one` on `U` is
the value of `(g^*S).one` on `g^♯ r`. -/
theorem pullbackPiece_one_app (r : Γ(X, U)) :
    S.pullbackPiece g U W h 0 (S.one.app U r) = (S.pullback g).one.app W ((g.appLE U W h).hom r) := by
  -- naturality of `η` for `S.one`
  have h1 : Modules.pullbackUnitHom g (S.part 0) U (S.one.app U r) =
      ((Modules.pullback g).map S.one).app (g ⁻¹ᵁ U)
        (Modules.pullbackUnitHom g (𝟙_ X.Modules) U r) :=
    congrArg (fun φ => φ.app U r) ((Modules.pullbackPushforwardAdjunction g).unit.naturality S.one)
  refine (congrArg (fun z => ((Modules.pullback g).obj (S.part 0)).presheaf.map (homOfLE h).op z)
    h1).trans ?_
  refine (Modules.app_map ((Modules.pullback g).map S.one) h _).symm.trans ?_
  exact congrArg (fun z => ((Modules.pullback g).map S.one).app W z)
    (Modules.pullbackSectionsOn_unit g U W h r)

theorem pullbackPiece_sectionsGOne :
    S.pullbackPiece g U W h 0 (S.sectionsGOne U) = (S.pullback g).sectionsGOne W := by
  show S.pullbackPiece g U W h 0 (S.one.app U (1 : Γ(X, U)))
    = (S.pullback g).one.app W (1 : Γ(V, W))
  rw [S.pullbackPiece_one_app g U W h 1, map_one]

/-- **Compatibility of pullback with the graded multiplication** (the sections description of the
monoidal structure `μ` of the pullback functor). -/
theorem pullbackPiece_sectionsGMul {m n : ℕ} (a : S.sectionsPiece U m) (b : S.sectionsPiece U n) :
    S.pullbackPiece g U W h (m + n) (S.sectionsGMul U a b) =
      (S.pullback g).sectionsGMul W (S.pullbackPiece g U W h m a) (S.pullbackPiece g U W h n b) := by
  -- naturality of `η` for `S.mul m n`
  have h1 : Modules.pullbackUnitHom g (S.part (m + n)) U
        ((S.mul m n).app U (Modules.tensorSections (S.part m) (S.part n) U a b)) =
      ((Modules.pullback g).map (S.mul m n)).app (g ⁻¹ᵁ U)
        (Modules.pullbackUnitHom g (S.part m ⊗ S.part n) U
          (Modules.tensorSections (S.part m) (S.part n) U a b)) :=
    congrArg (fun φ => φ.app U (Modules.tensorSections (S.part m) (S.part n) U a b))
      ((Modules.pullbackPushforwardAdjunction g).unit.naturality (S.mul m n))
  -- the sections description of `δ`: `η (a ⊗ b) = μ (η a ⊗ η b)`
  have h3 : Modules.pullbackUnitHom g (S.part m ⊗ S.part n) U
        (Modules.tensorSections (S.part m) (S.part n) U a b) =
      (Modules.pullbackTensorObjIso g (S.part m) (S.part n)).inv.app (g ⁻¹ᵁ U)
        (Modules.tensorSections ((Modules.pullback g).obj (S.part m))
          ((Modules.pullback g).obj (S.part n)) (g ⁻¹ᵁ U)
          (Modules.pullbackUnitHom g (S.part m) U a) (Modules.pullbackUnitHom g (S.part n) U b)) := by
    have h2 := Modules.pullbackTensorObjHom_app_unit_tensorSections g (S.part m) (S.part n) U a b
    have h4 := congrArg (fun φ => φ.app (g ⁻¹ᵁ U) (Modules.pullbackUnitHom g (S.part m ⊗ S.part n) U
      (Modules.tensorSections (S.part m) (S.part n) U a b)))
      (Modules.pullbackTensorObjIso g (S.part m) (S.part n)).hom_inv_id
    exact h4.symm.trans (congrArg (fun z =>
      (Modules.pullbackTensorObjIso g (S.part m) (S.part n)).inv.app (g ⁻¹ᵁ U) z) h2)
  show ((Modules.pullback g).obj (S.part (m + n))).presheaf.map (homOfLE h).op
      (Modules.pullbackUnitHom g (S.part (m + n)) U
        ((S.mul m n).app U (Modules.tensorSections (S.part m) (S.part n) U a b))) =
    ((Modules.pullback g).map (S.mul m n)).app W
      ((Modules.pullbackTensorObjIso g (S.part m) (S.part n)).inv.app W
        (Modules.tensorSections ((Modules.pullback g).obj (S.part m))
          ((Modules.pullback g).obj (S.part n)) W
          (S.pullbackPiece g U W h m a) (S.pullbackPiece g U W h n b)))
  refine (congrArg (fun z => ((Modules.pullback g).obj (S.part (m + n))).presheaf.map
    (homOfLE h).op z) h1).trans ?_
  refine (Modules.app_map ((Modules.pullback g).map (S.mul m n)) h _).symm.trans ?_
  refine (congrArg (fun z => ((Modules.pullback g).map (S.mul m n)).app W
    (((Modules.pullback g).obj (S.part m ⊗ S.part n)).presheaf.map (homOfLE h).op z)) h3).trans ?_
  refine (congrArg (fun z => ((Modules.pullback g).map (S.mul m n)).app W z)
    (Modules.app_map (Modules.pullbackTensorObjIso g (S.part m) (S.part n)).inv h _).symm).trans ?_
  exact congrArg (fun z => ((Modules.pullback g).map (S.mul m n)).app W
    ((Modules.pullbackTensorObjIso g (S.part m) (S.part n)).inv.app W z))
    (Modules.tensorSections_restrict ((Modules.pullback g).obj (S.part m))
      ((Modules.pullback g).obj (S.part n)) (homOfLE h) _ _)

/-- The pullback homomorphism of sections rings `Φ : S(U) →+* (g^*S)(W)` (piecewise `pullbackPiece`). -/
def pullbackSectionsRingHom : S.sectionsRing U →+* (S.pullback g).sectionsRing W :=
  DirectSum.toSemiring
    (fun m => (DirectSum.of ((S.pullback g).sectionsPiece W) m).comp (S.pullbackPiece g U W h m))
    (by
      show DirectSum.of ((S.pullback g).sectionsPiece W) 0
        (S.pullbackPiece g U W h 0 (S.sectionsGOne U)) = 1
      rw [S.pullbackPiece_sectionsGOne g U W h]
      rfl)
    (fun {i j} a b => by
      show DirectSum.of ((S.pullback g).sectionsPiece W) (i + j)
        (S.pullbackPiece g U W h (i + j) (S.sectionsGMul U a b)) = _
      rw [S.pullbackPiece_sectionsGMul g U W h a b]
      exact (DirectSum.of_mul_of _ _).symm)

theorem pullbackSectionsRingHom_of (m : ℕ) (a : S.sectionsPiece U m) :
    S.pullbackSectionsRingHom g U W h (DirectSum.of (S.sectionsPiece U) m a) =
      DirectSum.of ((S.pullback g).sectionsPiece W) m (S.pullbackPiece g U W h m a) :=
  DirectSum.toSemiring_of _ _ _ m a

theorem pullbackSectionsRingHom_ofPiece (m : ℕ) (a : S.sectionsPiece U m) :
    S.pullbackSectionsRingHom g U W h (S.ofPiece U m a) =
      (S.pullback g).ofPiece W m (S.pullbackPiece g U W h m a) :=
  S.pullbackSectionsRingHom_of g U W h m a

/-- `Φ` is compatible with the structure maps: `Φ (unit_U r) = unit_W (g^♯ r)`. -/
theorem pullbackSectionsRingHom_sectionsUnitHom (r : Γ(X, U)) :
    S.pullbackSectionsRingHom g U W h (S.sectionsUnitHom U r) =
      (S.pullback g).sectionsUnitHom W ((g.appLE U W h).hom r) := by
  have h1 : S.sectionsUnitHom U r = DirectSum.of (S.sectionsPiece U) 0 (S.one.app U r) := rfl
  have h2 : (S.pullback g).sectionsUnitHom W ((g.appLE U W h).hom r)
      = DirectSum.of ((S.pullback g).sectionsPiece W) 0
          ((S.pullback g).one.app W ((g.appLE U W h).hom r)) := rfl
  rw [h1, h2]
  exact (S.pullbackSectionsRingHom_of g U W h 0 (S.one.app U r)).trans
    (congrArg (DirectSum.of ((S.pullback g).sectionsPiece W) 0) (S.pullbackPiece_one_app g U W h r))


/-- `Φ` preserves the grading: the `m`-th piece is sent into the `m`-th piece. -/
theorem pullbackSectionsRingHom_mem {m : ℕ} {a : S.sectionsRing U} (ha : a ∈ S.sectionsGrading U m) :
    S.pullbackSectionsRingHom g U W h a ∈ (S.pullback g).sectionsGrading W m := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨S.pullbackPiece g U W h m a', (S.pullbackSectionsRingHom_of g U W h m a').symm⟩

/-! ## 2. The base change map `Ψ : Γ(V,W) ⊗_{Γ(X,U)} S(U) → (g^*S)(W)` -/

section Tensor

open scoped TensorProduct

variable (U' : X.AffineZariskiSite) (W' : V.AffineZariskiSite)
  (hW : W'.toOpens ≤ g ⁻¹ᵁ U'.toOpens)

/-- `Γ(V, W)` as a `Γ(X, U)`-algebra (via `g^♯ : Γ(X,U) → Γ(V,W)`). -/
abbrev pullbackBaseAlgebra : Algebra Γ(X, U'.toOpens) Γ(V, W'.toOpens) :=
  (g.appLE U'.toOpens W'.toOpens hW).hom.toAlgebra

/-- `(g^*S)(W)` as a `Γ(X, U)`-algebra (`g^♯` followed by the structure map). -/
abbrev pullbackSectionsAlgebra :
    Algebra Γ(X, U'.toOpens) ((S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.sections W') :=
  (((S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.unitHom W').comp
    (g.appLE U'.toOpens W'.toOpens hW).hom).toAlgebra

/-- `Φ` as a `Γ(X,U)`-algebra homomorphism `S(U) →ₐ (g^*S)(W)`. -/
def pullbackSectionsAlgHom :
    letI := S.pullbackSectionsAlgebra g U' W' hW
    S.toGradedAffineAlgebra.toAffineAlgebra.sections U' →ₐ[Γ(X, U'.toOpens)]
      (S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.sections W' :=
  letI := S.pullbackSectionsAlgebra g U' W' hW
  { toRingHom := S.pullbackSectionsRingHom g U'.toOpens W'.toOpens hW
    commutes' := fun r => S.pullbackSectionsRingHom_sectionsUnitHom g U'.toOpens W'.toOpens hW r }

/-- **The base change map** `Ψ : Γ(V,W) ⊗_{Γ(X,U)} S(U) →ₐ[Γ(V,W)] (g^*S)(W)`, `b ⊗ a ↦ b • Φ a`. -/
def pullbackTensorAlgHom :
    letI := pullbackBaseAlgebra g U' W' hW
    letI := S.pullbackSectionsAlgebra g U' W' hW
    (Γ(V, W'.toOpens) ⊗[Γ(X, U'.toOpens)] S.toGradedAffineAlgebra.toAffineAlgebra.sections U')
      →ₐ[Γ(V, W'.toOpens)] (S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.sections W' :=
  letI := pullbackBaseAlgebra g U' W' hW
  letI := S.pullbackSectionsAlgebra g U' W' hW
  haveI : IsScalarTower Γ(X, U'.toOpens) Γ(V, W'.toOpens)
      ((S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.sections W') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  AlgHom.liftEquiv _ _ _ _ (S.pullbackSectionsAlgHom g U' W' hW)

theorem pullbackTensorAlgHom_tmul (b : Γ(V, W'.toOpens))
    (a : S.toGradedAffineAlgebra.toAffineAlgebra.sections U') :
    letI := pullbackBaseAlgebra g U' W' hW
    letI := S.pullbackSectionsAlgebra g U' W' hW
    S.pullbackTensorAlgHom g U' W' hW (b ⊗ₜ a) = b • S.pullbackSectionsAlgHom g U' W' hW a := rfl

/-! ### Bijectivity: piecewise 01I9 and the commutation of tensor products with direct sums -/

/-- The `Γ(X,U)`-module structure on `Γ(U, S_m)`, registered in the spelling `sectionsPiece`
(as for `sectionsPieceModule_ofGradedQCAlgebra`: Mathlib's instance lives on `Γ(S.part m, U)`, and
instance search does not find a `Module` on `⨁ m, S.sectionsPiece U m` from it). -/
local instance sectionsPieceModule_atlasPullback {Y : AlgebraicGeometry.Scheme.{u}}
    (T : Y.GradedQCAlgebra) (O : Y.Opens) (m : ℕ) : Module Γ(Y, O) (T.sectionsPiece O m) :=
  inferInstanceAs (Module Γ(Y, O) Γ(T.part m, O))

/-- **The canonical map of 01I9, piecewise**: `Γ(V,W) ⊗_{Γ(X,U)} Γ(U, S_m) →ₗ Γ(W, (g^*S)_m)`,
`b ⊗ s ↦ b • (g^*s)|_W` (the adjoint transpose of `pullbackSectionsNative`). -/
def pieceBaseChangeMap (m : ℕ) :
    letI := pullbackBaseAlgebra g U' W' hW
    TensorProduct Γ(X, U'.toOpens) Γ(V, W'.toOpens) (S.sectionsPiece U'.toOpens m)
      →ₗ[Γ(V, W'.toOpens)] (S.pullback g).sectionsPiece W'.toOpens m :=
  letI := pullbackBaseAlgebra g U' W' hW
  (((ModuleCat.extendRestrictScalarsAdj (g.appLE U'.toOpens W'.toOpens hW).hom).homEquiv _ _).symm
    (Modules.pullbackSectionsNative g (S.part m) U'.toOpens W'.toOpens hW)).hom

theorem pieceBaseChangeMap_tmul (m : ℕ) (b : Γ(V, W'.toOpens))
    (s : S.sectionsPiece U'.toOpens m) :
    letI := pullbackBaseAlgebra g U' W' hW
    S.pieceBaseChangeMap g U' W' hW m (b ⊗ₜ s) =
      b • S.pullbackPiece g U'.toOpens W'.toOpens hW m s := rfl

/-- **Stacks 01I9, piecewise** (`isIso_transpose_pullbackSectionsNative`): the canonical map is
bijective. -/
theorem pieceBaseChangeMap_bijective (m : ℕ) :
    letI := pullbackBaseAlgebra g U' W' hW
    Function.Bijective (S.pieceBaseChangeMap g U' W' hW m) := by
  let _ := pullbackBaseAlgebra g U' W' hW
  have := S.quasicoherent m
  have := Modules.isIso_transpose_pullbackSectionsNative g (S.part m) U'.toOpens U'.2
    W'.toOpens W'.2 hW
  exact ConcreteCategory.bijective_of_isIso
    (((ModuleCat.extendRestrictScalarsAdj (g.appLE U'.toOpens W'.toOpens hW).hom).homEquiv _ _).symm
      (Modules.pullbackSectionsNative g (S.part m) U'.toOpens W'.toOpens hW))

/-- The two `Γ(X,U)`-module structures on the sections ring (from the structure map of the algebra
and piecewise) agree (`pieceSmulHom_eq`): the identity is a linear isomorphism. -/
def sectionsRingPieceEquiv :
    S.toGradedAffineAlgebra.toAffineAlgebra.sections U' ≃ₗ[Γ(X, U'.toOpens)]
      ⨁ m, S.sectionsPiece U'.toOpens m where
  toFun a := a
  invFun a := a
  map_add' _ _ := rfl
  map_smul' r a := (S.pieceSmulHom_eq U'.toOpens r a).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- Tensor products commute with direct sums (Mathlib `TensorProduct.directSumRight`). -/
def tensorDirectSumEquiv :
    letI := pullbackBaseAlgebra g U' W' hW
    (Γ(V, W'.toOpens) ⊗[Γ(X, U'.toOpens)] ⨁ m, S.sectionsPiece U'.toOpens m)
      ≃ₗ[Γ(V, W'.toOpens)]
      ⨁ m, Γ(V, W'.toOpens) ⊗[Γ(X, U'.toOpens)] S.sectionsPiece U'.toOpens m :=
  letI := pullbackBaseAlgebra g U' W' hW
  TensorProduct.directSumRight Γ(X, U'.toOpens) Γ(V, W'.toOpens) Γ(V, W'.toOpens)
    (fun m => S.sectionsPiece U'.toOpens m)

/-- **Factorization of `Ψ`**: `Ψ = (⊕_m 01I9_m) ∘ (tensor/direct sum commutation) ∘ (identity
changing the module structure)`. -/
theorem pullbackTensorAlgHom_eq_comp (x : _) :
    letI := pullbackBaseAlgebra g U' W' hW
    letI := S.pullbackSectionsAlgebra g U' W' hW
    (S.pullbackTensorAlgHom g U' W' hW x : (S.pullback g).sectionsRing W'.toOpens) =
      DirectSum.lmap (fun m => S.pieceBaseChangeMap g U' W' hW m)
        (S.tensorDirectSumEquiv g U' W' hW
          (TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl Γ(V, W'.toOpens) Γ(V, W'.toOpens))
            (S.sectionsRingPieceEquiv U') x)) := by
  let _ := pullbackBaseAlgebra g U' W' hW
  let _ := S.pullbackSectionsAlgebra g U' W' hW
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl
  | tmul b a =>
    obtain ⟨a', rfl⟩ : ∃ a' : ⨁ m, S.sectionsPiece U'.toOpens m,
        (a' : S.toGradedAffineAlgebra.toAffineAlgebra.sections U') = a := ⟨a, rfl⟩
    -- `congr refl e (b ⊗ a') = b ⊗ a'` holds by definition (`congr_tmul` is `rfl`)
    show (S.pullbackTensorAlgHom g U' W' hW (b ⊗ₜ a') : (S.pullback g).sectionsRing W'.toOpens) =
      DirectSum.lmap (fun m => S.pieceBaseChangeMap g U' W' hW m)
        (S.tensorDirectSumEquiv g U' W' hW (b ⊗ₜ a'))
    induction a' using DirectSum.induction_on with
    | zero =>
      refine Eq.trans (congrArg (fun z => (S.pullbackTensorAlgHom g U' W' hW z :
        (S.pullback g).sectionsRing W'.toOpens))
        ((TensorProduct.mk Γ(X, U'.toOpens) Γ(V, W'.toOpens)
          (S.toGradedAffineAlgebra.toAffineAlgebra.sections U') b).map_zero)) ?_
      refine Eq.trans (map_zero (S.pullbackTensorAlgHom g U' W' hW)) ?_
      refine Eq.trans ?_ (congrArg (fun z =>
        DirectSum.lmap (fun m => S.pieceBaseChangeMap g U' W' hW m)
          (S.tensorDirectSumEquiv g U' W' hW z))
        ((TensorProduct.mk Γ(X, U'.toOpens) Γ(V, W'.toOpens)
          (⨁ m, S.sectionsPiece U'.toOpens m) b).map_zero)).symm
      rw [map_zero, map_zero]
      rfl
    | of m s =>
      refine Eq.trans (S.pullbackTensorAlgHom_tmul g U' W' hW b
        (DirectSum.of (S.sectionsPiece U'.toOpens) m s)) ?_
      refine Eq.trans (Algebra.smul_def b _) ?_
      refine Eq.trans (congrArg (fun z => (S.pullback g).sectionsUnitHom W'.toOpens b * z)
        (S.pullbackSectionsRingHom_of g U'.toOpens W'.toOpens hW m s)) ?_
      refine Eq.trans ((S.pullback g).sectionsUnitHom_mul_ofPiece W'.toOpens b
        (S.pullbackPiece g U'.toOpens W'.toOpens hW m s)) ?_
      refine Eq.trans ?_ (congrArg
        (DirectSum.lmap fun m => S.pieceBaseChangeMap g U' W' hW m)
        (TensorProduct.directSumRight_tmul_lof Γ(X, U'.toOpens) Γ(V, W'.toOpens) b m s)).symm
      refine Eq.trans ?_ (DirectSum.lmap_lof
        (fun m => S.pieceBaseChangeMap g U' W' hW m) m (b ⊗ₜ s)).symm
      rfl
    | add x y hx hy =>
      refine Eq.trans (congrArg (fun z => (S.pullbackTensorAlgHom g U' W' hW z :
        (S.pullback g).sectionsRing W'.toOpens))
        ((TensorProduct.mk Γ(X, U'.toOpens) Γ(V, W'.toOpens)
          (S.toGradedAffineAlgebra.toAffineAlgebra.sections U') b).map_add x y)) ?_
      refine Eq.trans (map_add (S.pullbackTensorAlgHom g U' W' hW) _ _) ?_
      refine Eq.trans (congrArg₂ (fun u v : (S.pullback g).sectionsRing W'.toOpens => u + v)
        hx hy) ?_
      refine Eq.trans ?_ (congrArg (fun z =>
        DirectSum.lmap (fun m => S.pieceBaseChangeMap g U' W' hW m)
          (S.tensorDirectSumEquiv g U' W' hW z))
        ((TensorProduct.mk Γ(X, U'.toOpens) Γ(V, W'.toOpens)
          (⨁ m, S.sectionsPiece U'.toOpens m) b).map_add x y)).symm
      rw [map_add, map_add]
      rfl

/-- **The graded version of Stacks 01I9**: `Ψ` is bijective. -/
theorem pullbackTensorAlgHom_bijective :
    letI := pullbackBaseAlgebra g U' W' hW
    letI := S.pullbackSectionsAlgebra g U' W' hW
    Function.Bijective (S.pullbackTensorAlgHom g U' W' hW) := by
  let _ := pullbackBaseAlgebra g U' W' hW
  let _ := S.pullbackSectionsAlgebra g U' W' hW
  have hfun : (S.pullbackTensorAlgHom g U' W' hW : _ → (S.pullback g).sectionsRing W'.toOpens) =
      (DirectSum.lmap (fun m => S.pieceBaseChangeMap g U' W' hW m)) ∘
        (S.tensorDirectSumEquiv g U' W' hW) ∘
        (TensorProduct.AlgebraTensorModule.congr
          (LinearEquiv.refl Γ(V, W'.toOpens) Γ(V, W'.toOpens)) (S.sectionsRingPieceEquiv U')) :=
    funext fun x => S.pullbackTensorAlgHom_eq_comp g U' W' hW x
  show Function.Bijective (S.pullbackTensorAlgHom g U' W' hW : _ → (S.pullback g).sectionsRing W'.toOpens)
  rw [hfun]
  exact (DirectSum.lmap_bijective_of_bijective _ (S.pieceBaseChangeMap_bijective g U' W' hW)).comp
    ((S.tensorDirectSumEquiv g U' W' hW).bijective.comp (LinearEquiv.bijective _))

end Tensor

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-! ## 3. A general lemma: an injective graded ring homomorphism reflects the grading -/

/-- If the graded ring homomorphism `f` is injective, then `a ∈ 𝒜 i ↔ f a ∈ ℬ i` (uniqueness of the
decomposition). -/
theorem GradedRingHom.mem_iff_of_injective {ι A B σA σB : Type*} [DecidableEq ι] [AddMonoid ι]
    [Semiring A] [Semiring B] [SetLike σA A] [AddSubmonoidClass σA A] [SetLike σB B]
    [AddSubmonoidClass σB B] {𝒜 : ι → σA} {ℬ : ι → σB} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Injective f) (i : ι) (a : A) :
    a ∈ 𝒜 i ↔ f a ∈ ℬ i := by
  classical
  refine ⟨fun ha => f.map_mem ha, fun hfa => ?_⟩
  have hk : ∀ k, k ≠ i → (DirectSum.decompose 𝒜 a k : A) = 0 := fun k hk => by
    apply hf
    rw [map_zero, GradedRingHom.map_directSumDecompose, DirectSum.decompose_of_mem_ne ℬ hfa hk.symm]
  have ha : a = (DirectSum.decompose 𝒜 a i : A) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
    refine Finset.sum_eq_single i (fun k _ hki => hk k hki) fun hi => ?_
    rw [DFinsupp.notMem_support_iff.mp hi]
    rfl
  rw [ha]
  exact (DirectSum.decompose 𝒜 a i).2

/-! ## 4. The ring isomorphism on a chart and the assembly of the atlas -/

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

variable {X : AlgebraicGeometry.Scheme.{u}} {S : X.GradedAffineAlgebra} {σ : Type u} {w : σ → ℕ}

/-- The chart ring isomorphism upgraded to a `Γ(X,U)`-algebra isomorphism (by `equiv_unit`). -/
def algEquiv (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    S.toAffineAlgebra.sections (𝒜.chart i) ≃ₐ[Γ(X, (𝒜.chart i).toOpens)]
      MvPolynomial σ Γ(X, (𝒜.chart i).toOpens) :=
  AlgEquiv.ofRingEquiv (f := 𝒜.equiv i) fun r => by
    rw [MvPolynomial.algebraMap_eq]
    exact 𝒜.equiv_unit i r

theorem algEquiv_apply (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I)
    (a : S.toAffineAlgebra.sections (𝒜.chart i)) : 𝒜.algEquiv i a = 𝒜.equiv i a := rfl

theorem algEquiv_symm_apply (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I)
    (p : MvPolynomial σ Γ(X, (𝒜.chart i).toOpens)) :
    (𝒜.algEquiv i).symm p = (𝒜.equiv i).symm p := rfl

end AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

open scoped TensorProduct

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X) (S : X.GradedQCAlgebra)
variable {σ : Type u} {w : σ → ℕ} (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) (i : 𝒜.I)
variable (W' : V.AffineZariskiSite) (hW : W'.toOpens ≤ g ⁻¹ᵁ (𝒜.chart i).toOpens)

/- The chart isomorphism below takes the bijectivity of `Ψ` as an explicit hypothesis `hΨ` instead
of invoking `pullbackTensorAlgHom_bijective` inside the definition; `hΨ` is supplied in the proof of
the final `Nonempty` theorem. -/
variable (hΨ : letI := pullbackBaseAlgebra g (𝒜.chart i) W' hW
  letI := S.pullbackSectionsAlgebra g (𝒜.chart i) W' hW
  Function.Bijective (S.pullbackTensorAlgHom g (𝒜.chart i) W' hW))

/-- The `Γ(V,W)`-algebra isomorphism `(g^*S)(W) ≃ₐ Γ(V,W)[x_σ]` on a refined chart `W ⊆ g⁻¹(U_i)`:
`Ψ⁻¹`, then the chart isomorphism on the second tensor factor, then `algebraTensorAlgEquiv`. -/
def pullbackAtlasAlgEquiv :
    letI := pullbackBaseAlgebra g (𝒜.chart i) W' hW
    (S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.sections W' ≃ₐ[Γ(V, W'.toOpens)]
      MvPolynomial σ Γ(V, W'.toOpens) :=
  letI := pullbackBaseAlgebra g (𝒜.chart i) W' hW
  letI := S.pullbackSectionsAlgebra g (𝒜.chart i) W' hW
  (AlgEquiv.ofBijective _ hΨ).symm.trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl (𝒜.algEquiv i)).trans
      (MvPolynomial.algebraTensorAlgEquiv Γ(X, (𝒜.chart i).toOpens) Γ(V, W'.toOpens)))

/-- The ring isomorphism on a refined chart (the `equiv` field of the atlas). -/
def pullbackAtlasEquiv :
    (S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.sections W' ≃+*
      MvPolynomial σ Γ(V, W'.toOpens) :=
  letI := pullbackBaseAlgebra g (𝒜.chart i) W' hW
  (S.pullbackAtlasAlgEquiv g 𝒜 i W' hW hΨ).toRingEquiv

/-- The `equiv_unit` field of the atlas: the structure map corresponds to the constants. -/
theorem pullbackAtlasEquiv_unitHom (r : Γ(V, W'.toOpens)) :
    S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ
        ((S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.unitHom W' r) =
      MvPolynomial.C r :=
  letI := pullbackBaseAlgebra g (𝒜.chart i) W' hW
  (S.pullbackAtlasAlgEquiv g 𝒜 i W' hW hΨ).commutes r

/-- Conversely, a weighted homogeneous polynomial of weight `m` comes from the `m`-th piece of the
pulled-back algebra. -/
theorem pullbackAtlasEquiv_symm_mem (m : ℕ) (p : MvPolynomial σ Γ(V, W'.toOpens))
    (hp : p.IsWeightedHomogeneous w m) :
    (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ).symm p ∈ (S.pullback g).toGradedAffineAlgebra.grading W' m := by
  let _ := pullbackBaseAlgebra g (𝒜.chart i) W' hW
  let _ := S.pullbackSectionsAlgebra g (𝒜.chart i) W' hW
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact add_mem ihp ihq
  | monomial d c hd =>
    have key : (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ).symm (MvPolynomial.monomial d c) =
        S.pullbackTensorAlgHom g (𝒜.chart i) W' hW
          (c ⊗ₜ (𝒜.equiv i).symm (MvPolynomial.monomial d 1)) := by
      show (AlgEquiv.ofBijective _ hΨ)
        ((Algebra.TensorProduct.congr AlgEquiv.refl (𝒜.algEquiv i)).symm
          ((MvPolynomial.algebraTensorAlgEquiv Γ(X, (𝒜.chart i).toOpens)
            Γ(V, W'.toOpens)).symm (MvPolynomial.monomial d c))) = _
      rw [MvPolynomial.algebraTensorAlgEquiv_symm_monomial]
      rfl
    rw [key, pullbackTensorAlgHom_tmul]
    have hs : (𝒜.equiv i).symm (MvPolynomial.monomial d 1) ∈
        S.toGradedAffineAlgebra.grading (𝒜.chart i) m :=
      𝒜.symm_mem i (MvPolynomial.isWeightedHomogeneous_monomial w d 1 hd)
    have hΦ : S.pullbackSectionsAlgHom g (𝒜.chart i) W' hW
        ((𝒜.equiv i).symm (MvPolynomial.monomial d 1)) ∈
          (S.pullback g).toGradedAffineAlgebra.grading W' m :=
      S.pullbackSectionsRingHom_mem g (𝒜.chart i).toOpens W'.toOpens hW hs
    exact ((S.pullback g).toGradedAffineAlgebra.gradingSubmodule W' m).smul_mem c hΦ

/-- The `equiv_grading` field of the atlas: the `m`-th piece corresponds to the weighted homogeneous
component of weight `m`. -/
theorem pullbackAtlasEquiv_grading (m : ℕ)
    (a : (S.pullback g).toGradedAffineAlgebra.toAffineAlgebra.sections W') :
    a ∈ (S.pullback g).toGradedAffineAlgebra.grading W' m ↔
      (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ a).IsWeightedHomogeneous w m := by
  let f : MvPolynomial.weightedHomogeneousSubmodule Γ(V, W'.toOpens) w →+*ᵍ
      (S.pullback g).toGradedAffineAlgebra.grading W' :=
    { toRingHom := (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ).symm.toRingHom
      map_mem := fun {m} {p} hp => S.pullbackAtlasEquiv_symm_mem g 𝒜 i W' hW hΨ m p hp }
  have key := GradedRingHom.mem_iff_of_injective f
    (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ).symm.injective m (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ a)
  have hfa : f (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ a) = a :=
    (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ).symm_apply_apply a
  rw [hfa] at key
  exact key.symm

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-- The pullback of a graded quasi-coherent algebra with a weighted polynomial atlas carries a
weighted polynomial atlas with the same weights. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.weightedPolynomialAtlas_pullback
    {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X) (S : X.GradedQCAlgebra)
    {σ : Type u} (w : σ → ℕ)
    (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) :
    Nonempty ((S.pullback g).toGradedAffineAlgebra.WeightedPolynomialAtlas w) := by
  refine ⟨{ I := Σ i : 𝒜.I, {W' : V.AffineZariskiSite // W'.toOpens ≤ g ⁻¹ᵁ (𝒜.chart i).toOpens}
            chart := fun p => p.2.1
            covers := fun v => ?_
            equiv := fun p => S.pullbackAtlasEquiv g 𝒜 p.1 p.2.1 p.2.2
              (S.pullbackTensorAlgHom_bijective g (𝒜.chart p.1) p.2.1 p.2.2)
            equiv_grading := fun p m a => S.pullbackAtlasEquiv_grading g 𝒜 p.1 p.2.1 p.2.2
              (S.pullbackTensorAlgHom_bijective g (𝒜.chart p.1) p.2.1 p.2.2) m a
            equiv_unit := fun p r => S.pullbackAtlasEquiv_unitHom g 𝒜 p.1 p.2.1 p.2.2
              (S.pullbackTensorAlgHom_bijective g (𝒜.chart p.1) p.2.1 p.2.2) r }⟩
  obtain ⟨i, hi⟩ := 𝒜.covers (g.base v)
  obtain ⟨W₀, hW₀, hvW₀, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.isBasis_affineOpens
    (show v ∈ g ⁻¹ᵁ (𝒜.chart i).toOpens from hi)
  exact ⟨⟨i, ⟨⟨W₀, hW₀⟩, hle⟩⟩, hvW₀⟩

end
