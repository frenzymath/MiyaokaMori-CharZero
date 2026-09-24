import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.TwistMultiplicationRestrictTensorSections

/-! # Chart-level value of the local twist multiplication

Section-level formula for the local multiplication `twistMulLocal S a b U` of the relative Proj
(`TwistMultiplication`): transported to the chart `Proj A(U)` by the 01NR comparison
`twistAffineIso S U n` (followed by `restrictFunctorIsoPullback`), it is the pointwise multiplication
`Proj.twistMul` of the chart (Stacks 01MO), i.e. on a pure tensor section `x ⊗ y`

  χ_{a+b}(twistMulLocal (x ⊗ y)) = Proj.twistMul (χ_a x ⊗ χ_b y),   χ_n := twistAffineIso.hom ≫ rFIP⁻¹.

Route: `twistMulLocal` is an instance of a generic shape `localMulShape` (seven canonical isomorphisms
around a multiplication `μ`, with the families `T = twist S`, `O = Proj.twist 𝒜`, `e = twistAffineIso S U` as variables);
`localMulShape_comp` is the morphism-level normal form (iso cancellations and the naturality of
`restrictFunctorIsoPullback`), `localMulNF_app` evaluates the normal form on pure tensor sections
(`restrictTensorObjIso_*_app_tensorSections`, `tensorHom_tensorSections`, `tensorIsoTensorObj_inv_app_tensorSections`),
and `twistMulLocal_app_chart` instantiates.

Kernel discipline (this is what made the instantiation compile — a first version exceeded 60 s in the kernel):
the body of `twistMulLocal` differs from a freshly elaborated copy of it in exactly three *proof* terms (Lean abstracts the
nested `Prop`-valued instances `AddSubgroupClass`, `IsOpenImmersion ι`, `IsOpenImmersion φ` of a definition value into
`twistMulLocal._proof_i`), and these sit under projection heads (`≫`, `.app`, `.hom`), for which the kernel unfolds
both sides completely instead of comparing arguments. So the identification is done in two structural steps:
`twistMulLocalShape` takes the three proofs as parameters and is otherwise the body of `twistMulLocal` verbatim
(`twistMulLocal_eq_localMulShape`, `rfl` with the three holes filled by unification from the body itself), and the change
to the synthesized instances happens under the regular head `localMulShape`, where the kernel compares argument by
argument and closes each proof pair by proof irrelevance. `localMulShape` keeps the `let loc := fun n => …` of the
original body so that the zeta-reduced bodies are syntactically identical (verified by a structural diff; kernel time
of every declaration < 0.5 s).

Source: Stacks 01MO, 01NR. Used for the associativity of `twistMul` on sections (`RelativeProjTwistMulAssoc`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules


theorem app_comp_apply' {X' : AlgebraicGeometry.Scheme.{u}} {M N P : X'.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (U : X'.Opens) (x : Γ(M, U)) : (f ≫ g).app U x = g.app U (f.app U x) := rfl

theorem Hom.app_congr' {X' : AlgebraicGeometry.Scheme.{u}} {M N : X'.Modules}
    {f g : M ⟶ N} (h : f = g) (U : X'.Opens) (x : Γ(M, U)) : f.app U x = g.app U x := by
  subst h; rfl

variable {Y P Z : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ P) [AlgebraicGeometry.IsOpenImmersion ι]
  (φ : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion φ]

section NF
variable (Ta Tb : P.Modules) (Oa Ob Oab : Z.Modules)
  (χa : Ta.restrict ι ⟶ Oa.restrict φ) (χb : Tb.restrict ι ⟶ Ob.restrict φ) (μ : tensor Oa Ob ⟶ Oab)

/-- The normal form of the local multiplication: restriction of the tensor product, the two chart
comparisons, then the multiplication `μ` on the chart. -/
def localMulNF : (tensor Ta Tb).restrict ι ⟶ Oab.restrict φ :=
  (restrictFunctor ι).map (tensorIsoTensorObj Ta Tb).hom ≫
    (restrictTensorObjIso ι Ta Tb).hom ≫
    CategoryTheory.MonoidalCategoryStruct.tensorHom χa χb ≫
    (restrictTensorObjIso φ Oa Ob).inv ≫
    (restrictFunctor φ).map ((tensorIsoTensorObj Oa Ob).inv ≫ μ)

theorem localMulNF_app (A : Y.Opens) (x : Γ(Ta, ι ''ᵁ A)) (y : Γ(Tb, ι ''ᵁ A)) :
    (localMulNF ι φ Ta Tb Oa Ob Oab χa χb μ).app A (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y) =
      μ.app (φ ''ᵁ A) (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (χa.app A x) (χb.app A y)) := by
  have e2 := restrictTensorObjIso_hom_app_tensorSections ι Ta Tb A x y
  have e3 : (CategoryTheory.MonoidalCategoryStruct.tensorHom χa χb).app A
      (tensorSections (Ta.restrict ι) (Tb.restrict ι) A x y) =
      tensorSections (Oa.restrict φ) (Ob.restrict φ) A (χa.app A x) (χb.app A y) :=
    tensorHom_tensorSections χa χb A x y
  have e4 := restrictTensorObjIso_inv_app_tensorSections φ Oa Ob A (χa.app A x) (χb.app A y)
  have e5 : ∀ (p : Oa.val.obj (Opposite.op (φ ''ᵁ A))) (q : Ob.val.obj (Opposite.op (φ ''ᵁ A))),
      ((tensorIsoTensorObj Oa Ob).inv ≫ μ).app (φ ''ᵁ A) (tensorSections Oa Ob (φ ''ᵁ A) p q) =
      μ.app (φ ''ᵁ A) (AlgebraicGeometry.Scheme.Modules.moduleTensorSection p q) := fun p q =>
    congrArg (μ.app (φ ''ᵁ A)) (tensorIsoTensorObj_inv_app_tensorSections Oa Ob (φ ''ᵁ A) p q)
  set w : Γ((tensor Ta Tb).restrict ι, A) := AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y with hw
  have e1 : ((restrictFunctor ι).map (tensorIsoTensorObj Ta Tb).hom).app A w =
      tensorSections Ta Tb (ι ''ᵁ A) x y := rfl
  unfold localMulNF
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [e1, e2, e3, e4]
  exact e5 _ _
end NF

section Shape
variable (T : ℤ → P.Modules) (O : ℤ → Z.Modules)
  (e : ∀ n : ℤ, (T n).restrict ι ≅ (pullback φ).obj (O n)) (a b : ℤ) (μ : tensor (O a) (O b) ⟶ O (a + b))

/-- The shape of `relativeProj.twistMulLocal` (its definition body with the families `T = twist S`,
`O = Proj.twist 𝒜`, `e = twistAffineIso S U` and the multiplication `μ = Proj.twistMul 𝒜 a b` as variables).
The `let loc` is kept so that, after zeta-reduction, the body is *syntactically* the body of `twistMulLocal`
(the kernel never has to unfold anything below `≫`; see `twistMulLocalShape_eq`). -/
def localMulShape : (tensor (T a) (T b)).restrict ι ⟶ (T (a + b)).restrict ι :=
  let loc : ∀ n : ℤ, (pullback ι).obj (T n) ≅ (pullback φ).obj (O n) :=
    fun n => ((restrictFunctorIsoPullback ι).app (T n)).symm ≪≫ e n
  (restrictFunctorIsoPullback ι).hom.app _ ≫
    (pullbackTensorIsoOpen ι (T a) (T b)).hom ≫
    (tensorIsoTensorObj _ _).hom ≫
    CategoryTheory.MonoidalCategoryStruct.tensorHom (loc a).hom (loc b).hom ≫
    (tensorIsoTensorObj _ _).inv ≫
    (pullbackTensorIsoOpen φ _ _).inv ≫
    (pullback φ).map μ ≫
    (e (a + b)).inv

theorem localMulShape_comp :
    localMulShape ι φ T O e a b μ ≫ (e (a + b)).hom ≫ (restrictFunctorIsoPullback φ).inv.app (O (a + b)) =
      localMulNF ι φ (T a) (T b) (O a) (O b) (O (a + b))
        ((e a).hom ≫ (restrictFunctorIsoPullback φ).inv.app (O a))
        ((e b).hom ≫ (restrictFunctorIsoPullback φ).inv.app (O b)) μ := by
  have hι : (restrictFunctorIsoPullback ι).hom.app (tensor (T a) (T b)) ≫
      (pullback ι).map (tensorIsoTensorObj (T a) (T b)).hom ≫
      (restrictFunctorIsoPullback ι).inv.app (CategoryTheory.MonoidalCategoryStruct.tensorObj (T a) (T b)) =
      (restrictFunctor ι).map (tensorIsoTensorObj (T a) (T b)).hom := by
    rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hφ : (restrictFunctorIsoPullback φ).hom.app (CategoryTheory.MonoidalCategoryStruct.tensorObj (O a) (O b)) ≫
      (pullback φ).map ((tensorIsoTensorObj (O a) (O b)).inv ≫ μ) ≫
      (restrictFunctorIsoPullback φ).inv.app (O (a + b)) =
      (restrictFunctor φ).map ((tensorIsoTensorObj (O a) (O b)).inv ≫ μ) := by
    rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  unfold localMulShape localMulNF pullbackTensorIsoOpen pullbackTensorObjIsoOpen
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorIso_inv, Iso.app_inv, Iso.app_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Functor.map_comp, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← hι, ← Functor.map_comp (restrictFunctor φ), ← hφ, Functor.map_comp]
  simp only [Category.assoc]

theorem localMulShape_app (A : Y.Opens) (x : Γ(T a, ι ''ᵁ A)) (y : Γ(T b, ι ''ᵁ A)) :
    ((e (a + b)).hom ≫ (restrictFunctorIsoPullback φ).inv.app (O (a + b))).app A
        ((localMulShape ι φ T O e a b μ).app A (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) =
      μ.app (φ ''ᵁ A) (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
        (((e a).hom ≫ (restrictFunctorIsoPullback φ).inv.app (O a)).app A x)
        (((e b).hom ≫ (restrictFunctorIsoPullback φ).inv.app (O b)).app A y)) := by
  have h := Hom.app_congr' (localMulShape_comp ι φ T O e a b μ) A (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)
  exact h.trans (localMulNF_app ι φ (T a) (T b) (O a) (O b) (O (a + b)) _ _ μ A x y)
end Shape

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- The definition body of `twistMulLocal S a b U`, with its three `Prop`-valued instance arguments
(`AddSubgroupClass` inside `Proj A(U)`, `IsOpenImmersion ι`, `IsOpenImmersion φ`) as explicit parameters.
Lean abstracts the nested proofs of a definition value into auxiliary lemmas `twistMulLocal._proof_i`, so the
body of `twistMulLocal` and a freshly elaborated copy differ exactly in these three proof terms; since the
differences sit below `≫` / `.app` / `.hom` (projection heads, for which the kernel never compares arguments
lazily) a direct `rfl` makes the kernel normalise `restrictFunctorIsoPullback` (> 60 s). Taking the proofs as
parameters lets unification supply the body's own spelling (`twistMulLocal_eq_shape`, structural), and the
change of spelling then happens under the regular head `localMulShape`, where the kernel uses proof irrelevance
argument by argument (`localMulShape_proof_irrel`). -/
def twistMulLocalShape (U : X.affineOpens) (a b : ℤ)
    (hA : AddSubgroupClass (AddSubgroup (S.sectionsRing U.1)) (S.sectionsRing U.1))
    (hι : AlgebraicGeometry.IsOpenImmersion ((relativeProj S).hom ⁻¹ᵁ U.1).ι)
    (hφ : @AlgebraicGeometry.IsOpenImmersion _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _)
      (@Iso.hom _ _ _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _) (affineIso S U))) :
    AlgebraicGeometry.Scheme.Modules.restrict
        (AlgebraicGeometry.Scheme.Modules.tensor (twist S a) (twist S b)) ((relativeProj S).hom ⁻¹ᵁ U.1).ι ⟶
      AlgebraicGeometry.Scheme.Modules.restrict (twist S (a + b)) ((relativeProj S).hom ⁻¹ᵁ U.1).ι :=
  let loc : ∀ n : ℤ, (AlgebraicGeometry.Scheme.Modules.pullback ((relativeProj S).hom ⁻¹ᵁ U.1).ι).obj (twist S n) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (@Iso.hom _ _ _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _) (affineIso S U))).obj
        (@AlgebraicGeometry.Proj.twist _ _ _ _ hA (S.sectionsGrading U.1) _ n) :=
    fun n => ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ((relativeProj S).hom ⁻¹ᵁ U.1).ι).app
      (twist S n)).symm ≪≫ twistAffineIso S U n
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ((relativeProj S).hom ⁻¹ᵁ U.1).ι).hom.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorIsoOpen ((relativeProj S).hom ⁻¹ᵁ U.1).ι (twist S a)
      (twist S b)).hom ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
    CategoryTheory.MonoidalCategoryStruct.tensorHom (loc a).hom (loc b).hom ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorIsoOpen
      (@Iso.hom _ _ _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _) (affineIso S U)) _ _).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback
      (@Iso.hom _ _ _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _) (affineIso S U))).map
      (@AlgebraicGeometry.Proj.twistMul _ _ _ _ hA (S.sectionsGrading U.1) _ a b) ≫
    @Iso.inv _ _ (AlgebraicGeometry.Scheme.Modules.restrict (twist S (a + b)) ((relativeProj S).hom ⁻¹ᵁ U.1).ι)
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (@Iso.hom _ _ _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _) (affineIso S U))).obj
        (@AlgebraicGeometry.Proj.twist _ _ _ _ hA (S.sectionsGrading U.1) _ (a + b)))
      (twistAffineIso S U (a + b))

/-- `twistMulLocalShape` is the instance of the generic shape `localMulShape` (both sides unfold to the same
term; checked structurally). -/
theorem twistMulLocalShape_eq (U : X.affineOpens) (a b : ℤ)
    (hA : AddSubgroupClass (AddSubgroup (S.sectionsRing U.1)) (S.sectionsRing U.1))
    (hι : AlgebraicGeometry.IsOpenImmersion ((relativeProj S).hom ⁻¹ᵁ U.1).ι)
    (hφ : @AlgebraicGeometry.IsOpenImmersion _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _)
      (@Iso.hom _ _ _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _) (affineIso S U))) :
    twistMulLocalShape S U a b hA hι hφ =
      @AlgebraicGeometry.Scheme.Modules.localMulShape _ _ _ ((relativeProj S).hom ⁻¹ᵁ U.1).ι hι
        (@Iso.hom _ _ _ (@AlgebraicGeometry.Proj _ _ _ _ hA (S.sectionsGrading U.1) _) (affineIso S U)) hφ
        (twist S) (@AlgebraicGeometry.Proj.twist _ _ _ _ hA (S.sectionsGrading U.1) _) (twistAffineIso S U) a b
        (@AlgebraicGeometry.Proj.twistMul _ _ _ _ hA (S.sectionsGrading U.1) _ a b) := rfl

/-- `twistMulLocal S a b U` is `localMulShape` applied to the chart data of `U` (Stacks 01NR, 01MO).
The proof first identifies `twistMulLocal` with `twistMulLocalShape` at the body's own instance proofs
(unification fills the three holes; the kernel compares structurally identical terms), then changes the three
proofs to the synthesized instances under the regular head `localMulShape` (proof irrelevance argument by
argument). -/
theorem twistMulLocal_eq_localMulShape (U : X.affineOpens) (a b : ℤ) :
    twistMulLocal S a b U =
      AlgebraicGeometry.Scheme.Modules.localMulShape ((relativeProj S).hom ⁻¹ᵁ U.1).ι (affineIso S U).hom (twist S)
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1)) (twistAffineIso S U) a b
        (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading U.1) a b) := by
  have h1 : twistMulLocal S a b U = twistMulLocalShape S U a b _ _ _ := rfl
  exact h1.trans ((twistMulLocalShape_eq S U a b _ _ _).trans rfl)

/-- **`twistMulLocal` on a pure tensor section, seen on the chart**:
for `A ⊆ π⁻¹U` and `x ∈ Γ(O(a), ι''A)`, `y ∈ Γ(O(b), ι''A)`,
`χ_{a+b}(twistMulLocal S a b U (x ⊗ y)) = Proj.twistMul A(U) a b (χ_a x ⊗ χ_b y)` in `Γ(O_U(a+b), e''A)`,
where `χ_n := (twistAffineIso S U n).hom ≫ (restrictFunctorIsoPullback e).inv.app O_U(n)` (Stacks 01NR, 01MO).

**Proof.** `twistMulLocal S a b U` is, by its definition, the composite
`rFIP(ι) ≫ pTIO(ι) ≫ tITO ≫ (loc a ⊗ loc b) ≫ tITO⁻¹ ≫ pTIO(e)⁻¹ ≫ e^*(Proj.twistMul) ≫ twistAffineIso(a+b)⁻¹`,
i.e. `localMulShape ι e (O(a)) (O(b)) (O(a+b)) (O_U(a)) (O_U(b)) (O_U(a+b)) (twistAffineIso a) (twistAffineIso b)
(twistAffineIso (a+b)) (Proj.twistMul a b)` above. `localMulShape_comp` puts it in normal form
`R_ι(tITO) ≫ rTOI(ι) ≫ (χ_a ⊗ χ_b) ≫ rTOI(e)⁻¹ ≫ R_e(tITO⁻¹ ≫ Proj.twistMul)` (iso cancellations, naturality of
`restrictFunctorIsoPullback`, `tensorHom_comp_tensorHom`), and `localMulNF_app` evaluates the normal form on
`x ⊗ y` factor by factor (`restrictTensorObjIso_{hom,inv}_app_tensorSections`, `tensorHom_tensorSections`,
`tensorIsoTensorObj_inv_app_tensorSections`). So the statement is `localMulShape_app` instantiated.

**Formalization.** `rw [twistMulLocal_eq_localMulShape]; exact localMulShape_app …`. The first
step is the only delicate one: `twistMulLocal S a b U` is identified with `twistMulLocalShape S U a b _ _ _` by `rfl`
(the three holes — the instance proofs that Lean abstracted into `twistMulLocal._proof_i` — are filled by unification
from the body, so the kernel compares structurally identical terms), and the proofs are then exchanged for the
synthesized instances under the regular head `localMulShape` (proof irrelevance argument by argument). A direct
`unfold twistMulLocal; exact localMulShape_app …` does not finish in the kernel (> 60 s): the proof terms differ under
projection heads, where the kernel normalises the whole `restrictFunctorIsoPullback` machinery. -/
theorem twistMulLocal_app_chart (U : X.affineOpens) (a b : ℤ)
    (A : ((relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens)
    (x : Γ(twist S a, ((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A))
    (y : Γ(twist S b, ((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)) :
    ((twistAffineIso S U (a + b)).hom ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (affineIso S U).hom).inv.app
          (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) (a + b))).app A
        ((twistMulLocal S a b U).app A (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) =
      (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading U.1) a b).app ((affineIso S U).hom ''ᵁ A)
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          (((twistAffineIso S U a).hom ≫
            (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (affineIso S U).hom).inv.app
              (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) a)).app A x)
          (((twistAffineIso S U b).hom ≫
            (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (affineIso S U).hom).inv.app
              (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) b)).app A y)) := by
  rw [twistMulLocal_eq_localMulShape S U a b]
  exact AlgebraicGeometry.Scheme.Modules.localMulShape_app ((relativeProj S).hom ⁻¹ᵁ U.1).ι (affineIso S U).hom
    (twist S) (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1)) (twistAffineIso S U) a b
    (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading U.1) a b) A x y

end AlgebraicGeometry.Scheme.relativeProj

/-- **`Proj.twistMul` on a pure tensor section is the pointwise product** (Stacks 01MO): `Proj.twistMul` is the
transpose of `twistMulPresheaf` under the sheafification adjunction, and `twistMulPresheaf` is `twistSectionMul` on
pure tensors (`tensorLift_tmul`). -/
theorem AlgebraicGeometry.Proj.twistMul_app_moduleTensorSection {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (a b : ℤ) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : Γ(AlgebraicGeometry.Proj.twist 𝒜 a, W)) (t : Γ(AlgebraicGeometry.Proj.twist 𝒜 b, W)) :
    (AlgebraicGeometry.Proj.twistMul 𝒜 a b).app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t) =
      AlgebraicGeometry.Proj.twistSectionMul 𝒜 a b W s t := by
  have h2 : ((PresheafOfModules.sheafificationAdjunction (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj)).homEquiv
      _ _) (AlgebraicGeometry.Proj.twistMul 𝒜 a b) = AlgebraicGeometry.Proj.twistMulPresheaf 𝒜 a b :=
    Equiv.apply_symm_apply _ _
  exact congrArg (fun k => k.app (op W) (s ⊗ₜ[Γ(AlgebraicGeometry.Proj 𝒜, W)] t)) h2

end
