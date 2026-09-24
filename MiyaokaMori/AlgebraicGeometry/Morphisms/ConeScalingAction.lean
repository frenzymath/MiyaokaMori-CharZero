import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ScalarActionOnCone
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.ScalarActionOnConeHomogeneousPullback
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ConeScalingActionIdealSheafOfSectionLeKer
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Fibrewise scalar action on the twisted affine cone

The fibrewise scalar action on the twisted affine cone `𝒵 ⊂ Tot(A^{⊕(N+1)})`: a unit `u` of the
sheaf of functions acts on morphisms into `𝒵` by multiplying every coordinate by `u`.
This is the scalar action on jets used in §3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The closed immersion `𝒵 ↪ Tot(A^{⊕(N+1)})` of the twisted affine cone: the `subschemeι` of the
ideal sheaf appearing in the definition of `twistedAffineCone`, given a name. -/

noncomputable def twistedAffineCone.ι {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    (twistedAffineCone A N deg F hF).left ⟶
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left :=
  (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
    (homogeneousEquationSection A N (F j) (hF j))).subschemeι

instance twistedAffineCone.isClosedImmersion_ι {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    AlgebraicGeometry.IsClosedImmersion (twistedAffineCone.ι A N deg F hF) :=
  inferInstanceAs (AlgebraicGeometry.IsClosedImmersion
    (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A N (F j) (hF j))).subschemeι)

/- Fibrewise scalar multiplication in terms of sections (general twisted affine cone): a morphism
   `g : W → 𝒵`, composed with `ι`, corresponds to a section `σ_g ∈ Γ(W, (g ≫ p)^*V)`
   (`totalSpaceHomEquiv`), and the inverse equivalence turns `u • σ_g` into a morphism `W → Tot(V)`.
   This morphism satisfies the cone equations (`F_j` is homogeneous, so
   `F_j(u • σ) = u^{deg F_j} • F_j(σ) = 0`), hence `ker ι ≤ ker`, and the universal property of the
   closed immersion (`IsClosedImmersion.lift`) brings it back into `𝒵`. -/

/-- The morphism `W → Tot(A^{⊕(N+1)})` corresponding to the rescaled section: `g ≫ ι` corresponds to
the section `σ_g`; take `u • σ_g` and apply the inverse of `totalSpaceHomEquiv`. -/

noncomputable def twistedAffineCone.scaleTot {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (twistedAffineCone A N deg F hF).left) :
    W ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left :=
  ((AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
      (CategoryTheory.Over.mk (g ≫ (twistedAffineCone A N deg F hF).hom))).symm
    ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
      AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
        (CategoryTheory.Over.mk (g ≫ (twistedAffineCone A N deg F hF).hom))
        (CategoryTheory.Over.homMk (g ≫ twistedAffineCone.ι A N deg F hF)
          (CategoryTheory.Category.assoc _ _ _)))).left

/-- Homogeneity of a monomial: the monomial `f_{g 0} ⊗ ⋯ ⊗ f_{g (e-1)}` evaluated at `a • f` equals
`a^e` times its value at `f`. Proof by induction on `e`, using `AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul`
(`(a • s) ⊗ (b • t) = (a b) • (s ⊗ t)`) at each level. -/
theorem evalHomogeneousAtSections.monomial_smul {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) {N : ℕ}
    (a : Γ(X, ⊤)) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) (e : ℕ) (g : Fin e → Fin (N + 1)) :
    evalHomogeneousAtSections.monomial A (fun i => (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • f i) e g
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a ^ e) • evalHomogeneousAtSections.monomial A f e g := by
  induction e with
  | zero =>
    simp only [evalHomogeneousAtSections.monomial, pow_zero]
    exact (one_smul _ _).symm
  | succ e ih =>
    simp only [evalHomogeneousAtSections.monomial]
    rw [ih (fun i => g i.castSucc), pow_succ]
    exact AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul (U := ⊤) _ _ _ _

/-- Homogeneity: if `F` is homogeneous of degree `e`, then `F(a • f_0, …, a • f_N) = a^e • F(f_0, …, f_N)`.
Proof: apply `evalHomogeneousAtSections.monomial_smul` to every monomial, pull `a^e` out of the finite
sum (`Finset.smul_sum`), and commute it with the scalar multiplication by the coefficients. -/
theorem evalHomogeneousAtSections_smul {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : X.Modules) [A.IsLineBundle]
    {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    (a : Γ(X, ⊤)) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    evalHomogeneousAtSections A F hF (fun i => (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • f i)
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a ^ e) • evalHomogeneousAtSections A F hF f := by
  have hcomm : ∀ (c : Γ(X, ⊤)) (m : ((AlgebraicGeometry.Scheme.Modules.tensorPow A e).val.obj (Opposite.op ⊤) : Type u)),
      (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) • ((show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a ^ e) • m)
        = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a ^ e) • ((show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) • m) := by
    intro c m
    rw [smul_smul, smul_smul]
    congr 1
    exact mul_comm c (a ^ e)
  unfold evalHomogeneousAtSections
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [evalHomogeneousAtSections.monomial_smul, hcomm]

/-- General lemma: let `m` be an `X`-morphism from `T` to `Tot(V)`, with corresponding section `σ_m`.
The morphism corresponding to the rescaled section `a • σ_m`, precomposed with `j : W → T.left`, is the
underlying morphism of the one corresponding to the section `j^♯(a) • σ_{j ≫ m}` over `W` (with base
`t = j ≫ T.hom`).
Proof: `totalSpaceHomEquiv_symm_naturality` (precomposition with `j` is pulling the section back along
`j` followed by `pullbackComp`), `sectionPullbackAlong_smul` (`j^*(a • s) = j^♯(a) • j^*s`),
linearity of `pullbackComp` on `⊤` (`map_smul`), and `totalSpaceHomEquiv_naturality`, which identifies
`pullbackComp (j^* σ_m)` with `σ_{j ≫ m}`.
The parameters `t`, `m'`, `b` with the equations `ht`, `hm'`, `hb` only make the syntactic shape of the
conclusion match the call sites (they disappear after `subst`). -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_symm_smul_comp_left {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    {W : AlgebraicGeometry.Scheme.{u}} (j : W ⟶ T.left) (a : Γ(T.left, ⊤))
    (m : T ⟶ AlgebraicGeometry.Scheme.totalSpace V)
    (t : W ⟶ X) (ht : j ≫ T.hom = t)
    (m' : W ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left) (hm' : j ≫ m.left = m')
    (hw : m' ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = t)
    (b : Γ(W, ⊤)) (hb : j.appTop a = b) :
    j ≫ ((AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T).symm
        ((show T.left.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
          AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m)).left
      = ((AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk t)).symm
          ((show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from b) •
            AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk t)
              (CategoryTheory.Over.homMk m' hw))).left := by
  subst ht hm' hb
  have h1 : (CategoryTheory.Over.homMk (j ≫ m.left) hw :
        CategoryTheory.Over.mk (j ≫ T.hom) ⟶ AlgebraicGeometry.Scheme.totalSpace V)
      = (CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m :=
    CategoryTheory.Over.OverMorphism.ext rfl
  rw [h1]
  change ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T).symm
      ((show T.left.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
        AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m)).left = _
  rw [← AlgebraicGeometry.Scheme.totalSpaceHomEquiv_symm_naturality, sectionPullbackAlong_smul, map_smul,
    ← AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality]

/-- `g_u = scaleTot u g` coincides with `(λu, g) ≫ (λ · z)`: apply `totalSpaceHomEquiv_symm_smul_comp_left`
with `T = Over.mk (P → C)`, `j = pullback.lift λu g`, `a` the coordinate `λ` and `m = pr₂ ≫ ι`; then
`j ≫ pr₂ = g` (`pullback.lift_snd`) and `j^♯(λ) = λu^♯(λ) = u` (`pullback.lift_fst`,
`Scheme.comp_appTop`, `hu`). -/
theorem twistedAffineCone.scaleTot_eq_lift_comp_scaledTot {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (twistedAffineCone A N deg F hF).left)
    (lamu : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)))
    (hlam : lamu ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
          AlgebraicGeometry.Spec (CommRingCat.of k))
        = g ≫ (twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hu : lamu.appTop ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv
          Polynomial.X) = (u : Γ(W, ⊤))) :
    twistedAffineCone.scaleTot A N deg F hF u g
      = CategoryTheory.Limits.pullback.lift lamu g hlam ≫ coneScalarAction.scaledTot A N deg F hF := by
  have hsnd : CategoryTheory.Limits.pullback.lift lamu g hlam ≫ CategoryTheory.Limits.pullback.snd _ _ = g :=
    CategoryTheory.Limits.pullback.lift_snd _ _ _
  have hfst : CategoryTheory.Limits.pullback.lift lamu g hlam ≫ CategoryTheory.Limits.pullback.fst _ _ = lamu :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hu' : (CategoryTheory.Limits.pullback.lift lamu g hlam).appTop
      ((CategoryTheory.Limits.pullback.fst
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X))
      = (u : Γ(W, ⊤)) := by
    have h1 : (CategoryTheory.Limits.pullback.lift lamu g hlam ≫ CategoryTheory.Limits.pullback.fst
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X)
        = (CategoryTheory.Limits.pullback.lift lamu g hlam).appTop
          ((CategoryTheory.Limits.pullback.fst
            (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop
            ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X)) := rfl
    rw [← h1, hfst]
    exact hu
  have key := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_symm_smul_comp_left
    (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
    (CategoryTheory.Over.mk (coneScalarAction.toBase A N deg F hF))
    (CategoryTheory.Limits.pullback.lift lamu g hlam)
    ((CategoryTheory.Limits.pullback.fst
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X))
    (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _ ≫
        (coneScalarAction.ideal A N deg F hF).subschemeι) (coneScalarAction.point_compat A N deg F hF))
    (g ≫ (twistedAffineCone A N deg F hF).hom)
    (by
      change CategoryTheory.Limits.pullback.lift lamu g hlam ≫
        (CategoryTheory.Limits.pullback.snd _ _ ≫ (twistedAffineCone A N deg F hF).hom) = _
      rw [← CategoryTheory.Category.assoc, hsnd])
    (g ≫ twistedAffineCone.ι A N deg F hF)
    (calc CategoryTheory.Limits.pullback.lift lamu g hlam ≫
          (CategoryTheory.Limits.pullback.snd _ _ ≫ (coneScalarAction.ideal A N deg F hF).subschemeι)
        = (CategoryTheory.Limits.pullback.lift lamu g hlam ≫ CategoryTheory.Limits.pullback.snd _ _) ≫
            (coneScalarAction.ideal A N deg F hF).subschemeι := (CategoryTheory.Category.assoc _ _ _).symm
      _ = g ≫ twistedAffineCone.ι A N deg F hF :=
            congrArg (fun φ => φ ≫ (coneScalarAction.ideal A N deg F hF).subschemeι) hsnd)
    (CategoryTheory.Category.assoc _ _ _) (u : Γ(W, ⊤)) hu'
  exact key.symm

/-- Given a `k`-structure `s : W → Spec k` and a global function `u ∈ Γ(W, O_W)`, the `k`-morphism
`λu : W → Spec k[λ]` to the affine line whose coordinate is `u`. Under the `Γ`–`Spec` adjunction
(Mathlib's `ΓSpec.adjunction`) it corresponds to the ring homomorphism `k[λ] → Γ(W, ⊤)`, `λ ↦ u`,
with `k` acting through `s` (`Polynomial.eval₂RingHom`):
`λu := W.toSpecΓ ≫ Spec.map (eval₂ ρ u)` where `ρ := (ΓSpecIso k).inv ≫ s.appTop`. -/
noncomputable def AlgebraicGeometry.Scheme.unitToAffineLine {k : Type u} [CommRing k]
    {W : AlgebraicGeometry.Scheme.{u}} (s : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (u : Γ(W, ⊤)) : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) :=
  W.toSpecΓ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom u))

/-- `λu` is a `k`-morphism: `λu ≫ (Spec k[λ] ↘ Spec k) = s`. The structure morphism is
`Spec (k → k[λ])` (`specOverSpec_over`), `(eval₂ ρ u) ∘ (k → k[λ]) = ρ` (`Polynomial.eval₂_C`), and
by `toSpecΓ_naturality` and `toSpecΓ_SpecMap_ΓSpecIso_inv`,
`W.toSpecΓ ≫ Spec.map s.appTop ≫ Spec.map (ΓSpecIso k).inv = s`. -/
theorem AlgebraicGeometry.Scheme.unitToAffineLine_comp_over {k : Type u} [CommRing k]
    {W : AlgebraicGeometry.Scheme.{u}} (s : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (u : Γ(W, ⊤)) :
    AlgebraicGeometry.Scheme.unitToAffineLine s u ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = s := by
  unfold AlgebraicGeometry.Scheme.unitToAffineLine
  rw [AlgebraicGeometry.specOverSpec_over, CategoryTheory.Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (Polynomial.eval₂RingHom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom u).comp
        (algebraMap k (Polynomial k))
      = ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply, Polynomial.eval₂_C]
  rw [h, CommRingCat.ofHom_hom, AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Scheme.toSpecΓ_naturality_assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, CategoryTheory.Category.comp_id]

/-- `λu` pulls the coordinate `λ` back to `u`: `(λu)^♯(λ) = u`. Use `Hom.comp_appTop`,
`ΓSpecIso_inv_naturality` (which transports `(Spec.map φ)^♯` to `φ`), `toSpecΓ_appTop`
(`W.toSpecΓ^♯ = (ΓSpecIso Γ(W, ⊤)).hom`), and finally `(eval₂ ρ u)(λ) = u` (`Polynomial.eval₂_X`). -/
theorem AlgebraicGeometry.Scheme.unitToAffineLine_appTop_X {k : Type u} [CommRing k]
    {W : AlgebraicGeometry.Scheme.{u}} (s : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (u : Γ(W, ⊤)) :
    (AlgebraicGeometry.Scheme.unitToAffineLine s u).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X) = u := by
  unfold AlgebraicGeometry.Scheme.unitToAffineLine
  set φ : CommRingCat.of (Polynomial k) ⟶ Γ(W, ⊤) := CommRingCat.ofHom (Polynomial.eval₂RingHom
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom u) with hφ
  have h1 : (AlgebraicGeometry.Spec.map φ).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X)
      = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(W, ⊤)).inv (φ Polynomial.X) := by
    have h := CategoryTheory.ConcreteCategory.congr_hom
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality φ) (Polynomial.X : Polynomial k)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact h.symm
  rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h1,
    AlgebraicGeometry.Scheme.toSpecΓ_appTop, CategoryTheory.Iso.inv_hom_id_apply, hφ]
  simp only [CommRingCat.hom_ofHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- The rescaled morphism `g_u = scaleTot u g` composed with `Tot(V) → C` equals `g ≫ p_𝒵`: `g_u` is the
underlying morphism of a `C`-morphism from `Over.mk (g ≫ p_𝒵)` to `Tot(V)`, so this is `Over.w`. -/
theorem twistedAffineCone.scaleTot_comp_hom {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (twistedAffineCone A N deg F hF).left) :
    twistedAffineCone.scaleTot A N deg F hF u g ≫
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom =
      g ≫ (twistedAffineCone A N deg F hF).hom :=
  CategoryTheory.Over.w _

/-- The rescaled morphism `g_u := scaleTot u g : W → Tot(V)` (with `V = A^{⊕(N+1)}`) still factors
through the cone: `ker ι ≤ ker g_u`.

Proof: `ker ι = ⨆_j I_j` (Mathlib's `IdealSheafData.ker_subschemeι`, where
`I_j := idealSheafOfSection (F_j(τ))` and `ι` is by definition `(⨆_j I_j).subschemeι`), so it suffices to
show `I_j ≤ ker g_u` for every `j`; by the criterion `idealSheafOfSection_le_ker_iff` this means
`g_u^* F_j(τ) = 0`. Now `g_u` and `g ≫ ι` live over the same `C`-structure `b := g ≫ p_𝒵`
(`scaleTot_comp_hom` and associativity), and `Over.homMk g_u` is by definition
`(totalSpaceHomEquiv V (Over.mk b))⁻¹ (u • σ_g)` (`Over.OverMorphism.ext rfl`), so each of its
coordinates is `u` times the corresponding coordinate of `σ_g`
(`totalSpaceHomEquiv_symm_smul_coordinate`). Moreover `(g ≫ ι)^* F_j(τ) = 0`, since
`I_j ≤ ⨆_j I_j = ker ι ≤ ker (g ≫ ι)` (`le_iSup`, `ker_subschemeι`, Mathlib's `Hom.le_ker_comp`) and
the same criterion. The homogeneity lemma
`homogeneousEquationSection_pullback_eq_zero_of_coordinates_smul` (`F_j` homogeneous, so
`F_j(u • σ) = u^{deg j} • F_j(σ)`, with the coordinates transported along `pullbackComp` /
`pullbackCongr`) then gives `g_u^* F_j(τ) = 0`.

An alternative route reduces to the universal case, `g_u = (λu, g) ≫ scaledTot` (`unitToAffineLine`,
`scaleTot_eq_lift_comp_scaledTot`), and then uses `coneScalarAction.ideal_le_ker_scaledTot`; the direct
argument above avoids the universal scalar action. -/
theorem twistedAffineCone.ker_ι_le_ker_scaleTot {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (twistedAffineCone A N deg F hF).left) :
    (twistedAffineCone.ι A N deg F hF).ker ≤ (twistedAffineCone.scaleTot A N deg F hF u g).ker := by
  change (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
    (homogeneousEquationSection A N (F j) (hF j))).subschemeι.ker ≤ _
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
  refine iSup_le fun j => ?_
  rw [AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff]
  have hb₀ : (g ≫ twistedAffineCone.ι A N deg F hF) ≫
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom
      = g ≫ (twistedAffineCone A N deg F hF).hom := CategoryTheory.Category.assoc _ _ _
  refine homogeneousEquationSection_pullback_eq_zero_of_coordinates_smul A N (F j) (hF j)
    (g ≫ (twistedAffineCone A N deg F hF).hom) (g ≫ twistedAffineCone.ι A N deg F hF)
    (twistedAffineCone.scaleTot A N deg F hF u g) hb₀
    (twistedAffineCone.scaleTot_comp_hom A N deg F hF u g) (u : Γ(W, ⊤)) ?_ ?_
  · intro i
    have hmk : (CategoryTheory.Over.homMk (twistedAffineCone.scaleTot A N deg F hF u g)
          (twistedAffineCone.scaleTot_comp_hom A N deg F hF u g) :
          CategoryTheory.Over.mk (g ≫ (twistedAffineCone A N deg F hF).hom) ⟶
            AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
        = (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
            (CategoryTheory.Over.mk (g ≫ (twistedAffineCone A N deg F hF).hom))).symm
          ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
            AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
              (CategoryTheory.Over.mk (g ≫ (twistedAffineCone A N deg F hF).hom))
              (CategoryTheory.Over.homMk (g ≫ twistedAffineCone.ι A N deg F hF)
                (CategoryTheory.Category.assoc _ _ _))) :=
      CategoryTheory.Over.OverMorphism.ext rfl
    rw [hmk]
    exact AlgebraicGeometry.Scheme.totalSpaceHomEquiv_symm_smul_coordinate (fun _ : Fin (N + 1) => A)
      (CategoryTheory.Over.mk (g ≫ (twistedAffineCone A N deg F hF).hom)) (u : Γ(W, ⊤)) _ i
  · rw [← AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff]
    calc AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (F j) (hF j))
        ≤ ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (F j) (hF j)) :=
          le_iSup (fun j => AlgebraicGeometry.Scheme.idealSheafOfSection _
            (homogeneousEquationSection A N (F j) (hF j))) j
      _ = (twistedAffineCone.ι A N deg F hF).ker :=
          (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _).symm
      _ ≤ (g ≫ twistedAffineCone.ι A N deg F hF).ker := AlgebraicGeometry.Scheme.Hom.le_ker_comp _ _

/-- Fibrewise scalar multiplication of a morphism `g : W → 𝒵` by a unit `u ∈ Γ(W, O_W)ˣ`: the lift of
`scaleTot u g` along the closed immersion `ι` (`IsClosedImmersion.lift`), which exists by
`ker_ι_le_ker_scaleTot`. -/
noncomputable def twistedAffineCone.scale {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (twistedAffineCone A N deg F hF).left) : W ⟶ (twistedAffineCone A N deg F hF).left :=
  AlgebraicGeometry.IsClosedImmersion.lift (twistedAffineCone.ι A N deg F hF)
    (twistedAffineCone.scaleTot A N deg F hF u g)
    (twistedAffineCone.ker_ι_le_ker_scaleTot A N deg F hF u g)

/-- `scale u g` composed with `ι` is `g_u` (`lift_fac` for the lift along a closed immersion). -/
theorem twistedAffineCone.scale_comp_ι {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (twistedAffineCone A N deg F hF).left) :
    twistedAffineCone.scale A N deg F hF u g ≫ twistedAffineCone.ι A N deg F hF =
      twistedAffineCone.scaleTot A N deg F hF u g :=
  AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _

/-- Scalar multiplication is compatible with the projection to `C` (the general form of `scale_proj`):
`p_𝒵 = ι ≫ p_{Tot}`, `scale u g ≫ ι = g_u` (`scale_comp_ι`), and `g_u ≫ p_{Tot} = g ≫ p_𝒵`
(`scaleTot_comp_hom`). -/
theorem twistedAffineCone.scale_comp_hom {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (twistedAffineCone A N deg F hF).left) :
    twistedAffineCone.scale A N deg F hF u g ≫ (twistedAffineCone A N deg F hF).hom =
      g ≫ (twistedAffineCone A N deg F hF).hom := by
  change twistedAffineCone.scale A N deg F hF u g ≫ (twistedAffineCone.ι A N deg F hF ≫
    (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom) = _
  rw [← CategoryTheory.Category.assoc, twistedAffineCone.scale_comp_ι]
  exact twistedAffineCone.scaleTot_comp_hom A N deg F hF u g

/-- For `u = 1` we have `g_1 = g ≫ ι`: `1 • σ_g = σ_g`, then `totalSpaceHomEquiv` and its inverse cancel. -/
theorem twistedAffineCone.scaleTot_one {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ (twistedAffineCone A N deg F hF).left) :
    twistedAffineCone.scaleTot A N deg F hF 1 g = g ≫ twistedAffineCone.ι A N deg F hF := by
  unfold twistedAffineCone.scaleTot
  simp only [Units.val_one]
  erw [one_smul, Equiv.symm_apply_apply]
  rfl

/-- Scalar multiplication by `1` is the identity (the general form of `scale_one`): both sides composed
with the monomorphism `ι` equal `g ≫ ι`. -/
theorem twistedAffineCone.scale_one {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ (twistedAffineCone A N deg F hF).left) :
    twistedAffineCone.scale A N deg F hF 1 g = g := by
  rw [← CategoryTheory.cancel_mono (twistedAffineCone.ι A N deg F hF), twistedAffineCone.scale_comp_ι]
  exact twistedAffineCone.scaleTot_one A N deg F hF g

/-- The fibrewise scalar action on the twisted cone `MMSetup.cone f` of the Miyaoka–Mori setting:
`twistedAffineCone.scale` for the seed line bundle and the defining equations of `X`. -/
noncomputable def TwistedCone.scale {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (MMSetup.cone f).left) : W ⟶ (MMSetup.cone f).left :=
  twistedAffineCone.scale (seedLineBundle X.embedding f) X.embDim D.E.deg D.E.F D.E.homogeneous u g

theorem TwistedCone.scale_proj {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) [MMSetup f]
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ) (g : W ⟶ (MMSetup.cone f).left) :
    TwistedCone.scale f u g ≫ (MMSetup.cone f).hom = g ≫ (MMSetup.cone f).hom :=
  twistedAffineCone.scale_comp_hom _ _ _ _ _ u g

theorem TwistedCone.scale_one {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) [MMSetup f]
    {W : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ (MMSetup.cone f).left) :
    TwistedCone.scale f 1 g = g :=
  twistedAffineCone.scale_one _ _ _ _ _ g

/-- Relation between `scale` and `coneScalarAction` on a general twisted affine cone: compose both sides
with the monomorphism `ι`; the left side becomes `g_u` (`scale_comp_ι`), the right side
`(λu, g) ≫ (λ · z)` (`coneScalarAction ≫ ι = toImage ≫ imageι = λ · z`), and these agree by
`scaleTot_eq_lift_comp_scaledTot`. -/
theorem twistedAffineCone.scale_eq_lift_comp_coneScalarAction {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ)
    (g : W ⟶ (twistedAffineCone A N deg F hF).left)
    (lamu : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)))
    (hlam : lamu ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
          AlgebraicGeometry.Spec (CommRingCat.of k))
        = g ≫ (twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hu : lamu.appTop ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv
          Polynomial.X) = (u : Γ(W, ⊤))) :
    twistedAffineCone.scale A N deg F hF u g
      = CategoryTheory.Limits.pullback.lift lamu g hlam ≫ coneScalarAction A N deg F hF := by
  rw [← CategoryTheory.cancel_mono (twistedAffineCone.ι A N deg F hF), twistedAffineCone.scale_comp_ι,
    CategoryTheory.Category.assoc]
  have h : coneScalarAction A N deg F hF ≫ twistedAffineCone.ι A N deg F hF =
      coneScalarAction.scaledTot A N deg F hF :=
    calc coneScalarAction A N deg F hF ≫ twistedAffineCone.ι A N deg F hF
        = (coneScalarAction.scaledTot A N deg F hF).toImage ≫
            (AlgebraicGeometry.Scheme.IdealSheafData.inclusion
              (coneScalarAction.ideal_le_ker_scaledTot A N deg F hF) ≫
              (coneScalarAction.ideal A N deg F hF).subschemeι) := CategoryTheory.Category.assoc _ _ _
      _ = (coneScalarAction.scaledTot A N deg F hF).toImage ≫
            (coneScalarAction.scaledTot A N deg F hF).ker.subschemeι := by
          rw [AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι]
      _ = coneScalarAction.scaledTot A N deg F hF := AlgebraicGeometry.Scheme.Hom.toImage_imageι _
  rw [h]
  exact twistedAffineCone.scaleTot_eq_lift_comp_scaledTot A N deg F hF u g lamu hlam hu

/-- Relation with the universal scalar action `coneScalarAction` on the cone: give `W` the `k`-structure
through `g`, and let `lamu : W → A¹_k = Spec k[λ]` be the `k`-morphism with coordinate `u`; then
`scale f u g` is `(lamu, g)` followed by the scalar action. -/

theorem TwistedCone.scale_eq_coneScalarAction {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    {W : AlgebraicGeometry.Scheme.{u}} (u : Γ(W, ⊤)ˣ) (g : W ⟶ (MMSetup.cone f).left)
    (lamu : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)))
    (hlam : lamu ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
          AlgebraicGeometry.Spec (CommRingCat.of k))
        = g ≫ (MMSetup.cone f).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hu : lamu.appTop ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv
          Polynomial.X) = (u : Γ(W, ⊤))) :
    TwistedCone.scale f u g
      = CategoryTheory.Limits.pullback.lift lamu g hlam
          ≫ coneScalarAction (seedLineBundle X.embedding f) X.embDim D.E.deg D.E.F D.E.homogeneous :=
  twistedAffineCone.scale_eq_lift_comp_coneScalarAction _ _ _ _ _ u g lamu hlam hu

end
