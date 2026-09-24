import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyTransport
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # Assembly of the twist families on a piece of `relativeProj.lift`, part 1: the key identities

Companion of `RelativeProjLiftEvaluationTwistFamily.lean`, which imports this file. Contents:
* section bookkeeping at the variable level (restrictions between equal opens, section maps of morphisms out of a
  restriction, `unitSectionsToRing` rules, iso/inverse on sections);
* **working copies** `evalHomAux`, `dataHomAux`, `twistMulHomAux`, `IsTwistFamilyOnAux` of `LiftData.evalHom`,
  `dataHom`, `twistMulHom`, `IsTwistFamilyOn` (same terms; the originals live in the importing module, which cannot be
  imported here; the importing module converts by `exact`);
* the dictionary leaves of the Transport module restated with the `Aux` morphisms (`rfl`);
* `familyOfAbs`: the relative family `ψ_n := Θ_n ≫ χ_n ≫ Λ_n⁻¹` attached to an absolute twist family `χ`
  (`Proj.TwistFamily`), and the key identity `keyM` (multiplicativity) behind `IsTwistFamilyOnAux` for it; the other
  key identity `keyF` and the existence theorem are in `RelativeProjLiftEvaluationTwistFamilyAssemblyExists.lean`,
  the uniqueness theorem in `RelativeProjLiftEvaluationTwistFamilyAssemblyUnique.lean` (split for compile time). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-! ## Section bookkeeping (variable level) -/

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- Restricting back and forth between two opens that contain each other is the identity. -/
theorem presheaf_map_map_self (N : X.Modules) {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) (x : Γ(N, U)) :
    N.presheaf.map (homOfLE h).op (N.presheaf.map (homOfLE h').op x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have e : (homOfLE h').op ≫ (homOfLE h).op = 𝟙 (op U) := Subsingleton.elim _ _
  rw [e, CategoryTheory.Functor.map_id]
  rfl

/-- Restriction between two opens that contain each other is injective. -/
theorem presheaf_map_injective_of_le_le (N : X.Modules) {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    Function.Injective (N.presheaf.map (homOfLE h).op) := fun a b hab => by
  have := congrArg (N.presheaf.map (homOfLE h').op) hab
  rwa [presheaf_map_map_self N h' h, presheaf_map_map_self N h' h] at this

/-- A morphism out of a restriction is semilinear for the ambient scalars: `φ(r • x) = ι^♯(r) • φ(x)`. -/
theorem restrict_hom_app_smul_appIso (ι : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion ι] {M : X.Modules}
    {P : Y.Modules} (φ : M.restrict ι ⟶ P) (A' : Y.Opens) (r : Γ(X, ι ''ᵁ A')) (x : Γ(M, ι ''ᵁ A')) :
    φ.app A' (show Γ(M.restrict ι, A') from r • x) = ((ι.appIso A').hom r) • φ.app A' x := by
  rw [restrict_smul_eq ι M A' r x]
  exact Hom.app_smul φ _ _

/-- A morphism out of a restriction commutes with restriction, written with the ambient opens. -/
theorem restrict_hom_app_map (ι : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion ι] {M : X.Modules}
    {P : Y.Modules} (φ : M.restrict ι ⟶ P) {A' B' : Y.Opens} (h : B' ≤ A') (hB : ι ''ᵁ B' ≤ ι ''ᵁ A')
    (x : Γ(M, ι ''ᵁ A')) :
    φ.app B' (show Γ(M.restrict ι, B') from M.presheaf.map (homOfLE hB).op x) =
      P.presheaf.map (homOfLE h).op (φ.app A' x) := by
  have := hom_app_presheaf_map φ h x
  rw [restrict_map] at this
  have e : ι.opensFunctor.map (homOfLE h) = homOfLE hB := Subsingleton.elim _ _
  rw [e] at this
  exact this

/-- `unitSectionsToRing` is the identity, hence additive. -/
theorem unitSectionsToRing_add (B : Y.Opens) (a b : Γ(SheafOfModules.unit Y.ringCatSheaf, B)) :
    unitSectionsToRing Y B (a + b) = unitSectionsToRing Y B a + unitSectionsToRing Y B b := rfl

/-- On the unit sheaf, scalar multiplication is multiplication. -/
theorem unitSectionsToRing_smul (B : Y.Opens) (r : Γ(Y, B)) (a : Γ(SheafOfModules.unit Y.ringCatSheaf, B)) :
    unitSectionsToRing Y B (r • a) = r * unitSectionsToRing Y B a :=
  smul_eq_mul r a

/-- `unitSectionsToRing` commutes with restriction. -/
theorem unitSectionsToRing_map {B B' : Y.Opens} (h : B' ≤ B) (a : Γ(SheafOfModules.unit Y.ringCatSheaf, B)) :
    unitSectionsToRing Y B' ((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit Y.ringCatSheaf)).map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE h).op (unitSectionsToRing Y B a) := rfl

theorem unitSectionsToRing_zero (B : Y.Opens) :
    unitSectionsToRing Y B (0 : Γ(SheafOfModules.unit Y.ringCatSheaf, B)) = 0 := rfl



/-- `tensorSections` commutes with restriction (spelled with `presheaf.map`). -/
theorem tensorSections_map' (A B : X.Modules) {U V : X.Opens} (h : V ≤ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B).presheaf.map (homOfLE h).op
        (tensorSections A B U a b) =
      tensorSections A B V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) :=
  tensorSections_restrict A B (homOfLE h) a b


/-- `(φ ≫ ψ).app U x = ψ.app U (φ.app U x)` (`rfl`, for rewriting). -/
theorem comp_app_apply_tfa {A B C : X.Modules} (φ : A ⟶ B) (ψ : B ⟶ C) (U : X.Opens) (x : Γ(A, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

/-- Additivity of a morphism out of a restriction, with the ambient addition. -/
theorem restrict_hom_app_add (ι : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion ι] {M : X.Modules}
    {P : Y.Modules} (φ : M.restrict ι ⟶ P) (A' : Y.Opens) (x y : Γ(M, ι ''ᵁ A')) :
    φ.app A' (show Γ(M.restrict ι, A') from x + y) = φ.app A' x + φ.app A' y :=
  (φ.app A').hom.map_add x y

/-- A morphism out of a restriction kills zero (ambient zero). -/
theorem restrict_hom_app_zero (ι : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion ι] {M : X.Modules}
    {P : Y.Modules} (φ : M.restrict ι ⟶ P) (A' : Y.Opens) :
    φ.app A' (show Γ(M.restrict ι, A') from (0 : Γ(M, ι ''ᵁ A'))) = 0 :=
  (φ.app A').hom.map_zero

/-- Restricting `sectionMapOfRestrictHom φ A hA z` back to `W.ι ''ᵁ W.ι ⁻¹ᵁ A` gives `φ.app (W.ι ⁻¹ᵁ A)` of the
restriction of `z`. -/
theorem presheaf_map_sectionMapOfRestrictHom {M N : X.Modules} {W : X.Opens}
    (φ : M.restrict W.ι ⟶ N.restrict W.ι) (A : X.Opens) (hA : A ≤ W)
    (hA' : W.ι ''ᵁ W.ι ⁻¹ᵁ A ≤ A) (hA'' : A ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ A) (z : Γ(M, A)) :
    N.presheaf.map (homOfLE hA').op (sectionMapOfRestrictHom φ A hA z) =
      φ.app (W.ι ⁻¹ᵁ A) (M.presheaf.map (homOfLE hA').op z) :=
  presheaf_map_map_self N hA' hA'' _


/-- Additivity of the section map of a morphism of modules. -/
theorem hom_app_add {A B : X.Modules} (φ : A ⟶ B) (U : X.Opens) (x y : Γ(A, U)) :
    φ.app U (x + y) = φ.app U x + φ.app U y :=
  (φ.app U).hom.map_add x y

/-- The section map of a morphism of modules kills zero. -/
theorem hom_app_zero {A B : X.Modules} (φ : A ⟶ B) (U : X.Opens) : φ.app U (0 : Γ(A, U)) = 0 :=
  (φ.app U).hom.map_zero

/-- `e.inv (e.hom x) = x` on sections, for an isomorphism of modules. -/
theorem iso_inv_app_hom_app_tfa {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    e.inv.app U (e.hom.app U x) = x := by
  change (e.hom.app U ≫ e.inv.app U) x = x
  rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app]
  rfl

/-- `e.hom (e.inv y) = y` on sections, for an isomorphism of modules. -/
theorem iso_hom_app_inv_app {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (y : Γ(N, U)) :
    e.hom.app U (e.inv.app U y) = y := by
  change (e.inv.app U ≫ e.hom.app U) y = y
  rw [← Hom.comp_app, e.inv_hom_id, Hom.id_app]
  rfl

/-- `φ ((inv φ) y) = y` on sections, for an isomorphism `φ` of modules. -/
theorem isIso_app_inv_app {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (U : X.Opens) (y : Γ(N, U)) :
    φ.app U ((CategoryTheory.inv φ).app U y) = y := by
  change ((CategoryTheory.inv φ).app U ≫ φ.app U) y = y
  rw [← Hom.comp_app, IsIso.inv_hom_id, Hom.id_app]
  rfl

/-- `e.hom (e.inv r) = r` for an isomorphism of commutative rings (e.g. `f.appIso U`). -/
theorem _root_.CommRingCat.iso_hom_inv_apply {R S : CommRingCat.{u}} (e : R ≅ S) (r : S) :
    e.hom (e.inv r) = r := by
  rw [← CommRingCat.comp_apply, e.inv_hom_id]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T : AlgebraicGeometry.Scheme.{u}}

namespace LiftData

variable {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules} [M.IsLineBundle]
  (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)

/- `Λ_n = powTriv … n` is an isomorphism (`isIso_powTriv`); registered as a local instance so that `inv (powTriv …)`
elaborates uniformly (no global instance is added). -/
attribute [local instance] AlgebraicGeometry.Scheme.relativeProj.isIso_powTriv

/-- **Working copy** of `LiftData.evalHom` (`RelativeProjLiftEvaluationTwistFamily.lean`), definitionally equal to it
(same term). Needed here because that module imports this one; the assembly there converts by `exact`. -/
def evalHomAux (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)).obj
        (S.part n) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
      (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app (S.part n) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
      (AlgebraicGeometry.Scheme.relativeProj.evaluation S n)

/-- **Working copy** of `LiftData.dataHom` (definitionally equal, same term). -/
def dataHomAux (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)).obj
        (S.part n) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow M n :=
  (AlgebraicGeometry.Scheme.Modules.pullbackCongr
      (AlgebraicGeometry.Scheme.relativeProj.lift_hom S f M D)).hom.app (S.part n) ≫ D.Ψ n

/-- **Working copy** of `LiftData.twistMulHom` (definitionally equal, same term). -/
def twistMulHomAux (a b : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) ⊗
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S ((a + b : ℕ) : ℤ)) :=
  CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom
      (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ))
      (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ))
          (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))).inv ≫
        AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (Nat.cast_add a b).symm))

/-- **Working copy** of `LiftData.IsTwistFamilyOn` with the `Aux` morphisms (definitionally equal). Original docstring:
**Twist family on an open `V ≤ V₀`.** A family `ψ_n : (τ^*O(n))|_{V₀} ⟶ (M^{⊗n})|_{V₀}` (all `n : ℕ`) is a
*twist family over `V`* if, on every open `A ≤ V`, its section maps satisfy
* (F) the factorization `ψ_n ∘ α_n = β_n` (`evalHom`, `dataHom`), and
* (M) multiplicativity `ψ_{a+b}(μ_{ab}(x ⊗ y)) = monoidalPowCat(ψ_a x ⊗ ψ_b y)` (`twistMulHom`,
  `tensorSections`, `monoidalPowCat`).
Only section maps over opens `A ≤ V` are involved, so the predicate is monotone in `V` (`IsTwistFamilyOn.mono`)
and needs no restriction functor. -/
def IsTwistFamilyOnAux (V₀ : T.Opens)
    (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₀.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₀.ι)
    (V : T.Opens) (hV : V ≤ V₀) : Prop :=
  (∀ (n : ℕ) (A : T.Opens) (hA : A ≤ V)
      (s : Γ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)).obj
          (S.part n), A)),
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ n) A (hA.trans hV) ((D.evalHomAux n).app A s) =
        (D.dataHomAux n).app A s) ∧
  (∀ (a b : ℕ) (A : T.Opens) (hA : A ≤ V)
      (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)), A))
      (y : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)), A)),
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ (a + b)) A (hA.trans hV)
          ((D.twistMulHomAux a b).app A (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ A x y)) =
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat M a b).hom.app A
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ A
            (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ a) A (hA.trans hV) x)
            (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ b) A (hA.trans hV) y)))


/-- `evalHomAux` unfolded (`rfl`); a bridge lemma stating the definitional unfolding once, so that later proofs never unfold it themselves. -/
theorem evalHomAux_eq (n : ℕ) :
    D.evalHomAux n =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.relativeProj.lift S f M D) (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app (S.part n) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
          (AlgebraicGeometry.Scheme.relativeProj.evaluation S n) := rfl

/-- `dataHomAux` unfolded (`rfl`). -/
theorem dataHomAux_eq (n : ℕ) :
    D.dataHomAux n =
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.relativeProj.lift_hom S f M D)).hom.app (S.part n) ≫ D.Ψ n := rfl

/-- `twistMulHomAux` unfolded (`rfl`). -/
theorem twistMulHomAux_eq (a b : ℕ) :
    D.twistMulHomAux a b =
      CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
          (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ))
              (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))).inv ≫
            AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ) ≫
            CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (Nat.cast_add a b).symm)) := rfl

/-! ## Bridges to the transport dictionary (`rfl`: the `Aux` morphisms are the composites used there) -/

section Bridges

variable (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
  {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
  (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
    (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤)
  (hτ : V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
    AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
      AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)

/-- (D-α) with `evalHom`. -/
theorem twistTransport_evalHom' (n : ℕ) (A' : V.toScheme.Opens) (x : Γ(S.part n, W.1)) :
    (D.twistTransport U e W hle hΦ hτ n).hom.app A'
        ((D.evalHomAux n).app (V.ι ''ᵁ A') (D.pulledSection U W hle n A' x)) =
      AlgebraicGeometry.Proj.TwistFamily.pullSection (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ
        (S.sectionsOf W.1 n x).1 (S.sectionsOf W.1 n x).2 A' := by
  rw [D.evalHomAux_eq]
  exact D.twistTransport_evalHom U e W hle hΦ hτ n A' x

/-- (D-β) with `dataHom`. -/
theorem powTriv_dataHom' (n : ℕ) (A' : V.toScheme.Opens) (x : Γ(S.part n, W.1)) :
    AlgebraicGeometry.Scheme.Modules.unitSectionsToRing V.toScheme A'
        ((AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n).app A'
          ((D.dataHomAux n).app (V.ι ''ᵁ A') (D.pulledSection U W hle n A' x))) =
      V.toScheme.presheaf.map (homOfLE le_top).op
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle
          (DirectSum.of (S.sectionsPiece W.1) n x)) := by
  rw [D.dataHomAux_eq]
  exact D.powTriv_dataHom U e W hle n A' x

/-- (D-μ) with `twistMulHom`. -/
theorem twistTransport_twistMulHom' (a b : ℕ) (A' : V.toScheme.Opens)
    (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)), V.ι ''ᵁ A'))
    (y : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)), V.ι ''ᵁ A')) :
    (D.twistTransport U e W hle hΦ hτ (a + b)).hom.app A'
        ((D.twistMulHomAux a b).app (V.ι ''ᵁ A') (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (V.ι ''ᵁ A') x y)) =
      (AlgebraicGeometry.Proj.TwistFamily.mulHom (S.sectionsGrading W.1)
          (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ a b).app A'
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ A'
          ((D.twistTransport U e W hle hΦ hτ a).hom.app A' x) ((D.twistTransport U e W hle hΦ hτ b).hom.app A' y)) := by
  rw [D.twistMulHomAux_eq]
  exact D.twistTransport_twistMulHom U e W hle hΦ hτ a b A' x y

end Bridges


/-! ## The two key identities behind (F) and (M) for the family `ψ_n := Θ_n ≫ χ_n ≫ Λ_n⁻¹` -/

section Key

variable (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
  {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
  (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
    (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤)
  (hτ : V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
    AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
      AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)
  (χ : ∀ n : ℕ,
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)) ⟶
      SheafOfModules.unit V.toScheme.ringCatSheaf)
  (hχ : AlgebraicGeometry.Proj.TwistFamily.IsSectionFamily (S.sectionsGrading W.1)
    (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ
    (AlgebraicGeometry.Proj.TwistFamily.sectionMaps (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ χ))

/-- `ψ_n := Θ_n ≫ χ_n ≫ Λ_n⁻¹ : (τ^*O(n))|_V ⟶ (M^{⊗n})|_V`, the relative twist family attached to an absolute family
`χ` on the generalized piece `V`. -/
def familyOfAbs (n : ℕ) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V.ι ⟶
      (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V.ι :=
  (D.twistTransport U e W hle hΦ hτ n).hom ≫ χ n ≫
    CategoryTheory.inv (AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n)

/-- `Λ_n(ψ_n z) = χ_n(Θ_n z)` on sections. -/
theorem powTriv_app_familyOfAbs_app (n : ℕ) (A' : V.toScheme.Opens)
    (z : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)), V.ι ''ᵁ A')) :
    (AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n).app A' ((D.familyOfAbs U e W hle hΦ hτ χ n).app A' z) =
      (χ n).app A' ((D.twistTransport U e W hle hΦ hτ n).hom.app A' z) := by
  unfold AlgebraicGeometry.Scheme.relativeProj.LiftData.familyOfAbs
  rw [AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfa, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfa,
    AlgebraicGeometry.Scheme.Modules.isIso_app_inv_app]


include hχ in
/-- **Key identity (M), core form**: `Λ_{a+b}(ψ_{a+b}(μ(x' ⊗ y'))) = Λ_{a+b}(monoidalPowCat(ψ_a x' ⊗ ψ_b y'))` on
sections over `V.ι ''ᵁ A'`. Proof: the left side is `χ_{a+b}(Θ_{a+b}(μ(x' ⊗ y')))`, which is `χ_a(Θ_a x') · χ_b(Θ_b y')`
by (D-μ) and (M') of `χ`; the right side is `Λ_a(ψ_a x') · Λ_b(ψ_b y')` by (D-⊗), and `Λ_n ψ_n = χ_n Θ_n`. -/
theorem keyM (a b : ℕ) (A' : V.toScheme.Opens)
    (x' : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)), V.ι ''ᵁ A'))
    (y' : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)), V.ι ''ᵁ A')) :
    (AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle (a + b)).app A'
        ((D.familyOfAbs U e W hle hΦ hτ χ (a + b)).app A'
          ((D.twistMulHomAux a b).app (V.ι ''ᵁ A') (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (V.ι ''ᵁ A') x' y'))) =
      (AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle (a + b)).app A'
        ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat M a b).hom.app (V.ι ''ᵁ A')
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (V.ι ''ᵁ A')
            ((D.familyOfAbs U e W hle hΦ hτ χ a).app A' x') ((D.familyOfAbs U e W hle hΦ hτ χ b).app A' y'))) := by
  rw [D.powTriv_app_familyOfAbs_app U e W hle hΦ hτ χ, D.twistTransport_twistMulHom' U e W hle hΦ hτ a b A' x' y']
  have hmul := hχ.mul a b A' ((D.twistTransport U e W hle hΦ hτ a).hom.app A' x')
    ((D.twistTransport U e W hle hΦ hτ b).hom.app A' y')
  have hpow := AlgebraicGeometry.Scheme.relativeProj.powTriv_monoidalPowCat f M U e W hle a b A'
    ((D.familyOfAbs U e W hle hΦ hτ χ a).app A' x') ((D.familyOfAbs U e W hle hΦ hτ χ b).app A' y')
  rw [D.powTriv_app_familyOfAbs_app U e W hle hΦ hτ χ, D.powTriv_app_familyOfAbs_app U e W hle hΦ hτ χ] at hpow
  exact hmul.trans hpow.symm

end Key

end LiftData

end AlgebraicGeometry.Scheme.relativeProj

end
