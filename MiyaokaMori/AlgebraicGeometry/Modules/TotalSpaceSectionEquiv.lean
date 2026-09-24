import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesCoevaluation
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionConstructions
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # Points of the total space are sections of the pullback

`T`-points of the total space = sections of the pulled-back sheaf: `Hom_X(T, Tot(V)) ≃ Γ(T, g^*V)`;
for `T = X` this gives `Γ(X, V) ≃ {σ : X ⟶ Tot(V) | σ is a section}` (the basis for the construction
of the seed section `s = (f_0, …, f_N) : C → Z`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- The linear form `ψ_s : g^*(V^∨) → O_T`, `φ ↦ ⟨φ, s⟩`, given by a section `s ∈ Γ(T, g^*V)`:
   `g^*V^∨ ≅ g^*V^∨ ⊗ O_T →(id ⊗ s) g^*V^∨ ⊗ g^*V ≅ g^*(V^∨ ⊗ V) →(g^* of evaluation) g^*O_X ≅ O_T`.
   `s` as a morphism `O_T → g^*V` is `homOfTopSection`; evaluation is `internalHomEval`
   (`V^∨ = 𝓗om(V, O_X)`); `g^*A ⊗ g^*B → g^*(A ⊗ B)` is the inverse of `pullbackTensorObjIso`
   (Stacks 01CD). -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.functionalOfSection {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (T : CategoryTheory.Over X)
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf :=
  (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V))).inv ≫
    ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V) ◁
      AlgebraicGeometry.Scheme.Modules.homOfTopSection _ s) ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom
      (AlgebraicGeometry.Scheme.Modules.dual V) V).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
      (AlgebraicGeometry.Scheme.Modules.internalHomEval V (SheafOfModules.unit X.ringCatSheaf)) ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso T.hom).hom

/- Universal property of the symmetric algebra (construction direction): a linear form
   `ψ : g^*(V^∨) → O_T` gives an algebra map `Sym(V^∨) → g_*O_T`. The `m`-th component
   `g^*(Sym^m V^∨) → O_T^{⊗m} → O_T` (`symGradedPullbackDesc`, `unitPowCollapse`) is turned into
   `Sym^m V^∨ → g_*O_T` by the pullback–pushforward adjunction, then descended along the coproduct
   over `m`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctional {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total.carrier ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj (SheafOfModules.unit T.left.ringCatSheaf) :=
  CategoryTheory.Limits.Sigma.desc fun m =>
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
      (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc T.hom ψ m ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse T.left m)

/-- Proof obligation of the universal property of the symmetric algebra: `algebraMapOfFunctional V T ψ`
    given by a linear form `ψ : g^*(V^∨) → O_T` is an `O_X`-algebra map.
    (The hypotheses `[V.IsLocallyFree] [V.IsFiniteType]` cannot be dropped: when `V^∨` is not
    quasi-coherent, `symGradedAlgebra` is the trivial graded algebra, the components of
    `symGradedPullbackDesc` are `0`, and the unit is sent to `0` rather than `1`.)
    Proof route:
    1. `V` locally free of finite type ⇒ `V^∨` locally free of finite type ⇒ quasi-coherent, so
       `symGradedAlgebra (dual V)` is in the `symGradedAlgebraOfQC` branch and `symGradedPullbackDesc` is
       `symPowPullbackDesc`.
    2. Unit: `total.one = symPowπ (dual V) 0 ≫ Sigma.ι _ 0`;
       `Sigma.ι 0 ≫ Sigma.desc = homEquiv(symPowPullbackDesc ψ 0 ≫ 𝟙)`,
       `symPowπ 0 ≫ symPowDesc = homEquiv(pullbackMonoidalPow 0 ≫ monoidalPowMap ψ 0) = homEquiv((pullbackUnitIso g).hom)`,
       which is the adjunction unit `O_X → g_*g^*O_X ≅ g_*O_T`, sending `1` to `1` on `U` (`g^♯` is a
       ring homomorphism).
    3. Multiplication: by the definition of `mul` in `GradedQCAlgebra.total` (curried in the two coproduct
       variables, componentwise `S.mul m n ≫ Sigma.ι (m+n)`) and bilinearity of `tensorSections`, it
       reduces to the component `(m, n)`: one has to show
       `symPowMul m n ≫ φ_{m+n} = (φ_m ⊗ φ_n) ≫ (multiplication of g_*O_T)` with
       `φ_m = homEquiv(symPowPullbackDesc ψ m ≫ unitPowCollapse m)`. After precomposing both sides with
       the epimorphism `symPowπ m ⊗ symPowπ n` (`symPowMul` is descended from `symPowDesc₂` along
       `monoidalPowCat V m n ≫ symPowπ (m+n)`; unfold with `symPowπ_whiskerRight_descCurry`, `symPowπ_desc`),
       this becomes the comparison of `pullbackMonoidalPow g W (m+n) ≫ monoidalPowMap ψ (m+n) ≫ unitPowCollapse (m+n)`
       with `(… m) ⊗ (… n)` via the associativity isomorphism of `monoidalPow` and the compatibility of
       `pullbackTensorObjHom`: induction on `n`, `n = 0` is the right unitor, `n+1` uses associativity of
       the comultiplication `δ` of `pullback g` (`Functor.OplaxMonoidal.associativity`) and the recursive
       definition of `unitPowCollapse` (`λ_{𝟙} = ρ_{𝟙}`).
    4. Connect "the module morphism `𝟙 ⊗ 𝟙 → 𝟙` (left unitor) over `O_T` is multiplication on sections"
       with `tensorSections`: `tensorSections (𝟙_) (𝟙_) U a b ↦ a * b`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctional_isAlgebraMap {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total.IsAlgebraMapToPushforward
      T.hom (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctional V T ψ) := by
  simpa only [AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctional,
    AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore] using
    (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_preservesOperations V T ψ)

/- Section ↦ `X`-morphism `T → Tot(V)`: the construction direction of the universal property of the
   relative Spec (`relativeSpec.ofAlgebraMap`) applied to the algebra map above; compatibility with
   multiplication and unit (`IsAlgebraMapToPushforward`) is `algebraMapOfFunctional_isAlgebraMap`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.ofSection {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj (Opposite.op ⊤) : Type u)) :
    T ⟶ AlgebraicGeometry.Scheme.totalSpace V :=
  AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total T
    (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctional V T
      (AlgebraicGeometry.Scheme.totalSpace.functionalOfSection V T s))
    (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctional_isAlgebraMap V T
      (AlgebraicGeometry.Scheme.totalSpace.functionalOfSection V T s))

/- `X`-morphism `h : T → Tot(V)` ↦ section: the algebra map `Sym(V^∨) → g_*O_T` corresponding to `h`
   (`relativeSpec.toAlgebraMap`) restricted to the degree-one generators `V^∨ → Sym^1 → Sym` (`symGen`),
   transposed by the adjunction to `ψ : g^*(V^∨) → O_T`; the section is `(ψ ⊗ id)(g^* coev_V)`:
   `coev_V ∈ Γ(X, V^∨ ⊗ V)` is the coevaluation section (uses that `V` is locally free), pulled back
   along `g` (`sectionPullbackAlong`), mapped through `g^*(V^∨ ⊗ V) → g^*V^∨ ⊗ g^*V`
   (`pullbackTensorObjHom`), `ψ ⊗ id` and the left unitor into `Γ(T, g^*V)`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.toSection {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj (Opposite.op ⊤) : Type u) :=
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)
  let φ := AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total T h
  let ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      𝟙_ T.left.Modules :=
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _).symm
      (AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
        CategoryTheory.Limits.Sigma.ι S.part 1 ≫ φ)
  let Ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual V) V) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V :=
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual V) V).hom ≫
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom T.hom (AlgebraicGeometry.Scheme.Modules.dual V) V ≫
      (ψ ▷ (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V) ≫
      (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V)).hom
  Ψ.app ⊤ (sectionPullbackAlong T.hom (AlgebraicGeometry.Scheme.Modules.coevSection V))

/-- First inverse law: `h ↦ section ↦ morphism` returns `h`.
    Proof route (`S :=` the total of `Sym(V^∨)`, `φ_h := relativeSpec.toAlgebraMap S T h`, `ψ_h :=` the
    degree-one part of `φ_h` transposed by the adjunction, `s_h := toSection h`):
    1. By `left_inv` of `relativeSpecHomEquiv S T` (Stacks 01LQ), `h = ofAlgebraMap φ_h`; so it suffices
       to show `algebraMapOfFunctional V T (functionalOfSection V T s_h) = φ_h`.
    2. Both sides are `O_X`-algebra maps (left: `algebraMapOfFunctional_isAlgebraMap`; right: the `toFun`
       component of `relativeSpecHomEquiv`). An algebra map out of `Sym` is determined by its degree-one
       part: after precomposing the `m`-th component with the epimorphism `symPowπ (dual V) m`
       (`V^{∨⊗m} → Sym^m`), multiplicativity and induction on `m` reduce to `m`-fold products of the
       degree-one part. So it suffices to show `functionalOfSection V T s_h = ψ_h` (then use the degree-one
       component of `algebraMapOfFunctional`: `symGen ≫ Sigma.ι 1 ≫ algebraMapOfFunctional ψ = homEquiv ψ`,
       i.e. `symPowPullbackDesc ψ 1 ≫ unitPowCollapse 1` composed with `pullback(symGen)` equals `ψ`).
    3. `functionalOfSection V T ((ψ ⊗ id)(g^*coev)) = ψ`: the left-hand side is
       `φ ↦ ⟨φ, (ψ ⊗ id)(coev)⟩ = (ψ ⊗ ev)(φ' ⊗ coev)`, and the claim follows from the triangle identity
       `(V^∨ ⊗ ev) ∘ (coev ⊗ V^∨) = id_{V^∨}` for `(ev, coev)` when `V` is locally free of finite type
       (check locally with a basis `e_i` and dual basis `e^i`: `Σ_i ψ(e^i)·⟨φ, e_i⟩ = ψ(φ)`), the fact that
       `pullbackTensorObjHom`/`pullbackTensorObjIso` are inverse, and monoidality of `pullback g`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.ofSection_toSection {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    AlgebraicGeometry.Scheme.totalSpace.ofSection V T (AlgebraicGeometry.Scheme.totalSpace.toSection V T h) = h := by
  have hi := AlgebraicGeometry.Scheme.totalSpace.sectionConstructionsCore_inverse V T
  change AlgebraicGeometry.Scheme.totalSpace.ofSectionCore V T
      (AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T h) = h
  exact hi.1 h

/-- Second inverse law: `s ↦ morphism ↦ section` returns `s`.
    Proof route (`ψ_s := functionalOfSection V T s`):
    1. By `right_inv` of `relativeSpecHomEquiv S T`,
       `relativeSpec.toAlgebraMap S T (ofSection s) = algebraMapOfFunctional V T ψ_s`.
    2. Its degree-one part transposed by the adjunction is `ψ_s` (the degree-one component formula of
       step 2 above), so `toSection (ofSection s) = (ψ_s ⊗ id)(g^*coev)`.
    3. `(ψ_s ⊗ id)(g^*coev) = s`: the other triangle identity `(ev ⊗ V) ∘ (V ⊗ coev) = id_V` pulled back
       along `g` (locally: `Σ_i ⟨e^i, s⟩ e_i = s`), using naturality of `sectionPullbackAlong` in the module
       morphism and the compatibility of `pullbackTensorObjHom`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.toSection_ofSection {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.totalSpace.toSection V T (AlgebraicGeometry.Scheme.totalSpace.ofSection V T s) = s := by
  have hi := AlgebraicGeometry.Scheme.totalSpace.sectionConstructionsCore_inverse V T
  change AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T
      (AlgebraicGeometry.Scheme.totalSpace.ofSectionCore V T s) = s
  exact hi.2 s

/- `Hom_X(T, Tot V) ≃ Γ(T, g^*V)` (`g = T.hom`): both directions are the constructions above; they are
   mutually inverse by `ofSection_toSection`, `toSection_ofSection`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpaceHomEquiv {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X) :
    (T ⟶ AlgebraicGeometry.Scheme.totalSpace V) ≃
      (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj (Opposite.op ⊤) : Type u) where
  toFun := AlgebraicGeometry.Scheme.totalSpace.toSection V T
  invFun := AlgebraicGeometry.Scheme.totalSpace.ofSection V T
  left_inv := AlgebraicGeometry.Scheme.totalSpace.ofSection_toSection V T
  right_inv := AlgebraicGeometry.Scheme.totalSpace.toSection_ofSection V T

noncomputable def AlgebraicGeometry.Scheme.totalSpaceSectionEquiv {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    (V.val.obj (Opposite.op ⊤) : Type u) ≃
      { σ : X ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left //
        σ ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = CategoryTheory.CategoryStruct.id X } :=
  -- Γ(X, V) ≃ Γ(X, (𝟙 X)^* V) (sections over ⊤ of `Scheme.Modules.pullbackId`),
  -- then `totalSpaceHomEquiv` for T = (X, 𝟙 X), and finally Over-morphisms (X, 𝟙) ⟶ V ↔ sections σ (σ ≫ p = 𝟙)
  ((CategoryTheory.forget AddCommGrpCat).mapIso
      (((AlgebraicGeometry.Scheme.Modules.toPresheaf X).mapIso
        ((AlgebraicGeometry.Scheme.Modules.pullbackId X).app V).symm).app (Opposite.op ⊤))).toEquiv.trans
    ((AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X))).symm.trans
      { toFun := fun h => ⟨h.left, by simpa using CategoryTheory.Over.w h⟩
        invFun := fun σ => CategoryTheory.Over.homMk σ.1 (by simpa using σ.2)
        left_inv := fun h => by ext; rfl
        right_inv := fun σ => rfl })

end
