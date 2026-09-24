import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftPrecomp
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SymCoeffHomMulHomogeneousAux
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivizeSymCoeffAux
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetSpecIso

/-! # Projectivizing a based jet

The projectivization of a based jet (§3 of the paper): when the tuple of normalized coefficients is nowhere
simultaneously zero, it gives `τ = ȷ.projectivize : C̃ → Y_k^GG` with `π_k ∘ τ = ρ`; as soon as some coefficient of
positive order is nonzero, `ȷ` gives at the generic point a `K(C̃)`-point
`ȷ.genericWeightedPoint : Spec K(C̃) → Y_k^GG` (the weighted class at the generic point), which is the restriction
of `τ` to the generic point.

The data `totOver` / `totOverField` / `universalFrameAlg` / `universalFrame` / `jetPoint` / `weightComponent` live in
`JetWeightComponentEqCoefficient`; the `LiftData` of `projectivize` / `genericWeightedPoint` are the separate
definitions `liftData` / `genericLiftData`, whose three propositional fields are named theorems.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
  {L : LineBundle ρ.source.toVariety} {κ : ℕ}

/-! ## Auxiliary lemmas for `map_one` and `map_mul` -/

/-- The adjoint transpose of `pullbackUnitIso g` is Mathlib's `unitToPushforwardObjUnit` (on sections, `g^♯`).
    This is what the right-hand side of `BasedJet.weightComponent_map_one` needs.

    Proof: the `η` of the oplax structure is by definition the adjoint transpose of the `ε` of the lax structure
    (`Adjunction.leftAdjointOplaxMonoidal`); `pullback_η` says `η = pullbackUnitIso.hom` and
    `pushforwardLaxMonoidal_ε` says `ε = unitToPushforwardObjUnit`; apply `homEquiv` to both sides and use
    `Equiv.apply_symm_apply`. (The same statement is proved as `homEquiv_pullbackUnitIso_hom_eq` in
    `TotalSpaceSectionConstructions`; it is not imported here because of its large import closure.) -/
theorem AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackUnitIso_hom
    {Y T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ Y) :
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  rw [← AlgebraicGeometry.Scheme.Modules.pullback_η]
  exact (congrArg _ rfl).trans ((Equiv.apply_symm_apply _ _).trans
    (AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal_ε g))

/-! ## Auxiliary lemmas for `map_one` -/

/-- The unit of `symGradedAlgebra W` followed by `symPartToMonoidalPow W 0` is the identity: `W` is a line bundle,
    hence quasi-coherent, so `symGradedAlgebra W` is in the `symGradedAlgebraOfQC` branch, whose `one` is
    `symPowπ W 0`, while `symPartToMonoidalPow W 0 = inv (symPowπ W 0)`; conclude by `IsIso.hom_inv_id`.
    Technically as in `tensorPowerToSymPart_symPartToMonoidalPow`: `generalize_proofs` extracts the cast proof of
    `dif_pos`, then `subst` the equation `symGradedAlgebra W = symGradedAlgebraOfQC W hq`. -/
theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_one_symPartToMonoidalPow
    {Y : AlgebraicGeometry.Scheme.{u}} (W : Y.Modules) [W.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).one ≫
        AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow W 0 =
      CategoryTheory.CategoryStruct.id _ := by
  have hq : W.IsQuasicoherent := inferInstance
  unfold AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
  generalize_proofs pf1 pf2 pf3 pf4 pf5
  have hS : AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W =
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W hq := by
    delta AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    exact dif_pos hq
  change (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).one ≫
    (pf4 pf3).mpr (@CategoryTheory.inv _ _ _ _ (AlgebraicGeometry.Scheme.Modules.symPowπ W 0) (pf5 pf3)) = 𝟙 _
  generalize AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W = S at hS pf4 ⊢
  subst hS
  exact CategoryTheory.IsIso.hom_inv_id (AlgebraicGeometry.Scheme.Modules.symPowπ W 0)


/-- The inverse of `structureIso` preserves the unit: `structureIso⁻¹(1) = A.one(1)` (`structureHom` preserves the unit, plus `hom_inv_id`). -/
theorem AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_one {Y : AlgebraicGeometry.Scheme.{u}}
    (A : Y.QCAlgebra) (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U
        (show Γ((AlgebraicGeometry.Scheme.relativeSpec A).left,
          (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) from 1) =
      A.one.app U (show Γ(Y, U) from 1) := by
  have h1 := (AlgebraicGeometry.Scheme.relativeSpec.structureHom_isAlgebraMap A).2 U
  have h2 : ∀ x, (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U
      ((AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U x) = x := fun x =>
    congrArg (fun g : A.carrier ⟶ A.carrier => g.app U x)
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).hom_inv_id
  exact (congrArg ((AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U) h1.symm).trans (h2 _)

/-- The inverse of `structureIso` preserves multiplication:
    `structureIso⁻¹(s·t) = A.mul(structureIso⁻¹ s ⊗ structureIso⁻¹ t)` (`structureHom` preserves multiplication,
    plus `hom_inv_id` / `inv_hom_id`). Used by `symCoeffHom_mul_of_homogeneous` and `weightComponent_map_one`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_mul {Y : AlgebraicGeometry.Scheme.{u}}
    (A : Y.QCAlgebra) (U : Y.Opens)
    (s t : Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U)) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U
        (show Γ((AlgebraicGeometry.Scheme.relativeSpec A).left,
          (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) from s * t) =
      A.mul.app U (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U s)
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U t)) := by
  have hinv : ∀ x, (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U
      ((AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U x) = x := fun x =>
    congrArg (fun g : A.carrier ⟶ A.carrier => g.app U x)
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).hom_inv_id
  have hhom : ∀ y, (AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U
      ((AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U y) = y := fun y =>
    congrArg (fun g => g.app U y) (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv_hom_id
  have hmul := (AlgebraicGeometry.Scheme.relativeSpec.structureHom_isAlgebraMap A).1 U
    ((AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U s)
    ((AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U t)
  have e := congrArg₂ (fun a b : Γ((AlgebraicGeometry.Scheme.relativeSpec A).left,
    (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) => a * b) (hhom s) (hhom t)
  exact (congrArg ((AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app U)
    (hmul.trans e).symm).trans (hinv _)

/-- Products of elements of pure `ξ`-degree: if only the `m`-th `ξ`-coefficient of `x` and only the `n`-th
    `ξ`-coefficient of `y` are nonzero, then only the `(m+n)`-th coefficient of `xy` is nonzero, and it equals the
    product of the two coefficients under `monoidalPowCat`.

    Source: §3 of the paper (functions on `Tot(L)` are graded by `ξ`-degree and multiplication adds degrees);
    [Stacks, Tag 01M2] (the grading of the symmetric algebra).

    Proof (the auxiliary lemmas are in `SymCoeffHomMulHomogeneousAux`):
    (1) `symCoeffHom L p = structureIso⁻¹ ≫ totalProj p ≫ symPartToMonoidalPow p` (by definition); write
        `z := structureIso⁻¹ x`, `w := structureIso⁻¹ y ∈ (⊕_q Sym^q L^∨)(V)`. Since `symPartToMonoidalPow` is an
        isomorphism (`symPartToMonoidalPow_isIso`), `hx`, `hy` say `totalProj p z = 0` (`p ≠ m`) and
        `totalProj p w = 0` (`p ≠ n`).
    (2) Sheaf-theoretic step: `V` is an arbitrary open, and a section of `⊕_q Sym^q` need not be a finite sum, but
        the family of projections is jointly injective: `GradedQCAlgebra.totalIncl_totalProj_apply_of_forall_ne`
        gives `z = ι_m(totalProj m z)` and `w = ι_n(totalProj n w)` (on affine opens by
        `exists_finset_sum_eq_of_isColimit_of_isCompact`, then glue by separatedness of the sheaf).
    (3) `structureIso_inv_app_mul`: `structureIso⁻¹(xy) = total.mul(z ⊗ w)`; `tensorHom_tensorSections` and
        `GradedQCAlgebra.total_mul_component` (`(ι_m ⊗ ι_n) ≫ totalMul = mul m n ≫ ι_{m+n}`) give
        `structureIso⁻¹(xy) = ι_{m+n}(mul m n (z_m ⊗ w_n))`.
    (4) `totalIncl_totalProj_of_ne'` / `totalIncl_totalProj`: the `p`-th projection is `0` for `p ≠ m+n`, and the
        `(m+n)`-th is `mul m n (z_m ⊗ w_n)`.
    (5) `symGradedAlgebra_mul_symPartToMonoidalPow`: the multiplication of `Sym` of a line bundle becomes
        `monoidalPowCat` under `symPartToMonoidalPow = inv symPowπ` (by `symPowπ_tensor_symPowMul` and
        `symPowπ_tensor_cancel`); `tensorHom_tensorSections` then gives the right-hand side.
    Edge cases: for `m = n = 0`, `Sym^0 = O` and both sides send `1 ↦ 1`; if `x` or `y` is `0`, both sides are `0`. -/
theorem BasedJet.symCoeffHom_mul_of_homogeneous (L : LineBundle ρ.source.toVariety) (m n : ℕ)
    (V : ρ.source.toScheme.Opens)
    (x y : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V))
    (hx : ∀ p : ℕ, p ≠ m → ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
      (show (((AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
            (Opposite.op V) : Type u) from x) = 0)
    (hy : ∀ p : ℕ, p ≠ n → ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
      (show (((AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
            (Opposite.op V) : Type u) from y) = 0) :
    (∀ p : ℕ, p ≠ m + n → ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
            (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
              (Opposite.op V) : Type u) from x * y) = 0) ∧
      ((BasedJet.symCoeffHom L (m + n)).val.app (Opposite.op V)).hom
          (show (((AlgebraicGeometry.Scheme.Modules.pushforward
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
              (SheafOfModules.unit
                (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
                (Opposite.op V) : Type u) from x * y) =
        ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom.val.app
            (Opposite.op V)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            (AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m)
            (AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n) V
            (((BasedJet.symCoeffHom L m).val.app (Opposite.op V)).hom
              (show (((AlgebraicGeometry.Scheme.Modules.pushforward
                  (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
                  (SheafOfModules.unit
                    (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
                    (Opposite.op V) : Type u) from x))
            (((BasedJet.symCoeffHom L n).val.app (Opposite.op V)).hom
              (show (((AlgebraicGeometry.Scheme.Modules.pushforward
                  (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
                  (SheafOfModules.unit
                    (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
                    (Opposite.op V) : Type u) from y))) := by
  set D := AlgebraicGeometry.Scheme.Modules.dual L.toModules with hD
  set S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra D with hS
  -- σ⁻¹ : Γ(Tot, p⁻¹V) → (⊕ Sym)(V)
  let σinv : (((AlgebraicGeometry.Scheme.Modules.pushforward
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
        (Opposite.op V) : Type u) → (S.total.carrier.val.obj (Opposite.op V) : Type u) :=
    fun t => ((AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).inv.val.app (Opposite.op V)).hom t
  -- the p-th ξ-coefficient is symPartToMonoidalPow p ∘ π_p ∘ σ⁻¹ (definition of symCoeffHom)
  have hcoeff : ∀ (p : ℕ) (t : (((AlgebraicGeometry.Scheme.Modules.pushforward
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
        (Opposite.op V) : Type u)),
      ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom t =
        ((AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D p).val.app (Opposite.op V)).hom
          (((S.totalProj p).val.app (Opposite.op V)).hom (σinv t)) := fun p t => rfl
  -- all projections of σ⁻¹ x other than the m-th vanish, hence σ⁻¹ x = ι_m (π_m σ⁻¹ x); same for y
  have hπx : ∀ p, p ≠ m → ((S.totalProj p).val.app (Opposite.op V)).hom (σinv x) = 0 := fun p hp =>
    AlgebraicGeometry.Scheme.Modules.app_eq_zero_of_isIso _
      (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow_isIso D p) V _ ((hcoeff p x).symm.trans (hx p hp))
  have hπy : ∀ p, p ≠ n → ((S.totalProj p).val.app (Opposite.op V)).hom (σinv y) = 0 := fun p hp =>
    AlgebraicGeometry.Scheme.Modules.app_eq_zero_of_isIso _
      (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow_isIso D p) V _ ((hcoeff p y).symm.trans (hy p hp))
  have hzx := S.totalIncl_totalProj_apply_of_forall_ne m V (σinv x) hπx
  have hzy := S.totalIncl_totalProj_apply_of_forall_ne n V (σinv y) hπy
  set zm := ((S.totalProj m).val.app (Opposite.op V)).hom (σinv x) with hzm
  set wn := ((S.totalProj n).val.app (Opposite.op V)).hom (σinv y) with hwn
  -- σ⁻¹(xy) = ι_{m+n} (mul m n (z_m ⊗ w_n))
  have hmul : σinv (x * y) = ((S.totalIncl (m + n)).val.app (Opposite.op V)).hom
      (((S.mul m n).val.app (Opposite.op V)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn)) := by
    have h1 : σinv (x * y) = (S.total.mul.val.app (Opposite.op V)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections S.total.carrier S.total.carrier V (σinv x) (σinv y)) :=
      AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_mul S.total V x y
    have h2 : AlgebraicGeometry.Scheme.Modules.tensorSections S.total.carrier S.total.carrier V (σinv x) (σinv y) =
        ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := ρ.source.toScheme.Modules)
          (S.totalIncl m) (S.totalIncl n)).val.app (Opposite.op V))
          (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn) := by
      rw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
      exact congrArg₂ (AlgebraicGeometry.Scheme.Modules.tensorSections S.total.carrier S.total.carrier V)
        hzx.symm hzy.symm
    rw [h1, h2]
    exact congrArg (fun g : S.part m ⊗ S.part n ⟶ S.total.carrier =>
      (g.val.app (Opposite.op V)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn))
      (S.total_mul_component m n)
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [hcoeff, hmul]
    have h0 : ((S.totalProj p).val.app (Opposite.op V)).hom
        (((S.totalIncl (m + n)).val.app (Opposite.op V)).hom
          (((S.mul m n).val.app (Opposite.op V)).hom
            (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn))) = 0 :=
      congrArg (fun g : S.part (m + n) ⟶ S.part p => (g.val.app (Opposite.op V)).hom
        (((S.mul m n).val.app (Opposite.op V)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn)))
        (S.totalIncl_totalProj_of_ne' (Ne.symm hp))
    rw [h0]
    exact map_zero _
  · rw [hcoeff, hmul]
    have h1 : ((S.totalProj (m + n)).val.app (Opposite.op V)).hom
        (((S.totalIncl (m + n)).val.app (Opposite.op V)).hom
          (((S.mul m n).val.app (Opposite.op V)).hom
            (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn))) =
        ((S.mul m n).val.app (Opposite.op V)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn) :=
      congrArg (fun g : S.part (m + n) ⟶ S.part (m + n) => (g.val.app (Opposite.op V)).hom
        (((S.mul m n).val.app (Opposite.op V)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn)))
        (S.totalIncl_totalProj (m + n))
    rw [h1]
    have h2 := congrArg (fun g : S.part m ⊗ S.part n ⟶ AlgebraicGeometry.Scheme.Modules.monoidalPow D (m + n) =>
        (g.val.app (Opposite.op V)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn))
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_mul_symPartToMonoidalPow D m n)
    refine h2.trans ?_
    show (((AlgebraicGeometry.Scheme.Modules.monoidalPowCat D m n).hom).val.app (Opposite.op V)).hom
      (((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := ρ.source.toScheme.Modules)
        (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D m)
        (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D n)).val.app (Opposite.op V))
        (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) V zm wn)) = _
    rw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
    rfl

/-- `φ_J^♯` sends the weight-`m` piece into `Sym^m(L^∨)`: for `x ∈ S_m(U)` (`U` an affine open) and `n ≠ m`, the
    `n`-th `ξ`-coefficient of `φ_J^♯(x)` is `0`. This is the whole content, on sections, of the `G_m`-equivariance
    of `φ_J` (without it `weightComponent_map_mul` would be false).

    Source: §2 of the paper (`t ↦ λt` gives the grading; "its coordinates have weight `q`"); the ring-level
    counterpart is `BasedJetAlgebra.mem_grading_iff_coaction`.

    Proof sketch (`U` affine open, `F_U := J_κ(B_U, ε_U)` the chart ring):
    (1)–(3) With `y := chartSections⁻¹(partι x) ∈ F_U`, the hypothesis `x ∈ ker(weightDefect m)` says that `y` lies in
        the `m`-th graded piece: this is `relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff` (the kernel of the
        weight defect is the graded piece; the chart identification `χ_U = chartEquiv` agrees with `chartSections`
        transported along `preimage_eq_chartOpen`).
    (4)–(7) The `m`-th piece is spanned by the jet-coordinate monomials `∏_i d_{q_i} b_i` of weight `m`
        (`Σ(q_i+1) = m`), so it suffices to check the claim on monomials: this is the purely algebraic induction
        `PureDegree.isPure_eval_of_isWeightedHomogeneous` (`JetProjectivizePureDegree`), whose two inputs are the
        constants (`chartEquiv_unitHom` and "the scalar action of `p_*O_Tot` is multiplication by `p^♯`", in
        `JetProjectivizeSymCoeffAux`) and the generators `d_q b` (`BasedJet.jetPoint_appLE_jetCoordinate`: the value
        is in the image of `frameHom (q+1)`, hence of pure `ξ`-degree `q+1` by `frameHom_symCoeffHom_of_ne`);
        closure under products is `symCoeffHom_mul_of_homogeneous` above.
    Edge cases: for `κ = 0`, `F_U = Γ(𝒵,π⁻¹U)` has only the piece `m = 0`, and for `n ≠ 0` the claim follows from
    the value of `symCoeffHom` on constants; for `m = 0` the monomial in (4) is the empty product `1`. -/
theorem BasedJet.symCoeffHom_jetPoint_partι_of_ne (J : BasedJet f ρ L κ) (m n : ℕ) (hmn : n ≠ m)
    (U : C.toScheme.AffineZariskiSite)
    (x : (((jetAlgebra f κ).part m).val.obj (Opposite.op U.1) : Type u))
    (hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1 ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)) :
    ((BasedJet.symCoeffHom L n).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
            (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
              (Opposite.op (ρ.hom ⁻¹ᵁ U.1)) : Type u) from
          (J.jetPoint.left.appLE
              ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
              ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom
            (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
                (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1) from
              ((BasedJet.partι f κ m).val.app (Opposite.op U.1)).hom x)) = 0 := by
  -- Route: (1)–(3) are given at once by `relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff`
  -- (kernel of the weight defect = graded piece); (4)–(7) are the purely algebraic induction
  -- `PureDegree.isPure_eval_of_isWeightedHomogeneous` of `JetProjectivizePureDegree`, whose two inputs (constants,
  -- generators `d_q b`) are in `JetProjectivizeSymCoeffAux`; closure under products is `symCoeffHom_mul_of_homogeneous`.
  let _ := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) U.1
  -- notation: the chart identification `χ_U`, `φ_J^♯`, the family `c` of `ξ`-coefficients
  have hy : ∃ y : (jetGradedAffineAlgebra (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).toAffineAlgebra.sections U,
      relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U y =
        (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
            (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1) from
          ((BasedJet.partι f κ m).val.app (Opposite.op U.1)).hom x) :=
    ⟨(relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U).symm _,
      (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U).apply_symm_apply _⟩
  obtain ⟨y, hy⟩ := hy
  -- (1)–(3): x ∈ ker(weightDefect m) ⇒ y lies in the m-th piece
  have hker : ((GroupSchemeAction.weightDefect
      (jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ) m).val.app
        (Opposite.op U.1)).hom (((BasedJet.partι f κ m).val.app (Opposite.op U.1)).hom x) = 0 :=
    AlgebraicGeometry.Scheme.Modules.kernel_ι_app_apply _ U.1 x
  have hgr : y ∈ (jetGradedAffineAlgebra (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).grading U m :=
    (relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff (k := k) (MMSetup.cone f) (MMSetup.seed f).1
      (MMSetup.seed f).2 κ U m y).mp
      ((congrArg ((GroupSchemeAction.weightDefect
        (jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ) m).val.app
          (Opposite.op U.1)).hom hy).trans hker)
  have hgr' : (y : BasedJetAlgebra
      (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ) ∈
      BasedJetAlgebra.grading
        (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ m := hgr
  obtain ⟨q, hq, hqy⟩ := (BasedJetAlgebra.mem_grading_iff
    (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ m y).mp hgr'
  -- (4)–(7) pure algebra: Ψ := φ_J^♯ ∘ χ_U ∘ mk sends weight-m homogeneous polynomials to pure ξ-degree m
  have hmul : PureDegree.MulClosed (BasedJet.symCoeffAddHom L (ρ.hom ⁻¹ᵁ U.1)) := fun m' n' x' y' hx' hy' =>
    (BasedJet.isPure_symCoeffAddHom_iff L (ρ.hom ⁻¹ᵁ U.1) (m' + n') (x' * y')).mpr
      (BasedJet.symCoeffHom_mul_of_homogeneous L m' n' (ρ.hom ⁻¹ᵁ U.1) x' y'
        ((BasedJet.isPure_symCoeffAddHom_iff L (ρ.hom ⁻¹ᵁ U.1) m' x').mp hx')
        ((BasedJet.isPure_symCoeffAddHom_iff L (ρ.hom ⁻¹ᵁ U.1) n' y').mp hy')).1
  let Ψ : MvPolynomial (Fin κ × Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1)) Γ(C.toScheme, U.1) →+*
      Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) :=
    ((J.jetPoint.left.appLE
        ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
        ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom.comp
      (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U).toRingHom).comp
      (Ideal.Quotient.mk (BasedJetAlgebra.relations
        (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ))
  have hC : ∀ a : Γ(C.toScheme, U.1), PureDegree.IsPure (BasedJet.symCoeffAddHom L (ρ.hom ⁻¹ᵁ U.1)) 0
      (Ψ (MvPolynomial.C a)) := by
    intro a p hp
    have h1 : relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U
        (Ideal.Quotient.mk (BasedJetAlgebra.relations
          (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ)
          (MvPolynomial.C a)) =
        ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.app U.1).hom a :=
      relativeJetScheme.chartEquiv_unitHom (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U a
    refine Eq.trans ?_ (J.symCoeffHom_jetPoint_app_of_ne U.1 a hle hp)
    exact congrArg (fun t => ((BasedJet.symCoeffHom L p).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
      ((J.jetPoint.left.appLE
        ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
        ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom t)) h1
  have hX : ∀ i : Fin κ × Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1),
      PureDegree.IsPure (BasedJet.symCoeffAddHom L (ρ.hom ⁻¹ᵁ U.1))
        (BasedJetAlgebra.weight κ Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1) i)
        (Ψ (MvPolynomial.X i)) := fun i p hp =>
    J.symCoeffHom_jetPoint_chartEquiv_X_of_ne U hle i.1 i.2 hp
  have key := PureDegree.isPure_eval_of_isWeightedHomogeneous hmul Ψ _ hC hX hq n hmn
  -- assemble: Ψ q = φ_J^♯(χ_U y) = φ_J^♯(partι x)
  refine Eq.trans ?_ key
  exact congrArg (fun t => ((BasedJet.symCoeffHom L n).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
    ((J.jetPoint.left.appLE
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
      ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom t))
    (hy.symm.trans (congrArg
      (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U) hqy.symm))

/-- The `0`-th `ξ`-coefficient sends `1` to `1`: `structureIso⁻¹(1) = (S.one ≫ ι₀)(1)` (previous lemma),
    `totalIncl_totalProj`, then `symGradedAlgebra_one_symPartToMonoidalPow`. -/
theorem BasedJet.symCoeffHom_zero_app_one (L : LineBundle ρ.source.toVariety) (V : ρ.source.toScheme.Opens) :
    (show Γ(ρ.source.toScheme, V) from
      ((BasedJet.symCoeffHom L 0).val.app (Opposite.op V)).hom
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from 1)) = 1 := by
  set D := AlgebraicGeometry.Scheme.Modules.dual L.toModules
  set S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra D
  have e1 := AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_one S.total V
  have e2 : S.total.one ≫ S.totalProj 0 ≫ AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D 0 =
      CategoryTheory.CategoryStruct.id _ := by
    show (S.one ≫ S.totalIncl 0) ≫ S.totalProj 0 ≫ _ = _
    rw [CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc (S.totalIncl 0),
      S.totalIncl_totalProj, CategoryTheory.Category.id_comp]
    exact AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_one_symPartToMonoidalPow D
  have e3 := congrArg (fun g : 𝟙_ ρ.source.toScheme.Modules ⟶ _ => g.app V (show Γ(ρ.source.toScheme, V) from 1)) e2
  have e4 : (show Γ(ρ.source.toScheme, V) from
      ((BasedJet.symCoeffHom L 0).val.app (Opposite.op V)).hom
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from 1)) =
      (S.totalProj 0 ≫ AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D 0).app V
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).inv.app V
          (show Γ((AlgebraicGeometry.Scheme.relativeSpec S.total).left,
            (AlgebraicGeometry.Scheme.relativeSpec S.total).hom ⁻¹ᵁ V) from 1)) := rfl
  exact e4.trans ((congrArg ((S.totalProj 0 ≫ AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D 0).app V)
    e1).trans e3)

/-- The unit of the weight-`0` piece, pushed through `partι`, is the unit section `1` of `π_*O_J`
    (`kernel.lift_ι`: `S.one ≫ partι 0 = unitToPushforwardObjUnit π`, whose value on `1` is `π^♯(1) = 1`). -/
theorem BasedJet.partι_app_one (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (U : C.toScheme.Opens) :
    (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
        (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U) from
      ((BasedJet.partι f κ 0).val.app (Opposite.op U)).hom
        (((jetAlgebra f κ).one.val.app (Opposite.op U)).hom (show Γ(C.toScheme, U) from 1))) = 1 := by
  have h : (jetAlgebra f κ).one ≫ BasedJet.partι f κ 0 =
      SheafOfModules.unitToPushforwardObjUnit
        (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.toRingCatSheafHom :=
    CategoryTheory.Limits.kernel.lift_ι _ _ _
  have h2 := congrArg (fun g : (𝟙_ C.toScheme.Modules) ⟶ _ =>
    (g.val.app (Opposite.op U)).hom (show Γ(C.toScheme, U) from 1)) h
  refine h2.trans ?_
  exact map_one ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.app U).hom

/-- `Ψ` preserves the unit (§3 of the paper: the construction of `τ` requires `Ψ` to be a map of graded algebra
    sheaves, and this is the `map_one` field of `relativeProj.LiftData`).

    Proof: (1) apply the bijection `homEquiv` of `pullbackPushforwardAdjunction ρ.hom` to both sides, reducing to an
    equality of maps `S_0 ⟶ ρ_*O_C̃`. (2) Right-hand side: `homEquiv_pullbackUnitIso_hom` gives
    `unitToPushforwardObjUnit ρ^♯`. (3) Left-hand side: `Adjunction.homEquiv_naturality_left` gives
    `(jetAlgebra f κ).one ≫ homEquiv (J.weightComponent 0)`; both sides are maps out of `O_C`, so by injectivity of
    `SheafOfModules.unitHomEquiv` it suffices to compare the images of `1` on every open `U`.
    (4) `BasedJet.weightComponent_adj_app` writes the left-hand value on `1` as
    `symCoeffHom L 0 (φ_J^♯ (partι (one 1)))`. (5) `partι_app_one`: `partι (one 1) = 1`; (6) `φ_J^♯` is a ring map
    (`map_one`); (7) `symCoeffHom_zero_one` (from `structureIso_inv_app_one` and
    `symGradedAlgebra_one_symPartToMonoidalPow`); the right-hand side is `ρ^♯(1) = 1`. -/
theorem BasedJet.weightComponent_map_one (J : BasedJet f ρ L κ) :
    (AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).map (jetAlgebra f κ).one ≫ J.weightComponent 0 =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso ρ.hom).hom := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _).injective
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left]
  refine Eq.trans ?_ (AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackUnitIso_hom ρ.hom).symm
  apply (SheafOfModules.unitHomEquiv _).injective
  ext ⟨U⟩
  have hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, CategoryTheory.Over.w]
  have h1 := J.weightComponent_adj_app 0 U
    (((jetAlgebra f κ).one.val.app (Opposite.op U)).hom (show Γ(C.toScheme, U) from 1)) hle
  have h2 := BasedJet.partι_app_one f κ U
  have h3 := BasedJet.symCoeffHom_zero_app_one L (ρ.hom ⁻¹ᵁ U)
  show ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
      (J.weightComponent 0)).val.app (Opposite.op U)).hom
      (((jetAlgebra f κ).one.val.app (Opposite.op U)).hom (show Γ(C.toScheme, U) from 1)) =
    (ρ.hom.app U).hom (show Γ(C.toScheme, U) from 1)
  refine Eq.trans ?_ (map_one (ρ.hom.app U).hom).symm
  refine h1.trans ?_
  refine (congrArg (fun y => ((BasedJet.symCoeffHom L 0).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U))).hom
    ((J.jetPoint.left.appLE _ _ hle).hom y)) h2).trans ?_
  refine (congrArg (fun y => ((BasedJet.symCoeffHom L 0).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U))).hom y)
    (map_one (J.jetPoint.left.appLE _ _ hle).hom)).trans ?_
  exact h3

/-- `Ψ` preserves multiplication (§3 of the paper; the `map_mul` field of `relativeProj.LiftData`).

    Proof (the mathematical core is `symCoeffHom_jetPoint_partι_of_ne` above):
    (1) Both sides are maps `ρ^*(S_m ⊗ S_n) ⟶ (L^∨)^{⊗(m+n)}`; apply the bijection `homEquiv` of
        `pullbackPushforwardAdjunction ρ.hom` to reduce to an equality of maps `S_m ⊗ S_n ⟶ ρ_*(L^∨)^{⊗(m+n)}`
        (`homEquiv_naturality_left` / `homEquiv_naturality_right`).
    (2) A map out of a tensor product is determined by pairs of sections over **affine** opens:
        `Modules.tensorObj_hom_ext_of_isAffineOpen` (`SymCoeffHomMulHomogeneousAux`, from `tensorObj_hom_ext`,
        separatedness of the sheaf and `tensorSections_restrict`). Take an affine open `U`, `a ∈ S_m(U)`, `b ∈ S_n(U)`.
    (3) Left-hand side: `(jetAlgebra f κ).mul m n ≫ partι (m+n) = (partι m ⊗ partι n) ≫ (π_*O_J).mul`
        (`kernel.lift_ι`), and the multiplication of `π_*O_J` on sections is that of `Γ(π⁻¹U, O_J)`
        (`sectionsMul_eq_mul_tensorSections` and `pushforwardStructureSheaf.sectionsRing_mul`); so by
        `weightComponent_adj_app` and `φ_J^♯` being a ring map, the left-hand side is `symCoeffHom (m+n) (x·y)` with
        `x := φ_J^♯(partι a)`, `y := φ_J^♯(partι b)`.
    (4) `symCoeffHom_jetPoint_partι_of_ne`: only the `m`-th `ξ`-coefficient of `x` and only the `n`-th of `y` are
        nonzero; `symCoeffHom_mul_of_homogeneous`:
        `symCoeffHom (m+n) (x·y) = monoidalPowCat (symCoeffHom m x ⊗ symCoeffHom n y)`.
    (5) Right-hand side: `homEquiv_pullbackTensorObjHom_tensorSections` (the adjoint of `δ` sends `a ⊗ b` to
        `η(a) ⊗ η(b)`), `homEquiv_naturality_right` and `weightComponent_adj_app` twice give
        `monoidalPowCat (symCoeffHom m x ⊗ symCoeffHom n y)`.
    Edge cases: for `m = n = 0` both sides reduce to the case of `map_one`; for `κ = 0` only `m = n = 0` occurs. -/
theorem BasedJet.weightComponent_map_mul (J : BasedJet f ρ L κ) (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).map ((jetAlgebra f κ).mul m n) ≫ J.weightComponent (m + n) =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ.hom ((jetAlgebra f κ).part m) ((jetAlgebra f κ).part n) ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := ρ.source.toScheme.Modules)
          (J.weightComponent m) (J.weightComponent n) ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _).injective
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left, CategoryTheory.Adjunction.homEquiv_naturality_right]
  apply AlgebraicGeometry.Scheme.Modules.tensorObj_hom_ext_of_isAffineOpen
  intro U hU a b
  have hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, CategoryTheory.Over.w]
  -- abbreviations
  set adj := AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom with hadj
  set π := (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom with hπ
  set φ := J.jetPoint.left.appLE
    ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U)
    ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U) hle with hφ
  -- x := φ^♯ (partι a), y := φ^♯ (partι b)
  set x : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) :=
    φ.hom (((BasedJet.partι f κ m).val.app (op U)).hom a) with hx
  set y : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) :=
    φ.hom (((BasedJet.partι f κ n).val.app (op U)).hom b) with hy
  -- (1) partι (mul m n (a ⊗ b)) = partι a * partι b
  have hpart : ((BasedJet.partι f κ (m + n)).val.app (op U)).hom
      ((((jetAlgebra f κ).mul m n).val.app (op U)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b)) =
      (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
          π ⁻¹ᵁ U) from ((BasedJet.partι f κ m).val.app (op U)).hom a) *
      (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
          π ⁻¹ᵁ U) from ((BasedJet.partι f κ n).val.app (op U)).hom b) := by
    have h1 : (jetAlgebra f κ).mul m n ≫ BasedJet.partι f κ (m + n) =
        (BasedJet.partι f κ m ⊗ₘ BasedJet.partι f κ n) ≫
          (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf π).mul :=
      CategoryTheory.Limits.kernel.lift_ι _ _ _
    have h2 := congrArg (fun g : (jetAlgebra f κ).part m ⊗ (jetAlgebra f κ).part n ⟶ _ =>
      (g.val.app (op U)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b)) h1
    refine h2.trans ?_
    show (((AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf π).mul).val.app (op U)).hom
      (((BasedJet.partι f κ m ⊗ₘ BasedJet.partι f κ n).val.app (op U)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b)) = _
    rw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
    exact (AlgebraicGeometry.Scheme.QCAlgebra.sectionsMul_eq_mul_tensorSections
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf π) U _ _).symm.trans
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sectionsRing_mul π U _ _)
  -- (2) left-hand side
  have hL : ((((jetAlgebra f κ).mul m n ≫ adj.homEquiv _ _ (J.weightComponent (m + n))).val.app (op U)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b)) =
      ((BasedJet.symCoeffHom L (m + n)).val.app (op (ρ.hom ⁻¹ᵁ U))).hom (x * y) := by
    refine (J.weightComponent_adj_app (m + n) U _ hle).trans ?_
    exact (congrArg (fun z => ((BasedJet.symCoeffHom L (m + n)).val.app (op (ρ.hom ⁻¹ᵁ U))).hom (φ.hom z))
      hpart).trans (congrArg (((BasedJet.symCoeffHom L (m + n)).val.app (op (ρ.hom ⁻¹ᵁ U))).hom)
        (map_mul φ.hom _ _))
  -- (3) homogeneity of x, y
  have hxh : ∀ p : ℕ, p ≠ m → ((BasedJet.symCoeffHom L p).val.app (op (ρ.hom ⁻¹ᵁ U))).hom x = 0 :=
    fun p hp => J.symCoeffHom_jetPoint_partι_of_ne m p hp ⟨U, hU⟩ a hle
  have hyh : ∀ p : ℕ, p ≠ n → ((BasedJet.symCoeffHom L p).val.app (op (ρ.hom ⁻¹ᵁ U))).hom y = 0 :=
    fun p hp => J.symCoeffHom_jetPoint_partι_of_ne n p hp ⟨U, hU⟩ b hle
  have hmul := (BasedJet.symCoeffHom_mul_of_homogeneous L m n (ρ.hom ⁻¹ᵁ U) x y hxh hyh).2
  -- (4) right-hand side
  have hΨ : ∀ (p : ℕ) (c : (((jetAlgebra f κ).part p).val.obj (op U) : Type u)),
      ((J.weightComponent p).val.app (op (ρ.hom ⁻¹ᵁ U))).hom
          (((adj.unit.app ((jetAlgebra f κ).part p)).val.app (op U)).hom c) =
        ((adj.homEquiv _ _ (J.weightComponent p)).val.app (op U)).hom c := by
    intro p c
    rw [CategoryTheory.Adjunction.homEquiv_unit]
    rfl
  have hR : (((adj.homEquiv _ _ (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ.hom
        ((jetAlgebra f κ).part m) ((jetAlgebra f κ).part n))) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward ρ.hom).map
          (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := ρ.source.toScheme.Modules)
            (J.weightComponent m) (J.weightComponent n) ≫
          (AlgebraicGeometry.Scheme.Modules.monoidalPowCat
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom)).val.app (op U)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b) =
      (((AlgebraicGeometry.Scheme.Modules.monoidalPowCat
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom.val.app (op (ρ.hom ⁻¹ᵁ U))).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (ρ.hom ⁻¹ᵁ U)
          (((adj.homEquiv _ _ (J.weightComponent m)).val.app (op U)).hom a)
          (((adj.homEquiv _ _ (J.weightComponent n)).val.app (op U)).hom b))) := by
    have h1 := AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom_tensorSections ρ.hom
      ((jetAlgebra f κ).part m) ((jetAlgebra f κ).part n) U a b
    show (((AlgebraicGeometry.Scheme.Modules.monoidalPowCat
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom.val.app (op (ρ.hom ⁻¹ᵁ U))).hom
        (((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := ρ.source.toScheme.Modules)
            (J.weightComponent m) (J.weightComponent n)).val.app (op (ρ.hom ⁻¹ᵁ U))).hom
          (((adj.homEquiv _ _ (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ.hom
            ((jetAlgebra f κ).part m) ((jetAlgebra f κ).part n))).val.app (op U)).hom
            (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b)))) = _
    refine (congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.monoidalPowCat
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom.val.app (op (ρ.hom ⁻¹ᵁ U))).hom
        (((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := ρ.source.toScheme.Modules)
            (J.weightComponent m) (J.weightComponent n)).val.app (op (ρ.hom ⁻¹ᵁ U))).hom z))) h1).trans ?_
    refine congrArg (((AlgebraicGeometry.Scheme.Modules.monoidalPowCat
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom.val.app (op (ρ.hom ⁻¹ᵁ U))).hom) ?_
    refine (AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (J.weightComponent m) (J.weightComponent n)
      (ρ.hom ⁻¹ᵁ U) _ _).trans ?_
    exact congrArg₂ (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (ρ.hom ⁻¹ᵁ U)) (hΨ m a) (hΨ n b)
  refine hL.trans (hmul.trans ?_)
  refine Eq.trans ?_ hR.symm
  exact congrArg (((AlgebraicGeometry.Scheme.Modules.monoidalPowCat
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom.val.app (op (ρ.hom ⁻¹ᵁ U))).hom)
    (congrArg₂ (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (ρ.hom ⁻¹ᵁ U))
      (J.weightComponent_adj_app m U a hle).symm (J.weightComponent_adj_app n U b hle).symm)

/-- `Ψ` is locally surjective in some positive degree (from `hnz`): reduces to `weightComponent_generates_of_nowhereZero`. -/
theorem BasedJet.weightComponent_generates (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J) :
    ∀ t : ρ.source.toScheme, ∃ (U : ρ.source.toScheme.Opens) (_ : t ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map (J.weightComponent m)) :=
  J.weightComponent_generates_of_nowhereZero hnz

/-- The lift data of `projectivize`: the line bundle `L^∨` and `Ψ_m = J.weightComponent m`. -/
noncomputable def BasedJet.liftData (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J) :
    AlgebraicGeometry.Scheme.relativeProj.LiftData (jetAlgebra f κ) ρ.hom
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) where
  Ψ := J.weightComponent
  map_one := J.weightComponent_map_one
  map_mul := J.weightComponent_map_mul
  generates := J.weightComponent_generates hnz

/- The projectivization `τ : C̃ → Y_k^GG` of a nowhere-zero tuple of normalized coefficients (on the affine Proj chart
   containing the unit coordinate `x_{i,q}` it is given by evaluating the degree-zero weighted-homogeneous fractions,
   then glued), with `π_k ∘ τ = ρ`. -/

noncomputable def BasedJet.projectivize (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J) :
    ρ.source.toScheme ⟶ YGG f κ :=
  -- the line bundle is L^∨; the input data are BasedJet.liftData
  AlgebraicGeometry.Scheme.relativeProj.lift (jetAlgebra f κ) ρ.hom
    (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (J.liftData hnz)

theorem BasedJet.projectivize_proj (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J) :
    J.projectivize hnz ≫ YGG.proj f κ = ρ.hom :=
  AlgebraicGeometry.Scheme.relativeProj.lift_hom _ _ _ _

/-- The lift data of `J` pulled back along an arbitrary `g : T' → C̃`: the line bundle `g^*L^∨` and
    `Ψ_m = relativeProj.precompΨ g J.weightComponent m` (unfolded: `pullbackComp.inv ≫ g^*Ψ_m ≫ pullbackMonoidalPow`).
    `map_one` and `map_mul` follow from those of `J`; local surjectivity is taken as the hypothesis `hgen` (for `g`
    the inclusion of the generic point it follows from `hne`, without `hnz`). The statement is made for a general
    `T'` and then specialized because writing these equations directly on `T' = Spec K(C̃)` makes kernel type
    checking very slow. -/
noncomputable def BasedJet.precompLiftData (J : BasedJet f ρ L κ) {T' : AlgebraicGeometry.Scheme.{u}}
    (g : T' ⟶ ρ.source.toScheme)
    (hgen : ∀ t : T', ∃ (U : T'.Opens) (_ : t ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map
        (AlgebraicGeometry.Scheme.relativeProj.precompΨ g J.weightComponent m))) :
    AlgebraicGeometry.Scheme.relativeProj.LiftData (jetAlgebra f κ) (g ≫ ρ.hom)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) where
  Ψ := AlgebraicGeometry.Scheme.relativeProj.precompΨ g J.weightComponent
  map_one := AlgebraicGeometry.Scheme.relativeProj.precompΨ_map_one _ _ J.weightComponent_map_one
  map_mul := AlgebraicGeometry.Scheme.relativeProj.precompΨ_map_mul _ _ J.weightComponent_map_mul
  generates := hgen

/-- The lift data of `genericWeightedPoint`: the line bundle `η^*L^∨` and `Ψ_m = η^*(J.weightComponent m)`
    (`η : Spec K(C̃) → C̃`); `generates` follows from `hne`: some coefficient of positive order does not vanish at
    the generic point. -/
noncomputable def BasedJet.genericLiftData (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) :
    AlgebraicGeometry.Scheme.relativeProj.LiftData (jetAlgebra f κ)
      (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) :=
  J.precompLiftData (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))
    (J.genericWeightComponent_generates_of_ne_zero hne)

theorem BasedJet.genericLiftData_Ψ (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) :
    (J.genericLiftData hne).Ψ =
      AlgebraicGeometry.Scheme.relativeProj.precompΨ
        (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)) (J.liftData hnz).Ψ :=
  rfl

/- The weighted point of `J` at the generic point of `C̃`: `Spec K(C̃) → Y_k^GG` (it only requires `J` to be a
   nonconstant seed at the generic point, i.e. some coefficient of positive order is nonzero). -/

noncomputable def BasedJet.genericWeightedPoint (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) :
    AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶ YGG f κ :=
  -- the same construction on T = Spec K(C̃): g = (η ↪ C̃) ≫ ρ, line bundle η^*L^∨, Ψ_m pulled back along η;
  -- the input data are BasedJet.genericLiftData
  let η := ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)
  let D := AlgebraicGeometry.Scheme.Modules.dual L.toModules
  AlgebraicGeometry.Scheme.relativeProj.lift (jetAlgebra f κ) (η ≫ ρ.hom)
    ((AlgebraicGeometry.Scheme.Modules.pullback η).obj D) (J.genericLiftData hne)

theorem BasedJet.genericWeightedPoint_eq (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) :
    J.genericWeightedPoint hne
      = ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ J.projectivize hnz :=
  -- `lift` is natural with respect to precomposition: the Ψ components of the two LiftData are definitionally equal
  AlgebraicGeometry.Scheme.relativeProj.lift_eq_comp_of_Ψ_eq (J.liftData hnz) _ (J.genericLiftData hne)
    (J.genericLiftData_Ψ hnz hne)

end
