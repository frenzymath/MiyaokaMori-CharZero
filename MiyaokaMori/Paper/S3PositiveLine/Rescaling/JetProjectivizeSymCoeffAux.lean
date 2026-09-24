import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SymCoeffHomMulHomogeneousAux
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGradedAlgebraSectionsBridge
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivizePureDegree

/-! # Sym coeff jet point part of ne — geometric auxiliaries

The four "one-generator" facts behind `BasedJet.symCoeffHom_jetPoint_partι_of_ne`
(`JetProjectivize`): with `φ_J^♯` the ring map
`Γ(J, π⁻¹U) → Γ(Tot(L), (ρ∘p)⁻¹U)` induced by `φ_J = J.jetPoint` and `χ_U : J_κ(B_U, ε_U) ≃+* Γ(J, π⁻¹U)` the chart
identification (`relativeJetScheme.chartEquiv`),

* `symCoeffHom_app_one_of_ne`: the unit `1 ∈ Γ(Tot(L), p⁻¹V)` has pure ξ-degree `0`;
* `symCoeffHom_app_totalSpace_app_of_ne`: so does every function `p^♯ a`, `a ∈ Γ(C̃, V)`, pulled back from the base
  (`p^♯ a = a • 1` in the `O_{C̃}`-module `p_*O_{Tot}`, and `symCoeffHom` is `O_{C̃}`-linear);
* `symCoeffHom_jetPoint_app_of_ne`: hence so does `φ_J^♯(π^♯ a)`, `a ∈ Γ(C, U)` (`φ_J ≫ π = p ≫ ρ`, `Over.w`);
* `symCoeffHom_jetPoint_chartEquiv_X_of_ne`: the jet coordinate `d_q b = χ_U (X (q, b))` is sent by `φ_J^♯` to an element
  of pure ξ-degree `q + 1` (`jetPoint_appLE_jetCoordinate` + `frameHom_symCoeffHom_of_ne`);
* `symCoeffAddHom`: the coefficient maps packaged as additive maps, the input of `PureDegree`
  (`JetProjectivizePureDegree`), with `isPure_symCoeffAddHom_iff` unfolding `PureDegree.IsPure`.

Source: §2 of the paper ("its coordinates have weight `q`") and §3.
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

/-- `structureHom A` is an algebra map: second component of `relativeSpecHomEquiv A _ (𝟙 _)`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.structureHom_isAlgebraMap {Y : AlgebraicGeometry.Scheme.{u}} (A : Y.QCAlgebra) :
    A.IsAlgebraMapToPushforward (AlgebraicGeometry.Scheme.relativeSpec A).hom
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom A) :=
  (AlgebraicGeometry.Scheme.relativeSpecHomEquiv A (AlgebraicGeometry.Scheme.relativeSpec A)
    (CategoryTheory.CategoryStruct.id _)).2

/-- (Private copy of `relativeSpec.structureIso_inv_app_one` of `JetProjectivize`.) `structureIso⁻¹ 1 = A.one 1`. -/
private theorem structureIso_inv_app_one' {Y : AlgebraicGeometry.Scheme.{u}} (A : Y.QCAlgebra) (U : Y.Opens) :
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

/-- The `p`-th ξ-coefficient of `1` vanishes for `p ≠ 0`: `structureIso⁻¹ 1 = (S.one ≫ ι₀) 1`
(`structureIso_inv_app_one`) and `ι₀ ≫ π_p = 0` (`totalIncl_totalProj_of_ne'`). -/
theorem BasedJet.symCoeffHom_app_one_of_ne (L : LineBundle ρ.source.toVariety) (V : ρ.source.toScheme.Opens)
    {p : ℕ} (hp : p ≠ 0) :
    ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from 1) = 0 := by
  set D := AlgebraicGeometry.Scheme.Modules.dual L.toModules
  set S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra D
  have e1 := structureIso_inv_app_one' S.total V
  have e2 : S.total.one ≫ S.totalProj p ≫ AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D p = 0 := by
    show (S.one ≫ S.totalIncl 0) ≫ S.totalProj p ≫ _ = 0
    rw [CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc (S.totalIncl 0),
      S.totalIncl_totalProj_of_ne' (Ne.symm hp), CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  have e3 := congrArg (fun g : 𝟙_ ρ.source.toScheme.Modules ⟶ _ => g.app V (show Γ(ρ.source.toScheme, V) from 1)) e2
  have e4 : ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from 1) =
      (S.totalProj p ≫ AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D p).app V
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).inv.app V
          (show Γ((AlgebraicGeometry.Scheme.relativeSpec S.total).left,
            (AlgebraicGeometry.Scheme.relativeSpec S.total).hom ⁻¹ᵁ V) from 1)) := rfl
  exact e4.trans ((congrArg ((S.totalProj p ≫ AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D p).app V)
    e1).trans (e3.trans rfl))

/-- Functions pulled back from the base have pure ξ-degree `0`: for `a ∈ Γ(C̃, V)` and `p ≠ 0`,
`symCoeffHom L p (p^♯ a) = 0`. Indeed `p^♯ a = a • 1` in the `O_{C̃}`-module `p_*O_{Tot}` (the scalar action of
the pushforward is multiplication by `p^♯ a`), `symCoeffHom` is `O_{C̃}`-linear, and `symCoeffHom L p 1 = 0`. -/
theorem BasedJet.symCoeffHom_app_totalSpace_app_of_ne (L : LineBundle ρ.source.toVariety)
    (V : ρ.source.toScheme.Opens) (a : Γ(ρ.source.toScheme, V)) {p : ℕ} (hp : p ≠ 0) :
    ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom a) = 0 := by
  let one : Γ((AlgebraicGeometry.Scheme.Modules.pushforward
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf), V) :=
    show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from 1
  have hsmul : (show Γ((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf), V) from
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom a) = a • one :=
    (mul_one (((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom a)).symm
  refine (congrArg ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom hsmul).trans ?_
  refine (LinearMap.map_smul ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom a one).trans ?_
  exact (congrArg (fun t : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
    (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p, V) => a • t)
    (BasedJet.symCoeffHom_app_one_of_ne L V hp)).trans
    (smul_zero (M := Γ(ρ.source.toVariety.carrier, V)) (A := Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p, V)) a)

/-- `φ_J^♯ (π^♯ a)` has pure ξ-degree `0` for `a ∈ Γ(C, U)`: `φ_J ≫ π = p ≫ ρ` (`Over.w`), so
`φ_J^♯ (π^♯ a) = p^♯ (ρ^♯ a)`, and the previous lemma applies. -/
theorem BasedJet.symCoeffHom_jetPoint_app_of_ne (J : BasedJet f ρ L κ) (U : C.toScheme.Opens)
    (a : Γ(C.toScheme, U))
    (hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U))
    {p : ℕ} (hp : p ≠ 0) :
    ((BasedJet.symCoeffHom L p).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U))).hom
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) from
          (J.jetPoint.left.appLE
              ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U)
              ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U) hle).hom
            (((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.app U).hom
              a)) = 0 := by
  set π := (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom with hπ
  set Tot := AlgebraicGeometry.Scheme.totalSpace L.toModules with hTot
  have hle' : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U ≤ (J.jetPoint.left ≫ π) ⁻¹ᵁ U := hle
  have h1 : (J.jetPoint.left.appLE (π ⁻¹ᵁ U) ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U) hle).hom ((π.app U).hom a) =
      ((J.jetPoint.left ≫ π).appLE U ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U) hle').hom a := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_appLE]
    rfl
  have h2 : (J.jetPoint.left ≫ π).appLE U ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U) hle' =
      (Tot.hom ≫ ρ.hom).appLE U (Tot.hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) le_rfl :=
    AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (CategoryTheory.Over.w J.jetPoint) U _ hle' le_rfl
  have h3 : ((Tot.hom ≫ ρ.hom).appLE U (Tot.hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) le_rfl).hom a =
      (Tot.hom.app (ρ.hom ⁻¹ᵁ U)).hom ((ρ.hom.app U).hom a) :=
    (congrArg (fun g : Γ(C.toScheme, U) ⟶ Γ(Tot.left, Tot.hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) => g.hom a)
      (AlgebraicGeometry.Scheme.Hom.comp_appLE Tot.hom ρ.hom U (Tot.hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) le_rfl)).trans
      (congrArg (fun g : Γ(ρ.source.toScheme, ρ.hom ⁻¹ᵁ U) ⟶ Γ(Tot.left, Tot.hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) =>
        g.hom ((ρ.hom.app U).hom a))
        (AlgebraicGeometry.Scheme.Hom.app_eq_appLE Tot.hom).symm)
  have h4 := BasedJet.symCoeffHom_app_totalSpace_app_of_ne L (ρ.hom ⁻¹ᵁ U) ((ρ.hom.app U).hom a) hp
  refine Eq.trans ?_ h4
  exact congrArg ((BasedJet.symCoeffHom L p).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U))).hom
    (h1.trans ((congrArg (fun g => g.hom a) h2).trans h3))

/-- `frameHom L q t` has pure ξ-degree `q` (`frameHom_symCoeffHom_of_ne` at sections). -/
theorem BasedJet.symCoeffHom_frameHom_app_of_ne (L : LineBundle ρ.source.toVariety) (V : ρ.source.toScheme.Opens)
    {q p : ℕ} (h : p ≠ q)
    (t : ((AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
      q).val.obj (Opposite.op V) : Type u)) :
    ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
        (((BasedJet.frameHom L q).val.app (Opposite.op V)).hom t) = 0 :=
  congrArg (fun g : AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
      q ⟶ AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p =>
    (g.val.app (Opposite.op V)).hom t) (BasedJet.frameHom_symCoeffHom_of_ne L (Ne.symm h))

/-- The jet coordinate `d_q b = χ_U (X (q, b))` (`coeffClass_succ`) is sent by `φ_J^♯` to an element of pure
ξ-degree `q + 1`: `χ_U y = (eqToHom hU)^* (chartSections U y)` (`chartEquiv_eq_chartSections`),
`φ_J^♯ (d_q b) = frameHom (q+1) (pieceSection …)` (`jetPoint_appLE_jetCoordinate`, LE-jet-coordinate),
and `frameHom (q+1)` lands in ξ-degree `q + 1`. -/
theorem BasedJet.symCoeffHom_jetPoint_chartEquiv_X_of_ne (J : BasedJet f ρ L κ) (U : C.toScheme.AffineZariskiSite)
    (hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1 ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1))
    (q : Fin κ) (b : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1)) {p : ℕ} (hp : p ≠ (q : ℕ) + 1) :
    letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) U.1
    ((BasedJet.symCoeffHom L p).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) from
          (J.jetPoint.left.appLE
              ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
              ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom
            (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U
              (Ideal.Quotient.mk
                (BasedJetAlgebra.relations
                  (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ)
                (MvPolynomial.X (q, b))))) = 0 := by
  let _ := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) U.1
  have hU := relativeJetScheme.preimage_eq_chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ U
  have h0 : BasedJetAlgebra.coeffClass
      (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ ((q : ℕ) + 1) b =
      Ideal.Quotient.mk (BasedJetAlgebra.relations
        (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ)
        (MvPolynomial.X (q, b)) :=
    BasedJetAlgebra.coeffClass_succ _ κ (q : ℕ) q.2 b
  have h1 := relativeJetScheme.chartEquiv_eq_chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ U hU
    (BasedJetAlgebra.coeffClass
      (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ ((q : ℕ) + 1) b)
  have h2 := J.jetPoint_appLE_jetCoordinate U q b hU hle
  rw [← h0, h1]
  refine (congrArg ((BasedJet.symCoeffHom L p).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom h2).trans ?_
  exact BasedJet.symCoeffHom_frameHom_app_of_ne L (ρ.hom ⁻¹ᵁ U.1) hp _

/-- The ξ-coefficient maps `symCoeffHom L p` on `Γ(Tot(L), p⁻¹V)`, packaged as additive maps (the input of the pure
algebra in `JetProjectivizePureDegree`). -/
def BasedJet.symCoeffAddHom (L : LineBundle ρ.source.toVariety) (V : ρ.source.toScheme.Opens) (p : ℕ) :
    Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) →+
      ((AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p).val.obj
        (Opposite.op V) : Type u) where
  toFun t := ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
    (show (((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
          (Opposite.op V) : Type u) from t)
  map_zero' := map_zero ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
  map_add' a b := map_add ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom a b

theorem BasedJet.symCoeffAddHom_apply (L : LineBundle ρ.source.toVariety) (V : ρ.source.toScheme.Opens) (p : ℕ)
    (t : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) :
    BasedJet.symCoeffAddHom L V p t = ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
      (show (((AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
            (Opposite.op V) : Type u) from t) := rfl

/-- `PureDegree.IsPure (symCoeffAddHom L V) m t` unfolds to "all ξ-coefficients of `t` other than the `m`-th vanish"
(the hypothesis form of `BasedJet.symCoeffHom_mul_of_homogeneous`). -/
theorem BasedJet.isPure_symCoeffAddHom_iff (L : LineBundle ρ.source.toVariety) (V : ρ.source.toScheme.Opens) (m : ℕ)
    (t : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) :
    PureDegree.IsPure (BasedJet.symCoeffAddHom L V) m t ↔
      ∀ p : ℕ, p ≠ m → ((BasedJet.symCoeffHom L p).val.app (Opposite.op V)).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
            (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
              (Opposite.op V) : Type u) from t) = 0 :=
  Iff.rfl

end
