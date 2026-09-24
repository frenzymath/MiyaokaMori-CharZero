import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeilUniqueHelpers
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleLocalEquation
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.CurveStalkFunctionField

/-! # Pullback of Cartier divisors along a dominant morphism

The pullback `f^*D` of a Cartier divisor along a dominant morphism: pull back the local equations
along `f`. Sources: Stacks 02OO(2) (the pullback of Cartier divisors along a dominant morphism of
integral schemes is defined); Hartshorne II.6. Used for `f^*(-K_X)` in the degree identity of
Theorem 1.1 of the paper.

**Construction (choice-free).** `f^*D` is glued from the pulled-back local equations
`(f⁻¹U, f^♮ t)` of `D`, where `(U, t)` runs over **all** local equations of `D` (`U ≠ ∅`, `t ∈ 𝒦_Y^*(U)`,
`[t] = D|_U`: `CartierDivisor.LocalEquationIndex D`), and `f^♮ = AlgebraicGeometry.Scheme.dominantFunctionFieldMap f : K(Y) → K(X)`
(surjective on points ⇒ dominant). This universal family is local data of `D` (`isLocalData_localEquation`), so no
choice is made in the body; choosing *one* family of local data with `Classical.epsilon` instead gives the
same divisor (`pullback_eq_epsilon_localData`). The user-facing API is `pullback_ofLocalData`:
`f^*(ofLocalData U g) = ofLocalData (f⁻¹U) (f^♮ g)` for every local data `(U, g)` — this is the well-definedness of
Stacks 02OO(2): any local data of `D` pull back to the same divisor.

Uniqueness lemma behind it (`eq_ofLocalData_of_forall_isLocalEquation`): a Cartier divisor `E` having, on each
nonempty member `U_i` of local data `(U, g)`, a local equation with generic value `g_i`, equals `ofLocalData U g`
(sheaf separatedness of `𝒦^*/O^*` over the cover + injectivity of `𝒦^*(U_i) → K(Y)^*`, Stacks 01X5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CartierDivisor

variable {k : Type u} [Field k]

/-- The canonical local data of `D`: all pairs `(U, t)` with `U ≠ ∅` and `t ∈ 𝒦^*(U)` a local equation of
`D` on `U` (`IsLocalEquation D U t`, i.e. `[t] = D|_U`). -/
def LocalEquationIndex {Y : Variety k} (D : CartierDivisor Y) : Type u :=
  {p : Σ U : Y.toScheme.Opens, Y.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U) //
    Nonempty p.1 ∧ IsLocalEquation D p.1 p.2}

/-- The open set of a canonical local datum. -/
def localEquationOpens {Y : Variety k} (D : CartierDivisor Y) (i : D.LocalEquationIndex) :
    Y.toScheme.Opens :=
  i.1.1

/-- The generic value `t(η) ∈ K(Y)^*` of a canonical local datum `(U, t)`. -/
def localEquationValue {Y : Variety k} (D : CartierDivisor Y) (i : D.LocalEquationIndex) :
    (Y.toScheme.functionField)ˣ :=
  haveI : Nonempty i.1.1 := i.2.1
  Y.toScheme.rationalUnitsSectionToFunctionField i.1.1 i.1.2

/-- Two local equations of `D` (on `U`, `V`) have a stalk-unit ratio at every point of `U ⊓ V`:
`[s|_W] = D|_W = [t|_W]` on `W = U ⊓ V`, so `s/t` is locally a unit of `O_Y` (`local_unit_ratio_eq`). -/
theorem isLocalEquation_ratio_mem_range {Y : Variety k} {D : CartierDivisor Y}
    {U V : Y.toScheme.Opens} [Nonempty U] [Nonempty V]
    {s : Y.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)}
    {t : Y.toScheme.rationalFunctionsUnitsSheaf.val.obj (op V)}
    (hs : IsLocalEquation D U s) (ht : IsLocalEquation D V t) (x : Y.toScheme) (hx : x ∈ U ⊓ V) :
    ((Y.toScheme.rationalUnitsSectionToFunctionField U s /
        Y.toScheme.rationalUnitsSectionToFunctionField V t : (Y.toScheme.functionField)ˣ) :
          Y.toScheme.functionField) ∈
      Set.range (fun v : (Y.toScheme.presheaf.stalk x)ˣ =>
        algebraMap (Y.toScheme.presheaf.stalk x) Y.toScheme.functionField v) := by
  have hW : Nonempty (U ⊓ V : Y.toScheme.Opens) := ⟨⟨x, hx⟩⟩
  have hs' := hs.restrict (inf_le_left : U ⊓ V ≤ U)
  have ht' := ht.restrict (inf_le_right : U ⊓ V ≤ V)
  obtain ⟨W', hW'W, hxW', a, ha⟩ :=
    CartierToWeilQuotientUnitRatio.local_unit_ratio_eq (V := Y) hW x hx
      (Y.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE inf_le_left).op s)
      (Y.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE inf_le_right).op t)
      (hs'.symm.trans ht')
  rw [Y.toScheme.rationalUnitsSectionToFunctionField_res U _ inf_le_left,
    Y.toScheme.rationalUnitsSectionToFunctionField_res V _ inf_le_right] at ha
  refine ⟨a, ha.trans ?_⟩
  exact (Units.val_div_eq_div_val _ _).symm

/-- A covering family of local equations of `D` is local data (cover given; ratios by
`isLocalEquation_ratio_mem_range`). -/
theorem isLocalData_of_isLocalEquation {Y : Variety k} {D : CartierDivisor Y} {ι : Type u}
    (U : ι → Y.toScheme.Opens) (t : ∀ i, Y.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (U i)))
    (hne : ∀ i, Nonempty (U i)) (ht : ∀ i, IsLocalEquation D (U i) (t i))
    (hcov : (⨆ i, U i) = ⊤) :
    IsLocalData U (fun i =>
      haveI := hne i
      Y.toScheme.rationalUnitsSectionToFunctionField (U i) (t i)) := by
  refine ⟨hcov, fun i j x hx => ?_⟩
  have := hne i
  have := hne j
  exact ⟨isLocalEquation_ratio_mem_range (ht i) (ht j) x hx,
    isLocalEquation_ratio_mem_range (ht j) (ht i) x ⟨hx.2, hx.1⟩⟩

/-- **Uniqueness through local equations.** If `(U, g)` is local data and `E` has, on every nonempty
`U_i`, a local equation with generic value `g_i`, then `E = ofLocalData U g`. Proof: `ofLocalData U g`
has such local equations too (`local_section_ofLocalData`); on each nonempty `U_i` the two local
equations have the same generic value, hence coincide (`rationalUnitsSectionToFunctionField_injective`,
Stacks 01X5), so `E|_{U_i} = (ofLocalData U g)|_{U_i}`; the nonempty `U_i` cover `Y`, and `𝒦^*/O^*` is a
sheaf (`eq_of_locally_eq'`). -/
theorem eq_ofLocalData_of_forall_isLocalEquation {Y : Variety k} {ι : Type u}
    {U : ι → Y.toScheme.Opens} {g : ι → (Y.toScheme.functionField)ˣ} (hUg : IsLocalData U g)
    (E : CartierDivisor Y)
    (hE : ∀ i, ∀ hne : Nonempty (U i),
      ∃ t : Y.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (U i)),
        (haveI := hne; Y.toScheme.rationalUnitsSectionToFunctionField (U i) t) = g i ∧
        IsLocalEquation E (U i) t) :
    E = ofLocalData U g := by
  let Q := TopCat.Sheaf.quotient (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits Y.toScheme)
  let π := TopCat.Sheaf.quotientπ (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits Y.toScheme)
  let ι' := {i : ι // Nonempty (U i)}
  have hcov : (⊤ : Y.toScheme.Opens) ≤ ⨆ i : ι', U i.1 := by
    intro x _
    have hx : x ∈ (⨆ i, U i : Y.toScheme.Opens) := by rw [hUg.1]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨x, hi⟩⟩⟩, hi⟩
  have h : Additive.toMul E = Additive.toMul (ofLocalData U g) := by
    apply Q.eq_of_locally_eq' (fun i : ι' => U i.1) ⊤ (fun i => homOfLE le_top) hcov
    intro i
    have := i.2
    obtain ⟨⟨x, hx⟩⟩ := i.2
    obtain ⟨t, ht, hEt⟩ := hE i.1 i.2
    obtain ⟨t', ht', hOt'⟩ :=
      CartierToWeilLocalSection.local_section_ofLocalData U g hUg x i.1 hx
    have htt : t = t' :=
      Y.toScheme.rationalUnitsSectionToFunctionField_injective (U i.1) (ht.trans ht'.symm)
    exact hEt.trans ((congrArg (π.hom.app (op (U i.1))) htt).trans hOt'.symm)
  exact congrArg Additive.ofMul h

/-- A stalk-unit ratio pulls back to a stalk-unit ratio along a dominant morphism. -/
theorem mem_range_algebraMap_pullback {X Y : Variety k} (f : X.toScheme ⟶ Y.toScheme)
    [AlgebraicGeometry.IsDominant f] (x : X.toScheme) {a b : (Y.toScheme.functionField)ˣ}
    (h : ((a / b : (Y.toScheme.functionField)ˣ) : Y.toScheme.functionField) ∈
      Set.range (fun v : (Y.toScheme.presheaf.stalk (f.base x))ˣ =>
        algebraMap (Y.toScheme.presheaf.stalk (f.base x)) Y.toScheme.functionField v)) :
    ((Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom a /
        Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom b :
          (X.toScheme.functionField)ˣ) : X.toScheme.functionField) ∈
      Set.range (fun v : (X.toScheme.presheaf.stalk x)ˣ =>
        algebraMap (X.toScheme.presheaf.stalk x) X.toScheme.functionField v) := by
  obtain ⟨v, hv⟩ := h
  have hv' : algebraMap (Y.toScheme.presheaf.stalk (f.base x)) Y.toScheme.functionField v =
      ((a / b : (Y.toScheme.functionField)ˣ) : Y.toScheme.functionField) := hv
  refine ⟨Units.map (f.stalkMap x).hom.toMonoidHom v, ?_⟩
  show algebraMap (X.toScheme.presheaf.stalk x) X.toScheme.functionField
      ((Units.map (f.stalkMap x).hom.toMonoidHom v : (X.toScheme.presheaf.stalk x)ˣ) :
        X.toScheme.presheaf.stalk x) = _
  rw [← map_div, Units.coe_map, Units.coe_map]
  change algebraMap (X.toScheme.presheaf.stalk x) X.toScheme.functionField (f.stalkMap x v) =
    AlgebraicGeometry.Scheme.dominantFunctionFieldMap f ((a / b : (Y.toScheme.functionField)ˣ) :
      Y.toScheme.functionField)
  rw [← hv']
  exact (AlgebraicGeometry.Scheme.dominantFunctionFieldMap_algebraMap f x v).symm

/-- **Pullback of local data is local data** (Stacks 02OO(2)): cover `⨆ f⁻¹U_i = f⁻¹⊤ = ⊤`; ratios by
`mem_range_algebraMap_pullback`. -/
theorem IsLocalData.pullback {X Y : Variety k} (f : X.toScheme ⟶ Y.toScheme)
    [AlgebraicGeometry.IsDominant f] {ι : Type u} {U : ι → Y.toScheme.Opens}
    {g : ι → (Y.toScheme.functionField)ˣ} (hUg : IsLocalData U g) :
    IsLocalData (fun i => f ⁻¹ᵁ U i)
      (fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i)) := by
  refine ⟨?_, ?_⟩
  · rw [← AlgebraicGeometry.Scheme.Hom.preimage_iSup, hUg.1,
      AlgebraicGeometry.Scheme.Hom.preimage_top]
  · intro i j x hx
    have hfx : f.base x ∈ U i ⊓ U j := hx
    obtain ⟨h1, h2⟩ := hUg.2 i j (f.base x) hfx
    exact ⟨mem_range_algebraMap_pullback f x h1, mem_range_algebraMap_pullback f x h2⟩

end CartierDivisor

/-- The pullback `f^*D` of a Cartier divisor along a morphism that is surjective on points (hence
dominant). All local equations `(U, t)` of `D` (`U ≠ ∅`, `t ∈ 𝒦^*(U)`, `[t] = D|_U`; index set
`CartierDivisor.LocalEquationIndex D`) are pulled back to `(f⁻¹U, f^♮ t(η))` and glued with
`ofLocalData`, where `f^♮ : K(Y) → K(X)` is `AlgebraicGeometry.Scheme.dominantFunctionFieldMap`. This family is local
data of `D` (`isLocalData_localEquation`), and the result agrees with the pullback of any family of
local data (`pullback_ofLocalData`). -/

noncomputable def CartierDivisor.pullback {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) (hf : Function.Surjective f.base) (D : CartierDivisor Y) :
    CartierDivisor X :=
  haveI : AlgebraicGeometry.IsDominant f := ⟨hf.denseRange⟩
  CartierDivisor.ofLocalData (fun i : D.LocalEquationIndex => f ⁻¹ᵁ D.localEquationOpens i)
    (fun i : D.LocalEquationIndex =>
      Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (D.localEquationValue i))

namespace CartierDivisor

variable {k : Type u} [Field k]

/-- The canonical local data of `D` cover `Y` (every point has a local equation,
`exists_isLocalEquation`). -/
theorem iSup_localEquationOpens {Y : Variety k} (D : CartierDivisor Y) :
    (⨆ i, D.localEquationOpens i) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨U, hxU, g, hg⟩ := exists_isLocalEquation D x
  exact Opens.mem_iSup.mpr ⟨⟨⟨U, g⟩, ⟨⟨x, hxU⟩⟩, hg⟩, hxU⟩

/-- The canonical local data of `D` are local data. -/
theorem isLocalData_localEquation {Y : Variety k} (D : CartierDivisor Y) :
    IsLocalData D.localEquationOpens D.localEquationValue :=
  isLocalData_of_isLocalEquation D.localEquationOpens (fun i => i.1.2) (fun i => i.2.1)
    (fun i => i.2.2) D.iSup_localEquationOpens

/-- `D` is glued from its canonical local data. -/
theorem eq_ofLocalData_localEquation {Y : Variety k} (D : CartierDivisor Y) :
    D = ofLocalData D.localEquationOpens D.localEquationValue :=
  eq_ofLocalData_of_forall_isLocalEquation D.isLocalData_localEquation D
    (fun i _ => ⟨i.1.2, rfl, i.2.2⟩)

/-- **Well-definedness of the pullback** (Stacks 02OO(2)): for any local data `(U, g)`,
`f^*(ofLocalData U g) = ofLocalData (f⁻¹U_i) (f^♮ g_i)`. Proof: by uniqueness through local equations
(`eq_ofLocalData_of_forall_isLocalEquation`, applied to the pulled-back data, which is local data by
`IsLocalData.pullback`) it suffices to give, on each nonempty `f⁻¹U_i`, a local equation of `f^*D` with
generic value `f^♮ g_i`. Take a local equation `s ∈ 𝒦_Y^*(U_i)` of `D := ofLocalData U g` with value `g_i`
(`local_section_ofLocalData`); then `(U_i, s)` is a canonical local datum `p` of `D`, and `f^*D`, being
`ofLocalData` of the pulled-back canonical data, has on `f⁻¹U_i` a local equation with value
`f^♮ (value p) = f^♮ g_i` (`local_section_ofLocalData` again). -/
theorem pullback_ofLocalData {X Y : Variety k} (f : X.toScheme ⟶ Y.toScheme)
    (hf : Function.Surjective f.base) [AlgebraicGeometry.IsDominant f] {ι : Type u}
    {U : ι → Y.toScheme.Opens}
    {g : ι → (Y.toScheme.functionField)ˣ} (hUg : IsLocalData U g) :
    pullback f hf (ofLocalData U g) =
      ofLocalData (fun i => f ⁻¹ᵁ U i)
        (fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i)) := by
  have hcan := IsLocalData.pullback f (ofLocalData U g).isLocalData_localEquation
  apply eq_ofLocalData_of_forall_isLocalEquation (IsLocalData.pullback f hUg)
  intro i hne
  rcases id hne with ⟨⟨x, hx⟩⟩
  have hyi : f.base x ∈ U i := hx
  obtain ⟨s, hs, hDs⟩ := CartierToWeilLocalSection.local_section_ofLocalData U g hUg (f.base x) i hyi
  let p : (ofLocalData U g).LocalEquationIndex := ⟨⟨U i, s⟩, ⟨⟨f.base x, hyi⟩⟩, hDs⟩
  obtain ⟨t, ht, hEt⟩ := CartierToWeilLocalSection.local_section_ofLocalData _ _ hcan x p hx
  refine ⟨t, ht.trans ?_, hEt⟩
  exact congrArg (Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom) hs

/-- Choosing *some* local data `d` of `D` with `Classical.epsilon` and pulling it back gives the same
divisor (`cartierDivisor_exists_localData` + `pullback_ofLocalData`). -/
theorem pullback_eq_epsilon_localData {X Y : Variety k} (f : X.toScheme ⟶ Y.toScheme)
    (hf : Function.Surjective f.base) (D : CartierDivisor Y) :
    pullback f hf D =
      (haveI : AlgebraicGeometry.IsDominant f := ⟨hf.denseRange⟩
       let d := @Classical.epsilon
         (Σ ι : Type u, (ι → Y.toScheme.Opens) × (ι → (Y.toScheme.functionField)ˣ))
         ⟨⟨PEmpty, fun e => e.elim, fun e => e.elim⟩⟩
         (fun d => IsLocalData d.2.1 d.2.2 ∧ D = ofLocalData d.2.1 d.2.2)
       ofLocalData (fun i : d.1 => f ⁻¹ᵁ d.2.1 i)
         (fun i : d.1 => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (d.2.2 i))) := by
  have : AlgebraicGeometry.IsDominant f := ⟨hf.denseRange⟩
  have hex : ∃ d : (Σ ι : Type u, (ι → Y.toScheme.Opens) × (ι → (Y.toScheme.functionField)ˣ)),
      IsLocalData d.2.1 d.2.2 ∧ D = ofLocalData d.2.1 d.2.2 := by
    obtain ⟨ι, U, g, h1, h2⟩ := cartierDivisor_exists_localData Y D
    exact ⟨⟨ι, U, g⟩, h1, h2⟩
  have key := Classical.epsilon_spec hex
  exact (congrArg (pullback f hf) key.2).trans (pullback_ofLocalData f hf key.1)

end CartierDivisor

end
