import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleSections
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafLocalRange

/-! # Sections of `O_X(D)` in terms of a local equation

Let `t ∈ 𝒦^*(U)` be a local equation of the Cartier divisor `D` on `U` (`[t] = D|_U`, `IsLocalEquation`).
Then for `W ⊆ U` and `h ∈ 𝒦(W)`: `h ∈ O_X(D)(W)` iff `h·t|_W ∈ O_X(W)` (`L(D)|_U = t^{-1}·O_U`). Every
point has a local equation nearby (the quotient map is locally surjective).

Proof:
1. (`⇐`) Take `W` itself as the neighbourhood and `t|_W` as the local equation (`localEquation_restrict`).
2. (`⇒`) Near every point there is a local equation `g` with `h·g ∈ O`; `g` and `t` are both local
   equations of `D`, so on a smaller neighbourhood they differ by a section of `O`
   (`exists_unit_of_quotientπ_eq`), hence `h·t` lies locally in `O`.
3. The image of `O` in `𝒦` is a subsheaf (`RationalFunctionsSheafLocalRange`), so `h·t` lies in `O(W)`.
Source: Hartshorne II.6.13(a).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CartierDivisor

variable {k : Type u} [Field k] {X : Variety k}

/-- A section of `𝒦^*(U)` viewed as an element of `𝒦(U)` (the same spelling as in the definition of
`lineBundleSections`). -/
abbrev unitVal {U : X.toScheme.Opens}
    (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    X.toScheme.rationalFunctionsSheaf.val.obj (op U) :=
  ((show (X.toScheme.rationalFunctionsSheaf.val.obj (op U))ˣ from g) :
    X.toScheme.rationalFunctionsSheaf.val.obj (op U))

/-- `g ∈ 𝒦^*(U)` is a local equation of `D` on `U`: `[g] = D|_U ∈ (𝒦^*/O^*)(U)`. -/
def IsLocalEquation (D : CartierDivisor X) (U : X.toScheme.Opens)
    (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) : Prop :=
  (TopCat.Sheaf.quotient
      (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).val.map
      (homOfLE (show U ≤ ⊤ from le_top)).op (Additive.toMul D) =
    (TopCat.Sheaf.quotientπ
      (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme)).hom.app (op U) g

/-- Every point has a local equation nearby (the quotient map is locally surjective). -/
theorem exists_isLocalEquation (D : CartierDivisor X) (x : X.toScheme) :
    ∃ (U : X.toScheme.Opens) (_ : x ∈ U)
      (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)), IsLocalEquation D U g := by
  obtain ⟨U, hxU, hUW, g, hg⟩ := TopCat.Sheaf.quotientπ_exists_local
    (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme) ⊤
    (Additive.toMul D) x trivial
  exact ⟨U, hxU, g, hg⟩

theorem IsLocalEquation.restrict {D : CartierDivisor X} {U V : X.toScheme.Opens}
    {g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)} (hg : IsLocalEquation D U g)
    (hVU : V ≤ U) :
    IsLocalEquation D V (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVU).op g) :=
  CartierDivisor.localEquation_restrict D hVU g hg

theorem unitVal_restrict {U V : X.toScheme.Opens} (hVU : V ≤ U)
    (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    unitVal (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVU).op g) =
      (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom (unitVal g) := rfl

/-- Characterization of sections (Hartshorne II.6.13): on the domain of a local equation `t`,
`h ∈ O_X(D)(W) ⟺ h·t|_W ∈ O_X(W)`. -/
theorem IsLocalEquation.mem_lineBundleSections_iff {D : CartierDivisor X} {U W : X.toScheme.Opens}
    {t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)} (ht : IsLocalEquation D U t)
    (hWU : W ≤ U) (h : X.toScheme.rationalFunctionsSheaf.val.obj (op W)) :
    h ∈ CartierDivisor.lineBundleSections D W ↔
      h * unitVal (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t) ∈
        Set.range (X.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom := by
  constructor
  · intro hh
    apply X.toScheme.mem_range_toRationalFunctionsSheaf_of_locally W
    intro x hx
    obtain ⟨V, hxV, hVW, g, hg, a, ha⟩ := hh x hx
    have hEq := (ht.restrict (hVW.trans hWU)).symm.trans hg
    obtain ⟨V', hxV', hV'V, c, hc⟩ := CartierDivisor.exists_unit_of_quotientπ_eq _ g hEq x hxV
    refine ⟨V', hxV', hV'V.trans hVW,
      c * (X.toScheme.presheaf.map (homOfLE hV'V).op).hom a, ?_⟩
    have hta : (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (hV'V.trans hVW)).op).hom
        (unitVal (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t)) =
        (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hV'V).op).hom
          (unitVal (X.toScheme.rationalFunctionsUnitsSheaf.val.map
            (homOfLE (hVW.trans hWU)).op t)) := by
      rw [unitVal_restrict, unitVal_restrict]
      exact (X.toScheme.rationalFunctionsSheaf_map_map hWU (hV'V.trans hVW) (unitVal t)).trans
        (X.toScheme.rationalFunctionsSheaf_map_map (hVW.trans hWU) hV'V (unitVal t)).symm
    have hha : (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (hV'V.trans hVW)).op).hom h =
        (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hV'V).op).hom
          ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVW).op).hom h) :=
      (X.toScheme.rationalFunctionsSheaf_map_map hVW hV'V h).symm
    let ι' := (X.toScheme.toRationalFunctionsSheaf.hom.app (op V')).hom
    let KV' := (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hV'V).op).hom
    let KW' := (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (hV'V.trans hVW)).op).hom
    let hV := (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVW).op).hom h
    have e1 : ι' (c * (X.toScheme.presheaf.map (homOfLE hV'V).op).hom a) =
        ι' c * KV' (hV * unitVal g) :=
      (ι'.map_mul _ _).trans (congrArg (fun z => ι' c * z)
        ((X.toScheme.toRationalFunctionsSheaf_res hV'V a).trans (congrArg KV' ha)))
    have e2 : ι' c * KV' (hV * unitVal g) = KV' hV * (ι' c * KV' (unitVal g)) := by
      rw [KV'.map_mul]; ring
    have e3 : KV' hV * (ι' c * KV' (unitVal g)) =
        KW' h * KW' (unitVal (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t)) := by
      rw [hha, hta]
      exact congrArg (fun z => KV' hV * z) hc.symm
    exact (e1.trans (e2.trans e3)).trans (KW'.map_mul _ _).symm
  · intro hh x hx
    refine ⟨W, hx, le_rfl, _, ht.restrict hWU, ?_⟩
    have hid : (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (le_refl W)).op).hom h = h := by
      have : (homOfLE (le_refl W)).op = 𝟙 (op W) := rfl
      rw [this, X.toScheme.rationalFunctionsSheaf.val.map_id]; rfl
    rw [hid]
    exact hh

end CartierDivisor

end
