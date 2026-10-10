import GradedQuotient
import BlowupProjective

/-!
# ブローアップ(層7: `Scheme` としての構成)

体 `k` 上、`𝔸² × ℙ¹` の座標環 `k[x, y, t, u]`(`(t, u)` に次数 1、`x, y` に次数 0 の重み付き次数)を
斉次イデアル `(x u − t y)` で割った次数付き環 `B` を作り、`Proj B` を `Scheme` として
ブローアップ `Bl₀ 𝔸²` とみなす。構造射 `Proj B ⟶ Spec (B₀)` は `Proj.toSpecZero`。

ここでは構成と、`B₀` の元としての `x, y`、斉次イデアルの証明を与える。
-/

open MvPolynomial AlgebraicGeometry

universe u

namespace Blowup

section scheme

variable (k : Type u) [Field k]

/-- 重み `x, y ↦ 0`、`t, u ↦ 1`。 -/
def wt : Fin 4 → ℕ := ![0, 0, 1, 1]

/-- `k[x, y, t, u]` の `(t, u)` についての次数付け。 -/
noncomputable def bigrading : ℕ → Submodule k (MvPolynomial (Fin 4) k) :=
  weightedHomogeneousSubmodule k wt

noncomputable instance : GradedAlgebra (bigrading k) := weightedGradedAlgebra k wt

/-- ブローアップを定めるイデアル `(x u − t y)`。 -/
noncomputable def blowIdeal : Ideal (MvPolynomial (Fin 4) k) := Ideal.span {blowEq k}

lemma blowEq_mem_bigrading : blowEq k ∈ bigrading k 1 := by
  have h03 : wt 0 + wt 3 = 1 := rfl
  have h21 : wt 2 + wt 1 = 1 := rfl
  have h1 := (isWeightedHomogeneous_X k wt 0).mul (isWeightedHomogeneous_X k wt 3)
  have h2 := (isWeightedHomogeneous_X k wt 2).mul (isWeightedHomogeneous_X k wt 1)
  rw [h03] at h1
  rw [h21] at h2
  exact Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2)

lemma blowIdeal_homogeneous (i : ℕ) (r : MvPolynomial (Fin 4) k) (hr : r ∈ blowIdeal k) :
    (DirectSum.decompose (bigrading k) r i : MvPolynomial (Fin 4) k) ∈ blowIdeal k := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [DirectSum.coe_decompose_mul_of_right_mem (bigrading k) i (blowEq_mem_bigrading k)]
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exact Ideal.zero_mem _

/-- 座標環 `B = k[x, y, t, u] / (x u − t y)`。 -/
abbrev BlowRing : Type u := MvPolynomial (Fin 4) k ⧸ blowIdeal k

/-- `B` の次数付け。 -/
noncomputable abbrev blowGrading : ℕ → Submodule k (BlowRing k) :=
  GradedQuotient.grading (bigrading k) (blowIdeal k)

noncomputable instance : GradedRing (blowGrading k) :=
  GradedQuotient.gradedRing (blowIdeal_homogeneous k)

/-- **`Scheme` としてのブローアップ `Proj B`**。 -/
noncomputable def blowupScheme : Scheme.{u} := Proj (blowGrading k)

/-- 構造射 `Proj B ⟶ Spec B₀`(`B₀` は次数 0 の部分環で、`k[x, y]` に当たる)。 -/
noncomputable def blowupMap : blowupScheme k ⟶ Spec (CommRingCat.of (blowGrading k 0)) :=
  Proj.toSpecZero (blowGrading k)


/-! ### 固有性と `k[x, y]` からの単射 -/

open Classical in
/-- `B` は `B₀` 上、`t, u` で生成される(有限型)。 -/
instance blowRing_finiteType : Algebra.FiniteType (blowGrading k 0) (BlowRing k) := by
  refine ⟨⟨{Ideal.Quotient.mk (blowIdeal k) (X 2), Ideal.Quotient.mk (blowIdeal k) (X 3)}, ?_⟩⟩
  rw [eq_top_iff]
  rintro b -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h0 : ∀ q : MvPolynomial (Fin 4) k, q ∈ bigrading k 0 →
      Ideal.Quotient.mk (blowIdeal k) q ∈ Algebra.adjoin (blowGrading k 0)
        (({Ideal.Quotient.mk (blowIdeal k) (X 2), Ideal.Quotient.mk (blowIdeal k) (X 3)} :
          Finset (BlowRing k)) : Set (BlowRing k)) := fun q hq =>
    Subalgebra.algebraMap_mem _ (⟨Ideal.Quotient.mk (blowIdeal k) q, GradedQuotient.mem_grading hq⟩ :
      blowGrading k 0)
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact h0 _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_C wt c))
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | mul_X a i ha =>
    rw [map_mul]
    refine mul_mem ha ?_
    fin_cases i
    · exact h0 _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_X k wt 0 : IsWeightedHomogeneous wt (X 0 : MvPolynomial (Fin 4) k) 0))
    · exact h0 _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_X k wt 1 : IsWeightedHomogeneous wt (X 1 : MvPolynomial (Fin 4) k) 0))
    · exact Algebra.subset_adjoin (by simp)
    · exact Algebra.subset_adjoin (by simp)

/-- **ブローアップは `Spec B₀` 上固有**(`Mathlib` の `Proj` の固有性から)。 -/
instance blowupMap_isProper : IsProper (blowupMap k) :=
  inferInstanceAs (IsProper (Proj.toSpecZero (blowGrading k)))

/-- `k[x, y] → B`。 -/
noncomputable def xyToBlow : MvPolynomial (Fin 2) k →ₐ[k] BlowRing k :=
  (Ideal.Quotient.mkₐ k (blowIdeal k)).comp
    (MvPolynomial.aeval (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 4) k))

/-- `t ↦ x`、`u ↦ y` の代入。`(x u − t y)` を消す。 -/
noncomputable def blowSpecialize : MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (![X 0, X 1, X 0, X 1] : Fin 4 → MvPolynomial (Fin 2) k)

lemma blowSpecialize_blowEq : blowSpecialize k (blowEq k) = 0 := by
  rw [blowEq, blowSpecialize, map_sub, map_mul, map_mul, aeval_X, aeval_X, aeval_X, aeval_X]
  exact sub_self _

lemma blowSpecialize_blowIdeal {z : MvPolynomial (Fin 4) k} (hz : z ∈ blowIdeal k) :
    blowSpecialize k z = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  rw [map_mul, blowSpecialize_blowEq, mul_zero]

lemma blowSpecialize_comp (f : MvPolynomial (Fin 2) k) :
    blowSpecialize k (MvPolynomial.aeval (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 4) k) f) = f := by
  have h : (blowSpecialize k).comp
      (MvPolynomial.aeval (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 4) k)) = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · rw [AlgHom.comp_apply, aeval_X]
      change blowSpecialize k (X 0) = X 0
      exact aeval_X _ _
    · rw [AlgHom.comp_apply, aeval_X]
      change blowSpecialize k (X 1) = X 1
      exact aeval_X _ _
  exact congrArg (fun φ => φ f) h

/-- **`k[x, y] → B` は単射**(`B₀ ⊇ k[x, y]`;ブローアップは `𝔸²` の上にある)。 -/
theorem xyToBlow_injective : Function.Injective (xyToBlow k) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hmem : MvPolynomial.aeval (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 4) k) f ∈ blowIdeal k :=
    Ideal.Quotient.eq_zero_iff_mem.mp hf
  have := blowSpecialize_blowIdeal k hmem
  rwa [blowSpecialize_comp] at this
end scheme

end Blowup
