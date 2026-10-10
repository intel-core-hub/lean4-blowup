import Mathlib

/-!
# ブローアップ(層1: 多項式)

`n = 2`、チャート `t = 1`(`y = x * u`)での計算を形式化する。

* `sub f = f(x, x * u)`  (`x = X 0`, `y = u = X 1`)
* `f` の `(0,0)` での重複度が `r` のとき `f(x, x u) = x^r * f̃`、かつ `X 0 ∤ f̃`
-/

open MvPolynomial

set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

namespace Blowup

variable {R : Type*} [CommRing R]

/-- `R[x,y]`。`x = X 0`, `y = X 1`。 -/
abbrev Poly (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R

/-- 単項式の全次数 `a + b`。 -/
def deg (s : Fin 2 →₀ ℕ) : ℕ := s 0 + s 1

/-- 原点での重複度:支持の全次数の最小値(`f = 0` のときは `0`)。 -/
noncomputable def mult (f : Poly R) : ℕ := sInf (deg '' (f.support : Set (Fin 2 →₀ ℕ)))

/-- チャート `y = x * u` への代入 `f(x, x u)`。 -/
noncomputable def sub : Poly R →ₐ[R] Poly R := aeval ![X 0, X 0 * X 1]

/-- 指数 `(a, b)` を `x^a y^b` に対応させる。 -/
noncomputable def mon2 (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma mon2_zero (a b : ℕ) : mon2 a b 0 = a := by simp [mon2]
@[simp] lemma mon2_one (a b : ℕ) : mon2 a b 1 = b := by simp [mon2]

lemma eq_mon2 (s : Fin 2 →₀ ℕ) : s = mon2 (s 0) (s 1) := by
  ext i; fin_cases i <;> simp

lemma monomial_mon2 (a b : ℕ) (c : R) :
    monomial (mon2 a b) c = C c * X 0 ^ a * X 1 ^ b := by
  rw [mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, C_mul_monomial]
  simp [mon2]

/-- 単項式 `x^a y^b` は `x^(a+b) u^b` に写る。 -/
lemma sub_monomial (s : Fin 2 →₀ ℕ) (c : R) :
    sub (monomial s c) = monomial (mon2 (s 0 + s 1) (s 1)) c := by
  conv_lhs => rw [eq_mon2 s, monomial_mon2]
  simp only [sub, map_mul, map_pow, aeval_C, aeval_X, monomial_mon2]
  simp [pow_add]
  ring

lemma deg_mon2 (a b : ℕ) : deg (mon2 a b) = a + b := by simp [deg]

lemma mult_le {f : Poly R} {s : Fin 2 →₀ ℕ} (hs : s ∈ f.support) : mult f ≤ deg s :=
  Nat.sInf_le ⟨s, hs, rfl⟩

lemma exists_mult {f : Poly R} (hf : f ≠ 0) : ∃ s ∈ f.support, deg s = mult f := by
  have hne : (deg '' (f.support : Set (Fin 2 →₀ ℕ))).Nonempty := by
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hf
    exact ⟨_, s, hs, rfl⟩
  obtain ⟨s, hs, h⟩ := Nat.sInf_mem hne
  exact ⟨s, hs, h⟩

/-- `f̃`:`f(x, x u)` から `x^r` を括り出した残り。 -/
noncomputable def strict (f : Poly R) : Poly R :=
  ∑ s ∈ f.support, monomial (mon2 (deg s - mult f) (s 1)) (coeff s f)

lemma sub_eq (f : Poly R) : sub f = X 0 ^ mult f * strict f := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum, strict, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [sub_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have := mult_le hs
  have e : mon2 (s 0 + s 1) (s 1) = Finsupp.single 0 (mult f) + mon2 (deg s - mult f) (s 1) := by
    ext i; fin_cases i <;> simp [mon2, deg] at *; omega
  rw [e]

theorem not_dvd_strict {f : Poly R} (hf : f ≠ 0) : ¬ X 0 ∣ strict f := by
  rintro ⟨h, hh⟩
  obtain ⟨s, hs, hsd⟩ := exists_mult hf
  set t := mon2 0 (s 1) with ht
  have h1 : coeff t (strict f) = coeff s f := by
    rw [strict, coeff_sum, Finset.sum_eq_single s]
    · simp [coeff_monomial, ht, hsd]
    · intro s' hs' hne
      rw [coeff_monomial, if_neg]
      intro heq
      apply hne
      have h0 := congrArg (fun m => m 0) heq
      have h1 := congrArg (fun m => m 1) heq
      have := mult_le hs'
      simp [ht] at h0 h1
      ext i; fin_cases i <;> simp [deg] at * <;> omega
    · intro hns; exact absurd hs hns
  have h2 : coeff t (X 0 * h) = 0 := by
    rw [coeff_X_mul']
    simp [ht]
  rw [hh, h2] at h1
  exact (mem_support_iff.mp hs) h1.symm

/-- 層1の主定理。 -/
theorem sub_factor {f : Poly R} (hf : f ≠ 0) :
    ∃ g : Poly R, sub f = X 0 ^ mult f * g ∧ ¬ X 0 ∣ g :=
  ⟨strict f, sub_eq f, not_dvd_strict hf⟩

/-- 二項式の補題:`a ≤ b` なら `(y^a - x^b)(x, x u) = x^a (u^a - x^(b-a))`。 -/
theorem sub_binomial {a b : ℕ} (h : a ≤ b) :
    sub ((X 1 : Poly R) ^ a - X 0 ^ b) = X 0 ^ a * (X 1 ^ a - X 0 ^ (b - a)) := by
  simp only [sub, map_sub, map_pow, aeval_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  ring

/-! ### もう一方のチャート `x = t * y` -/

/-- `x ↔ y` の入れ替え。 -/
noncomputable def swapXY : Poly R →ₐ[R] Poly R := rename (Equiv.swap (0 : Fin 2) 1)

lemma swapXY_swapXY (f : Poly R) : swapXY (swapXY f) = f := by
  have h : (⇑(Equiv.swap (0 : Fin 2) 1) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id := by
    ext i; simp
  simp [swapXY, rename_rename, h]

lemma swapXY_X0 : swapXY (X 0 : Poly R) = X 1 := by simp [swapXY]

lemma swapXY_X1 : swapXY (X 1 : Poly R) = X 0 := by simp [swapXY]

lemma mult_swapXY_le (f : Poly R) : mult (swapXY f) ≤ mult f := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨s, hs, hsd⟩ := exists_mult hf
  have hmem : Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) s ∈ (swapXY f).support := by
    rw [swapXY, support_rename_of_injective (Equiv.injective _)]
    exact Finset.mem_image_of_mem _ hs
  refine (mult_le hmem).trans ?_
  have h0 : Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) s 0 = s 1 := by
    simpa using Finsupp.mapDomain_apply (Equiv.injective (Equiv.swap (0 : Fin 2) 1)) s 1
  have h1 : Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) s 1 = s 0 := by
    simpa using Finsupp.mapDomain_apply (Equiv.injective (Equiv.swap (0 : Fin 2) 1)) s 0
  simp only [deg, h0, h1] at hsd ⊢
  omega

lemma mult_swapXY (f : Poly R) : mult (swapXY f) = mult f :=
  le_antisymm (mult_swapXY_le f) (by simpa [swapXY_swapXY] using mult_swapXY_le (swapXY f))

lemma swapXY_ne_zero {f : Poly R} (hf : f ≠ 0) : swapXY f ≠ 0 := fun h => hf <| by
  simpa [swapXY_swapXY] using congrArg swapXY h

/-- チャート `x = t * y` への代入 `f(t y, y)`(`t = X 0`, `y = X 1`)。 -/
noncomputable def sub' : Poly R →ₐ[R] Poly R := swapXY.comp (sub.comp swapXY)

/-- 層1の主定理(`u = 1` チャート版)。 -/
theorem sub'_factor {f : Poly R} (hf : f ≠ 0) :
    ∃ g : Poly R, sub' f = X 1 ^ mult f * g ∧ ¬ X 1 ∣ g := by
  obtain ⟨g, hg, hndvd⟩ := sub_factor (swapXY_ne_zero hf)
  refine ⟨swapXY g, ?_, ?_⟩
  · have := congrArg swapXY hg
    simpa [sub', swapXY_swapXY, mult_swapXY, swapXY_X0] using this
  · rintro ⟨h, hh⟩
    apply hndvd
    refine ⟨swapXY h, ?_⟩
    have := congrArg swapXY hh
    simpa [swapXY_swapXY, swapXY_X0, swapXY_X1] using this

/-- 二項式の補題(`u = 1` チャート版):`(x^a - y^b)(t y, y) = y^a (t^a - y^(b-a))`。 -/
theorem sub'_binomial {a b : ℕ} (h : a ≤ b) :
    sub' ((X 0 : Poly R) ^ a - X 1 ^ b) = X 1 ^ a * (X 0 ^ a - X 1 ^ (b - a)) := by
  have := congrArg swapXY (sub_binomial (R := R) h)
  simpa [sub', swapXY, rename_X] using this

/-! ### 層2: 引き算型の互除法

曲線 `y^a = x^b` を 1 回ブローアップすると strict transform は `(a, b-a)`(`a ≤ b`)、
`a > b` なら `x,y` を入れ替えて `(a-b, b)`。`a = 0`、`b = 0`、`min a b = 1` で停止。 -/

/-- 引き算型の互除法でのブローアップ回数。 -/
def blowCount (a b : ℕ) : ℕ :=
  if h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1 then 0
  else if hab : a ≤ b then 1 + blowCount a (b - a)
  else 1 + blowCount (a - b) b
termination_by a + b
decreasing_by all_goals omega

lemma blowCount_stop {a b : ℕ} (h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1) : blowCount a b = 0 := by
  rw [blowCount, dif_pos h]

lemma blowCount_le {a b : ℕ} (h : ¬(a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1)) (hab : a ≤ b) :
    blowCount a b = 1 + blowCount a (b - a) := by
  rw [blowCount, dif_neg h, dif_pos hab]

lemma blowCount_gt {a b : ℕ} (h : ¬(a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1)) (hab : ¬ a ≤ b) :
    blowCount a b = 1 + blowCount (a - b) b := by
  rw [blowCount, dif_neg h, dif_neg hab]

lemma blowCount_comm (a b : ℕ) : blowCount a b = blowCount b a := by
  induction' hn : a + b using Nat.strong_induction_on with n ih generalizing a b
  by_cases h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1
  · rw [blowCount_stop h, blowCount_stop (by tauto)]
  · have h' : ¬(b = 0 ∨ a = 0 ∨ b = 1 ∨ a = 1) := by tauto
    rcases lt_trichotomy a b with hlt | heq | hgt
    · rw [blowCount_le h hlt.le, blowCount_gt h' (by omega),
        ih (a + (b - a)) (by omega) a (b - a) rfl]
    · subst heq; rfl
    · rw [blowCount_gt h (by omega), blowCount_le h' hgt.le,
        ih ((a - b) + b) (by omega) (a - b) b rfl]
/-- 教科書 V 3.9.5:`y^2 = x^r` は `[r/2]` 回で解消する。 -/
theorem blowCount_two (r : ℕ) : blowCount 2 r = r / 2 := by
  induction' r using Nat.strong_induction_on with r ih
  by_cases h : r = 0 ∨ r = 1
  · rcases h with rfl | rfl <;> simp [blowCount_stop]
  · have h2 : ¬(2 = 0 ∨ r = 0 ∨ 2 = 1 ∨ r = 1) := by omega
    by_cases hr : 2 ≤ r
    · rw [blowCount_le h2 hr, ih (r - 2) (by omega)]
      omega
    · omega


/-! ### 層1と層2の接続:二項式 `y^a - x^b` -/

/-- 二項式 `y^a - x^b`。 -/
noncomputable def binom (a b : ℕ) : Poly R := X 1 ^ a - X 0 ^ b

section binom
variable [Nontrivial R]

omit [Nontrivial R] in
lemma X1_pow_eq (a : ℕ) : (X 1 ^ a : Poly R) = monomial (mon2 0 a) 1 := by
  rw [monomial_mon2]; simp

omit [Nontrivial R] in
lemma X0_pow_eq (b : ℕ) : (X 0 ^ b : Poly R) = monomial (mon2 b 0) 1 := by
  rw [monomial_mon2]; simp

lemma mon2_ne {a b : ℕ} (hb : 1 ≤ b) : mon2 b 0 ≠ mon2 0 a := fun h => by
  have := congrArg (fun m => m 0) h
  simp at this; omega

omit [Nontrivial R] in
lemma coeff_binom_Y {a b : ℕ} (hb : 1 ≤ b) : coeff (mon2 0 a) (binom a b : Poly R) = 1 := by
  rw [binom, X1_pow_eq, X0_pow_eq, coeff_sub, coeff_monomial, coeff_monomial,
    if_pos rfl, if_neg (mon2_ne hb)]
  simp

omit [Nontrivial R] in
lemma coeff_binom_X {a b : ℕ} (ha : 1 ≤ a) :
    coeff (mon2 b 0) (binom a b : Poly R) = -1 := by
  have : mon2 0 a ≠ mon2 b 0 := fun h => by
    have := congrArg (fun m => m 1) h
    simp at this; omega
  rw [binom, X1_pow_eq, X0_pow_eq, coeff_sub, coeff_monomial, coeff_monomial,
    if_pos rfl, if_neg this]
  simp

omit [Nontrivial R] in
lemma support_binom {a b : ℕ} {s : Fin 2 →₀ ℕ} (hs : s ∈ (binom a b : Poly R).support) :
    s = mon2 0 a ∨ s = mon2 b 0 := by
  by_contra hc
  push_neg at hc
  rw [mem_support_iff, binom, X1_pow_eq, X0_pow_eq, coeff_sub, coeff_monomial,
    coeff_monomial, if_neg (Ne.symm hc.1), if_neg (Ne.symm hc.2)] at hs
  simp at hs

/-- `mult (y^a - x^b) = min a b`。 -/
theorem mult_binom {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    mult (binom a b : Poly R) = min a b := by
  have hY : mon2 0 a ∈ (binom a b : Poly R).support := by
    rw [mem_support_iff, coeff_binom_Y hb]; exact one_ne_zero
  have hX : mon2 b 0 ∈ (binom a b : Poly R).support := by
    rw [mem_support_iff, coeff_binom_X ha]; simp
  have hf : (binom a b : Poly R) ≠ 0 := fun h => by simp [h] at hY
  apply le_antisymm
  · exact le_min (by simpa [deg_mon2] using mult_le hY) (by simpa [deg_mon2] using mult_le hX)
  · obtain ⟨s, hs, hsd⟩ := exists_mult hf
    rw [← hsd]
    rcases support_binom hs with rfl | rfl <;> simp [deg_mon2]

/-- `a ≤ b`:チャート `y = x u` で `y^a - x^b ↦ x^m (y^a - x^(b-a))`、`m = mult`。 -/
theorem binom_sub_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    sub (binom a b : Poly R) = X 0 ^ mult (binom a b : Poly R) * binom a (b - a) := by
  rw [mult_binom ha (ha.trans hab), min_eq_left hab]
  exact sub_binomial hab

/-- `b < a`:チャート `x = t y` で `y^a - x^b ↦ y^m (y^(a-b) - x^b)`、`m = mult`。 -/
theorem binom_sub'_gt {a b : ℕ} (hb : 1 ≤ b) (hab : b < a) :
    sub' (binom a b : Poly R) = X 1 ^ mult (binom a b : Poly R) * binom (a - b) b := by
  rw [mult_binom (hb.trans hab.le) hb, min_eq_right hab.le]
  have h := sub'_binomial (R := R) hab.le
  have e : (binom a b : Poly R) = -((X 0 : Poly R) ^ b - X 1 ^ a) := by simp [binom]
  rw [e, map_neg, h]
  simp only [binom]
  ring

/-- strict transform が二項式のまま移る(`a ≤ b`、整域上)。 -/
theorem strict_binom_le [IsDomain R] {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    strict (binom a b : Poly R) = binom a (b - a) := by
  have h1 := sub_eq (binom a b : Poly R)
  rw [binom_sub_le ha hab] at h1
  exact (mul_left_cancel₀ (pow_ne_zero _ (X_ne_zero (0 : Fin 2))) h1).symm

lemma stop_iff {a b : ℕ} : (a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1) ↔ min a b ≤ 1 := by omega

/-- 停止条件 ⇔ 重複度 ≤ 1(非特異)。 -/
theorem blowCount_eq_zero_iff {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    blowCount a b = 0 ↔ mult (binom a b : Poly R) ≤ 1 := by
  rw [mult_binom ha hb]
  constructor
  · intro h
    by_contra hc
    have hn : ¬(a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1) := by omega
    rcases le_or_gt a b with hab | hab
    · rw [blowCount_le hn hab] at h; omega
    · rw [blowCount_gt hn (by omega)] at h; omega
  · intro h
    exact blowCount_stop (stop_iff.mpr h)

end binom

/-! ### 主定理:`y^a = x^b` は `blowCount a b` 回のブローアップで非特異になる -/

/-- 1 回のブローアップによる指数の組の変化。 -/
def step (p : ℕ × ℕ) : ℕ × ℕ := if p.1 ≤ p.2 then (p.1, p.2 - p.1) else (p.1 - p.2, p.2)

lemma blowCount_step {a b : ℕ} (h : ¬(a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1)) :
    blowCount a b = 1 + blowCount (step (a, b)).1 (step (a, b)).2 := by
  unfold step
  split_ifs with hab
  · exact blowCount_le h hab
  · exact blowCount_gt h hab

lemma step_lt {a b : ℕ} (h : ¬(a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1)) :
    (step (a, b)).1 + (step (a, b)).2 < a + b := by
  unfold step
  split_ifs <;> simp <;> omega

section main
variable [Nontrivial R]

/-- 1 段の実現:`a, b ≥ 2` なら、適切なチャートの代入 `σ` で
`σ (y^a - x^b) = (x または y)^(min a b) * (次の二項式)`。 -/
lemma binom_step {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ (σ : Poly R →ₐ[R] Poly R) (i : Fin 2),
      σ (binom a b) = X i ^ min a b * binom (step (a, b)).1 (step (a, b)).2 := by
  unfold step
  split_ifs with hab
  · dsimp only at hab ⊢
    refine ⟨sub, 0, ?_⟩
    have := binom_sub_le (R := R) (by omega) hab
    rw [min_eq_left hab]
    rwa [mult_binom (by omega) (by omega), min_eq_left hab] at this
  · dsimp only at hab ⊢
    refine ⟨sub', 1, ?_⟩
    have hab' : b < a := by omega
    have := binom_sub'_gt (R := R) (by omega) hab'
    rw [min_eq_right hab'.le]
    rwa [mult_binom (by omega) (by omega), min_eq_right hab'.le] at this

lemma main_aux (a b : ℕ) :
    (∀ k < blowCount a b,
      2 ≤ min (step^[k] (a, b)).1 (step^[k] (a, b)).2 ∧
      ∃ (σ : Poly R →ₐ[R] Poly R) (i : Fin 2),
        σ (binom (step^[k] (a, b)).1 (step^[k] (a, b)).2) =
          X i ^ min (step^[k] (a, b)).1 (step^[k] (a, b)).2 *
            binom (step^[k + 1] (a, b)).1 (step^[k + 1] (a, b)).2) ∧
    (let p := step^[blowCount a b] (a, b); p.1 = 0 ∨ p.2 = 0 ∨ p.1 = 1 ∨ p.2 = 1) := by
  induction' hn : a + b using Nat.strong_induction_on with n ih generalizing a b
  by_cases h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1
  · simp [blowCount_stop h, h]
  · have hlt := step_lt h
    obtain ⟨ih1, ih2⟩ := ih _ (by omega) (step (a, b)).1 (step (a, b)).2 rfl
    have hc := blowCount_step h
    refine ⟨fun k hk => ?_, ?_⟩
    · rcases k with _ | k
      · simp only [Function.iterate_zero, id_eq, zero_add, Function.iterate_one]
        have h2 : 2 ≤ a ∧ 2 ≤ b := by omega
        exact ⟨by omega, binom_step h2.1 h2.2⟩
      · rw [hc] at hk
        have := ih1 k (by omega)
        simpa [Function.iterate_succ_apply] using this
    · rw [hc, add_comm, Function.iterate_succ_apply]
      exact ih2

/-- 停止した組では重複度は `≤ 1`(`0` の場合は原点を通らない)。 -/
lemma mult_binom_le_one {a b : ℕ} (h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1) :
    mult (binom a b : Poly R) ≤ 1 := by
  by_cases hz : a = 0 ∨ b = 0
  · rcases hz with rfl | rfl
    · by_cases hb : 1 ≤ b
      · have hm : mon2 0 0 ∈ (binom 0 b : Poly R).support := by
          rw [mem_support_iff, coeff_binom_Y hb]; exact one_ne_zero
        have := mult_le hm
        simp [deg_mon2] at this; omega
      · obtain rfl : b = 0 := by omega
        simp [binom, mult]
    · by_cases ha : 1 ≤ a
      · have hm : mon2 0 0 ∈ (binom a 0 : Poly R).support := by
          rw [mem_support_iff, coeff_binom_X ha]; simp
        have := mult_le hm
        simp [deg_mon2] at this; omega
      · obtain rfl : a = 0 := by omega
        simp [binom, mult]
  · rw [mult_binom (by omega) (by omega)]
    omega

/-- **主定理**:`y^a = x^b` に対し、`N = blowCount a b` として、
各 `k < N` 段で重複度 `min ≥ 2`(特異)かつ適切なチャートで strict transform が
次の二項式に移り、`N` 段目で重複度 `≤ 1`(非特異、または原点を通らない)になる。 -/
theorem binom_resolution (a b : ℕ) :
    (∀ k < blowCount a b,
      2 ≤ mult (binom (step^[k] (a, b)).1 (step^[k] (a, b)).2 : Poly R) ∧
      ∃ (σ : Poly R →ₐ[R] Poly R) (i : Fin 2),
        σ (binom (step^[k] (a, b)).1 (step^[k] (a, b)).2) =
          X i ^ mult (binom (step^[k] (a, b)).1 (step^[k] (a, b)).2 : Poly R) *
            binom (step^[k + 1] (a, b)).1 (step^[k + 1] (a, b)).2) ∧
    mult (binom (step^[blowCount a b] (a, b)).1 (step^[blowCount a b] (a, b)).2 : Poly R) ≤ 1 := by
  obtain ⟨h1, h2⟩ := main_aux (R := R) a b
  refine ⟨fun k hk => ?_, mult_binom_le_one h2⟩
  obtain ⟨hk2, σ, i, hσ⟩ := h1 k hk
  rw [mult_binom (by omega) (by omega)]
  exact ⟨hk2, σ, i, hσ⟩

/-- **最小性**:`blowCount a b` は、重複度が `≤ 1` になる最初の段である。
すなわち `N` 回で解消でき(`binom_resolution`)、`N` 回未満では特異点が残る。 -/
theorem blowCount_isLeast (a b : ℕ) :
    IsLeast {k : ℕ | mult (binom (step^[k] (a, b)).1 (step^[k] (a, b)).2 : Poly R) ≤ 1}
      (blowCount a b) := by
  obtain ⟨h1, h2⟩ := binom_resolution (R := R) a b
  refine ⟨h2, fun k hk => ?_⟩
  by_contra hlt
  push_neg at hlt
  have := (h1 k hlt).1
  simp only [Set.mem_setOf_eq] at hk
  omega

/-- 系:`k` 回のブローアップで解消できるなら `blowCount a b ≤ k`。 -/
theorem blowCount_le_of_resolved {a b k : ℕ}
    (h : mult (binom (step^[k] (a, b)).1 (step^[k] (a, b)).2 : Poly R) ≤ 1) :
    blowCount a b ≤ k :=
  (blowCount_isLeast (R := R) a b).2 h
end main

/-! ### 定理A:連分数による記述 -/

set_option linter.unusedVariables false in
/-- ブローアップする点の重複度の列(停止するまで `min a b` を記録する)。 -/
def mults (a b : ℕ) : List ℕ :=
  if h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1 then []
  else if hab : a ≤ b then a :: mults a (b - a)
  else b :: mults (a - b) b
termination_by a + b
decreasing_by all_goals omega

lemma mults_stop {a b : ℕ} (h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1) : mults a b = [] := by
  rw [mults, dif_pos h]

lemma mults_le {a b : ℕ} (h : ¬(a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1)) (hab : a ≤ b) :
    mults a b = a :: mults a (b - a) := by
  rw [mults, dif_neg h, dif_pos hab]

lemma mults_gt {a b : ℕ} (h : ¬(a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1)) (hab : ¬ a ≤ b) :
    mults a b = b :: mults (a - b) b := by
  rw [mults, dif_neg h, dif_neg hab]

lemma mults_comm (a b : ℕ) : mults a b = mults b a := by
  induction' hn : a + b using Nat.strong_induction_on with n ih generalizing a b
  by_cases h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1
  · rw [mults_stop h, mults_stop (by tauto)]
  · have h' : ¬(b = 0 ∨ a = 0 ∨ b = 1 ∨ a = 1) := by tauto
    rcases lt_trichotomy a b with hlt | heq | hgt
    · rw [mults_le h hlt.le, mults_gt h' (by omega),
        ih (a + (b - a)) (by omega) a (b - a) rfl]
    · subst heq; rfl
    · rw [mults_gt h (by omega), mults_le h' hgt.le,
        ih ((a - b) + b) (by omega) (a - b) b rfl]

lemma mults_step {a b : ℕ} (h : ¬(a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1)) :
    mults a b = min a b :: mults (step (a, b)).1 (step (a, b)).2 := by
  unfold step
  split_ifs with hab
  · rw [mults_le h hab, min_eq_left hab]
  · rw [mults_gt h hab, min_eq_right (by omega)]

/-- `step` を `j` 回進めた組の `min` を並べた列が `mults`。 -/
lemma map_min_eq_mults (a b : ℕ) :
    (List.range (blowCount a b)).map
      (fun j => min (step^[j] (a, b)).1 (step^[j] (a, b)).2) = mults a b := by
  induction' hn : a + b using Nat.strong_induction_on with n ih generalizing a b
  by_cases h : a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1
  · simp [blowCount_stop h, mults_stop h]
  · have hlt := step_lt h
    have ih' := ih _ (by omega) (step (a, b)).1 (step (a, b)).2 rfl
    rw [blowCount_step h, add_comm, List.range_succ_eq_map, List.map_cons, List.map_map,
      mults_step h]
    congr 1

lemma length_mults (a b : ℕ) : (mults a b).length = blowCount a b := by
  rw [← map_min_eq_mults, List.length_map, List.length_range]

set_option linter.unusedVariables false in
/-- 互除法のブロック列:`(r_i, a_i)`(重複度 `r_i` が `a_i` 個)。
`q/p = [a_0; a_1, …, a_r]`、`r_{-1} = q`、`r_0 = p`、`r_{i-1} = a_i r_i + r_{i+1}` に対し、
`blocks q p = [(r_0, a_0), (r_1, a_1), …, (r_{r-1}, a_{r-1})]`(`r_r = 1` で止まる)。 -/
def blocks (prev cur : ℕ) : List (ℕ × ℕ) :=
  if h : cur ≤ 1 then [] else (cur, prev / cur) :: blocks cur (prev % cur)
termination_by cur
decreasing_by exact Nat.mod_lt _ (by omega)

/-- ブロック列を「`r_i` が `a_i` 個」の並びに展開する。 -/
def expand (L : List (ℕ × ℕ)) : List ℕ := L.flatMap fun x => List.replicate x.2 x.1

lemma length_expand (L : List (ℕ × ℕ)) : (expand L).length = (L.map Prod.snd).sum := by
  induction L with
  | nil => simp [expand]
  | cons x L ih => simp [expand] at ih ⊢

lemma mults_run {m : ℕ} (hm : 2 ≤ m) (k s : ℕ) :
    mults m (k * m + s) = List.replicate k m ++ mults m s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (k + 1) * m + s = (k * m + s) + m := by ring
    have hle : m ≤ (k * m + s) + m := Nat.le_add_left _ _
    have hn : ¬(m = 0 ∨ (k + 1) * m + s = 0 ∨ m = 1 ∨ (k + 1) * m + s = 1) := by
      rw [e]; omega
    rw [mults_le hn (by rw [e]; exact hle), e, Nat.add_sub_cancel, ih, List.replicate_succ,
      List.cons_append]

lemma mults_euclid (cur prev : ℕ) : mults cur prev = expand (blocks prev cur) := by
  induction' cur using Nat.strong_induction_on with cur ih generalizing prev
  by_cases hc : cur ≤ 1
  · rw [mults_stop (by omega), blocks, dif_pos hc]; rfl
  · rw [blocks, dif_neg hc, expand, List.flatMap_cons, ← expand]
    have e : prev = prev / cur * cur + prev % cur := (Nat.div_add_mod' prev cur).symm
    conv_lhs => rw [e]
    rw [mults_run (by omega), mults_comm cur (prev % cur),
      ih (prev % cur) (Nat.mod_lt _ (by omega)) cur]

section theoremA
variable [Nontrivial R]

/-- **定理A**(`y^p = x^q`、モデルは原点の strict transform を追う):
`N = blowCount p q` は `a_0 + … + a_{r-1}`(`blocks` の個数の総和)に等しく、
`j` 回目の重複度の列は「`r_0` が `a_0` 個、`r_1` が `a_1` 個、…」の順、
かつ `N` は重複度が `≤ 1` になる最初の段である。 -/
theorem theoremA (p q : ℕ) :
    blowCount p q = ((blocks q p).map Prod.snd).sum ∧
    (List.range (blowCount p q)).map
      (fun j => mult (binom (step^[j] (p, q)).1 (step^[j] (p, q)).2 : Poly R)) =
        expand (blocks q p) ∧
    IsLeast {k : ℕ | mult (binom (step^[k] (p, q)).1 (step^[k] (p, q)).2 : Poly R) ≤ 1}
      (blowCount p q) := by
  refine ⟨?_, ?_, blowCount_isLeast p q⟩
  · rw [← length_mults, mults_euclid, length_expand]
  · rw [← mults_euclid, ← map_min_eq_mults]
    refine List.map_congr_left fun j hj => ?_
    obtain ⟨h2, -⟩ := (main_aux (R := R) p q).1 j (List.mem_range.mp hj)
    exact mult_binom (by omega) (by omega)

end theoremA

end Blowup

