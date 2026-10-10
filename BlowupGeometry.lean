import Blowup

/-!
# ブローアップ(層3: 幾何)

体 `k` 上の集合論的モデル `X = {((x,y),[t:u]) | x u = t y} ⊂ 𝔸² × ℙ¹` と、
`Blowup.lean`(多項式の層)で示した strict transform との接続。

* `φ : X ∖ E → 𝔸² ∖ 0` は全単射、`E ≅ ℙ¹`(`blowup_bijOn_compl`, `exceptional_eq`)
* `X ∖ E` は `X` で Zariski 稠密、`X` は既約(`density_chart_*`, `irreducible_*`)
* `Ỹ = closure(φ⁻¹(Y ∖ 0)) = Z(f̃)`(`closure_preimage_eq_strict`)
* `Ỹ · E = mult f`(接線の重複度の総和、`tangent_total`)
-/

open MvPolynomial

set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

namespace Blowup
/-! ### 層3: 幾何(体 `k` 上の集合論的な定式化)

`X = {((x,y),[t:u]) | x u = t y} ⊂ 𝔸² × ℙ¹`、`φ = Prod.fst`、`E = φ⁻¹(0)`。 -/

section geometry
open Projectivization

variable (k : Type*) [Field k]

/-- ブローアップ `X = {((x,y),[t:u]) | x u = t y}`(代表元 `rep` で書く)。 -/
def blowupSet : Set ((Fin 2 → k) × Projectivization k (Fin 2 → k)) :=
  {z | z.1 0 * z.2.rep 1 = z.2.rep 0 * z.1 1}

variable {k}

/-- 任意の代表元で方程式を判定できる(代表元の取り方によらない)。 -/
lemma mem_blowupSet_iff {P v : Fin 2 → k} {L : Projectivization k (Fin 2 → k)} (hv : v ≠ 0)
    (h : mk k v hv = L) : (P, L) ∈ blowupSet k ↔ P 0 * v 1 = v 0 * P 1 := by
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff k _ _ L.rep_nonzero hv).mp ((mk_rep L).trans h.symm)
  have h0 : L.rep 0 = a * v 0 := by rw [← ha]; simp [Units.smul_def]
  have h1 : L.rep 1 = a * v 1 := by rw [← ha]; simp [Units.smul_def]
  have hane : (a : k) ≠ 0 := a.ne_zero
  simp only [blowupSet, Set.mem_setOf_eq, h0, h1]
  constructor
  · intro h2
    exact mul_left_cancel₀ hane (by linear_combination h2)
  · intro h2
    linear_combination (a : k) * h2

lemma ne_zero_iff_fin2 {P : Fin 2 → k} : P ≠ 0 ↔ P 0 ≠ 0 ∨ P 1 ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  · rintro (h | h) rfl <;> simp at h

/-- `P ≠ 0` と `v` が平行(`P₀ v₁ = v₀ P₁`)なら `[v] = [P]`。 -/
lemma mk_eq_of_parallel {P v : Fin 2 → k} (hP : P ≠ 0) (hv : v ≠ 0)
    (h : P 0 * v 1 = v 0 * P 1) : mk k v hv = mk k P hP := by
  rw [mk_eq_mk_iff]
  have hP' := ne_zero_iff_fin2.mp hP
  have hv' := ne_zero_iff_fin2.mp hv
  by_cases h0 : P 0 = 0
  · have h1 : P 1 ≠ 0 := hP'.resolve_left (not_not.mpr h0)
    have hv0 : v 0 = 0 := by
      rw [h0] at h
      have : v 0 * P 1 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_right h1
    have hv1 : v 1 ≠ 0 := hv'.resolve_left (not_not.mpr hv0)
    refine ⟨Units.mk0 (v 1 / P 1) (div_ne_zero hv1 h1), ?_⟩
    ext i; fin_cases i
    · simp [h0, hv0]
    · simp [Units.smul_def]; field_simp
  · have hv0 : v 0 ≠ 0 := by
      intro hv0
      rw [hv0] at h
      have hv1 : v 1 = 0 := by
        have : P 0 * v 1 = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_left h0
      exact hv (by ext i; fin_cases i <;> simp [hv0, hv1])
    refine ⟨Units.mk0 (v 0 / P 0) (div_ne_zero hv0 h0), ?_⟩
    ext i; fin_cases i
    · simp [Units.smul_def]; field_simp
    · simp [Units.smul_def]; field_simp; linear_combination -h

/-- `φ = Prod.fst`、`E = φ⁻¹(0) ∩ X`。 -/
def exceptional (k : Type*) [Field k] : Set ((Fin 2 → k) × Projectivization k (Fin 2 → k)) :=
  blowupSet k ∩ {z | z.1 = 0}

/-- 性質 (1):`φ : X ∖ E → 𝔸² ∖ 0` は全単射。 -/
theorem blowup_bijOn_compl :
    Set.BijOn Prod.fst (blowupSet k ∩ {z | z.1 ≠ 0}) {P | P ≠ 0} := by
  refine ⟨fun z hz => hz.2, ?_, ?_⟩
  · rintro ⟨P, L⟩ ⟨hz, hP⟩ ⟨P', L'⟩ ⟨hz', -⟩ (h : P = P')
    subst h
    have hP : P ≠ 0 := hP
    have e1 := (mem_blowupSet_iff L.rep_nonzero (mk_rep L)).mp hz
    have e2 := (mem_blowupSet_iff L'.rep_nonzero (mk_rep L')).mp hz'
    have a1 := mk_eq_of_parallel hP L.rep_nonzero e1
    have a2 := mk_eq_of_parallel hP L'.rep_nonzero e2
    rw [mk_rep] at a1 a2
    simp [a1, a2]
  · intro P hP
    refine ⟨(P, mk k P hP), ⟨?_, hP⟩, rfl⟩
    exact (mem_blowupSet_iff hP rfl).mpr rfl

/-- 性質 (2):`E = {0} × ℙ¹`、特に第2射影で `E ≅ ℙ¹`。 -/
theorem exceptional_eq : exceptional k = {0} ×ˢ Set.univ := by
  ext ⟨P, L⟩
  simp only [exceptional, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_univ, and_true, blowupSet]
  constructor
  · exact fun h => h.2
  · rintro rfl; simp

theorem exceptional_bijOn : Set.BijOn Prod.snd (exceptional k) Set.univ := by
  rw [exceptional_eq]
  refine ⟨fun _ _ => trivial, ?_, fun L _ => ⟨(0, L), by simp, rfl⟩⟩
  rintro ⟨P, L⟩ ⟨h1, -⟩ ⟨P', L'⟩ ⟨h1', -⟩ (h : L = L')
  simp at h1 h1'
  simp [h1, h1', h]

/-- `X` の点 `(P, L')`(`P ≠ 0`)では `L' = [P]`。 -/
lemma snd_eq_mk {P : Fin 2 → k} {L : Projectivization k (Fin 2 → k)} (hP : P ≠ 0)
    (hz : (P, L) ∈ blowupSet k) : L = mk k P hP := by
  have e := (mem_blowupSet_iff L.rep_nonzero (mk_rep L)).mp hz
  have := mk_eq_of_parallel hP L.rep_nonzero e
  rwa [mk_rep] at this

lemma mem_submodule_iff_mk {P : Fin 2 → k} (hP : P ≠ 0) (L : Projectivization k (Fin 2 → k)) :
    P ∈ L.submodule ↔ mk k P hP = L := by
  rw [submodule_eq, Submodule.mem_span_singleton]
  calc (∃ a : k, a • L.rep = P)
      ↔ mk k P hP = mk k L.rep L.rep_nonzero := (mk_eq_mk_iff' k _ _ hP L.rep_nonzero).symm
    _ ↔ mk k P hP = L := by rw [mk_rep]

/-- 性質 (3):`X ∖ E` の点 `(P, L')` について、`P` が `L` の張る直線 `ℓ_L` 上にあることと
`L' = L` は同値。すなわち `ℓ_L ∖ 0` の持ち上げは `{z ∈ X ∖ E | z₂ = L}`。
`E` の点 `(0, L)` が `ℓ_L` の方向に対応する。 -/
theorem line_lift {P : Fin 2 → k} {L' : Projectivization k (Fin 2 → k)}
    (hP : P ≠ 0) (hz : (P, L') ∈ blowupSet k) (L : Projectivization k (Fin 2 → k)) :
    P ∈ L.submodule ↔ L' = L := by
  rw [mem_submodule_iff_mk hP, snd_eq_mk hP hz]

/-! #### strict transform とチャートの接続 -/

lemma eval_sub (f : Poly k) (a : Fin 2 → k) :
    eval a (sub f) = eval ![a 0, a 0 * a 1] f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [sub]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    fin_cases i <;> simp [sub]

lemma one_ne_zero_vec (u : k) : (![1, u] : Fin 2 → k) ≠ 0 := fun h => by
  have := congrFun h 0
  simp at this

/-- チャート `t = 1` の点 `((x, x u), [1 : u])` は `X` の点。 -/
lemma chart_mem (x u : k) :
    ((![x, x * u] : Fin 2 → k), mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k := by
  rw [mem_blowupSet_iff (one_ne_zero_vec u) rfl]
  simp

/-- `x ≠ 0` では、`f(x, x u) = 0` と `f̃(x, u) = 0` は同値
(`φ⁻¹(Y ∖ 0)` と `Z(f̃)` はチャートの `E` の外で一致する)。 -/
theorem eval_strict_iff (f : Poly k) {x : k} (hx : x ≠ 0) (u : k) :
    eval ![x, x * u] f = 0 ↔ eval ![x, u] (strict f) = 0 := by
  have h := congrArg (eval ![x, u]) (sub_eq f)
  rw [eval_sub, map_mul, map_pow, eval_X] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  simp [hx]

/-- `E` 上の点(チャートの `x = 0`)で `f̃(0, u) = f_r(1, u)`:最低次の斉次部分で、
`f̃ ∩ E` は接線方向に対応する。 -/
theorem eval_strict_zero (f : Poly k) (u : k) :
    eval ![0, u] (strict f) =
      ∑ s ∈ f.support.filter (fun s => deg s = mult f), coeff s f * u ^ (s 1) := by
  rw [strict, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hle := mult_le hs
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  by_cases h : deg s = mult f
  · simp [h, mon2]
  · have : deg s - mult f ≠ 0 := by omega
    simp [h, this, mon2]

/-! #### 性質 (4):`X ∖ E` は `X` で Zariski 稠密(代数的な定式化)

`𝔸² × ℙ¹` を 2 つのチャート(`t = 1`: 座標 `(x, y, u)`、`u = 1`: 座標 `(x, y, t)`)で覆い、
閉集合をチャート上の多項式の零点集合として扱う。「`X ∖ E` 上で消える多項式は `E` 上でも消える」
ことが稠密性にあたる。 -/

section density
open Polynomial

lemma eval_aeval_vec (φ : Fin 3 → k[X]) (g : MvPolynomial (Fin 3) k) (x : k) :
    (MvPolynomial.aeval φ g).eval x = MvPolynomial.eval (fun i => (φ i).eval x) g := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- 1 変数の議論:`x ≠ 0` で消える曲線 `x ↦ g(φ(x))` は `x = 0` でも消える。 -/
lemma eval_zero_of_forall [Infinite k] (φ : Fin 3 → k[X]) (g : MvPolynomial (Fin 3) k)
    (h : ∀ x : k, x ≠ 0 → MvPolynomial.eval (fun i => (φ i).eval x) g = 0) :
    MvPolynomial.eval (fun i => (φ i).eval 0) g = 0 := by
  set p := MvPolynomial.aeval φ g with hp
  have hroot : ∀ x : k, x ≠ 0 → p.IsRoot x := fun x hx => by
    rw [IsRoot, hp, eval_aeval_vec]; exact h x hx
  have hinf : {x : k | p.IsRoot x}.Infinite := by
    refine Set.Infinite.mono (s := {x : k | x ≠ 0}) (fun x hx => hroot x hx) ?_
    have : {x : k | x ≠ 0} = Set.univ \ {0} := by ext; simp
    rw [this]
    exact Set.infinite_univ.diff (Set.finite_singleton 0)
  have : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hinf
  have h0 := congrArg (Polynomial.eval 0) this
  rw [hp, eval_aeval_vec] at h0
  simpa using h0

variable [Infinite k]

/-- チャート `t = 1`(点 `((x, y), [1 : u])`、`y = x u`):`X ∖ E` 上で消える
`g ∈ k[x, y, u]` は `E` 上(`x = y = 0`)でも消える。 -/
theorem density_chart_t (g : MvPolynomial (Fin 3) k)
    (h : ∀ (P : Fin 2 → k) (u : k), (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k →
      P ≠ 0 → MvPolynomial.eval ![P 0, P 1, u] g = 0)
    (u : k) : MvPolynomial.eval ![0, 0, u] g = 0 := by
  have e : ∀ x : k, (fun i : Fin 3 => (![Polynomial.X, Polynomial.C u * Polynomial.X,
      Polynomial.C u] i).eval x) = ![x, u * x, u] := fun x => by
    funext i; fin_cases i <;> simp
  have key := eval_zero_of_forall ![Polynomial.X, Polynomial.C u * Polynomial.X,
      Polynomial.C u] g (fun x hx => by
    rw [e x]
    have := h ![x, x * u] u (chart_mem x u) (fun h0 => hx (by simpa using congrFun h0 0))
    simpa [mul_comm] using this)
  simpa [e 0] using key
end density

lemma one_ne_zero_vec' (t : k) : (![t, 1] : Fin 2 → k) ≠ 0 := fun h => by
  have := congrFun h 1
  simp at this

/-- チャート `u = 1` の点 `((t y, y), [t : 1])` は `X` の点。 -/
lemma chart_mem' (t y : k) :
    ((![t * y, y] : Fin 2 → k), mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k := by
  rw [mem_blowupSet_iff (one_ne_zero_vec' t) rfl]
  simp

/-- 2 つのチャートは `ℙ¹` を覆う。 -/
theorem chart_cover (L : Projectivization k (Fin 2 → k)) :
    (∃ u, L = mk k ![1, u] (one_ne_zero_vec u)) ∨ (∃ t, L = mk k ![t, 1] (one_ne_zero_vec' t)) := by
  have hr := ne_zero_iff_fin2.mp L.rep_nonzero
  by_cases h0 : L.rep 0 = 0
  · right
    have h1 : L.rep 1 ≠ 0 := hr.resolve_left (not_not.mpr h0)
    refine ⟨L.rep 0 / L.rep 1, ?_⟩
    rw [eq_comm, ← mk_rep L, mk_eq_mk_iff']
    refine ⟨(L.rep 1)⁻¹, ?_⟩
    ext i; fin_cases i <;> simp [h0, h1]
  · left
    refine ⟨L.rep 1 / L.rep 0, ?_⟩
    rw [eq_comm, ← mk_rep L, mk_eq_mk_iff']
    refine ⟨(L.rep 0)⁻¹, ?_⟩
    ext i; fin_cases i <;> simp [h0] <;> field_simp

section density'
open Polynomial
variable [Infinite k]

/-- チャート `u = 1`(点 `((x, y), [t : 1])`、`x = t y`):`X ∖ E` 上で消える
`g ∈ k[x, y, t]` は `E` 上でも消える。 -/
theorem density_chart_u (g : MvPolynomial (Fin 3) k)
    (h : ∀ (P : Fin 2 → k) (t : k), (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k →
      P ≠ 0 → MvPolynomial.eval ![P 0, P 1, t] g = 0)
    (t : k) : MvPolynomial.eval ![0, 0, t] g = 0 := by
  have e : ∀ y : k, (fun i : Fin 3 => (![Polynomial.C t * Polynomial.X, Polynomial.X,
      Polynomial.C t] i).eval y) = ![t * y, y, t] := fun y => by
    funext i; fin_cases i <;> simp
  have key := eval_zero_of_forall ![Polynomial.C t * Polynomial.X, Polynomial.X,
      Polynomial.C t] g (fun y hy => by
    rw [e y]
    have := h ![t * y, y] t (chart_mem' t y) (fun h0 => hy (by simpa using congrFun h0 1))
    simpa using this)
  simpa [e 0] using key

end density'
/-! #### 性質 (4'):`X` の既約性

`X ∩ U_t ≅ 𝔸²`(座標 `(x, u)`、`y = x u`)と `X ∩ U_u ≅ 𝔸²`(座標 `(y, t)`、`x = t y`)は
整域の座標環を持ち(各チャートで既約)、2 つのチャート上の空でない基本開集合は交わる。 -/

section irreducible
variable [Infinite k]

omit [Infinite k] in
lemma eval_aeval_vec2 (φ : Fin 3 → MvPolynomial (Fin 2) k) (g : MvPolynomial (Fin 3) k)
    (a : Fin 2 → k) :
    MvPolynomial.eval a (MvPolynomial.aeval φ g) =
      MvPolynomial.eval (fun i => MvPolynomial.eval a (φ i)) g := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

/-- チャート `t` の座標環への引き戻し `g ↦ g(x, x u, u)`。 -/
noncomputable def pullT (g : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![X 0, X 0 * X 1, X 1] g

/-- チャート `u` の座標環への引き戻し `g ↦ g(t y, y, t)`(`y = X 0`, `t = X 1`)。 -/
noncomputable def pullU (g : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![X 1 * X 0, X 0, X 1] g

omit [Infinite k] in
lemma eval_pullT (g : MvPolynomial (Fin 3) k) (a b : k) :
    MvPolynomial.eval ![a, b] (pullT g) = MvPolynomial.eval ![a, a * b, b] g := by
  have e : (fun i : Fin 3 => MvPolynomial.eval ![a, b] (![X 0, X 0 * X 1, X 1] i)) =
      ![a, a * b, b] := by funext i; fin_cases i <;> simp
  rw [pullT, eval_aeval_vec2, e]

omit [Infinite k] in
lemma eval_pullU (g : MvPolynomial (Fin 3) k) (y t : k) :
    MvPolynomial.eval ![y, t] (pullU g) = MvPolynomial.eval ![t * y, y, t] g := by
  have e : (fun i : Fin 3 => MvPolynomial.eval ![y, t] (![X 1 * X 0, X 0, X 1] i)) =
      ![t * y, y, t] := by funext i; fin_cases i <;> simp [mul_comm]
  rw [pullU, eval_aeval_vec2, e]

/-- チャート `t` 上で `g` が `X` の全点で消えることは、`pullT g = 0` と同値。 -/
theorem vanishes_chart_t_iff (g : MvPolynomial (Fin 3) k) :
    (∀ (P : Fin 2 → k) (u : k), (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k →
      MvPolynomial.eval ![P 0, P 1, u] g = 0) ↔ pullT g = 0 := by
  constructor
  · intro h
    refine MvPolynomial.funext fun a => ?_
    have := h ![a 0, a 0 * a 1] (a 1) (chart_mem _ _)
    simp only [map_zero]
    rw [show a = ![a 0, a 1] by ext i; fin_cases i <;> rfl, eval_pullT]
    simpa using this
  · intro h P u hP
    rw [mem_blowupSet_iff (one_ne_zero_vec u) rfl] at hP
    have h1 : P 1 = P 0 * u := by simpa using hP.symm
    have := congrArg (MvPolynomial.eval ![P 0, u]) h
    rw [eval_pullT] at this
    simpa [h1] using this

theorem vanishes_chart_u_iff (g : MvPolynomial (Fin 3) k) :
    (∀ (P : Fin 2 → k) (t : k), (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k →
      MvPolynomial.eval ![P 0, P 1, t] g = 0) ↔ pullU g = 0 := by
  constructor
  · intro h
    refine MvPolynomial.funext fun a => ?_
    have := h ![a 1 * a 0, a 0] (a 1) (chart_mem' _ _)
    simp only [map_zero]
    rw [show a = ![a 0, a 1] by ext i; fin_cases i <;> rfl, eval_pullU]
    simpa using this
  · intro h P t hP
    rw [mem_blowupSet_iff (one_ne_zero_vec' t) rfl] at hP
    have h0 : P 0 = t * P 1 := by simpa using hP
    have := congrArg (MvPolynomial.eval ![P 1, t]) h
    rw [eval_pullU] at this
    simpa [h0] using this

/-- 各チャートは整域(既約):`g₁ g₂` が `X ∩ U_t` 上で消えるなら、どちらかが消える。 -/
theorem irreducible_chart_t (g₁ g₂ : MvPolynomial (Fin 3) k)
    (h : ∀ (P : Fin 2 → k) (u : k), (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k →
      MvPolynomial.eval ![P 0, P 1, u] (g₁ * g₂) = 0) :
    (∀ (P : Fin 2 → k) (u : k), (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k →
      MvPolynomial.eval ![P 0, P 1, u] g₁ = 0) ∨
    (∀ (P : Fin 2 → k) (u : k), (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k →
      MvPolynomial.eval ![P 0, P 1, u] g₂ = 0) := by
  rw [vanishes_chart_t_iff] at h ⊢
  rw [vanishes_chart_t_iff]
  have e : pullT (g₁ * g₂) = pullT g₁ * pullT g₂ := by simp only [pullT, map_mul]
  have : pullT g₁ * pullT g₂ = 0 := by rw [← e]; exact h
  exact mul_eq_zero.mp this

theorem irreducible_chart_u (g₁ g₂ : MvPolynomial (Fin 3) k)
    (h : ∀ (P : Fin 2 → k) (t : k), (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k →
      MvPolynomial.eval ![P 0, P 1, t] (g₁ * g₂) = 0) :
    (∀ (P : Fin 2 → k) (t : k), (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k →
      MvPolynomial.eval ![P 0, P 1, t] g₁ = 0) ∨
    (∀ (P : Fin 2 → k) (t : k), (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k →
      MvPolynomial.eval ![P 0, P 1, t] g₂ = 0) := by
  rw [vanishes_chart_u_iff] at h ⊢
  rw [vanishes_chart_u_iff]
  have e : pullU (g₁ * g₂) = pullU g₁ * pullU g₂ := by simp only [pullU, map_mul]
  have : pullU g₁ * pullU g₂ = 0 := by rw [← e]; exact h
  exact mul_eq_zero.mp this

/-- `H(y, t)` の `y = a b`、`t = 1/b` での値の分母を `b^M` で払った多項式
(`y^i t^j ↦ a^i b^(i + M - j)`)。 -/
noncomputable def clearU (H : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 2) k :=
  ∑ s ∈ H.support, monomial (mon2 (s 0) (s 0 + H.support.sup (fun s => s 1) - s 1)) (coeff s H)

omit [Infinite k] in
lemma eval_clearU (H : MvPolynomial (Fin 2) k) (a : k) {b : k} (hb : b ≠ 0) :
    MvPolynomial.eval ![a, b] (clearU H) =
      b ^ H.support.sup (fun s => s 1) * MvPolynomial.eval ![a * b, b⁻¹] H := by
  rw [clearU, map_sum, MvPolynomial.eval_eq' (![a * b, b⁻¹]) H, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hM : s 1 ≤ H.support.sup (fun s => s 1) := Finset.le_sup (f := fun s => s 1) hs
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hM
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Fin.prod_univ_two, mon2_zero, mon2_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hd, show s 0 + (s 1 + d) - s 1 = s 0 + d by omega]
  have hbi : b ^ s 1 * b⁻¹ ^ s 1 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hb, one_pow]
  linear_combination (coeff s H * a ^ s 0 * b ^ s 0 * b ^ d) * (-hbi)

omit [Infinite k] in
lemma clearU_ne_zero {H : MvPolynomial (Fin 2) k} (hH : H ≠ 0) : clearU H ≠ 0 := by
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hH
  intro h0
  have hM : s 1 ≤ H.support.sup (fun s => s 1) := Finset.le_sup (f := fun s => s 1) hs
  have key : coeff (mon2 (s 0) (s 0 + H.support.sup (fun s => s 1) - s 1)) (clearU H) = coeff s H := by
    rw [clearU, coeff_sum, Finset.sum_eq_single s]
    · simp [coeff_monomial]
    · intro s' hs' hne
      rw [coeff_monomial, if_neg]
      intro heq
      apply hne
      have e0 := congrArg (fun m => m 0) heq
      have e1 := congrArg (fun m => m 1) heq
      have hM' : s' 1 ≤ H.support.sup (fun s => s 1) := Finset.le_sup (f := fun s => s 1) hs'
      simp at e0 e1
      ext i; fin_cases i <;> simp <;> omega
    · intro hns; exact absurd hs hns
  rw [h0] at key
  exact (mem_support_iff.mp hs) (by simpa using key.symm)

/-- 重なりの存在:`U_t` と `U_u` 上の空でない基本開集合 `D(g)`, `D(h)` は `X` の中で交わる。
(各チャートの既約性 `irreducible_chart_t/u` と合わせて `X` の既約性。) -/
theorem irreducible_overlap (g h : MvPolynomial (Fin 3) k)
    (hg : ∃ (P : Fin 2 → k) (u : k), (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k ∧
      MvPolynomial.eval ![P 0, P 1, u] g ≠ 0)
    (hh : ∃ (P : Fin 2 → k) (t : k), (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k ∧
      MvPolynomial.eval ![P 0, P 1, t] h ≠ 0) :
    ∃ (P : Fin 2 → k) (u t : k) (_hut : mk k ![1, u] (one_ne_zero_vec u) =
        mk k ![t, 1] (one_ne_zero_vec' t)),
      (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k ∧
      MvPolynomial.eval ![P 0, P 1, u] g ≠ 0 ∧ MvPolynomial.eval ![P 0, P 1, t] h ≠ 0 := by
  have hG : pullT g ≠ 0 := fun h0 => by
    obtain ⟨P, u, hP, hne⟩ := hg
    exact hne ((vanishes_chart_t_iff g).mpr h0 P u hP)
  have hH : pullU h ≠ 0 := fun h0 => by
    obtain ⟨P, t, hP, hne⟩ := hh
    exact hne ((vanishes_chart_u_iff h).mpr h0 P t hP)
  have hprod : pullT g * clearU (pullU h) * X 1 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hG (clearU_ne_zero hH)) (X_ne_zero _)
  obtain ⟨z, hz⟩ : ∃ z : Fin 2 → k, MvPolynomial.eval z (pullT g * clearU (pullU h) * X 1) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hprod (MvPolynomial.funext fun z => by simpa using hcon z)
  simp only [map_mul, MvPolynomial.eval_X] at hz
  have hz1 := mul_ne_zero_iff.mp hz
  have hz2 := mul_ne_zero_iff.mp hz1.1
  have hz' : z = ![z 0, z 1] := by ext i; fin_cases i <;> rfl
  have ez : ∀ f : MvPolynomial (Fin 2) k, MvPolynomial.eval z f = MvPolynomial.eval ![z 0, z 1] f :=
    fun f => congrArg (fun w => MvPolynomial.eval w f) hz'
  have hb : z 1 ≠ 0 := hz1.2
  have hQ : MvPolynomial.eval ![z 0 * z 1, (z 1)⁻¹] (pullU h) ≠ 0 := by
    have := hz2.2
    rw [ez, eval_clearU _ _ hb] at this
    exact right_ne_zero_of_mul this
  have hG' : MvPolynomial.eval ![z 0, z 1] (pullT g) ≠ 0 := by
    have := hz2.1
    rwa [ez] at this
  refine ⟨![z 0, z 0 * z 1], z 1, (z 1)⁻¹, ?_, chart_mem (z 0) (z 1), ?_, ?_⟩
  · rw [mk_eq_mk_iff']
    refine ⟨z 1, ?_⟩
    ext i; fin_cases i <;> simp [hb]
  · rw [eval_pullT] at hG'
    simpa using hG'
  · rw [eval_pullU] at hQ
    have e : (z 1)⁻¹ * (z 0 * z 1) = z 0 := by field_simp
    rw [e] at hQ
    simpa using hQ
end irreducible

/-! #### strict transform は `φ⁻¹(Y ∖ 0)` の Zariski 閉包(チャート `t` 上)

`k` は代数閉体(`x² + u² = 0` のように `x ∤ f̃` でも実点が足りない例があるため必須)。
鍵は `x ∤ f̃`(`not_dvd_strict`)と Nullstellensatz。 -/

section closure
variable [IsAlgClosed k]

/-- 根基の議論:`x g` が `Z(q)` 上で消え、`x ∤ q` なら `g` は `Z(q)` 上で消える。 -/
lemma vanishes_of_vanishes_off_x (i : Fin 2) (q g : Poly k) (hq : ¬ X i ∣ q)
    (h : ∀ p : Fin 2 → k, p i ≠ 0 → MvPolynomial.eval p q = 0 → MvPolynomial.eval p g = 0) :
    ∀ p : Fin 2 → k, MvPolynomial.eval p q = 0 → MvPolynomial.eval p g = 0 := by
  have hmem : X i * g ∈ MvPolynomial.vanishingIdeal k
      (MvPolynomial.zeroLocus k (Ideal.span {q} : Ideal (Poly k))) := by
    intro p hp
    have hq0 : MvPolynomial.eval p q = 0 := hp q (Ideal.subset_span rfl)
    by_cases hp0 : p i = 0
    · show MvPolynomial.eval p (X i * g) = 0
      simp [hp0]
    · show MvPolynomial.eval p (X i * g) = 0
      simp [h p hp0 hq0]
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hmem
  obtain ⟨n, hn⟩ := hmem
  rw [mul_pow, Ideal.mem_span_singleton] at hn
  have hrp : IsRelPrime q (X i ^ n) :=
    ((MvPolynomial.X_prime (R := k) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr hq).symm.pow_right
  obtain ⟨c, hc⟩ := hrp.dvd_of_dvd_mul_left hn
  intro p hp
  have := congrArg (MvPolynomial.eval p) hc
  rw [map_mul, hp, zero_mul, map_pow] at this
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp at this
  · exact (pow_eq_zero_iff hn0.ne').mp this
/-- 切断 `φ⁻¹(Y ∖ 0)` のチャート `t` 座標 `(x, u)`:`x ≠ 0` かつ `f(x, x u) = 0`。 -/
def preimageT (f : Poly k) : Set (Fin 2 → k) :=
  {p | p 0 ≠ 0 ∧ MvPolynomial.eval ![p 0, p 0 * p 1] f = 0}

/-- チャートの Zariski 閉包(消える多項式の共通零点)。 -/
def zclosure (S : Set (Fin 2 → k)) : Set (Fin 2 → k) :=
  {p | ∀ g : Poly k, (∀ s ∈ S, MvPolynomial.eval s g = 0) → MvPolynomial.eval p g = 0}

omit [IsAlgClosed k] [Field k] in
lemma vec2_eta (p : Fin 2 → k) : p = ![p 0, p 1] := by ext i; fin_cases i <;> rfl

/-- **`Ỹ = closure(φ⁻¹(Y ∖ 0)) = Z(f̃)`**(チャート `t` 上、`k` 代数閉体、`f ≠ 0`)。 -/
theorem closure_preimage_eq_strict (f : Poly k) (hf : f ≠ 0) :
    zclosure (preimageT f) = {p | MvPolynomial.eval p (strict f) = 0} := by
  ext p
  constructor
  · intro hp
    refine hp (strict f) fun s hs => ?_
    obtain ⟨hs0, hs1⟩ := hs
    rw [vec2_eta s]
    exact (eval_strict_iff f hs0 (s 1)).mp hs1
  · intro hp g hg
    refine vanishes_of_vanishes_off_x 0 (strict f) g (not_dvd_strict hf) (fun q hq0 hqz => ?_) p hp
    refine hg q ⟨hq0, ?_⟩
    rw [vec2_eta q] at hqz
    exact (eval_strict_iff f hq0 (q 1)).mpr hqz

/-- `Ỹ ∩ E`:閉包の `x = 0` 上の点は、最低次斉次部分 `f_r(1, u) = 0` の根(接線方向)。 -/
theorem closure_preimage_inter_E (f : Poly k) (hf : f ≠ 0) (u : k) :
    (![0, u] : Fin 2 → k) ∈ zclosure (preimageT f) ↔
      ∑ s ∈ f.support.filter (fun s => deg s = mult f), coeff s f * u ^ (s 1) = 0 := by
  rw [closure_preimage_eq_strict f hf, Set.mem_setOf_eq, ← eval_strict_zero]


/-! ##### チャート `u = 1`(座標 `(t, y)`、`x = t y`) -/

omit [IsAlgClosed k] in
lemma eval_swapXY (g : Poly k) (a : Fin 2 → k) :
    MvPolynomial.eval a (swapXY g) = MvPolynomial.eval ![a 1, a 0] g := by
  have e : (a ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![a 1, a 0] := by
    funext i; fin_cases i <;> simp
  rw [swapXY, MvPolynomial.eval_rename, e]

/-- チャート `u` の strict transform:`f(t y, y) = y^r f̃'(t, y)`。 -/
noncomputable def strictU (f : Poly k) : Poly k := swapXY (strict (swapXY f))

omit [IsAlgClosed k] in
lemma sub'_eq (f : Poly k) : sub' f = X 1 ^ mult f * strictU f := by
  have h := congrArg swapXY (sub_eq (swapXY f))
  rw [map_mul, map_pow, swapXY_X0, mult_swapXY] at h
  rw [strictU]
  simpa [sub'] using h

omit [IsAlgClosed k] in
lemma eval_sub' (f : Poly k) (a : Fin 2 → k) :
    MvPolynomial.eval a (sub' f) = MvPolynomial.eval ![a 0 * a 1, a 1] f := by
  simp only [sub', AlgHom.comp_apply, eval_swapXY, eval_sub]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_comm]

omit [IsAlgClosed k] in
theorem eval_strictU_iff (f : Poly k) {y : k} (hy : y ≠ 0) (t : k) :
    MvPolynomial.eval ![t * y, y] f = 0 ↔ MvPolynomial.eval ![t, y] (strictU f) = 0 := by
  have h := congrArg (MvPolynomial.eval ![t, y]) (sub'_eq f)
  rw [eval_sub', map_mul, map_pow, MvPolynomial.eval_X] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  simp [hy]

omit [IsAlgClosed k] in
theorem not_dvd_strictU {f : Poly k} (hf : f ≠ 0) : ¬ X 1 ∣ strictU f := by
  rintro ⟨h, hh⟩
  refine not_dvd_strict (swapXY_ne_zero hf) ⟨swapXY h, ?_⟩
  have := congrArg swapXY hh
  rw [strictU, swapXY_swapXY, map_mul, swapXY_X1] at this
  exact this

/-- 切断 `φ⁻¹(Y ∖ 0)` のチャート `u` 座標 `(t, y)`:`y ≠ 0` かつ `f(t y, y) = 0`。 -/
def preimageU (f : Poly k) : Set (Fin 2 → k) :=
  {p | p 1 ≠ 0 ∧ MvPolynomial.eval ![p 0 * p 1, p 1] f = 0}

/-- **`Ỹ = closure(φ⁻¹(Y ∖ 0)) = Z(f̃')`**(チャート `u` 上)。 -/
theorem closure_preimageU_eq_strictU (f : Poly k) (hf : f ≠ 0) :
    zclosure (preimageU f) = {p | MvPolynomial.eval p (strictU f) = 0} := by
  ext p
  constructor
  · intro hp
    refine hp (strictU f) fun s hs => ?_
    obtain ⟨hs0, hs1⟩ := hs
    rw [vec2_eta s]
    exact (eval_strictU_iff f hs0 (s 0)).mp hs1
  · intro hp g hg
    refine vanishes_of_vanishes_off_x 1 (strictU f) g (not_dvd_strictU hf) (fun q hq0 hqz => ?_) p hp
    refine hg q ⟨hq0, ?_⟩
    rw [vec2_eta q] at hqz
    exact (eval_strictU_iff f hq0 (q 0)).mpr hqz

end closure


/-! #### 接線の重複度:`Ỹ ∩ E` の接線方向の重複度の総和は `r = mult f`

最低次斉次部分 `f_r` の 2 変数形式を、`P(u) = f_r(1, u)`(チャート `t`)と
`P^∞(t) = f_r(t, 1) = t^r P(1/t)`(チャート `u`)で表す。`P` の根が `u` 座標の接線方向
(`closure_preimage_inter_E`)、`P^∞` の `t = 0` での根の位数が点 `[0:1]` の重複度。
全部足すと `r`(`Ỹ · E = r` の代数的な形)。 -/

section tangent

/-- 最低次斉次部分の `f_r(1, u)`(`u` の多項式)。 -/
noncomputable def tangentPoly (f : Poly k) : Polynomial k :=
  ∑ j ∈ Finset.range (mult f + 1),
    Polynomial.C (coeff (mon2 (mult f - j) j) f) * Polynomial.X ^ j

/-- 無限遠方向 `f_r(t, 1) = t^r f_r(1, 1/t)`。 -/
noncomputable def tangentPolyU (f : Poly k) : Polynomial k := (tangentPoly f).reflect (mult f)

lemma coeff_tangentPoly (f : Poly k) (j : ℕ) :
    (tangentPoly f).coeff j = if j ≤ mult f then coeff (mon2 (mult f - j) j) f else 0 := by
  rw [tangentPoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_iff]

lemma natDegree_tangentPoly_le (f : Poly k) : (tangentPoly f).natDegree ≤ mult f :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => by
    rw [coeff_tangentPoly, if_neg (by omega)]

lemma tangentPoly_ne_zero {f : Poly k} (hf : f ≠ 0) : tangentPoly f ≠ 0 := by
  obtain ⟨s, hs, hsd⟩ := exists_mult hf
  intro h
  have hcoef := coeff_tangentPoly f (s 1)
  rw [h, Polynomial.coeff_zero] at hcoef
  have hle : s 1 ≤ mult f := by rw [← hsd]; simp [deg]
  rw [if_pos hle] at hcoef
  have e : mon2 (mult f - s 1) (s 1) = s := by
    rw [← hsd]; ext i; fin_cases i <;> simp [deg]
  rw [e] at hcoef
  exact (mem_support_iff.mp hs) hcoef.symm

lemma eval_tangentPoly (f : Poly k) (u : k) :
    (tangentPoly f).eval u =
      ∑ s ∈ f.support.filter (fun s => deg s = mult f), coeff s f * u ^ (s 1) := by
  rw [tangentPoly, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hinj : Set.InjOn (fun s : Fin 2 →₀ ℕ => s 1)
      ↑(f.support.filter (fun s => deg s = mult f)) := by
    intro s hs s' hs' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs hs'
    have h0 : s 0 = s' 0 := by
      have := hs.2.trans hs'.2.symm
      simp only [deg] at this h
      omega
    ext i; fin_cases i
    · exact h0
    · exact h
  have h1 : ∑ s ∈ f.support.filter (fun s => deg s = mult f), coeff s f * u ^ (s 1) =
      ∑ s ∈ f.support.filter (fun s => deg s = mult f),
        (fun j => coeff (mon2 (mult f - j) j) f * u ^ j) (s 1) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hd := (Finset.mem_filter.mp hs).2
    have e : mon2 (mult f - s 1) (s 1) = s := by
      rw [← hd]; ext i; fin_cases i <;> simp [deg]
    simp only [e]
  rw [h1, ← Finset.sum_image (f := fun j => coeff (mon2 (mult f - j) j) f * u ^ j) hinj]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
    have hd := Finset.mem_filter.mp hs
    rw [Finset.mem_range, Nat.lt_succ_iff, ← hd.2]
    simp [deg]
  · intro j hj hnot
    have : coeff (mon2 (mult f - j) j) f = 0 := by
      by_contra hne
      apply hnot
      refine Finset.mem_image.mpr ⟨mon2 (mult f - j) j, ?_, by simp⟩
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr hne, ?_⟩
      have hjle : j ≤ mult f := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp [deg_mon2]
      omega
    simp [this]

/-- `P` の `reflect` の `0` での根の位数は `N - deg P`。 -/
lemma rootMultiplicity_zero_reflect {P : Polynomial k} (hP : P ≠ 0) {N : ℕ}
    (hN : P.natDegree ≤ N) :
    (P.reflect N).rootMultiplicity 0 = N - P.natDegree := by
  have hrefl : P.reflect N = Polynomial.X ^ (N - P.natDegree) * P.reverse := by
    ext n
    rw [Polynomial.coeff_reflect, Polynomial.coeff_X_pow_mul', Polynomial.coeff_reverse]
    by_cases hn : n ≤ N
    · rw [Polynomial.revAt_le hn]
      by_cases hm : N - P.natDegree ≤ n
      · rw [if_pos hm, Polynomial.revAt_le (by omega)]
        congr 1; omega
      · rw [if_neg hm]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · push_neg at hn
      rw [Polynomial.revAt_eq_self_of_lt hn, if_pos (by omega),
        Polynomial.revAt_eq_self_of_lt (by omega)]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  rw [hrefl, Polynomial.rootMultiplicity_eq_natTrailingDegree]
  simp only [map_zero, add_zero, Polynomial.comp_X]
  rw [Polynomial.natTrailingDegree_mul (by simp) (by simpa using hP),
    Polynomial.natTrailingDegree_X_pow, Polynomial.natTrailingDegree_reverse]
  simp

/-- **接線の重複度の総和**:`k` 代数閉体、`f ≠ 0` で、
`f_r(1, u)` の根(重複度込み)の個数と、無限遠の点 `[0:1]` での重複度の和は `r = mult f`。 -/
theorem tangent_total [IsAlgClosed k] {f : Poly k} (hf : f ≠ 0) :
    (tangentPoly f).roots.card + (tangentPolyU f).rootMultiplicity 0 = mult f := by
  have hP := tangentPoly_ne_zero hf
  have hle := natDegree_tangentPoly_le f
  rw [tangentPolyU, rootMultiplicity_zero_reflect hP hle, IsAlgClosed.card_roots_eq_natDegree]
  omega

/-- `Ỹ ∩ E` の点(チャート `t`)は `tangentPoly` の根で、その重複度は `rootMultiplicity`。 -/
theorem closure_preimage_inter_E_root [IsAlgClosed k] (f : Poly k) (hf : f ≠ 0) (u : k) :
    (![0, u] : Fin 2 → k) ∈ zclosure (preimageT f) ↔ (tangentPoly f).IsRoot u := by
  rw [closure_preimage_inter_E f hf, Polynomial.IsRoot, eval_tangentPoly]


/-! ##### 無限遠側:`f̃'(t, 0) = f_r(t, 1)` -/

lemma coeff_swapXY_mon2 (f : Poly k) (a b : ℕ) :
    coeff (mon2 a b) (swapXY f) = coeff (mon2 b a) f := by
  have h := MvPolynomial.coeff_rename_mapDomain (Equiv.swap (0 : Fin 2) 1)
    (Equiv.injective _) f (mon2 b a)
  have e : Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) (mon2 b a) = mon2 a b := by
    ext i; fin_cases i
    · simpa using Finsupp.mapDomain_apply (Equiv.injective (Equiv.swap (0 : Fin 2) 1))
        (mon2 b a) 1
    · simpa using Finsupp.mapDomain_apply (Equiv.injective (Equiv.swap (0 : Fin 2) 1))
        (mon2 b a) 0
  rw [e] at h
  exact h

/-- 入れ替えた多項式の接線多項式は、無限遠側の多項式 `tangentPolyU` に一致する。 -/
lemma tangentPoly_swapXY (f : Poly k) : tangentPoly (swapXY f) = tangentPolyU f := by
  ext i
  rw [coeff_tangentPoly, mult_swapXY, tangentPolyU, Polynomial.coeff_reflect]
  by_cases hi : i ≤ mult f
  · rw [if_pos hi, Polynomial.revAt_le hi, coeff_tangentPoly, if_pos (Nat.sub_le _ _),
      coeff_swapXY_mon2, Nat.sub_sub_self hi]
  · rw [if_neg hi, Polynomial.revAt_eq_self_of_lt (by omega), coeff_tangentPoly, if_neg hi]

/-- **`eval_strictU_zero`**:`f̃'(t, 0) = f_r(t, 1)`。 -/
theorem eval_strictU_zero (f : Poly k) (t : k) :
    MvPolynomial.eval ![t, 0] (strictU f) = (tangentPolyU f).eval t := by
  rw [strictU, eval_swapXY, ← tangentPoly_swapXY, eval_tangentPoly, ← eval_strict_zero]
  simp

/-- `Ỹ ∩ E` の点(チャート `u`、`[t : 1]`)は `tangentPolyU` の根。特に `t = 0` が
点 `[0 : 1]` で、その重複度が `rootMultiplicity 0 (tangentPolyU f)`。 -/
theorem closure_preimageU_inter_E_root [IsAlgClosed k] (f : Poly k) (hf : f ≠ 0) (t : k) :
    (![t, 0] : Fin 2 → k) ∈ zclosure (preimageU f) ↔ (tangentPolyU f).IsRoot t := by
  rw [closure_preimageU_eq_strictU f hf, Set.mem_setOf_eq, Polynomial.IsRoot,
    ← eval_strictU_zero]


/-! ##### 重なり `t ≠ 0` での整合性:`[1 : 1/t] = [t : 1]` の接線の重複度は一致する -/

lemma reflect_pow_X_sub_C (a : k) (n : ℕ) :
    ((Polynomial.X - Polynomial.C a) ^ n).reflect n = (1 - Polynomial.C a * Polynomial.X) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdeg : ((Polynomial.X - Polynomial.C a) ^ n).natDegree ≤ n :=
      (Polynomial.natDegree_pow_le).trans (by simp)
    have h1 : (Polynomial.X - Polynomial.C a).natDegree ≤ 1 := by simp
    rw [pow_succ, Polynomial.reflect_mul _ _ hdeg h1, ih, pow_succ]
    congr 1
    rw [Polynomial.reflect_sub, Polynomial.reflect_one_X, Polynomial.reflect_C]
    simp

/-- 体上、`c ≠ 0` なら `P` の `c⁻¹` での根の位数は `reflect N P` の `c` での根の位数に等しい。 -/
theorem rootMultiplicity_inv_reflect {P : Polynomial k} (hP : P ≠ 0) {N : ℕ}
    (hN : P.natDegree ≤ N) {c : k} (hc : c ≠ 0) :
    P.rootMultiplicity c⁻¹ = (P.reflect N).rootMultiplicity c := by
  set a := c⁻¹ with ha
  have hac : a * c = 1 := inv_mul_cancel₀ hc
  have ha0 : a ≠ 0 := inv_ne_zero hc
  set m := P.rootMultiplicity a with hm
  set Q := P /ₘ (Polynomial.X - Polynomial.C a) ^ m with hQdef
  have hPQ : (Polynomial.X - Polynomial.C a) ^ m * Q = P :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq P a
  have hQ0 : Q ≠ 0 := fun h => hP (by rw [← hPQ, h, mul_zero])
  have hQa : Q.eval a ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hP
  have hdeg : P.natDegree = m + Q.natDegree := by
    conv_lhs => rw [← hPQ]
    rw [Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)) hQ0,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    ring
  have hmN : m ≤ N := by omega
  have hQN : Q.natDegree ≤ N - m := by omega
  have hpowdeg : ((Polynomial.X - Polynomial.C a) ^ m).natDegree ≤ m :=
    (Polynomial.natDegree_pow_le).trans (by simp)
  have hlin : (1 : Polynomial k) - Polynomial.C a * Polynomial.X =
      Polynomial.C (-a) * (Polynomial.X - Polynomial.C c) := by
    have h2 : Polynomial.C a * Polynomial.C c = 1 := by rw [← Polynomial.C_mul, hac, Polynomial.C_1]
    rw [map_neg]
    linear_combination (-1 : Polynomial k) * h2
  have hrefl : P.reflect N =
      Polynomial.C ((-a) ^ m) * (Polynomial.X - Polynomial.C c) ^ m * Q.reflect (N - m) := by
    have key := Polynomial.reflect_mul ((Polynomial.X - Polynomial.C a) ^ m) Q hpowdeg hQN
    rw [Nat.add_sub_cancel' hmN, hPQ] at key
    rw [key, reflect_pow_X_sub_C, hlin, mul_pow, map_pow]
  have hRc : ¬ (Q.reflect (N - m)).IsRoot c := by
    intro hroot
    letI : Invertible a := invertibleOfNonzero ha0
    have hinv : ⅟a = c := by rw [invOf_eq_inv, ha, inv_inv]
    have := Polynomial.eval₂_reflect_mul_pow (RingHom.id k) a (N - m) Q hQN
    rw [hinv] at this
    have hz : Polynomial.eval₂ (RingHom.id k) c (Q.reflect (N - m)) = 0 := hroot
    rw [hz, zero_mul] at this
    exact hQa this.symm
  have hne : Polynomial.C ((-a) ^ m) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr ha0))
  have hnz : Polynomial.C ((-a) ^ m) * (Polynomial.X - Polynomial.C c) ^ m * Q.reflect (N - m) ≠ 0 := by
    rw [← hrefl]; exact fun h => hP (Polynomial.reflect_eq_zero_iff.mp h)
  rw [hrefl, Polynomial.rootMultiplicity_mul hnz, Polynomial.rootMultiplicity_mul_X_sub_C_pow hne,
    Polynomial.rootMultiplicity_C, Polynomial.rootMultiplicity_eq_zero hRc]
  simp [hm]

/-- 重なり `t ≠ 0` で、チャート `t`(座標 `u = 1/t`)とチャート `u`(座標 `t`)の接線の
重複度は一致する。 -/
theorem rootMultiplicity_tangent_overlap {f : Poly k} (hf : f ≠ 0) {t : k} (ht : t ≠ 0) :
    (tangentPoly f).rootMultiplicity t⁻¹ = (tangentPolyU f).rootMultiplicity t := by
  rw [tangentPolyU]
  exact rootMultiplicity_inv_reflect (tangentPoly_ne_zero hf) (natDegree_tangentPoly_le f) ht

/-- 同じ点 `[t : 1] = [1 : 1/t]` は、チャート `t` で閉包に入ることとチャート `u` で入ることが同値。 -/
theorem overlap_mem_iff [IsAlgClosed k] {f : Poly k} (hf : f ≠ 0) {t : k} (ht : t ≠ 0) :
    (![0, t⁻¹] : Fin 2 → k) ∈ zclosure (preimageT f) ↔ (![t, 0] : Fin 2 → k) ∈ zclosure (preimageU f) := by
  rw [closure_preimage_inter_E_root f hf, closure_preimageU_inter_E_root f hf]
  have hPU : tangentPolyU f ≠ 0 := fun h =>
    tangentPoly_ne_zero hf (Polynomial.reflect_eq_zero_iff.mp h)
  rw [← Polynomial.rootMultiplicity_pos (tangentPoly_ne_zero hf),
    ← Polynomial.rootMultiplicity_pos hPU, rootMultiplicity_tangent_overlap hf ht]

end tangent

end geometry

end Blowup

