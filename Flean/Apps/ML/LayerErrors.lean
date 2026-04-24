import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.Basic
import Flean.Apps.ML.Softmax

/-!
# Flean.Apps.ML.LayerErrors

Layer-composition error bounds: residual connections, Lipschitz composition,
and multi-layer error accumulation. These are the list / real-valued
counterparts of the transformer-block error-propagation theorems referenced
in the paper's Month 6-7 plan. They are stated in pure real analysis so
they remain reusable across FP8, FP4, and INT8 kernels.
-/

namespace Flean

/-! ## Residual connection: pointwise triangle inequality -/

/-- Scalar residual-connection error bound: the additive triangle inequality
    specialised to `x + f(x)`. -/
theorem residual_connection_error_scalar (x x' fx fx' : ℝ) :
    |(x + fx) - (x' + fx')| ≤ |x - x'| + |fx - fx'| := by
  have h : (x + fx) - (x' + fx') = (x - x') + (fx - fx') := by ring
  rw [h]
  exact abs_add_le _ _

/-- List-level residual-connection error bound: if pointwise errors on `x` and
    `fx` are bounded by `δx` and `δf` (L∞ per coordinate), then the residual
    `x + fx` has pointwise error bounded by `δx + δf`. -/
theorem residual_connection_error_bound
    (x x' fx fx' : List ℝ)
    (hlen1 : x.length = x'.length)
    (hlen2 : fx.length = fx'.length)
    (hlen3 : x.length = fx.length)
    {δx δf : ℝ}
    (hbx : ∀ d ∈ x.zipWith (fun a b => |a - b|) x', d ≤ δx)
    (hbf : ∀ d ∈ fx.zipWith (fun a b => |a - b|) fx', d ≤ δf) :
    ∀ d ∈ (x.zipWith (· + ·) fx).zipWith (fun a b => |a - b|)
            (x'.zipWith (· + ·) fx'),
      d ≤ δx + δf := by
  induction x generalizing x' fx fx' with
  | nil =>
    cases x' with
    | cons _ _ => simp at hlen1
    | nil =>
      cases fx with
      | cons _ _ => simp at hlen3
      | nil =>
        cases fx' with
        | cons _ _ => simp at hlen2
        | nil =>
          intro d hd
          simp at hd
  | cons xh xt ih =>
    cases x' with
    | nil => simp at hlen1
    | cons xh' xt' =>
      cases fx with
      | nil => simp at hlen3
      | cons fh ft =>
        cases fx' with
        | nil => simp at hlen2
        | cons fh' ft' =>
          have hlen1' : xt.length = xt'.length := by
            simpa [List.length_cons] using hlen1
          have hlen2' : ft.length = ft'.length := by
            simpa [List.length_cons] using hlen2
          have hlen3' : xt.length = ft.length := by
            simpa [List.length_cons] using hlen3
          have hbxt : ∀ d' ∈ xt.zipWith (fun a b => |a - b|) xt', d' ≤ δx := by
            intro d' hd'
            exact hbx d' (by
              simp only [List.zipWith_cons_cons, List.mem_cons]
              exact Or.inr hd')
          have hbft : ∀ d' ∈ ft.zipWith (fun a b => |a - b|) ft', d' ≤ δf := by
            intro d' hd'
            exact hbf d' (by
              simp only [List.zipWith_cons_cons, List.mem_cons]
              exact Or.inr hd')
          have htail_ih := ih xt' ft ft' hlen1' hlen2' hlen3' hbxt hbft
          intro d hd
          simp only [List.zipWith_cons_cons, List.mem_cons] at hd
          rcases hd with rfl | htail
          · have h_xh : |xh - xh'| ≤ δx :=
              hbx _ (by simp [List.zipWith_cons_cons])
            have h_fh : |fh - fh'| ≤ δf :=
              hbf _ (by simp [List.zipWith_cons_cons])
            calc |xh + fh - (xh' + fh')|
                = |(xh - xh') + (fh - fh')| := by congr 1; ring
              _ ≤ |xh - xh'| + |fh - fh'| := abs_add_le _ _
              _ ≤ δx + δf := add_le_add h_xh h_fh
          · exact htail_ih d htail

/-! ## Lipschitz composition with additive error

One-step error propagation for a Lipschitz-with-error layer: if the
*input* side has error `δ` and the layer itself has Lipschitz constant `L`
and evaluation error `ε`, the *output* side has error `L · δ + ε`. This is
the recurrence that drives the multi-layer accumulation theorem.
-/

/-- One-step input/output error propagation for a Lipschitz-with-error layer:
    `|y − y'| ≤ δ` and `F` being `L`-Lipschitz with perturbed `F'` of error `ε`
    gives `|F y − F' y'| ≤ L · δ + ε`. -/
theorem lipschitz_with_error_step
    {F F' : ℝ → ℝ} {L ε : ℝ} (hLnn : 0 ≤ L)
    (hF_lip : ∀ a b, |F a - F b| ≤ L * |a - b|)
    (hF_err : ∀ y, |F y - F' y| ≤ ε)
    {y y' δ : ℝ} (hy : |y - y'| ≤ δ) :
    |F y - F' y'| ≤ L * δ + ε := by
  calc |F y - F' y'|
      = |(F y - F y') + (F y' - F' y')| := by congr 1; ring
    _ ≤ |F y - F y'| + |F y' - F' y'| := abs_add_le _ _
    _ ≤ L * |y - y'| + ε := add_le_add (hF_lip y y') (hF_err y')
    _ ≤ L * δ + ε := by
        have := mul_le_mul_of_nonneg_left hy hLnn
        linarith

/-- Specialisation of `lipschitz_with_error_step` with `y = y'` (no input
    error), recovering the plain composition bound `|G(Fx) − G'(F'x)| ≤
    L_G · ε_F + ε_G` (a scalar transformer-block error step). -/
theorem lipschitz_compose_with_error
    (F F' G G' : ℝ → ℝ)
    {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hG_lip : ∀ a b, |G a - G b| ≤ Lg * |a - b|)
    {εF εG : ℝ}
    (hF_err : ∀ x, |F x - F' x| ≤ εF)
    (hG_err : ∀ y, |G y - G' y| ≤ εG)
    (x : ℝ) :
    |G (F x) - G' (F' x)| ≤ Lg * εF + εG :=
  lipschitz_with_error_step (F := G) (F' := G') hLg hG_lip hG_err
    (hy := hF_err x)

/-! ## Multi-layer error accumulation

Iterating `lipschitz_with_error_step` across a list of layers gives a
telescoping `foldl` bound: after applying layers `[(F₁, F'₁, L₁, ε₁), …,
(Fₙ, F'ₙ, Lₙ, εₙ)]` in order, the end-to-end output error at a common
input `x` is bounded by

    Σ_{k=1..n} (∏_{j>k} L_j) · ε_k

which is the unique `foldl` that satisfies the one-step recurrence
`acc ↦ L · acc + ε`. -/

/-- A quantized layer: `(F, F', L, ε)` packages the ideal map `F`, the
    perturbed map `F'`, a Lipschitz constant `L` for `F`, and an error
    budget `ε` on `F'` (viewed as a perturbation of `F`). -/
abbrev QLayer : Type := (ℝ → ℝ) × (ℝ → ℝ) × ℝ × ℝ

/-- Apply the ideal map of a `QLayer`. -/
@[inline] def QLayer.F (lyr : QLayer) : ℝ → ℝ := lyr.1

/-- Apply the perturbed map of a `QLayer`. -/
@[inline] def QLayer.F' (lyr : QLayer) : ℝ → ℝ := lyr.2.1

/-- Lipschitz constant of `lyr.F`. -/
@[inline] def QLayer.L (lyr : QLayer) : ℝ := lyr.2.2.1

/-- Evaluation-error budget on `lyr.F'`. -/
@[inline] def QLayer.ε (lyr : QLayer) : ℝ := lyr.2.2.2

/-- Apply the list of ideal layers left-to-right starting from `x`. -/
def applyIdealLayers (layers : List QLayer) (x : ℝ) : ℝ :=
  layers.foldl (fun z lyr => lyr.F z) x

/-- Apply the list of perturbed layers left-to-right starting from `x`. -/
def applyPerturbedLayers (layers : List QLayer) (x : ℝ) : ℝ :=
  layers.foldl (fun z lyr => lyr.F' z) x

/-- Telescoping error budget: iterate the one-step recurrence
    `acc ↦ lyr.L · acc + lyr.ε` across the layer list. -/
def layerErrorBudget (layers : List QLayer) (δ0 : ℝ) : ℝ :=
  layers.foldl (fun acc lyr => lyr.L * acc + lyr.ε) δ0

theorem applyIdealLayers_cons (lyr : QLayer) (layers : List QLayer) (x : ℝ) :
    applyIdealLayers (lyr :: layers) x = applyIdealLayers layers (lyr.F x) := by
  simp [applyIdealLayers]

theorem applyPerturbedLayers_cons (lyr : QLayer) (layers : List QLayer) (x : ℝ) :
    applyPerturbedLayers (lyr :: layers) x =
      applyPerturbedLayers layers (lyr.F' x) := by
  simp [applyPerturbedLayers]

theorem layerErrorBudget_cons (lyr : QLayer) (layers : List QLayer) (δ0 : ℝ) :
    layerErrorBudget (lyr :: layers) δ0 =
      layerErrorBudget layers (lyr.L * δ0 + lyr.ε) := by
  simp [layerErrorBudget]

/-- **Multi-layer error accumulation**: applying a list of
    Lipschitz-with-error layers to inputs `y` and `y'` whose difference is
    bounded by `δ` produces outputs whose difference is bounded by
    `layerErrorBudget layers δ`. This is the formal end-to-end
    transformer-block error recurrence, driven by iterated application of
    `lipschitz_with_error_step`. -/
theorem multi_layer_error_accumulation
    (layers : List QLayer)
    (hLnn : ∀ lyr ∈ layers, 0 ≤ lyr.L)
    (hlip : ∀ lyr ∈ layers, ∀ a b, |lyr.F a - lyr.F b| ≤ lyr.L * |a - b|)
    (herr : ∀ lyr ∈ layers, ∀ z, |lyr.F z - lyr.F' z| ≤ lyr.ε)
    (y y' δ : ℝ) (hy : |y - y'| ≤ δ) :
    |applyIdealLayers layers y - applyPerturbedLayers layers y'|
      ≤ layerErrorBudget layers δ := by
  induction layers generalizing y y' δ with
  | nil =>
    simp [applyIdealLayers, applyPerturbedLayers, layerErrorBudget]
    exact hy
  | cons lyr rest ih =>
    have hlyr_mem : lyr ∈ lyr :: rest := List.mem_cons_self
    have hlyr_Lnn : 0 ≤ lyr.L := hLnn lyr hlyr_mem
    have hlyr_lip := hlip lyr hlyr_mem
    have hlyr_err := herr lyr hlyr_mem
    have hrest_Lnn : ∀ lyr' ∈ rest, 0 ≤ lyr'.L :=
      fun lyr' h => hLnn lyr' (List.mem_cons_of_mem _ h)
    have hrest_lip :
        ∀ lyr' ∈ rest, ∀ a b, |lyr'.F a - lyr'.F b| ≤ lyr'.L * |a - b| :=
      fun lyr' h => hlip lyr' (List.mem_cons_of_mem _ h)
    have hrest_err : ∀ lyr' ∈ rest, ∀ z, |lyr'.F z - lyr'.F' z| ≤ lyr'.ε :=
      fun lyr' h => herr lyr' (List.mem_cons_of_mem _ h)
    have hstep :
        |lyr.F y - lyr.F' y'| ≤ lyr.L * δ + lyr.ε :=
      lipschitz_with_error_step (F := lyr.F) (F' := lyr.F')
        hlyr_Lnn hlyr_lip hlyr_err hy
    rw [applyIdealLayers_cons, applyPerturbedLayers_cons, layerErrorBudget_cons]
    exact ih hrest_Lnn hrest_lip hrest_err _ _ _ hstep

/-! ## Affine layer error (LayerNorm γ / β quantization)

The affine portion of a LayerNorm, `y = γ · z + β` where `z = (x − μ)/σ` is
the standardised input, splits the end-to-end error into three
independently quantifiable terms: scale-input, scale-parameter, and bias.
This is the Lipschitz-with-error counterpart for the γ / β quantization
step in LayerNorm and the common "scale-and-bias" layers. -/

/-- Scalar affine error: `y = a·x + b` perturbed to `y' = a'·x' + b'` gives
    `|y − y'| ≤ |a|·|x − x'| + |a − a'|·|x'| + |b − b'|`. This is the
    transformer-level LayerNorm γ / β quantization bound after the
    standardisation `(x − μ)/σ` has been factored out. -/
theorem affine_layer_error_bound (a b x a' b' x' : ℝ) :
    |(a * x + b) - (a' * x' + b')| ≤
      |a| * |x - x'| + |a - a'| * |x'| + |b - b'| := by
  have hdecomp :
      (a * x + b) - (a' * x' + b') = a * (x - x') + ((a - a') * x' + (b - b')) := by
    ring
  rw [hdecomp]
  have h1 : |a * (x - x') + ((a - a') * x' + (b - b'))|
      ≤ |a * (x - x')| + |(a - a') * x' + (b - b')| := abs_add_le _ _
  have h2 : |(a - a') * x' + (b - b')| ≤ |(a - a') * x'| + |b - b'| := abs_add_le _ _
  have h3 : |a * (x - x')| = |a| * |x - x'| := abs_mul _ _
  have h4 : |(a - a') * x'| = |a - a'| * |x'| := abs_mul _ _
  linarith

/-- **LayerNorm γ / β quantization bound**: a LayerNorm output
    `γ_i · z_i + β_i` perturbed to `γ'_i · z'_i + β'_i` has per-coordinate
    error bounded by `|γ_i|·|z_i − z'_i| + |γ_i − γ'_i|·|z'_i| + |β_i − β'_i|`.
    This is just `affine_layer_error_bound` renamed for the LayerNorm
    call-site. -/
theorem layerNorm_affine_error_bound
    (γ β z γ' β' z' : ℝ) :
    |(γ * z + β) - (γ' * z' + β')| ≤
      |γ| * |z - z'| + |γ - γ'| * |z'| + |β - β'| :=
  affine_layer_error_bound γ β z γ' β' z'

/-- **Transformer-block error step** (residual + attention composition):
    combining `residual_connection_error_scalar` with
    `lipschitz_with_error_step` captures the per-block accumulation used in
    the paper. Given an ideal block `F(x) = x + G(x)` where `G` is
    Lipschitz, a perturbed `F'(x) = x + G'(x)` with `|G(x) − G'(x)| ≤ ε_G`,
    and an input error `|x − x'| ≤ δ`, the block output error satisfies
    `|F(x) − F'(x')| ≤ (1 + L_G)·δ + ε_G`. -/
theorem residual_block_error_step
    (G G' : ℝ → ℝ)
    {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hG_lip : ∀ a b, |G a - G b| ≤ Lg * |a - b|)
    {εG : ℝ} (hG_err : ∀ y, |G y - G' y| ≤ εG)
    {x x' δ : ℝ} (hx : |x - x'| ≤ δ) :
    |(x + G x) - (x' + G' x')| ≤ (1 + Lg) * δ + εG := by
  calc |(x + G x) - (x' + G' x')|
      = |(x - x') + (G x - G' x')| := by congr 1; ring
    _ ≤ |x - x'| + |G x - G' x'| := abs_add_le _ _
    _ ≤ δ + (Lg * δ + εG) :=
        add_le_add hx (lipschitz_with_error_step hLg hG_lip hG_err hx)
    _ = (1 + Lg) * δ + εG := by ring

/-! ## Log-sum-exp: 1-Lipschitz in L∞

The log-sum-exp functional `LSE(x) = log Σᵢ exp xᵢ` is 1-Lipschitz under L∞
perturbation of the inputs. This follows immediately from the exponential
squeeze bounds `expShiftSum_zipWith_le_mul_exp` / `_ge_mul_exp` already
established in `Softmax.lean`: taking `log` of a multiplicative
`exp ε` factor produces an additive `ε`. The LSE bound is the key
lemma behind the cross-entropy logit-error bound used in the paper's
end-to-end theorem. -/

/-- Scalar log-sum-exp over a list of real logits: `log Σᵢ exp xᵢ`. -/
noncomputable def logSumExp (xs : List ℝ) : ℝ :=
  Real.log (expShiftSum 0 xs)

theorem logSumExp_nil : logSumExp [] = 0 := by
  simp [logSumExp, expShiftSum_nil]

/-- Log-sum-exp is 1-Lipschitz under L∞ perturbation of the inputs:
    if `|δᵢ| ≤ ε` pointwise, then `|LSE(xs + δs) − LSE(xs)| ≤ ε`. -/
theorem logSumExp_linf_lipschitz
    (xs deltas : List ℝ)
    (hlen : xs.length = deltas.length)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ d ∈ deltas, |d| ≤ ε) :
    |logSumExp (xs.zipWith (· + ·) deltas) - logSumExp xs| ≤ ε := by
  by_cases hxs : xs = []
  · subst hxs
    have hdeltas : deltas = [] := by
      have : deltas.length = 0 := by simpa using hlen.symm
      exact List.length_eq_zero_iff.mp this
    subst hdeltas
    simp [logSumExp, expShiftSum_nil, hε]
  · have hxs_pos : 0 < expShiftSum 0 xs := by
      cases xs with
      | nil => exact absurd rfl hxs
      | cons x tl =>
        rw [expShiftSum_cons]
        have h1 : 0 < Real.exp (x - 0) := Real.exp_pos _
        have h2 : 0 ≤ expShiftSum 0 tl := expShiftSum_nonneg 0 tl
        linarith
    have hxs'_pos : 0 < expShiftSum 0 (xs.zipWith (· + ·) deltas) := by
      have hge := expShiftSum_zipWith_ge_mul_exp (m := 0) hlen hbound
      have hexp : 0 < Real.exp (-ε) := Real.exp_pos _
      have := mul_pos hexp hxs_pos
      linarith
    have hle : expShiftSum 0 (xs.zipWith (· + ·) deltas)
                ≤ Real.exp ε * expShiftSum 0 xs :=
      expShiftSum_zipWith_le_mul_exp (m := 0) hlen hbound
    have hge : Real.exp (-ε) * expShiftSum 0 xs
                ≤ expShiftSum 0 (xs.zipWith (· + ·) deltas) :=
      expShiftSum_zipWith_ge_mul_exp (m := 0) hlen hbound
    have hexpε_pos : 0 < Real.exp ε := Real.exp_pos _
    have hexp_neg_pos : 0 < Real.exp (-ε) := Real.exp_pos _
    have hmul_pos : 0 < Real.exp ε * expShiftSum 0 xs := mul_pos hexpε_pos hxs_pos
    have hmul_pos' : 0 < Real.exp (-ε) * expShiftSum 0 xs :=
      mul_pos hexp_neg_pos hxs_pos
    have hlog_le : Real.log (expShiftSum 0 (xs.zipWith (· + ·) deltas))
                    ≤ Real.log (Real.exp ε * expShiftSum 0 xs) :=
      Real.log_le_log hxs'_pos hle
    have hlog_ge : Real.log (Real.exp (-ε) * expShiftSum 0 xs)
                    ≤ Real.log (expShiftSum 0 (xs.zipWith (· + ·) deltas)) :=
      Real.log_le_log hmul_pos' hge
    have hlog_mul_pos : Real.log (Real.exp ε * expShiftSum 0 xs)
                        = ε + Real.log (expShiftSum 0 xs) := by
      rw [Real.log_mul (ne_of_gt hexpε_pos) (ne_of_gt hxs_pos)]
      rw [Real.log_exp]
    have hlog_mul_neg : Real.log (Real.exp (-ε) * expShiftSum 0 xs)
                        = -ε + Real.log (expShiftSum 0 xs) := by
      rw [Real.log_mul (ne_of_gt hexp_neg_pos) (ne_of_gt hxs_pos)]
      rw [Real.log_exp]
    rw [hlog_mul_pos] at hlog_le
    rw [hlog_mul_neg] at hlog_ge
    unfold logSumExp
    rw [abs_le]
    constructor <;> linarith

/-! ## Cross-entropy loss bound from logit error

For a one-hot target at index `k`, the cross-entropy is
`CE_k(l) = LSE(l) − l_k`. If the logits are perturbed by `ε` in L∞, the
CE differs by at most `2ε`: `ε` from the LSE term (1-Lipschitz in L∞) and
`ε` from the indexed logit itself. -/

/-- Cross-entropy loss for logits `xs` against a one-hot target with value
    `tgt` (the selected logit): `CE = LSE(xs) − tgt`. When `tgt = xs[k]`
    for a ground-truth index `k`, this is the standard one-hot CE loss. -/
noncomputable def crossEntropyFromLogits (xs : List ℝ) (tgt : ℝ) : ℝ :=
  logSumExp xs - tgt

/-- **Cross-entropy loss bound from logit error**: logits perturbed pointwise
    by `ε` in L∞ (with the same perturbation applied to the target logit)
    change the cross-entropy by at most `2ε`. Specifically, if the target
    logit differs by at most `εTgt` and each logit by at most `ε`, then
    `|CE − CE'| ≤ ε + εTgt`. -/
theorem crossEntropy_loss_bound_from_logit_error
    (xs deltas : List ℝ)
    (hlen : xs.length = deltas.length)
    {ε εTgt : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ d ∈ deltas, |d| ≤ ε)
    (tgt tgt' : ℝ) (hTgt : |tgt - tgt'| ≤ εTgt) :
    |crossEntropyFromLogits xs tgt -
      crossEntropyFromLogits (xs.zipWith (· + ·) deltas) tgt'| ≤ ε + εTgt := by
  unfold crossEntropyFromLogits
  have hLSE : |logSumExp (xs.zipWith (· + ·) deltas) - logSumExp xs| ≤ ε :=
    logSumExp_linf_lipschitz xs deltas hlen hε hbound
  have hLSE' : |logSumExp xs - logSumExp (xs.zipWith (· + ·) deltas)| ≤ ε := by
    rw [abs_sub_comm]; exact hLSE
  calc |logSumExp xs - tgt - (logSumExp (xs.zipWith (· + ·) deltas) - tgt')|
      = |(logSumExp xs - logSumExp (xs.zipWith (· + ·) deltas)) + (tgt' - tgt)| := by
          congr 1; ring
    _ ≤ |logSumExp xs - logSumExp (xs.zipWith (· + ·) deltas)| + |tgt' - tgt| :=
        abs_add_le _ _
    _ ≤ ε + εTgt := by
        have htgt_sym : |tgt' - tgt| ≤ εTgt := by rw [abs_sub_comm]; exact hTgt
        exact add_le_add hLSE' htgt_sym

/-! ## MLP quantization error bound

A 2-layer scalar MLP `MLP(x) = a₂ · σ(a₁ · x + b₁) + b₂` with Lipschitz
nonlinearity `σ` (e.g. ReLU with `Lσ = 1`, GELU/SiLU with `Lσ ≈ 1.1`) has
its end-to-end quantization error bounded by a chain of affine and Lipschitz
error terms. This is the formal counterpart of transformer FFN error
propagation. -/

/-- Scalar 2-layer MLP: `a₂ · σ(a₁ · x + b₁) + b₂`. -/
noncomputable def mlpScalar (σ : ℝ → ℝ) (a1 b1 a2 b2 x : ℝ) : ℝ :=
  a2 * σ (a1 * x + b1) + b2

/-- **MLP quantization error bound**: perturbing all parameters
    `(a₁, b₁, a₂, b₂, σ)` of a 2-layer scalar MLP gives an end-to-end error
    controlled by the three affine-layer error terms composed with the
    Lipschitz constant of `σ` plus the `σ`-quantization error. -/
theorem mlp_quantization_error_bound
    (σ σ' : ℝ → ℝ)
    {Lσ : ℝ} (hLσ : 0 ≤ Lσ)
    (hσ_lip : ∀ a b, |σ a - σ b| ≤ Lσ * |a - b|)
    {εσ : ℝ} (hσ_err : ∀ y, |σ y - σ' y| ≤ εσ)
    (a1 b1 a2 a1' b1' a2' b2 b2' x : ℝ) :
    |mlpScalar σ a1 b1 a2 b2 x - mlpScalar σ' a1' b1' a2' b2' x|
      ≤ |a2| *
          (Lσ * (|a1 - a1'| * |x| + |b1 - b1'|) + εσ)
        + |a2 - a2'| * |σ' (a1' * x + b1')|
        + |b2 - b2'| := by
  unfold mlpScalar
  -- Inner affine error: `|(a1*x+b1) − (a1'*x+b1')| ≤ |a1−a1'|·|x| + |b1−b1'|`
  have h_inner_affine :
      |(a1 * x + b1) - (a1' * x + b1')| ≤ |a1 - a1'| * |x| + |b1 - b1'| := by
    have heq : (a1 * x + b1) - (a1' * x + b1') = (a1 - a1') * x + (b1 - b1') := by ring
    rw [heq]
    calc |(a1 - a1') * x + (b1 - b1')|
        ≤ |(a1 - a1') * x| + |b1 - b1'| := abs_add_le _ _
      _ = |a1 - a1'| * |x| + |b1 - b1'| := by rw [abs_mul]
  -- `σ` Lipschitz-with-error step applied to the inner affine error:
  -- |σ(a1*x+b1) − σ'(a1'*x+b1')| ≤ Lσ · (|a1-a1'|·|x| + |b1-b1'|) + εσ
  have h_sigma : |σ (a1 * x + b1) - σ' (a1' * x + b1')|
                  ≤ Lσ * (|a1 - a1'| * |x| + |b1 - b1'|) + εσ :=
    lipschitz_with_error_step (F := σ) (F' := σ') hLσ hσ_lip hσ_err h_inner_affine
  -- Outer affine error on (a2, b2, σ(...)) vs (a2', b2', σ'(...)).
  have h_outer :=
    affine_layer_error_bound a2 b2 (σ (a1 * x + b1)) a2' b2' (σ' (a1' * x + b1'))
  calc |a2 * σ (a1 * x + b1) + b2 - (a2' * σ' (a1' * x + b1') + b2')|
      ≤ |a2| * |σ (a1 * x + b1) - σ' (a1' * x + b1')|
        + |a2 - a2'| * |σ' (a1' * x + b1')| + |b2 - b2'| := h_outer
    _ ≤ |a2| * (Lσ * (|a1 - a1'| * |x| + |b1 - b1'|) + εσ)
        + |a2 - a2'| * |σ' (a1' * x + b1')| + |b2 - b2'| := by
          have habs_nn : 0 ≤ |a2| := abs_nonneg _
          have := mul_le_mul_of_nonneg_left h_sigma habs_nn
          linarith

/-! ## Full transformer-block error theorem

A simplified transformer block is `y = x + MLP(LN(x + Attn(LN(x))))`. For
the scalar error-propagation question, the block decomposes into a chain of
Lipschitz-with-error layers, so the end-to-end error bound is a direct
application of `multi_layer_error_accumulation` with the transformer's
specific layer list. -/

/-- **Full transformer-block error theorem**: given a concrete layer list
    (Attn, LN, MLP, residuals), the transformer block's output error is
    bounded by `layerErrorBudget` of the composed layer list at the input
    error. This is just `multi_layer_error_accumulation` applied to a
    concrete `QLayer` list; the value of the statement lies in reducing
    end-to-end transformer quantization analysis to per-layer Lipschitz and
    per-layer error bounds. -/
theorem transformer_block_error_bound
    (layers : List QLayer)
    (hLnn : ∀ lyr ∈ layers, 0 ≤ lyr.L)
    (hlip : ∀ lyr ∈ layers, ∀ a b, |lyr.F a - lyr.F b| ≤ lyr.L * |a - b|)
    (herr : ∀ lyr ∈ layers, ∀ z, |lyr.F z - lyr.F' z| ≤ lyr.ε)
    (x : ℝ) :
    |applyIdealLayers layers x - applyPerturbedLayers layers x|
      ≤ layerErrorBudget layers 0 :=
  multi_layer_error_accumulation layers hLnn hlip herr x x 0 (by simp)

/-! ## Mathlib-style abstractions

Thin wrappers that expose the `QLayer` + `multi_layer_error_accumulation`
machinery under names suitable for composition with Mathlib's
`LipschitzWith` ecosystem. These are refactoring hooks rather than new
mathematical content. -/

/-- A `QLayer` whose Lipschitz constant witnesses
    `|lyr.F a − lyr.F b| ≤ lyr.L · |a − b|`. Useful for building
    compositional `QLayer` lists from Mathlib-style Lipschitz maps. -/
structure LipschitzQLayer where
  layer : QLayer
  Lnn : 0 ≤ layer.L
  F_lip : ∀ a b, |layer.F a - layer.F b| ≤ layer.L * |a - b|
  F_err : ∀ z, |layer.F z - layer.F' z| ≤ layer.ε

/-- A list of `LipschitzQLayer` values satisfies the hypotheses of
    `multi_layer_error_accumulation` uniformly. This is the Mathlib-style
    abstraction that makes the transformer error theorem a one-line
    corollary of `multi_layer_error_accumulation`. -/
theorem LipschitzQLayer.error_accumulation
    (layers : List LipschitzQLayer)
    (y y' δ : ℝ) (hy : |y - y'| ≤ δ) :
    |applyIdealLayers (layers.map (·.layer)) y -
        applyPerturbedLayers (layers.map (·.layer)) y'|
      ≤ layerErrorBudget (layers.map (·.layer)) δ := by
  apply multi_layer_error_accumulation
  · intro lyr hlyr
    rcases List.mem_map.mp hlyr with ⟨L, hL, rfl⟩
    exact L.Lnn
  · intro lyr hlyr
    rcases List.mem_map.mp hlyr with ⟨L, hL, rfl⟩
    exact L.F_lip
  · intro lyr hlyr
    rcases List.mem_map.mp hlyr with ⟨L, hL, rfl⟩
    exact L.F_err
  · exact hy

/-! ## `AffineErrorModel`: bundled affine error-propagation structure

A named wrapper around `affine_layer_error_bound`. Useful for chaining
affine-quantization steps with the rest of the `QLayer` machinery under a
Mathlib-style API (`.apply`, `.applyP`, `.bound`). -/

/-- Bundled affine perturbation model: the ideal map `x ↦ a·x + b` alongside
    the perturbed map `x ↦ a'·x + b'`. Packages the per-parameter
    quantization errors into a single structure. -/
structure AffineErrorModel where
  /-- Ideal slope. -/
  a : ℝ
  /-- Ideal intercept. -/
  b : ℝ
  /-- Perturbed slope. -/
  a' : ℝ
  /-- Perturbed intercept. -/
  b' : ℝ

/-- Ideal application of the affine model. -/
@[inline] def AffineErrorModel.apply (m : AffineErrorModel) (x : ℝ) : ℝ :=
  m.a * x + m.b

/-- Perturbed application of the affine model. -/
@[inline] def AffineErrorModel.applyP (m : AffineErrorModel) (x : ℝ) : ℝ :=
  m.a' * x + m.b'

/-- **`AffineErrorModel.bound`**: standard error bound
    `|apply x − applyP x'| ≤ |a|·|x−x'| + |a−a'|·|x'| + |b−b'|`. This is
    the bundled counterpart of `affine_layer_error_bound`. -/
theorem AffineErrorModel.bound (m : AffineErrorModel) (x x' : ℝ) :
    |m.apply x - m.applyP x'| ≤
      |m.a| * |x - x'| + |m.a - m.a'| * |x'| + |m.b - m.b'| :=
  affine_layer_error_bound m.a m.b x m.a' m.b' x'

/-- Packaging an `AffineErrorModel` as a `QLayer` with Lipschitz constant
    `|a|` and evaluation error `|a − a'|·|x₀| + |b − b'|` at a reference
    point `x₀`. The evaluation-error field encodes the affine-parameter
    perturbation at a particular input. -/
@[inline] def AffineErrorModel.toQLayer (m : AffineErrorModel) (x₀ : ℝ) :
    QLayer :=
  (m.apply, m.applyP, |m.a|, |m.a - m.a'| * |x₀| + |m.b - m.b'|)

/-! ## Multi-block transformer end-to-end error bound

A full transformer is a `List (List QLayer)` — a list of blocks, each a list
of layers. Concatenating (flattening) the blocks lets us reuse
`multi_layer_error_accumulation` directly, giving a per-layer
Lipschitz-with-error decomposition of the end-to-end error. -/

/-- Apply the ideal layers of a list of blocks left-to-right. -/
def applyBlocks (blocks : List (List QLayer)) (x : ℝ) : ℝ :=
  blocks.foldl (fun y block => applyIdealLayers block y) x

/-- Apply the perturbed layers of a list of blocks left-to-right. -/
def applyBlocksP (blocks : List (List QLayer)) (x : ℝ) : ℝ :=
  blocks.foldl (fun y block => applyPerturbedLayers block y) x

theorem applyIdealLayers_append (ls ms : List QLayer) (x : ℝ) :
    applyIdealLayers (ls ++ ms) x =
      applyIdealLayers ms (applyIdealLayers ls x) := by
  simp [applyIdealLayers, List.foldl_append]

theorem applyPerturbedLayers_append (ls ms : List QLayer) (x : ℝ) :
    applyPerturbedLayers (ls ++ ms) x =
      applyPerturbedLayers ms (applyPerturbedLayers ls x) := by
  simp [applyPerturbedLayers, List.foldl_append]

theorem layerErrorBudget_append (ls ms : List QLayer) (δ : ℝ) :
    layerErrorBudget (ls ++ ms) δ =
      layerErrorBudget ms (layerErrorBudget ls δ) := by
  simp [layerErrorBudget, List.foldl_append]

theorem applyBlocks_eq_flatten (blocks : List (List QLayer)) (x : ℝ) :
    applyBlocks blocks x = applyIdealLayers blocks.flatten x := by
  induction blocks generalizing x with
  | nil => simp [applyBlocks, applyIdealLayers]
  | cons b bs ih =>
    simp only [applyBlocks, List.foldl_cons, List.flatten_cons,
               applyIdealLayers_append]
    exact ih (applyIdealLayers b x)

theorem applyBlocksP_eq_flatten (blocks : List (List QLayer)) (x : ℝ) :
    applyBlocksP blocks x = applyPerturbedLayers blocks.flatten x := by
  induction blocks generalizing x with
  | nil => simp [applyBlocksP, applyPerturbedLayers]
  | cons b bs ih =>
    simp only [applyBlocksP, List.foldl_cons, List.flatten_cons,
               applyPerturbedLayers_append]
    exact ih (applyPerturbedLayers b x)

/-- **Transformer end-to-end error bound**: a list of blocks (each itself
    a list of layers) composes into an end-to-end error bounded by
    `layerErrorBudget` over the flattened layer list. This is the paper's
    multi-block transformer error theorem, stated as a clean corollary of
    `multi_layer_error_accumulation`. -/
theorem transformer_end_to_end_error_bound
    (blocks : List (List QLayer))
    (hLnn : ∀ lyr ∈ blocks.flatten, 0 ≤ lyr.L)
    (hlip : ∀ lyr ∈ blocks.flatten, ∀ a b,
              |lyr.F a - lyr.F b| ≤ lyr.L * |a - b|)
    (herr : ∀ lyr ∈ blocks.flatten, ∀ z, |lyr.F z - lyr.F' z| ≤ lyr.ε)
    (x : ℝ) :
    |applyBlocks blocks x - applyBlocksP blocks x|
      ≤ layerErrorBudget blocks.flatten 0 := by
  rw [applyBlocks_eq_flatten, applyBlocksP_eq_flatten]
  exact multi_layer_error_accumulation blocks.flatten hLnn hlip herr
    x x 0 (by simp)

end Flean
