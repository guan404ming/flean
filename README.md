# Flean

A Lean 4 formalization of IEEE 754 floating-point arithmetic with mixed-precision analysis, built on Mathlib.

420+ theorems, zero `sorry`.

## Getting Started

```
lake build
```

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

## Structure

```
Flean/
├── Core/           Real-valued rounding models, error bounds, double rounding,
│                   cast chain composition, relative error, ULP, Sterbenz
├── Binary/         Bit-level IEEE 754 (BitVec packing, classification, special values)
├── Arith/          Arithmetic operations (add, mul, div, sqrt, FMA, comparisons)
├── Apps/
│   ├── EFT/        Error-free transforms and expansion-based summation
│   ├── Compensated/ Kahan, chunked Kahan, and Neumaier summation
│   ├── ML/         ML-facing kernels such as dot product and stable log-sum-exp
│   └── Common/     Shared application-level helpers
├── Bridge.lean     Refinement connecting bit-level and real-valued models
└── Tactics/        Automation (flean_cast_safe, flean_chain_bound,
                    flean_numeric_bound, flean_quant_bound)
```

## Tactics

```lean
-- Cast chain exactness (widen-narrow, idempotence, absorption)
example {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary16 (roundNNE binary32 x) = x := by
  flean_cast_auto

-- Error bounds for arbitrary-length chains
example (fmts : List FloatFormat) (x : ℝ) :
    |x - roundChain fmts x| ≤ chainBpowSum fmts x := by
  flean_chain_bound

-- Concrete numeric bounds via machineEpsilon rewriting
example (x : ℝ) (hx : (2 : ℝ) ^ ((-14 : ℤ) + 11 - 1) ≤ |x|) :
    |x - roundNNE binary16 x| ≤ 1 / 2048 * |x| := by
  flean_numeric_bound
```

## Case Studies

| Layer | File | Key results |
|-------|------|-------------|
| EFT | `EFT/TwoSum` | `fast2Sum_exact` |
| Compensated | `Compensated/Kahan` | `kahanSum_exact`, `kahanSum_tight_bound` |
| Compensated | `Compensated/ChunkedKahan` | `chunkedKahanSum_exact` |
| Compensated | `Compensated/Neumaier` | `neumaierSum_exact_of_finiteFloatBits` |
| ML | `ML/DotProd` | `dotprod_error`, `mpMul_error` |
| ML | `ML/DotProdBits` | `mpDotProdBits_toReal_eq_mpDotProd` |
| ML | `ML/StableLogSumExp` | `stableLogSumExpBlocks_main` |
| ML | `ML/Softmax` | `softmaxBlocks_sum_one`, `roundedSoftmaxBlocks_sum_error_bound` |

## License

Apache-2.0
