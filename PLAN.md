# Flean Plan

## Paper Roadmap

- `CPP`: position Flean as a verified numerical-kernel framework.
  It is reasonable for the first paper to focus on `Flean` itself.
  Focus on reusable floating-point proof infrastructure plus one strong end-to-end case study.
  Core technical story: `IEEE 754` reconstruction / porting in Lean, plus reusable proof abstractions.
  Current backbone: `TwoSum -> Expansion -> AdaptiveExpansion -> Kahan/Neumaier -> chunked reduction`.
  Primary case study: stable `log-sum-exp` skeleton with chunked reduction safety,
  with `softmax` as the next extension.
  Working paper title:
  `Flean: A Lean Framework for Verified Numerics, from Rounding Theory to Stable Reductions`

- `CAV`: lift the CPP kernel story to a verified numerical pipeline / system story.
  Focus on compositional safety of mixed-precision reduction trees, blockwise kernels,
  and refinement from abstract numerical proofs to executable kernel models.
  Working paper title:
  `Verified Mixed-Precision Reduction Pipelines: Refinement from Numerical Proofs to Executable Kernels`

- `MLSys`: connect the verified kernels to ML compiler workflows and practical workloads.
  Focus on compiler-integrated verified reduction kernels, performance, robustness,
  and empirical impact in training / inference pipelines.
  Likely venue angle: ML compiler / TVM stack.
  Working paper title:
  `Compiler-Integrated Verified Reductions for Reliable ML Workloads`

## Current CPP Position

- Do not position the first paper as a full verified ML system.
- Position it as `Flean`: verified compensated reductions with automated mixed-precision reasoning.
- Two core contributions:
  (a) Lean 4 proof automation for floating-point chains (tactics as the key differentiator),
  (b) verified compensated summation with tight error identities plus an ML case study.
- Use Kahan / Neumaier as infrastructure, not as the whole paper.
- Treat stable `log-sum-exp` as the flagship CPP case study, not just an optional application.
- Treat full `softmax` verification as the natural next layer on top of that case study.
- The paper will feel too shallow only if the `IEEE 754` story looks like mechanical translation
  or the case study looks toy-sized.
- To avoid that, emphasize proof automation, Lean 4 metaprogramming advantages,
  and one nontrivial end-to-end case study.
- Working paper title:
  `Flean: Verified Compensated Reductions with Automated Mixed-Precision Reasoning in Lean 4`

## CPP Gap Analysis

### G1. Conditional exactness without satisfiability bridge

All core theorems (`kahanSum_exact`, `chunkedKahanSum_exact`, `stableLogSumExpBlocks_exact`)
require strong preconditions (`KahanInput`, `KahanChain`, `ChunkedKahanInput`).
The paper does not show these conditions hold for practical inputs.
Reviewers will ask whether the "exactness" story is tautological.

### G2. No approximate error bounds for the general case

Everything is exact-or-nothing. No `O(n * eps)` fallback bound exists for when
the exactness preconditions fail. Standard references (Higham) give approximate bounds.
Without this, practical usefulness is questionable.

### G3. Tactics contribution underrepresented

`flean_chain_bound`, `MixedPrecision`, `ChainDecomp` are the strongest differentiators
vs Flocq / VCFloat, but the plan barely mentions them.
These should be a core section of the paper.

### G4. Log-sum-exp case study too thin

`StableLogSumExp.lean` is ~188 lines of skeleton properties.
Missing: overflow avoidance theorem, comparison with naive implementation,
softmax wrapper, sum-to-one property.

### G5. Related work positioning absent

No clear answer to "why is this not a Flocq port?"
Need explicit differentiation vs Flocq, VCFloat2, Harrison (HOL Light).

### G6. Paper title too broad

"from Rounding Theory to Stable Reductions" covers more than 12 CPP pages can hold.

## Near-Term Priorities

### P0: Paper can stand

1. **Condition satisfiability bridge (fixes G1).**
   - Neumaier: prove `NeumaierInput` holds for any list of IEEE 754 floats
     via `Bridge.toReal_isRepresentable`. This turns conditional exactness into
     "exact for all IEEE float inputs".
   - Kahan: characterize when `KahanInput` holds, e.g. nonneg sorted inputs,
     or bounded partial sums.
   - ChunkedKahan: give sufficient conditions on block size.

2. **Refocus thesis and rewrite plan (fixes G6).**
   Narrow the paper to two contributions:
   (a) Lean 4 proof automation for mixed-precision chains,
   (b) verified compensated summation + ML case study.

### P1: Paper is competitive

3. **Approximate error bound (fixes G2).**
   Add a general bound that only requires representable inputs, no magnitude conditions:
   `|xs.sum - (kahanSum fmt xs).1| ≤ C * eps * sum_of_abs`
   where `C` depends on list length and format.
   This complements the exact results with a practical fallback.

4. **Tactics showcase section (fixes G3).**
   - Dedicated paper section on `flean_chain_bound` and `MixedPrecision`.
   - Side-by-side: manual ~15 line proof vs 1 line tactic call.
   - `DotProd.lean` as the primary tactic demonstration.
   - Describe the Lean 4 `Syntax` / `Elab` metaprogramming that enables this.

### P2: Paper is strong

5. **Softmax wrapper (fixes G4).**
   - Define `softmax` on top of `stableLogSumExpBlocks`.
   - Prove exact softmax outputs sum to 1.
   - Bound deviation under rounding.

6. **Related work positioning (fixes G5).**

   | comparison      | Flean's differentiator                                             |
   |-----------------|--------------------------------------------------------------------|
   | vs Flocq (Coq)  | Lean 4 type class polymorphism for format-generic proofs; tactic automation |
   | vs VCFloat2      | VCFloat is bottom-up (C to float props); Flean is top-down (abstract to kernel) |
   | vs Harrison (HOL)| Lean 4 ecosystem, Mathlib integration, stronger automation         |

   Core argument: Flean leverages Lean 4 type classes + metaprogramming to provide
   a proof automation layer that Flocq/VCFloat do not have.

### P3: Nice to have

7. **Overflow avoidance proof for log-sum-exp.**
   Prove `exp(x - m) ≤ 1 ≤ fmt.maxFinite` so the shifted exponentials
   are guaranteed representable and within range.

8. **Strengthen bridge to implementation-facing kernels.**
   This is the key step for turning the CPP case study into a later CAV refinement story.
