既然專案命名為 **Flean**，且目標是追隨 Flocq 的腳步實現 IEEE 754 的完整形式化，這份規劃將著重於從抽象數學層次到底層位元實作的架構設計。

---

## ## 核心架構規劃 (Flean Roadmap)

### 一、 抽象數學層 (Flean.Core)
這是整個庫的基石，不涉及具體的位元表示，純粹處理實數與浮點格式的邏輯關係。
* **格式定義 (Generic Formats)**：定義參數化的浮點系統，包含基數 $\beta$（通常為 2）、尾數精度 $p$、以及指數範圍 $[e_{min}, e_{max}]$。
* **實數映射**：建立實數 $\mathbb{R}$ 與浮點集合 $\mathbb{F}$ 的關聯函數。
* **捨入公理化 (Rounding Theory)**：
    * 定義五種 IEEE 754 捨入模式的抽象函數。
    * 證明捨入函數的性質：單調性、等冪性 ($R(R(x)) = R(x)$)、以及對稱性 ($R(-x) = -R(x)$)。

---

### 二、 二進制與位元層 (Flean.Binary)
將抽象格式具體化為電腦中的位元串，這部分需緊密結合 Lean 4 的 `BitVec`。
* **位元拆解 (Bit-level Layout)**：
    * 實作 `sign` (1-bit), `exponent` (w_e bit), `significand` (w_m bit) 的封裝與解構。
    * 支援標準精度：`Binary16` (Half), `Binary32` (Single), `Binary64` (Double), `Binary128` (Quad)。
* **特殊值定義**：
    * 嚴格定義 `NaN` (Quiet/Signaling), `+/- Infinity`, `+/- Zero`。
    * 處理 **Subnormal numbers** (次常態數) 的特殊階碼邏輯。

---

### 三、 算術運算與誤差證明 (Flean.Arith)
證明基本的算術運算符合 IEEE 754 標準規範。
* **基本運算形式化**：定義加、減、乘、除、開方等運算在捨入後的行為。
* **誤差界限證明**：
    * 證明相對誤差公式：$R(x) = x(1 + \epsilon)$，其中 $|\epsilon| < 2^{-p}$。
    * 證明 ULP (Unit in the Last Place) 的相關引理。
* **例外狀態 (Exceptions)**：形式化 Invalid Operation, Division by Zero, Overflow, Underflow, Inexact 等標誌位。

---

### 四、 自動化與工具鏈 (Flean.Tactics)
為了讓 Flean 易於使用，需要開發專屬的證明策略。
* **浮點判定程序 (Float Decide)**：利用 Lean 4 的 `native_decide` 或連線 SMT Solver (如 Z3)，自動證明具體的浮點不等式。
* **常數轉化**：提供將十進制字串（如 "0.1"）精確轉化為 `Flean.Binary` 結構的計算宏。

---

### 五、 應用與驗證 (Flean.Apps)
驗證 Flean 在真實場景中的價值。
* **硬體一致性驗證**：撰寫測試集，比對 Lean 的形式化輸出與真實 CPU/GPU 的運算結果。
* **算子驗證**：驗證簡單的數值算法（如 Kahan Summation 或 Softmax）的累積誤差界限。

---

## ### 關鍵技術挑戰
* **Dependent Types 的複雜性**：浮點格式的參數（如位元長度）會進入型別系統，需小心處理型別依賴導致的證明難度。
* **NaN 的非自反性**：在 Lean 的 `Eq` 框架下處理 `x != x` (NaN) 的邏輯，需要一套優雅的封裝策略。
* **效能平衡**：確保形式化定義既能用於嚴謹證明，又能透過 `#eval` 進行快速的數值測試。

---
