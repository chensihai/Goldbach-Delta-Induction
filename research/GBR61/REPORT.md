# GB-R61：原稿與 Lean 來源定位，明列條件性基礎

日期：2026-10-26。本輪依使用者提供的原 DOCX，核對早期 δ 主張的範圍，並尋找使用者記得的 Lean 驗證。原稿、舊 Lean 來源及舊研究目錄均未改動。

## 1. 已實際讀取的原稿

來源為本地 `D:\work_dir\Prime\A_Structural_Sub_Conjecture_on_Cousin_Prime_Pairs_Simon_Chen.docx`，作者 Simon Chen，日期 2025-07-09。檔案大小 39,305 bytes，SHA-256：

`79251e15f2ebc7dc5c251cb3c3a63b5061bde07837a7afb8c897d895ddfc97fe`

本輪讀取 DOCX 的全部正文段落及表格文字。檔案沒有嵌入圖片或原生 OMML 公式；數學表示保留於文字中。本輪是內容審查，沒有完成頁面渲染或排版審查，不提供未核實的頁碼。原稿本身不複製進公開儲存庫。

原問題確實是：給定 p、p+4 為素數，尋找奇數 δ≡0 (mod 3)，使 p+1±δ 均為素數，從而表示 2p+2。這不是中央項 p+(p+4)=2p+4。

第 3 節聲稱在 generalized EHθ、θ>1/2 下，所有充分大的表哥中心都有上述 δ；正文給出一段標為 Outline 的主項與餘項描述，第 5.2 節再作同一聲明。該稿沒有在正文中定義所需的 β 權重、精確篩選序列、X 與中心 p 的關係，或建立逐中心一致的素數對正下界。因此本輪不能把這段綱要認證為已完成的條件證明；這也不是對「EH 是否可能推出該結論」給出否定定理。

## 2. 找到的 Lean 驗證究竟證明甚麼

### `../data/DeltaMod3.lean`

其核心定理 `delta_mod_three` 的型別是

```lean
(h₁ : (2 + δ) % 3 ≠ 0) →
(h₂ : (2 - δ) % 3 ≠ 0) → 3 ∣ δ
```

δ 為整數。抽出原始檔案中 debug 段之前的完整前綴，使用本專案 Lean 4.34.0-rc1 獨立編譯成功；`#print axioms delta_mod_three` 恰列出 `propext, Classical.choice, Quot.sound`。抽取未改寫主要證明，也沒有修改原始檔。

原檔 SHA-256 為 `81329a99322ea9dd5f7887e34b0f155b0d8693dd122b8c7178b6f8ed0230875a`。原整檔的 debug 引理仍留有未解目標，R58 已重現這個整檔建置失敗；主要必要條件可通過與整檔 debug 未完成是兩項不同事實。

### `../Delta/Delta.lean`

可讀來源包括對稱和式恆等式、在已假設 3∣δ 下的兩項同餘，以及 5、11 為素數的具體例子。`../Delta.lean` 和 `../Main.lean` 是入口／示例程式，沒有新增 δ 存在性定理。

這些檔案中沒有找到如下全稱存在性型別：

\[
\forall p>3,\quad p,p+4\in\mathbb P
\Longrightarrow\exists\delta,\quad p+1\pm\delta\in\mathbb P.
\]

這是對已定位檔案的結論，並不排除另有尚未取得的 Lean 檔。對 `D:\work_dir\Prime` 的可見 `.lean` 檔名檢索，以及其中六個 ZIP 的成員名稱檢索，亦未找到額外 Lean 來源。

## 3. 可以採用的條件性基礎

為研究歸納，可以明列原稿的左側假設 L₂：每個 p>3 的表哥素數對，都有上述 δ。若只研究普通 Goldbach，還要保留含質數 3 的表示；不能把必要同餘條件無條件套到這個例外。

也可以為測試繼承而暫採更強的完整窗口假設 B₂：

\[
B_2:\quad\forall s,t,\quad
\operatorname{AdjacentPrimes}(s,t)\land t=s+4
\Longrightarrow\forall 0\le j\le4,\quad G(2s+2j).
\]

B₂ 包括左右兩個非中央目標；原稿只研究其中左側，故不把 B₂ 說成原稿已證結論。本輪未將 L₂ 或 B₂ 寫成 Lean 公理，也未聲稱使用者已採納更強假設。這些都是可供後續條件性推理明列的輸入。

## 4. 從基礎到更大間隙，直接重用的支持範圍

本輪證明一項真正涉及相鄰素數的範圍事實。若 p<q 為相鄰素數、p<c<q，而另一對素數 s≤c≤t 包住同一中心，則

\[
s\le p<q\le t,\qquad q-p\le t-s.
\]

理由是 s、t 都不能落在 (p,q) 內。因此當 q−p>4 時，c 不可能同時落在任何素數端點的 gap=4 窗口 [s,s+4] 中。

這表示：B₂ 的已覆蓋和值，不能僅靠換一對表哥端點，就直接重用為較大間隙中的同一個目標 2c。若要從 B₂ 推進 k=3、4，需要改變表示並證明新加數仍是素數，或引入其他有實質算術內容的轉移。

這**沒有證明實際素數上的 B₂ 蘊含不了更大 k**，也沒有否定使用較小和值作來源的歸納。排除的只有同一和值直接落入較短素數窗口的做法。

兩項結果已在 `GoldbachDeltaInduction/WindowSeparation.lean` 形式化：

- `prime_window_containing_center_not_shorter`
- `gap_four_window_excludes_larger_gap_center`

一般 Goldbach 與 k=2 的存在性仍未證明；下一步可以在明列假設的條件下研究轉移，而不把必要同餘引理當作存在性證明。
