# GB-R63：把 186 的條件性素數間距證明接到完整 Goldbach 窗口

日期：2026-10-26。本輪針對使用者提出的 186 結果，讀取其實際 Lean 原始碼，而非只用末端的 liminf 聲明。Astra 已獨立確認固定 profiles、定量裕量、逐點權重、端點及相鄰性等步驟。下述是保留該專案三項輸入的紙面推論；不是本地獨立重建完整 186 證明，也不是對指定 gap=4 的證明。不宣稱文獻首創。

## 結論及其前提

在 `openai/PrimeGaps186` 明列的三項輸入成立時，存在某個固定偶數

\[
d\in\{2,4,\ldots,186\},
\]

使任意大的相鄰奇素數 p、p+d 的完整倍增窗口

\[
[2p,2(p+d)]
\]

中，每個偶數都有兩個素數之和的表示。

此處 d 尚未識別；尤其不能指定 d=4，也不能排除本推導選出的 d=2。GB-R62 的固定 d≥6 及最小 δ 無界結論仍然成立，但其 CRT 構造使用另一個間距範圍，不能把那些性質直接套到本輪的 d≤186 上。

原專案三項額外輸入為：

| 名稱 | 內容與本輪處理 |
| --- | --- |
| `PrimeGap186.kloosterman3_bound` | 規範化 rank-three hyper-Kloosterman 上界；沿用來源的精確陳述。 |
| `PrimeGap186.kloosterman2_correlation_bound` | rank-two Kloosterman 關聯和上界；沿用來源的精確陳述。 |
| `PrimeGap186.physical_integral_bounds` | 來源數值積分及 cap 上界；本輪沒有重新執行數值證書或將其形式化。 |

來源 [README](https://github.com/openai/PrimeGaps186/blob/61340d0b74163003b32756bb16e91d9209a5e330/README.md) 明列三者仍為其 Lean 專案未證輸入。前兩項附有原始文獻出處，但本輪並未重新核對全部有限域論證。它們沒有被匯入本專案成為公理。

## 固定來源與實際讀取範圍

公開來源 commit：`61340d0b74163003b32756bb16e91d9209a5e330`。下載的是該 commit 的檔案，後續 main 改動不影響本紀錄。

- [實際證明 `PrimeGaps186.lean`](https://github.com/openai/PrimeGaps186/blob/61340d0b74163003b32756bb16e91d9209a5e330/PrimeGaps186.lean)：10,312,565 bytes，SHA256 `fd7d9296871d276f7cd950ebf88d38627ff326abdf214a1facabc52fb6794d27`。
- README SHA256：`be1e3ec09817391ee634f23c624b498fc0e5563f1c30ad1fbfadf57ae4bacb3b`。
- `Challenge.lean` SHA256：`b99a403b1946547ef1926cd43ebce717640f7f76fa7e1f8f5a4b19ac2e53e1f0`。該檔為目標規格，三個刻意保留的目標佔位不是實際證明檔中的未完成證明。
- `formalization.yaml` SHA256：`8977ce060c1214afb4b71cb28a4c52d9d3db86d4d61183d0ece6ce57edf50752`。

本輪針對以下聲明及其相關證明段落作來源檢查，沒有聲稱逐行審查全部約 21 萬行：

| 聲明 | 固定版本起始行 | 在本推導中的用途 |
| --- | ---: | --- |
| `presievingModulus` | 2019 | W(x) 的定義。 |
| `fragmentNormalization` | 2039 | B(x)=(φ(W)/W)log R。 |
| `presieving_le_mul_log_eventually` | 181190 | 對每個 c>0，充分大 x 時 W(x)≤c log x。 |
| `selberg40_canonical_erased_coefficient_bound` | 185335 | Selberg 係數的 totient-ratio 上界。 |
| `canonical40_fixed_profile_coefficient_roots` | 200754 | 對每個固定 u>0 成立的逐點權重根界。 |
| `literal_minorant_eventually_positive_first_moment` | 201927 | 證明正文給出正裕量乘 Z(x) 的定量下界。 |
| `trial_source_supported_smooth_profiles_positive` | 205800 | 數值輸入供給固定的平滑 profiles 及嚴格裕量。 |
| `canonical40_source_profile_signed_margin` | 207078 | 將 profile 裕量轉為所用加權裕量。 |
| `canonical40_fixed_source_positive_first_moment` | 209933 | 組裝上述 moments、同一個 A、Z 與預篩起點集。 |
| `exists_smooth_selberg_profiles_with_positive_first_moment` | 210412 | 三項輸入到固定 profiles 的最後組裝。 |
| `infinite_two_prime_translates_admissibleTuple` | 210621 | 來源匯出的無窮性結論；單獨此聲明不足以完成例外刪除。 |

這些精確行號僅適用於上述固定 commit。來源使用 Lean 4.34.0-rc2，本專案使用 rc1；本輪沒有為外部專案另裝工具鏈、下載其完整快取或聲稱外部專案本地編譯通過。

## 來源提供的兩個定量資訊

固定該專案的四十位置集合 H 及其一次選定的平滑 profile F。令

\[
\rho=2624989/10000000,\quad
R(x)=x^\rho,\quad
B(x)=\frac{\varphi(W(x))}{W(x)}\log R(x),\quad
Z(x)=\frac{x}{W(x)B(x)^{40}}.
\]

S_x 是 [⌈x⌉,⌊2x⌋] 中所選預篩餘類的起點集。令 P_H(n) 為 n+H 中的素數個數，A(x,n) 為來源使用的 Selberg 係數和。

**第一個資訊：總量下界。** `literal_minorant_eventually_positive_first_moment` 的結論雖只匯出正值，其證明先固定一個與 x 無關的裕量 M>0，再取 ε=M/2000，實際證明了

\[
\sum_{n\in S_x}(P_H(n)-1)A(x,n)^2
\ge \frac M2 Z(x)
\tag{63.1}
\]

（正文的 `hsmall`、`hmain`、`hfinite` 連接給出此界）。後續 fixed-source 組裝使用同一套固定 profiles 與 moments。只讀取最後的無窮性定理會丟掉這項定量資訊。

取來源的預篩上界 c=1，充分大 x 時 W(x)≤log x；再由 φ(W)≤W 得 0<B(x)≤ρ log x。因此

\[
Z(x)\ge\frac{x}{\rho^{40}(\log x)^{41}}.
\tag{63.2}
\]

**第二個資訊：單點權重界。** `canonical40_fixed_profile_coefficient_roots` 對每個固定 u>0 給出 C_u>0，使充分大 x 後，整個 [⌈x⌉,⌊2x⌋] 中

\[
|A(x,n)|\le C_u x^u.
\tag{63.3}
\]

它要求 F 的值域有界，固定的光滑緊支撐 profile 滿足此條件。這一上界不只適用於素數命中的起點；因此可以用來控制所有被 Goldbach 例外污染的起點。

## 加權刪除所有失敗窗口

沿用 GB-R62 核對的 Montgomery–Vaughan 無條件例外集定理，取 η>0，使 E(Y)≪Y^(1−η)。如有需要縮小 η，可取 0<η<1。

在全部 n∈[⌈x⌉,⌊2x⌋] 中，只要有某個 j∈{0,…,186} 的 2n+2j 失敗，就稱 n 為壞起點。固定 j 時 n↦2n+2j 單射，目標至多 4x+372，故壞起點數至多

\[
187E(4x+372)\ll x^{1-\eta}.
\tag{63.4}
\]

在 (63.3) 取 u=η/4。單點非負權重 w_x(n)=A(x,n)^2 至多 C_u² x^(η/2)。又 P_H(n)≤40，故刪去壞起點時，損失的加權正貢獻至多

\[
40 C_u^2 x^{\eta/2}\,187E(4x+372)
\ll x^{1-\eta/2}
=o\!\left(\frac{x}{(\log x)^{41}}\right).
\tag{63.5}
\]

這嚴格小於 (63.1)、(63.2) 的供給。於是充分大 x 時，刪除全部壞起點後的加權和仍為正，必有某個保留下來的 n 滿足 P_H(n)≥2。這個**同一個 n** 同時滿足：n+H 中至少兩個素數，且全部 j=0,…,186 的 2n+2j 都有 Goldbach 表示。

亦可從 (63.1)–(63.3) 推得：對每個固定 ε∈(0,1)，至少有 ≫_ε x^(1−ε) 個 n 命中兩個 tuple 素數（取 u=ε/4，再吸收 log^41）。此數量界是閱讀來源證明後的紙面抽取，並非來源已匯出的同名 Lean 定理。

## 相鄰性與同一固定間距

從 n+H 中選兩個不同素數 p<r。令 q 為 p 在全體素數序列中的下一個素數，則 p<q≤r≤n+186，所以 p、q 真正相鄰，q−p≤186。不能只把排序後相鄰的 tuple 命中當作全體相鄰；兩個 tuple 位置之間可能另有素數。

所有偶數 N∈[2p,2q] 都可寫成 2n+2j，其中 0≤j≤186，故完整窗口成功。由 n 隨 x 無界，p≥n 亦無界。充分大時 p、q 皆為奇數，q−p 是 {2,4,…,186} 中的一員；有限鴿巢原理固定其中一個 d，完成開頭的結論。

## 常數 186 的有限檢查

已從固定原始碼的 `admissibleTuple` 定義讀取四十個整數，獨立確認無重複、最小值 0、最大值 186。對所有不超過 40 的素數，一個未佔用的剩餘類分別為：

| 素數 | 2 | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 | 37 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 未佔用類 | 1 | 1 | 4 | 3 | 7 | 5 | 11 | 8 | 16 | 9 | 4 | 3 |

對 p>40，四十個位置不可能佔滿 p 個剩餘類。因此該集合可容許，直徑確為 186。這項有限檢查不核驗任何分布定理或數值積分前提。

## 審查與形式化範圍

Astra 已獨立確認上述紙面推論，特別核對 profiles 先固定再令 x 增大、Z 中已包含預篩餘類的密度因子，以及從真正的下一個素數取得相鄰性。

Luna 完成 `WeightedExceptionDetection.lean` 的 `exists_weighted_prime_detection`。它對任意有限起點集 S、例外集 E、位置集 H 及非負權重 w 證明：若逐點 w≤M，E 包含所有失敗目標，且加權裕量大於 |H| M (L+1)|E|，則存在**同一個**起點，既命中至少兩個 H 位置的素數，又使全部 j≤L 的目標成功。它直接使用 GB-R62 的有限例外計數定理。

主代理已整合並獨立執行完整 `verify_project.py`，建置與既有有限檢查全部通過。`Checks.lean` 現核對 38 個定理，公理依賴僅為標準三公理的子集；專案 Lean 檔無新增公理、`sorry`、`admit` 或 `native_decide`。收據見根目錄 `verification.json`。

有限加權偵測定理沒有供給外部的漸近前提。三項外部輸入、整個 186 分布證明、Montgomery–Vaughan 例外界、漸近比較與本輪完整無窮性推論，均未新增為本專案公理，也沒有宣稱已由本地 Lean 完整核驗。
