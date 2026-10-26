# GB-R60：Maynard 聚簇與 CRT 排除任意固定線性半徑

日期：2026-10-26。這是本專案從已發表定理推導的紙面結果，不宣稱文獻首創。Astra 獨立檢查了構造與量詞；Lean 核驗範圍另列，沒有把 Maynard 定理寫成專案公理。

## 結論

存在絕對常數 L，使對每個整數 R≥0 和每個 X，都能找到相鄰奇素數

\[
X<p<q,\qquad 6\le q-p\le L,
\]

使得

\[
\boxed{\forall\,0\le\delta\le R,\quad
\neg\bigl((p+1-\delta)\in\mathbb P\ \land\ (p+1+\delta)\in\mathbb P\bigr).}
\tag{60.1}
\]

可以同時要求 p>R+3，故上式涉及的整數均為正數，沒有自然數減法截斷問題。

因此，本專案的全稱命題 `GapRadiusBound C` 對**每個固定自然數 C** 都不成立。這把 GB-R56 的有限 C≤128 結果推廣到全部固定 C；此處的完整證明使用外部已知的無條件素數聚簇定理。

(60.1) 沒有保證更遠處存在表示，所以不能無條件把它說成「有限的最小 δ 比值無界」。若另假設相應 Goldbach 表示存在，才可對有限最小偏移作這個解讀。它也沒有判定固定 gap=4 的原始 δ 猜想。

## 唯一外部素數存在性輸入

使用 Maynard，[Dense clusters of primes in subsets](https://doi.org/10.1112/S0010437X16007296)，Compositio Math. 152 (2016)，Theorem 3.4（第 1520 頁；[出版者 PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B49458BB98CB2D9C93ACF3BB09B4B08D/S0010437X16007296a.pdf/div-class-title-dense-clusters-of-primes-in-subsets-div.pdf)）。固定 m=2、ε=1/12，並取 y=x，可得以下所需特例：存在固定 K，使每個由 K 個不同、正斜率線性式組成的可容許族，都在任意大的參數值同時包含至少兩個素數。

量詞順序很重要：K 先固定。其後選定的係數 W 與常數項雖可很大，但始終固定；當 x 足夠大時，它們滿足該定理的係數範圍。參數開始生效的尺度可以依賴這些係數，**不要求對所有 R 統一的起始尺度**。

一般線性式版本也明列於 Banks–Freiberg–Turnage-Butterbaugh，[Consecutive primes in tuples](https://doi.org/10.4064/aa167-3-4)，Acta Arith. 167 (2015)，第 261 頁的 Maynard–Tao 定理。下面的 CRT 隔離步與其第 263–264 頁的構造相近，但增加了兩側緩衝區及對稱和值的同餘障礙。

## 完整推導

**1. 固定可容許的位置族。** 取上述 K（必有 K≥2），令

\[
B=6K!,\qquad H=\{0,B,\ldots,(K-1)B\},\qquad L=(K-1)B.
\]

這些量完全不依賴 R。對每個素數 ℓ≤K，H 模 ℓ 只佔 0 類；對 ℓ>K，K 個位置不足以佔滿全部類。因此平移族 {n+h:h∈H} 可容許。

**2. 用 CRT 排除緩衝區內的其他所有位置。** 現在才固定 R。令

\[
I_R=[-R-2,L+R+2]\cap\mathbb Z,\qquad S_R=I_R\setminus H.
\]

對每個 t∈S_R 選一個不同素數 ℓ_t，大於 B+L+2R+10。由 CRT 選 0≤a<W，使

\[
a\equiv1\pmod B,\qquad a\equiv-t\pmod{\ell_t},
\qquad W=B\prod_{t\in S_R}\ell_t.
\tag{60.2}
\]

因 t∉H 且 |h−t|<ℓ_t，所有 h∈H 都有 a+h≢0 (mod ℓ_t)。也有 a+h≡1 (mod 每個 B 的素因子)。

**3. 檢查真正要套定理的線性式。** 取

\[
F_h(n)=Wn+a+h\quad(h\in H).
\]

若 ℓ|W，上一步證明所有 F_h 在模 ℓ 下均非零；若 ℓ∤W，則 W 可逆，而且必有 ℓ>K，此時至多 K 個禁止參數類不能填滿全部 ℓ 類。故 {F_h} 可容許。斜率 W 為正，兩個不同位置的行列式為 W(h'−h)≠0。

**4. 取得真實素數，並確保排除因子為真因子。** Maynard 給出任意大的 n，使至少兩個 F_h(n) 為素數。寫 T=Wn+a，並要求

\[
T-R-2>\max_{t\in S_R}\ell_t,\qquad T>X+R+4.
\]

這只是排除有限多個 n。對每個 t∈S_R，T+t 被 ℓ_t 整除且嚴格大於 ℓ_t，因而為合數。故 T+I_R 內的每個素數都位於 T+H。

按大小取 T+H 中實際為素數的位置的前兩個，記為 p=T+h_i、q=T+h_j。兩者之間的任何素數也必須來自 H，與選取方式矛盾，所以 p、q 是全體素數序列中的相鄰項。又有 B≤q−p≤L，兩者均為大於 3 的奇素數。

**5. 對稱表示造成模 B 矛盾。** 若 0≤δ≤R 且 p+1±δ 都為素數，兩個整數的位置

\[
h_i+1-\delta,\quad h_i+1+\delta
\]

都在 I_R，因此都屬於 H，均為 B 的倍數。但其和為 2h_i+2≡2 (mod B)，與 B≥6 矛盾。(60.1) 得證。

## 與原線性界的嚴格對接

給定自然數 C，取 R=CL，並令 q−p=2k。由 6≤2k≤L 得 k≥3 且 k≤L。於是 j=1 是有效非中央標籤，任何 δ≤Ck 都滿足 δ≤R，與 (60.1) 矛盾。所以 `GapRadiusBound C` 為假，包括 C=0。

還能作有限鴿巢推論：存在一個固定間隙 d∈{B,2B,…,(K−1)B}，對每個 R 都有任意大的相鄰 p、p+d 滿足 (60.1)。理由是，對每個 R，使這類 p 無界的間隙集合是一個非空有限集；R 增大時這些集合遞減，因此交集非空。這個 d 沒有被識別為 4，本構造實際只使用 B 的正倍數。

## 新提供的原始線程對照

使用者補充的[「Delta猜想应用分析」](https://chatgpt.com/c/6850cc53-6210-800e-98d6-4ba562f00a15)、[「δ猜想讨论」](https://chatgpt.com/g/g-p-684f7652c29c8191aa64f2eae1cb0787-ge-de-ba-he-cai-xiang/c/687f922b-f6b4-8333-9453-2ba39b244b44)、[「δ Mode Conjecture」](https://chatgpt.com/g/g-p-684f7652c29c8191aa64f2eae1cb0787-ge-de-ba-he-cai-xiang/c/685bf41f-fee8-800e-bbdf-940155a364cd)已讀取目前工具返回的可見回覆；附件、Canvas 與未返回的早期回覆不算已審查。

「δ猜想讨论」提出的族

\[
H_s=\{0,4\}\cup\{1\pm(6j-3):1\le j\le s\}
\]

在 s≥3 時不能直接當成 Maynard 的可容許族：H₃ 包含 −14,−8,−2,0,4,10,16，模 5 已佔滿全部五類。這是精確的局部反例；其中 δ=3 還使位置 4 重複，需按不同位置計數。

從「至少兩個位置為素數」也不能直接推出對稱位置同時為素數，更不能點名 0、4 均命中。本輪構造正是使用可容許族，取得至少兩個真實素數，同時排除指定中心的所有短對稱表示。這說明需另外證明配對機制。該線程中的 HL/BH 固定偏移陳述也是條件性、無窮多起點的命題，不是每個既定表哥中心的結論。

## 核驗層級

- 上述一般構造與鴿巢推論：完整紙面證明，使用已發表的無條件 Maynard 定理；Astra 對主要構造作了獨立審查。
- `verify.py`：以小型示範位置族核驗 CRT、真因子、線性式的局部條件和對稱位置矛盾；**示範 K 不宣稱達到 Maynard 門檻，也不聲稱數值找到所需無窮素數族**。
- `ClusterResidueObstruction.lean`：Luna 完成 `cluster_residue_sum_obstruction`，只核驗末端確定性的整數同餘矛盾；未形式化 Maynard 定理、CRT 存在性、自然數對稱表示接口或完整無窮族構造。具體型別與公理依賴見 `Checks.lean`。

一般 Goldbach 存在性與固定 gap=4 的原始目標仍未證明。這輪的用途是完整排除一類過強的短半徑要求，並讓後續歸納容許真正需要的遠距表示。
