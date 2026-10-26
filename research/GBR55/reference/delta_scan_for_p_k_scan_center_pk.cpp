// scan_center_pk.cpp  (C++17)
// g++ -O3 -march=native -std=c++17 scan_center_pk.cpp -o scan_center_pk

#include <bits/stdc++.h>
using namespace std;

struct PrimeTable {
    int N;
    vector<uint8_t> is_prime; // 0/1 for 0..N
    PrimeTable(int n): N(n), is_prime(n+1, 1) {
        if (N >= 0) is_prime[0] = 0;
        if (N >= 1) is_prime[1] = 0;
        for (int i=4; i<=N; i+=2) is_prime[i] = 0;
        int r = (int)std::sqrt((double)N);
        for (int p=3; p<=r; p+=2) {
            if (!is_prime[p]) continue;
            long long step = (long long)p * 2;
            long long start = 1LL * p * p;
            for (long long x=start; x<=N; x+=step) is_prime[(int)x] = 0;
        }
        if (N >= 2) is_prime[2] = 1;
    }
    inline bool operator()(int x) const {
        return x >= 0 && x <= N && is_prime[x];
    }
};

static inline int mod_pos(int a, int m) {
    int r = a % m;
    return r < 0 ? r + m : r;
}

int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    // ===== params (edit or parse args) =====
    int X = 100000000;   // p <= X
    int delta_max = 1000;
    vector<int> ks = {2,3,5};  // try k=2,3,5 first

    // Small primes for modular filter
    vector<int> qs = {3,5,7,11};
    int Q = 1;
    for (int q: qs) Q *= q;

    // Sieve upper bound: need up to (p+k)+delta_max and also p+2k
    int kmax = 0;
    for (int k: ks) kmax = max(kmax, k);
    int N = X + 2*kmax + delta_max + 10;

    cerr << "Sieve up to N=" << N << " ...\n";
    PrimeTable prime(N);

    // ===== Precompute candidate deltas by residue r = c mod Q =====
    // candidates[r] contains deltas in [1..delta_max] that PASS modular "not divisible by q" filters
    // Note: this filter ignores the special case c±delta == q (which is safe because prime check will accept it).
    vector<vector<int>> candidates(Q);
    for (int r=0; r<Q; r++) {
        candidates[r].reserve(delta_max);
        for (int d=1; d<=delta_max; d++) {
            bool ok = true;
            for (int q: qs) {
                int cq = r % q;              // c mod q (since r=c mod Q)
                int dq = d % q;              // d mod q
                // forbid d ≡  c (mod q) or d ≡ -c (mod q)
                int forb1 = cq;
                int forb2 = (q - cq) % q;    // -c mod q
                if (dq == forb1 || dq == forb2) { ok = false; break; }
            }
            if (ok) candidates[r].push_back(d);
        }
    }

    // ===== Output =====
    cout << "k,p,c,delta_min,c_mod3,c_mod5,c_mod7,c_modQ\n";

    // ===== Scan =====
    for (int k: ks) {
        cerr << "Scanning k=" << k << " ...\n";
        int step = 2; // odd p only
        for (int p=3; p<=X; p+=step) {
            if (!prime(p)) continue;
            int p2 = p + 2*k;
            if (p2 > N) break;
            if (!prime(p2)) continue;

            int c = p + k;
            int r = c % Q;

            int delta_min = -1;

            // We always know delta=k gives back (p, p+2k) => both prime.
            // But we still search smaller deltas first via candidates list.
            for (int d: candidates[r]) {
                if (d > delta_max) break;
                int a = c - d;
                int b = c + d;
                if (a < 2 || b > N) continue;
                if (prime(a) && prime(b)) { delta_min = d; break; }
            }
            // Fallback: if modular filter was too strict (e.g. hits "a==q" special), do direct check up to k
            if (delta_min < 0) {
                // Guaranteed success at d=k (since endpoints are prime), so only need scan 1..min(k,delta_max)
                int lim = min(k, delta_max);
                for (int d=1; d<=lim; d++) {
                    int a = c - d;
                    int b = c + d;
                    if (a < 2 || b > N) continue;
                    if (prime(a) && prime(b)) { delta_min = d; break; }
                }
            }

            cout << k << "," << p << "," << c << "," << delta_min << ","
                 << (c%3) << "," << (c%5) << "," << (c%7) << "," << r << "\n";
        }
    }

    cerr << "Done.\n";
    return 0;
}
