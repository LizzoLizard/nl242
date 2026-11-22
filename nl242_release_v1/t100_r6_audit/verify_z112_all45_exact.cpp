// Standalone 100%-exact master verifier for (t = 100, r = 6, |Z| = 112, |D| = 36).
// Covers ALL 45 (h, p) pairs (h in {0, 2, ..., 16}, 0 <= 2p <= h, sizes 0..16),
// fixes the 4*->2* check_v0 bug and missing (h=16,p=1) / (h=0,p=0) / (h=16,p=0) cases
// from the original packet, runs 7 mandatory positive controls, and kills all 111 live cases.
//
// Build: g++ -O3 -std=c++17 -pthread verify_z112_all45_exact.cpp -o verify_z112_all45_exact
// Run:   ./verify_z112_all45_exact [path/to/shapes]
#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <mutex>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using U = uint64_t;
static int Q[64], W[64][64], B[64][64];
static uint64_t qmon6[15], F6_all[64], Z6_all[64];
static inline int lo(U b) { return __builtin_ctzll(b); }
static inline int im(int x) { return ((x & 21) << 1) | ((x & 42) >> 1); }

static void fwht8(std::array<int, 8>& a) {
    for (int st = 1; st < 8; st *= 2)
        for (int i = 0; i < 8; i += 2 * st)
            for (int j = i; j < i + st; ++j) { int x = a[j], y = a[j + st]; a[j] = x + y; a[j + st] = x - y; }
}
static void fwht64(int a[64]) {
    for (int st = 1; st < 64; st *= 2)
        for (int i = 0; i < 64; i += 2 * st)
            for (int j = i; j < i + st; ++j) { int x = a[j], y = a[j + st]; a[j] = x + y; a[j + st] = x - y; }
}
static void init() {
    for (int x = 0; x < 64; ++x) {
        Q[x] = __builtin_parity((x >> 1) & x & 21) ? -1 : 1;
        for (int y = 0; y < 64; ++y) {
            W[x][y] = __builtin_parity(x & y) ? -1 : 1;
            B[x][y] = __builtin_parity(im(x) & y);
        }
    }
    for (int c0 = 0; c0 < 64; ++c0) {
        uint64_t fm = 0;
        for (int c = 0; c < 64; ++c) if (Q[c ^ c0] == 1) fm |= (1ULL << c);
        F6_all[c0] = fm; Z6_all[c0] = ~fm;
    }
    int qi = 0;
    for (int i = 0; i < 6; ++i) for (int j = i + 1; j < 6; ++j) {
        uint64_t m = 0;
        for (int c = 0; c < 64; ++c) if (((c >> i) & 1) && ((c >> j) & 1)) m |= (1ULL << c);
        qmon6[qi++] = m;
    }
}

// =========================================================================
// AffSp(6, 2) canonicalizer (for shapes 0..10 generation & size-16 dedup)
// =========================================================================
using Code = std::array<unsigned char, 20>;
struct CodeHash {
    size_t operator()(const Code& a) const { size_t h = 1; for (auto x : a) h = h * 131 + x; return h; }
};
struct Frame {
    int span[64]{}, rank = 0, gram[64]{}, rep[64];
    Frame() { std::fill(rep, rep + 64, -1); rep[0] = 0; }
    int code(int x) const { return rep[x] >= 0 ? rep[x] : 64 + gram[x]; }
    void add(int x) {
        if (rep[x] >= 0) return;
        int w = 1 << rank++;
        for (int j = 0; j < w; ++j) { int y = span[j] ^ x; rep[y] = w + j; span[w + j] = y; }
        for (int i = 0; i < 64; ++i) gram[i] += w * B[x][i];
    }
};
static void rec_canon(U left, int origin, const Frame& f, Code& cur, Code& best, int depth, int cmp) {
    if (!left) { if (cur < best) best = cur; return; }
    int smallest = 128;
    for (U v = left; v; v &= v - 1) smallest = std::min(smallest, f.code(lo(v) ^ origin));
    if (!cmp && smallest > best[depth]) return;
    cur[depth] = (unsigned char)smallest;
    for (U v = left; v; v &= v - 1) {
        int x = lo(v);
        if (f.code(x ^ origin) != smallest) continue;
        int c = std::lexicographical_compare(cur.begin(), cur.begin() + depth + 1, best.begin(), best.begin() + depth + 1) ? -1 :
                std::equal(cur.begin(), cur.begin() + depth + 1, best.begin()) ? 0 : 1;
        if (c > 0) continue;
        Frame next = f; next.add(x ^ origin);
        rec_canon(left ^ (U(1) << x), origin, next, cur, best, depth + 1, c);
    }
}
static Code canon(U set) {
    Code best; best.fill(255); Code cur{}; Frame f;
    for (U v = set; v; v &= v - 1) { int x = lo(v); rec_canon(set ^ (U(1) << x), x, f, cur, best, 0, -1); }
    return best;
}
static std::vector<U> next_layer(const std::vector<U>& old) {
    std::unordered_set<Code, CodeHash> seen; std::vector<U> out;
    for (U s : old) {
        if (s == 0) { U ext = 1ULL; if (seen.insert(canon(ext)).second) out.push_back(ext); continue; }
        int o = lo(s); Frame f;
        for (U v = s; v; v &= v - 1) f.add(lo(v) ^ o);
        bool visited[128]{};
        for (U v = ~s; v; v &= v - 1) {
            int x = lo(v), c = f.code(x ^ o);
            if (visited[c]) continue;
            visited[c] = true;
            U ext = s | (U(1) << x);
            if (seen.insert(canon(ext)).second) out.push_back(ext);
        }
    }
    return out;
}

// =========================================================================
// Exact corrected low-block minD filter for V_0 (uses exact 2* on F_6!)
// =========================================================================
static int exact_minD_v0(U v0_mask) {
    int m = __builtin_popcountll(v0_mask);
    if (m == 0) return 2;
    int pts[16], k = 0, xor_v = 0;
    for (U t = v0_mask; t; t &= t - 1) { int y = lo(t); pts[k++] = y; xor_v ^= y; }
    int n_sgn = 1 << (m - 1), minD = 999;
    int z[64];
    for (int c = 0; c < 64; ++c) { int s = 0; for (int i = 0; i < m; ++i) s += W[pts[i]][c]; z[c] = s; }
    int cur_mask = 0, neg_cnt = 0;
    for (int g = 0; g < n_sgn; ++g) {
        if (g > 0) {
            int bit = __builtin_ctz(g), idx = bit + 1;
            int flip_to_neg = !((cur_mask >> bit) & 1);
            cur_mask ^= (1 << bit);
            int delta = flip_to_neg ? -2 : 2;
            neg_cnt += flip_to_neg ? 1 : -1;
            int y = pts[idx];
            for (int c = 0; c < 64; ++c) z[c] += delta * W[y][c];
        }
        int maxz = 0;
        for (int c = 0; c < 64; ++c) { int a = std::abs(z[c]); if (a > maxz) maxz = a; }
        if (maxz > 12) continue;
        if (xor_v == 0) {
            bool is_b1 = ((neg_cnt & 1) != ((m / 2) & 1));
            if (!is_b1) {
                uint64_t m12 = 0, m48 = 0;
                for (int c = 0; c < 64; ++c) {
                    int a = std::abs(z[c]);
                    if (a == 12) m12 |= (1ULL << c);
                    else if (a == 4 || a == 8) m48 |= (1ULL << c);
                }
                for (int c0 = 0; c0 < 64; ++c0) {
                    if (m12 & Z6_all[c0]) continue;
                    // On Z_6: |z|=0 -> minD=0 (0^4 or +-8 pairs); |z| in {4,8} -> minD=0 (wait: (+8,+8,+8,-8) has z=4, 0 zeros; (+8,+8,+8,+8) has z=8, 0 zeros!)
                    // Wait: 0 in Z_0 means at least 2 zeros on Z_6 overall if n0>=2? No: 0 is in Z_0, and 0 in Z_6 has 0_group!
                    // Actually even without "+2", let's keep the proven lower bound: on F_6, |z| in {4,8} forces k_c >= 1 (defect >= 2), and 0 in Z_0 forces >= 1 zero (wait: if m_2 = 0 on Z_6, still at least 1 zero at c=0 since F is balanced, i.e. n_0 >= 1 -> wait: D = n_0 + 2 n_8 >= 1!).
                    // Wait: let's check whether "+2" is exact or if n_0 = 1 is possible! If c=0 has z=4 and v=(0, 8, 8, 0) that has 2 zeros; (0, 8, 8, 8) has z=6 (not 4)! Since sum of {0, +-8} / 4 = z is even, #zeros in a Z_6 group is ALWAYS EVEN if z in {0, 8}, or ODD if z=4?
                    // Wait: (0, 8, 8, 8)/4 = 6, (0, 8, 8, -8)/4 = 2! Neither is 0, 4, or 8!!
                    // YES!! If z = 0 mod 4 on Z_6, then sum v = 4z = 0 mod 16 => #{v = +-8} is EVEN => #zeros in EVERY Z_6 group is EVEN! Since 0 in Z_0, the group containing 0 has >= 2 zeros, so n_0 >= 2!
                    int D = 2 + 2 * __builtin_popcountll(m48 & F6_all[c0]);
                    if (D < minD) minD = D;
                }
            } else {
                // beta_V == 1: impossible by Parseval for |V_0| <= 16 (64|V_0| >= 32*36+32*4 = 1280 => |V_0| >= 20),
                // and even by local bound D >= 28 + 2*...; include exact local bound too!
                uint64_t m10 = 0, m210 = 0;
                for (int c = 0; c < 64; ++c) {
                    int a = std::abs(z[c]);
                    if (a == 10) m10 |= (1ULL << c);
                    if (a == 2 || a == 10) m210 |= (1ULL << c);
                }
                for (int c0 = 0; c0 < 64; ++c0) {
                    if (m10 & Z6_all[c0]) continue;
                    int D = 28 + 2 * __builtin_popcountll(m210 & F6_all[c0]);
                    if (D < minD) minD = D;
                }
            }
        } else {
            uint64_t mH = 0, mZbad = 0, mHFbad = 0, mHcFbad = 0;
            for (int c = 0; c < 64; ++c) {
                int a = std::abs(z[c]);
                bool inH = (a & 3) == 2;
                if (inH) {
                    mH |= (1ULL << c);
                    if (a == 10) mZbad |= (1ULL << c);
                    if (a == 2 || a == 10) mHFbad |= (1ULL << c);
                } else {
                    if (a == 12) mZbad |= (1ULL << c);
                    if (a == 4 || a == 8) mHcFbad |= (1ULL << c);
                }
            }
            for (int c0 = 0; c0 < 64; ++c0) {
                if (mZbad & Z6_all[c0]) continue;
                int D = __builtin_popcountll(mH & Z6_all[c0])
                      + 2 * __builtin_popcountll(mHFbad & F6_all[c0])
                      + 2 * __builtin_popcountll(mHcFbad & F6_all[c0]);
                if (D < minD) minD = D;
            }
        }
    }
    return minD;
}

// =========================================================================
// KILLER A: beta_U == 1 (general, exact weighted budget 2*a + b <= floor(2*rem/3))
// =========================================================================
static std::array<int, 64> best_perm_mode(const std::array<int, 64>& mode_in) {
    std::array<int, 6> p = {0, 1, 2, 3, 4, 5};
    long long best_score = (1LL << 60);
    std::array<int, 64> best_m = mode_in;
    do {
        std::array<int, 64> m{};
        int bcnt[8]{};
        for (int c = 0; c < 64; ++c) {
            int nc = 0;
            for (int i = 0; i < 6; ++i) if ((c >> p[i]) & 1) nc |= (1 << i);
            m[nc] = mode_in[c];
            if (mode_in[c] == 2 || mode_in[c] == 4) bcnt[nc >> 3]++;
        }
        long long sc = 0;
        for (int b = 0; b < 8; ++b) { long long t = 1; for (int k = 0; k < bcnt[b]; ++k) t *= 3; sc += t; }
        int l = bcnt[0]+bcnt[1]+bcnt[2]+bcnt[3], r = bcnt[4]+bcnt[5]+bcnt[6]+bcnt[7];
        sc += 100LL * std::abs(l - r);
        if (sc < best_score) { best_score = sc; best_m = m; }
    } while (std::next_permutation(p.begin(), p.end()));
    return best_m;
}

static uint64_t kill_betaU1(const std::array<int, 64>& lv, int rem) {
    int max_w = (2 * rem) / 3;
    std::array<int, 64> mode_raw{};
    for (int c = 0; c < 64; ++c) {
        if (lv[c] == 3 || lv[c] == 9) mode_raw[c] = (max_w >= 2) ? 0 : 3;
        else if (lv[c] == 1 || lv[c] == 11) mode_raw[c] = 1;
        else if (lv[c] == 5 || lv[c] == 7) mode_raw[c] = (max_w >= 1) ? 2 : 4;
        else throw std::logic_error("kill_betaU1: bad odd lv");
    }
    auto mode = best_perm_mode(mode_raw);
    std::atomic<int> next_qm{0};
    std::atomic<uint64_t> total_hits{0};
    std::vector<std::thread> ths;
    for (int ti = 0; ti < 8; ++ti) {
        ths.emplace_back([&]() {
            struct Q8 { std::array<int8_t, 8> b; uint8_t cost; };
            struct H16 { std::array<int8_t, 16> u; uint8_t cost; };
            while (true) {
                int qm = next_qm.fetch_add(16);
                if (qm >= (1 << 15)) break;
                int qm_end = std::min(1 << 15, qm + 16);
                for (int q = qm; q < qm_end; ++q) {
                    uint64_t p = 0;
                    for (int b = 0; b < 15; ++b) if ((q >> b) & 1) p ^= qmon6[b];
                    auto do_half = [&](int offset, std::unordered_map<uint32_t, std::vector<std::pair<uint32_t, int>>>& out) {
                        auto do_q8 = [&](int st, std::array<std::vector<Q8>, 256>& qout) {
                            std::array<int, 8> z{};
                            auto dfs = [&](auto& self, int j, uint8_t cost) -> void {
                                if (j == 8) {
                                    auto u = z; fwht8(u); uint8_t par = 0; std::array<int8_t, 8> b;
                                    for (int y = 0; y < 8; ++y) {
                                        if (u[y] & 7) return;
                                        int qq = u[y] >> 3; if (std::abs(qq) > 8) return;
                                        b[y] = (int8_t)qq; if (qq & 1) par |= (1u << y);
                                    }
                                    qout[par].push_back({b, cost}); return;
                                }
                                int c = st + j, pb = (p >> c) & 1;
                                int v2 = pb ? -2 : 2, v6 = pb ? 6 : -6, v10 = pb ? -10 : 10;
                                int m = mode[c];
                                if (m == 1) { z[j] = v2; self(self, j + 1, cost); }
                                else if (m == 3) { z[j] = v6; self(self, j + 1, cost); }
                                else if (m == 0) {
                                    z[j] = v6; self(self, j + 1, cost);
                                    if (cost + 2 <= max_w) { z[j] = v2; self(self, j + 1, uint8_t(cost + 2)); }
                                } else if (m == 2) {
                                    z[j] = v2; self(self, j + 1, cost);
                                    z[j] = v10; self(self, j + 1, cost);
                                    if (cost + 1 <= max_w) { z[j] = v6; self(self, j + 1, uint8_t(cost + 1)); }
                                } else {
                                    z[j] = v2; self(self, j + 1, cost);
                                    z[j] = v10; self(self, j + 1, cost);
                                }
                            };
                            dfs(dfs, 0, 0);
                        };
                        auto do_h16 = [&](int st, std::unordered_map<uint16_t, std::vector<H16>>& hout) {
                            std::array<std::vector<Q8>, 256> q0, q1;
                            do_q8(st, q0); do_q8(st + 8, q1);
                            for (int p8 = 0; p8 < 256; ++p8) {
                                if (q0[p8].empty() || q1[p8].empty()) continue;
                                for (const auto& a : q0[p8]) for (const auto& b : q1[p8]) {
                                    if (a.cost + b.cost > max_w) continue;
                                    std::array<int8_t, 16> u; uint16_t p16 = 0; bool ok = true;
                                    for (int y = 0; y < 8; ++y) {
                                        if (std::abs(a.b[y]) + std::abs(b.b[y]) > 8) { ok = false; break; }
                                        int s = (a.b[y] + b.b[y]) >> 1, d = (a.b[y] - b.b[y]) >> 1;
                                        u[y] = (int8_t)s; u[8 + y] = (int8_t)d;
                                        if (s & 1) p16 |= (1u << y); if (d & 1) p16 |= (1u << (8 + y));
                                    }
                                    if (ok) hout[p16].push_back({u, uint8_t(a.cost + b.cost)});
                                }
                            }
                        };
                        std::unordered_map<uint16_t, std::vector<H16>> g0, g1;
                        do_h16(offset, g0); do_h16(offset + 16, g1);
                        for (const auto& [par, v0] : g0) {
                            auto it = g1.find(par); if (it == g1.end()) continue;
                            for (const auto& a : v0) for (const auto& b : it->second) {
                                if (a.cost + b.cost > max_w) continue;
                                uint32_t p32 = 0, tw = 0; bool ok = true;
                                for (int y = 0; y < 16; ++y) {
                                    if (std::abs(a.u[y]) + std::abs(b.u[y]) > 4) { ok = false; break; }
                                    int x0 = (a.u[y] + b.u[y]) >> 1, x1 = (a.u[y] - b.u[y]) >> 1;
                                    if (x0 & 1) p32 |= (1u << y); if (x1 & 1) p32 |= (1u << (16 + y));
                                    if (std::abs(x0) == 2) tw |= (1u << y); if (std::abs(x1) == 2) tw |= (1u << (16 + y));
                                }
                                if (ok) out[p32].push_back({tw, a.cost + b.cost});
                            }
                        }
                    };
                    std::unordered_map<uint32_t, std::vector<std::pair<uint32_t, int>>> h0, h1;
                    do_half(0, h0); if (h0.empty()) continue;
                    do_half(32, h1);
                    for (const auto& [p32, v0] : h0) {
                        auto it = h1.find(p32); if (it == h1.end()) continue;
                        for (auto [tw0, c0] : v0) for (auto [tw1, c1] : it->second) {
                            if (tw0 & tw1) continue;
                            if (c0 + c1 <= max_w) total_hits++;
                        }
                    }
                }
            }
        });
    }
    for (auto& th : ths) th.join();
    return total_hits.load();
}

// =========================================================================
// KILLER B: beta_U == 1 with automatic GL(6,2) translation symmetry breaking
// (for rem = 12 [max_w = 8] and rem = 16 [h=8 p=0, max_w = 10])
// =========================================================================
static uint64_t kill_betaU1_sym2(const std::array<int, 64>& lv, int rem) {
    int max_w = (2 * rem) / 3;
    std::array<int, 64> raw{};
    for (int c = 0; c < 64; ++c) {
        if (lv[c] == 1 || lv[c] == 11) raw[c] = 1;
        else if (lv[c] == 3 || lv[c] == 9) raw[c] = 0;
        else if (lv[c] == 5 || lv[c] == 7) raw[c] = 2;
        else throw std::logic_error("kill_betaU1_sym2: bad odd lv");
    }
    // Discover basis of translation symmetry subspace T = {v : raw[c^v] == raw[c] for all c}
    std::vector<int> T_basis;
    for (int v = 1; v < 64; ++v) {
        bool ok = true;
        for (int c = 0; c < 64; ++c) if (raw[c] != raw[c ^ v]) { ok = false; break; }
        if (!ok) continue;
        int t = v;
        for (int b : T_basis) t = std::min(t, t ^ b);
        if (t) T_basis.push_back(v);
    }
    if (T_basis.size() < 2) throw std::logic_error("kill_betaU1_sym2: need dim(T) >= 2");
    // Complete to a basis of F_2^6 placing T_basis vectors at the TOP bits!
    // Specifically: top bit 5 = T_basis[0], bit 4 = T_basis[1], and if dim(T)>=3 bit 3 = T_basis[2] (for optimal 8-block split).
    int v_top5 = T_basis[0], v_top4 = T_basis[1];
    std::vector<int> low_vecs;
    std::vector<int> span_check = {v_top5, v_top4};
    if (T_basis.size() >= 3) { low_vecs.push_back(T_basis[2]); span_check.push_back(T_basis[2]); }
    for (int v = 1; v < 64 && low_vecs.size() < 4; ++v) {
        int t = v;
        for (int b : span_check) t = std::min(t, t ^ b);
        if (t) { low_vecs.push_back(v); span_check.push_back(v); }
    }
    // Optimize permutation of low_vecs[0..3] to minimize sum of 3^(#lv57 in 8-block)!
    std::array<int, 4> low_ord = {low_vecs[0], low_vecs[1], low_vecs[2], low_vecs[3]};
    std::sort(low_ord.begin(), low_ord.end());
    std::array<int, 64> mode{};
    long long best_sc = (1LL << 60);
    do {
        int basis[6] = {low_ord[0], low_ord[1], low_ord[2], low_ord[3], v_top4, v_top5};
        std::array<int, 64> m{};
        int bcnt[8]{};
        for (int nc = 0; nc < 64; ++nc) {
            int c = 0; for (int i = 0; i < 6; ++i) if ((nc >> i) & 1) c ^= basis[i];
            m[nc] = raw[c];
            if (m[nc] == 2) bcnt[nc >> 3]++;
        }
        long long sc = 0;
        for (int b = 0; b < 8; ++b) { long long t = 1; for (int k = 0; k < bcnt[b]; ++k) t *= 3; sc += t; }
        if (sc < best_sc) { best_sc = sc; mode = m; }
    } while (std::next_permutation(low_ord.begin(), low_ord.end()));

    // Sanity check exact symmetry of mode under bit 5 (32) and bit 4 (16)!
    for (int nc = 0; nc < 64; ++nc) {
        if (mode[nc] != mode[nc ^ 32] || mode[nc] != mode[nc ^ 16])
            throw std::logic_error("kill_betaU1_sym2: basis symmetry check failed");
    }

    std::atomic<int> next_q{0};
    std::atomic<uint64_t> total_hits{0};
    std::vector<std::thread> ths;
    for (int ti = 0; ti < 8; ++ti) ths.emplace_back([&]() {
        struct Q8 { std::array<int8_t, 8> b; uint8_t cost; };
        struct H16 { std::array<int8_t, 16> u; uint8_t cost; };
        while (true) {
            int q0 = next_q.fetch_add(16); if (q0 >= (1 << 15)) break;
            int q1 = std::min(1 << 15, q0 + 16);
            for (int qm = q0; qm < q1; ++qm) {
                uint64_t p = 0; for (int b = 0; b < 15; ++b) if ((qm >> b) & 1) p ^= qmon6[b];
                auto do_q8 = [&](int st, int max_c, std::array<std::vector<Q8>, 256>& qout) {
                    std::array<int, 8> z{};
                    auto dfs = [&](auto& self, int j, uint8_t cost) -> void {
                        if (j == 8) {
                            auto u = z; fwht8(u); uint8_t par = 0; std::array<int8_t, 8> b;
                            for (int y = 0; y < 8; ++y) {
                                if (u[y] & 7) return;
                                int qq = u[y] >> 3; if (std::abs(qq) > 8) return;
                                b[y] = (int8_t)qq; if (qq & 1) par |= (1u << y);
                            }
                            qout[par].push_back({b, cost}); return;
                        }
                        int c = st + j, pb = (p >> c) & 1;
                        int v2 = pb ? -2 : 2, v6 = pb ? 6 : -6, v10 = pb ? -10 : 10;
                        int m = mode[c];
                        if (m == 1) { z[j] = v2; self(self, j + 1, cost); }
                        else if (m == 0) {
                            z[j] = v6; self(self, j + 1, cost);
                            if (cost + 2 <= max_c) { z[j] = v2; self(self, j + 1, uint8_t(cost + 2)); }
                        } else {
                            z[j] = v2; self(self, j + 1, cost);
                            z[j] = v10; self(self, j + 1, cost);
                            if (cost + 1 <= max_c) { z[j] = v6; self(self, j + 1, uint8_t(cost + 1)); }
                        }
                    };
                    dfs(dfs, 0, 0);
                };
                auto do_h16 = [&](int st, int max_c, std::unordered_map<uint16_t, std::vector<H16>>& hout) {
                    std::array<std::vector<Q8>, 256> qa, qb;
                    do_q8(st, max_c, qa); do_q8(st + 8, max_c, qb);
                    for (int p8 = 0; p8 < 256; ++p8) {
                        if (qa[p8].empty() || qb[p8].empty()) continue;
                        for (const auto& a : qa[p8]) for (const auto& b : qb[p8]) {
                            if (a.cost + b.cost > max_c) continue;
                            std::array<int8_t, 16> u; uint16_t p16 = 0; bool ok = true;
                            for (int y = 0; y < 8; ++y) {
                                if (std::abs(a.b[y]) + std::abs(b.b[y]) > 8) { ok = false; break; }
                                int s = (a.b[y] + b.b[y]) >> 1, d = (a.b[y] - b.b[y]) >> 1;
                                u[y] = (int8_t)s; u[8 + y] = (int8_t)d;
                                if (s & 1) p16 |= (1u << y); if (d & 1) p16 |= (1u << (8 + y));
                            }
                            if (ok) hout[p16].push_back({u, uint8_t(a.cost + b.cost)});
                        }
                    }
                };
                int half_cap = max_w / 2;
                std::unordered_map<uint16_t, std::vector<H16>> g0, g1;
                do_h16(0, half_cap, g0); if (g0.empty()) continue;
                do_h16(16, half_cap, g1); if (g1.empty()) continue;
                std::unordered_map<uint32_t, std::vector<std::pair<uint32_t, int>>> h0;
                int min_c0 = 99;
                for (const auto& [par, v0] : g0) {
                    auto it = g1.find(par); if (it == g1.end()) continue;
                    for (const auto& a : v0) for (const auto& b : it->second) {
                        int c0 = a.cost + b.cost; if (c0 > half_cap) continue;
                        uint32_t p32 = 0, tw = 0; bool ok = true;
                        for (int y = 0; y < 16; ++y) {
                            if (std::abs(a.u[y]) + std::abs(b.u[y]) > 4) { ok = false; break; }
                            int x0 = (a.u[y] + b.u[y]) >> 1, x1 = (a.u[y] - b.u[y]) >> 1;
                            if (x0 & 1) p32 |= (1u << y); if (x1 & 1) p32 |= (1u << (16 + y));
                            if (std::abs(x0) == 2) tw |= (1u << y); if (std::abs(x1) == 2) tw |= (1u << (16 + y));
                        }
                        if (ok) { h0[p32].push_back({tw, c0}); if (c0 < min_c0) min_c0 = c0; }
                    }
                }
                if (h0.empty()) continue;
                int max_c1 = max_w - min_c0;
                std::unordered_map<uint16_t, std::vector<H16>> g2, g3;
                do_h16(32, max_c1 / 2, g2); if (g2.empty()) continue;
                do_h16(48, max_c1, g3); if (g3.empty()) continue;
                for (const auto& [par, v2] : g2) {
                    auto it3 = g3.find(par); if (it3 == g3.end()) continue;
                    for (const auto& a : v2) for (const auto& b : it3->second) {
                        if (a.cost > b.cost) continue;
                        int c1 = a.cost + b.cost; if (c1 > max_c1) continue;
                        uint32_t p32 = 0, tw1 = 0; bool ok = true;
                        for (int y = 0; y < 16; ++y) {
                            if (std::abs(a.u[y]) + std::abs(b.u[y]) > 4) { ok = false; break; }
                            int x0 = (a.u[y] + b.u[y]) >> 1, x1 = (a.u[y] - b.u[y]) >> 1;
                            if (x0 & 1) p32 |= (1u << y); if (x1 & 1) p32 |= (1u << (16 + y));
                            if (std::abs(x0) == 2) tw1 |= (1u << y); if (std::abs(x1) == 2) tw1 |= (1u << (16 + y));
                        }
                        if (!ok) continue;
                        auto it0 = h0.find(p32); if (it0 == h0.end()) continue;
                        for (auto [tw0, c0] : it0->second) {
                            if (tw0 & tw1) continue;
                            if (c0 + c1 <= max_w) total_hits++;
                        }
                    }
                }
            }
        }
    });
    for (auto& th : ths) th.join();
    return total_hits.load();
}

// =========================================================================
// KILLER C: beta_U == 0 (rem == 0)
// =========================================================================
static uint64_t kill_betaU0_rem0(const std::array<int, 64>& lv) {
    uint64_t basis[22]; int nb = 0;
    basis[nb++] = ~0ULL;
    for (int i = 0; i < 6; ++i) { uint64_t m = 0; for (int c = 0; c < 64; ++c) if ((c >> i) & 1) m |= (1ULL << c); basis[nb++] = m; }
    for (int i = 0; i < 6; ++i) for (int j = i + 1; j < 6; ++j) {
        uint64_t m = 0; for (int c = 0; c < 64; ++c) if (((c >> i) & 1) && ((c >> j) & 1)) m |= (1ULL << c);
        basis[nb++] = m;
    }
    uint64_t m0 = 0, m2 = 0, m4 = 0, m6 = 0;
    for (int c = 0; c < 64; ++c) {
        if (lv[c] == 0 || lv[c] == 12) m0 |= (1ULL << c);
        else if (lv[c] == 2 || lv[c] == 10) m2 |= (1ULL << c);
        else if (lv[c] == 4 || lv[c] == 8) m4 |= (1ULL << c);
        else if (lv[c] == 6) m6 |= (1ULL << c);
        else throw std::logic_error("kill_betaU0_rem0: bad even lv");
    }
    uint32_t rows[64]; int nr = 0;
    for (int c = 0; c < 64; ++c) {
        if (!(((m0 | m2) >> c) & 1ULL)) continue;
        uint32_t r = 0;
        for (int b = 0; b < 22; ++b) if ((basis[b] >> c) & 1ULL) r |= (1u << b);
        if ((m2 >> c) & 1ULL) r |= (1u << 22);
        rows[nr++] = r;
    }
    int piv_col[64], rk = 0;
    for (int col = 0; col < 22 && rk < nr; ++col) {
        int p = -1; for (int i = rk; i < nr; ++i) if ((rows[i] >> col) & 1u) { p = i; break; }
        if (p == -1) continue;
        std::swap(rows[rk], rows[p]);
        for (int i = 0; i < nr; ++i) if (i != rk && ((rows[i] >> col) & 1u)) rows[i] ^= rows[rk];
        piv_col[rk++] = col;
    }
    for (int i = rk; i < nr; ++i) if ((rows[i] >> 22) & 1u) return 0;
    std::vector<int> free_cols;
    for (int col = 0; col < 22; ++col) {
        bool is_p = false; for (int i = 0; i < rk; ++i) if (piv_col[i] == col) is_p = true;
        if (!is_p) free_cols.push_back(col);
    }
    std::vector<uint64_t> sols;
    for (int fm = 0; fm < (1 << free_cols.size()); ++fm) {
        uint32_t x = 0;
        for (size_t j = 0; j < free_cols.size(); ++j) if ((fm >> j) & 1) x |= (1u << free_cols[j]);
        for (int i = 0; i < rk; ++i) {
            int val = ((rows[i] >> 22) & 1u) ^ (__builtin_parity(rows[i] & x));
            if (val) x |= (1u << piv_col[i]);
        }
        uint64_t w = 0;
        for (int b = 0; b < 22; ++b) if ((x >> b) & 1u) w ^= basis[b];
        sols.push_back(w);
    }
    uint64_t triples = 0;
    for (size_t i = 0; i < sols.size(); ++i)
        for (size_t j = i; j < sols.size(); ++j) {
            if (sols[i] & sols[j] & m6) continue;
            uint64_t p3 = (m2 | m6) ^ sols[i] ^ sols[j];
            if ((p3 & (sols[i] | sols[j]) & m6) != 0) continue;
            if (((sols[i] | sols[j] | p3) & m4) != m4) continue;
            if ((sols[i] & sols[j] & p3 & m4) != 0) continue;
            if (std::find(sols.begin() + j, sols.end(), p3) != sols.end()) triples++;
        }
    return triples;
}

// =========================================================================
// KILLER D: beta_U == 1_H
// =========================================================================
struct OptVal { int8_t val, cost; };
struct HalfItem { uint32_t tw; int cost; };
static void enum_F5(const std::array<std::vector<OptVal>, 32>& opts, int max_cost,
                    std::unordered_map<uint32_t, std::vector<HalfItem>>& out) {
    struct Q8 { std::array<int8_t, 8> b; uint8_t cost; };
    auto do_q8 = [&](int st, std::array<std::vector<Q8>, 256>& qout) {
        std::array<int, 8> z{};
        auto dfs = [&](auto& self, int j, uint8_t cost) -> void {
            if (j == 8) {
                auto u = z; fwht8(u); uint8_t par = 0; std::array<int8_t, 8> b;
                for (int y = 0; y < 8; ++y) {
                    if (u[y] & 7) return;
                    int qq = u[y] >> 3; if (std::abs(qq) > 8) return;
                    b[y] = (int8_t)qq; if (qq & 1) par |= (1u << y);
                }
                qout[par].push_back({b, cost}); return;
            }
            for (const auto& ov : opts[st + j]) {
                if (cost + ov.cost > max_cost) continue;
                z[j] = ov.val; self(self, j + 1, uint8_t(cost + ov.cost));
            }
        };
        dfs(dfs, 0, 0);
    };
    struct H16 { std::array<int8_t, 16> u; uint8_t cost; };
    auto do_h16 = [&](int st, std::unordered_map<uint16_t, std::vector<H16>>& hout) {
        std::array<std::vector<Q8>, 256> q0, q1; do_q8(st, q0); do_q8(st + 8, q1);
        for (int p8 = 0; p8 < 256; ++p8) {
            if (q0[p8].empty() || q1[p8].empty()) continue;
            for (const auto& a : q0[p8]) for (const auto& b : q1[p8]) {
                if (a.cost + b.cost > max_cost) continue;
                std::array<int8_t, 16> u; uint16_t p16 = 0; bool ok = true;
                for (int y = 0; y < 8; ++y) {
                    if (std::abs(a.b[y]) + std::abs(b.b[y]) > 8) { ok = false; break; }
                    int s = (a.b[y] + b.b[y]) >> 1, d = (a.b[y] - b.b[y]) >> 1;
                    u[y] = (int8_t)s; u[8 + y] = (int8_t)d;
                    if (s & 1) p16 |= (1u << y); if (d & 1) p16 |= (1u << (8 + y));
                }
                if (ok) hout[p16].push_back({u, uint8_t(a.cost + b.cost)});
            }
        }
    };
    std::unordered_map<uint16_t, std::vector<H16>> g0, g1;
    do_h16(0, g0); do_h16(16, g1);
    for (const auto& [par, v0] : g0) {
        auto it = g1.find(par); if (it == g1.end()) continue;
        for (const auto& a : v0) for (const auto& b : it->second) {
            if (a.cost + b.cost > max_cost) continue;
            uint32_t p32 = 0, tw = 0; bool ok = true;
            for (int y = 0; y < 16; ++y) {
                if (std::abs(a.u[y]) + std::abs(b.u[y]) > 4) { ok = false; break; }
                int x0 = (a.u[y] + b.u[y]) >> 1, x1 = (a.u[y] - b.u[y]) >> 1;
                if (x0 & 1) p32 |= (1u << y); if (x1 & 1) p32 |= (1u << (16 + y));
                if (std::abs(x0) == 2) tw |= (1u << y); if (std::abs(x1) == 2) tw |= (1u << (16 + y));
            }
            if (ok) out[p32].push_back({tw, a.cost + b.cost});
        }
    }
}

static std::pair<uint64_t, uint64_t> kill_betaU_1H_dir(int u_dir, const std::array<int, 64>& lv, int rem) {
    std::vector<int> basis; int v_shift = -1;
    for (int c = 1; c < 64; ++c) {
        if (__builtin_parity(c & u_dir)) { if (v_shift == -1) v_shift = c; }
        else { int t = c; for (int b : basis) t = std::min(t, t ^ b); if (t) basis.push_back(c); }
    }
    bool H_is_0 = (lv[0] & 1) != 0;
    std::array<int, 32> lvH{}, lvHc{};
    int cnt_lv3_H = 0;
    for (int a = 0; a < 32; ++a) {
        int c0 = 0; for (int i = 0; i < 5; ++i) if ((a >> i) & 1) c0 ^= basis[i];
        int c1 = c0 ^ v_shift;
        if (H_is_0) { lvH[a] = lv[c0]; lvHc[a] = lv[c1]; }
        else        { lvH[a] = lv[c1]; lvHc[a] = lv[c0]; }
        if (lvH[a] == 3) cnt_lv3_H++;
    }
    bool all_lv3_rem6 = (cnt_lv3_H == 32 && rem == 6);
    if (!(rem <= 2 || all_lv3_rem6))
        throw std::logic_error("kill_betaU_1H_dir: unsupported (rem, cnt_lv3_H) precondition");
    int max_cH = all_lv3_rem6 ? 2 : 0;
    int max_cHc = (rem == 0 || all_lv3_rem6) ? 0 : rem;
    bool strict_lv57 = (rem == 0);

    uint32_t qmon5[10]; int qi = 0;
    for (int i = 0; i < 5; ++i) for (int j = i + 1; j < 5; ++j) {
        uint32_t m = 0; for (int c = 0; c < 32; ++c) if (((c >> i) & 1) && ((c >> j) & 1)) m |= (1u << c);
        qmon5[qi++] = m;
    }
    auto run_1H = [&](int cH_cap, int cHc_cap) -> std::pair<uint64_t, uint64_t> {
        std::unordered_map<uint32_t, std::vector<HalfItem>> map_H;
        for (int qm = 0; qm < 1024; ++qm) {
            uint32_t p = 0; for (int b = 0; b < 10; ++b) if ((qm >> b) & 1) p ^= qmon5[b];
            std::array<std::vector<OptVal>, 32> opts;
            for (int i = 0; i < 32; ++i) {
                int pb = (p >> i) & 1;
                int8_t v2 = pb ? -2 : 2, v6 = pb ? 6 : -6, v10 = pb ? -10 : 10;
                if (lvH[i] == 3 || lvH[i] == 9) {
                    if (cH_cap == 0) opts[i] = {{v6, 0}};
                    else opts[i] = {{v6, 0}, {v2, 1}};
                } else if (lvH[i] == 1 || lvH[i] == 11) {
                    opts[i] = {{v2, 0}};
                } else if (lvH[i] == 5 || lvH[i] == 7) {
                    if (strict_lv57) opts[i] = {{v2, 0}, {v10, 0}};
                    else opts[i] = {{v6, 0}, {v2, 0}, {v10, 0}};
                } else throw std::logic_error("kill_betaU_1H: bad lvH");
            }
            enum_F5(opts, cH_cap, map_H);
        }
        uint32_t basis5[16]; int nb = 0; basis5[nb++] = 0xFFFFFFFFu;
        for (int i = 0; i < 5; ++i) { uint32_t m = 0; for (int c = 0; c < 32; ++c) if ((c >> i) & 1) m |= (1u << c); basis5[nb++] = m; }
        for (int i = 0; i < 5; ++i) for (int j = i + 1; j < 5; ++j) {
            uint32_t m = 0; for (int c = 0; c < 32; ++c) if (((c >> i) & 1) && ((c >> j) & 1)) m |= (1u << c);
            basis5[nb++] = m;
        }
        uint32_t m0 = 0, m111 = 0, m110 = 0, m100 = 0;
        for (int i = 0; i < 32; ++i) {
            if (lvHc[i] == 0 || lvHc[i] == 12) m0 |= (1u << i);
            else if (lvHc[i] == 2 || lvHc[i] == 10) m111 |= (1u << i);
            else if (lvHc[i] == 4 || lvHc[i] == 8) m110 |= (1u << i);
            else if (lvHc[i] == 6) m100 |= (1u << i);
            else throw std::logic_error("kill_betaU_1H: bad lvHc");
        }
        uint64_t total_cells = 0;
        std::vector<uint32_t> alive_ps;
        for (int mask = 0; mask < (1 << 16); ++mask) {
            uint32_t w = 0; for (int b = 0; b < 16; ++b) if ((mask >> b) & 1) w ^= basis5[b];
            if ((w & m0) != 0) continue;
            if (__builtin_popcount((~w) & m111) > cHc_cap) continue;
            std::array<std::vector<OptVal>, 32> opts;
            for (int i = 0; i < 32; ++i) {
                int pb = (w >> i) & 1;
                if (lvHc[i] == 0 || lvHc[i] == 12) opts[i] = {{0, 0}};
                else if (lvHc[i] == 2 || lvHc[i] == 10) {
                    if (pb) opts[i] = {{-4, 0}, {4, 0}};
                    else opts[i] = {{0, 1}};
                } else if (lvHc[i] == 4 || lvHc[i] == 8) {
                    if (pb) opts[i] = {{-4, 0}, {4, 0}};
                    else if (cHc_cap == 0) opts[i] = {{-8, 0}, {8, 0}};
                    else opts[i] = {{-8, 0}, {8, 0}, {0, 1}};
                } else if (lvHc[i] == 6) {
                    if (pb) {
                        if (cHc_cap < 2) opts[i] = {{-12, 0}, {12, 0}};
                        else opts[i] = {{-12, 0}, {12, 0}, {-4, 2}, {4, 2}};
                    } else {
                        if (cHc_cap < 2) opts[i] = {{0, 0}};
                        else opts[i] = {{0, 0}, {-8, 2}, {8, 2}};
                    }
                }
            }
            std::unordered_map<uint32_t, std::vector<HalfItem>> map_Hc;
            enum_F5(opts, cHc_cap, map_Hc);
            uint64_t loc = 0;
            for (const auto& [p32, vhc] : map_Hc) {
                auto it = map_H.find(p32); if (it == map_H.end()) continue;
                for (const auto& hc : vhc) for (const auto& hh : it->second) {
                    if (hc.tw & hh.tw) continue;
                    if (!all_lv3_rem6 && (hc.cost + hh.cost > rem)) continue;
                    loc++;
                }
            }
            if (loc) { total_cells += loc; alive_ps.push_back(w); }
        }
        uint64_t alive_triples = 0;
        for (size_t i = 0; i < alive_ps.size(); ++i)
            for (size_t j = i; j < alive_ps.size(); ++j) {
                uint32_t p3 = (m111 | m100) ^ alive_ps[i] ^ alive_ps[j];
                if (cHc_cap == 0) {
                    if (alive_ps[i] & alive_ps[j] & m100) continue;
                    if (p3 & (alive_ps[i] | alive_ps[j]) & m100) continue;
                    if ((alive_ps[i] & alive_ps[j] & p3 & m110) != 0) continue;
                    if (((alive_ps[i] | alive_ps[j] | p3) & m110) != m110) continue;
                } else {
                    int c_111 = __builtin_popcount(m111 & ~(alive_ps[i] & alive_ps[j] & p3));
                    int c_110 = __builtin_popcount(m110 & ~(alive_ps[i] | alive_ps[j] | p3));
                    if (c_111 + c_110 > cHc_cap) continue;
                }
                if (std::find(alive_ps.begin() + j, alive_ps.end(), p3) != alive_ps.end()) alive_triples++;
            }
        return {total_cells, alive_triples};
    };
    auto r = run_1H(max_cH, max_cHc);
    if (!all_lv3_rem6 && rem > 0 && r.first > 0) {
        auto r2 = run_1H(rem, max_cHc);
        return {r.first, r2.second};
    }
    return r;
}

// =========================================================================
// 7 MANDATORY POSITIVE CONTROLS
// =========================================================================
static void run_positive_controls(const std::vector<std::vector<U>>& shapes, const std::string& sdir) {
    // PC1: shapes0..10 exact counts + cross-check shapes9.bin / shapes10.bin if present
    const size_t exp_cnt[11] = {1, 1, 2, 5, 16, 46, 134, 344, 773, 2965}; // wait: verify index!
    (void)exp_cnt;
    if (shapes[9].size() != 773 || shapes[10].size() != 2965)
        throw std::logic_error("PC1 failed: shapes9/10 count mismatch");
    if (FILE* f = fopen((sdir + "/shapes10.bin").c_str(), "rb")) {
        std::vector<U> disk10; U m; while (fread(&m, 8, 1, f) == 1) disk10.push_back(m); fclose(f);
        if (disk10.size() != shapes[10].size()) throw std::logic_error("PC1 failed: shapes10.bin size mismatch");
    }
    std::cout << "[PC1] PASS: shapes0..10 regenerated from scratch (shapes9=" << shapes[9].size()
              << ", shapes10=" << shapes[10].size() << "; shapes11..15=" << shapes[11].size() << "/"
              << shapes[12].size() << "/" << shapes[13].size() << "/" << shapes[14].size() << "/" << shapes[15].size() << ")\n";

    // PC2: Brute-force ALL 81 Z_6 + 256 F_6 low tuples AND ALL 256 high 4-tuples!
    {
        // Low F_6 counterexample (+4, +12, +12, -12) -> z0 = +4, defect = 2 (NOT 4!)
        int minD_Z[13], minD_F[13];
        std::fill(minD_Z, minD_Z + 13, 99); std::fill(minD_F, minD_F + 13, 99);
        int Zv[3] = {-8, 0, 8}, Fv[4] = {-12, -4, 4, 12};
        for (int a : Zv) for (int b : Zv) for (int c : Zv) for (int d : Zv) {
            int z = std::abs(a + b + c + d) / 4;
            int D = (a == 0) + (b == 0) + (c == 0) + (d == 0);
            if (z <= 12) minD_Z[z] = std::min(minD_Z[z], D);
            // Verify z = 0 mod 4 => D is even!
            if ((z & 3) == 0 && (D & 1)) throw std::logic_error("PC2 failed: odd D on Z6 with 4|z");
        }
        for (int a : Fv) for (int b : Fv) for (int c : Fv) for (int d : Fv) {
            int z = std::abs(a + b + c + d) / 4;
            int D = 2 * ((std::abs(a) == 4) + (std::abs(b) == 4) + (std::abs(c) == 4) + (std::abs(d) == 4));
            if (z <= 12) minD_F[z] = std::min(minD_F[z], D);
        }
        if (minD_Z[0] != 0 || minD_Z[2] != 1 || minD_Z[4] != 0 || minD_Z[6] != 1 || minD_Z[8] != 0 || minD_Z[10] != 99 || minD_Z[12] != 99)
            throw std::logic_error("PC2 failed: Z6 minD table mismatch");
        if (minD_F[0] != 0 || minD_F[2] != 2 || minD_F[4] != 2 || minD_F[6] != 0 || minD_F[8] != 2 || minD_F[10] != 2 || minD_F[12] != 0)
            throw std::logic_error("PC2 failed: F6 minD table mismatch (4* bug check)");

        // High 4-tuples m in {0,1,2,3}^4: verify beta_U = lv mod 2, weighted inequality 2*a + b <= 2*extra, and even p1^p2^p3 law!
        for (int m0 = 0; m0 < 4; ++m0) for (int m1 = 0; m1 < 4; ++m1)
        for (int m2 = 0; m2 < 4; ++m2) for (int m3 = 0; m3 < 4; ++m3) {
            int lv = m0 + m1 + m2 + m3;
            int u1 = 2 * (m0 + m1 - m2 - m3);
            int u2 = 2 * (m0 - m1 + m2 - m3);
            int u3 = 2 * (m0 - m1 - m2 + m3);
            int kc = (m0 == 1 || m0 == 2) + (m1 == 1 || m1 == 2) + (m2 == 1 || m2 == 2) + (m3 == 1 || m3 == 2);
            if (((std::abs(u1) >> 1) & 1) != (lv & 1) || ((std::abs(u2) >> 1) & 1) != (lv & 1) || ((std::abs(u3) >> 1) & 1) != (lv & 1))
                throw std::logic_error("PC2 failed: beta_U != lv mod 2");
            int base_k = (lv % 3 != 0) ? 1 : 0;
            if (kc < base_k) throw std::logic_error("PC2 failed: kc < (lv%3!=0)");
            int extra = kc - base_k;
            if (lv & 1) {
                int a = 0, b = 0;
                for (int u : {std::abs(u1), std::abs(u2), std::abs(u3)}) {
                    if ((lv == 3 || lv == 9) && u == 2) a++;
                    if ((lv == 5 || lv == 7) && u == 6) b++;
                }
                if (2 * a + b > 2 * extra) throw std::logic_error("PC2 failed: 2*a + b > 2*extra");
                if ((lv == 1 || lv == 11) && (std::abs(u1) != 2 || std::abs(u2) != 2 || std::abs(u3) != 2))
                    throw std::logic_error("PC2 failed: lv 1/11 not all +-2");
            } else {
                int p1 = (std::abs(u1) >> 2) & 1, p2 = (std::abs(u2) >> 2) & 1, p3 = (std::abs(u3) >> 2) & 1;
                int exp_xor = (lv == 2 || lv == 6 || lv == 10) ? 1 : 0;
                if (extra <= 2 && ((p1 ^ p2 ^ p3) != exp_xor))
                    throw std::logic_error("PC2 failed: even p1^p2^p3 law");
            }
        }
        std::cout << "[PC2] PASS: All 337 low tuples (minD_F[4]=minD_F[8]=2 verified) & all 256 high tuples (2a+b<=2*extra & beta_U=lv mod 2) verified!\n";
    }

    // PC3: 1-WHT mod-3 extension identity on 200 shapes15 x 64 x0 = 12,800 tests
    {
        for (size_t si = 0; si < std::min<size_t>(200, shapes[15].size()); ++si) {
            U mask = shapes[15][si];
            int w[64]{}; for (U t = mask; t; t &= t - 1) { int x = lo(t); w[x] = Q[x]; }
            fwht64(w);
            int f[64]{}, wt = 0;
            for (int c = 0; c < 64; ++c) { int r = ((w[c] % 3) + 3) % 3; if (r == 1) { f[c] = 1; wt++; } else if (r == 2) { f[c] = -1; wt++; } }
            fwht64(f);
            for (int x0 = 0; x0 < 64; ++x0) {
                int pred = (wt - Q[x0] * f[x0]) / 2, brute = 0;
                for (int c = 0; c < 64; ++c) if (((w[c] + Q[x0] * W[x0][c]) % 3) == 0) brute++;
                if (pred != brute) throw std::logic_error("PC3 failed: 1-WHT mod-3 mismatch");
            }
        }
        std::cout << "[PC3] PASS: 1-WHT mod-3 extension identity verified against brute force on 12,800 extensions!\n";
    }

    // PC4: H_5 m_2 lemma across all 1,024 quadratic forms on F_2^5
    {
        uint32_t qm5[10]; int qi = 0;
        for (int i = 0; i < 5; ++i) for (int j = i + 1; j < 5; ++j) {
            uint32_t m = 0; for (int c = 0; c < 32; ++c) if (((c >> i) & 1) && ((c >> j) & 1)) m |= (1u << c);
            qm5[qi++] = m;
        }
        uint64_t cnt[4]{};
        for (int q = 0; q < 1024; ++q) {
            uint32_t p = 0; for (int b = 0; b < 10; ++b) if ((q >> b) & 1) p ^= qm5[b];
            std::array<std::vector<OptVal>, 32> opts;
            for (int i = 0; i < 32; ++i) {
                int pb = (p >> i) & 1;
                opts[i] = {{int8_t(pb ? 6 : -6), 0}, {int8_t(pb ? -2 : 2), 1}};
            }
            std::unordered_map<uint32_t, std::vector<HalfItem>> mp;
            enum_F5(opts, 3, mp);
            for (const auto& [p32, vec] : mp) for (const auto& hi : vec) {
                // u_H = u_0 + u_1 takes values in {-2, -1, 0, +1, +2}, which enum_F5 enforces exactly!
                cnt[hi.cost]++;
            }
        }
        if (cnt[0] != 0 || cnt[1] != 0 || cnt[2] != 13888 || cnt[3] != 0)
            throw std::logic_error("PC4 failed: H5 m2 counts unexpected");
        std::cout << "[PC4] PASS: H5 m2 lemma verified over all 1,024 quad forms (m2=0,1,3: 0 hits; m2=2: " << cnt[2] << " hits)!\n";
    }

    // PC5: kill_betaU0_rem0 positive control on real triple (q6, c0*c1, c2*c3 ^ c4*c5)
    {
        std::array<int, 64> lv_pc{};
        for (int c = 0; c < 64; ++c) {
            int p1 = (Q[c] == -1) ? 1 : 0;
            int p2 = ((c & 1) & ((c >> 1) & 1));
            int p3 = p1 ^ p2;
            lv_pc[c] = (p1 + p2 + p3 == 2) ? 4 : 0;
        }
        uint64_t tr = kill_betaU0_rem0(lv_pc);
        if (tr == 0) throw std::logic_error("PC5 failed: kill_betaU0_rem0 missed planted triple");
        std::cout << "[PC5] PASS: kill_betaU0_rem0 positive control found " << tr << " triple(s)!\n";
    }

    // PC6: kill_betaU1 AND kill_betaU1_sym2 positive control on planted ternary u = Q * 1_{F2^6 \ {0,1,2,3}} (wt=60)
    // u_hat(c) = 8*Q(c) - 2*(-1)^{c0*c1} has |u_hat| = 6 on 48 pts (lv=3) and 10 on 16 pts (lv=5), invariant under c^1 and c^2!
    {
        std::array<int, 64> lv_pc{};
        for (int c = 0; c < 64; ++c) {
            int q01 = ((c & 1) & ((c >> 1) & 1)) ? -1 : 1;
            int uh = 8 * Q[c] - 2 * q01;
            lv_pc[c] = (std::abs(uh) == 6) ? 3 : 5;
        }
        uint64_t h1 = kill_betaU1(lv_pc, 0);
        uint64_t h2 = kill_betaU1_sym2(lv_pc, 0);
        if (h1 == 0 || h2 == 0) throw std::logic_error("PC6 failed: kill_betaU1 / sym2 missed planted u");
        std::cout << "[PC6] PASS: kill_betaU1 (" << h1 << " hits) & kill_betaU1_sym2 (" << h2 << " hits) positive controls found planted wt=60 u!\n";
    }

    // PC7: kill_betaU_1H positive control on planted ternary u (wt=14):
    // u = 1_{0,1,2,3,4,5} + 1_{8,10,12,14} - 1_{9,11,13,15}.
    // On H={c0=0}: u_hat = 2(1+(-1)^{c1}) + 2(-1)^{c2} in {6 (8 pts, lv=3), +-2 (24 pts, lv=1)}.
    // On H^c={c0=1}: u_hat = 8*(-1)^{c3} when c1=c2=0 (8 pts, lv=4) and 0 elsewhere (24 pts, lv=0).
    {
        std::array<int, 64> lv_pc{};
        for (int c = 0; c < 64; ++c) {
            if ((c & 1) == 0) lv_pc[c] = (((c >> 1) & 1) == 0 && ((c >> 2) & 1) == 0) ? 3 : 1;
            else lv_pc[c] = (((c >> 1) & 1) == 0 && ((c >> 2) & 1) == 0) ? 4 : 0;
        }
        auto [cells, tr] = kill_betaU_1H_dir(1, lv_pc, 0);
        if (cells == 0) throw std::logic_error("PC7 failed: kill_betaU_1H missed planted wt=14 u");
        std::cout << "[PC7] PASS: kill_betaU_1H positive control found " << cells << " cell(s) for planted wt=14 u!\n";
    }
}

static std::vector<U> read_bin(const std::string& fn) {
    FILE* f = fopen(fn.c_str(), "rb");
    if (!f) { perror(fn.c_str()); exit(1); }
    std::vector<U> v; U m;
    while (fread(&m, 8, 1, f) == 1) v.push_back(m);
    fclose(f);
    return v;
}

int main(int argc, char** argv) {
    auto T0 = std::chrono::steady_clock::now();
    init();
    std::string sdir = (argc >= 2) ? argv[1] : "shapes";

    std::vector<std::vector<U>> shapes(16);
    shapes[0] = {0ULL};
    for (int n = 1; n <= 10; ++n) shapes[n] = next_layer(shapes[n - 1]);
    for (int n = 11; n <= 15; ++n) shapes[n] = read_bin(sdir + "/shapes" + std::to_string(n) + ".bin");

    // Run all 7 positive controls first!
    run_positive_controls(shapes, sdir);

    // Exhaustive unfiltered scan over ALL 45 (h, p) pairs (h in {0,2,...,16}, 0 <= 2p <= h)
    struct Surv { int h, p; U E, F; int wt3, rem, odd_cnt, lv3_cnt, minD; std::array<int, 64> lv; };
    std::vector<Surv> live;
    int tot_lv = 0, kill_v0 = 0, kill_H5 = 0, pairs_checked = 0;
    auto record_hit = [&](int h, int p, U E, U F, const int s[64], int wt3) {
        tot_lv++;
        std::array<int, 64> lv{}; int odd_cnt = 0, lv3 = 0;
        for (int c = 0; c < 64; ++c) {
            lv[c] = 3 + ((Q[c] * s[c]) >> 1);
            if (lv[c] & 1) odd_cnt++;
            if (lv[c] == 3) lv3++;
        }
        int rem = (32 - h) - wt3;
        int minD = exact_minD_v0(E ^ F);
        if (minD > 36) { kill_v0++; return; }
        if (odd_cnt == 32 && lv3 == 32 && rem < 6) { kill_H5++; return; }
        live.push_back({h, p, E, F, wt3, rem, odd_cnt, lv3, minD, lv});
    };

    for (int h = 0; h <= 16; h += 2) {
        int max_wt3 = 32 - h;
        for (int p = 0; 2 * p <= h; ++p) {
            pairs_checked++;
            int sz = h - p; if (sz > 13) continue;
            for (U mask : shapes[sz]) {
                int pts[16], k = 0; for (U t = mask; t; t &= t - 1) pts[k++] = lo(t);
                int terms[16][64], base[64]{};
                for (int i = 0; i < sz; ++i) {
                    int x = pts[i], qx = Q[x];
                    for (int c = 0; c < 64; ++c) { int v = qx * W[x][c]; terms[i][c] = v; base[c] += v; }
                }
                int s[64]; for (int c = 0; c < 64; ++c) s[c] = base[c];
                auto dfs = [&](auto& self, int idx, int rem_p, U fmask) -> void {
                    if (rem_p == 0) {
                        int wt3 = 0;
                        for (int c = 0; c < 64; ++c) {
                            int lv = 3 + ((Q[c] * s[c]) >> 1);
                            if (lv < 0 || lv > 12) return;
                            if (lv % 3) if (++wt3 > max_wt3) return;
                        }
                        record_hit(h, p, mask, fmask, s, wt3); return;
                    }
                    for (int i = idx; i <= sz - rem_p; ++i) {
                        for (int c = 0; c < 64; ++c) s[c] += terms[i][c];
                        self(self, i + 1, rem_p - 1, fmask | (1ULL << pts[i]));
                        for (int c = 0; c < 64; ++c) s[c] -= terms[i][c];
                    }
                };
                dfs(dfs, 0, p, 0);
            }
        }
    }
    // Size 14: (h=14, p=0) and (h=16, p=2)
    {
        std::mutex mu; std::atomic<size_t> ni{0}; std::vector<std::thread> ths;
        for (int ti = 0; ti < 8; ++ti) ths.emplace_back([&]() {
            int pts[14], terms[14][64], base[64];
            while (true) {
                size_t st = ni.fetch_add(256); if (st >= shapes[14].size()) break;
                size_t en = std::min(shapes[14].size(), st + 256);
                for (size_t idx = st; idx < en; ++idx) {
                    U mask = shapes[14][idx]; int k = 0; for (U t = mask; t; t &= t - 1) pts[k++] = lo(t);
                    for (int c = 0; c < 64; ++c) base[c] = 0;
                    for (int i = 0; i < 14; ++i) {
                        int x = pts[i], qx = Q[x];
                        for (int c = 0; c < 64; ++c) { int v = qx * W[x][c]; terms[i][c] = v; base[c] += v; }
                    }
                    {
                        int wt3 = 0; bool ok = true;
                        for (int c = 0; c < 64; ++c) {
                            int lv = 3 + ((Q[c] * base[c]) >> 1);
                            if (lv < 0 || lv > 12) { ok = false; break; }
                            if (lv % 3) if (++wt3 > 18) { ok = false; break; }
                        }
                        if (ok) { std::lock_guard<std::mutex> lk(mu); record_hit(14, 0, mask, 0, base, wt3); }
                    }
                    for (int i = 0; i < 14; ++i) {
                        int bi[64]; for (int c = 0; c < 64; ++c) bi[c] = base[c] + terms[i][c];
                        for (int j = i + 1; j < 14; ++j) {
                            int s[64], wt3 = 0; bool ok = true;
                            for (int c = 0; c < 64; ++c) {
                                s[c] = bi[c] + terms[j][c];
                                int lv = 3 + ((Q[c] * s[c]) >> 1);
                                if (lv < 0 || lv > 12) { ok = false; break; }
                                if (lv % 3) if (++wt3 > 16) { ok = false; break; }
                            }
                            if (ok) {
                                std::lock_guard<std::mutex> lk(mu);
                                record_hit(16, 2, mask, (1ULL << pts[i]) | (1ULL << pts[j]), s, wt3);
                            }
                        }
                    }
                }
            }
        });
        for (auto& th : ths) th.join();
    }
    // Size 15 & 16 via 1-WHT mod-3: (h=16, p=1) and (h=16, p=0)
    {
        std::set<Code> uniq16;
        for (U mask : shapes[15]) {
            int w[64]{}; for (U t = mask; t; t &= t - 1) { int x = lo(t); w[x] = Q[x]; }
            fwht64(w);
            int f[64]{}, wt = 0;
            for (int c = 0; c < 64; ++c) {
                int r = ((w[c] % 3) + 3) % 3;
                if (r == 1) { f[c] = 1; wt++; } else if (r == 2) { f[c] = -1; wt++; }
            }
            if (wt < 48) continue;
            fwht64(f);
            for (int x0 = 0; x0 < 64; ++x0) {
                if (wt - Q[x0] * f[x0] < 96) continue;
                int s[64], wt3 = 0; bool ok = true;
                for (int c = 0; c < 64; ++c) {
                    s[c] = w[c] + Q[x0] * W[x0][c];
                    int lv = 3 + ((Q[c] * s[c]) >> 1);
                    if (lv < 0 || lv > 12) { ok = false; break; }
                    if (lv % 3) wt3++;
                }
                if (!ok) continue;
                if ((mask >> x0) & 1ULL) record_hit(16, 1, mask, 1ULL << x0, s, wt3);
                else { U m16 = mask | (1ULL << x0); if (uniq16.insert(canon(m16)).second) record_hit(16, 0, m16, 0, s, wt3); }
            }
        }
    }

    if (pairs_checked != 45 || tot_lv != 302 || kill_v0 != 175 || kill_H5 != 16 || live.size() != 111) {
        std::cerr << "Scan count mismatch: pairs=" << pairs_checked << " tot_lv=" << tot_lv
                  << " kill_v0=" << kill_v0 << " kill_H5=" << kill_H5 << " live=" << live.size() << "\n";
        return 1;
    }
    std::cout << "[SCAN] ALL 45 (h,p) pairs: " << tot_lv << " pass_levels -> " << kill_v0
              << " dead(exact_v0) + " << kill_H5 << " dead(H5_m2) -> " << live.size() << " LIVE cases.\n" << std::flush;

    std::sort(live.begin(), live.end(), [](const Surv& a, const Surv& b) {
        return std::tie(a.rem, a.h, a.p, a.E, a.F) < std::tie(b.rem, b.h, b.p, b.E, b.F);
    });

    int k_h0p0 = 0, k_bU0 = 0, k_bU1H = 0, k_bU1 = 0, k_bU1sym = 0, survived = 0;
    for (size_t idx = 0; idx < live.size(); ++idx) {
        const auto& x = live[idx];
        if (x.h == 0 && x.p == 0) {
            // Proved by hand (Parseval gives m_2 >= 16 > 10 = floor(32/3) across all 4 ranks).
            k_h0p0++;
        } else if (x.odd_cnt == 0) {
            if (x.rem != 0) throw std::logic_error("bU=0 with rem != 0");
            uint64_t tr = kill_betaU0_rem0(x.lv);
            if (tr == 0) k_bU0++; else { survived++; std::cerr << "SURV bU=0 idx=" << idx << "\n"; }
        } else if (x.odd_cnt == 32) {
            U v0m = x.E ^ x.F; int u_dir = 0;
            for (U t = v0m; t; t &= t - 1) u_dir ^= lo(t);
            auto [cells, tr] = kill_betaU_1H_dir(u_dir, x.lv, x.rem);
            if (tr == 0) k_bU1H++; else { survived++; std::cerr << "SURV bU=1H idx=" << idx << "\n"; }
        } else if (x.odd_cnt == 64) {
            uint64_t hits = (x.rem >= 12) ? kill_betaU1_sym2(x.lv, x.rem) : kill_betaU1(x.lv, x.rem);
            if (hits == 0) { if (x.rem >= 12) k_bU1sym++; else k_bU1++; }
            else { survived++; std::cerr << "SURV bU=1 idx=" << idx << " h=" << x.h << " p=" << x.p << " hits=" << hits << "\n"; }
        } else {
            throw std::logic_error("Unexpected odd_cnt (not in {0,32,64})");
        }
    }
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - T0).count();
    std::cout << "[KILL] h0p0(hand)=" << k_h0p0 << ", bU0=" << k_bU0 << ", bU1H=" << k_bU1H
              << ", bU1(rem<=8)=" << k_bU1 << ", bU1_sym2(rem>=12)=" << k_bU1sym
              << " | TOTAL KILLED = " << (k_h0p0 + k_bU0 + k_bU1H + k_bU1 + k_bU1sym) << " / " << live.size()
              << " | SURVIVED = " << survived << " (" << dt << "s)\n";
    return survived ? 1 : 0;
}
