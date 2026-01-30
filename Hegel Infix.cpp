#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#ifdef HEGEL_WASM
#include <emscripten/emscripten.h>
#endif

using namespace std;
// ==================== Global Parameters (Mutable via hegel_configure)
// ====================
static int MAX_NEST = 4;
static int TARGET = 24;
static int MAX_USE_SQRT = 2;
static int MAX_USE_FACT = 2;
static int MAX_USE_LG = 1;
static int MAX_USE_LB = 2;
static int MAX_USE_LOG = 1;
static bool NO_NEGATIVE_INTERMEDIATE = true;
static bool ONLY_ARITHMETIC = false;

// ==================== Constants ====================
static const long long MAX_ABS_VAL = 1LL << 50;
static const int MAX_FACT_ARG = 100;
static const int MAX_EXP_SUM =
    100; // Increased significantly for factorial chains
static const int SIMPLIFY_STEPS = 50;
static const bool SKIP_EQUIV_DURING_SEARCH = false;
static const int MAX_EQUIV_KEY_CACHE = 20000;
static const bool MEMO_IN_FIND_ALL = true;
static const bool NORMAL_FIND_FIRST_ONLY = false;

enum FuncIdx { F_SQRT, F_FACT, F_LG, F_LB, F_LOG, F_CNT };

static int MAX_USE[F_CNT] = {2, 2, 1, 2, 1};

static void update_max_use_array() {
  MAX_USE[F_SQRT] = MAX_USE_SQRT;
  MAX_USE[F_FACT] = MAX_USE_FACT;
  MAX_USE[F_LG] = MAX_USE_LG;
  MAX_USE[F_LB] = MAX_USE_LB;
  MAX_USE[F_LOG] = MAX_USE_LOG;
}

struct Num {
  int sign = 0;
  vector<pair<int, int>> pe;
  bool has_ll = false;
  long long ll = 0;
};

struct Node {
  Num num;
  vector<string> expr;                // RPN tokens
  array<unsigned char, F_CNT> used{}; // 每种函数使用次数
  int depth = 0;                      // 最大嵌套深度
};

// --------------- 工具：RPN 拼接 ---------------
static inline vector<string>
merge_expr(const vector<string> &a, const vector<string> &b, const string &op) {
  vector<string> res;
  res.reserve(a.size() + b.size() + 1);
  res.insert(res.end(), a.begin(), a.end());
  res.insert(res.end(), b.begin(), b.end());
  res.push_back(op);
  return res;
}
static inline vector<string> apply_unary_expr(const vector<string> &a,
                                              const string &op) {
  vector<string> res = a;
  res.push_back(op);
  return res;
}

// ---- Expression normalization for + / - / * / / duplicates ----
static bool is_unary_token(const string &t) {
  return (t == "sqrt" || t == "!" || t == "lg" || t == "lb");
}
static bool is_binary_token(const string &t) {
  return (t == "+" || t == "-" || t == "*" || t == "/" || t == "log");
}

struct ExprNodeTmp {
  string op;
  int left = -1;
  int right = -1;
  int child = -1;
  string tok;
  bool is_leaf = false;
  bool is_unary = false;
  bool is_binary = false;
};
static int build_expr_tree(const vector<string> &expr,
                           vector<ExprNodeTmp> &nodes) {
  vector<int> st;
  st.reserve(expr.size());
  for (const string &t : expr) {
    if (is_binary_token(t)) {
      if (st.size() < 2)
        return -1;
      int b = st.back();
      st.pop_back();
      int a = st.back();
      st.pop_back();
      ExprNodeTmp n;
      n.op = t;
      n.left = a;
      n.right = b;
      n.is_binary = true;
      nodes.push_back(std::move(n));
      st.push_back((int)nodes.size() - 1);
    } else if (is_unary_token(t)) {
      if (st.empty())
        return -1;
      int a = st.back();
      st.pop_back();
      ExprNodeTmp n;
      n.op = t;
      n.child = a;
      n.is_unary = true;
      nodes.push_back(std::move(n));
      st.push_back((int)nodes.size() - 1);
    } else {
      ExprNodeTmp n;
      n.tok = t;
      n.is_leaf = true;
      nodes.push_back(std::move(n));
      st.push_back((int)nodes.size() - 1);
    }
  }
  if (st.size() != 1)
    return -1;
  return st.back();
}

// Simplification cache for equivalence (bounded by SIMPLIFY_STEPS)
static bool try_parse_ll(const string &t, long long &out) {
  try {
    size_t pos = 0;
    long long v = stoll(t, &pos);
    if (pos != t.size())
      return false;
    out = v;
    return true;
  } catch (...) {
    return false;
  }
}
static bool safe_add_ll(long long a, long long b, long long &out) {
  __int128 r = (__int128)a + (__int128)b;
  if (r < LLONG_MIN || r > LLONG_MAX)
    return false;
  out = (long long)r;
  return true;
}
static bool safe_sub_ll(long long a, long long b, long long &out) {
  __int128 r = (__int128)a - (__int128)b;
  if (r < LLONG_MIN || r > LLONG_MAX)
    return false;
  out = (long long)r;
  return true;
}
static bool safe_mul_ll(long long a, long long b, long long &out) {
  __int128 r = (__int128)a * (__int128)b;
  if (r < LLONG_MIN || r > LLONG_MAX)
    return false;
  out = (long long)r;
  return true;
}
static bool safe_fact_ll(long long n, long long &out) {
  if (n < 0 || n > MAX_FACT_ARG)
    return false;
  __int128 r = 1;
  for (long long i = 2; i <= n; i++) {
    r *= i;
    if (r > LLONG_MAX)
      return false;
  }
  out = (long long)r;
  return true;
}
static bool safe_lg_ll(long long v, long long &out) {
  if (v <= 0)
    return false;
  long long k = 0;
  while (v % 10 == 0) {
    v /= 10;
    k++;
  }
  if (v != 1)
    return false;
  out = k;
  return true;
}
static bool safe_lb_ll(long long v, long long &out) {
  if (v <= 0)
    return false;
  if ((v & (v - 1)) != 0)
    return false;
  long long k = 0;
  while (v > 1) {
    v >>= 1;
    k++;
  }
  out = k;
  return true;
}
static bool safe_log_ll(long long a, long long b, long long &out) {
  if (a < 2 || b <= 0)
    return false;
  if (b == 1) {
    out = 0;
    return true;
  }
  long long k = 0;
  __int128 cur = 1;
  while (cur < b) {
    cur *= a;
    k++;
    if (cur > LLONG_MAX)
      return false;
  }
  if (cur != b)
    return false;
  out = k;
  return true;
}
// Forward declarations
static bool is_perfect_square_ll(long long x, long long &r);
static void print_infix(const vector<string> &expr, const string &prefix);

struct SimplifyCache {
  const vector<ExprNodeTmp> *nodes = nullptr;
  vector<char> vis;
  vector<char> ok;
  vector<long long> val;
  vector<int> steps;
};
static thread_local SimplifyCache g_simpl;
static unordered_map<string, string> equiv_key_cache;

static void init_simplify_cache(const vector<ExprNodeTmp> &nodes) {
  g_simpl.nodes = &nodes;
  g_simpl.vis.assign(nodes.size(), 0);
  g_simpl.ok.assign(nodes.size(), 0);
  g_simpl.val.assign(nodes.size(), 0);
  g_simpl.steps.assign(nodes.size(), 0);
}
static bool simplify_dfs(int idx, long long &out_val, int &out_steps) {
  if (SIMPLIFY_STEPS <= 0 || g_simpl.nodes == nullptr)
    return false;
  if (g_simpl.vis[idx]) {
    if (g_simpl.ok[idx]) {
      out_val = g_simpl.val[idx];
      out_steps = g_simpl.steps[idx];
      return true;
    }
    return false;
  }
  g_simpl.vis[idx] = 1;
  const ExprNodeTmp &n = (*g_simpl.nodes)[idx];
  long long v = 0;
  int steps = 0;
  bool ok = false;
  if (n.is_leaf) {
    if (try_parse_ll(n.tok, v)) {
      ok = true;
      steps = 0;
    }
  } else if (n.is_unary) {
    long long cv;
    int cs;
    if (simplify_dfs(n.child, cv, cs)) {
      if (cs + 1 <= SIMPLIFY_STEPS) {
        if (n.op == "sqrt") {
          long long r;
          if (is_perfect_square_ll(cv, r)) {
            v = r;
            ok = true;
            steps = cs + 1;
          }
        } else if (n.op == "!") {
          if (safe_fact_ll(cv, v)) {
            ok = true;
            steps = cs + 1;
          }
        } else if (n.op == "lg") {
          if (safe_lg_ll(cv, v)) {
            ok = true;
            steps = cs + 1;
          }
        } else if (n.op == "lb") {
          if (safe_lb_ll(cv, v)) {
            ok = true;
            steps = cs + 1;
          }
        }
      }
    }
  } else if (n.is_binary) {
    long long lv, rv;
    int ls, rs;
    if (simplify_dfs(n.left, lv, ls) && simplify_dfs(n.right, rv, rs)) {
      if (ls + rs + 1 <= SIMPLIFY_STEPS) {
        if (n.op == "+") {
          if (safe_add_ll(lv, rv, v)) {
            ok = true;
            steps = ls + rs + 1;
          }
        } else if (n.op == "-") {
          if (safe_sub_ll(lv, rv, v)) {
            ok = true;
            steps = ls + rs + 1;
          }
        } else if (n.op == "*") {
          if (safe_mul_ll(lv, rv, v)) {
            ok = true;
            steps = ls + rs + 1;
          }
        } else if (n.op == "/") {
          if (rv != 0 && (lv % rv == 0)) {
            v = lv / rv;
            ok = true;
            steps = ls + rs + 1;
          }
        } else if (n.op == "log") {
          if (safe_log_ll(lv, rv, v)) {
            ok = true;
            steps = ls + rs + 1;
          }
        }
      }
    }
  }
  if (ok) {
    g_simpl.ok[idx] = 1;
    g_simpl.val[idx] = v;
    g_simpl.steps[idx] = steps;
    out_val = v;
    out_steps = steps;
    return true;
  }
  return false;
}
static bool try_simplify_const(const vector<ExprNodeTmp> &nodes, int idx,
                               long long &out_val) {
  if (!SKIP_EQUIV_DURING_SEARCH)
    return false;
  if (SIMPLIFY_STEPS <= 0)
    return false;
  if (g_simpl.nodes != &nodes)
    init_simplify_cache(nodes);
  int steps = 0;
  return simplify_dfs(idx, out_val, steps);
}

static string normalized_expr_key_from_nodes(const vector<ExprNodeTmp> &nodes,
                                             int idx);

static void collect_mul_factors(const vector<ExprNodeTmp> &nodes, int idx,
                                int sign, vector<string> &factors) {
  const ExprNodeTmp &n = nodes[idx];
  if (n.is_binary && (n.op == "*" || n.op == "/")) {
    collect_mul_factors(nodes, n.left, sign, factors);
    int s2 = (n.op == "*") ? sign : -sign;
    collect_mul_factors(nodes, n.right, s2, factors);
    return;
  }
  string key = normalized_expr_key_from_nodes(nodes, idx);
  factors.push_back(string(sign > 0 ? "*" : "/") + key);
}
static string normalized_mul_key(const vector<ExprNodeTmp> &nodes, int idx,
                                 bool &direct_key) {
  vector<string> factors;
  factors.reserve(8);
  collect_mul_factors(nodes, idx, 1, factors);
  // drop neutral factor 1 and /1
  vector<string> filtered;
  filtered.reserve(factors.size());
  for (const string &f : factors) {
    if (f.size() >= 2) {
      string key = f.substr(1);
      if (key == "1")
        continue;
    }
    filtered.push_back(f);
  }
  if (filtered.empty()) {
    direct_key = true;
    return "1";
  }
  if (filtered.size() == 1 && filtered[0][0] == '*') {
    direct_key = true;
    return filtered[0].substr(1);
  }
  sort(filtered.begin(), filtered.end());
  string out;
  for (size_t i = 0; i < filtered.size(); i++) {
    if (i)
      out.push_back('|');
    out += filtered[i];
  }
  direct_key = false;
  return out;
}
static void collect_add_terms(const vector<ExprNodeTmp> &nodes, int idx,
                              int sign, vector<string> &terms) {
  const ExprNodeTmp &n = nodes[idx];
  if (n.is_binary && (n.op == "+" || n.op == "-")) {
    collect_add_terms(nodes, n.left, sign, terms);
    int s2 = (n.op == "+") ? sign : -sign;
    collect_add_terms(nodes, n.right, s2, terms);
    return;
  }
  string key = normalized_expr_key_from_nodes(nodes, idx);
  terms.push_back(string(sign > 0 ? "+" : "-") + key);
}
static string normalized_add_key_from_nodes(const vector<ExprNodeTmp> &nodes,
                                            int idx, bool &direct_key) {
  vector<string> terms;
  terms.reserve(8);
  collect_add_terms(nodes, idx, 1, terms);
  // drop neutral term 0 and -0
  vector<string> filtered;
  filtered.reserve(terms.size());
  for (const string &t : terms) {
    if (t.size() >= 2) {
      string key = t.substr(1);
      if (key == "0")
        continue;
    }
    filtered.push_back(t);
  }
  if (filtered.empty()) {
    direct_key = true;
    return "0";
  }

  vector<string> a = filtered;
  vector<string> b;
  b.reserve(filtered.size());
  for (const string &t : filtered) {
    if (!t.empty()) {
      char s = t[0];
      string key = t.substr(1);
      b.push_back(string(1, (s == '+') ? '-' : '+') + key);
    }
  }
  sort(a.begin(), a.end());
  sort(b.begin(), b.end());
  string sa, sb;
  for (size_t i = 0; i < a.size(); i++) {
    if (i)
      sa.push_back('|');
    sa += a[i];
  }
  for (size_t i = 0; i < b.size(); i++) {
    if (i)
      sb.push_back('|');
    sb += b[i];
  }
  bool neg = false;
  vector<string> *use = &a;
  if (!sb.empty() && sb < sa) {
    neg = true;
    use = &b;
  }

  if (use->size() == 1) {
    string t = (*use)[0];
    if (t.size() >= 2 && t[0] == '+') {
      direct_key = true;
      return neg ? (string("-") + t.substr(1)) : t.substr(1);
    }
    direct_key = true;
    return neg ? t.substr(1) : t;
  }

  string out;
  for (size_t i = 0; i < use->size(); i++) {
    if (i)
      out.push_back('|');
    out += (*use)[i];
  }
  direct_key = false;
  return neg ? (string("-") + out) : out;
}
static string normalized_expr_key_from_nodes(const vector<ExprNodeTmp> &nodes,
                                             int idx) {
  long long sv;
  if (try_simplify_const(nodes, idx, sv))
    return to_string(sv);
  const ExprNodeTmp &n = nodes[idx];
  if (n.is_leaf)
    return n.tok;
  if (n.is_unary)
    return n.op + "(" + normalized_expr_key_from_nodes(nodes, n.child) + ")";
  if (n.is_binary) {
    if (n.op == "+" || n.op == "-") {
      bool direct_key = false;
      string ak = normalized_add_key_from_nodes(nodes, idx, direct_key);
      if (direct_key)
        return ak;
      if (!ak.empty() && ak[0] == '-')
        return string("-") + string("A:") + ak.substr(1);
      return string("A:") + ak;
    }
    if (n.op == "*" || n.op == "/") {
      bool direct_key = false;
      string mk = normalized_mul_key(nodes, idx, direct_key);
      if (direct_key)
        return mk;
      return string("M:") + mk;
    }
    return n.op + "(" + normalized_expr_key_from_nodes(nodes, n.left) + "," +
           normalized_expr_key_from_nodes(nodes, n.right) + ")";
  }
  return "";
}
static string normalized_expr_key(const vector<string> &expr) {
  string rpn_key;
  rpn_key.reserve(expr.size() * 3);
  for (size_t i = 0; i < expr.size(); i++) {
    if (i)
      rpn_key.push_back(' ');
    rpn_key += expr[i];
  }
  auto it = equiv_key_cache.find(rpn_key);
  if (it != equiv_key_cache.end())
    return it->second;

  vector<ExprNodeTmp> nodes;
  nodes.reserve(expr.size());
  int root = build_expr_tree(expr, nodes);
  if (root < 0)
    return "";
  init_simplify_cache(nodes);
  string key = normalized_expr_key_from_nodes(nodes, root);

  if (equiv_key_cache.size() > MAX_EQUIV_KEY_CACHE)
    equiv_key_cache.clear();
  equiv_key_cache.emplace(std::move(rpn_key), key);
  return key;
}
static int count_plus_tokens(const vector<string> &expr) {
  int c = 0;
  for (const string &t : expr)
    if (t == "+")
      c++;
  return c;
}

static int count_leaf_tokens(const vector<string> &expr) {
  int c = 0;
  for (const string &t : expr) {
    if (!is_binary_token(t) && !is_unary_token(t))
      c++;
  }
  return c;
}

// --------------- 质因数分解（仅对 |v|<=MAX_ABS_VAL 范围做） ---------------
static vector<pair<int, int>> factorize_small(long long x) {
  vector<pair<int, int>> res;
  if (x <= 1)
    return res;
  for (long long p = 2; p * p <= x; ++p) {
    if (x % p == 0) {
      int e = 0;
      while (x % p == 0) {
        x /= p;
        ++e;
      }
      res.push_back({(int)p, e});
    }
  }
  if (x > 1)
    res.push_back({(int)x, 1});
  return res;
}

static int exp_sum(const vector<pair<int, int>> &pe) {
  int s = 0;
  for (auto &kv : pe)
    s += kv.second;
  return s;
}

// factors: out = a + b (指数相加)
static vector<pair<int, int>> factors_add(const vector<pair<int, int>> &a,
                                          const vector<pair<int, int>> &b) {
  vector<pair<int, int>> out;
  out.reserve(a.size() + b.size());
  size_t i = 0, j = 0;
  while (i < a.size() || j < b.size()) {
    if (j == b.size() || (i < a.size() && a[i].first < b[j].first)) {
      out.push_back(a[i++]);
    } else if (i == a.size() || b[j].first < a[i].first) {
      out.push_back(b[j++]);
    } else {
      int p = a[i].first;
      int e = a[i].second + b[j].second;
      if (e)
        out.push_back({p, e});
      ++i;
      ++j;
    }
  }
  return out;
}

// factors: out = a - b (指数相减)，要求 a 可被 b 整除（每个指数>=）
static bool factors_subtract(const vector<pair<int, int>> &a,
                             const vector<pair<int, int>> &b,
                             vector<pair<int, int>> &out) {
  out.clear();
  out.reserve(a.size());
  size_t i = 0, j = 0;
  while (i < a.size() || j < b.size()) {
    if (j == b.size() || (i < a.size() && a[i].first < b[j].first)) {
      out.push_back(a[i++]);
    } else if (i == a.size() || b[j].first < a[i].first) {
      return false; // b 有 a 没有的质因子
    } else {
      int p = a[i].first;
      int ea = a[i].second, eb = b[j].second;
      if (ea < eb)
        return false;
      int e = ea - eb;
      if (e)
        out.push_back({p, e});
      ++i;
      ++j;
    }
  }
  return true;
}

// 尝试把质因数指数还原为 |v|（只在 <=MAX_ABS_VAL 时成功；全程不用浮点）
static bool try_eval_small_abs(const vector<pair<int, int>> &pe,
                               long long &out_abs) {
  __int128 prod = 1;
  for (auto &kv : pe) {
    int p = kv.first;
    int e = kv.second;
    for (int i = 0; i < e; i++) {
      prod *= p;
      if (prod > MAX_ABS_VAL)
        return false;
    }
  }
  out_abs = (long long)prod;
  return true;
}

static void normalize_num(Num &n) {
  if (n.sign == 0) {
    n.has_ll = true;
    n.ll = 0;
    n.pe.clear();
    return;
  }
  long long abs_v;
  if (try_eval_small_abs(n.pe, abs_v)) {
    n.has_ll = true;
    n.ll = (n.sign < 0 ? -abs_v : abs_v);
  } else {
    n.has_ll = false;
    n.ll = 0;
  }
}

static Num make_num_from_ll_pruned(long long v, bool &ok) {
  ok = false;
  Num n;
  if (NO_NEGATIVE_INTERMEDIATE && v < 0)
    return n; // forbid negative intermediates
  if (v == 0) {
    n.sign = 0;
    n.pe.clear();
    n.has_ll = true;
    n.ll = 0;
    ok = true;
    return n;
  }
  long long av = llabs(v);
  if (av > MAX_ABS_VAL)
    return n; // 剪枝：普通整数太大直接丢
  n.sign = (v < 0 ? -1 : 1);
  n.pe = factorize_small(av);
  n.has_ll = true;
  n.ll = v;
  ok = true;
  return n;
}

// --------------- 完全平方判定（整数） ---------------
static bool is_perfect_square_ll(long long x, long long &r) {
  if (x < 0)
    return false;
  long long lo = 0, hi = min<long long>(x, 3037000499LL);
  while (lo <= hi) {
    long long mid = lo + (hi - lo) / 2;
    __int128 sq = (__int128)mid * mid;
    if (sq == x) {
      r = mid;
      return true;
    }
    if (sq < x)
      lo = mid + 1;
    else
      hi = mid - 1;
  }
  return false;
}

// --------------- 阶乘质因子（Legendre） ---------------
static vector<int> primes_up_to(int n) {
  vector<int> ps;
  if (n < 2)
    return ps;
  vector<bool> isPrime(n + 1, true);
  isPrime[0] = isPrime[1] = false;
  for (int i = 2; i * i <= n; i++)
    if (isPrime[i]) {
      for (int j = i * i; j <= n; j += i)
        isPrime[j] = false;
    }
  for (int i = 2; i <= n; i++)
    if (isPrime[i])
      ps.push_back(i);
  return ps;
}

static vector<pair<int, int>> factorial_factors(int n) {
  vector<pair<int, int>> res;
  static vector<int> cached_primes = primes_up_to(MAX_FACT_ARG);
  for (int p : cached_primes) {
    if (p > n)
      break;
    int e = 0, t = n;
    while (t) {
      t /= p;
      e += t;
    }
    if (e)
      res.push_back({p, e});
  }
  return res;
}

// --------------- 函数使用次数合并检查 ---------------
static bool merge_used(const Node &A, const Node &B,
                       array<unsigned char, F_CNT> &out) {
  for (int i = 0; i < F_CNT; i++) {
    int s = (int)A.used[i] + (int)B.used[i];
    if (s > MAX_USE[i])
      return false;
    out[i] = (unsigned char)s;
  }
  return true;
}
static bool inc_used(const Node &A, FuncIdx f,
                     array<unsigned char, F_CNT> &out) {
  out = A.used;
  if ((int)out[f] + 1 > MAX_USE[f])
    return false;
  out[f] = (unsigned char)(out[f] + 1);
  return true;
}

// --------------- 目标判断（不依赖大整数） ---------------
static vector<pair<int, int>> TARGET_FACTORS = factorize_small(TARGET);

static bool is_target_24(const Num &n) {
  if (n.sign <= 0)
    return false;
  if (n.has_ll)
    return n.ll == TARGET;
  return n.pe == TARGET_FACTORS;
}

// ======================= RPN -> 中缀（高性能：栈式一次扫描）
// =======================
struct InfixItem {
  string s;
  int prec; // 1:+- 2:*/ 3:func/! 4:atom
  char bop; // 若顶层是二元运算符：+ - * /，否则为 0
};

static inline int prec_of_binop(char op) {
  if (op == '+' || op == '-')
    return 1;
  if (op == '*' || op == '/')
    return 2;
  return 0;
}
static inline bool need_paren_left(char op, const InfixItem &a) {
  int p = prec_of_binop(op);
  if (a.prec < p)
    return true;
  // 同优先级下左结合：左侧一般不需要括号
  return false;
}
static inline bool need_paren_right(char op, const InfixItem &b) {
  int p = prec_of_binop(op);
  if (op == '+') {
    if (b.prec < p)
      return true;
    // a + (b - c) 必须加括号
    if (b.prec == p && b.bop == '-')
      return true;
    return false;
  }
  if (op == '-') {
    // a - (b +/- c) 必须加括号
    if (b.prec <= p)
      return true;
    return false;
  }
  if (op == '*') {
    if (b.prec < p)
      return true;
    // a * (b / c) 必须加括号
    if (b.prec == p && b.bop == '/')
      return true;
    return false;
  }
  if (op == '/') {
    // a / (b * c) 和 a / (b / c) 都必须加括号
    if (b.prec <= p)
      return true;
    return false;
  }
  return false;
}

static string rpn_to_infix(const vector<string> &expr) {
  vector<InfixItem> st;
  st.reserve(expr.size());

  for (const string &t : expr) {
    if (t == "+" || t == "-" || t == "*" || t == "/") {
      if (st.size() < 2) {
        // fallback
        string raw;
        for (size_t i = 0; i < expr.size(); i++) {
          if (i)
            raw.push_back(' ');
          raw += expr[i];
        }
        return raw;
      }
      InfixItem b = std::move(st.back());
      st.pop_back();
      InfixItem a = std::move(st.back());
      st.pop_back();
      char op = t[0];

      bool lp = need_paren_left(op, a);
      bool rp = need_paren_right(op, b);

      string as = lp ? ("(" + a.s + ")") : a.s;
      string bs = rp ? ("(" + b.s + ")") : b.s;

      InfixItem c;
      c.prec = prec_of_binop(op);
      c.bop = op;
      c.s.reserve(as.size() + bs.size() + 3);
      c.s = as;
      c.s.push_back(' ');
      c.s.push_back(op);
      c.s.push_back(' ');
      c.s += bs;
      st.push_back(std::move(c));
    } else if (t == "log") {
      if (st.size() < 2) {
        string raw;
        for (size_t i = 0; i < expr.size(); i++) {
          if (i)
            raw.push_back(' ');
          raw += expr[i];
        }
        return raw;
      }
      InfixItem b = std::move(st.back());
      st.pop_back();
      InfixItem a = std::move(st.back());
      st.pop_back();
      InfixItem c;
      c.prec = 3;
      c.bop = 0;
      c.s = "log(" + a.s + ", " + b.s + ")";
      st.push_back(std::move(c));
    } else if (t == "sqrt" || t == "lg" || t == "lb") {
      if (st.empty()) {
        string raw;
        for (size_t i = 0; i < expr.size(); i++) {
          if (i)
            raw.push_back(' ');
          raw += expr[i];
        }
        return raw;
      }
      InfixItem a = std::move(st.back());
      st.pop_back();
      InfixItem c;
      c.prec = 3;
      c.bop = 0;
      c.s = t + "(" + a.s + ")";
      st.push_back(std::move(c));
    } else if (t == "!") {
      if (st.empty()) {
        string raw;
        for (size_t i = 0; i < expr.size(); i++) {
          if (i)
            raw.push_back(' ');
          raw += expr[i];
        }
        return raw;
      }
      InfixItem a = std::move(st.back());
      st.pop_back();
      bool need = (a.prec < 3); // (a+b)! 这类需要括号
      InfixItem c;
      c.prec = 3;
      c.bop = 0;
      c.s = (need ? ("(" + a.s + ")") : a.s) + "!";
      st.push_back(std::move(c));
    } else {
      // number / atom
      InfixItem a;
      a.s = t;
      a.prec = 4;
      a.bop = 0;
      st.push_back(std::move(a));
    }
  }

  if (st.size() != 1) {
    string raw;
    for (size_t i = 0; i < expr.size(); i++) {
      if (i)
        raw.push_back(' ');
      raw += expr[i];
    }
    return raw;
  }
  return st.back().s;
}

// --------------- Solver ---------------
struct Solver {
  bool find_first = false;
  bool found = false;
  int expected_leaf_count = 0;
  vector<string> first_expr;
  bool immediate_print = false;
  string immediate_prefix;

  unordered_map<string, vector<string>> best_exprs;
  unordered_map<string, int> best_plus;

  unordered_set<string> memo; // 记忆化用

  // node key（用于记忆化）
  static string num_key(const Num &n) {
    if (n.sign == 0)
      return "0";
    string s;
    s.push_back(n.sign < 0 ? '-' : '+');
    for (auto &kv : n.pe) {
      s += to_string(kv.first);
      s.push_back('^');
      s += to_string(kv.second);
      s.push_back(',');
    }
    return s;
  }
  static string node_key(const Node &nd) {
    string s = num_key(nd.num);
    s.push_back('|');
    for (int i = 0; i < F_CNT; i++) {
      s += to_string((int)nd.used[i]);
      s.push_back(',');
    }
    s += "D";
    s += to_string(nd.depth);
    return s;
  }
  static string state_key(const vector<Node> &cur) {
    vector<string> ks;
    ks.reserve(cur.size());
    for (auto &nd : cur)
      ks.push_back(node_key(nd));
    sort(ks.begin(), ks.end());
    string s;
    for (size_t i = 0; i < ks.size(); i++) {
      if (i)
        s.push_back(';');
      s += ks[i];
    }
    return s;
  }

  void add_answer(const vector<string> &expr) {
    string key = normalized_expr_key(expr);
    if (key.empty())
      return;
    key += "#C" + to_string(count_leaf_tokens(expr));
    int plus_cnt = count_plus_tokens(expr);
    auto it = best_plus.find(key);
    if (it == best_plus.end() || plus_cnt > it->second) {
      bool is_better = (it != best_plus.end());
      best_plus[key] = plus_cnt;
      best_exprs[key] = expr;
      if (immediate_print) {
        if (!is_better) {
          print_infix(expr, immediate_prefix);
        } else if (!SKIP_EQUIV_DURING_SEARCH) {
          print_infix(expr, immediate_prefix);
        }
      }
    }
  }

  // ========== 一元函数尝试 ==========
  bool try_sqrt(const Node &A, Node &out) {
    if (A.depth + 1 > MAX_NEST)
      return false;
    array<unsigned char, F_CNT> used2;
    if (!inc_used(A, F_SQRT, used2))
      return false;
    if (!A.num.has_ll)
      return false;
    long long v = A.num.ll;
    if (v == 0 || v == 1)
      return false;
    long long r;
    if (!is_perfect_square_ll(v, r))
      return false;

    bool ok;
    Num n = make_num_from_ll_pruned(r, ok);
    if (!ok)
      return false;

    out.num = std::move(n);
    out.expr = apply_unary_expr(A.expr, "sqrt");
    out.used = used2;
    out.depth = A.depth + 1;
    return true;
  }

  bool try_fact(const Node &A, Node &out) {
    if (A.depth + 1 > MAX_NEST)
      return false;
    array<unsigned char, F_CNT> used2;
    if (!inc_used(A, F_FACT, used2))
      return false;
    if (!A.num.has_ll)
      return false;
    long long v = A.num.ll;
    if (v < 0 || v > MAX_FACT_ARG)
      return false;

    if (v == 0 || v == 1 || v == 2)
      return false;
    if (v == 4)
      return false;

    Num n;
    if (v == 0 || v == 1) {
      bool ok;
      n = make_num_from_ll_pruned(1, ok);
      if (!ok)
        return false;
    } else {
      n.sign = 1;
      n.pe = factorial_factors((int)v);
      normalize_num(n);
      // Allow large factorials even if they overflow long long
      if (!n.has_ll &&
          exp_sum(n.pe) > MAX_EXP_SUM * 2) // Double limit just in case
        return false;
    }

    out.num = std::move(n);
    out.expr = apply_unary_expr(A.expr, "!");
    out.used = used2;
    out.depth = A.depth + 1;
    return true;
  }

  bool try_lg(const Node &A, Node &out) {
    if (A.depth + 1 > MAX_NEST)
      return false;
    array<unsigned char, F_CNT> used2;
    if (!inc_used(A, F_LG, used2))
      return false;
    if (!A.num.has_ll)
      return false;
    long long v = A.num.ll;
    if (v <= 0 || v == 1)
      return false;
    if (v == 4 || v == 16)
      return false;

    long long x = v;
    long long k = 0;
    while (x % 10 == 0) {
      x /= 10;
      ++k;
    }
    if (x != 1)
      return false;

    bool ok;
    Num n = make_num_from_ll_pruned(k, ok);
    if (!ok)
      return false;

    out.num = std::move(n);
    out.expr = apply_unary_expr(A.expr, "lg");
    out.used = used2;
    out.depth = A.depth + 1;
    return true;
  }

  bool try_lb(const Node &A, Node &out) {
    if (A.depth + 1 > MAX_NEST)
      return false;
    array<unsigned char, F_CNT> used2;
    if (!inc_used(A, F_LB, used2))
      return false;
    if (!A.num.has_ll)
      return false;
    long long v = A.num.ll;
    if (v <= 0 || v == 1)
      return false;
    if (v == 4 || v == 16)
      return false;

    if ((v & (v - 1)) != 0)
      return false;
    long long k = 0;
    while (v > 1) {
      v >>= 1;
      ++k;
    }

    bool ok;
    Num n = make_num_from_ll_pruned(k, ok);
    if (!ok)
      return false;

    out.num = std::move(n);
    out.expr = apply_unary_expr(A.expr, "lb");
    out.used = used2;
    out.depth = A.depth + 1;
    return true;
  }

  // ========== 二元 log_a(b) 尝试 ==========
  bool try_logab(const Node &A, const Node &B, Node &out) {
    int newDepth = max(A.depth, B.depth) + 1;
    if (newDepth > MAX_NEST)
      return false;

    array<unsigned char, F_CNT> used2;
    if (!merge_used(A, B, used2))
      return false;
    if ((int)used2[F_LOG] + 1 > MAX_USE[F_LOG])
      return false;
    used2[F_LOG] = (unsigned char)(used2[F_LOG] + 1);

    if (!A.num.has_ll || !B.num.has_ll)
      return false;
    long long a = A.num.ll;
    long long b = B.num.ll;
    if (a < 2)
      return false;
    if (b <= 0 || b == 1)
      return false;

    long long k = 0;
    __int128 cur = 1;
    while (cur < b) {
      cur *= a;
      ++k;
      if (cur > MAX_ABS_VAL)
        break;
    }
    if (cur != b)
      return false;

    bool ok;
    Num n = make_num_from_ll_pruned(k, ok);
    if (!ok)
      return false;

    out.num = std::move(n);
    out.expr = merge_expr(A.expr, B.expr, "log"); // a b log
    out.used = used2;
    out.depth = newDepth;
    return true;
  }

  // ========== 二元四则 ==========
  bool try_add(const Node &A, const Node &B, Node &out) {
    array<unsigned char, F_CNT> used2;
    if (!merge_used(A, B, used2))
      return false;
    int d = max(A.depth, B.depth);

    if (!A.num.has_ll || !B.num.has_ll)
      return false;
    __int128 r = (__int128)A.num.ll + (__int128)B.num.ll;
    if (r > MAX_ABS_VAL || r < -MAX_ABS_VAL)
      return false;

    bool ok;
    Num n = make_num_from_ll_pruned((long long)r, ok);
    if (!ok)
      return false;

    out.num = std::move(n);
    out.expr = merge_expr(A.expr, B.expr, "+");
    out.used = used2;
    out.depth = d;
    return true;
  }

  bool try_sub(const Node &A, const Node &B, Node &out) {
    array<unsigned char, F_CNT> used2;
    if (!merge_used(A, B, used2))
      return false;
    int d = max(A.depth, B.depth);

    if (!A.num.has_ll || !B.num.has_ll)
      return false;
    __int128 r = (__int128)A.num.ll - (__int128)B.num.ll;
    if (r > MAX_ABS_VAL || r < -MAX_ABS_VAL)
      return false;

    bool ok;
    Num n = make_num_from_ll_pruned((long long)r, ok);
    if (!ok)
      return false;

    out.num = std::move(n);
    out.expr = merge_expr(A.expr, B.expr, "-");
    out.used = used2;
    out.depth = d;
    return true;
  }

  bool try_mul(const Node &A, const Node &B, Node &out) {
    array<unsigned char, F_CNT> used2;
    if (!merge_used(A, B, used2))
      return false;
    int d = max(A.depth, B.depth);

    Num n;
    if (A.num.sign == 0 || B.num.sign == 0) {
      n.sign = 0;
      n.pe.clear();
      n.has_ll = true;
      n.ll = 0;
    } else {
      n.sign = A.num.sign * B.num.sign;
      n.pe = factors_add(A.num.pe, B.num.pe);
      if (exp_sum(n.pe) > MAX_EXP_SUM)
        return false;
      normalize_num(n);
    }

    out.num = std::move(n);
    out.expr = merge_expr(A.expr, B.expr, "*");
    out.used = used2;
    out.depth = d;
    return true;
  }

  bool try_div(const Node &A, const Node &B, Node &out) {
    array<unsigned char, F_CNT> used2;
    if (!merge_used(A, B, used2))
      return false;
    int d = max(A.depth, B.depth);

    if (B.num.sign == 0)
      return false;
    if (B.num.has_ll && B.num.ll == 1)
      return false;

    Num n;
    if (A.num.sign == 0) {
      n.sign = 0;
      n.pe.clear();
      n.has_ll = true;
      n.ll = 0;
    } else {
      vector<pair<int, int>> pe2;
      if (!factors_subtract(A.num.pe, B.num.pe, pe2))
        return false; // 必须整除
      n.sign = A.num.sign * B.num.sign;
      n.pe = std::move(pe2);
      normalize_num(n);
      if (!n.has_ll && exp_sum(n.pe) > MAX_EXP_SUM)
        return false;
    }

    out.num = std::move(n);
    out.expr = merge_expr(A.expr, B.expr, "/");
    out.used = used2;
    out.depth = d;
    return true;
  }

  // ========== DFS ==========
  void dfs(vector<Node> cur) {
    if (found && find_first)
      return;

    if (SKIP_EQUIV_DURING_SEARCH && cur.size() > 1) {
      unordered_map<string, pair<int, Node>> best_by_key;
      unordered_map<string, int> key_counts;
      vector<Node> filtered;
      filtered.reserve(cur.size());
      for (auto &nd : cur) {
        string k = normalized_expr_key(nd.expr);
        if (k.empty()) {
          filtered.push_back(nd);
          continue;
        }
        k += "#C" + to_string(count_leaf_tokens(nd.expr));
        key_counts[k]++;
        int plus_cnt = count_plus_tokens(nd.expr);
        auto it = best_by_key.find(k);
        if (it == best_by_key.end() || plus_cnt > it->second.first) {
          best_by_key[k] = {plus_cnt, nd};
        }
      }
      for (auto &kv : best_by_key) {
        int cnt = key_counts[kv.first];
        for (int i = 0; i < cnt; i++) {
          filtered.push_back(kv.second.second);
        }
      }
      if (filtered.size() < cur.size()) {
        cur.swap(filtered);
      }
    }

    if (cur.size() == 1) {
      if (is_target_24(cur[0].num) &&
          count_leaf_tokens(cur[0].expr) == expected_leaf_count) {
        if (find_first) {
          found = true;
          first_expr = cur[0].expr;
          if (immediate_print) {
            print_infix(cur[0].expr, immediate_prefix);
          }
        } else {
          found = true;
          add_answer(cur[0].expr);
        }
      }
      return;
    }

    if (find_first || MEMO_IN_FIND_ALL) {
      string key = state_key(cur);
      if (memo.find(key) != memo.end())
        return;
      memo.insert(std::move(key));
    }

    // 一元函数：对每个元素尝试
    for (size_t i = 0; i < cur.size(); i++) {
      Node out;
      if (!ONLY_ARITHMETIC) {
        if (try_sqrt(cur[i], out)) {
          Node bak = cur[i];
          cur[i] = std::move(out);
          dfs(cur);
          cur[i] = std::move(bak);
          if (found && find_first)
            return;
        }
        if (try_fact(cur[i], out)) {
          Node bak = cur[i];
          cur[i] = std::move(out);
          dfs(cur);
          cur[i] = std::move(bak);
          if (found && find_first)
            return;
        }
        if (try_lg(cur[i], out)) {
          Node bak = cur[i];
          cur[i] = std::move(out);
          dfs(cur);
          cur[i] = std::move(bak);
          if (found && find_first)
            return;
        }
        if (try_lb(cur[i], out)) {
          Node bak = cur[i];
          cur[i] = std::move(out);
          dfs(cur);
          cur[i] = std::move(bak);
          if (found && find_first)
            return;
        }
      }
    }

    // 二元合并
    int n = (int)cur.size();
    unordered_set<string> pair_seen;
    for (int i = 0; i < n - 1; i++)
      for (int j = i + 1; j < n; j++) {
        Node A = cur[i], B = cur[j];
        string keyA = node_key(A);
        string keyB = node_key(B);
        string pair_key = keyA;
        pair_key.push_back('|');
        pair_key += keyB;
        if (!pair_seen.insert(pair_key).second)
          continue;

        vector<Node> rest;
        rest.reserve(n - 1);
        for (int k = 0; k < n; k++)
          if (k != i && k != j)
            rest.push_back(cur[k]);

        auto push_and_dfs = [&](Node &&C) {
          rest.push_back(std::move(C));
          dfs(rest);
          rest.pop_back();
        };

        {
          Node C;
          if (try_add(A, B, C)) {
            push_and_dfs(std::move(C));
            if (found && find_first)
              return;
          }
        }
        {
          Node C;
          if (try_sub(A, B, C)) {
            push_and_dfs(std::move(C));
            if (found && find_first)
              return;
          }
          if (try_sub(B, A, C)) {
            push_and_dfs(std::move(C));
            if (found && find_first)
              return;
          }
        }
        {
          Node C;
          if (try_mul(A, B, C)) {
            push_and_dfs(std::move(C));
            if (found && find_first)
              return;
          }
        }
        {
          Node C;
          if (try_div(A, B, C)) {
            push_and_dfs(std::move(C));
            if (found && find_first)
              return;
          }
          if (try_div(B, A, C)) {
            push_and_dfs(std::move(C));
            if (found && find_first)
              return;
          }
        }
        {
          Node C;
          if (try_logab(A, B, C)) {
            push_and_dfs(std::move(C));
            if (found && find_first)
              return;
          }
          if (try_logab(B, A, C)) {
            push_and_dfs(std::move(C));
            if (found && find_first)
              return;
          }
        }
      }
  }

  // 输入数字 -> Node
  static vector<Node> parse_nodes_from_line(const string &line) {
    istringstream iss(line);
    vector<Node> res;
    long long x;
    while (iss >> x) {
      bool ok;
      Num n = make_num_from_ll_pruned(x, ok);
      if (!ok)
        continue;
      Node nd;
      nd.num = std::move(n);
      nd.expr = {to_string(x)};
      nd.used.fill(0);
      nd.depth = 0;
      res.push_back(std::move(nd));
    }
    return res;
  }

  // 求解接口
  bool solve_first(const vector<long long> &nums, vector<string> &out_expr) {
    found = false;
    first_expr.clear();
    memo.clear();
    immediate_print = true;
    immediate_prefix = ">>> ";
    expected_leaf_count = (int)nums.size();

    vector<Node> cur;
    cur.reserve(nums.size());
    for (long long x : nums) {
      bool ok;
      Num n = make_num_from_ll_pruned(x, ok);
      if (!ok)
        return false;
      Node nd;
      nd.num = std::move(n);
      nd.expr = {to_string(x)};
      nd.used.fill(0);
      nd.depth = 0;
      cur.push_back(std::move(nd));
    }

    find_first = true;
    dfs(cur);
    if (found)
      out_expr = first_expr;
    return found;
  }

  void solve_all_or_first_normal(const vector<Node> &input,
                                 bool findFirstOnly) {
    found = false;
    first_expr.clear();
    best_exprs.clear();
    best_plus.clear();
    memo.clear();
    immediate_print = !findFirstOnly;
    immediate_prefix.clear();
    expected_leaf_count = (int)input.size();

    vector<Node> cur = input;
    find_first = findFirstOnly;
    dfs(cur);

    if (find_first) {
      if (found && !immediate_print)
        add_answer(first_expr);
    }
  }
};

#ifdef HEGEL_WASM
static string g_wasm_output;
static int g_wasm_limit = 0;
static int g_wasm_count = 0;

static void wasm_reset_output(int limit) {
  g_wasm_output.clear();
  g_wasm_limit = limit;
  g_wasm_count = 0;
}

static void wasm_append_line(const string &line) {
  if (g_wasm_limit > 0 && g_wasm_count >= g_wasm_limit)
    return;
  g_wasm_output += line;
  g_wasm_output.push_back('\n');
  g_wasm_count++;
}
#endif

// 打印一条：中缀表达式 = TARGET
static void print_infix(const vector<string> &expr, const string &prefix) {
#ifdef HEGEL_WASM
  (void)prefix;
  wasm_append_line(rpn_to_infix(expr) + " = " + to_string(TARGET));
#else
  cout << prefix << rpn_to_infix(expr) << " = " << TARGET << "\n";
  cout << flush;
#endif
}

#ifdef HEGEL_WASM
extern "C" {
EMSCRIPTEN_KEEPALIVE const char *hegel_solve(const char *line, int limit) {
  static Solver solver;
  wasm_reset_output(limit);
  if (!line || !*line)
    return g_wasm_output.c_str();

  vector<Node> input = Solver::parse_nodes_from_line(string(line));
  if (input.empty())
    return g_wasm_output.c_str();

  if (NO_NEGATIVE_INTERMEDIATE) {
    for (auto &nd : input) {
      if (nd.num.has_ll && nd.num.ll < 0)
        return g_wasm_output.c_str();
    }
  }

  solver.solve_all_or_first_normal(input, false);
  return g_wasm_output.c_str();
}

EMSCRIPTEN_KEEPALIVE void hegel_configure(int target, int max_nest,
                                          int max_sqrt, int max_fact,
                                          int max_lg, int max_lb, int max_log,
                                          int no_neg, int only_math) {
  TARGET = target;
  MAX_NEST = max_nest;
  MAX_USE_SQRT = max_sqrt;
  MAX_USE_FACT = max_fact;
  MAX_USE_LG = max_lg;
  MAX_USE_LB = max_lb;
  MAX_USE_LOG = max_log;
  NO_NEGATIVE_INTERMEDIATE = (no_neg != 0);
  ONLY_ARITHMETIC = (only_math != 0);

  TARGET_FACTORS = factorize_small(TARGET);
  update_max_use_array();
}
}
#endif

// 解析模式命令：random / solution
static bool parse_mode_cmd(const string &line, bool &toRandom) {
  if (line == "random") {
    toRandom = true;
    return true;
  }
  if (line == "solution") {
    toRandom = false;
    return true;
  }
  return false;
}

#ifndef HEGEL_WASM
int main() {
  ios::sync_with_stdio(false);
  cin.tie(nullptr);

  Solver solver;
  bool randomMode = false;

  std::mt19937 rng((unsigned)chrono::high_resolution_clock::now()
                       .time_since_epoch()
                       .count());

  while (true) {
    if (!randomMode) {
      cout << "请输入数字（输入 random 进入随机模式）：";
    } else {
      cout << "输入模拟次数、数字个数、最小值、最大值（输入 solution "
              "返回解题模式）：";
    }
    cout << flush;

    string line;
    if (!getline(cin, line))
      break;
    if (line.empty())
      break;

    bool toRandom;
    if (parse_mode_cmd(line, toRandom)) {
      randomMode = toRandom;
      continue;
    }

    if (!randomMode) {
      vector<Node> input = Solver::parse_nodes_from_line(line);
      if (input.empty()) {
        cout << "??\n";
        continue;
      }
      if (NO_NEGATIVE_INTERMEDIATE) {
        bool has_neg = false;
        for (auto &nd : input) {
          if (nd.num.has_ll && nd.num.ll < 0) {
            has_neg = true;
            break;
          }
        }
        if (has_neg) {
          cout << "??\n";
          continue;
        }
      }

      solver.solve_all_or_first_normal(input, NORMAL_FIND_FIRST_ONLY);

      if (!solver.found) {
        cout << "无解\n";
      } else if (!solver.immediate_print) {
        for (auto &kv : solver.best_exprs)
          print_infix(kv.second);
      }
      continue;
    }

    // 随机模式
    int T, N, L, R;
    {
      istringstream iss(line);
      if (!(iss >> T >> N >> L >> R) || T <= 0 || N <= 0 || L > R) {
        cout << "输入格式错误\n";
        continue;
      }
    }

    uniform_int_distribution<int> dist(L, R);
    int okcnt = 0;

    for (int t = 0; t < T; t++) {
      vector<long long> nums;
      nums.reserve(N);
      for (int i = 0; i < N; i++)
        nums.push_back(dist(rng));

      // 打印本组数字
      for (int i = 0; i < N; i++) {
        cout << nums[i] << (i + 1 == N ? '\n' : ' ');
      }
      cout << flush;

      vector<string> expr;
      bool ok = solver.solve_first(nums, expr);
      if (ok) {
        okcnt++;
      } else {
        cout << ">>> 无解\n";
      }
    }

    // 概率：只用分数（不引入浮点）
    cout << "有解概率为" << okcnt << "/" << T << "=";
    if (okcnt == 0) {
      cout << 0 << "\n";
    } else if (okcnt == T) {
      cout << 1 << "\n";
    } else {
      cout << fixed << setprecision(2) << (float)okcnt / T << "\n";
    }
  }
  return 0;
}
#else
int main() { return 0; }
#endif
