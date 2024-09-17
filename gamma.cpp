#include <iostream>
#include <optional>
#include <set>
#include <unordered_set>
#include <vector>
#include <queue>
#include <algorithm>
#include <utility>
using namespace std;

/* Operations on packed strings */
typedef unsigned long long ull;
typedef pair<ull, ull> String;
struct hashFunction2 {
  size_t operator()(String const& x) const {
    return x.first ^ x.second;
  }
};
struct hashFunction {
  size_t operator()(pair<String, int> const& x) const {
    return x.first.first ^ x.first.second;
  }
};
inline char charAt(const String &s, int i) {
  if (i < 0) return 0;
  if (i < 21) return (s.first >> (3 * i)) & 7;
  else return (s.second >> (3 * (i - 21))) & 7;
}
inline void assign(String &s, int i, char ch) {
  if (i < 21) {
    s.first &= ~(7ULL << (3 * i));
    s.first += ((ull)(ch)) << (3 * i);
  } else {
    s.second &= ~(7ULL << (3 * (i - 21)));
    s.second += ((ull)(ch)) << (3 * (i - 21));
  }
}
inline string toString(const String &s, int len) {
  string ss;
  for (int i = 0; i < len; ++i) ss += 'a' + charAt(s, i) - 1;
  return ss;
}
inline String emptyString() {
  return make_pair(0ULL, 0ULL);
}
inline String pref(const String &s, int l) {
  String res = s;
  if (l <= 21) {
    res.second = 0;
    res.first &= (1ULL << (3 * l)) - 1;
  } else {
    res.second &= (1ULL << (3 * (l - 21))) - 1;
  }
  return res;
}
inline String reverse(const String &s, int len) {
  String t;
  for (int i = 0; i < len; ++i)
    assign(t, i, charAt(s, len - i - 1));
  return t;
}
inline int length(const String &s) {
  if (s.second) return 42 - (__builtin_clzll(s.second) - 1) / 3;
  if (s.first) return 21 - (__builtin_clzll(s.first) - 1) / 3;
  return 0;
}



int alph;


/* s-primitivity test */
inline vector<int> get_subsequence_cnt_on_left(String c, int c_size, String s, int n) {
  vector<int> res(n);
  int c_idx = 0;
  for (int i = 0; i < n; i++) {
    if (c_idx != c_size && charAt(c, c_idx) == charAt(s, i))
      c_idx++;
    res[i] = c_idx;
  }
  return res;
}
inline vector<int> get_subsequence_cnt_on_right(String c, int c_size, String s, int n) {
  String rc = reverse(c, c_size);
  String rs = reverse(s, n);
  vector<int> r_result = get_subsequence_cnt_on_left(rc, c_size, rs, n);
  reverse(r_result.begin(), r_result.end());
  return r_result;
}

inline vector<int> pref_sum(String s, int n, char a) {
  vector<int> res(n + 1);
  for(int i = 0; i < n; i++) {
    res[i + 1] = res[i];
    res[i + 1] += a == charAt(s, i);
  }
  return res;
}

inline bool has_any(const vector<int> & pref_sum, int l, int r) {
  l = max(0, l);
  r = min((int)pref_sum.size() - 2, r);
  if (l > r) return false;
  return pref_sum[r + 1] - pref_sum[l] > 0;
}

bool is_covering_subsequence(String c, int c_size, String s, int n) {
  int c_idx = 0;
  vector<int> left_subsequence_cnt = get_subsequence_cnt_on_left(c, c_size, s, n);
  vector<int> right_subsequence_cnt = get_subsequence_cnt_on_right(c, c_size, s, n);
  vector<vector<int>> pref_sums;
  for (char l = 1; l <= alph; l++)
    pref_sums.push_back(pref_sum(c, c_size, l));
  for (int i = 0; i < n; i++) {
    int c_idx = charAt(s, i) - 1;
    int l = i ? left_subsequence_cnt[i - 1] : 0;
    int r = i == n - 1 ? 0 : right_subsequence_cnt[i + 1];
    if (!has_any(pref_sums[c_idx], c_size - r - 1, l))
      return false;
  }
  return true;
}


unordered_set<String, hashFunction2> coverless;

char perm[300];
inline String minimal_perm(const String &s, int len) {
  String s1 = emptyString();
  for (char ch = 1; ch <= alph; ++ch) perm[ch] = 0;
  char curr = 1;
  for (int i = 0; i < len; ++i) {
    char ch = charAt(s, i);
    if (perm[ch] == 0) perm[ch] = curr++;
    assign(s1, i, perm[ch]);
  }
  return s1;
}

inline bool iscoverless(const String &s, int len) {
  return coverless.find(minimal_perm(s, len)) != coverless.end();
}

unordered_set<pair<String, int>, hashFunction> subseq, subseq2;

bool has_s_cover(String s, int len) {
  if (len <= 3) return false;
  s = reverse(s, len);
  if (!iscoverless(pref(s, len - 2), len - 2)) return true;

  subseq.clear();
  subseq.insert(make_pair(pref(s, 2), 2));
  for (int i = 3; i <= len; ++i) {
    subseq2.clear();
    char sim = charAt(s, i - 1);
    for (pair<String, int> subpair : subseq) {
      subseq2.insert(subpair);
      String sub = subpair.first;
      int l = subpair.second;
      if (charAt(sub, l - 1) != sim) {
        String sub1 = sub;
        assign(sub1, l, sim);
        String sub2 = reverse(sub1, l + 1);
        int len2 = min(len - 2, l + 1);
        if (!iscoverless(pref(sub2, len2), len2)) continue;
        subseq2.insert(make_pair(sub1, l + 1));
      }
    }
    subseq = subseq2;
    
    String pref_s = pref(s, i);
    for (pair<String, int> candpair : subseq) {
      String cand = candpair.first;
      int l = candpair.second;
      if (l < 2 || l == i) continue;
      if (charAt(cand, l - 2) != charAt(pref_s, i - 2) || charAt(cand, l - 1) != charAt(pref_s, i - 1))
        continue;
      if (is_covering_subsequence(cand, l, pref_s, i)) return true;
    }
  }
  return false;
}

inline char maxletter(const String &s, int len) {
  char ch = 1;
  for (int i = 0; i < len; ++i) ch = max(ch, charAt(s, i));
  return ch;
}

queue<pair<String, int> > fifo;

void BFS() {
  String a = emptyString();
  assign(a, 0, 1);
  fifo.push(make_pair(a, 1));
  int bestlen = 0;
  while (!fifo.empty()) {
    String s = fifo.front().first;
    int len = fifo.front().second;
    if (len > bestlen) {
      cout << "Length reached: " << len << '\n';
      bestlen = len;
    }
    fifo.pop();
    coverless.insert(s);

    char maxchar = min(maxletter(s, len) + 1, alph);
    for (char ch = 1; ch <= maxchar; ++ch) {
      if (charAt(s, len - 1) == ch) continue;
      String s1 = s;
      assign(s1, len, ch);
      if (has_s_cover(s1, len + 1)) continue;
      fifo.push(make_pair(s1, len + 1));
    }
  }
}

void writeLongest() {
  int maxlen = 0;
  for (String s : coverless)
    maxlen = max(maxlen, length(s));
  cout << "gamma(" << alph << ") = " << maxlen << '\n';
  cout << "s-primitive words S of length " << maxlen << " with first(S) = ";
  for (char ch = 'a'; ch < 'a' + alph; ++ch)
    cout << ch;
  cout << ":\n";
  for (String s : coverless)
    if (length(s) == maxlen)
      cout << toString(s, length(s)) << '\n';
}

int main() {
  cin >> alph;
  coverless.insert(emptyString());
  BFS();
  writeLongest();
  return 0;
}
