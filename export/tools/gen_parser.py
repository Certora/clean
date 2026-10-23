#!/usr/bin/env python3
"""Generate `export/CCLib/cparser/Parser.lean` from `cparser/Parser.vy`.

CompCert obtains `cparser/Parser.v` by running Menhir in its Rocq mode
(`menhir --coq`) on `cparser/Parser.vy`.  Menhir has no Lean back end, so this
script plays its role for the Lean port: it reads the same grammar file,
builds an LR(1) automaton (LR(0) item sets with LALR(1) lookaheads, which are
conflict-free for this grammar), computes the annotations that the MenhirLib
validators need (known stack symbols, possible past states, items with their
lookahead sets, nullable and first sets), and emits a Lean module that
instantiates the `CC.MenhirLib` classes.

Nothing produced here is trusted: as in CompCert, the generated automaton is
checked inside Lean by the safety and completeness validators of
`CCLib/MenhirLib` (`Parser.safe` and `Parser.complete`).

Usage (from the repository root):
    python3 export/tools/gen_parser.py cparser/Parser.vy export/CCLib/cparser/Parser.lean
"""

import re
import sys

# ---------------------------------------------------------------------------
# 1. Reading the `.vy` file
# ---------------------------------------------------------------------------


def strip_comments(text):
    """Remove `(* ... *)` (nested) and `/* ... */` comments outside actions."""
    out = []
    i = 0
    n = len(text)
    depth_brace = 0
    in_header = False
    while i < n:
        if text.startswith('%{', i) and depth_brace == 0:
            in_header = True
            out.append('%{')
            i += 2
            continue
        if in_header:
            if text.startswith('%}', i):
                in_header = False
                out.append('%}')
                i += 2
            else:
                out.append(text[i])
                i += 1
            continue
        c = text[i]
        if depth_brace == 0 and text.startswith('(*', i):
            d = 1
            i += 2
            while i < n and d > 0:
                if text.startswith('(*', i):
                    d += 1
                    i += 2
                elif text.startswith('*)', i):
                    d -= 1
                    i += 2
                else:
                    i += 1
            out.append(' ')
            continue
        if depth_brace == 0 and text.startswith('/*', i):
            j = text.index('*/', i + 2)
            i = j + 2
            out.append(' ')
            continue
        if c == '{':
            depth_brace += 1
        elif c == '}':
            depth_brace -= 1
        out.append(c)
        i += 1
    return ''.join(out)


def strip_type_comments(t):
    return re.sub(r'\(\*.*?\*\)', ' ', t)


class Grammar:
    def __init__(self):
        self.tokens = []          # list of terminal names, in order
        self.token_type = {}      # terminal -> Coq type string (or None)
        self.nt_type = {}         # nonterminal -> Coq type string
        self.start = None
        self.start_type = None
        self.rules = {}           # name -> (params, [alternatives])
        self.rule_order = []


def read_angle(text, i):
    """Read `<...>` starting at text[i] == '<'; return (content, next index)."""
    assert text[i] == '<'
    depth = 0
    j = i
    while True:
        if text[j] == '<':
            depth += 1
        elif text[j] == '>' and text[j - 1] != '-':
            depth -= 1
            if depth == 0:
                return text[i + 1:j], j + 1
        j += 1


def parse_vy(path):
    raw = open(path).read()
    # Comments inside %type<...> are removed with the others.
    text = strip_comments(raw)
    g = Grammar()
    decls, rules = text.split('%%', 1)
    # Remove header.
    decls = re.sub(r'%\{.*?%\}', '', decls, flags=re.S)
    i = 0
    n = len(decls)
    while i < n:
        if decls.startswith('%token', i) or decls.startswith('%type', i) or decls.startswith('%start', i):
            m = re.match(r'%(token|type|start)', decls[i:])
            kind = m.group(1)
            i += len(m.group(0))
            while decls[i].isspace():
                i += 1
            ty = None
            if decls[i] == '<':
                ty, i = read_angle(decls, i)
                ty = ' '.join(strip_type_comments(ty).split())
            j = decls.find('%', i)
            if j < 0:
                j = n
            names = re.findall(r'[A-Za-z_][A-Za-z_0-9]*(?:\([A-Za-z_0-9]*\))?', decls[i:j])
            for nm in names:
                if kind == 'token':
                    g.tokens.append(nm)
                    g.token_type[nm] = ty
                elif kind == 'type':
                    g.nt_type[nm] = ty
                else:
                    g.start = nm
                    g.start_type = ty
                    g.nt_type[nm] = ty
            i = j
        else:
            i += 1
    # Rules.
    pos = 0
    rule_re = re.compile(r'\s*([A-Za-z_][A-Za-z_0-9]*)(?:\(([A-Za-z_0-9]*)\))?\s*:')
    body_items = []
    # Tokenise the rules section.
    toks = []
    i = 0
    rs = rules
    n = len(rs)
    while i < n:
        c = rs[i]
        if c.isspace():
            i += 1
        elif c == '{':
            d = 0
            j = i
            while True:
                if rs[j] == '{':
                    d += 1
                elif rs[j] == '}':
                    d -= 1
                    if d == 0:
                        break
                j += 1
            toks.append(('ACTION', rs[i + 1:j].strip()))
            i = j + 1
        elif c in '|:=':
            toks.append((c, c))
            i += 1
        elif c.isalpha() or c == '_':
            m = re.match(r'[A-Za-z_][A-Za-z_0-9]*(?:\([A-Za-z_0-9]*\))?', rs[i:])
            toks.append(('ID', m.group(0)))
            i += len(m.group(0))
        else:
            raise ValueError('unexpected char %r at %d' % (c, i))
    # Group into rules: ID ':' alternatives ...
    k = 0
    while k < len(toks):
        assert toks[k][0] == 'ID' and toks[k + 1][0] == ':', toks[k:k + 3]
        head = toks[k][1]
        k += 2
        m = re.match(r'([A-Za-z_0-9]+)(?:\(([A-Za-z_0-9]*)\))?$', head)
        name, param = m.group(1), m.group(2)
        alts = []
        pending = []  # alternatives waiting for an action
        cur = None
        while k < len(toks):
            t = toks[k]
            if t[0] == 'ID' and k + 1 < len(toks) and toks[k + 1][0] == ':':
                break
            if t[0] == '|':
                if cur is not None:
                    pending.append(cur)
                cur = []
                k += 1
            elif t[0] == 'ID':
                if cur is None:
                    cur = []
                if k + 1 < len(toks) and toks[k + 1][0] == '=':
                    cur.append((t[1], toks[k + 2][1]))
                    k += 3
                else:
                    cur.append((None, t[1]))
                    k += 1
            elif t[0] == 'ACTION':
                if cur is None:
                    cur = []
                pending.append(cur)
                for p in pending:
                    alts.append((p, t[1]))
                pending = []
                cur = None
                k += 1
            else:
                raise ValueError(t)
        assert not pending and cur is None, (name, pending, cur)
        g.rules[name] = (param, alts)
        g.rule_order.append(name)
    return g


# ---------------------------------------------------------------------------
# 2. Expansion of parameterised non-terminals
# ---------------------------------------------------------------------------


def mangle(sym):
    m = re.match(r'([A-Za-z_0-9]+)\(([A-Za-z_0-9]+)\)$', sym)
    if m:
        return '%s_%s_' % (m.group(1), m.group(2))
    return sym


def expand(g):
    """Return (nonterminals in order, productions) after expansion.

    A production is (lhs, [(binder or None, symbol)], action)."""
    prods = []
    nts = []
    done = set()
    types = {}
    for nm, ty in g.nt_type.items():
        types[mangle(nm)] = ty

    def inst(name, arg):
        key = name if arg is None else '%s(%s)' % (name, arg)
        mk = mangle(key)
        if mk in done:
            return mk
        done.add(mk)
        nts.append(mk)
        param, alts = g.rules[name]
        for producers, action in alts:
            rhs = []
            for b, s in producers:
                if param is not None and s == param:
                    s = arg
                rhs.append((b, s))
            prods.append([mk, rhs, action])
        return mk

    for name in g.rule_order:
        param, _ = g.rules[name]
        if param is None:
            inst(name, None)
    # Instantiate the parameterised rules that are used, then fix up symbols.
    changed = True
    while changed:
        changed = False
        for p in prods:
            new_rhs = []
            for b, s in p[1]:
                m = re.match(r'([A-Za-z_0-9]+)\(([A-Za-z_0-9]+)\)$', s)
                if m:
                    before = len(nts)
                    s2 = inst(m.group(1), m.group(2))
                    if len(nts) != before:
                        changed = True
                    new_rhs.append((b, s2))
                else:
                    new_rhs.append((b, s))
            p[1] = new_rhs
    # Keep rule order: parameterised instances are placed at the end.
    return nts, [tuple(p) for p in prods], types


# ---------------------------------------------------------------------------
# 3. LR automaton
# ---------------------------------------------------------------------------


class Automaton:
    pass


def build(g):
    nts, prods, types = expand(g)
    terms = list(g.tokens)
    tindex = {t: i for i, t in enumerate(terms)}
    ntindex = {n: i for i, n in enumerate(nts)}
    for p in prods:
        for _, s in p[1]:
            assert s in tindex or s in ntindex, s
    # Reachability from the start symbol.
    reach = {g.start}
    stack = [g.start]
    while stack:
        a = stack.pop()
        for p in prods:
            if p[0] == a:
                for _, s in p[1]:
                    if s in ntindex and s not in reach:
                        reach.add(s)
                        stack.append(s)
    unreachable = [n for n in nts if n not in reach]
    assert not unreachable, unreachable
    NT = len(terms)
    rhs = [[s for _, s in p[1]] for p in prods]
    lhs = [p[0] for p in prods]
    prods_of = {n: [i for i, p in enumerate(prods) if p[0] == n] for n in nts}
    # Nullable and first.
    nullable = {n: False for n in nts}
    first = {n: 0 for n in nts}

    def first_word(word):
        """(first set as bitmask, nullable) of a word."""
        f = 0
        for s in word:
            if s in tindex:
                return f | (1 << tindex[s]), False
            f |= first[s]
            if not nullable[s]:
                return f, False
        return f, True

    changed = True
    while changed:
        changed = False
        for i, p in enumerate(prods):
            f, nl = first_word(rhs[i])
            if nl and not nullable[p[0]]:
                nullable[p[0]] = True
                changed = True
            if f | first[p[0]] != first[p[0]]:
                first[p[0]] |= f
                changed = True
    # LR(0) states.
    def closure0(kernel):
        items = list(kernel)
        seen = set(items)
        k = 0
        while k < len(items):
            pi, d = items[k]
            k += 1
            if d < len(rhs[pi]) and rhs[pi][d] in ntindex:
                for q in prods_of[rhs[pi][d]]:
                    it = (q, 0)
                    if it not in seen:
                        seen.add(it)
                        items.append(it)
        return items

    start_kernel = tuple(sorted((q, 0) for q in prods_of[g.start]))
    states = [start_kernel]
    sindex = {start_kernel: 0}
    items_of = []
    trans = []  # list of dict symbol -> state
    k = 0
    while k < len(states):
        items = closure0(states[k])
        items_of.append(items)
        succ = {}
        for pi, d in items:
            if d < len(rhs[pi]):
                succ.setdefault(rhs[pi][d], []).append((pi, d + 1))
        tr = {}
        for sym in sorted(succ, key=lambda s: (s in ntindex, s)):
            ker = tuple(sorted(succ[sym]))
            if ker not in sindex:
                sindex[ker] = len(states)
                states.append(ker)
            tr[sym] = sindex[ker]
        trans.append(tr)
        k += 1
    S = len(states)
    # LALR(1) lookaheads by fixpoint.
    ALL = (1 << NT) - 1
    la = [dict() for _ in range(S)]
    for it in items_of[0]:
        la[0][it] = 0
    for s in range(S):
        for it in items_of[s]:
            la[s].setdefault(it, 0)
    for it in start_kernel:
        la[0][it] = ALL
    changed = True
    while changed:
        changed = False
        for s in range(S):
            lst = la[s]
            for (pi, d) in items_of[s]:
                L = lst[(pi, d)]
                if d < len(rhs[pi]):
                    X = rhs[pi][d]
                    # goto
                    s2 = trans[s][X]
                    old = la[s2][(pi, d + 1)]
                    if old | L != old:
                        la[s2][(pi, d + 1)] = old | L
                        changed = True
                    if X in ntindex:
                        f, nl = first_word(rhs[pi][d + 1:])
                        add = f | (L if nl else 0)
                        for q in prods_of[X]:
                            old = lst[(q, 0)]
                            if old | add != old:
                                lst[(q, 0)] = old | add
                                changed = True
    # Actions.
    actions = []
    conflicts = []
    for s in range(S):
        act = {}
        for (pi, d) in items_of[s]:
            if d == len(rhs[pi]):
                L = la[s][(pi, d)]
                for t in range(NT):
                    if L >> t & 1:
                        if t in act and act[t] != ('R', pi):
                            conflicts.append((s, terms[t], act[t], ('R', pi)))
                        act[t] = ('R', pi)
        for sym, s2 in trans[s].items():
            if sym in tindex:
                t = tindex[sym]
                if t in act:
                    conflicts.append((s, sym, act[t], ('S', s2)))
                act[t] = ('S', s2)
        actions.append(act)
    a = Automaton()
    a.terms, a.nts, a.prods, a.types = terms, nts, prods, types
    a.tindex, a.ntindex = tindex, ntindex
    a.rhs, a.lhs = rhs, lhs
    a.nullable, a.first = nullable, first
    a.states, a.items_of, a.trans, a.la = states, items_of, trans, la
    a.actions, a.conflicts = actions, conflicts
    a.S = S
    a.start = g.start
    return a


# ---------------------------------------------------------------------------
# 4. Annotations for the validators
# ---------------------------------------------------------------------------


def annotate(a):
    S = a.S
    T = len(a.terms)

    def code(sym):
        return a.tindex[sym] if sym in a.tindex else T + a.ntindex[sym]

    # The symbol on top of the stack in each non-initial state.
    last = [None] * S
    preds = [[] for _ in range(S)]
    for s in range(S):
        for sym, s2 in a.trans[s].items():
            assert last[s2] in (None, sym)
            last[s2] = sym
            preds[s2].append(s)
    # Maximal dot position of each state.
    md = [max([d for (_, d) in a.items_of[s]] + [0]) for s in range(S)]
    # Known stack symbols: longest common suffix of the paths, by fixpoint.
    past = [None] * S
    past[0] = []

    def head(s):
        if s == 0:
            return []
        return [last[s]] + past[s]

    def lcp(x, y):
        r = []
        for u, v in zip(x, y):
            if u != v:
                break
            r.append(u)
        return r

    changed = True
    while changed:
        changed = False
        for s2 in range(1, S):
            cur = past[s2]
            for s in preds[s2]:
                if s != 0 and past[s] is None:
                    continue
                h = head(s)
                cur = h if cur is None else lcp(cur, h)
            if cur != past[s2]:
                past[s2] = cur
                changed = True
    past_symb = [None] + [past[s][:max(md[s] - 1, 0)] for s in range(1, S)]
    # Possible past states: least fixpoint, of length md.
    pst = [[0] * md[s] for s in range(S)]
    pst[0] = []
    changed = True
    while changed:
        changed = False
        for s2 in range(1, S):
            for s in preds[s2]:
                hs = [1 << s] + pst[s]
                L = md[s2]
                assert L <= len(hs), (s, s2)
                for i in range(L):
                    if pst[s2][i] | hs[i] != pst[s2][i]:
                        pst[s2][i] |= hs[i]
                        changed = True
    # Action tables.
    default_red = [0] * S
    rows = []
    for s in range(S):
        act = a.actions[s]
        vals = set(act.values())
        if vals and all(v[0] == 'R' for v in vals) and len(vals) == 1:
            default_red[s] = list(vals)[0][1] + 1
            rows.append([])
        else:
            row = []
            for t in sorted(act):
                k, v = act[t]
                row += [t, 2 * (v - 1) if k == 'S' else 2 * v + 1]
            rows.append(row)
    gotos = []
    for s in range(S):
        row = []
        for sym, s2 in sorted(a.trans[s].items(), key=lambda kv: code(kv[0])):
            if sym in a.ntindex:
                row += [a.ntindex[sym], s2 - 1]
        gotos.append(row)
    items = []
    for s in range(S):
        row = []
        for (pi, d) in sorted(a.items_of[s]):
            row += [pi, d, a.la[s][(pi, d)]]
        items.append(row)
    a.code = code
    a.last = last
    a.past_symb = past_symb
    a.past_state = pst
    a.default_red = default_red
    a.rows = rows
    a.gotos = gotos
    a.items_rows = items


# ---------------------------------------------------------------------------
# 5. Translation of Rocq types and semantic actions to Lean
# ---------------------------------------------------------------------------

LEAN_KEYWORDS = {'def', 'fun', 'let', 'in', 'match', 'with', 'do', 'then', 'else', 'if',
                 'for', 'where', 'at', 'by', 'from', 'have', 'show', 'open', 'end',
                 'structure', 'class', 'instance', 'theorem', 'namespace', 'section',
                 'import', 'mut', 'return', 'try', 'catch', 'finally', 'local', 'macro',
                 'syntax', 'deriving', 'unless', 'break', 'continue', 'variable'}


def cabs_type_name(n):
    if n == 'string':
        return 'String'
    return 'Cabs.' + ''.join(w[:1].upper() + w[1:] for w in n.split('_'))


def tokenize_coq(s):
    return re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*|:=|=>|->|::|[()\[\],;*']|\S", s)


def tr_type(s):
    toks = tokenize_coq(s)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def eat(x=None):
        t = toks[pos[0]]
        assert x is None or t == x, (t, x, s)
        pos[0] += 1
        return t

    def atom():
        t = peek()
        if t == '(':
            eat('(')
            r = arrow()
            eat(')')
            return r
        eat()
        if t.startswith('Cabs.'):
            return cabs_type_name(t[5:])
        return {'list': 'List', 'option': 'Option', 'bool': 'Bool', 'unit': 'Unit',
                'nat': 'Nat'}[t]

    def app():
        f = atom()
        args = []
        while peek() not in (None, ')', '*', '->'):
            args.append(atom())
        if args:
            return '(' + ' '.join([f] + args) + ')'
        return f

    def prod():
        r = app()
        while peek() == '*':
            eat('*')
            r = '(' + r + ' × ' + app() + ')'
        return r

    def arrow():
        l = prod()
        if peek() == '->':
            eat('->')
            return '(' + l + ' → ' + arrow() + ')'
        return l

    r = arrow()
    assert pos[0] == len(toks), s
    if r.startswith('(') and r.endswith(')'):
        # Strip one redundant outer pair when balanced.
        d = 0
        ok = True
        for i, c in enumerate(r):
            d += c == '('
            d -= c == ')'
            if d == 0 and i < len(r) - 1:
                ok = False
                break
        if ok:
            r = r[1:-1]
    return r


def tree_of(toks):
    """Group tokens by parentheses and brackets."""
    stack = [('top', [])]
    for t in toks:
        if t in '([':
            stack.append((t, []))
        elif t in ')]':
            kind, items = stack.pop()
            assert (kind, t) in (('(', ')'), ('[', ']'))
            stack[-1][1].append((kind, items))
        else:
            stack[-1][1].append(t)
    assert len(stack) == 1
    return stack[0][1]


def flatten(items):
    for it in items:
        if isinstance(it, tuple):
            yield from flatten(it[1])
        else:
            yield it


def unused_pat(it, used):
    """Replace the variables of a pattern that are not used by `_`."""
    kind, sub = it
    out = []
    for x in sub:
        if isinstance(x, tuple):
            out.append(unused_pat(x, used))
        elif re.match(r'[a-z_][A-Za-z_0-9]*$', x) and x not in used:
            out.append('_')
        else:
            out.append(x)
    return (kind, out)


class ActionTranslator:
    def __init__(self, ctor_types):
        self.ctor_types = ctor_types
        self.kw_binders = set()

    def ident(self, t):
        if t.startswith('Cabs.'):
            c = t[5:]
            assert c in self.ctor_types, t
            return 'Cabs.%s.%s' % (self.ctor_types[c], c)
        m = {'fst': 'Prod.fst', 'snd': 'Prod.snd', "rev'": 'List.reverse', 'rev': 'List.reverse',
             "List.rev'": 'List.reverse', 'List.rev': 'List.reverse', 'List.app': 'List.append',
             'nil': '[]', 'Some': 'some', 'None': 'none'}
        if t in m:
            return m[t]
        if t in self.kw_binders:
            return '«%s»' % t
        return t

    def split_commas(self, items):
        parts = [[]]
        for it in items:
            if it == ',':
                parts.append([])
            else:
                parts[-1].append(it)
        return parts

    def seq(self, items):
        out = []
        i = 0
        while i < len(items):
            it = items[i]
            if it == 'let' and i + 1 < len(items) and items[i + 1] == "'":
                j = items.index(':=', i)
                pat = items[i + 2:j]
                k = items.index('in', j)
                e = items[j + 1:k]
                body = items[k + 1:]
                used = set(flatten(e)) | set(flatten(body))
                pat = [x if not (isinstance(x, str) and re.match(r'[a-z_][A-Za-z_0-9]*$', x)
                                 and x not in used) else '_' for x in pat]
                pat = [unused_pat(x, used) if isinstance(x, tuple) else x for x in pat]
                out.append('(match %s with | %s => %s)' % (self.seq(e), self.seq(pat), self.seq(body)))
                return ' '.join(out)
            if it == 'match':
                j = items.index('with', i)
                k = items.index('=>', j)
                l = items.index('end', k)
                out.append('(match %s with | %s => %s)' % (self.seq(items[i + 1:j]),
                                                          self.seq(items[j + 1:k]),
                                                          self.seq(items[k + 1:l])))
                i = l + 1
                continue
            if isinstance(it, tuple):
                kind, sub = it
                if kind == '(':
                    parts = [self.seq(p) for p in self.split_commas(sub)]
                    if len(parts) >= 3:
                        r = parts[0]
                        for p in parts[1:]:
                            r = '(%s, %s)' % (r, p)
                        out.append(r)
                    else:
                        out.append('(' + ', '.join(parts) + ')')
                else:
                    parts = [self.seq(p) for p in self.split_commas(sub)]
                    out.append('[' + ', '.join(parts) + ']')
            else:
                out.append(self.ident(it))
            i += 1
        return ' '.join(out)

    def translate(self, action):
        return self.seq(tree_of(tokenize_coq(action)))


def cabs_ctor_types(path):
    src = open(path).read()
    src = re.sub(r'/--.*?-/', '', src, flags=re.S)
    src = re.sub(r'--[^\n]*', '', src)
    blocks = re.findall(r'inductive (\w+) where(.*?)(?=\ninductive|\nend|\nstructure|\ninstance|\nabbrev|\Z)',
                        src, flags=re.S)
    m = {}
    for ty, body in blocks:
        for c in re.findall(r'\|\s*([A-Za-z_][A-Za-z_0-9]*)', body):
            assert c not in m, c
            m[c] = ty
    return m


# ---------------------------------------------------------------------------
# 6. Emission
# ---------------------------------------------------------------------------


def chunks(xs, n):
    for i in range(0, len(xs), n):
        yield xs[i:i + n]


def lean_rows(rows, indent='  '):
    """Rows of numbers, encoded as a string literal decoded by `decodeRows`
    (large array literals are slow to elaborate)."""
    text = ';'.join(','.join('%x' % x for x in r) for r in rows)
    lines = [text[i:i + 96] for i in range(0, len(text), 96)]
    return 'decodeRows\n' + indent + '"' + ('\\\n' + indent).join(lines) + '"'


def lean_nat_array(xs, indent='  ', per_line=None):
    return '(' + lean_rows([xs], indent + '  ') + ').getD 0 #[]'


def prod_name(a, i):
    lhs = a.lhs[i]
    k = sum(1 for j in range(i) if a.lhs[j] == lhs)
    return "Prod_%s_%d" % (lhs, k)


def emit(a, g, ctor_types, vy_name):
    T = len(a.terms)
    N = len(a.nts)
    P = len(a.prods)
    S = a.S
    tr = ActionTranslator(ctor_types)
    o = []
    w = o.append
    w('''/-
  Port of `cparser/Parser.v`: CompCert's verified C parser.

  In CompCert, `Parser.v` is generated by Menhir (`menhir --coq`) from the
  grammar `cparser/Parser.vy`.  Menhir has no Lean back end, so this file is
  generated from the same grammar by `export/tools/gen_parser.py`; do not edit
  it by hand.  As in Rocq it consists of
  * the grammar (Rocq's module `Gram`): terminals, non-terminals, the types of
    their semantic values, the productions with their semantic actions, and
    the tokens;
  * the LR(1) automaton (Rocq's module `Aut`) with the annotations needed by
    the validators;
  * the two validation theorems `safe` and `complete`, which run the
    validators of `CCLib/MenhirLib` on the automaton (Rocq proves them by
    computation, here they are checked by compiled evaluation), and the parser
    `translation_unit_file` obtained from `MenhirLib.Main.parse`.

  The generator is untrusted: if it produced a wrong automaton, `safe` or
  `complete` would fail to check.  The results that do not depend on it are
  `translation_unit_file_correct`, `translation_unit_file_complete` and
  `c_grammar_unambiguous` at the end of this file.

  Differences from Menhir's output:
  * the tables of the automaton are stored as arrays of numbers (states are
    `Fin n`, sets of states and of terminals are bit masks) and decoded by
    small functions; the shift and goto entries check the required equality
    `T t = last_symb_of_non_init_state s` at run time;
  * the automaton is built from LR(0) item sets with LALR(1) lookaheads
    instead of Menhir's Pager construction (the grammar is LALR(1), so this
    yields a conflict-free automaton);
  * the parameterised non-terminals `labeled_statement(...)` and
    `iteration_statement(...)` are expanded to
    `labeled_statement_statement_safe_` etc.;
  * Rocq's `Cabs.v` parameters `string`, `loc` and `char_code` are `String`,
    `Cabs.Loc` and `Cabs.CharCode` (see `Cabs.lean`).

  Statistics: %d terminals, %d non-terminals, %d productions, %d states.
-/
import CCLib.cparser.Cabs
import CCLib.MenhirLib.Main

namespace CC
namespace Parser

open MenhirLib

/-! ## Grammar (Rocq's module `Gram`) -/

''' % (T, N, P, S))

    def enum_type(name, ctors, doc):
        w('/-- %s -/\n' % doc)
        w('inductive %s where\n' % name)
        for c in chunks(ctors, 6):
            w('  | ' + ' | '.join(c) + '\n')
        w('  deriving Repr\n\n')
        w('/-- All the constructors of `%s`, in order. -/\n' % name)
        w('def %s.all : Array %s := #[\n  ' % (name, name))
        w(',\n  '.join(', '.join('.' + x for x in c) for c in chunks(ctors, 6)))
        w(']\n\n')
        w('def %s.toNat : %s → Nat\n' % (name, name))
        for i, c in enumerate(ctors):
            w('  | .%s => %d\n' % (c, i))
        w('\n')
        w('def %s.ofNat (n : Nat) : %s := %s.all.getD n .%s\n\n' % (name, name, name, ctors[0]))
        w('set_option maxRecDepth 100000 in\n')
        w('instance %s.numbered : Numbered %s where\n' % (name, name))
        w('  inj := %s.toNat\n' % name)
        w('  surj := %s.ofNat\n' % name)
        w('  surj_inj_compat x := by cases x <;> rfl\n')
        w('  inj_bound := %d\n' % len(ctors))
        w('  inj_bound_spec x := by cases x <;> decide\n\n')
        w('instance %s.alphabet : Alphabet %s := NumberedAlphabet %s.numbered\n\n' % (name, name, name))

    enum_type('Terminal', a.terms, 'The terminals of the grammar (Rocq\'s `terminal\'`).')
    enum_type('Nonterminal', a.nts, 'The non-terminals of the grammar (Rocq\'s `nonterminal\'`).')
    w('instance alphs : Alphs where\n  terminal := Terminal\n  nonterminal := Nonterminal\n\n')

    def term_type(t):
        ty = g.token_type[t]
        return 'Unit' if ty is None else tr_type(ty)

    w('/-- The types of the semantic values of the terminals. -/\n')
    w('def terminalSemType : Terminal → Type\n')
    for t in a.terms:
        w('  | .%s => %s\n' % (t, term_type(t)))
    w('\n')
    w('/-- The types of the semantic values of the non-terminals. -/\n')
    w('def nonterminalSemType : Nonterminal → Type\n')
    for n in a.nts:
        w('  | .%s => %s\n' % (n, tr_type(a.types[n])))
    w('\n')
    w('''/-- The types of the semantic values of the symbols. -/
def symbolSemType : Symbol → Type
  | .T t => terminalSemType t
  | .NT n => nonterminalSemType n

''')
    pnames = [prod_name(a, i) for i in range(P)]
    enum_type('Production', pnames, 'The productions of the grammar, in the order of `Parser.vy`.')

    def sym_lean(sym):
        if sym in a.tindex:
            return '.T .%s' % sym
        return '.NT .%s' % sym

    w('/-- The left-hand side of each production. -/\n')
    w('def prodLhs : Production → Nonterminal\n')
    for i in range(P):
        w('  | .%s => .%s\n' % (pnames[i], a.lhs[i]))
    w('\n')
    w('/-- The right-hand side of each production, in reverse order. -/\n')
    w('def prodRhsRev : Production → List Symbol\n')
    for i in range(P):
        w('  | .%s => [%s]\n' % (pnames[i], ', '.join('(%s)' % sym_lean(s) for s in reversed(a.rhs[i]))))
    w('\n')

    def sem_type(sym):
        if sym in a.tindex:
            return term_type(sym)
        return tr_type(a.types[sym])

    w('''/-- The semantic actions of `Parser.vy`; the arguments are taken in reverse
order (last symbol of the right-hand side first). -/
def prodAction : ∀ p : Production,
    arrows_right (symbolSemType (.NT (prodLhs p))) ((prodRhsRev p).map symbolSemType)
''')
    for i in range(P):
        prod = a.prods[i]
        binders = []
        tr.kw_binders = {b for b, _ in prod[1] if b in LEAN_KEYWORDS}
        for b, s in reversed(prod[1]):
            nm = '_' if b is None else tr.ident(b)
            binders.append('(%s : %s)' % (nm, sem_type(s)))
        body = tr.translate(prod[2])
        w('  | .%s => fun %s =>\n' % (pnames[i], ' '.join(binders)) if binders else
          '  | .%s =>\n' % pnames[i])
        w('    (%s : %s)\n' % (body, tr_type(a.types[a.lhs[i]])))
    w('\n')
    # Tokens.
    w('/-- Tokens: a terminal together with its semantic value. -/\n')
    w('inductive Token where\n')
    for t in a.terms:
        w('  | %s : %s → Token\n' % (t, term_type(t)))
    w('\n')
    w('def Token.term : Token → Terminal\n')
    for t in a.terms:
        w('  | .%s _ => .%s\n' % (t, t))
    w('\n')
    w('def Token.sem : ∀ tok : Token, terminalSemType tok.term\n')
    for t in a.terms:
        w('  | .%s v => v\n' % t)
    w('\n')
    w('''instance gram : GrammarT where
  symbol_semantic_type := symbolSemType
  production := Production
  prod_lhs := prodLhs
  prod_rhs_rev := prodRhsRev
  prod_action := prodAction
  token := Token
  token_term := Token.term
  token_sem := Token.sem

/-! ## Automaton (Rocq's module `Aut`) -/

/-- `Fin (n + 1)` as a numbered type. -/
@[reducible] def finNumbered (n : Nat) : Numbered (Fin (n + 1)) where
  inj := Fin.val
  surj k := ⟨k %% (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
  surj_inj_compat x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  inj_bound := n + 1
  inj_bound_spec x := x.isLt

/-- The non-initial states (Rocq's `noninitstate'`). -/
abbrev NonInitState := Fin %d

instance NonInitState.alphabet : Alphabet NonInitState := NumberedAlphabet (finNumbered %d)

/-- The initial states (Rocq's `initstate'`): one per `%%start` symbol. -/
inductive InitState where
  | Init_translation_unit_file
  deriving Repr

instance InitState.numbered : Numbered InitState where
  inj _ := 0
  surj _ := .Init_translation_unit_file
  surj_inj_compat x := by cases x; rfl
  inj_bound := 1
  inj_bound_spec x := by cases x; decide

instance InitState.alphabet : Alphabet InitState := NumberedAlphabet InitState.numbered

/-- Decoding of the tables below: rows are separated by `;`, entries by `,`,
and entries are written in hexadecimal. -/
def decodeRows (s : String) : Array (Array Nat) :=
  (s.splitOn ";").toArray.map fun r =>
    if r.isEmpty then #[] else (r.splitOn ",").toArray.map hexToNat
where
  hexToNat (w : String) : Nat :=
    w.foldl (fun n c => 16 * n + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0

/-- Decoding symbols: terminals are numbered first, then non-terminals. -/
def symOfNat (c : Nat) : Symbol :=
  if c < %d then .T (Terminal.ofNat c) else .NT (Nonterminal.ofNat (c - %d))

/-- The symbol on top of the stack in each non-initial state. -/
def lastSymbTable : Array Nat :=
  %s

instance autInit : AutInit where
  noninitstate := NonInitState
  initstate := InitState
  last_symb_of_non_init_state s := symOfNat (lastSymbTable.getD s.val 0)

/-- States are numbered `0` (the initial state) and `s + 1` (non-initial). -/
def stateIdx : State → Nat
  | .Init _ => 0
  | .Ninit s => s.val + 1

/-- For each state, `p + 1` if it reduces production `p` by default, else `0`. -/
def defaultRedTable : Array Nat :=
  %s

/-- For each state, its lookahead actions as a flat list of pairs
`terminal, code`, where `code = 2 * s` shifts to non-initial state `s` and
`code = 2 * p + 1` reduces production `p`; missing terminals fail. -/
def actionTable : Array (Array Nat) := %s

/-- For each state, its goto entries as a flat list of pairs
`non-terminal, non-initial state`. -/
def gotoTable : Array (Array Nat) := %s

/-- For each non-initial state, the codes of the symbols known to be below the
top of the stack. -/
def pastSymbTable : Array (Array Nat) := %s

/-- For each non-initial state, bit masks (indexed by `stateIdx`) of the
states that may appear below the top of the stack. -/
def pastStateTable : Array (Array Nat) := %s

/-- For each state, its LR(1) items as a flat list of triples
`production, dot position, bit mask of lookahead terminals`. -/
def itemsTable : Array (Array Nat) := %s

/-- The nullable non-terminals, as a bit mask. -/
def nullableMask : Nat := 0x%x

/-- For each non-terminal, the bit mask of the terminals that can begin it. -/
def firstTable : Array Nat :=
  %s

/-- The list of terminals in a bit mask. -/
def termsOfMask (m : Nat) : List Terminal :=
  (List.range %d).filterMap fun i => if m.testBit i then some (Terminal.ofNat i) else none

/-- Search a flat list of pairs. -/
def findPair (row : Array Nat) (k : Nat) : Option Nat := Id.run do
  let mut i := 0
  while i + 1 < row.size do
    if row[i]! == k then return some row[i + 1]!
    i := i + 2
  return none

def lookaheadOf (row : Array Nat) (t : Terminal) : lookahead_action t :=
  match findPair row t.toNat with
  | none => .Fail_act
  | some c =>
    if c %% 2 = 0 then
      let s2 : NonInitState := (finNumbered %d).surj (c / 2)
      if h : Symbol.T t = last_symb_of_non_init_state s2 then .Shift_act s2 h else .Fail_act
    else .Reduce_act (Production.ofNat (c / 2))

def actionOf (s : State) : action :=
  let d := defaultRedTable.getD (stateIdx s) 0
  if d = 0 then .Lookahead_act (lookaheadOf (actionTable.getD (stateIdx s) #[]))
  else .Default_reduce_act (Production.ofNat (d - 1))

def gotoOf (s : State) (nt : Nonterminal) :
    Option { s2 : noninitstate // Symbol.NT nt = last_symb_of_non_init_state s2 } :=
  match findPair (gotoTable.getD (stateIdx s) #[]) nt.toNat with
  | none => none
  | some k =>
    let s2 : NonInitState := (finNumbered %d).surj k
    if h : Symbol.NT nt = last_symb_of_non_init_state s2 then some ⟨s2, h⟩ else none

/-- The items of each state, decoded once. -/
def itemsDecoded : Array (List item) :=
  itemsTable.map fun row => Id.run do
    let mut acc : List item := []
    let mut i := 0
    while i + 2 < row.size do
      acc := { prod_item := Production.ofNat row[i]!, dot_pos_item := row[i + 1]!,
               lookaheads_item := termsOfMask row[i + 2]! } :: acc
      i := i + 3
    return acc.reverse

instance aut : AutomatonT where
  start_nt _ := .translation_unit_file
  action_table := actionOf
  goto_table := gotoOf
  past_symb_of_non_init_state s :=
    ((pastSymbTable.getD s.val #[]).map symOfNat).toList
  past_state_of_non_init_state s :=
    ((pastStateTable.getD s.val #[]).map fun m (st : State) => m.testBit (stateIdx st)).toList
  items_of_state s := itemsDecoded.getD (stateIdx s) []
  nullable_nterm nt := nullableMask.testBit nt.toNat
  first_nterm nt := termsOfMask (firstTable.getD nt.toNat 0)

/-! ## Validation and the parser -/

/-- The automaton is safe (Rocq's `Parser.safe`). -/
theorem safe : Main.safe_validator () = true := by native_decide

/-- The automaton is complete with respect to the grammar (Rocq's
`Parser.complete`). -/
theorem complete : Main.complete_validator () = true := by native_decide

/-- The parser of C translation units (Rocq's `Parser.translation_unit_file`).
`log_n_steps` bounds the number of steps by `2 ^ log_n_steps`. -/
def translation_unit_file (log_n_steps : Nat) (buf : Buffer) :
    parse_result (List Cabs.Definition) :=
  Main.parse safe .Init_translation_unit_file log_n_steps buf

/-- Correctness of the parser: when it accepts, its result is the semantic
value of a parse tree (for the grammar of `Parser.vy`) of a prefix of the
input, and the rest of the input is returned. -/
theorem translation_unit_file_correct (log_n_steps : Nat) (buf : Buffer)
    (sem : List Cabs.Definition) (buf_rest : Buffer)
    (h : translation_unit_file log_n_steps buf = .Parsed_pr sem buf_rest) :
    ∃ word, ∃ pt : parse_tree (.NT .translation_unit_file) word,
      buf = app_buf word buf_rest ∧ pt_sem pt = sem := by
  have hc := Main.parse_correct safe .Init_translation_unit_file log_n_steps buf
  unfold translation_unit_file at h
  rw [h] at hc
  exact hc

/-- Completeness of the parser: for every parse tree of a word, the parser run
on this word followed by any input returns the semantic value of the tree and
the rest of the input when `pt_size tree ≤ 2 ^ log_n_steps`, and times out
otherwise; in particular it never fails. -/
theorem translation_unit_file_complete (log_n_steps : Nat) (word : List Token)
    (buf_end : Buffer) (tree : parse_tree (.NT .translation_unit_file) word) :
    (pt_size tree ≤ 2 ^ log_n_steps →
      translation_unit_file log_n_steps (app_buf word buf_end) = .Parsed_pr (pt_sem tree) buf_end) ∧
    (2 ^ log_n_steps < pt_size tree →
      translation_unit_file log_n_steps (app_buf word buf_end) = .Timeout_pr) := by
  have hc := Main.parse_complete safe .Init_translation_unit_file log_n_steps word buf_end
    complete tree
  unfold translation_unit_file
  revert hc
  cases Main.parse safe .Init_translation_unit_file log_n_steps (app_buf word buf_end) with
  | Parsed_pr sem rest =>
    rintro ⟨h1, h2, h3⟩
    subst h1 h2
    exact ⟨fun _ => rfl, fun h => absurd h (Nat.not_lt.mpr h3)⟩
  | Timeout_pr =>
    intro h
    exact ⟨fun h' => absurd h (Nat.not_lt.mpr h'), fun _ => rfl⟩
  | Fail_pr_full _ _ => intro h; exact h.elim

/-- The grammar of `Parser.vy` is unambiguous: two parse trees of the same
word have the same semantic value. -/
theorem c_grammar_unambiguous (word : List Token)
    (tree1 tree2 : parse_tree (.NT .translation_unit_file) word) :
    pt_sem tree1 = pt_sem tree2 :=
  Main.unambiguity safe complete ⟨.EOF ()⟩ .Init_translation_unit_file word tree1 tree2

end Parser
end CC
''' % (S - 1, S - 2, T, T,
       lean_nat_array([a.code(a.last[s]) for s in range(1, S)], '    '),
       lean_nat_array(a.default_red, '    '),
       lean_rows(a.rows), lean_rows(a.gotos),
       lean_rows([[a.code(x) for x in a.past_symb[s]] for s in range(1, S)]),
       lean_rows([a.past_state[s] for s in range(1, S)]),
       lean_rows(a.items_rows),
       sum(1 << a.ntindex[n] for n in a.nts if a.nullable[n]),
       lean_nat_array([a.first[n] for n in a.nts], '    '),
       T, S - 2, S - 2))
    return ''.join(o)


if __name__ == '__main__':
    vy, out = sys.argv[1], sys.argv[2]
    g = parse_vy(vy)
    a = build(g)
    if a.conflicts:
        for c in a.conflicts:
            print('conflict', c, file=sys.stderr)
        sys.exit(1)
    annotate(a)
    import os
    cabs = os.path.join(os.path.dirname(out), 'Cabs.lean')
    text = emit(a, g, cabs_ctor_types(cabs), vy)
    open(out, 'w').write(text)
    print('terminals %d, nonterminals %d, productions %d, states %d'
          % (len(a.terms), len(a.nts), len(a.prods), a.S))
