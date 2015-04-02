
class Cnf (object) :
    def __init__ (self) :
        self.varmap = {}
        self.clsset = set ()

    def var (self, obj) :
        if not obj in self.varmap :
            self.varmap[obj] = len (self.varmap) + 1
        return self.varmap[obj]

    def add (self, cls) :
        c = frozenset (cls)
        print "podisc: cnf: new clause", cls
        if c in self.clsset :
            print "podisc: cnf: dupplicated!"
        self.clsset.add (c)

    def amo_pairwise (self, l) :
        # for n >= 0 items, produces (n^2-n)/2 clauses, no new variables
        for i in xrange (len (l)) :
            for j in xrange (i + 1, len (l)) :
                self.add ([-l[i], -l[j]])

    def amo_2tree (self, l) :
        # for n >= 3 items, produces n-1 new vars and 3n-5 clauses
        if len (l) <= 1 : return
        if len (l) == 2 :
            self.add ([-l[0], -l[1]])
            return

        l2 = []
        if len (l) & 1 : l2.append (l.pop ())
        for i in xrange (0, len (l), 2) :
            v1 = l[i]
            v2 = l[i + 1]
            v = self.var (('amo_2tree', v1, v2))

            self.add ([-v1, -v2])
            self.add ([-v1, v])
            self.add ([-v2, v])
            l2.append (v)
        self.amo_2tree (l2)

    def amo_ktree (self, l, k) :
        if len (l) <= 1 : return
        assert (k >= 2)
        if len (l) <= k :
            self.amo_pairwise (l)
            return

        l2 = l[: len (l) % k]
        del l[: len (l) % k]
        for i in xrange (0, len (l), k) :
            l3 = l[i:i + k]
#            db ('c i', i, 'k', k, 'l3', l3, 'l', l)
            v = self.var (('amo_ktree', frozenset (l3)))
            for vi in l3 : self.add ([-vi, v])
            self.amo_pairwise (l3)
            l2.append (v)
        self.amo_ktree (l2, k)

    def amo_seq (self, l) :
        # for n >= 3, produces n-2 new vars and 3n-5 clauses
        if len (l) <= 1 : return
        self.add ([-l[0], -l[1]])
        if len (l) == 2 : return
        ref = frozenset (l)
        self.add ([-l[0], self.var (('amo_seq', ref, l[1]))])
        va = self.var (('amo_seq', ref, l[-2]))
        self.add ([-l[-2], va])
        self.add ([-va, -l[-1]])
        if len (l) == 3 : return

        for i in xrange (1, len (l) - 2) :
            va = self.var (('amo_seq', ref, l[i]))
            va1 = self.var (('amo_seq', ref, l[i + 1]))
            self.add ([-l[i], va])
            self.add ([-va, va1])
            self.add ([-va, -l[i + 1]])

    def amo_bin (self, l) :
        # for n >= 2, generates ceil(log n) new vars and n*ceil(log n) clauses at most
        if len (l) <= 1 : return
        k = int (math.ceil (math.log (len (l), 2)))
        z = (1 << k) - len (l)

        i = 0
        fs = frozenset (l)
        for v in l :
            f = 1 if z >= 1 else 0
            z -= 1
            for j in xrange (f, k) :
                p = self.var (('amo_bin', fs, j))
                if (1 << j) & i == 0 : p = -p
                self.add ([-v, p])
            i += 1 + f

    def amo_kprod (self, l, k) :
        assert (k >= 2)
        if len (l) <= 1 : return
        if len (l) == 2 :
            self.add ([-l[0], -l[1]])
            return

        db ('c k', k, 'l', l)
        ref = frozenset (l)
        # there are better ways to implement this comparison, k might be large!
        if (1 << (k - 1)) >= len (l) :
            k = int (math.ceil (math.log (len (l), 2)))
            db ('c new k', k)
        b = int (math.ceil (len (l) ** (1.0 / k)))
        db ('c b', b)
        assert ((b ** k) >= len (l))

        t = [0 for i in xrange (k)]
        for v in l :
            db ('c v', v, 'assigned to', t)
            for i in xrange (k) :
                vij = self.var (('amo_kprod', ref, i, t[i]))
                db ('c %d -> %d' % (v, vij))
                self.add ([-v, vij])
            for i in xrange (k) :
                t[i] += 1
                if t[i] < b : break
                t[i] = 0
        for i in xrange (k - 1) :
            l2 = [self.var (('amo_kprod', ref, i, j)) for j in xrange (b)]
            db ('c amo dim', i, 'l2', l2)
            self.amo_kprod (l2, k)
        i = t[k - 1] + 1 if t[k - 1] != 0 else b
        l2 = [self.var (('amo_kprod', ref, k - 1, j)) for j in xrange (i)]
        db ('c amo dim', k-1, 'l2', l2)
        self.amo_kprod (l2, k)

    def write (self, f) :
        f.write ('p cnf %d %d\n' % (len (self.varmap), len (self.clsset)))
        for c in self.clsset :
            s = ''
            for v in c : s += str (v) + ' '
            s += '0\n'
            f.write (s)

    def __repr__ (self) :
        s = ''
        for (k,v) in sorted (self.varmap.items (), key=lambda (k,v) : v) :
            s += 'c %5d is "%s"\n' % (v, k)
        s += '\np cnf %d %d\n' % (len (self.varmap), len (self.clsset))
        for c in self.clsset :
            for v in c : s += str (v) + ' '
            s += '0\n'
        return s

    def __str__ (self) :
        return self.__repr__ ()

# vi:ts=4:sw=4:et:
