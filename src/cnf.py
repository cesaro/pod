
import os
import time
import select
import signal
import tempfile
import subprocess

class Cnf :
    def __init__ (self) :
        self.varmap = {}
        self.clsset = set ()

    def var (self, obj) :
        if not obj in self.varmap :
            self.varmap[obj] = len (self.varmap) + 1
        return self.varmap[obj]

    def add (self, cls) :
        c = frozenset (cls)
        #print "podisc: cnf: new clause", cls
        #if c in self.clsset : print "podisc: cnf: dupplicated!"
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

class Integer :
    def __init__ (self, cnf, obj, k) :
        # width in bits
        self.k = k
        # the cnf formula on which we append encodings
        self.cnf = cnf
        # the object on which this integer is associated
        self.obj = obj

        self.bit = []
        for i in xrange (k) :
            self.bit.append (cnf.var (("int-bit%d" % i, obj)))

    def encode_eq (self, other, vout=None) :
        # this encodes self == other
        # the returned variable v holds iff (self == other)
        if other.k != self.k :
            raise Exception, "Different bit width while encoding integer equality"
        v = vout
        if v == None :
            v = self.cnf.var (("int-eq", self.obj, other.obj))
        vi_clause = [v]
        for i in xrange (self.k) :
            vi = self.cnf.var (("int-eq-aux%d" % i, self.obj, other.obj))
            vi_clause.append (-vi)

            # v -> (s[i] <-> o[i])
            self.cnf.add ([-v, -self.bit[i], other.bit[i]])
            self.cnf.add ([-v, -other.bit[i], self.bit[i]])

            # (s[i] <-> o[i]) -> vi
            self.cnf.add ([-self.bit[i], -other.bit[i], vi])
            self.cnf.add ([self.bit[i], other.bit[i], vi])

        # v1 ^ ... ^ vn -> v
        self.cnf.add (vi_clause)
        return v

    def encode_lt (self, other) :
        # this encode self < other
        # the returned variable is such that, if it is true, then (self < other)
        if other.k != self.k :
            raise Exception, "Different bit width while encoding integer lt"

        # three variables per bit: s[i], o[i], a[i] (a for "aux")
        #
        # for i >= 1:
        #   (a[i] ^  a[i-1]) -> s[i] = o[i]
        #   (a[i] ^ !a[i-1]) -> s[i] < o[i]
        # for i == 0:
        #   a[0] -> s[0] < o[0]
        #
        # now, to force self < other it's enough with setting a[k-1]
        # NOTE: setting a[k-1] to false does not imply "not (self < other)"
        #

        si = self.bit[0]
        oi = other.bit[0]
        ai1 = self.cnf.var (("int-lt-aux0", self.obj, other.obj))

        # if a[0], then s[0] < o[0]
        self.cnf.add ([-ai1, -si])
        self.cnf.add ([-ai1, oi])

        for i in xrange (1, self.k) :
            si = self.bit[i]
            oi = other.bit[i]
            ai = self.cnf.var (("int-lt-aux%d" % i, self.obj, other.obj))

            # if a[i] and a[i-1], then si == oi
            self.cnf.add ([-ai, -ai1, -si, oi])
            self.cnf.add ([-ai, -ai1, si, -oi])

            # if a[i] and not a[i-1], then si < oi
            self.cnf.add ([-ai, ai1, -si])
            self.cnf.add ([-ai, ai1, oi])

            ai1 = ai

        return ai1

    def encode_eq_constant (self, n) :
        # encode the fact that this integer equals integer n
        if n >= (1 << self.k) :
            raise Exception, "Bit width of %d is insufficient to encode constant %d" % (self.k, n)

        for i in xrange (self.k) :
            if n & (1 << i) :
                self.cnf.add ([self.bit[i]])
            else :
                self.cnf.add ([-self.bit[i]])

class SatSolver :
    def __init__ (self) :
        pass

    def solve (self, phi, timeout=-1) :
        pathin, pathout = '', ''
        try :
            # make temporary files for the formula and minisat's output
            fdin, pathin = tempfile.mkstemp (suffix='.cnf.py.cnf')
            fdout, pathout = tempfile.mkstemp (suffix='.cnf.py.cnf')
            # write the formula in dimacs format
            fin = os.fdopen (fdin, 'w')
            fout = os.fdopen (fdout, 'r')
            #db ('write cnf')
            phi.write (fin)
            fin.close ()
            # call the solver
            #db ('solve')
            s, out = self.__runit (['minisat', pathin, pathout], timeout)
            # load minisat's results
            out = fout.readlines ()
            fout.close ()
        finally :
            # remove temporary files
            os.unlink (pathin)
            os.unlink (pathout)

        # handle errors
        if s != 20 and s != 10 and s != 254 :
            raise Exception, \
                    'Minisat terminated with unknown exit status %d' % s

        # UNDEF (killed due to timeout)
        if s == 254 :
            return SatModel (phi, SatModel.RESULT_UNDEF)

        # UNSAT
        if s == 20 :
            return SatModel (phi, SatModel.RESULT_UNSAT)

        # out is the contents of the minisat output file, of the form:
        # SAT
        # 1 43 591 -1 4 0
        if len (out) != 2 :
            raise Exception, 'Error while parsing minisat output'
        out = out[1].split ()
        try :
            out = [int (x) for x in out]
        except :
            raise Exception, 'Error when parsing minisat output'

        out = set (x for x in out if x > 0)
        return SatModel (phi, SatModel.RESULT_SAT, out)

    def __runit (self, args, timeout=-1, sh=False) :
        print "podisc: cnf:", args, "timeout", timeout
        try :
            p = subprocess.Popen (args, bufsize=8192, stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    preexec_fn=os.setsid, shell=sh)
        except Exception :
            raise Exception, "Unable to execute the command `minisat', is minisat installed?"

    #    db ('pid', p.pid)
        try :
            killed = False
            s = ''
            p.stdin.close ()
            if timeout > 0 :
                tref = time.time ()
                while True :
                    t = timeout - (time.time () - tref)
                    if t <= 0 : t = 0
    #                db ('select at', time.time () - tref, t)
                    (r, w, x) = select.select ([p.stdout], [], [p.stdout], t)
    #                db ('return at', time.time () - tref, r, w, x)
                    if len (r) :
                        # read (n) waits for n bytes before returning
                        c = p.stdout.read (1)
                        if len (c) == 0 : break
                        s += c
                    else :
    #                    db ('killing', p.pid)
                        os.killpg (p.pid, signal.SIGTERM)
                        killed = True
                        break
            p.wait ()
            s += p.stdout.read ()
            return (p.returncode if not killed else 254, s)
        except KeyboardInterrupt :
            os.killpg (p.pid, signal.SIGKILL)
            p.wait ()
            raise

# class SatResult:
#     SAT = 0
#     UNSAT = 1
#     UNKNOWN = 2
# 
#     def __init__(self, r):
#         assert (r in [SatResult.SAT, SatResult.UNSAT, SatResult.UNDEF])
#         self.r = r
# 
#     def __eq__(self, other):
#         return isinstance (other, SatResult) and self.r == other.r
# 
#     def __ne__(self, other):
#         return not self.__eq__(other)
# 
#     def __repr__(self):
#         if self.r == SatResult.SAT :
#             return "SAT"
#         elif self.r == SatResult.UNSAT :
#             return "UNSAT"
#         else :
#             return "UNKNOWN"
# 
# SAT     = SatResult (SatResult.SAT)
# UNSAT   = SatResult (SatResult.UNSAT)
# UNKNOWN = SatResult (SatResult.UNKNOWN) 

class SatModel :

    # outcome of the solving
    RESULT_SAT   = 'SAT'
    RESULT_UNSAT = 'UNSAT'
    RESULT_UNDEF = '?'

    def __init__ (self, phi, result, satvars=None) :
        self.result = result
        self.phi = phi

        if satvars == None :
            satvars = set ()
        self.satisfied_vars = satvars

    def is_sat (self) :
        return self.result == SatModel.RESULT_SAT

    def is_unsat (self) :
        return self.result == SatModel.RESULT_UNSAT

    def is_undef (self) :
        return self.result == SatModel.RESULT_UNDEF

    def __getitem__ (self, obj) :
        if self.result != SatModel.RESULT_SAT :
            raise Exception, "The formula is not SAT"
        try :
            v = self.phi.varmap[obj];
        except KeyError :
            raise Exception, "Error: object '%s' is not in the variable map" % obj
        return v in self.satisfied_vars

    def __iter__ (self) :
        if self.result != SatModel.RESULT_SAT :
            raise Exception, "The formula is unsatisfiable"
        for k,v in self.phi.variable.items () :
            if v in self.satisfied_vars :
                yield k

    def __repr__ (self) :
        return self.result

    def __str__ (self) :
        s = repr (self)
        if self.result != SatModel.RESULT_SAT : return s
        s += "\n"
        for (k,v) in sorted (self.phi.varmap.items (), key=lambda (k,v) : v) :
            s += " %s  %4d %s\n" % ("T" if v in self.satisfied_vars else "F", v, repr (k))
        return s

# vi:ts=4:sw=4:et:
