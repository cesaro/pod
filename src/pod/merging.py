
import math
import time

import sat
import ptnet
import z3

from util import *

def sgl (s) :
    return (list (s))[0]


class MergingEquivalence :
    def are_merged (self, x, y) :
        return False

class Smt2MergingEquivalence (MergingEquivalence) :
    def __init__ (self, enc) :
        self.enc = enc
        self.model = enc.z3.model ()

    def are_merged (self, x, y) :
        if isinstance (x, ptnet.unfolding.Condition) :
            assert (isinstance (y, ptnet.unfolding.Condition))

            vx = self.enc.smt_varmap (x)
            vy = self.enc.smt_varmap (y)

            # if we didn't generate variable for one of them
            # then it is surely possible to have one that
            # has the same value as the other, ie, we merge
            if (vx == None or vy == None) : return True

            return self.model[vx].as_long () == self.model[vy].as_long ()

        else :
            assert (isinstance (x, ptnet.unfolding.Event))
            assert (isinstance (y, ptnet.unfolding.Event))

            if x.label != y.label : return False
            vx = self.enc.smt_varmap (x)
            vy = self.enc.smt_varmap (y)
            assert (vx != None)
            assert (vy != None)
            return self.model[vx].as_long () == self.model[vy].as_long ()

    def __str__ (self) :
        return str (self.model)

class EquivalenceSolver :
    def __init__ (self, unfolding, smt_or_sat = 'SMT_2') :
        assert (smt_or_sat in ['SMT_1', 'SMT_2', 'SAT'])
        self.unf = unfolding
        self.enc = EquivalenceEncoding (unfolding)
        self.smt_or_sat = smt_or_sat

    def find_best (self) :
        # does the binary search
        pass

    def find_with_measure (self, k, timeout = 10 * 1000) :
        # returns an equivalence, or None
        
        if self.smt_or_sat == 'SMT_2' :
            print "podisc: solver: building SMT_2 encoding"
            self.enc.smt_encode_2 (k)
            print "podisc: solver: z3: calling, timeout=%ds ..." % (timeout / 1000)
            self.enc.z3.set ("timeout", timeout)
            tstart = time.time ()
            result = self.enc.z3.check ()
            tend = time.time ()
            print "podisc: solver: z3: done, %.2fs, %s" % (tend - tstart, result)
            print_stats (sys.stdout, self.enc.stats (), "podisc: solver: z3: ")
            if result == z3.sat :
                return Smt2MergingEquivalence (self.enc)
            elif result == z3.unsat :
                return None
            else :
                print "podisc: solver: answer: unknown"
                return None
        elif smt_or_sat == 'SMT_1' :
            return None # fixme
        else :
            return None # fixme

class EquivalenceEncoding :
    def __init__ (self, unfolding) :
        self.unf = unfolding
        self.satf = None
        self.z3 = None
        self.k = -1
        self.__co = None

        self.__compute_co_relation ()

        # many algorithms in here rely on this property
        for i in range (len (self.unf.events)) :
            assert (self.unf.events[i].nr == i)
        for i in range (len (self.unf.conds)) :
            assert (self.unf.conds[i].nr == i)

    def stats (self) :
        # nr of events, conditions, labels
        # int variables, constraints
        d = {}
        d['unf.events']         = len (self.unf.events)
        d['unf.conditions']     = len (self.unf.conds)
        d['labels.transitions'] = len (self.unf.net.trans)
        d['labels.places']      = len (self.unf.net.places)
        d['k']                  = self.k

        # distribution of events per label
        distrib = {}
        histo = {}
        s = ""
        avg = 0
        nmin = len (self.unf.net.trans[0].inverse_label)
        nmax = -1
        for t in self.unf.net.trans :
            n = len (t.inverse_label)
            distrib[t] = n
            try :
                histo[n] += 1
            except KeyError :
                histo[n] = 1
            s += "%s=%d " % (repr (t), n)

            if n < nmin : nmin = n
            if n > nmax : nmax = n
            avg += n

        avg /= len (self.unf.net.trans)

        d['labels.distrib'] = s
        d['labels.distrib.min/max/avg'] = (nmin, nmax, avg)
        d['labels.histogram'] = histo

        if self.z3 :
            d['z3.constaints'] = len (self.z3.assertions())
        if self.satf :
            d['sat.clauses'] = len (self.satf.clsset)
            d['sat.vars']    = len (self.satf.varmap)
        return d

    def __ord_pair (self, x, y) :
        if x.nr < y.nr :
            return (x, y)
        else :
            return (y, x)

    def are_co (self, c1, c2) :
        self.__compute_co_relation ()
        return self.__ord_pair (c1, c2) in self.__co

    def __compute_co_relation (self) :
        if self.__co != None :
            return
        self.__co = set ()
        for c in self.unf.conds :
            self.__compute_co_relation_c (c)

    def __compute_co_relation_c (self, cgoal) :
        #print "podisc: compute_co: goal", repr (cgoal)
        mpast = self.unf.new_mark ()
        mfuture = self.unf.new_mark ()

        # mark conditions consumed and events fired to mark cgoal
        work = [cgoal]
        for c in work :
            if len (c.pre) == 0 : continue
            e = sgl (c.pre)
            if e.m == mpast : continue
            e.m = mpast
            for cc in e.pre :
                cc.m = mpast
                work.append (cc)
        consumed = work
        #print "podisc: compute_co:  past"
        #print "podisc: compute_co: ", work

        # mark conditions that consume conditions in work (future of cgoal
        # or conflict)
        for c in work :
            for e in c.post :
                if e.m == mpast : continue # this one is in local config
                e.m = mfuture
                for cc in e.post :
                    cc.m = mfuture
                    work.append (cc)
        #print "podisc: compute_co:  past and future"
        #print "podisc: compute_co: ", work

        # at this point
        # - conds marked with mpast   : have been consumed to mark cgoal
        # - conds marked with mfuture : cgoal in conflict or causal # predecessor
        # - all others                : are concurrent
        l = []
        for c in self.unf.conds :
            if c.m == mpast or c.m == mfuture : continue
            if c != cgoal :
                l.append (c)
                self.__co.add (self.__ord_pair (cgoal, c))
        #print "podisc: compute_co:  co"
        #print "podisc: compute_co: ", l
        #print "podisc: compute_co:  total", len (l)

    def sat_encode (self, k) :
        self.satf = sat.Cnf ()
        self.k = k

        # EQ : it is an equivalence relation
        self.__sat_encode_transitivity ()

        # IP : it preserves independence
        self.__sat_encode_labels ()
        self.__sat_encode_pre ()
        self.__sat_encode_post ()
        self.__sat_encode_co ()

        # RA : does not merge removed events
        self.__sat_encode_removal ()

        # MET : the measure of the folded net is at most k
        self.__sat_encode_measure (k)

    def __sat_encode_transitivity (self) :
        # events with events
        for ei in self.unf.events :
            for ej in self.unf.events :
                if ei == ej : continue
                for ek in self.unf.events :
                    if ek == ei or ek == ej : continue
                    vij = self.satf.var (self.__ord_pair (ei, ej))
                    vjk = self.satf.var (self.__ord_pair (ej, ek))
                    vik = self.satf.var (self.__ord_pair (ei, ek))
                    self.satf.add ([-vij, -vjk, vik])
                    #print "podisc: sat: clause", repr (ei), repr (ej), repr (ek), [-vij, -vjk, vik]

        # conditions with conditions
        for ci in self.unf.conds :
            for cj in self.unf.conds :
                if ci == cj : continue
                for ck in self.unf.conds :
                    if ck == ci or ck == cj : continue
                    vij = self.satf.var (self.__ord_pair (ci, cj))
                    vjk = self.satf.var (self.__ord_pair (cj, ck))
                    vik = self.satf.var (self.__ord_pair (ci, ck))
                    self.satf.add ([-vij, -vjk, vik])
                    #print "podisc: sat: clause", [-vij, -vjk, vik]

    def __sat_encode_labels (self) :
        # for each pair of events, if labels are different, they cannot be
        # merged
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                if ei.label != ej.label :
                    vij = self.satf.var (self.__ord_pair (ei, ej))
                    self.satf.add ([-vij])
        
    def __sat_encode_subset (self, setx, sety) :
        # we generate a new variable v that holds iff
        # every element of setx shall be merged with at least one element
        # of sety
        #print "podisc: sat: encode_subset: setx", setx, "sety", sety
        setx = frozenset (setx)
        sety = frozenset (sety)
        v = self.satf.var (("subset", setx, sety))
        and_clause = [v]
        for x in setx :
            vx = self.satf.var (("subset_x_match", x, sety))
            and_clause.append (-vx) # conjuntion of all or variables imply v
            clause = [-v]
            for y in sety :
                vxy = self.satf.var (self.__ord_pair (x, y))
                clause.append (vxy)
                self.satf.add ([-vxy, vx]) # each or implies vx
            self.satf.add (clause)
        self.satf.add (and_clause)
        return v

    def __sat_encode_pre (self) :
        # for every two events, if we decide to merge them, then the
        # presets must merge as well (the set of equivalence classes in the
        # preset of one must be equal to the set of equvalence classes in
        # the preset of the other)
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                if ei.label != ej.label : continue # optimization
                vij = self.satf.var (self.__ord_pair (ei, ej))

                # subset inclusion in both directions
                v1 = self.__sat_encode_subset (ei.pre, ej.pre)
                v2 = self.__sat_encode_subset (ej.pre, ei.pre)

                #print "podisc: sat: encode_pre:", repr (ei), repr (ej), "(2 cls):"
                self.satf.add ([-vij, v1])
                self.satf.add ([-vij, v2])

    def __sat_encode_post (self) :
        # same as for __sat_encode_pre but this time for postset
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                if ei.label != ej.label : continue # optimization
                vij = self.satf.var (self.__ord_pair (ei, ej))

                # subset inclusion in both directions
                v1 = self.__sat_encode_subset (ei.post, ej.post)
                v2 = self.__sat_encode_subset (ej.post, ei.post)

                #print "podisc: sat: encode_pre:", repr (ei), repr (ej), "(2 cls):"
                self.satf.add ([-vij, v1])
                self.satf.add ([-vij, v2])

    def __sat_encode_co (self) :
        self.__compute_co_relation ()
        for (c1, c2) in self.__co :
            assert ((c1, c2) == self.__ord_pair (c1, c2))
            v = self.satf.var ((c1, c2))
            #print "podisc: sat: encode_co:", repr (c1), repr (c2)
            self.satf.add ([-v])

    def __sat_encode_measure (self, k) :
        # we associate an integer to every event
        bitwith = int (math.ceil (math.log (1 + len (self.unf.events), 2)))
        intmap = {}
        for e in self.unf.events :
            intmap[e] = sat.Integer (self.satf, e, bitwith)
        
        # for every two events, if they are merged, the integers must equal
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                vij = self.satf.var (self.__ord_pair (ei, ej))

                intmap[ei].encode_eq (intmap[ej], vij)

        # we generate one more integer for the bound
        bound = sat.Integer (self.satf, "bound (k+1)", bitwith)
        bound.encode_eq_constant (k + 1)

        # the integer associated to any event must be smaller than the bound
        for encint in intmap.values () :
            v = encint.encode_lt (bound)
            self.satf.add ([v])

    def __sat_encode_removal (self) :
        pass

    def __smt_assert_repr (self) :

        # assert that the repr() of all events and conditions is different
        reprs = set ()
        for e in self.unf.events :
            assert (repr (e) not in reprs)
            reprs.add (repr (e))
        for c in self.unf.conds :
            assert (repr (c) not in reprs)
            reprs.add (repr (c))
        for t in self.unf.net.trans :
            assert (len (t.inverse_label) != 0)
            assert (repr (t) not in reprs)
            reprs.add (repr (t))

        # not needed so far
        # for p in self.unf.net.places : assert (len (p.inverse_label) != 0)

    def smt_encode_1 (self, k) :

        # assert that the unfolding is in right shape and create the solver
        self.k = k
        self.__smt_assert_repr ()
        self.z3 = z3.Solver ()

        # equivalence: nothing to do !!

        # IP : it preserves independence
        self.__smt_encode_labels_1 ()
        self.__smt_encode_pre_post ()
        self.__smt_encode_co_1 ()

        # RA: does not merge removed events
        self.__smt_encode_removal ()

        # MET : the measure of the folded net is at most k
        self.__smt_encode_measure_1 (k)
        return

    def __smt_encode_labels_1 (self) :
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                if ei.label != ej.label :
                    x_ei = self.smt_varmap (ei)
                    x_ej = self.smt_varmap (ej)
                    self.z3.add (x_ei != x_ej)

    def __smt_encode_pre_post (self, which = "pre_and_post") :
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                #print "podisc: smt: pre_post: ei", repr (ei), "ej", repr (ej)
                if ei.label != ej.label : continue # important optimization
                #print "podisc: smt: pre_post: after!"

                xi = self.smt_varmap (ei)
                xj = self.smt_varmap (ej)

                s = "merge-%s-%s-%s" % (which, repr (ei), repr (ej))
                b = z3.Bool (s)
                self.z3.add (z3.Implies (xi == xj, b))
                #b = (xi == xj)

                if which in ["pre", "pre_and_post"] :
                    self.__smt_encode_subset (ei.pre, ej.pre, b)
                    self.__smt_encode_subset (ej.pre, ei.pre, b)
                if which in ["post", "pre_and_post"] :
                    self.__smt_encode_subset (ei.post, ej.post, b)
                    self.__smt_encode_subset (ej.post, ei.post, b)

    def __smt_encode_co_1 (self) :
        self.__compute_co_relation ()
        for (c1, c2) in self.__co :
            assert ((c1, c2) == self.__ord_pair (c1, c2))

            x1 = self.smt_varmap (c1)
            x2 = self.smt_varmap (c2)

            #print "podisc: sat: encode_co:", repr (c1), repr (c2)
            self.z3.add (x1 != x2)

    def __smt_encode_removal (self) :
        pass

    def __smt_encode_measure_1 (self, k) :
        # for each event e, x_e must be smaller or equal to k
        for e in self.unf.events :
            x = self.smt_varmap (e)
            self.z3.add (x < k)
            self.z3.add (0 <= x)

    def __smt_encode_subset (self, setx, sety, b = None) :
        # each element of setx must be merged to some element of sety
        # this function generates and returns a boolean variable that, if it is
        # true, then subset inclusion happens
        l = []
        for x in setx :
            vx = self.smt_varmap (x)
            cons = z3.Or ([vx == self.smt_varmap (y) for y in sety])
            l.append (cons)
        if b == None :
            s = "merge-subset-%s-%s" % (repr (setx), repr (sety))
            b = z3.Bool (s)
        self.z3.add (z3.Implies (b, z3.And (l)))
        return b

    def smt_varmap (self, item) :
        return z3.Int (repr (item))

    def smt_encode_2 (self, k) :

        # assert that the unfolding is in right shape and create the solver
        self.k = k
        self.__smt_assert_repr ()
        self.z3 = z3.Solver ()

        # equivalence: nothing to do !!

        # IP : it preserves independence
        print "podisc: smt_2: presets + posets"
        self.__smt_encode_pre_post ()
        print "podisc: smt_2: co"
        self.__smt_encode_co_2 ()

        # RA: does not merge removed events
        #self.__smt_encode_removal_2 ()

        # MET : the measure of the folded net is at most k
        print "podisc: smt_2: measure"
        self.__smt_encode_measure_2 (k)
        print "podisc: smt_2: done"
        return

    def __smt_encode_co_2 (self) :
        self.__compute_co_relation ()
        for (c1, c2) in self.__co :
            assert ((c1, c2) == self.__ord_pair (c1, c2))

            if not self.__smt_encode_co_2_need_to (c1, c2) :
                #print "podisc: smt_2: co: not needed", repr (c1), repr (c2)
                continue

            #print "podisc: smt_2: co: needed", repr (c1), repr (c2)
            x1 = self.smt_varmap (c1)
            x2 = self.smt_varmap (c2)

            #print "podisc: sat: encode_co:", repr (c1), repr (c2)
            self.z3.add (x1 != x2)

    def __smt_encode_co_2_need_to (self, c1, c2) :

        return True

        # FIXME this is unsound
        if len (set (e.label for e in c1.post) & set (e.label for e in c2.post)) :
            return True
        if len (set (e.label for e in c1.pre) & set (e.label for e in c2.pre)) :
            return True
        return False

    def __smt_encode_measure_2 (self, k) :
        # the number of merged transitions in each label must be under k
        self.z3.add (sum (self.smt_varmap (t) for t in self.unf.net.trans) <= k)

        # for each label, and each event e in h' (a)
        for t in self.unf.net.trans :
            y = self.smt_varmap (t)
            for e in t.inverse_label :
                x = self.smt_varmap (e)
                self.z3.add (z3.And (0 <= x, x < y))

# vi:ts=4:sw=4:et:
