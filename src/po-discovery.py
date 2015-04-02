#!/usr/bin/env python

try :
    import os
    import sys
    import time
    import math
    import resource
    import argparse
    import ptnet
    import cnf
except Exception, e:
    print 'ERROR!'
    print 'It seems that your python installation is missing some package.'
    print 'This tool requires, among others, argparse, and networkx'
    print 'The runtime reported the following error:\n\n', str (e), '\n'
    print 'You might want to use "easy_install --user PACKAGE"'
    raise e
    sys.exit (1)
finally :
    if sys.version_info < (2, 7, 0) or sys.version_info >= (3, 0, 0) :
        print ("")
        print ("*** ERROR ***")
        print ("This tool relies on Python 2.7!!")
        print ("Install Python 2.7 or modify the first line of the file 'po-discovery.py' so that it calls Python 2.7")
        print ("")
        sys.exit (1)

def sgl (s) :
    return (list (s))[0]

class Equivalence_finder :
    def __init__ (self, unfolding) :
        self.unf = unfolding
        self.satf = None
        self.smtf = None
        self.__co = None

        self.__compute_co_relation ()

        # many algorithms in here rely on this property
        for i in range (len (self.unf.events)) :
            assert (self.unf.events[i].nr == i)
        for i in range (len (self.unf.conds)) :
            assert (self.unf.conds[i].nr == i)

    def __ord_pair (self, x, y) :
        if x.nr < y.nr :
            return (x, y)
        else :
            return (y, x)

    def are_co (self, c1, c2) :
        if self.co == None :
            self.__compute_co_relation ()
        return self.__ord_pair (c1, c2) in self.__co

    def __compute_co_relation (self, ) :
        self.__co = set ()
        for c in self.unf.conds :
            self.__compute_co_relation_c (c)

    def __compute_co_relation_c (self, cgoal) :
        print "podisc: compute_co: goal", repr (cgoal)
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
        print "podisc: compute_co:  past"
        print "podisc: compute_co: ", work

        # mark conditions that consume conditions in work (future of cgoal
        # or conflict)
        for c in work :
            for e in c.post :
                if e.m == mpast : continue # this one is in local config
                e.m = mfuture
                for cc in e.post :
                    cc.m = mfuture
                    work.append (cc)
        print "podisc: compute_co:  past and future"
        print "podisc: compute_co: ", work

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
        print "podisc: compute_co:  co"
        print "podisc: compute_co: ", l
        print "podisc: compute_co:  total", len (l)

    # def __are_co_assert (c1, c2) :
    #     # if they are siblings, then they are surely concurrent
    #     if len (c1.pre) and len (c2.pre) :
    #         if sgl (c1.pre) == sgl (c2.pre) : return True

    def sat_encode (self, k) :
        self.satf = cnf.Cnf ()

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
                    print "podisc: sat: clause", repr (ei), repr (ej), repr (ek), [-vij, -vjk, vik]

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
                    print "podisc: sat: clause", [-vij, -vjk, vik]

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
        print "podisc: sat: encode_subset: setx", setx, "sety", sety
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
                vij = self.satf.var (self.__ord_pair (ei, ej))

                # subset inclusion in both directions
                v1 = self.__sat_encode_subset (ei.pre, ej.pre)
                v2 = self.__sat_encode_subset (ej.pre, ei.pre)

                print "podisc: sat: encode_pre:", repr (ei), repr (ej), "(2 cls):"
                self.satf.add ([-vij, v1])
                self.satf.add ([-vij, v2])

    def __sat_encode_post (self) :
        # same as for __sat_encode_pre but this time for postset
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                vij = self.satf.var (self.__ord_pair (ei, ej))

                # subset inclusion in both directions
                v1 = self.__sat_encode_subset (ei.post, ej.post)
                v2 = self.__sat_encode_subset (ej.post, ei.post)

                print "podisc: sat: encode_pre:", repr (ei), repr (ej), "(2 cls):"
                self.satf.add ([-vij, v1])
                self.satf.add ([-vij, v2])

    def __sat_encode_co (self) :
        self.__compute_co_relation ()
        for (c1, c2) in self.__co :
            assert ((c1, c2) == self.__ord_pair (c1, c2))
            v = self.satf.var ((c1, c2))
            print "podisc: sat: encode_co:", repr (c1), repr (c2)
            self.satf.add ([-v])

    def __sat_encode_measure (self, k) :
        # we associate an integer to every event
        bitwith = int (math.ceil (math.log (1 + len (self.unf.events), 2)))
        intmap = {}
        for e in self.unf.events :
            intmap[e] = cnf.Integer (self.cnf, e, bitwith)
        
        # for every two events, if they are merged, the integers must equal
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                vij = self.satf.var (self.__ord_pair (ei, ej))

                intmap[ei].encode_eq (intmap[ej], vij)

        # we generate one more integer for the bound
        bound = cnf.Integer (self, cnf, "bound (k+1)", bitwith)
        bound.encode_eq_constant (k + 1)

        # the integer associated to any event must be smaller than the bound
        for encint in intmap.values () :
            v = encint.encode_lt (bound)
            self.cnf.add ([v])

    def __sat_encode_removal (self) :
        pass

    def smt_encode (self) :
        pass

def test1 () :
    n = ptnet.net.Net (True)
    n.read (sys.stdin, 'pnml')
    n.write (sys.stdout, 'pnml')

def test2 () :
    u = ptnet.unfolding.Unfolding (True)
    f = open ('benchmarks/nets/small/dme2.cuf', 'r')
    u.read (f)
    print 'x' * 80
    print 'events'
    for e in u.events :
        print e
    print 'x' * 80
    print 'conditions'
    for c in u.conds :
        print c

    print 'x' * 80
    print 'dot'
    u.write (sys.stdout, 'dot')

def test3 () :
    u = ptnet.unfolding.Unfolding (True)
    f = open ('benchmarks/nets/small/gas_station.cuf', 'r')
    u.read (f)

    print 'x' * 80
    print "before removing condition"
    u.write (sys.stdout, 'dot')
    print "condition"
    print u.conds[1]
    u.remove_cond (u.conds[1].nr)

    print 'x' * 80
    print "after removing condition"
    u.write (sys.stdout, 'dot')

    print 'x' * 80
    print "event"
    print u.events[0]
    u.remove_event (u.events[0].nr)
    print "after removing event"
    u.write (sys.stdout, 'dot')

def test4 () :
    f = open ('benchmarks/nets/small/gas_station.cuf', 'r')
    #f = open ('benchmarks/nets/small/dme2.cuf', 'r')
    u = ptnet.unfolding.Unfolding (True)
    u.read (f)
    u.prune_by_depth (2)
    #u.write (sys.stdout, 'dot')

    finder = Equivalence_finder (u)
    print
    finder.sat_encode (1)
    print
    #f = open ('/tmp/out.cnf', 'w')
    print repr (finder.satf)

def test5 () :
    for k in range (1, 6) :
        u = ptnet.unfolding.Unfolding (True)
        f = open ('benchmarks/nets/small/dme2.cuf', 'r')
        u.read (f)
        u.prune_by_depth (k)
        ff = open ('dme2-pref%d.dot' % k, 'w')
        u.write (ff, 'dot')

def test6 () :
    phi = cnf.Cnf ()

    a = cnf.Integer (phi, "first", 4)
    b = cnf.Integer (phi, "second", 4)
    v = a.encode_lt (b)
    print 'returned', v

    print repr (phi)

    phi.add ([v])
    a.encode_eq_constant (5)
    b.encode_eq_constant (5)

    f = open ("/tmp/out.cnf", "w")
    phi.write (f)

def test7 () :
    # events, conditions, k, vars, clauses, k, minisat time, answer

def main () :
    # parse arguments
    # assert that input net is 1-safe!!

    # TODO
    # - support for reading the model and building a Merge_equivalence
    # - support for merging the unfolding given a Merge_equivalence
    # - debug on some small example, start with gas_station.cuf, depth=2,3,4

    pass

if __name__ == '__main__' :
    test6 ()

# vi:ts=4:sw=4:et:
