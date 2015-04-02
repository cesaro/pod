#!/usr/bin/env python

try :
    import os
    import sys
    import time
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
    def __init__ (self) :
        self.unf = None
        self.satf = None
        self.smtf = None
        self.__co = None

        # many algorithms rely on this property
        for i in range (self.unf.events) :
            assert (self.unf.events[i].nr == i)
        for i in range (self.unf.conds) :
            assert (self.unf.conds[i].nr == i)

    def __ord_pair (x, y) :
        if x.nr < y.nr :
            return (x, y)
        else :
            return (y, x)

    def are_co (c1, c2) :
        if self.co == None :
            self.__compute_co_relation ()
        return self.__ord_pair (c1, c2) in self.__co

    def __compute_co_relation () :
        self.__co = set ()
        for c in self.unf.conds :
            self.__compute_co_relation_c (c)
        
    def __compute_co_relation_c (cgoal) :
        mpre = self.unf.new_mark ()
        mpost = self.unf.new_mark ()
        mcfl = self.unf.new_mark ()

        # mark conditions consumed and events fired to mark cgoal
        work = [cgoal]
        for c in work :
            if len (c.pre) == 0 : continue
            e = sgl (c.pre)
            if e.m == mpre : continue
            e.m = mpre
            for cc in e.pre :
                cc.m = mpre
                work.append (cc)
        consumed = work

        # mark conditions that need to consume cgoal to be marked
        work = [cgoal]
        for c in work :
            for e in c.post :
                if e.m == mpost : continue
                e.m = mpost
                for cc in e.post :
                    cc.m = mpost
                    work.append (cc)

        # mark conditions (and events) in conflict with cgoal
        work = consumed
        for c in work :
            for e in c.post :
                if e.m == mpre : continue # skip events in local config
                if e.m == mcfl : continue
                e.m = mcfl
                for cc in c.post :
                    cc.m = mcfl
                    work.append (cc)

        # at this point
        # - conds marked with mpre  : have been consumed to mark cgoal
        # - conds marked with mpost : cgoal will be consumed to mark them
        # - conds marked with mcfl  : are in conflict with cgoal
        # - all others              : are concurrent
        for c in self.unf.conds :
            if c.m == mpre or c.m == mcfl or c.m == mpost : continue
            if c != cgoal :
                self.__co.add (self.__ord_pair (cgoal, c))

    # def __are_co_assert (c1, c2) :
    #     # if they are siblings, then they are surely concurrent
    #     if len (c1.pre) and len (c2.pre) :
    #         if sgl (c1.pre) == sgl (c2.pre) : return True

    def sat_encode (k) :
        self.satf = cnf.Cnf ()

        # EQ : it is an equivalence relation
        self.__sat_encode_transitivity ()

        # IP : it preserves independence
        self.__sat_encode_labels ()
        self.__sat_encode_pre ()
        self.__sat_encode_post ()
        self.__sat_encode_co ()

        # RA : do no merge removed events
        self.__sat_encode_removal ()

        # MET : the measure of the folded net is at most k
        self.__sat_encode_measure (k)

    def __sat_encode_transitivity () :
        # events with events
        for ei in self.unf.events :
            for ej in self.unf.events :
                for ek in self.unf.events :
                    vij = self.satf.var (self.__ord_pair (ei, ej))
                    vjk = self.satf.var (self.__ord_pair (ej, ek))
                    vik = self.satf.var (self.__ord_pair (ei, ek))
                    self.satf.add ([-vij, -vjk, vik])

        # conditions with conditions
        for ci in self.unf.conds :
            for cj in self.unf.conds :
                for ck in self.unf.conds :
                    vij = self.satf.var (self.__ord_pair (ci, cj))
                    vjk = self.satf.var (self.__ord_pair (cj, ck))
                    vik = self.satf.var (self.__ord_pair (ci, ck))
                    self.satf.add ([-vij, -vjk, vik])

    def __sat_encode_labels () :
        # for each pair of events, if labels are different, they cannot be
        # merged
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                if ei.label != ej.label :
                    vij = self.satf.var (self.__ord_pair (ei, ej))
                    self.satf.add ([-vij])
        
    def __sat_encode_subset (setx, sety) :
        # we generate a new variable v that holds iff
        # every element of setx shall be merged with at least one element
        # of sety
        print "podisc: encode_subset: setx", setx, "sety", sety
        setx = frozenset (setx)
        sety = frozenset (sety)
        v = self.satf.var ((setx, sety))
        and_clause = [v]
        for x in setx :
            vx = self.satf.var ((x, sety))
            and_clause.append (-vx) # conjuntion of all or variables imply v
            clause = [-v]
            for y in sety :
                vxy = self.satf.var (self.__ord_pair (x, y))
                clause.append (vxy)
                self.satf.add ([-vxy, vx]) # each or implies vx
            self.satf.add (clause)
        self.satf.add (and_clause)
        return v

    def __sat_encode_pre () :
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

                self.satf.add ([-vij, v1])
                self.satf.add ([-vij, v2])

    def __sat_encode_post () :
        # same as for __sat_encode_pre but this time for postset
        for i in range (len (self.unf.events)) :
            for j in range (i + 1, len (self.unf.events)) :
                ei = self.unf.events[i]
                ej = self.unf.events[j]
                vij = self.satf.var (self.__ord_pair (ei, ej))

                # subset inclusion in both directions
                v1 = self.__sat_encode_subset (ei.post, ej.post)
                v2 = self.__sat_encode_subset (ej.post, ei.post)

                self.satf.add ([-vij, v1])
                self.satf.add ([-vij, v2])

    def __sat_encode_co () :
        self.__compute_co_relation ()
        for (c1, c2) in self.__co :
            assert ((c1, c2) == self.__ord_pair (c1, c2))
            v = self.satf.var ((c1, c2))
            self.satf.add ([-v])

    def __sat_encode_removal () :
        pass

    def __sat_encode_measure (k) :
        pass

    def smt_encode () :
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
    u = ptnet.unfolding.Unfolding (True)
    f = open ('benchmarks/nets/small/gas_station.cuf', 'r')
    #f = open ('out.cuf', 'r')
    u.read (f)
    u.prune_by_depth (4)
    u.write (sys.stdout, 'dot')
    #u.remove_event (6)
    #u.write (sys.stdout, 'dot')

    #print 'conditions'
    #for c in u.conds :
    #    print c
    #print 'events'
    #for e in u.events :
    #    print e

def main () :
    # parse arguments
    # assert that input net is 1-safe!!
    pass

if __name__ == '__main__' :
    test4 ()

# vi:ts=4:sw=4:et:
