
import math
import time

import sat
import ptnet
import z3

from util import *
from equivalence import *
from encoding import *

def sgl (s) :
    return (list (s))[0]


class SmtEquivalenceFinder :
    def __init__ (self, unfolding, smt_or_sat = 'SMT_2') :
        assert (smt_or_sat in ['SMT_1', 'SMT_2', 'SAT'])
        self.unf = unfolding
        self.enc = SmtEquivalenceEncoding (unfolding)
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


    # The following methods come from an old version of the merge method,
    # could be useful here

    def __assert_merge_pre (self, unf, meq) :

        # all events have non-empty preset
        for e in unf.events :
            assert (len (e.pre))

        ## inverse labelling is good
        #m = unf.new_mark ()
        #for a in unf.net.trans :
        #    assert (len (a.inverse_label) >= 1)
        #    for e in a.inverse_label :
        #        assert (e.m != m)
        #        e.m = m
        #for e in unf.events :
        #    assert (e.m == m)

    def __assert_merge_post (self, unf, meq, e2t, c2p) :

        assert (len (e2t) == len (unf.events))
        assert (len (c2p) == len (unf.conds))

        for e,t in e2t.items () :
            for ee in e2t :
                if e2t[ee] == t :
                    assert (meq.are_merged (e, ee))
                    self.__assert_merge_subset (meq, e, ee)
                    self.__assert_merge_subset (meq, ee, e)
        for c,p in c2p.items () :
            for cc in c2p :
                if c2p[cc] == p :
                    assert (meq.are_merged (c, cc))

    def __assert_merge_subset (self, meq, e, ee) :
        # all events in preset and postset of e are merged with at least
        # one of ee
        for x,y in [(e.pre, ee.pre), (e.post, ee.post)] :
            for c in x :
                assert (any (map (lambda cc : meq.are_merged (c, cc), y)))

    def __apply_merging_eq (self, meq) :
        # this function does the actual marging of unf, using the merging
        # equivalence me, and returns the resulting ptnet.Net
        unf = self.bp
        self.__assert_merge_pre (unf, meq)
        net = ptnet.Net (True)

        # merge events
        e2t = {}
        c2p = {}
        for a in unf.net.trans :
            d = {}
            for e in a.inverse_label :
                found = False
                for ee in d :
                    if meq.are_merged (e, ee) :
                        d[ee].add (e)
                        found = True
                        break
                if not found :
                    d[e] = set ([e])
            print "pod: merging: label", repr (a), "result:", d.values ()
            for e,evs in d.items () :
                t = net.trans_add (repr ((a, evs)))
                for ee in evs : e2t[ee] = t

        # merge conditions
        d = {}
        for c in unf.conds :
            found = False
            for cc in d :
                if meq.are_merged (c, cc) :
                    d[cc].add (c)
                    found = True
                    break
            if not found :
                d[c] = set ([c])
        print "pod: merging: conditions:", d.values ()
        for c,conds in d.items () :
            p = net.place_add (repr (conds))
            for c in conds : c2p[c] = p

        self.__assert_merge_post (unf, meq, e2t, c2p)

        # build flow
        for e in e2t :
            for c in e.pre :
                e2t[e].pre_add (c2p[c])
            for c in e.post :
                e2t[e].post_add (c2p[c])

        # build initial marking
        for c in unf.m0 :
            net.m0[c2p[c]] = 1

        self.net = net
        return net

class SpMergingEquivalenceFactory :

    @staticmethod
    def one_place (unf) :

        # sp-all
        # merges all events with same label
        # merges all conditions into 1 single place
        # ignores negative info

        domain = set (unf.events) | set (unf.conds)
        meq = ComputedMergingEquivalence (domain)
        i = 0
        for a in unf.net.trans :
            for e in a.inverse_label :
                meq.tag_class (e, i)
            i += 1
        for c in unf.conds :
            meq.tag_class (c, i)

        meq.assert_is_equivalence ()
        return meq

    @staticmethod
    def pre_singleton (unf) :

        # sp-pre-sgl
        # merges all events with same label
        # merges the presets of all events it merges into 1 single place
        # ignores negative info

        domain = set (unf.events) | set (unf.conds)
        meq = ComputedMergingEquivalence (domain)
        i = 0
        for a in unf.net.trans :
            # merge all events with same label
            for e in a.inverse_label :
                meq.tag_class (e, i)
            i += 1

            if len (a.inverse_label) <= 1 :
                # if we are not merging events, do NOT merge the preset
                for e in a.inverse_label :
                    for c in e.pre :
                        meq.tag_class (c, i)
                        i += 1
            else :
                # if we are merging at least 2 events, merge ALL places into 1
                for e in a.inverse_label :
                    for c in e.pre :
                        meq.tag_class (c, i)
                i += 1

        # since all conditions are in the preset of some event, the
        # previous should define an equivalence class for all of them

        meq.assert_is_equivalence ()
        return meq

# vi:ts=4:sw=4:et:
