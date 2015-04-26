
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


# vi:ts=4:sw=4:et:
