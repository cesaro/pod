
import sat
import ptnet
import z3

from util import *
from encoding import *

class MergingEquivalence :
    def are_merged (self, x, y) :
        return x == y
    def class_of (self, x) :
        return [x]
    def classes (self) :
        raise NotImplementedError

    def __repr__ (self) :
        return str (self.classes ())
    def __str__ (self) :
        return repr (self)

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

    def class_of (self, x) :
        raise NotImplementedError
    def classes (self) :
        raise NotImplementedError
    def __str__ (self) :
        return str (self.model)

class ComputedMergingEquivalence (MergingEquivalence) :
    def __init__ (self, domain) :
        self.class_by_id = {}
        self.class_by_member = {}
        self.domain = domain

    def set_class (self, x, class_id) :
        if x not in self.domain :
            raise ValueError, "'%s' is not in the domain" % repr (x)
        if class_id in self.class_by_id :
            self.class_by_id[class_id].add (x)
        else :
            self.class_by_id[class_id] = set ([x])
        self.class_by_member[x] = self.class_by_id[class_id]
        return self.class_by_member[x]
        
    def are_merged (self, x, y) :
        if x == y : return True
        if x not in self.class_by_member or y not in self.class_by_member :
            raise LookupError, \
                "Unknown equivalence class for either '%s' or '%s'" % \
                (repr (x), repr (y))
        return self.class_by_member[x] == self.class_by_member[y]

    def class_of (self, x) :
        if x not in self.class_by_member :
            raise LookupError, \
                "'%s': unknown equivalence class" % repr (x)
        return self.class_by_member[x]

    def classes (self) :
        raise self.class_by_member.values ()

class IdentityMergingEquivalence (MergingEquivalence) :
    def __init__ (self, domain) :
        self.domain = domain
    def classes (self) :
        return [[x] for x in self.domain]

# vi:ts=4:sw=4:et:
