
import sat
import ptnet
import z3

from util import *
from encoding import *

class MergingEquivalence :
    def __init__ (self, domain) :
        self.domain = domain

    def is_in_domain (self, it) :
        for x in it :
            if x not in self.domain :
                raise LookupError, "'%s' is not in the domain" % repr (x)

    def are_merged (self, x, y) :
        self.is_in_domain ([x, y])
        return x == y

    def class_of (self, x) :
        self.is_in_domain ([x])
        return [x]

    def classes (self) :
        return [[x] for x in self.domain]

    def assert_is_equivalence (self) :
        return NotImplementedError

    def __repr__ (self) :
        return str (self.classes ())
    def __str__ (self) :
        return repr (self)

class Smt2MergingEquivalence (MergingEquivalence) :
    def __init__ (self, domain, enc) :
        MergingEquivalence.__init__ (self, domain)
        self.enc = enc
        self.model = enc.z3.model ()

    def are_merged (self, x, y) :
        self.is_in_domain ([x, y])
        if isinstance (x, ptnet.Condition) :
            assert (isinstance (y, ptnet.Condition))

            vx = self.enc.smt_varmap (x)
            vy = self.enc.smt_varmap (y)

            # if we didn't generate variable for one of them
            # then it is surely possible to have one that
            # has the same value as the other, ie, we merge
            if (vx == None or vy == None) : return True

            return self.model[vx].as_long () == self.model[vy].as_long ()

        else :
            assert (isinstance (x, ptnet.Event))
            assert (isinstance (y, ptnet.Event))

            if x.label != y.label : return False
            vx = self.enc.smt_varmap (x)
            vy = self.enc.smt_varmap (y)
            assert (vx != None)
            assert (vy != None)
            return self.model[vx].as_long () == self.model[vy].as_long ()

    def class_of (self, x) :
        raise RuntimeError
    def classes (self) :
        raise RuntimeError
    def __str__ (self) :
        return str (self.model)

class ComputedMergingEquivalence (MergingEquivalence) :
    def __init__ (self, domain) :
        MergingEquivalence.__init__ (self, domain)
        self.class_by_id = {}
        self.class_by_member = {}

    def set_class (self, x, class_id) :
        # FIXME
        # there is a bug here, the code is broken!
        self.is_in_domain ([x])
        if class_id in self.class_by_id :
            self.class_by_id[class_id].add (x)
        elif x in self.class_by_member :
            self.class_by_id[class_id] = self.class_by_member[x]
        else :
            self.class_by_id[class_id] = set ([x])
        self.class_by_member[x] = self.class_by_id[class_id]
        return self.class_by_member[x]
        
    def are_merged (self, x, y) :
        if x == y : return True
        self.is_in_domain ([x, y])
        if x not in self.class_by_member :
            raise LookupError, \
                "'%s': unknown equivalence class" % repr (x)
        if y not in self.class_by_member :
            raise LookupError, \
                "'%s': unknown equivalence class" % repr (y)
        return id (self.class_by_member[x]) == id (self.class_by_member[y])

    def class_of (self, x) :
        self.is_in_domain ([x])
        if x not in self.class_by_member :
            raise LookupError, \
                "'%s': unknown equivalence class" % repr (x)
        return self.class_by_member[x]

    def classes (self) :
        return list (set (tuple (x) for x in self.class_by_member.values ()))

class IdentityMergingEquivalence (MergingEquivalence) :
    pass

# vi:ts=4:sw=4:et:
