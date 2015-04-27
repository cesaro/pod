
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
        # we asser that
        # - every class is disjoint from any other class
        # - every element of the domain is in at least one class
        # to do it we just iterate through all elements of all classes, and
        # watch if we see two times the same element, checking at the end
        # that we saw all elements of the domain

        e2c = {}
        for c in self.classes () :
            for e in c :
                if e in e2c :
                    # already seen!
                    raise AssertionError, \
                            "Element '%s' is two classes, %s and %s" % \
                            (repr (e), long_list (c, 5), long_list (e2c[e], 5))
                e2c[e] = c
        seen = set (e2c.keys ())
        if not self.domain <= seen :
            print 'seen', seen
            print 'domain', self.domain
            raise AssertionError, \
                    "The set of classes contains less elements than the domain!"
        if not seen <= self.domain :
            print 'seen', seen
            print 'domain', self.domain
            raise AssertionError, \
                    "The set of classes contains more elements than the domain!"

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
        self.__tag2class = {}
        self.__class2tags = {}
        self.__mem2class = {}

    def __merge_classes (self, c1, c2) :
        # optimization: merge the smaller one into the larger one :)
        if id (c1) == id (c2) : return
        if len (c2) > len (c1) :
            c = c1
            c1 = c2
            c2 = c

        # move all elements of c2 into c1
        c1.update (c2)

        # update the pointer of all members of c2 in mem2class to point to c1
        for e in c2 :
            self.__mem2class[e] = c1

        # same for the tags, all tags pointing to c2 must now point to c1
        tagsc2 = self.__class2tags[id(c2)]
        for tag in tagsc2 :
            self.__tag2class[tag] = c1

        # all tags of c2 are now tags of c1
        self.__class2tags[id(c1)].update (tagsc2)
        del self.__class2tags[id(c2)]
        return c1

    def tag_class (self, x, tag) :
        # find x's class, or create a new one
        self.is_in_domain ([x])
        try :
            c = self.__mem2class[x]
        except KeyError :
            c = self.__mem2class[x] = set ([x])
            self.__class2tags[id(c)] = set ()

        # if the tag is new and unknown, update the tables
        if tag not in self.__tag2class :
            self.__tag2class[tag] = c
            self.__class2tags[id(c)].add (tag)
        else :
            # if it is not new, it already pointed to some class and we
            # need to merge x's class and that class
            c = self.__merge_classes (c, self.__tag2class[tag])
        return c

    def __memb_is_known (self, it) :
        for x in it :
            if x not in self.__mem2class :
                raise LookupError, "No equivalence class defined for '%s'" % repr (x)
    def __tag_is_known (self, it) :
        for tag in it :
            if tag not in self.__tag2class :
                raise LookupError, "No equivalence class defined for tag '%s'" % repr (tag)

    def are_merged (self, x, y) :
        self.is_in_domain ([x, y])
        self.__memb_is_known ([x, y])
        if id (x) == id (y) : return True
        return id (self.__mem2class[x]) == id (self.__mem2class[y])

    def class_of (self, x ) :
        return self.class_of_member (x)
    def class_of_member (self, x) :
        self.is_in_domain ([x])
        self.__memb_is_known ([x])
        return self.__mem2class[x]
    def class_of_tag (self, tag) :
        self.__tag_is_known ([tag])
        return self.__tag2class[tag]

    def classes (self) :
        return list (set (tuple (x) for x in self.__tag2class.values ()))

class IdentityMergingEquivalence (MergingEquivalence) :
    pass

# vi:ts=4:sw=4:et:
