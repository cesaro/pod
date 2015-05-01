"""

pod [OPTIONS] net-stats            PNMLFILE
pod [OPTIONS] extract-dependence   PNMLFILE
pod [OPTIONS] compare-independence PNMLFILE PNMLFILE
pod [OPTIONS] extract-log          PNMLFILE
pod [OPTIONS] dump-log             LOGFILE
pod [OPTIONS] dump-pes             LOGFILE DEPENFILE
pod [OPTIONS] dump-bp              LOGFILE DEPENFILE
pod [OPTIONS] dump-encoding        LOGFILE DEPENFILE
pod [OPTIONS] dump-merge           LOGFILE DEPENFILE
pod [OPTIONS] merge                LOGFILE DEPENFILE

NOTE: Only the commands:
 - extract-dependence
 - compare-independence
 - extract-log
 - net-stats
 - dump-log
 - dump-pes
 - merge
are so far implemented. But wait for a while :)

The OPTIONS above is zero or more of the following options:

 --help, -h
   Shows this message.

 --log-truncate=N
   Uses only the first N sequences of the log to perform the synthesis. This
   can be very useful for understanding the transformation performed by the
   tool.  When in 'extract-log' mode, N is the number of sequences to generate.

 --log-fraction-truncate=N
   If the log has x sequences, it uses only the first x*(N/100) sequences of it.
   Option incompatible with --log-truncate

 --log-only=N1,N2,...
   Uses only sequences N1, N2, ... of the log to perform the synthesis. The
   argument is a comma-separated list of integers indicating the position in
   the log of the sequences that will be used (first sequence is index 0).
   (NOTE: not yet implemented)

 --log-exclude=N1,N2
   Use all sequences in LOGFILE except those whose index is N1, N2, ...
   (NOTE: not yet implemented)

 --log-negative=LOGFILE
   Provides a negative log to the tool.

 --smt-timeout=N
   When using z3, abort SMT solving after N seconds.

 --no-asserts
   Disables defensive programming verifications.

 --output=OUTPUTPATH
   Save the output of the command to OUTPUTPATH

 --log-unique
   Prior to any usage (or truncation) of the log, it discards duplicate log
   sequences.

 --eq=ID
   Instructs the tool to use the folding equivalence identified by ID. The
   following are available:

   * id
     The identity relation

   * sp-1place
     Merges all events with same label into 1 single transition.
     Merges all conditions into 1 single place.
     Ignores negative information.

   * sp-pre-singleton
     Merges all events with same label into 1 single transition.
     Merges the presets of all events with the same label into 1 single place.
     Ignores negative information.

   * sp-pre-max
     Merges all events with same label into 1 single transition.
     Merges the presets of all events with the same label trying to get the
     largest set of equivalence classes possible, ie, trying to merge as less
     as possible.
     Ignores negative information.

   * sp-smt
     Merges all events with same label into 1 single transition.
     Ignores negative information.
     If it merges two events, it also merges the preset of one with the preset
     of the other. Accepts many options:
     --smt-min-places   : minimum number of places on the final net
     --smt-max-places   : maximum number of places on the final net
     --smt-nr-places    : sets the above two options to the same value
     --smt-pre-distinct : require transition presets to be as large as possible
     --smt-forbid-self  : forbids the presence of self loops

   * sp-smt-post
     Like 'sp-smt' but additionally merging event postsets.
     That is, if two events are merged, then the postset of one is merged with
     the postset of the other.
     Accepts the same options than 'sp-smt', except for --smt-max-places.

   * ip-smt
     Merges all events with same label into 1 single transition.
     Ignores negative information.
     If it merges two events, it also merges the preset of one with the preset
     of the other, and similarly for their postsets.
     Accepts options:
     --smt-min-places   : minimum number of places on the final net
     --smt-pre-distinct : require transition presets to be as large as possible
     --smt-forbid-self  : forbids the presence of self loops

     Like 'sp-smt-post', it is incompatible with options --smt-{max,nr}-places.

   * ev-only
     Merges all events with same label into 1 single transition.
     Merges no condition at all.
     Ignores negative information.
     Mainly for debuging purposes
"""

try :
    from util import *

    import os
    import sys
    import resource
    import networkx
    import argparse
    import random

    import z3
    import ptnet
    import pes

    from log import *
    from folding import *
    from equivalence import *
    from transformations import *
except ImportError, e:
    error_missing_package (e)

if sys.version_info < (2, 7, 0) or sys.version_info >= (3, 0, 0) :
    print ("")
    print ("*** ERROR ***")
    print ("This tool relies on Python 2.7!!")
    print ("Install Python 2.7 or modify the first line of the file 'po-discovery.py' so that it calls Python 2.7")
    print ("")
    sys.exit (1)

class Main :
    def __init__ (self) :

        self.arg_command = ""
        self.arg_log_path = ""
        self.arg_depen_path = ""

        self.arg_log_trunc = None     # integer
        self.arg_log_only = None      # list
        self.arg_log_exclude = None   # list
        self.arg_log_negative = None  # path string

        self.arg_output_path = ""
        self.arg_eq = "id"
        self.arg_no_asserts = False
        self.arg_smt_timeout = 60
        self.arg_smt_min_places = None
        self.arg_smt_max_places = None
        self.arg_smt_pre_distinct = False
        #self.arg_smt_merge_post = False
        self.arg_smt_forbid_self = False

        self.acset = None
        self.log = None
        self.log_negative = None
        self.indep = None
        self.pes = None
        self.meq = None
        self.bp = None
        self.net = None

    def parse_cmdline_args (self) :

        cmd_choices = [
                "compare-independence",
                "extract-dependence",
                "extract-log",
                "net-stats",
                "dump-log",
                "dump-pes",
                "dump-bp",
                "dump-encoding",
                "dump-merge",
                "merge",
                ]
        eq_choices = [
                "id",
                "sp-1place",
                "sp-pre-singleton",
                "sp-pre-max",
                "sp-smt",
                "sp-smt-post",
                "ip-smt",
                "ev-only",
                ]
        p = argparse.ArgumentParser (usage = __doc__, add_help=False)
        #p = argparse.ArgumentParser (usage=__doc__)
        p.add_argument ("-h", "--help", action="store_true")
        #g = p.add_mutually_exclusive_group ()
        p.add_argument ("--log-truncate", type=int)
        p.add_argument ("--log-fraction-truncate", type=float)
        p.add_argument ("--log-unique", action="store_true")
        p.add_argument ("--log-only")
        p.add_argument ("--log-negative")
        p.add_argument ("--log-exclude")
        p.add_argument ("--no-asserts", action="store_true")
        p.add_argument ("--output")
        p.add_argument ("--eq", choices=eq_choices, default="id")
        p.add_argument ("--smt-timeout", type=int, default=60)
        p.add_argument ("--smt-nr-places", type=int)
        p.add_argument ("--smt-min-places", type=int)
        p.add_argument ("--smt-max-places", type=int)
        p.add_argument ("--smt-pre-distinct", action="store_true")
        #p.add_argument ("--smt-merge-post", action="store_true")
        p.add_argument ("--smt-forbid-self", action="store_true")
        #p.add_argument ("--format", choices=["pdf","dot","pnml"])

        p.add_argument ('cmd', metavar="COMMAND", choices=cmd_choices)
        p.add_argument ('log_pnml', metavar="LOGFILE/PNML")
        p.add_argument ('depen', metavar="DEPENFILE", nargs="?", default=None)

        args = p.parse_args ()
        #print "pod: args:", args

        if args.help :
            print __doc__
            sys.exit (0);

        self.arg_command = args.cmd
        self.arg_depen_path = args.depen
        self.arg_eq = args.eq
        self.arg_log_path = args.log_pnml
        self.arg_log_trunc = args.log_truncate
        self.arg_log_trunc_frac = args.log_fraction_truncate
        self.arg_log_unique = args.log_unique
        self.arg_log_negative = args.log_negative
        self.arg_smt_timeout = args.smt_timeout
        self.arg_smt_pre_distinct = args.smt_pre_distinct
        #self.arg_smt_merge_post = args.smt_merge_post
        self.arg_smt_forbid_self = args.smt_forbid_self
        self.arg_no_asserts = args.no_asserts

        # nr-places translates to min-places and max-places
        if args.smt_nr_places != None :
            self.arg_smt_min_places = args.smt_nr_places
            self.arg_smt_max_places = args.smt_nr_places
        else :
            self.arg_smt_min_places = args.smt_min_places
            self.arg_smt_max_places = args.smt_max_places

        # at most one of log-trunc and log-trunc-frac
        if self.arg_log_trunc_frac != None and self.arg_log_trunc != None :
                raise Exception, "At most one of --log-truncate and --log-fraction-truncate"

        if self.arg_command not in \
            ["extract-dependence", "dump-log", "net-stats", "extract-log"] :
            if self.arg_depen_path == None :
                raise Exception, "Expected path to a dependence file"

        if args.log_only != None :
            try :
                self.arg_log_only = [int (x) for x in args.log_only.split (",")]
            except Exception :
                raise Exception, "'%s': expected a comma-separated list of numbers" % (args.log_only)
        if args.log_exclude != None :
            try :
                self.arg_log_exclude = [int (x) for x in args.log_exclude.split (",")]
            except Exception :
                raise Exception, "'%s': expected a comma-separated list of numbers" % (args.log_exclude)

        if args.output != None :
            self.arg_output_path = args.output
        else :
            d = {
                "extract-dependence" : "dependence.txt",
                "extract-log"        : "log.xes",
                "dump-pes"           : "pes.dot",
                "dump-bp"            : "bp.pdf",
                "dump-encoding"      : "encoding.smt2",
                "merge"              : "output.pnml"}
            self.arg_output_path = d.get (self.arg_command, "output.txt")
        for opt in [
                    "arg_command",
                    "arg_depen_path",
                    "arg_no_asserts",
                    "arg_log_path",
                    "arg_log_trunc",
                    "arg_log_trunc_frac",
                    "arg_log_only",
                    "arg_log_exclude",
                    "arg_log_negative",
                    "arg_log_unique",
                    "arg_smt_timeout",
                    "arg_smt_pre_distinct",
                    #"arg_smt_merge_post",
                    "arg_smt_forbid_self",
                    "arg_smt_min_places",
                    "arg_smt_max_places",
                    "arg_eq",
                    "arg_output_path",
                    ] :
            output_pair (sys.stdout, opt, self.__dict__[opt], 20, "pod: ")

    def main (self) :
        self.parse_cmdline_args ()
        #sys.exit (0)

        if self.arg_command == "extract-dependence" :
            self.cmd_extract_dependence ()
        elif self.arg_command == "compare-independence" :
            self.cmd_compare_independence ()
        elif self.arg_command == "extract-log" :
            self.cmd_extract_log ()
        elif self.arg_command == "dump-log" :
            self.cmd_dump_log ()
        elif self.arg_command == "dump-pes" :
            self.cmd_dump_pes ()
        elif self.arg_command == "net-stats" :
            self.cmd_net_stats ()
        elif self.arg_command == "merge" :
            self.cmd_merge ()
        else :
            print 'pod: command not yet implemented'

    def load_coe_pairs (self, path) :
        try :
            print "pod: cmp-indep: loading coe file '%s'" % path
            f = open (path, 'r')
            s = set ()
            for line in f :
                [t1,t2] = line.split ()
                #print "'%s', '%s'" % (t1, t2)
                s.add ((t1, t2))
                s.add ((t2, t1))
            f.close ()
            print 'pod: cmp-indep: done, %d pairs created' % len (s)
            return s
        except Exception as e :
            raise Exception, "'%s': %s" % (path, e)

    def cmd_compare_independence (self) :
        # load the two nets
        net1 = load_net (self.arg_log_path, "pnml", "pod: cmp-indep: ")
        net2 = load_net (self.arg_depen_path, "pnml", "pod: cmp-indep: ")

        if False :
            path = self.arg_log_path[:-4] + "coe"
            coe1 = self.load_coe_pairs (path)
            path = self.arg_depen_path[:-4] + "coe"
            coe2 = self.load_coe_pairs (path)

        # construct independence relations for both
        print "pod: cmp-indep: extracting dependence relations from the nets ..."
        indep1 = Indep ()
        indep2 = Indep ()
        indep1.from_net_names (net1)
        indep2.from_net_names (net2)
        print "pod: cmp-indep: done"
        print '---------------------------------'
        print "pod: cmp-indep: net1 is '%s'" % self.arg_log_path
        print "pod: cmp-indep: net2 is '%s'" % self.arg_depen_path
        names1 = set (indep1.domain.tab.keys ())
        names2 = set (indep2.domain.tab.keys ())
        if names1 != names2 :
            l = list (names1 - names2)
            if len (l) :
                print "pod: cmp-indep: WARNING: net1 - net2: %s" % l
            l = list (names2 - names1)
            if len (l) :
                print "pod: cmp-indep: WARNING: net2 - net1: %s" % l

        indep1_pairs = set ((a1.name, a2.name) for a1,a2 in indep1)
        indep2_pairs = set ((a1.name, a2.name) for a1,a2 in indep2)
        inter = indep1_pairs & indep2_pairs
        d1sq = len (indep1.domain) * len (indep1.domain)
        d2sq = len (indep2.domain) * len (indep2.domain)
        x = len (indep1_pairs)
        y = len (indep2_pairs)
        z = len (inter)

        print 'pod: cmp-indep: net1: dep / indep = %3d / %3d pairs' % (d1sq - x, x)
        print 'pod: cmp-indep: net2: dep / indep = %3d / %3d pairs' % (d2sq - y, y)
        print 'pod: cmp-indep: inters. of indep. rels. : %d pairs' % z
        print '---------------------------------'
        print 'pod: cmp-indep: ratios: indep1 in indep2: %.2f' % (float (z) / x)
        print 'pod: cmp-indep: ratios: indep2 in indep1: %.2f' % (float (z) / y)

        if False :
            print '---------------------------------'
            indep1_pairs &= coe1
            indep2_pairs &= coe2
            inter = indep1_pairs & indep2_pairs
            x = len (indep1_pairs)
            y = len (indep2_pairs)
            z = len (inter)
            print 'pod: cmp-indep: net1: indep & coe = %3d pairs' % x
            print 'pod: cmp-indep: net2: indep & coe = %3d pairs' % y
            print 'pod: cmp-indep: net2: intersection: %3d pairs' % z
            print 'pod: cmp-indep: new ratios: indep1 in indep2: %.2f' % (float (z) / x)
            print 'pod: cmp-indep: new ratios: indep2 in indep1: %.2f' % (float (z) / y)

    def cmd_extract_dependence (self) :

        # load the net
        net = load_net (self.arg_log_path, "pnml", "pod: extract-dep: ")

        # create a dependence relation and fill it from the net
        dep = Depen ()
        print "pod: extract-dep: extracting dependence relation ..."
        dep.from_net_names (net)

        # XXX - hack: ensure that the relation is "positively" stored
        assert (dep.negate == False)
        print "pod: extract-dep: done, %d different actions, %d pairs" \
                % (len (dep.domain), len (dep.pairs))

        # warnings
        s = set ()
        for t in net.trans :
            if " " in t.name :
                print "pod: extract-dep: WARNING: transition '%s' contains spaces in the name" % t.name
            if t.name in s :
                print "pod: extract-dep: WARNING: 2 transition with same name: '%s'" % t.name
            s.add (t.name)

        # save
        try :
            f = open (self.arg_output_path, "w")
            f.write ("# Dependence relation on transition names, automatically extracted from:\n")
            f.write ("# %s\n" % self.arg_log_path)
            for (a1, a2) in dep.pairs :
                f.write ("%s %s\n" % (a1.name, a2.name))
            f.close ()
        except Exception as (e, m) :
            raise Exception, "'%s': %s" % (self.arg_output_path, m)
        print "pod: extract-dep: output saved to '%s'" % self.arg_output_path

    def cmd_extract_log (self) :
        # load the net
        net = load_net (self.arg_log_path, "pnml", "pod: extract-log: ")
        acset = ActionSet
        log = Log ()

        nr_seqs = self.arg_log_trunc
        if nr_seqs == None : nr_seqs = 100
        min_len = 2
        max_len = 30

        print "pod: extract-log: generating %d random runs, min/max len = %d/%d" \
                % (nr_seqs, min_len, max_len)
        while True :
            for i in xrange (20) :
                le = random.randrange (min_len, max_len + 1)
                run = net.generate_random_run (le)
                run = [t.name for t in run]
                log.add_seq_from_names (run)
            log.discard_duplicates ()
            print 'pod: extract-log: %s' % repr (log)
            if len (log) >= nr_seqs :
                log.truncate (nr_seqs)
                break
        print 'pod: extract-log: done, removing duplicates'
        print 'pod: extract-log: result:', repr (log)
        print 'pod: extract-log: first 10 sequences:'

        i = 0
        print " Idx Len Sequence"
        print "---- --- ----------------------------------------"
        for seq in log :
            print "%4d %3d %s" % (i, len (seq), long_list (seq, 8))
            i += 1
            if i >= 10 : break

        # save
        try :
            log.write (self.arg_output_path, 'xes')
        except Exception as (e, m) :
            raise Exception, "'%s': %s" % (self.arg_output_path, m)
        print "pod: extract-log: output saved to '%s'" % self.arg_output_path

    def cmd_dump_log (self) :
        # load the positive and negative logs
        self.__load_all_logs ()

        print "pod: logs: dumping the positive log:\n"

        i = 0
        print " Idx Len Sequence"
        print "---- --- ----------------------------------------"
        for seq in self.log_both :
            print "%4d %3d %s" % (i, len (seq), seq)
            i += 1

    def cmd_net_stats (self) :
        # load the net
        net = load_net (self.arg_log_path, "pnml", "pod: stats: ")

        d = {}
        d["net.transitions"] = len (net.trans)
        d["net.places"] = len (net.places)

        # min, max, avg preset/postsets size for transitions
        pre_mi, pre_ma, pre_av = 9999999999, 0, 0
        post_mi, post_ma, post_av = 9999999999, 0, 0
        for t in net.trans :
            if len (t.pre) < pre_mi : pre_mi = len (t.pre)
            if len (t.pre) > pre_ma : pre_ma = len (t.pre)
            pre_av += len (t.pre)
            if len (t.post) < post_mi : post_mi = len (t.post)
            if len (t.post) > post_ma : post_ma = len (t.post)
            post_av += len (t.post)

        spre  = "%d, %d, %.2f" % (pre_mi, pre_ma, pre_av / float (len (net.trans)))
        spost = "%d, %d, %.2f" % (post_mi, post_ma, post_av / float (len (net.trans)))

        d["trans.pre  size min/max/avg"] = spre
        d["trans.post size min/max/avg"] = spost

        # min, max, avg preset/postsets size for places
        pre_mi, pre_ma, pre_av = 9999999999, 0, 0
        post_mi, post_ma, post_av = 9999999999, 0, 0
        for p in net.places :
            if len (p.pre) < pre_mi : pre_mi = len (p.pre)
            if len (p.pre) > pre_ma : pre_ma = len (p.pre)
            pre_av += len (p.pre)
            if len (p.post) < post_mi : post_mi = len (p.post)
            if len (p.post) > post_ma : post_ma = len (p.post)
            post_av += len (p.post)

        spre  = "%d, %d, %.2f" % (pre_mi, pre_ma, pre_av / float (len (net.places)))
        spost = "%d, %d, %.2f" % (post_mi, post_ma, post_av / float (len (net.places)))

        d["place.pre  size min/max/avg"] = spre
        d["place.post size min/max/avg"] = spost

        s = ""
        for t in net.trans :
            for p,w in t.weight_pre.items () :
                if w != 1 :
                    s = "no, '%s' -> '%s' has weight %d" % (repr (p), repr (t), w)
            for p,w in t.weight_post.items () :
                if w != 1 :
                    s = "no, '%s' -> '%s' has weight %d" % (repr (t), repr (p), w)
            assert (len (t.cont) == 0)
        for p in net.places :
            for t,w in p.weight_pre.items () :
                if w != 1 :
                    s = "no, '%s' -> '%s' has weight %d" % (repr (t), repr (p), w)
            for t,w in p.weight_post.items () :
                if w != 1 :
                    s = "no, '%s' -> '%s' has weight %d" % (repr (p), repr (t), w)
            assert (len (p.cont) == 0)
        if len (s) == 0 :
            s = "yes, all arc weights are 1"
        d["net.is-ordinary"] = s

        print
        output_dict (sys.stdout, d, "")

    def cmd_dump_pes (self) :
        # same as dump log but with the pes
        # load the positive and negative logs
        self.__load_all_logs ()

        # load the independence relation
        self.__load_indep ()

        # build the PES
        print "pod: building the PES from the logs..."
        self.pes = log_to_pes (self.log_both, self.indep)

        print "pod: logs: dumping the PES in dot format ..."
        # save the dot file
        try :
            f = open (self.arg_output_path, "w")
            self.pes.write (f, 'dot')
            f.close ()
        except Exception as (e, m) :
            raise Exception, "'%s': %s" % (self.arg_output_path, m)
        print "pod: result PES saved to '%s'" % self.arg_output_path

    def cmd_merge (self) :

        # load the positive and negative logs
        self.__load_all_logs ()

        # load the independence relation
        self.__load_indep ()

        # build the PES
        print "pod: building the PES from the logs..."
        self.pes = log_to_pes (self.log_both, self.indep)

        #print 'indep', self.indep
        #print 'es', es
        #print 'log positive', repr (self.log)
        #print 'log negative', repr (self.log_negative)
        #print 'log both', repr (self.log_both)

        # build the BP
        print "pod: building the BP from the PES..."
        want_max_conds = self.arg_eq == 'sp-smt-post' or self.arg_eq == 'ip-smt'
        self.bp = pes_to_bp (self.pes, self.indep, want_max_conds)

        # merge the BP into a net
        self.__merge ()

        # save the net
        try :
            f = open (self.arg_output_path, "w")
            self.net.write (f, 'pnml')
            f.close ()
        except Exception as (e, m) :
            raise Exception, "'%s': %s" % (self.arg_output_path, m)
        print "pod: result net saved to '%s'" % self.arg_output_path

    def __load_all_logs (self) :
        # create a new action set
        self.acset = ActionSet ()

        # load the positive log
        print "pod: logs: loading log with positive information"
        self.log = self.__load_log (self.arg_log_path, \
                "pod: logs: positive: ")

        # discard duplicated sequences if requested
        if self.arg_log_unique :
            print "pod: logs: positive: discarding duplicated sequences"
            self.log.discard_duplicates ()
            nre = sum (len (seq) for seq in self.log.traces)
            print 'pod: logs: positive: new log: %s' % repr (self.log)

        # translate --log-trunc-frac to --log-trunc
        assert (len (self.log) == len (self.log.traces))
        assert (self.arg_log_trunc_frac == None or self.arg_log_trunc == None)
        if self.arg_log_trunc_frac :
            print "pod: logs: positive: truncating: keeping only first %.2f%% log seqs" % \
                    self.arg_log_trunc_frac
            n = len (self.log) * float (self.arg_log_trunc_frac) / 100
            self.arg_log_trunc = int (n)

        # truncate the log according to options --log-{trunc,only,exclude,trunc-fraction}
        if self.arg_log_trunc != None :
            print "pod: logs: positive: truncating: keeping only first %d seq" \
                % self.arg_log_trunc
            self.log.truncate (self.arg_log_trunc)
            nre = sum (len (seq) for seq in self.log.traces)
            print 'pod: logs: positive: new log:', repr (self.log)
        if self.arg_log_only != None or self.arg_log_exclude != None:
            raise NotImplementedError

        # create another log to store positive and negative information and
        # set its actionset to the be the same as the positive log, so all
        # the three logs will share the same ActionSet
        self.log_both = self.log.clone ()
        self.log_both.actionset = self.acset

        # load negative and fill log_both
        if self.arg_log_negative != None :
            print "pod: logs: loading log with negative information"
            self.log_negative = self.__load_log (self.arg_log_negative, \
                    "pod: logs: negative: ")
            self.log_both.union (self.log_negative)

    def __load_log (self, path, prefix="pod: ") :
        log = Log (self.acset)
        try :
            size = os.path.getsize (path) / (1024 * 1024.0)
            print "%sloading log file '%s' (%.1fM), assuming XES format" % (prefix, path, size)
            f = open (path, 'r')
            log.read (f, 'xes')
            f.close ()
        except Exception as e:
            raise Exception, "'%s': %s" % (path, e)
        nre = sum (len (seq) for seq in log.traces)
        print '%sdone, %s' % (prefix, repr (log))
        return log

    def __load_indep (self) :

        # load the file arg_depen_path into a Depen object, we share the
        # same ActionSet than all the three logs
        dep = Depen (self.acset)
        try :
            print "pod: loading dependence from file '%s'" % self.arg_depen_path
            f = open (self.arg_depen_path, 'r')
            i = 0
            for line in f :
                i += 1
                line = line.lstrip ()
                if len (line) == 0 : continue
                if line[0] == '#' : continue
                ls = line.split ()
                if len (ls) != 2 :
                    raise Exception, "line %d: expected two words separated by spaces"
                a1 = self.acset.lookup (ls[0])
                if a1 == None :
                    print "pod: line %d: NOTICE: new action '%s' not happening in the logs" % (i, ls[0])
                    a1 = self.acset.lookup_or_create (ls[0])
                a2 = self.acset.lookup (ls[1])
                if a2 == None :
                    print "pod: line %d: NOTICE: new action '%s' not happening in the logs" % (i, ls[1])
                    a2 = self.acset.lookup_or_create (ls[1])
                dep.set (a1, a2)
            f.close ()
        except Exception as (e, m) :
            raise Exception, "'%s': %s" % (self.arg_depen_path, m)
        print 'pod: done, %d pairs, %d distinct actions now known' \
                % (len (dep), len (self.acset))

        print 'pod: validating reflexivity'
        try :
            dep.check_is_dependence ()
        except Exception as e:
            print 'pod: ERROR: %s' % e
            print "pod: are you sure '%s' is a dependence relation for '%s'?" \
                    % (self.arg_depen_path, self.arg_log_path)
            raise e
        self.indep = Indep ()
        self.indep.from_depen (dep)

    def __merge (self) :

        # construir el encoding
        # pasarselo a z3
        # construir la equivalencia
        # fusionar

        print "pod: folding the BP into a net"
        print "pod: bp > net: using equivalence '%s'" % self.arg_eq

        # selecting the folding equivalence
        if self.arg_eq == "id" :
            domain = set (self.bp.events) | set (self.bp.conds)
            self.meq = IdentityMergingEquivalence (domain)
        elif self.arg_eq == "sp-1place" :
            self.meq = Merging_equivalence_factory.sp_one_place (self.bp)
        elif self.arg_eq == "sp-pre-singleton" :
            self.meq = Merging_equivalence_factory.sp_pre_singleton (self.bp)
        elif self.arg_eq == "sp-pre-max" :
            self.meq = Merging_equivalence_factory.sp_pre_max (self.bp)
        elif self.arg_eq == "sp-smt" :
            self.meq = Merging_equivalence_factory.sp_smt (self.bp, \
                    self.arg_smt_timeout * 1000,
                    self.arg_smt_min_places,
                    self.arg_smt_max_places,
                    self.arg_smt_forbid_self,
                    self.arg_smt_pre_distinct,
                    False)
        elif self.arg_eq == "sp-smt-post" :
            self.meq = Merging_equivalence_factory.sp_smt (self.bp, \
                    self.arg_smt_timeout * 1000,
                    self.arg_smt_min_places,
                    self.arg_smt_max_places,
                    self.arg_smt_forbid_self,
                    self.arg_smt_pre_distinct,
                    True)
        elif self.arg_eq == "ip-smt" :
            self.meq = Merging_equivalence_factory.ip_smt (self.bp, self.indep, \
                    self.arg_smt_timeout * 1000,
                    self.arg_smt_min_places,
                    self.arg_smt_max_places,
                    self.arg_smt_forbid_self,
                    self.arg_smt_pre_distinct)
        elif self.arg_eq == "ev-only" :
            self.meq = Merging_equivalence_factory.ev_only (self.bp)
        else :
            raise AssertionError, "Internal inconsistency"

        # if the previous was unable to find a folding equivalence, abort
        if self.meq == None :
            raise Exception, "Couldn't find a folding equivalence with requested characteristics, aborting"

        # the merge equivalence is meq, folding the BP into a net
        (net, e2t, c2p) = bp_to_net (self.bp, self.meq)
        self.net = net

        # verify transformations
        if self.arg_no_asserts or self.arg_eq == "ev-only":
            print 'pod: bp > net: asserting correctness: skipping !!'
        else :
            bp_to_net_assert_sp (self.bp, self.meq, e2t, c2p)

# vi:ts=4:sw=4:et:
