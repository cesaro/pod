
import os

import ptnet

def output_dict (f, d, prefix='podisc: ') :
    n = max ([len (k) for k in d])
    l = list (d)
    l.sort ()
    for k in l :
        output (f, k, d[k], n, prefix)

def output_pair (f, k, v, n, prefix='', fmt='%s') :
    f.write (prefix + ('%-*s : ' + fmt + '\n') % (n, k, v))

def load_net (path, fmt="pnml", prefix="pod: ") :
    net = ptnet.Net ()
    try :
        size = os.path.getsize (path) / (1024 * 1024.0)
        print "%sloading net file '%s' (%.1fM)" % (prefix, path, size)
        f = open (path, 'r')
        net.read (f, fmt=fmt)
        f.close ()
    except Exception as (e, m) :
        raise Exception, "'%s': %s" % (path, m)
    print "%sdone, %d transitions, %d places" % (prefix, len (net.trans), len (net.places))
    print "%sfirst 5 transitions are:" % prefix
    for t in net.trans[:5] :
        print "%s%s" % (prefix, str (t))
    return net

def error_missing_package (exception) :
    print 'ERROR!'
    print 'It seems that your python installation is missing some package.'
    print 'This tool requires, among others, argparse, and networkx'
    print 'The runtime reported the following error:\n\n', str (exception), '\n'
    print 'You might want to use "easy_install --user PACKAGE"'
    print ''
    import sys
    sys.exit (1)

def avg_iter (it) :
    s = 0
    i = 0
    for x in it :
        s += x
        i += 1
    return float (s) / i

# vi:ts=4:sw=4:et:
