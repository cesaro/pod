
def print_stats (f, d, prefix='podisc: ') :
    n = max ([len (k) for k in d])
    l = list (d)
    l.sort ()
    for k in l :
        output (f, k, d[k], n, prefix)

def output (f, k, v, n, prefix='', fmt='%s') :
    f.write (prefix + ('%-*s : ' + fmt + '\n') % (n, k, v))

def error_missing_package (exception) :
    print 'ERROR!'
    print 'It seems that your python installation is missing some package.'
    print 'This tool requires, among others, argparse, and networkx'
    print 'The runtime reported the following error:\n\n', str (exception), '\n'
    print 'You might want to use "easy_install --user PACKAGE"'
    raise exception
