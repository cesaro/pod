#/usr/bin/env
import ptnet

def test1 () :
    n = ptnet.Net (True)
    n.read (sys.stdin, 'pnml')
    n.write (sys.stdout, 'pnml')

if __name__ == '__main__' :
    test1 ()
