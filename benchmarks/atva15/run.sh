#!/bin/bash

tune_parameters ()
{
	case "$PREFIX" in
	"a22" )
		MIN=19
		;;

	"a32" )
		MIN=32
		;;

	"a42" )
		MIN=40
		;;

	"t32" )
		MIN=31
		;;

	"Angiogenesis-PT-01" )
		MIN=32
		;;

	"complex" )
		MIN=12
		;;

	"confDimBlocking" )
		MIN=10
		;;

	"cycles5_2" )
		MIN=16
		;;

	"DatabaseWithMutex-PT-02" )
		MIN=32
		;;

	"dc" )
		MIN=27
		;;

	"Peterson-PT-2" )
		MIN=51
		;;

	*)
		echo "WARNING: leaving --smt-min-places to default of $MIN"
		;;
	esac
}

main ()
{
	#set -x

	POD=../../src/pod.py
	for XES in *xes; do
		PREFIX=`echo "$XES" | sed 's/.xes$//'`
		DEP=$PREFIX.dep
		ORIG=$PREFIX.pnml
		OUTPUT=$XES.disc.pnml
		STDOUT=$XES.disc.stdout

		# these might be modified in tune_parameters
		EQ=sp-smt
		MIN=5
		TIMEOUT=40

		tune_parameters

		echo
		echo
		echo 'xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'
		echo "Processing '$XES'"

		set -x
		$POD discover --no-ass --eq=$EQ --smt-timeout=$TIMEOUT --smt-min=$MIN --output=$OUTPUT  $XES $DEP > $STDOUT 2>&1
		EXITSTAT=$?
		set +x
		if test "$EXITSTAT" != "0"; then
			echo "ERROR: pod returned a non-zero exit state"
			exit 1
		fi

		echo
		echo "Statistics of the discovered net"
		echo "================================"
		$POD net-stats $OUTPUT | grep -v is-ordi | grep -v '^pod'

		echo
		echo "Independence ratios"
		echo "==================="
		$POD compare-independence $ORIG $OUTPUT | grep "cmp-indep: net1 is " -A 200

	done
}

main
