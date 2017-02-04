#!/bin/bash

if [ ! -f ./verigrep/verigrep ]
then
   mkdir ./verigrep
   mv ../dist/Main ./verigrep/verigrep
fi   

if [ ! -f ./haskell-regexp/hregexp ]
then
   cd ./haskell-regex
   stack ghc -- --make ./app/Main -o hregexp
   cd ..
fi

if [ ! -f ./nc/nc ]
then
    cd ./nc
    g++ -o nc nc.cpp
    cd ..
fi    

for i in $(seq 1 10)
do
    N=$(($i*20000))
    ./nc/nc $N a > $(($i*20))ka.txt
    ./nc/nc $(($N/2)) ab > $(($i*10))kab.txt
done

PROGS=(re2 haskell-regexp grep verigrep)

declare -a COMMANDS=(
    "/usr/local/bin/gtime -f \"%e\" ./re2/re2 \"(a + b + ab)*\" < \$N"
    "/usr/local/bin/gtime -f \"%e\" ./haskell-regex/hregexp \"(a|b|ab)*\" < \$N"
    "/usr/local/bin/gtime -f \"%e\" grep -x -E \"(a|b|ab)*\" \$N"
    "/usr/local/bin/gtime -f \"%e\" ./verigrep/verigrep -B \"(a + b + ab)*\" \$N"
    "/usr/local/bin/gtime -f \"%e\" ./verigrep/verigrep -A \"(a + b + ab)*\" \$N"
)

for c in a ab
do
    echo -n \#thousands of $c's|'

    for p in ${PROGS[@]}
    do
        echo -n $p'|'
    done
    echo -n -e '\n'

    for i in $(seq 1 10)
    do
        N=$(($i*20/${#c}))k$c".txt"
        echo -n ${N%k*}
        for ((p=0;p<${#PROGS[@]};p++))
        do
            echo -n -e '\t'
            echo -n $(eval ${COMMANDS[$p]} 2>&1 1>/dev/null)
        done
        echo -n -e '\n'

    done
    echo -ne "\n"

done

rm *ka.txt
rm *kab.txt
