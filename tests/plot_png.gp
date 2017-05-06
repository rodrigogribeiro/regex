set terminal png size 550,430 enhanced
set output 'as.png'
set xlabel 'Input size (thousands of "a"s)'
set ylabel 'Time (sec)'
set title 'Matching (a + b + ab)* with sequences of "a"s'
plot 'as.dat' using 1:2 title 're2' with linespoints,\
       'as.dat' using 1:3 title 'haskell-regexp' with linespoints,\
       'as.dat' using 1:4 title 'grep' with linespoints,\
       'as.dat' using 1:5 title 'Brzozowski' with linespoints,\
       'as.dat' using 1:6 title 'Antimirov' with linespoints, \
       'as.dat' using 1:7 title 'Bit-codes' with linespoints
set output 'abs.png'
set title 'Matching (a + b + ab)* with sequences of "ab"s'
plot 'abs.dat' using 1:2 title 're2' with linespoints,\
       'abs.dat' using 1:3 title 'haskell-regexp' with linespoints,\
       'abs.dat' using 1:4 title 'grep' with linespoints,\
       'abs.dat' using 1:5 title 'Brzozowski' with linespoints,\
       'abs.dat' using 1:6 title 'Antimirov' with linespoints, \
       'abs.dat' using 1:7 title 'Bit-codes' with linespoints       