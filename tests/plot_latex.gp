set terminal latex
set output 'as.tex'
set xlabel 'Input size (thousands of "a"s)'
set ylabel 'Time (sec)'
set title 'Matching (a + b + ab)* with sequences of "a"s'
plot 'as.dat' using 1:2 title 're' with linespoints,\
     'as.dat' using 1:3 title 'haskell-regexp' with linespoints,\
     'as.dat' using 1:4 title 'grep' with linespoints,\
     'as.dat' using 1:5 title 'verigrep' with linespoints

set output 'abs.tex'
set title 'Matching (a + b + ab)* with sequences of "ab"s'
plot 'abs.dat' using 1:2 title 're' with linespoints,\
     'abs.dat' using 1:3 title 'haskell-regexp' with linespoints,\
     'abs.dat' using 1:4 title 'grep' with linespoints,\
     'abs.dat' using 1:5 title 'verigrep' with linespoints
