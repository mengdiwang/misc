print "*** Boxplot tcas ***"

set style fill solid 0.25 border -1
set style boxplot outliers pointtype 7
set style data boxplot
set boxwidth  0.5
set pointsize 0.5

unset key
set border 2
set xtics ("RP" 1, "CAUT-CREST" 2, "CAUT-KLEE" 3, "Hybrid" 4) scale 0.0
set xtics nomirror
set ytics nomirror
set yrange [0:9.0]

set term post eps color
set output "tcas_df_test.eps"

plot 'boxplot-tcas.log' using (1):(4.0*$2), '' using (2):(4.3*$3), '' using (3):(6.78*$4), '' using (4):(3.78*$5)

pause -1 'Hit <cr> to continue: Compare sub-datasets'




