MACHINE Queens_midQ //n can be provided by the -card Q n command in probcli
SETS Q
DEFINITIONS abs(x,y) == (IF x>=y THEN x-y ELSE y-x END)
CONSTANTS n,queens
PROPERTIES
 /* n = 71 & */
 n = card(Q) &
 queens : 1..n >-> 1..n /* for each column the row in which the queen is in */
 &
 !(q1,q2).(q1:1..n & q2:2..n & q1/=q2 => abs(q1,q2) /= abs(queens(q1),queens(q2)))
END
