MACHINE Queens_con//n can be provided by the -card Q n command in probcli
SETS Q
DEFINITIONS SET_PREF_RANDOMISE_ENUMERATION_ORDER == TRUE
CONSTANTS n,queens
PROPERTIES
 /* n = 480 & */
 n = card(Q) &
 queens : 1..n >-> 1..n /* for each column the row in which the queen is in */
 &
 !(q1,q2).(q1:1..n & q2:2..n & q2>q1
    => queens(q1)+q1 /= queens(q2)+q2 & queens(q1)-q1 /= queens(q2)-q2)
END

/* This is just the original B machine with the equations rearranged */