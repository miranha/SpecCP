MACHINE Queens_prm //n can be provided by the -card Q n command in probcli
SETS Q
/* can be solved for n=480:
  MacBook Air 2.2Ghz i7, 27.4.2017: 
    % Runtime for SOLUTION for SETUP_CONSTANTS: 13700 ms (walltime: 25930 ms)
    % Runtime for SOLUTION for SETUP_CONSTANTS: 12570 ms (walltime: 21570 ms)
*/
DEFINITIONS SET_PREF_RANDOMISE_ENUMERATION_ORDER == TRUE
CONSTANTS n,queens
PROPERTIES
 /* n = 480 & */
 n = card(Q) &
 queens : perm(1..n) /* for each column the row in which the queen is in */
 &
 !(q1,q2).(q1:1..n & q2:2..n & q2>q1
    => queens(q1)+q2-q1 /= queens(q2) & queens(q1)-q2+q1 /= queens(q2))
END
