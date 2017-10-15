MACHINE Queens_arrQ //n can be provided by the -card Q n command in probcli
SETS Q
CONSTANTS n,queens
PROPERTIES
 n = card(Q) &
 queens : (1..n) --> (1..n)
 &
 !(p,q). (p|->q : queens => !i.(i: (-n..n)-{0} => p+i|->q /: queens & p+i|->q+i /: queens & p+i|->q-i /: queens))
END
