theory NQueens_CSP
imports Main CSP
begin

(* The general problem *)

definition board0 :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "board0 n b = (n\<ge>0 \<and> b \<subseteq> {1..n}\<times>{1..n} \<and> (int (card b) = n))"

definition safe0 :: "int \<Rightarrow> int \<Rightarrow> int rel \<Rightarrow> bool" where
  "safe0 p q b = (\<forall>i. i\<noteq>0 \<longrightarrow> (p+i,q)\<notin>b \<and> (p,q+i)\<notin>b \<and> (p+i,q+i)\<notin>b \<and> (p+i,q-i)\<notin>b)"

definition nqueens0 :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "nqueens0 n b = (board0 n b \<and> (\<forall>p q. (p,q)\<in>b \<longrightarrow> safe0 p q b))"

(* The problem with all queens preassigned to different columns, *)
(* that is, no queen can vertically attack another. *)
(* This makes b an array! *)

definition board1 :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "board1 n b = (n\<ge>0 \<and> array n n b)"

definition safe1 :: "int \<Rightarrow> int \<Rightarrow> int rel \<Rightarrow> bool" where
  "safe1 p q b = (\<forall>i. i\<noteq>0 \<longrightarrow> (p+i,q)\<notin>b \<and> (p+i,q+i)\<notin>b \<and> (p+i,q-i)\<notin>b)"

definition nqueens1 :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "nqueens1 n b = (board1 n b \<and> (\<forall>p q. (p,q)\<in>b \<longrightarrow> safe1 p q b))"

lemma from0to1: "nqueens1 n b \<Longrightarrow> nqueens0 n b" 
apply (simp add: nqueens1_def nqueens0_def safe1_def safe0_def board1_def board0_def)
by (smt Domain.intros Range.RangeI array_def arraycard mem_Sigma_iff subrelI subsetCE)

(* The safety constraints split. *)
(* Constraint a: No queen can horizontally attack another. *)
(* Constraint 2: No queen can diagonally attack another. *)

definition board2 :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "board2 n b = board1 n b"

definition safe2a :: "int rel \<Rightarrow> bool" where
  "safe2a b = allDifferent b"

definition safe2b :: "int rel \<Rightarrow> bool" where
  "safe2b b = (\<forall>p q r s. (p,q)\<in>b \<and> (r,s)\<in>b \<and> p\<noteq>r \<longrightarrow> abs (p-r) \<noteq> abs (q-s))"

definition safe2b_impl :: "int rel \<Rightarrow> bool" where
  "safe2b_impl b = (\<forall>p r. p\<in>Domain b \<and> r\<in>Domain b \<and> p\<noteq>r \<longrightarrow> abs (p-r) \<noteq> abs ((valof b p)-(valof b r)))"

lemma safe2bimpl: "array n n b \<Longrightarrow> (safe2b b \<longleftrightarrow> safe2b_impl b)"
apply (simp add: safe2b_def safe2b_impl_def)
by (metis Domain.DomainI valofarr valofarrev)

definition nqueens2 :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "nqueens2 n b = (board2 n b \<and> safe2a b \<and> safe2b b)"

lemma nqueens2_impl: "nqueens2 n b \<longleftrightarrow> (board2 n b \<and> safe2a b \<and> safe2b_impl b)"
using board1_def board2_def nqueens2_def safe2bimpl by blast

lemma safe1dcmp: "\<lbrakk>\<forall>p q. (p, q) \<in> b \<longrightarrow> (\<forall>i. i\<noteq>0 \<longrightarrow> (p+i,q)\<notin>b); \<forall>p q. (p, q) \<in> b \<longrightarrow> (\<forall>i. i\<noteq>0 \<longrightarrow> (p+i,q+i)\<notin>b); \<forall>p q. (p, q) \<in> b \<longrightarrow> (\<forall>i. i\<noteq>0 \<longrightarrow> (p+i,q-i)\<notin>b)\<rbrakk> \<Longrightarrow> (\<forall>p q. (p, q) \<in> b \<longrightarrow> safe1 p q b)"
by (simp add: safe1_def)

lemma from1to2: "nqueens2 n b \<longrightarrow> nqueens1 n b"
proof (simp add: nqueens2_def nqueens1_def board2_def, standard)
  {
  fix p q
  assume b1: "board1 n b"
     and s1: "safe2a b"
     and s2: "safe2b b"
     and b2: "(p, q) \<in> b"
  hence "\<forall>p q r s. (p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> q \<noteq> s" 
  by (simp add: safe2a_def allDifferent_def)
  hence s3: "\<forall>i. i \<noteq> 0 \<longrightarrow> (p + i, q) \<notin> b" using b2 by force
  have s4: "\<forall>p q r s. (p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> \<bar>p - r\<bar> \<noteq> \<bar>q - s\<bar>" 
  using s2 safe2b_def by blast
  hence "\<forall>i. i \<noteq> 0 \<longrightarrow> (p + i, q) \<notin> b \<and> (p + i, q + i) \<notin> b \<and> (p + i, q - i) \<notin> b" 
  using s3 using b2 by fastforce
  hence "safe1 p q b" by (simp add: safe1_def)
  }
  thus "board1 n b \<and> safe2a b \<and> safe2b b \<Longrightarrow> \<forall>p q. (p, q) \<in> b \<longrightarrow> safe1 p q b" by blast
qed

definition board3 :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "board3 n b = board2 n b"

definition safe3a :: "int rel \<Rightarrow> bool" where
  "safe3a b = safe2a b"

definition safe3b :: "int rel \<Rightarrow> bool" where
  "safe3b b = (\<forall>p q r s. (p,q)\<in>b \<and> (r,s)\<in>b \<and> p\<noteq>r \<longrightarrow> q+p\<noteq>s+r)"

lemma safead3b: "safe3b b \<longleftrightarrow> allDifferent {(x,y). \<exists>z. (x,z)\<in>b \<and> y=z+x}"
proof (simp add: safe3b_def allDifferent_def array_def, standard)
show "\<forall>p q r s. (p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> q + p \<noteq> s + r \<Longrightarrow>
    \<forall>x y p q. (\<exists>z. (x, z) \<in> b \<and> p = z + x) \<and> (\<exists>z. (y, z) \<in> b \<and> q = z + y) \<and> x \<noteq> y \<longrightarrow> p \<noteq> q"
by smt
next
  {
  fix p q r s
  assume h2: "\<forall>x y p q. (\<exists>z. (x, z) \<in> b \<and> p = x + z) \<and> (\<exists>z. (y, z) \<in> b \<and> q = y + z) \<and> x \<noteq> y \<longrightarrow> p \<noteq> q"
     and h3: "(p, q) \<in> b"
     and h4: "(r, s) \<in> b"
     and h5: "p \<noteq> r"
  hence "\<forall>p0 q0. (\<exists>z. (p, z) \<in> b \<and> p0 = p + z) \<and> (\<exists>z. (r, z) \<in> b \<and> q0 = r + z) \<and> p \<noteq> r \<longrightarrow> p0 \<noteq> q0" by blast
  hence "\<forall>p0 q0. ((p, q) \<in> b \<and> p0 = p + q) \<and> ((r, s) \<in> b \<and> q0 = r + s) \<and> p \<noteq> r \<longrightarrow> p0 \<noteq> q0" by blast
  hence "(p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> p+q \<noteq> r+s" by blast
  hence "p + q \<noteq> r + s" using h3 h4 h5 by blast
  }
  thus "\<forall>x y p q. (\<exists>z. (x, z) \<in> b \<and> p = z + x) \<and> (\<exists>z. (y, z) \<in> b \<and> q = z + y) \<and> x \<noteq> y \<longrightarrow> p \<noteq> q \<Longrightarrow>
    \<forall>p q r s. (p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> q + p \<noteq> s + r" by blast
qed

definition safe3c :: "int rel \<Rightarrow> bool" where
  "safe3c b = (\<forall>p q r s. (p,q)\<in>b \<and> (r,s)\<in>b \<and> p\<noteq>r \<longrightarrow> q-p\<noteq>s-r)"

lemma safead3c: "safe3c b \<longleftrightarrow> allDifferent {(x,y). \<exists>z. (x,z)\<in>b \<and> y=z-x}"
proof (simp add: safe3c_def allDifferent_def array_def, standard)
show "\<forall>p q r s. (p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> q - p \<noteq> s - r \<Longrightarrow>
    \<forall>x y p q. (\<exists>z. (x, z) \<in> b \<and> p = z - x) \<and> (\<exists>z. (y, z) \<in> b \<and> q = z - y) \<and> x \<noteq> y \<longrightarrow> p \<noteq> q"
by smt
next
  {
  fix p q r s
  assume h2: "\<forall>x y p q. (\<exists>z. (x, z) \<in> b \<and> p = z - x) \<and> (\<exists>z. (y, z) \<in> b \<and> q = z - y) \<and> x \<noteq> y \<longrightarrow> p \<noteq> q"
     and h3: "(p, q) \<in> b"
     and h4: "(r, s) \<in> b"
     and h5: "p \<noteq> r"
  hence "\<forall>p0 q0. (\<exists>z. (p, z) \<in> b \<and> p0 = z - p) \<and> (\<exists>z. (r, z) \<in> b \<and> q0 = z - r) \<and> p \<noteq> r \<longrightarrow> p0 \<noteq> q0" by blast
  hence "\<forall>p0 q0. ((p, q) \<in> b \<and> p0 = q - p) \<and> ((r, s) \<in> b \<and> q0 = s - r) \<and> p \<noteq> r \<longrightarrow> p0 \<noteq> q0" by blast
  hence "(p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> q-p \<noteq> s-r" by blast
  hence "q-p \<noteq> s-r" using h3 h4 h5 by blast
  }
  thus "\<forall>x y p q. (\<exists>z. (x, z) \<in> b \<and> p = z - x) \<and> (\<exists>z. (y, z) \<in> b \<and> q = z - y) \<and> x \<noteq> y \<longrightarrow> p \<noteq> q \<Longrightarrow>
    \<forall>p q r s. (p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> q - p \<noteq> s - r" by blast
qed


definition nqueens3 :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "nqueens3 n b = (board3 n b \<and> safe3a b \<and> safe3b b \<and> safe3c b)"

lemma from2to3: "nqueens3 n b \<longrightarrow> nqueens2 n b"
proof (simp add: nqueens3_def nqueens2_def board3_def safe3a_def, standard)
  {
  assume b1:"board2 n b"
     and s1: "safe2a b"
     and s2: "safe3b b"
     and s3: "safe3c b"
     hence "\<forall>p q r s. (p, q) \<in> b \<and> (r, s) \<in> b \<and> p \<noteq> r \<longrightarrow> \<bar>p - r\<bar> \<noteq> \<bar>q - s\<bar>" by (smt s3 safe3b_def safe3c_def)
     hence "safe2b b" by (simp add: safe2b_def)
  }
  thus "board2 n b \<and> safe2a b \<and> safe3b b \<and> safe3c b \<Longrightarrow> safe2b b" by blast
qed

definition nqueens3i :: "int \<Rightarrow> int rel \<Rightarrow> bool" where
  "nqueens3i n b = (n\<ge>0 \<and> array n n b \<and> 
                    allDifferent b \<and> 
                    allDifferent {(x,y). \<exists>z. (x,z)\<in>b \<and> y=z+x} \<and> 
                    allDifferent {(x,y). \<exists>z. (x,z)\<in>b \<and> y=z-x})"

lemma impl3: "nqueens3i n b \<longleftrightarrow> nqueens3 n b"
by (simp add: nqueens3_def board3_def board2_def board1_def safe3a_def safe2a_def safead3b safead3c nqueens3i_def)

lemma arrplus: "array n n b \<Longrightarrow> {(x, y). \<exists>z. (x, z) \<in> b \<and> y = z + x} = {(x, y). x\<in>Domain b \<and> y = valof b x + x}"
using valofarr valofarrev Collect_cong Domain.DomainI Pair_inject case_prodE case_prodI2 by blast

lemma arrminus: "array n n b \<Longrightarrow> {(x, y). \<exists>z. (x, z) \<in> b \<and> y = z - x} = {(x, y). x\<in>Domain b \<and> y = valof b x - x}"
using valofarr valofarrev Collect_cong Domain.DomainI Pair_inject case_prodE case_prodI2 by blast

lemma implNotation: "nqueens3i n b \<longleftrightarrow> (n\<ge>0 \<and> array n n b \<and> 
                    allDifferent b \<and> 
                    allDifferent {(x,y). x\<in>Domain b \<and> y=(valof b x)+x} \<and> 
                    allDifferent {(x,y). x\<in>Domain b \<and> y=(valof b x)-x})"
apply (simp_all add: nqueens3i_def arrplus arrminus)
apply (auto)
by (simp_all add: nqueens3i_def arrplus arrminus)
