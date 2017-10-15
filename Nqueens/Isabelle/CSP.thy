theory CSP
imports Main
begin

(* declarations *)

definition funrel :: "int \<Rightarrow> int \<Rightarrow> int rel \<Rightarrow> bool" where
  "funrel m n b = (Domain b = {m..n} \<and> (\<forall>i x y. (i,x)\<in>b \<and> (i,y)\<in>b \<longrightarrow> x=y))"

definition array :: "int \<Rightarrow> int \<Rightarrow> int rel \<Rightarrow> bool" where
  "array n q b = (Domain b = {1..n} \<and> Range b \<subseteq> {1..q} \<and> (\<forall>i x y. (i,x)\<in>b \<and> (i,y)\<in>b \<longrightarrow> x=y))"

lemma arrayb1: "array n q b \<Longrightarrow> funrel 1 n b" by (simp add: funrel_def array_def)

definition valof :: "int rel \<Rightarrow> int \<Rightarrow> int" where
  "x\<in>Domain b \<Longrightarrow> (valof b x = (THE y. (x,y)\<in>b))"

lemma valofarr: "array n q b \<Longrightarrow> (x,z)\<in>b \<Longrightarrow> z = valof b x"
proof (simp add: array_def)
  {
  assume "(x, z) \<in> b"
     and f: "(\<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y)"
  hence a: "\<exists>!v. (x,v)\<in>b \<and> z = v" by blast
  then obtain v where h: "(x,v)\<in>b \<and> z = v" by blast
  hence "z = (THE y. y = v)" by auto
  hence "z = (THE y. (x,y)\<in>b)" using f a h theI by metis
  hence "z = valof b x" using \<open>(x, z) \<in> b\<close> valof_def by fastforce
  }
  thus "Domain b = {1..n} \<and>
    Range b \<subseteq> {1..q} \<and> (\<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y) \<Longrightarrow>
    (x, z) \<in> b \<Longrightarrow> z = valof b x" by (simp)
qed

lemma valofarrev: "array n q b \<Longrightarrow> x\<in>Domain b \<Longrightarrow> z = valof b x \<Longrightarrow> (x,z)\<in>b"
proof -
assume a: "array n q b"
hence "(\<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y)" by (simp add: array_def)
assume d: "x\<in>Domain b"
   and z: "z = valof b x"
hence "z = (THE y. (x,y)\<in>b)" by (simp add: valof_def)
thus ?thesis using a d valofarr z by auto
qed

lemma card1: "card {1..(n::nat)} = n"
proof (induction n)
case 0 show ?case by (simp)
next
case (Suc n) show ?case by (simp)
qed

lemma card2: "card {1..(n::nat)} = card {1..int n}"
proof (induction n)
case 0 show ?case by (simp)
next
case (Suc n) show ?case by (simp)
qed

lemma card3: "n\<ge>0 \<Longrightarrow> int (card {1..n}) = n "
proof -
  assume "n\<ge>0"
  then have "\<exists>m::nat. n = int m" by presburger
  then obtain m where h: "n = int m" by blast
  hence "card {1..int m} = m" using card1 card2 by simp
  thus "int (card {1..n}) = n" using h by simp
qed

lemma domcard: "finite b \<Longrightarrow> (\<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y) \<Longrightarrow> n = card b \<Longrightarrow> n = card (Domain b)"
proof (induction n arbitrary: b)
case 0
assume h0: "finite b"
assume h1: "\<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y"
assume h2: "0 = card b"
 show ?case
proof -
  from h0 h2 have "b={}" by (simp)
  hence "Domain b = {}" by simp
  thus ?thesis by simp
qed
next
case (Suc n)
assume h1: "\<And>b. finite b \<Longrightarrow>
    \<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y \<Longrightarrow> n = card b \<Longrightarrow> n = card (Domain b)"
assume h2: "finite b"
assume h3: "\<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y"
assume h4: "Suc n = card b"
show ?case
proof -
  from h4 have "\<exists>x. x\<in>b" using card_le_Suc_iff h2 insertI1 le_refl by fastforce
  then obtain x where h5: "x\<in>b" by blast
  then have "\<exists>a. x\<notin>a\<and>b=a\<union>{x}" by (metis Set.set_insert Un_commute insert_is_Un)
  then obtain a where h6: "x\<notin>a\<and>b=a\<union>{x}" by blast
  hence h7: "n = card a" 
  using Un_infinite Un_insert_right card_insert_disjoint 
        diff_Suc_1 h2 h4 sup_bot.right_neutral by auto
  hence h8: "n = card a \<Longrightarrow> n = card (Domain a)" using Suc.IH h2 h3 h6 by fastforce
  hence h9: "n = card (Domain a)" by (simp add: h7)
  from h6 have h11: "\<exists>p q. x=(p,q)" by simp
  then obtain p q where h12: "x=(p,q)" by blast
  hence h13: "Domain b - {p} = Domain a" 
  using Diff_insert_absorb DomainE Domain_insert Un_insert_right h3 h6 
        insertCI sup_bot.comm_neutral by blast
  hence h14: "card (Domain b - {p}) = n" by (simp add: h9)
  thus h10: "Suc n = card (Domain b)" using h3 
  by (metis Domain.DomainI card_Suc_Diff1 finite_Domain h12 h2 h5)
qed
qed

lemma domcard1: "finite b \<Longrightarrow> (\<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y) \<Longrightarrow> card b = card (Domain b)"
using domcard by blast

lemma arraycard: "\<lbrakk>n\<ge>0; array n q b\<rbrakk> \<Longrightarrow> int (card b) = n"
proof (simp add: array_def, auto)
  {
  assume b0: "0\<le>n"
     and b1: "Domain b = {1..n}"
     and b2: "Range b \<subseteq> {1..q}"
     and b3: "\<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y"
  from b1 b2 have f0: "b \<subseteq> {1..n}\<times>{1..q}"
  using Domain.DomainI Range.intros mem_Sigma_iff subrelI subset_eq by auto
  hence f1: "finite b" by (meson finite_SigmaI finite_atLeastAtMost_int rev_finite_subset)
  hence s3: "int (card b) = n" by (simp add: b0 b1 b3 domcard1)
  }
  thus "0 \<le> n \<Longrightarrow>
    Domain b = {1..n} \<Longrightarrow>
    Range b \<subseteq> {1..q} \<Longrightarrow> \<forall>i x y. (i, x) \<in> b \<and> (i, y) \<in> b \<longrightarrow> x = y \<Longrightarrow> int (card b) = n"
    by blast
qed

(* constraints *)

definition allDifferent :: "('s\<times>'t) set \<Rightarrow> bool" where
  "allDifferent a = (\<forall>x y p q. (x,p)\<in>a \<and> (y,q)\<in>a \<and> x\<noteq>y \<longrightarrow> p\<noteq>q)"

definition notInSet :: "'s \<Rightarrow> 's set \<Rightarrow> bool" where
  "notInSet a s = (a\<notin>s)"

end