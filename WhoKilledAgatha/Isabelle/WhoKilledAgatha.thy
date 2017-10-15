theory WhoKilledAgatha
imports Main
begin

datatype Person = Agatha | butler | Charles

definition richer :: "'a rel \<Rightarrow> bool" where
  "richer r = (irrefl r \<and> trans r \<and> antisym r)"

definition hates0 :: "Person rel \<Rightarrow> Person rel \<Rightarrow> bool" where
  "hates0 h r = (richer r \<and> 
    h``{Agatha} \<inter> h``{Charles} = {} \<and>
    h``{Agatha} = UNIV-{butler} \<and>
    (\<forall>x. (x,Agatha) \<notin> r \<longrightarrow> (butler,x) \<in> h) \<and>
    h``{Agatha} \<subseteq> h``{butler} \<and>
    (\<forall> x. h``{x} \<noteq> UNIV))"

definition wka0 :: "Person rel \<Rightarrow> Person rel \<Rightarrow> Person \<Rightarrow> Person \<Rightarrow> bool" where
  "wka0 r h v k = (hates0 h r \<and> (k,v) \<in> h-r \<and> v=Agatha)"

definition PI :: "int set" where "PI = {1..3}"

fun con :: "Person \<Rightarrow> int" where
  "con Agatha = 1" |
  "con butler = 2" |
  "con Charles = 3"

fun abs :: "int \<Rightarrow> Person" where
absp:  "abs i = (if i = 1 then Agatha else (if i = 2 then butler else Charles))"

lemma abs1 [simp]: "abs 1 = Agatha" by (simp)
lemma abs2 [simp]: "abs 2 = butler" by (simp)
lemma abs3 [simp]: "abs 3 = Charles" by (simp)

fun absr :: "int rel \<Rightarrow> Person rel" where
  "absr r = {(x,y). \<exists>x0 y0. (x0,y0)\<in>r \<and> x = abs x0 \<and> y = abs y0}"

definition hates1 :: "int rel \<Rightarrow> int rel \<Rightarrow> bool" where
  "hates1 h r = (richer r \<and> 
    h``{1} \<inter> h``{3} = {} \<and>
    h``{1} = PI-{2} \<and>
    (\<forall>x. (x,1) \<notin> r \<longrightarrow> (2,x) \<in> h) \<and>
    h``{1} \<subseteq> h``{2} \<and>
    (\<forall>x. h``{x} \<noteq> PI))"

definition wka1 :: "int rel \<Rightarrow> int rel \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "wka1 r h v k = (hates1 h r \<and> (k,v) \<in> h-r \<and> v=1)"

lemma from0to1: "\<lbrakk>v=abs w; k=abs l; s \<subseteq> PI\<times>PI; r = absr s; i \<subseteq> PI\<times>PI; h = absr i \<and> wka1 s i w l\<rbrakk> \<Longrightarrow> wka0 r h v k"
apply (simp only: wka0_def wka1_def hates0_def hates1_def richer_def PI_def)
apply (rule conjI)+
apply (rule irreflI)
apply (simp_all)
apply (smt atLeastAtMost_iff mem_Sigma_iff subsetCE)
apply (rule conjI)
apply (smt atLeastAtMost_iff mem_Sigma_iff subsetCE)
apply (smt atLeastAtMost_iff mem_Sigma_iff subset_eq)
apply (rule conjI)
apply (smt atLeastAtMost_iff mem_Sigma_iff subset_eq)
apply (rule conjI)
apply (smt atLeastAtMost_iff mem_Sigma_iff subset_eq)
apply (rule conjI)
apply (rule_tac [2] conjI)
apply (rule_tac [4] conjI)
defer
apply (blast)
apply (smt atLeastAtMost_iff mem_Sigma_iff subset_eq)
apply smt
apply (smt atLeastAtMost_iff mem_Sigma_iff subsetCE)
apply (smt atLeastAtMost_iff mem_Sigma_iff subsetCE)
done

definition hates2 :: "int rel \<Rightarrow> int rel \<Rightarrow> bool" where
  "hates2 h r = (richer r \<and> 
    (\<forall>x. (1,x)\<in> h \<longrightarrow> (3,x) \<notin> h) \<and>
    (1,1) \<in> h \<and>
    (1,2) \<notin> h \<and>
    (1,3) \<in> h \<and>
    (\<forall>x. (x,1) \<notin> r \<longrightarrow> (2,x) \<in> h) \<and>
    (\<forall>x. (1,x) \<in> h \<longrightarrow> (2,x) \<in> h) \<and>
    (\<forall>x. h``{x} \<noteq> PI))"

definition wka2 :: "int rel \<Rightarrow> int rel \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "wka2 r h v k = (hates2 h r \<and> (k,v) \<in> h-r \<and> v=1)"

lemma from1to2: "\<lbrakk>s \<subseteq> PI\<times>PI; i \<subseteq> PI\<times>PI; wka2 s i w l\<rbrakk> \<Longrightarrow> wka1 s i w l"
apply (simp add: wka2_def wka1_def hates2_def hates1_def PI_def)
using simp_from_to by auto

definition hates3 :: "int rel \<Rightarrow> int rel \<Rightarrow> bool" where
  "hates3 h r = (richer r \<and> 
    (\<forall>x. (1,x)\<in> h \<longrightarrow> (3,x) \<notin> h) \<and>
    (1,1) \<in> h \<and>
    (1,2) \<notin> h \<and>
    (1,3) \<in> h \<and>
    (\<forall>x. (x,1) \<notin> r \<longrightarrow> (2,x) \<in> h) \<and>
    (\<forall>x. (1,x) \<in> h \<longrightarrow> (2,x) \<in> h) \<and>
    (\<forall>x. (\<Sum>y\<in>h``{x}. y) \<le> 5))"

definition wka3 :: "int rel \<Rightarrow> int rel \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "wka3 r h v k = (hates3 h r \<and> (k,v) \<in> h-r \<and> v=1)"

lemma from2to3: "\<lbrakk>s \<subseteq> PI\<times>PI; i \<subseteq> PI\<times>PI; wka3 s i w l\<rbrakk> \<Longrightarrow> wka2 s i w l"
apply (simp add: wka3_def wka2_def hates3_def hates2_def PI_def)
by (smt Domain.DomainI DomainE ImageE Image_singleton_iff atLeastAtMost_iff atLeastAtMost_singleton_iff equalityCE equalityI insertI1 insert_commute insert_iff mem_Sigma_iff simp_from_to singletonD subrelI subsetCE subset_eq)

definition hates4 :: "int rel \<Rightarrow> int rel \<Rightarrow> bool" where
  "hates4 h r = (
    (\<forall>x. \<not> (x,x) \<in> r) \<and>
    (\<forall>x y z. (x,y) \<in> r \<and> (y,z) \<in> r \<longrightarrow> (x,z) \<in> r) \<and>
    (\<forall>x y. (x,y) \<in> r \<longleftrightarrow> (y,x) \<notin> r) \<and>
    (\<forall>x. (1,x)\<in> h \<longrightarrow> (3,x) \<notin> h) \<and>
    (1,1) \<in> h \<and>
    (1,2) \<notin> h \<and>
    (1,3) \<in> h \<and>
    (\<forall>x. (x,1) \<notin> r \<longrightarrow> (2,x) \<in> h) \<and>
    (\<forall>x. (1,x) \<in> h \<longrightarrow> (2,x) \<in> h) \<and>
    (\<forall>x. (\<Sum>y\<in>h``{x}. y) \<le> 5))"

definition wka4 :: "int rel \<Rightarrow> int rel \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "wka4 r h v k = (hates4 h r \<and> (k,v) \<in> h-r \<and> v=1)"

lemma from3to4: "\<lbrakk>s \<subseteq> PI\<times>PI; i \<subseteq> PI\<times>PI; wka4 s i w l\<rbrakk> \<Longrightarrow> wka3 s i w l"
apply (simp only: wka4_def wka3_def hates3_def PI_def)
apply (rule conjI)+
apply (simp only: hates4_def)
apply blast
apply (metis hates4_def)
by blast

definition predrel :: "(int \<times> int \<Rightarrow> bool) \<Rightarrow> int rel" where
  "predrel p = {(x,y). p(x,y)}"

definition sum :: "(int \<times> int \<Rightarrow> bool) \<Rightarrow> int \<Rightarrow> int" where
  "sum p x = (\<Sum>y\<in>{m. x\<in>PI \<and> p(x,m)}. y)"

definition hates5 :: "(int \<times> int \<Rightarrow> bool) \<Rightarrow> (int \<times> int \<Rightarrow> bool) \<Rightarrow> bool" where
  "hates5 h r = (
    (\<forall>x. x\<in>PI \<longrightarrow> \<not> r(x,x)) \<and>
    (\<forall>x y z. x\<in>PI \<and> y\<in>PI \<and> z\<in>PI \<longrightarrow> r(x,y) \<and> r(y,z) \<longrightarrow> r(x,z)) \<and>
    (\<forall>x y. x\<in>PI \<and> y\<in>PI \<longrightarrow> r(x,y) \<noteq> r(y,x)) \<and>
    (\<forall>x. x\<in>PI \<longrightarrow> h(1,x) \<longrightarrow> \<not>h(3,x)) \<and>
    h(1,1) \<and>
    \<not>h(1,2) \<and>
    h(1,3) \<and>
    (\<forall>x. x\<in>PI \<longrightarrow> r(x,1) \<longrightarrow> h(2,x)) \<and>
    (\<forall>x. x\<in>PI \<longrightarrow> h(1,x) \<longrightarrow> h(2,x)) \<and>
    (\<forall>x. x\<in>PI \<longrightarrow> sum h x \<le> 5))"

definition wka5 :: "(int \<times> int \<Rightarrow> bool) \<Rightarrow> (int \<times> int \<Rightarrow> bool) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "wka5 r h v k = (hates5 h r \<and> h(k,v) \<and> \<not>r(k,v) \<and> v=1)"

definition lim :: "int set => (int \<times> int \<Rightarrow> bool) \<Rightarrow> bool" where
  "lim s a = (\<forall>x y. (x,y)\<notin>s\<times>s \<longrightarrow> \<not>a(x,y))"

lemma from4to5: "\<lbrakk>lim {1..3} t; lim {1..3} j; s = predrel t; i = predrel j; wka5 t j w l\<rbrakk> \<Longrightarrow> s \<subseteq> PI\<times>PI \<and> i \<subseteq> PI\<times>PI \<and> wka4 s i w l"
apply (simp only: wka5_def wka4_def hates5_def hates4_def lim_def predrel_def PI_def)
by (metis mem_Sigma_iff)