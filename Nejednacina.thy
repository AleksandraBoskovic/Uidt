theory Nejednacina 
  imports HOL.Real Main
begin

lemma saberi_levo [simp]:
  fixes a b :: real
  assumes "a > 0" 
  assumes "b > 0"
  shows "a + b > a"
  using assms
  by auto


lemma saberi_desno [simp]:
  fixes a b :: real
  assumes "a > 0" 
  assumes "b > 0"
  shows "b + a > a"
  using assms
  by auto

lemma pomnozi_levo [simp]:
  fixes a b :: real
  assumes "a > 0" 
  assumes "b > 0"
  assumes "a < 1"
  assumes "b < 1"
  shows "a * b < a"
  using assms
  by auto

lemma pomnozi_desno [simp]:
  fixes a b :: real
  assumes "a > 0" 
  assumes "b > 0"
  assumes "a < 1"
  assumes "b < 1"
  shows " b * a < a"
  using assms
  by auto

lemma kroz_jedan [simp]:
  fixes a :: real
  shows "a/1=a"
  by auto


lemma poredjenje_u_imeniocu [simp]:
  fixes a b :: real
  assumes "b > 0"
  assumes "a > 0"
  assumes "b > a"
  shows "1/b < 1/a"
  by (simp add: assms(2) assms(3) frac_less2)
  
lemma stepenovan_pozitivan [simp]:
   fixes a :: real and n::nat
   assumes "a ≥ 0"
   assumes "a ≤ 1"
   shows "a ^ n ≥ 0"
   using assms
   apply (induction n)
    apply auto
   done

lemma proizvod_pozitivan [simp]:
  fixes a b :: real
  assumes "b > 0"
  assumes "a > 0"
  shows "a*b > 0"
  using assms
  by auto

lemma zbir_pozitivan [simp]:
  fixes a b :: real
  assumes "b > 0"
  assumes "a > 0"
  shows "a+b > 0"
  using assms
  by auto


lemma moj_seminarski:
  fixes a b c :: real
  assumes "a+b+c=1" : zbir
  assumes "a > 0" 
  assumes "b > 0" 
  assumes "c > 0" 
  shows "1 + 8/27*a*b*c ≥ a/(a^3 + b^2*c + c^2*b) + b/(b^3 + c^2*a + a^2*c) + c/(c^3 + a^2*b + b^2*a) "
  using assms
proof-
  have "a/(a^3 + b^2*c + c^2*b) + b/(b^3 + c^2*a + a^2*c) + c/(c^3 + a^2*b + b^2*a)<a/(a^3) + b/(b^3) + c/(c^3)"
    by auto

qed






end