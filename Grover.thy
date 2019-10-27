(*
Authors: 
  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
*)

theory Grover
imports                           
  Deutsch_Jozsa (*I would rather prefer to copy everything but its a lot*)
begin

abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1" 

lemma ket_zero_is_state: 
  shows "state 1 |zero\<rangle>"
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

lemma ket_one_is_state:
  shows "state 1 |one\<rangle>" 
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

locale grover =
  fixes f :: "nat \<Rightarrow> nat" and n x :: nat 
  fixes q_oracle :: "complex Matrix.mat" ("O")
  assumes fun_dom: "f \<in> ({(i::nat). i < 2^n} \<rightarrow>\<^sub>E {0,1})"
  assumes dim: "n \<ge> 1"
  assumes searched_dom: "x \<in> {(i::nat). i < 2^n}"
  assumes searched: "\<forall>i < 2^n. f(i) = 1 \<longleftrightarrow> i = x" 
  assumes q_oracle_app: "\<forall>(A::complex Matrix.mat). dim_row A = 2^n \<and> dim_col A = 1 \<longrightarrow>   
                         O * (A \<Otimes> (H * |one\<rangle>)) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (A $$ (i,j))))  \<Otimes> (H * |one\<rangle>)"
  assumes q_oracle_gate: "gate (n+1) O"

context grover
begin

definition iterations :: nat where
"iterations = nat \<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>"

lemma iterations_nat [simp]:
  shows "nat \<lfloor>(pi/4 * sqrt(2)^n)\<rfloor> = \<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>"
proof-
  have "(pi/4 * sqrt(2)^n) \<ge> 0" by simp
  then have "\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor> \<ge> 0" by linarith
  then show ?thesis by simp
qed

lemma f_ge_0: 
  shows "\<forall>x. (f x \<ge> 0)" by simp

lemma f_dom_not_zero: 
  shows "f \<in> ({i::nat. n \<ge> 1 \<and> i < 2^n} \<rightarrow>\<^sub>E {0,1})" 
  using fun_dom dim by simp

lemma f_values: "\<forall>x \<in> {(i::nat). i < 2^n}. (f x = 0 \<or> f x = 1)" 
  using fun_dom by auto

lemma search_function_zero [simp]:
  assumes "i < 2^n" and "i \<noteq> x"
  shows "f(i) = 0" 
  using fun_dom searched f_values assms
  by blast

lemma search_function_one [simp]:
  assumes "i < 2^n" and "i = x"
  shows "f(i) = 1" 
  using fun_dom searched f_values assms
  by simp

end (*context grover*)

lemma sum_without_x:
  fixes n i :: nat
      and a :: complex
  assumes "i < n"
  shows "(\<Sum> k \<in> ({0..<n}-{i}). a) = (of_nat n - 1) * a" 
  by (metis assms(1) atLeast0LessThan card_atLeastLessThan diff_zero finite_atLeastLessThan lessThan_iff 
      linordered_field_class.sign_simps(20) mult_cancel_right1 sum_constant sum_diff1) 

lemma sum_without_x_and_i:
  fixes n i x :: nat
      and a :: complex
  assumes "i < n" and "x < n"  and "i \<noteq> x" 
  shows "(\<Sum> k \<in> ({0..<n}-{i,x}). a) = (of_nat n - 2) * a" 
proof-
  have "x \<in> {0..<n}-{i}-{}"
    by (metis Diff_insert2 assms(1) assms(2) assms(3) atLeast0LessThan insertE insert_Diff lessThan_iff)
  moreover have "finite ({0..<n}-{i}-{})"
    by simp
  ultimately have "(\<Sum>n \<in> ({0..<n}-{i}-{}-{x}). a) = (\<Sum>n \<in> ({0..<n}-{i}-{}). a) - a"
   by (meson sum_diff1)
  then have "(\<Sum> k \<in> ({0..<n}-{i,x}). a) = (\<Sum> k \<in> ({0 ..< n}-{i}). a) - a" 
    by (metis (no_types) Diff_insert2)
  then have "(\<Sum> k \<in> ({0..<n}-{i,x}). a) = (of_nat n - 1) * a - a" 
    using assms(1) sum_without_x by simp
  then show "(\<Sum> k \<in> ({0..<n}-{i,x}). a) = (of_nat n - 2) * a" 
    by (simp add: linordered_field_class.sign_simps(20))
qed

(*Do I need to show that this is 2 |psi><psi|-I?*)
definition(in grover) diffusion_operator :: "complex Matrix.mat" where
"diffusion_operator = Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if i=j then ((1-2^(n-1))/2^(n-1)) else 1/(2^(n-1)))"

notation(in grover) diffusion_operator ("D")

lemma (in grover) diffusion_operator_values_hidden:
  fixes k :: nat
  assumes "i < 2^n \<and> j < 2^n" 
  shows "k \<in> ({0..<2^n}-{i,j}) \<longrightarrow> D $$ (i,k) = 1/(2^(n-1)) \<and> D $$ (k,j) = 1/(2^(n-1))"
  by (simp add: assms diffusion_operator_def)
    
lemma (in grover) transpose_of_diffusion:
  shows "(D)\<^sup>t = D"
proof
  fix i j :: nat
  assume "i < dim_row D" and "j < dim_col D"
  thus "D\<^sup>t $$ (i, j) = D $$ (i, j)" using diffusion_operator_def
    by (auto simp add: transpose_mat_def)
next
  show "dim_row D\<^sup>t = dim_row D"
    by (simp add: diffusion_operator_def)
next  
  show "dim_col D\<^sup>t = dim_col D"
    by (simp add: diffusion_operator_def)
qed

lemma (in grover) dagger_of_diffusion: 
  shows "(D)\<^sup>\<dagger> = D"
proof
  show "dim_row (D\<^sup>\<dagger>) = dim_row D" by (simp add: diffusion_operator_def)
next
  show "dim_col (D\<^sup>\<dagger>) = dim_col D" by (simp add: diffusion_operator_def)
next
  fix i j :: nat
  assume a0: "i < dim_row D" and a1: "j < dim_col D"
  then have f0: "D\<^sup>\<dagger> $$ (i, j) = cnj (D $$ (j,i))" 
    using dagger_def by (metis case_prod_conv index_mat(1) index_transpose_mat(3) transpose_of_diffusion)
  show "D\<^sup>\<dagger> $$ (i, j) = D $$ (i, j)"
  proof(rule disjE)
    show "i = j \<or> i \<noteq> j" by auto
  next
    assume a2: "i = j"
    moreover have "D $$ (i, j) = (1 - 2^(n-1))/2^(n-1)"
        using a0 a2 diffusion_operator_def complex_cnj_cancel_iff by simp
    ultimately show "D\<^sup>\<dagger> $$ (i, j) = D $$ (i, j)" using f0 cnj_def by simp
  next
    assume a2: "i \<noteq> j"
    moreover have "D $$ (i, j) = 1/(2^(n-1))"
      using a0 a1 a2 diffusion_operator_def by simp
    moreover have "D $$ (j, i) = 1/(2^(n-1))"
      using a0 a1 a2 diffusion_operator_def by simp
    ultimately show "D\<^sup>\<dagger> $$ (i, j) = D $$ (i, j)" using f0 by simp
  qed
qed
    
lemma (in grover) diffusion_is_gate:
  shows "gate n D"
proof
  show "dim_row D = 2^n" using diffusion_operator_def by simp
next
  show "square_mat D" using diffusion_operator_def by simp
next
  show "unitary D" 
  proof-
    have "D * D = 1\<^sub>m (dim_col D)"
    proof
      show "dim_row (D * D) = dim_row (1\<^sub>m (dim_col D))" by (simp add: diffusion_operator_def)
    next
      show "dim_col (D * D) = dim_col (1\<^sub>m (dim_col D))" by (simp add: diffusion_operator_def)
    next
      fix i j :: nat
      assume a0: "i < dim_row (1\<^sub>m (dim_col D))" and a1: "j < dim_col (1\<^sub>m (dim_col D))"
      then have f0: "i < 2^n \<and> j < 2^n" by (simp add: diffusion_operator_def)
      show "(D * D) $$ (i,j) = 1\<^sub>m (dim_col D) $$ (i, j)"
      proof(rule disjE)
        show "i = j \<or> i \<noteq> j" by auto
      next
        assume a2: "i = j"
        then have "(D * D) $$ (i,j) = (\<Sum> k < dim_row D. (D $$ (i,k)) * (D $$ (k,j)))"       
          using a0 a1 
          by (metis (no_types, lifting) index_matrix_prod index_one_mat(2) index_transpose_mat(3) sum.cong transpose_of_diffusion)
        also have "... = (\<Sum> k \<in> ({0..<2^n}). (D $$ (i,k)) * (D $$ (k,j)))"  
          by (simp add: atLeast0LessThan diffusion_operator_def)
        also have "... = (\<Sum> k \<in> ({0..<2^n}-{i}). (D $$ (i,k)) * (D $$ (k,j))) + (D $$ (i,i)) * (D $$ (i,j))" 
          using a1 a2
          by (metis (no_types, lifting) add.commute atLeast0LessThan diffusion_operator_def dim_col_mat(1) finite_atLeastLessThan index_one_mat(3) insert_Diff insert_Diff_single lessThan_iff sum.insert_remove)
        also have "... = (\<Sum> k \<in> ({0..<2^n}-{i}). 1/(2^(n-1)) * 1/(2^(n-1))) + ((1-2^(n-1))/2^(n-1)) * ((1-2^(n-1))/2^(n-1)) "
          using diffusion_operator_def a1 a2 by simp
        also have "... = (2^n - 1) * (1/2^(n-1) * 1/2^(n-1)) + ((1-2^(n-1))/2^(n-1)) * ((1-2^(n-1))/2^(n-1))"
          using sum_without_x[of "i" "2^n" "1/(2^(n-1)) * 1/(2^(n-1))"] a0 a1 dim diffusion_operator_def by simp
        also have "... = ((2^n - 1) + (1 - 2^(n-1))\<^sup>2)/(2^(n-1))\<^sup>2" 
          by (simp add: power2_eq_square add_divide_distrib)
        also have "... = ((2^n - 1) + (1\<^sup>2 + (2^(n-1))\<^sup>2 - 2 * 2^(n-1)))/(2^(n-1))\<^sup>2"
          using power2_diff[of 1 "2^(n-1)"] mult.right_neutral by metis
        also have "... = (2^n + (2^(n-1))\<^sup>2 - 2 * 2^(n-1))/(2^(n-1))\<^sup>2" by simp
        also have "... = (2^n + (2^(n-1))\<^sup>2 - 2^n)/(2^(n-1))\<^sup>2" by (metis dim le_numeral_extra(2) power_eq_if)
        also have "... = 1" by simp
        finally have "(D * D) $$ (i,j) = 1" by simp
        then show "(D * D) $$ (i,j) = 1\<^sub>m (dim_col D) $$ (i, j)" 
          using a1 a2 by simp
      next
        assume a2: "i \<noteq> j"
        then have "(D * D) $$ (i,j) = (\<Sum> k < dim_row D. (D $$ (i,k)) * (D $$ (k,j)))"       
          using a0 a1 
          by (metis (no_types, lifting) index_matrix_prod index_one_mat(2) index_one_mat(3) index_transpose_mat(3) sum.cong 
              transpose_of_diffusion)
        also have "... = (\<Sum>k \<in> ({0..<2^n}). (D $$ (i,k)) * (D $$ (k,j)))"  
          by (simp add: atLeast0LessThan diffusion_operator_def)
        also have "... = (\<Sum>k \<in> ({0..<2^n}-{i,j}). (D $$ (i,k)) * (D $$ (k,j))) 
                       + (D $$ (i,i)) * (D $$ (i,j)) + (D $$ (i,j)) * (D $$ (j,j))"  
          using a0 a1 a2 diffusion_operator_def 
          by (smt Diff_insert add.commute atLeast0LessThan dim_col_mat(1) finite_Diff finite_atLeastLessThan 
              index_one_mat(2) index_one_mat(3) insert_Diff insert_Diff_single insert_iff lessThan_iff sum.insert_remove)
        also have "... = (\<Sum>k \<in> ({0..<2^n}-{i,j}). 1/(2^(n-1)) * 1/(2^(n-1))) 
                        + ((1 - 2^(n-1))/2^(n-1)) * 1/(2^(n-1)) + 1/(2^(n-1)) * ((1 - 2^(n-1))/2^(n-1))" 
          using diffusion_operator_values_hidden f0 sum.cong a2 diffusion_operator_def by simp
        also have "... = (2^n - 2)* 1/2^(n-1) * 1/2^(n-1)
                       + (1 - 2^(n-1))/2^(n-1) * 1/2^(n-1) + 1/2^(n-1) * (1 - 2^(n-1))/2^(n-1)" 
          using sum_without_x_and_i[of "i" "2^n" "j" "(1/(2^(n-1)) * 1/(2^(n-1)))"] a0 a1 a2 diffusion_operator_def 
          by simp
        also have "... = (2^n - 2) * (1/2^(n-1))\<^sup>2 + (1 - 2^(n-1)) * (1/2^(n-1))\<^sup>2 + (1 - 2^(n-1)) * (1/2^(n-1))\<^sup>2" 
          by (simp add: power2_eq_square)
        also have "... = ((2^n - 2) + (1-2^(n-1)) + (1 - 2^(n-1))) * (1/2^(n-1))\<^sup>2" 
          by (metis comm_semiring_class.distrib)
        also have "... = (2^n - 2 * 2^(n-1)) * (1/2^(n-1))\<^sup>2" by simp
        also have "... = (2^n - 2^n) * (1/2^(n-1))\<^sup>2" 
          by (metis dim le_add_diff_inverse plus_1_eq_Suc power.simps(2))
        also have "... = 0" by simp
        finally have "(D * D) $$ (i,j) = 0" by simp
        then show "(D * D) $$ (i,j) = 1\<^sub>m (dim_col D) $$ (i, j)" 
          using a0 a1 a2 by simp
      qed
    qed
    then show "unitary D" 
      by (metis dagger_of_diffusion index_transpose_mat(3) transpose_of_diffusion unitary_def)
  qed
qed
         
lemma (in grover) diffusion_Id_is_gate:
  shows "gate (n+1) (D \<Otimes> Id 1)"
  using diffusion_is_gate id_is_gate tensor_gate by blast

lemma (in grover) app_oracle:
  fixes \<alpha> \<beta>
  defines "v \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
  defines "w \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
  shows "O * (v \<Otimes> (H * |one\<rangle>)) = (w \<Otimes> (H * |one\<rangle>))"
proof-
  have "dim_row v = 2^n \<and> dim_col v = 1" using assms by simp
  then have "O * (v \<Otimes> (H * |one\<rangle>)) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) \<Otimes> (H * |one\<rangle>)"
    using q_oracle_app assms by simp
  moreover have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = w" 
  proof
    fix i j :: nat
    assume "i < dim_row w" and "j < dim_col w"
    then have f0: "i < 2^n \<and> j = 0" using assms by simp
    moreover have "i = x \<longrightarrow> (-1)^f(i) = (-(1::real))" 
      using searched_dom grover_axioms by simp
    moreover have "i \<noteq> x \<and> i < 2^n  \<longrightarrow> (-1)^f(i) = 1" for i::nat
      using searched_dom grover_axioms search_function_zero by simp
    ultimately show "(Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) $$ (i,j) = w $$ (i,j)" 
      using assms f0 by simp
  next
    show "dim_row (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = dim_row w" 
      by (simp add: assms(2))
  next
    show "dim_col (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = dim_col w" 
      by (simp add: assms(2))
  qed
  ultimately show "O * (v \<Otimes> (H * |one\<rangle>)) = (w \<Otimes> (H * |one\<rangle>))" by simp
qed

lemma (in grover) pow_2_n_half [simp]:
  shows "2^n - 2^(n-1) = (2::complex)^(n-1)" 
proof (rule Nat.nat_induct_at_least[of 1 n])
  show "n \<ge> 1" using dim by simp
next
  show "2^1 - 2^(1-1) = (2::complex)^(1-1)" by simp
next
  fix n
  assume a0: "n \<ge> 1" and IH: "2^n - 2^(n-1) = (2::complex)^(n-1)"  
  then have "2^(n+1) - 2^n = (2::complex) * (2^n - 2^(n-1))" by simp
  also have "... = (2::complex) * 2^(n-1)" using IH by simp
  also have "... = (2::complex)^n" 
    using IH le_add_diff_inverse2 by simp
  finally show "2^(Suc n) - 2^((Suc n)-1) = (2::complex)^((Suc n)-1)" by simp
qed

lemma (in grover) aux_calculation_pow_2[simp]: 
  shows "(2::complex)/2^n = 1/2^(n-1)" 
  and "(2::real)/2^n = 1/2^(n-1)" 
  and "((2^(n-1) - (1::complex))/2^(n-1)) = (2^n - 2)/(2::complex)^n" 
  and "(1/sqrt(2)^n)\<^sup>2 = 1/2^n"
  and "1/sqrt(2)^n * 1/sqrt(2)^n = 1/2^n" (* Still needed? *)
  and "1/sqrt(2)^n = sqrt(1/2^n)" 
proof-
  show "(2::complex)/2^n = 1/2^(n-1)" using dim 
    by (metis (no_types, lifting) One_nat_def Suc_diff_le diff_Suc_Suc diff_zero divide_divide_eq_left divide_self_if power.simps(2) zero_neq_numeral)
next
  show "(2::real)/2^n = 1/2^(n-1)" using dim 
   by (smt One_nat_def Suc_diff_le diff_Suc_Suc diff_zero divide_divide_eq_left divide_self_if power.simps(2))
next
  show "((2^(n-1) - (1::complex))/2^(n-1)) = (2^n - 2)/(2::complex)^n"
    by (smt dim One_nat_def Suc_diff_le diff_Suc_Suc diff_divide_distrib diff_zero divide_divide_eq_left 
        divide_self power.simps(2) power_not_zero zero_neq_numeral)
next
  show "(1/sqrt(2)^n)\<^sup>2 = 1/2^n" using dim 
    by (metis power_one_over real_sqrt_pow2 real_sqrt_power zero_le_numeral zero_le_power)
next
  show "1/sqrt(2)^n * 1/sqrt(2)^n = 1/2^n" by (simp add: aux_comp_with_sqrt2)
next
  show "1/sqrt(2)^n = sqrt(1/2^n)" 
    by (simp add: real_sqrt_divide real_sqrt_power)
qed


lemma (in grover) app_diffusion_op:
  fixes \<alpha> \<beta> :: complex 
  defines "v \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
    and "w \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^n-2)/2^n) * \<alpha> + (2^n-1)/(2^(n-1)) * \<beta>
                                             else 2/2^n * -\<alpha> + (2^n-2)/2^n * \<beta>))"
  shows "D * v = w"
proof
  fix i j :: nat
  assume a0: "i < dim_row w" and a1: "j < dim_col w"
  then have f0: "i < 2^n \<and> j = 0" using assms by simp
  then have "(D * v) $$ (i,j) = (\<Sum> k \<in> {0..<2^n}. (Matrix.row D i) $ k * (Matrix.col v j) $ k)"
    using assms atLeast0LessThan diffusion_operator_def by simp
  then have f1: "(D * v) $$ (i,j) =
                (\<Sum> k \<in> ({0..<2^n}-{i}). (Matrix.row D i) $ k * (Matrix.col v j) $ k)
              + (Matrix.row D i) $ i * (Matrix.col v j) $ i" 
    by (simp add: f0 sum_diff1)
  show "(D * v) $$ (i,j) = w  $$ (i,j)" 
  proof(rule disjE) 
    show "i = x \<or> i \<noteq> x" by simp
  next
    assume a2: "i = x" 
    moreover have "(\<Sum> k \<in> ({0..<2^n}-{i}).  1/(2^(n-1)) * \<beta>) = (2^n - 1) * \<beta> / 2^(n-1)" 
      using sum_without_x[of i "2^n" "(1/(2^(n-1)) * \<beta>)::complex"] dim f0 
      by (simp add: of_nat_diff)
    moreover have  "((1 - 2^(n-1)) / 2^(n-1)) * (-\<alpha>) = ((2^(n-1) - 1) / 2^(n-1)) * \<alpha>" 
      by (metis divide_minus_left minus_diff_eq minus_mult_minus)
    ultimately have f0: "(D * v) $$ (i,j) = ((2^(n-1) - 1)/2^(n-1)) * \<alpha> + (2^n - 1)/(2^(n-1)) * \<beta>"
      using assms diffusion_operator_def a2 f0 f1
      by (simp add: of_nat_diff)
    then have "(D * v) $$ (i,j) = ((2^n - 2) / 2^n) * \<alpha> + (2^n - 1)/(2^(n-1)) * \<beta>" using dim aux_calculation_pow_2 by (simp add: f0)
    then show "(D * v) $$ (i,j) = w $$ (i,j)" using assms a2 a0 a1 f1 by simp
  next
    assume a2: "i \<noteq> x "
    have "(\<Sum> k \<in> ({0..<2^n}-{i}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) =
                   (\<Sum> k \<in> ({0..<2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k)
                   + ((Matrix.row D i) $ x * (Matrix.col v j) $ x)" 
      using sum_diff1 a2 f0
      by (smt Diff_insert2 add.commute atLeast0LessThan finite_Diff finite_atLeastLessThan 
          insertE insert_Diff_single insert_absorb lessThan_iff mem_Collect_eq searched_dom sum.insert_remove)
    moreover have "(\<Sum> k \<in> ({0..<2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) = (2^n - 2) /(2^(n-1)) * \<beta>" 
    proof-
      have "i < 2^n \<and> x < 2^n \<and> i \<noteq> x "
        using a2 f0 grover.searched_dom grover_axioms by fastforce
      then have "(\<Sum> k \<in> ({0..<2^n}-{i,x}). 1/(2^(n-1)) * \<beta>) = (2^n - 2) * (1/2^(n-1) * \<beta>)"
        using sum_without_x_and_i[of i "2^n" x "1/(2^(n-1)) * \<beta>"] assms by simp
      moreover have "(\<Sum> k \<in> ({0..<2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) =
                     (\<Sum> k \<in> ({0..<2^n}-{i,x}). 1/(2^(n-1)) * \<beta>)" 
        using diffusion_operator_def a2 f0 assms by simp
      ultimately show  "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) 
                        = (2^n - 2) /(2 ^ (n-1)) * \<beta>" 
        by simp
    qed
    moreover have "((Matrix.row D i) $ x * (Matrix.col v j) $ x) = 1/2^(n-1)*-\<alpha>" 
      using diffusion_operator_def a2 v_def f0 searched_dom by simp
    moreover have "(Matrix.row D i) $ i * (Matrix.col v j) $ i = ((1-2^(n-1))/2^(n-1))*\<beta>" 
      using diffusion_operator_def a2 f0 v_def searched_dom by simp
    ultimately have  "(D * v) $$ (i,j) = (2^n-2)/(2^(n-1)) * \<beta> + 1/2^(n-1)*-\<alpha> +((1-2^(n-1))/2^(n-1))*\<beta>" 
      using f1 by simp 
    moreover have "(2^n-2)/(2^(n-1)) * \<beta> + ((1-2^(n-1))/2^(n-1))*\<beta> = (2^n-2)/2^n*\<beta>" 
    proof-
      have "(2^n - 2) /(2^(n-1))+((1-2^(n-1))/2^(n-1)) = ((2^n - (2::complex)) + (1 - 2^(n-1))) * 1/(2^(n-1))"
        using comm_semiring_class.distrib[of "(2^n - (2::complex))" "(1-2^(n-1))" "1/(2^(n-1))"] by simp
      also have "... = (2^n-2^(n-1)-(2::complex)+1) * 1/(2^(n-1))" 
        by (simp add: dim)
      also have "... = (2^(n-1)-(1::complex)) * 1/(2^(n-1))" 
        using dim pow_2_n_half by simp
      also have "... = (2^n-(2::complex))/2 * 1/(2^(n-1))" 
        using aux_calculation_pow_2 dim pow_2_n_half by simp
      also have "... = (2^n-(2::complex)) * 1/(2^n)" using aux_calculation_pow_2 pow_2_n_half by simp
      finally show "(2^n - (2::complex)) /(2^(n-1)) * \<beta> + ((1-2^(n-1))/2^(n-1)) * \<beta> = (2^n-2)/2^n*\<beta>" 
        by (metis comm_semiring_class.distrib mult.right_neutral)
    qed
    moreover have "1/2^(n-1)*-\<alpha> = 2/2^n*-\<alpha>" using aux_calculation_pow_2 by auto
    ultimately have "(D * v) $$ (i,j) = 2/2^n*-\<alpha> + (2^n-2)/2^n*\<beta>"
      by (metis (mono_tags, hide_lams) add_divide_distrib combine_common_factor power_one_over ring_class.ring_distribs(1) 
          semiring_normalization_rules(24) semiring_normalization_rules(7))
    then show "(D * v) $$ (i,j) = w $$ (i,j)" using assms a2 f0 by simp
  qed
next
  show "dim_row (D * v) = dim_row w" using assms diffusion_operator_def by simp 
next 
  show "dim_col (D * v) = dim_col w" using assms diffusion_operator_def by simp 
qed


lemma (in grover) app_diffusion_op_res:
  fixes \<alpha> \<beta> :: complex 
  defines "v \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
  defines "w \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^n-2)/2^n) * \<alpha> + (2^n-1)/(2^(n-1)) * \<beta>
                                             else 2/2^n * -\<alpha> + (2^n-2)/2^n * \<beta> ))"
  assumes "state n v" 
  shows "(D \<Otimes> Id 1) * (v \<Otimes> (H * |one\<rangle>)) = w \<Otimes> (H * |one\<rangle>)" 
proof-
  have "dim_col (Id 1) = dim_row (H * |one\<rangle>)" 
    using assms Id_def
    by (simp add: H_without_scalar_prod)
  moreover have "dim_col D = dim_row v" 
    using assms diffusion_operator_def by simp
  moreover have "dim_col D > 0" and "dim_col v > 0" and "dim_col (Id 1) > 0" and  "dim_col (H * |one\<rangle>) > 0" 
    using assms diffusion_operator_def Id_def ket_vec_def by auto
  ultimately have "(D \<Otimes> Id 1) * (v \<Otimes> (H * |one\<rangle>)) = (D * v) \<Otimes> (Id 1 * (H * |one\<rangle>))" 
    using mult_distr_tensor by simp
  moreover have "(Id 1 * (H * |one\<rangle>)) = (H * |one\<rangle>)" 
    using right_mult_one_mat H_on_ket_one Quantum.Id_def H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1 by auto
  ultimately show "(D \<Otimes> Id 1) * (v \<Otimes> (H * |one\<rangle>)) = w \<Otimes> (H * |one\<rangle>)" using app_diffusion_op assms by simp
qed

primrec (in grover) grover_iter :: "nat \<Rightarrow> complex Matrix.mat" where
"grover_iter 0 = ((H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>)) \<Otimes> (H * |one\<rangle>)"|
"grover_iter (Suc m) = (D \<Otimes> Id 1) * (O * (grover_iter m))"

lemma (in grover) grover_iter_is_state:
  shows "state (n+1) (grover_iter m)" 
proof(induction m)
  have "grover_iter 0 = ((H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>)) \<Otimes> (H * |one\<rangle>)" by simp
  moreover have "state n ((H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>))" 
    using \<psi>\<^sub>1\<^sub>0_tensor_is_state dim iter_tensor_of_H_is_gate by simp
  moreover have "state 1 (H * |one\<rangle>)" 
    using H_on_ket_one_is_state by auto
  ultimately show "state (n+1) (grover_iter 0)" using tensor_state[of n "(H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>)" 1 "(H * |one\<rangle>)"] by simp
next
  fix m 
  assume IH: "state (n+1) (grover_iter m)" 
  moreover have "gate (n+1) O" using q_oracle_gate by simp
  ultimately have "state (n+1) (O * (grover_iter m))" by simp
  moreover have "grover_iter (Suc m) = (D \<Otimes> Id 1) * (O * (grover_iter m))" by simp
  moreover have "gate (n+1) (D \<Otimes> Id 1)" using diffusion_Id_is_gate by simp
  ultimately show "state (n+1) (grover_iter (Suc m))" by simp 
qed

definition (in grover) grover_algo :: "complex Matrix.mat" where 
"grover_algo \<equiv> grover_iter iterations"

theorem (in grover) grover_algo_is_state:
  shows "state (n+1) grover_algo" 
  using grover_iter_is_state 
  by (simp add: grover_algo_def)

declare[[show_types]]
lemma (in grover) double_sinus:
  fixes m
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  shows "sin(2*\<theta>) = sqrt(2^n-1) * (2/2^n)"
proof-
  have "sin(2*\<theta>) = 2 * cos(\<theta>) * sin(\<theta>)" 
    by (metis mult.commute mult.left_commute semigroup_mult_class.mult.assoc sin_double) 
  moreover have f0: "-1 \<le> 1/sqrt(2)^n" 
    by (meson le_minus_one_simps(1) order.trans real_sqrt_ge_0_iff zero_le_divide_1_iff zero_le_numeral zero_le_power)
  moreover have "1/sqrt(2)^n \<le> 1" by simp
  ultimately have "sin(2*\<theta>) = 2 * cos(\<theta>) * 1/sqrt(2)^n" 
    using \<theta>_def sin_arcsin[of "1/sqrt(2)^n"] by (metis times_divide_eq_right)
  also have "... = 2 * sqrt(1-(1/sqrt(2)^n)\<^sup>2) * 1/sqrt(2)^n" using \<theta>_def cos_arcsin f0 by simp
  also have "... = 2 * sqrt((2^n-1)/2^n) * 1/sqrt(2)^n" by (simp add: diff_divide_distrib)
  also have "... = 2 * (sqrt(2^n-1) * sqrt(1/2^n)) * 1/sqrt(2)^n"
    by (metis mult.right_neutral real_sqrt_mult semigroup_mult_class.mult.assoc times_divide_eq_right)
  also have "... = 2 * sqrt(2^n-1) * (1/sqrt(2)^n * 1/sqrt(2)^n)" by simp
  also have "... = 2 * sqrt(2^n-1) * (1/sqrt(2)^n)\<^sup>2" 
    by (metis (no_types, hide_lams) power_divide power_even_eq power_one power_one_right semiring_normalization_rules(36) times_divide_eq_right)
  also have "... = 2 * sqrt(2^n-1) * 1/2^n" using aux_calculation_pow_2(4)by auto
  finally show ?thesis 
    by (metis mult.commute mult.left_neutral semiring_normalization_rules(7) times_divide_eq_left)
qed

lemma (in grover) double_cos:
  fixes m
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  shows "cos(2*\<theta>) = ((2^n-2)/2^n)"
proof-
  have "cos(2*\<theta>) = (cos(\<theta>))\<^sup>2 - ((sin(\<theta>))\<^sup>2)" by (simp add: cos_double) 
  moreover have f0: "-1 \<le> 1/sqrt(2)^n" 
    by (meson le_minus_one_simps(1) order.trans real_sqrt_ge_0_iff zero_le_divide_1_iff zero_le_numeral zero_le_power)
  ultimately have "cos(2*\<theta>) = (cos(\<theta>))\<^sup>2 - ((1/(sqrt(2)^n))\<^sup>2)" using \<theta>_def sin_arcsin by simp
  also have "... = (cos(\<theta>))\<^sup>2 - (1/2^n)" by simp
  also have "... = (sqrt(1-(1/sqrt(2)^n)\<^sup>2))\<^sup>2 - (1/2^n)" using \<theta>_def cos_arcsin f0 by simp
  finally show ?thesis by (simp add: diff_divide_distrib)
qed
 

lemma (in grover) aux_grover_it_sin_rep:
  fixes m   
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  shows "((2^n-2)/2^n) * (complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1)) * (complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
       = complex_of_real (sin((2*real (Suc m)+1)*\<theta>))" 
proof- 
  have "((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
= cos(2*\<theta>) * (sin((2*real m+1)*\<theta>)) + (2^n-1)/(2^(n-1)) * (complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))"
     using double_cos \<theta>_def by auto
  then have "((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
= cos(2*\<theta>) * (sin((2*real m+1)*\<theta>)) + (complex_of_real ((2^n-1)/(2^(n-1)) * 1/sqrt(2^n-1))) * (complex_of_real (cos((2*real m+1)*\<theta>)))"
    by auto
  moreover have "complex_of_real ((2^n-1)/(2^(n-1)) * 1/sqrt(2^n-1)) = complex_of_real(sin(2*\<theta>))" (*TODO: start with this *) 
  proof-
    have "sin(2*\<theta>) = sqrt(2^n-1) * (2/2^n)" using double_sinus \<theta>_def by auto
    also have "... = sqrt(2^n-1) * 1/2^(n-1)" by simp
    also have "... = ((2^n-1)/sqrt(2^n-1)) * 1/2^(n-1)" using aux_calculation_pow_2 sorry
    finally show "complex_of_real ((2^n-1)/(2^(n-1)) * 1/sqrt(2^n-1)) = complex_of_real(sin(2*\<theta>))" 
      by (smt divide_divide_eq_left mult.commute)
  qed
  ultimately have "((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
= cos(2*\<theta>) * (sin((2*real m+1)*\<theta>)) + (sin(2*\<theta>)) * (complex_of_real (cos((2*real m+1)*\<theta>)))"
    by presburger
  then have "((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
= sin((2*real m+1)*\<theta>) * cos(2*\<theta>) + cos((2*real m+1)*\<theta>) * sin(2*\<theta>)" by simp
  then have "((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
= (sin((2*real m+1)*\<theta>+2*\<theta>))"
    using sin_add[of "(2*real m+1)*\<theta>" "2*\<theta>"] by auto
  moreover have "(2*real m+1)*\<theta>+2*\<theta> = 2*real m*\<theta>+\<theta>+2*\<theta>" 
    by (simp add: semiring_normalization_rules(2))
  moreover have "2*real m*\<theta>+\<theta>+2*\<theta> = 2*(real m + 1)*\<theta>+\<theta>"
    using semiring_normalization_rules(2)[of "real m" "2*\<theta>"] by linarith
  moreover have "2*(real m + 1)*\<theta>+\<theta> = (2*(real m + 1)+1)*\<theta>" 
    using semiring_normalization_rules(2)[of "2*(real m + 1)" "\<theta>"] by simp
  ultimately have "((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
= (sin((2*(real m + 1)+1)*\<theta>))" by auto
  then show "((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
       = complex_of_real (sin((2*real (Suc m)+1)*\<theta>))" 
    by auto
qed


lemma (in grover) aux_grover_it_cos_rep:
  fixes m
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  shows "2/2^n*-(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
       = complex_of_real (1/sqrt(2^n-1)*cos((2*real (Suc m)+1)*\<theta>))"
proof-    
  have "2/2^n*-(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
      = -2/2^n*(sin((2*real m+1)*\<theta>)) + (2^n-2)/2^n*(1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>))"
    by auto
  moreover have "sqrt(2^n-1) \<noteq> 0" 
    by (metis (no_types, hide_lams) add.left_neutral cancel_ab_semigroup_add_class.diff_right_commute diff_0 diff_eq_diff_less_eq 
        diff_minus_eq_add diff_numeral_special(11) diff_zero dim eq_iff_diff_eq_0 le_minus_one_simps(1) le_minus_one_simps(3)
        power_increasing real_sqrt_eq_zero_cancel_iff semiring_normalization_rules(33)) 
  ultimately have "2/2^n * -(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
      = 1/sqrt(2^n-1) * (sqrt(2^n-1) * -2/2^n * (sin((2*real m+1)*\<theta>))) + 1/sqrt(2^n-1) * (2^n-2)/2^n*(cos((2*real m+1)*\<theta>))"
    using divide_self_if by auto
  then have "2/2^n * -(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
      = 1/sqrt(2^n-1) * (sqrt(2^n-1) * -2/2^n * (sin((2*real m+1)*\<theta>))) + 1/sqrt(2^n-1) * ((2^n-2)/2^n * cos((2*real m+1)*\<theta>))"
    by auto
  then have "2/2^n * -(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
      = 1/sqrt(2^n-1) * (sqrt(2^n-1) * -2/2^n * (sin((2*real m+1)*\<theta>)) + (2^n-2)/2^n * cos((2*real m+1)*\<theta>))"
    using comm_semiring_class.distrib[of "(sqrt(2^n-1) * -2/2^n * (sin((2*real m+1)*\<theta>)))" "((2^n-2)/2^n * cos((2*real m+1)*\<theta>))"
          "1/sqrt(2^n-1)"] mult.commute by auto
  then have "2/2^n * -(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
      = 1/sqrt(2^n-1) * ((sqrt(2^n-1) * -2/2^n) * (sin((2*real m+1)*\<theta>)) + ((2^n-2)/2^n) * cos((2*real m+1)*\<theta>))"
    by auto
  moreover have "(sqrt(2^n-1) * -2/2^n) = -sin(2*\<theta>)" using double_sinus \<theta>_def by auto
  moreover have "((2^n-2)/2^n) = cos(2*\<theta>)" using double_cos \<theta>_def by auto
  ultimately have "2/2^n * -(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
      = 1/sqrt(2^n-1) * (-sin(2*\<theta>) * (sin((2*real m+1)*\<theta>)) + cos(2*\<theta>) * cos((2*real m+1)*\<theta>))"
    by presburger
  then have "2/2^n * -(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
      = 1/sqrt(2^n-1) * cos((2*real m+1)*\<theta>+2*\<theta>)" using cos_add[of "(2*real m+1)*\<theta>"] by auto
   moreover have "(2*real m+1)*\<theta>+2*\<theta> = 2*real m*\<theta>+\<theta>+2*\<theta>"
    by (simp add: semiring_normalization_rules(2))
  moreover have "2*real m*\<theta>+\<theta>+2*\<theta> = 2*(real m + 1)*\<theta>+\<theta>"
    using semiring_normalization_rules(2)[of "real m" "2*\<theta>"] by linarith
  moreover have "2*(real m + 1)*\<theta>+\<theta> = (2*(real m + 1)+1)*\<theta>" 
    using semiring_normalization_rules(2)[of "2*(real m + 1)" "\<theta>"] by simp
  ultimately have "2/2^n * -(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
      = 1/sqrt(2^n-1) * cos((2*real (Suc m)+1)*\<theta>)" by auto
  then show "2/2^n*-(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
       = complex_of_real (1/sqrt(2^n-1)*cos((2*real (Suc m)+1)*\<theta>))" by auto
qed

lemma (in grover) t2:
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  shows "grover_iter m = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*m+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*m+1)*\<theta>)) )) \<Otimes> (H * |one\<rangle>)"
proof(induction m)
  have "grover_iter 0 = (\<psi>\<^sub>1\<^sub>0 n) \<Otimes> (H * |one\<rangle>)" sorry
  moreover have "(\<psi>\<^sub>1\<^sub>0 n) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>))))"
  proof
    fix i j::nat
    assume a0: "i < dim_row (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>))))"
       and a1: "j < dim_col (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>))))"
    show "(\<psi>\<^sub>1\<^sub>0 n) $$ (i,j) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)))) $$ (i,j)"
    proof(rule disjE)
      show "i \<noteq> x \<or> i = x" by auto
    next
      assume a2: "i = x"
      then have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)))) $$ (i,j)
          = sin(arcsin((1/(sqrt(2)^n))))" using a1 searched_dom \<theta>_def by auto
      moreover have "- 1 \<le> 1/(sqrt(2)^n)" 
        by (meson le_minus_one_simps(1) order_trans real_sqrt_ge_0_iff zero_le_divide_1_iff zero_le_numeral zero_le_power)
      ultimately have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)))) $$ (i,j)
          = 1/(sqrt(2)^n)" using arcsin by auto
      moreover have "(\<psi>\<^sub>1\<^sub>0 n) $$ (i,j) = 1/(sqrt(2))^n" using searched_dom a1 a2 by auto
      ultimately show  "(\<psi>\<^sub>1\<^sub>0 n) $$ (i,j) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)) )) $$ (i,j)"
        by auto
    next
      assume a2: "i \<noteq> x"
      then have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)))) $$ (i,j)
          = 1/sqrt(2^n-1)*cos(arcsin((1/(sqrt(2)^n))))" using a0 a1 \<theta>_def by auto
      moreover have "-1 \<le> 1/(sqrt(2)^n)" 
        by (meson le_minus_one_simps(1) order.trans real_sqrt_ge_0_iff zero_le_divide_1_iff zero_le_numeral zero_le_power)
      moreover have "1 \<ge> 1/(sqrt(2)^n)" by simp
      ultimately have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)))) $$ (i,j)
          = 1/sqrt(2^n-1)*sqrt(1-((1/(sqrt(2)^n))\<^sup>2))" 
        using cos_arcsin by auto
      moreover have "(1/(sqrt(2)^n))\<^sup>2 = 1/2^n" 
        by (smt one_power2 power_divide real_sqrt_pow2 real_sqrt_power zero_le_power)
      ultimately have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)))) $$ (i,j)
          = 1/sqrt(2^n-1)*sqrt(1-1/2^n)" by auto
      moreover have "sqrt(1-1/2^n) = sqrt((2^n-1)/2^n)" 
      proof-
        have "sqrt(1-1/2^n) = sqrt(2^n/2^n-1/2^n)" by simp
        then show "sqrt(1-1/2^n) = sqrt((2^n-1)/2^n)" 
          by (metis diff_divide_distrib)
      qed
      moreover have "complex_of_real (1/sqrt(2^n-1)*sqrt((2^n-1)/2^n)) = complex_of_real (1/sqrt(2)^n)"
      proof-
        have "1/sqrt(2^n-1)*sqrt((2^n-1)/2^n) = sqrt(1/(2^n-1))*sqrt((2^n-1)/2^n)" by (simp add: real_sqrt_divide)
        then have "1/sqrt(2^n-1)*sqrt((2^n-1)/2^n) = sqrt(1/(2^n-1)*(2^n-1)/2^n)" using real_sqrt_mult by (metis times_divide_eq_right)
        then have "1/sqrt(2^n-1)*sqrt((2^n-1)/2^n) = sqrt((1/(2^n-1)*(2^n-1))*1/2^n)" by simp
        then have "1/sqrt(2^n-1)*sqrt((2^n-1)/2^n) = sqrt(1/2^n)" 
          by (smt dim divide_self_if one_power2 power2_eq_square power_increasing power_one_right times_divide_eq_left times_divide_eq_right)
        then have "1/sqrt(2^n-1)*sqrt((2^n-1)/2^n) = 1/sqrt(2^n)" by (simp add: real_sqrt_divide)
        then show "complex_of_real (1/sqrt(2^n-1)*sqrt((2^n-1)/2^n)) = complex_of_real (1/sqrt(2)^n)" by (simp add: real_sqrt_power)
      qed
      ultimately have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)))) $$ (i,j)
          = (1/sqrt(2)^n)" by auto
      then show "(\<psi>\<^sub>1\<^sub>0 n) $$ (i,j) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)) )) $$ (i,j)"
        using a0 a1 a2 by auto
    qed
  next
    show "dim_row (\<psi>\<^sub>1\<^sub>0 n) = dim_row (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)) ))"
      by auto
  next
    show "dim_col (\<psi>\<^sub>1\<^sub>0 n) = dim_col (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)) ))"
      by auto
  qed
  ultimately show "grover_iter 0 = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real 0+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real 0+1)*\<theta>)))) \<Otimes> (H * |one\<rangle>)"
    by auto
next
  fix m 
  assume IH: "grover_iter m = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*m+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*m+1)*\<theta>)) )) \<Otimes> (H * |one\<rangle>)"
  have "grover_iter (m+1) = (D \<Otimes> Id 1) * (O * (grover_iter m))" by auto
  then have "grover_iter (m+1) 
= (D \<Otimes> Id 1) * (O * ((Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real m+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)) )) \<Otimes> (H * |one\<rangle>)))"
    using IH by auto
  moreover have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real m+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)) ))
= (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then complex_of_real (sin((2*real m+1)*\<theta>)) else complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>))))"
    by auto
  ultimately have "grover_iter (m+1) 
= (D \<Otimes> Id 1) * (O * ((Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then complex_of_real (sin((2*real m+1)*\<theta>)) else complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))) \<Otimes> (H * |one\<rangle>)))"
    by auto
  then have "grover_iter (m+1) = (D \<Otimes> Id 1) * ((Matrix.mat (2^n) 1 (\<lambda>(i,j). (if i=x then - complex_of_real (sin((2*real m+1)*\<theta>)) else complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>))))) \<Otimes> (H * |one\<rangle>))"
    using app_oracle[of "sin((2*real m+1)*\<theta>)" "1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)"] by auto
  moreover have "state n (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -complex_of_real (sin((2*real m+1)*\<theta>)) else complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>))))"
    sorry
  ultimately have "grover_iter (m+1) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x 
then ((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
else 2/2^n*-(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>))) ))
 \<Otimes> (H * |one\<rangle>)"
    using app_diffusion_op_res[of "complex_of_real (sin((2*real m+1)*\<theta>))" "complex_of_real(1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>))"] by auto
  moreover have "((2^n-2)/2^n)*(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-1)/(2^(n-1))*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
= complex_of_real (sin((2*real (Suc m)+1)*\<theta>))" 
    using aux_grover_it_sin_rep \<theta>_def by auto
  moreover have "2/2^n*-(complex_of_real (sin((2*real m+1)*\<theta>))) + (2^n-2)/2^n*(complex_of_real (1/sqrt(2^n-1)*cos((2*real m+1)*\<theta>)))
= complex_of_real (1/sqrt(2^n-1)*cos((2*real (Suc m)+1)*\<theta>))" 
    using aux_grover_it_cos_rep \<theta>_def by auto
  ultimately have "grover_iter (m+1) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). (if i=x then complex_of_real (sin((2*real (Suc m)+1)*\<theta>)) 
else complex_of_real (1/sqrt(2^n-1)*cos((2* real (Suc m)+1)*\<theta>))) )) \<Otimes> (H * |one\<rangle>)"
    by presburger
  moreover have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). (if i=x then complex_of_real (sin((2*real (Suc m)+1)*\<theta>)) 
else complex_of_real (1/sqrt(2^n-1)*cos((2* real (Suc m)+1)*\<theta>))) ))
=  (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then (sin((2*real (Suc m)+1)*\<theta>)) 
else (1/sqrt(2^n-1)*cos((2* real (Suc m)+1)*\<theta>))) ))" by auto
  ultimately show "grover_iter (Suc m) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*real (Suc m)+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2* real (Suc m)+1)*\<theta>)) )) \<Otimes> (H * |one\<rangle>)"
    by auto
qed

(*See proof online that pi \<le> 22/7? *) 
lemma pi_bounds [simp]:
  shows "pi \<ge> 3" and "pi \<le> 22/7"
  sorry

lemma pi_div_4:
  shows "\<lceil>pi/4\<rceil> = 1" and "\<lfloor>pi/4\<rfloor> = 0"  
  using pi_bounds apply (simp add: ceiling_eq_iff) 
  using pi_less_4 pi_not_less_zero by linarith

lemma pi_square_le:
  shows "pi * pi \<le> (10::real)" 
proof- 
  have "pi \<le> 22/7" sorry
  moreover have "22/7*22/7 \<le> 10" sorry
  ultimately show ?thesis sorry
qed

lemma pi_half_square[simp]:
  shows "pi/2 * pi/2 \<le> 2.5" 
proof-
  have "pi/2 * pi/2 = (pi * pi)/(2*2)" by simp
  then have "pi/2 * pi/2 \<le> 10/4" using pi_square_le by auto
  then show ?thesis by auto
qed

lemma limit_on_arcsin:
  fixes n
  assumes "n\<ge>2"
  shows "pi/4*(arcsin((1/(sqrt(2)^n)))) \<le> 1/2"
proof(rule Nat.nat_induct_at_least[of 2 n])
  show "2 \<le> n" using assms by auto
next
  have "arcsin(sin(pi/6)) = pi/6" using arcsin_sin[of "pi/6"] by simp
  moreover have "sin(pi/6) = 1/2" by (simp add: sin_30)
  ultimately have "arcsin(1/2) = pi/6" using arcsin_eq_iff by auto
  moreover have "pi/4*pi/6 \<le> 1/2" using pi_square_le by auto
  ultimately show "pi/4*(arcsin((1/(sqrt(2)^2)))) \<le> 1/2" 
    by (simp add: \<open>arcsin (1 / 2) = pi / 6\<close>)
next
  fix n::nat
  assume a0: "n \<ge> 2"
  and IH: "pi/4*(arcsin((1/(sqrt(2)^n)))) \<le> 1/2"
  have "1/(sqrt(2)^(Suc n)) \<le> 1/(sqrt(2)^n)" 
  proof(induction n)
    show "1/(sqrt(2)^(Suc 0)) \<le> 1/(sqrt(2)^0)"
      by simp
  next
    fix n
    assume IH: "1/(sqrt(2)^(Suc n)) \<le> 1/(sqrt(2)^n)" 
    have "1/(sqrt(2)^(Suc (Suc n))) \<le> 1/sqrt(2)*1/(sqrt(2)^(Suc n))" by simp
    moreover have "1/sqrt(2) \<ge> 0" and "1/sqrt(2) \<le> 1" by auto
    ultimately have "1/(sqrt(2)^(Suc (Suc n))) \<le> 1/sqrt(2)*1/(sqrt(2)^n)" using IH a1 
      by (smt divide_divide_eq_left divide_right_mono power_Suc real_sqrt_ge_0_iff zero_le_power)
    then show "1/(sqrt(2)^(Suc (Suc n))) \<le> 1/(sqrt(2)^(Suc n))" 
      by simp
  qed
  moreover have "\<bar>1/(sqrt(2)^(Suc n))\<bar> \<le> (1::real)" 
  proof-
    have "1/(sqrt(2)^(Suc n)) \<le> 1" 
      by (smt divide_le_eq_1_pos one_le_power real_sqrt_ge_1_iff)
    moreover have "-1/(sqrt(2)^(Suc n)) \<le> 1" 
      by (smt divide_nonpos_nonneg real_sqrt_ge_0_iff zero_le_power)
    ultimately show ?thesis by auto
  qed
  moreover have "\<bar>1/(sqrt(2)^n)\<bar> \<le> (1::real)" 
  proof-
    have "1/(sqrt(2)^n) \<le> 1" by simp
    moreover have "-1/(sqrt(2)^n) \<le> 1" 
      by (smt divide_nonpos_nonneg real_sqrt_ge_0_iff zero_le_power)
    ultimately show ?thesis by auto
  qed
  ultimately have "(arcsin((1/(sqrt(2)^(Suc n))))) \<le> (arcsin((1/(sqrt(2)^n))))"
    using arcsin_le_mono[of "1/(sqrt(2)^(Suc n))" "1/(sqrt(2)^n)"] by auto
  then have "pi/4*(arcsin((1/(sqrt(2)^(Suc n))))) \<le> pi/4*(arcsin((1/(sqrt(2)^n))))" by auto
  then show "pi/4*(arcsin((1/(sqrt(2)^(Suc n))))) \<le> 1/2" using IH by linarith
qed

lemma mult_mono_times_2:
  fixes a b c::real
  assumes "a \<le> b" and "c\<ge>0" and "c\<le>1"
  shows "2*a*c \<le> 2*b*c"
  by (simp add: assms(1) assms(2) mult_right_mono)

lemma aux_sqrt_2_sin [simp]:
  assumes "n \<ge> 4" (* 3 would be enough *)
  shows "1/sqrt(2)^n \<le> sin(1/2)"  
  sorry



(*In the paper it just says \<theta> \<approx> sin(\<theta>) = 1/sqrt(2)^n. I tried to find a bound for the difference *)
lemma (in grover) aux_prob_no_success:
  fixes \<theta>::real
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  assumes "n \<ge> 4"
  shows "(cos((2*iterations+1)*\<theta>)) \<le> sin(\<theta>)"
proof-
  define it where "it \<equiv> pi/4*1/\<theta>"
  have f0: "\<theta> \<le> pi/2 \<and> \<theta> \<ge> -pi/2"
  proof-
    have "-1 < 1/(sqrt(2)^n)" 
      by (smt real_sqrt_ge_0_iff zero_le_divide_1_iff zero_le_power)
    moreover have "1/(sqrt(2)^n) < 1" using assms by simp
    ultimately show ?thesis using arcsin_bounded[of "1/(sqrt(2)^n)"] \<theta>_def by auto
  qed

  have f1: "\<theta> > 0" using \<theta>_def arcsin_less_mono[of 0] by simp

  have f2: "\<theta> \<le> 1/2"
  proof-
    have "arcsin (sin ((1::real)/2)) = 1/2" using arcsin_sin pi_ge_two by auto
    moreover have "1/sqrt(2)^n \<le> (sin (1/2))" using aux_sqrt_2_sin[of n] assms by auto
    ultimately show ?thesis using \<theta>_def arcsin_le_mono[of "1/sqrt(2)^n" "sin (1/2)"] by auto
  qed

  have f3: "1/\<theta> \<le> sqrt(2)^n"
  proof-
    have "\<theta> \<ge> sin(\<theta>)" using f1 by (simp add: sin_x_le_x)
    then have "1 \<ge> sin(\<theta>)*1/\<theta>" by (simp add: f1)
    moreover have "sin(\<theta>) = 1/sqrt(2)^n" 
      by (smt \<theta>_def divide_le_eq_1_pos one_le_power real_sqrt_ge_1_iff sin_arcsin zero_le_divide_1_iff)
    ultimately have "1 \<ge> 1/sqrt(2)^n * 1/\<theta>" by simp
    then show ?thesis 
      by (metis divide_divide_eq_left divide_le_eq_1_pos mult.left_neutral real_sqrt_gt_0_iff rel_simps(51) 
          semiring_normalization_rules(7) zero_less_power) 
  qed
 
  have f4: "abs (-\<lfloor>it\<rfloor>+(pi-2*\<theta>)/4*1/\<theta>) \<le> 1/2"
  proof-
    have "-\<lfloor>it\<rfloor>+(pi-2*\<theta>)/4*1/\<theta> \<le> 1/2"
    proof-
      have "(pi-2*\<theta>)/4*1/\<theta> = pi/4*1/\<theta>-2*\<theta>/4*1/\<theta>" by (simp add: diff_divide_distrib)
      moreover have "2*\<theta>/4*1/\<theta> = 1/2" using f1 by auto
      ultimately have "(pi-2*\<theta>)/4*1/\<theta> = pi/4*1/\<theta>-1/2" by simp 
      then have "-\<lfloor>it\<rfloor>+(pi-2*\<theta>)/4*1/\<theta> = -\<lfloor>pi/4*1/\<theta>\<rfloor>+pi/4*1/\<theta>-1/2" using it_def by (smt divide_minus_left mult_minus_left)
      moreover have "-\<lfloor>pi/4*1/\<theta>\<rfloor>+pi/4*1/\<theta> \<le> 1" by linarith
      ultimately show "-\<lfloor>it\<rfloor>+(pi-2*\<theta>)/4*1/\<theta> \<le> 1/2" by auto
    qed
    moreover have "\<lfloor>it\<rfloor>-(pi-2*\<theta>)/4*1/\<theta> \<le> 1/2" 
    proof-
      have "(pi-2*\<theta>)/4*1/\<theta> = pi/4*1/\<theta>-2*\<theta>/4*1/\<theta>" by (simp add: diff_divide_distrib)
      moreover have "2*\<theta>/4*1/\<theta> = 1/2" using f1 by auto
      ultimately have "(pi-2*\<theta>)/4*1/\<theta> = pi/4*1/\<theta>-1/2" by simp 
      then have "\<lfloor>it\<rfloor>-(pi-2*\<theta>)/4*1/\<theta> = \<lfloor>pi/4*1/\<theta>\<rfloor>-pi/4*1/\<theta>+1/2" using it_def by (smt divide_minus_left mult_minus_left)
      moreover have "\<lfloor>pi/4*1/\<theta>\<rfloor>-pi/4*1/\<theta> \<le> 0" by simp
      ultimately show "\<lfloor>it\<rfloor>-(pi-2*\<theta>)/4*1/\<theta> \<le> 1/2" by linarith
    qed
    ultimately show ?thesis by linarith
  qed


(*abs part may be deleted if not needed anymore, i.e. just keep (cos((2*\<lfloor>it\<rfloor>+1)*\<theta>)) \<le> (sin(\<theta>))  *)
  have "abs (cos((2*\<lfloor>it\<rfloor>+1)*\<theta>)) \<le> (sin(\<theta>))"
  proof-
    have "abs ((2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta>) \<le> \<theta>"  
    proof-
      have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta>"
      proof-
        have "\<lfloor>it\<rfloor> \<le> 1/2+(pi-2*\<theta>)/4*1/\<theta>" using f4 by linarith
        then have "2*\<lfloor>it\<rfloor>*\<theta> \<le> 2*(1/2+(pi-2*\<theta>)/4*1/\<theta>)*\<theta>" 
          using mult_mono_times_2[of "\<lfloor>it\<rfloor>" "1/2+(pi-2*\<theta>)/4*1/\<theta>" \<theta>] f1 f2 by auto
        moreover have "(2*\<lfloor>it\<rfloor>+1)*\<theta> = 2*\<lfloor>it\<rfloor>*\<theta> + \<theta>" 
          by (metis (no_types, hide_lams) add.commute dbl_def mult.right_neutral mult_2_right 
              mult_hom.hom_add of_int_hom.hom_add of_int_hom.hom_one semiring_normalization_rules(7))
        ultimately have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> 2*(1/2+(pi-2*\<theta>)/4*1/\<theta>)*\<theta> + \<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta>"
          by auto
        then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> 2*(1/2+(pi-2*\<theta>)/4*1/\<theta>)*\<theta> + \<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>*\<theta> + \<theta>)"
          using distrib_right[of "2*(pi-2*\<theta>)/4*1/\<theta>" 1 \<theta>] by auto
        then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> (1+2*(pi-2*\<theta>)/4*1/\<theta>)*\<theta> + \<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>*\<theta> + \<theta>)"
          using distrib_right by auto
        then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta> + 2*(pi-2*\<theta>)/4*1/\<theta>*\<theta> + \<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>*\<theta> + \<theta>)"
          using distrib_left by (smt semiring_normalization_rules(2))
        then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta> + \<theta> - \<theta>" by simp
        then show "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta>" by simp
      qed
      moreover have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta>" 
      proof-
        have "-\<lfloor>it\<rfloor> \<le> 1/2 - (pi-2*\<theta>)/4*1/\<theta>" using f4 by linarith
        then have "2*-\<lfloor>it\<rfloor>*\<theta> \<le> 2*(1/2 - (pi-2*\<theta>)/4*1/\<theta>)*\<theta>" 
          using mult_mono_times_2[of "-\<lfloor>it\<rfloor>" "1/2-(pi-2*\<theta>)/4*1/\<theta>" \<theta>] f1 f2 by simp
        moreover have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> = -2*\<lfloor>it\<rfloor>*\<theta> - \<theta>" 
          by (simp add: left_diff_distrib)
        ultimately have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> (1 - 2*(pi-2*\<theta>)/4*1/\<theta>)*\<theta> - \<theta> + (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta>" by auto
        then have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta> - 2*(pi-2*\<theta>)/4*1/\<theta>*\<theta> - \<theta> + (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta>" 
          by (simp add: left_diff_distrib)
        then have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta> - 2*(pi-2*\<theta>)/4*1/\<theta>*\<theta> - \<theta> + 2*(pi-2*\<theta>)/4*1/\<theta>*\<theta>+\<theta>" 
          by (smt semiring_normalization_rules(2))
        then have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta> - \<theta>+\<theta>" by auto 
        then show "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + (2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> \<le> \<theta>" by auto 
      qed
      ultimately show ?thesis by linarith
    qed
    moreover have "(2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> = pi/2" 
    proof-
      have "(2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> = 2*(pi-2*\<theta>)/4*1/\<theta>*\<theta>+\<theta>" 
        by (metis semiring_normalization_rules(2))
      also have "... = 2*(pi-2*\<theta>)/4+\<theta>" using f1 by auto
      also have "... = (2*pi-4*\<theta>)/4+\<theta>" by auto
      also have "... = 2*pi/4-4*\<theta>/4+\<theta>" by (simp add: diff_divide_distrib)
      also have "... = pi/2-\<theta>+\<theta>" by simp
      finally show "(2*(pi-2*\<theta>)/4*1/\<theta>+1)*\<theta> = pi/2" by auto
    qed
    ultimately have f4: "abs ((2*\<lfloor>it\<rfloor>+1)*\<theta> - pi/2) \<le> \<theta>" by linarith
    
    have "cos((2*\<lfloor>it\<rfloor>+1)*\<theta>) \<le> (sin(\<theta>))" 
    proof-
      have "- (pi / 2) \<le> real_of_int (-(2 * \<lfloor>it\<rfloor> + 1)) * \<theta> + pi / 2" using f0 f4 by linarith
      moreover have "real_of_int (-(2 * \<lfloor>it\<rfloor> + 1)) * \<theta> + pi / 2 \<le> pi / 2"  
        by (smt divide_nonneg_nonneg f1 it_def mult_minus_left mult_nonneg_nonneg of_int_le_0_iff pi_ge_zero zero_le_floor)
      moreover have "- (pi / 2) \<le> -\<theta>" and "-\<theta> \<le> pi / 2" 
        using f0 pi_half_ge_zero f2 by auto
      moreover have "(real_of_int (- ((2::int) * \<lfloor>it\<rfloor> + (1::int))) * \<theta> + pi / (2::real) \<le> \<theta>)" using f4 by linarith
      ultimately have "sin(-(2*\<lfloor>it\<rfloor>+1)*\<theta>+pi/2) \<le> sin(\<theta>)"
        using sin_mono_le_eq[of "-(2*\<lfloor>it\<rfloor>+1)*\<theta>+pi/2" "\<theta>"] by auto
      moreover have "sin(-(2*\<lfloor>it\<rfloor>+1)*\<theta>+pi/2) = sin(pi/2-(2*\<lfloor>it\<rfloor>+1)*\<theta>)" 
        by (metis (no_types, hide_lams) add.commute arcsin_1 minus_real_def mult.commute mult_minus_right of_int_hom.hom_uminus)
      moreover have "sin(pi/2-(2*\<lfloor>it\<rfloor>+1)*\<theta>) = cos((2*\<lfloor>it\<rfloor>+1)*\<theta>)" 
        using cos_sin_eq[of "(2*\<lfloor>it\<rfloor>+1)*\<theta>"] by auto
      ultimately show ?thesis by simp
    qed
    moreover have "-cos((2*\<lfloor>it\<rfloor>+1)*\<theta>) \<le> (sin(\<theta>))" 
    proof-
      have "- pi/2 \<le> real_of_int (2*\<lfloor>it\<rfloor>+1)*\<theta>-pi/2" 
        using f0 f4 by linarith
      moreover have "real_of_int (2*\<lfloor>it\<rfloor>+1)*\<theta>-pi/2 \<le> pi/2" 
        using f0 f4 by auto
      ultimately have "sin((2*\<lfloor>it\<rfloor>+1)*\<theta>-pi/2) \<le> sin(\<theta>)"
        using sin_mono_le_eq[of "(2*\<lfloor>it\<rfloor>+1)*\<theta>-pi/2" "\<theta>"] f4 f0 by simp
      moreover have "-(-(2*\<lfloor>it\<rfloor>+1)*\<theta>+pi/2) = (2*\<lfloor>it\<rfloor>+1)*\<theta>-pi/2" by linarith
      ultimately have "sin(-(-(2*\<lfloor>it\<rfloor>+1)*\<theta>+pi/2)) \<le> sin(\<theta>)" by simp
      then have "-sin((-(2*\<lfloor>it\<rfloor>+1)*\<theta>+pi/2)) \<le> sin(\<theta>)" 
        by (metis sin_minus)
      moreover have "-sin(-(2*\<lfloor>it\<rfloor>+1)*\<theta>+pi/2) = -sin(pi/2-(2*\<lfloor>it\<rfloor>+1)*\<theta>)" 
        by (metis (no_types, hide_lams) add.commute arcsin_1 minus_real_def mult.commute mult_2_right mult_minus_right of_int_hom.hom_uminus)
      moreover have "-sin(pi/2-(2*\<lfloor>it\<rfloor>+1)*\<theta>) = -cos((2*\<lfloor>it\<rfloor>+1)*\<theta>)" 
        using cos_sin_eq[of "(2*\<lfloor>it\<rfloor>+1)*\<theta>"] by auto
      ultimately have "-cos((2*\<lfloor>it\<rfloor>+1)*\<theta>) \<le> (sin(\<theta>))" by linarith
      then show ?thesis by linarith
    qed
    ultimately show ?thesis by auto
  qed
  moreover have "(cos((2*iterations+1)*\<theta>)) \<le> (cos((2*\<lfloor>it\<rfloor>+1)*\<theta>))" 
  proof-
    have h1: "sqrt(2)^n*\<theta> \<le> pi" sorry

    have "(2*\<lfloor>it\<rfloor>+1)*\<theta> \<le> (2*iterations+1)*\<theta>" 
    proof-
      have "0 \<le> 1/\<theta>" using f1 by auto
      then have "pi/4*1/\<theta> \<le> pi/4*sqrt(2)^n" using mult_mono[of "pi/4" "pi/4" "1/\<theta>" "sqrt(2)^n"] f3 by auto
      then have "\<lfloor>pi/4*1/\<theta>\<rfloor> \<le> \<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>" using floor_mono by blast
      then have "\<lfloor>it\<rfloor> \<le> iterations"
        using it_def iterations_def iterations_nat real_sqrt_power by auto
      then show ?thesis using f1 by simp
    qed
    moreover have "(2*iterations+1)*\<theta> \<le> pi" 
    proof-
      have "(2*iterations+1)*\<theta> = 2*iterations*\<theta>+\<theta>" 
        by (simp add: semiring_normalization_rules(2))
      then have "(2*iterations+1)*\<theta> \<le> 2*\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>*\<theta>+\<theta>" 
        by (smt iterations_def iterations_nat mult.left_neutral of_int_of_nat_eq of_nat_add one_add_one semiring_normalization_rules(2))
      moreover have "2*\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>*\<theta>+\<theta> \<le> pi" 
      proof-
        have "\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor> \<le> pi/4 * sqrt(2)^n" 
          using of_int_floor_le by blast
        then have "2*\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor> \<le> pi/2 * sqrt(2)^n" by simp
        then have "2*\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>*\<theta> \<le> pi/2 * sqrt(2)^n*\<theta>" using f1 real_mult_le_cancel_iff1 by blast
        then have "2*\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>*\<theta> \<le> pi/2 * pi/2" using h1 sorry
        then have "2*\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>*\<theta> + \<theta> \<le> pi/2 * pi/2 + 1/2" using f2 by auto
        then have "2*\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>*\<theta> + \<theta> \<le> 2.5 + 1/2" using pi_half_square by auto
        then show "2*\<lfloor>(pi/4 * sqrt(2)^n)\<rfloor>*\<theta> + \<theta> \<le> pi" using pi_bounds(1) by linarith
      qed
      ultimately show "(2*iterations+1)*\<theta> \<le> pi" by linarith
    qed
    moreover have "(2*\<lfloor>it\<rfloor>+1)*\<theta> \<ge> 0"
    proof-
      have "pi/4 \<ge> 0" by simp
      moreover have "1/\<theta> \<ge> 0" using f0 f1 by simp
      ultimately have "\<lfloor>pi/4*1/\<theta>\<rfloor> \<ge> \<lfloor>pi/4\<rfloor>*\<lfloor>1/\<theta>\<rfloor>" by (metis le_mult_floor times_divide_eq_right)
      then have  "\<lfloor>pi/4*1/\<theta>\<rfloor> \<ge> 0*\<lfloor>1/\<theta>\<rfloor>" by (simp add: pi_div_4(2))
      then have "\<lfloor>pi/4*1/\<theta>\<rfloor>*\<theta> \<ge> 0" using \<open>(0::real) \<le> (1::real) / (\<theta>::real)\<close> by auto
      then have "2*\<lfloor>pi/4*1/\<theta>\<rfloor>*\<theta> \<ge> 0" using \<open>(0::real) \<le> (1::real) / (\<theta>::real)\<close> by auto
      then have "2*\<lfloor>pi/4*1/\<theta>\<rfloor>*\<theta>+\<theta> \<ge> 0" using \<open>(0::real) \<le> (1::real) / (\<theta>::real)\<close> by auto
      then show ?thesis using \<open>(0::real) \<le> (1::real) / (\<theta>::real)\<close> it_def by auto 
    qed
    moreover have "(2*iterations+1)*\<theta> \<ge> 0"
    proof-
      have "pi/4 \<ge> 0" by auto
      moreover have "sqrt(2)^n \<ge> 0" by simp
      ultimately have "\<lfloor>pi/4*sqrt(2)^n\<rfloor> \<ge> \<lfloor>pi/4\<rfloor>*\<lfloor>sqrt(2)^n\<rfloor>" by (metis le_mult_floor)
      then have "\<lfloor>pi/4*sqrt(2)^n\<rfloor> \<ge> 0*\<lfloor>sqrt(2)^n\<rfloor>" by simp
      then have "2*\<lfloor>pi/4*sqrt(2)^n\<rfloor>*\<theta>+\<theta> \<ge> 0" using f1 by simp
      then have "2*iterations*\<theta>+\<theta> \<ge> 0" using f1 by auto
      moreover have "2*iterations*\<theta>+\<theta> = (2*iterations+1)*\<theta>" by (simp add: semiring_normalization_rules(2))
      ultimately show ?thesis by simp
    qed
    ultimately show "cos ((2*\<lfloor>it\<rfloor>+1)*\<theta>) \<ge> cos ((2*iterations+1)*\<theta>)"  
      using cos_mono_le_eq[of "(2*iterations+1)*\<theta>" "(2*\<lfloor>it\<rfloor>+1)*\<theta>"] by auto
  qed
  ultimately show ?thesis by auto
qed
 

(* We have a problem here since: "(cos((2*iterations+1)*\<theta>))\<^sup>2 \<le> (sin(\<theta>))\<^sup>2" 
does not hold in general. (cos((2*iterations+1)*\<theta>)) does not has to be \<ge> 0 (see e.g. Wolfram alpha)
and does -(cos((2*iterations+1)*\<theta>)) \<le> sin(\<theta>) really hold?
We could show that there is always a bigger n that satisfies that?*)

lemma (in grover) prob_no_success:
  fixes \<theta> :: real
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  assumes "n \<ge> 4" and "(cos((2*iterations+1)*\<theta>)) \<ge> 0" 
  shows "(2^n-1) * (cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<le> 1/2^n"
proof- 
  have "(cos((2*iterations+1)*\<theta>)) \<le> sin(\<theta>)" using aux_prob_no_success assms by auto
  then have f7: "(cos((2*iterations+1)*\<theta>))\<^sup>2 \<le> (sin(\<theta>))\<^sup>2" using assms power_mono by blast
  have f8: "Im (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)) = 0"
  proof-
    have "Im (1/sqrt(2^n-1)*cos((2*iterations+1)*\<theta>)) = Re (1/sqrt(2^n-1)) * Im (cos((2*iterations+1)*\<theta>)) + Im (1/sqrt(2^n-1)) * Re (cos((2*iterations+1)*\<theta>))"
      by auto
    moreover have "Im (1/sqrt(2^n-1)) = 0" by simp
    moreover have "Im (cos((2*iterations+1)*complex_of_real \<theta>)) = 0" 
      by (metis Im_complex_of_real cos_of_real of_real_mult of_real_of_nat_eq)
    ultimately show ?thesis by auto
  qed 
  then have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 = (Re (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2"
    using norm_def by (smt cmod_power2 zero_eq_power2)
  then have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 = ((1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>))\<^sup>2)" 
    using f8 by auto
  then have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 = (1/sqrt(2^n-1))\<^sup>2 * (cos((2*iterations+1)*complex_of_real \<theta>))\<^sup>2"
    by (metis of_real_power power_mult_distrib)
  moreover have "(1/sqrt(2^n-1))\<^sup>2 = 1/(2^n-1)" by (simp add: power_divide)
  ultimately have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 = 1/(2^n-1) * (cos((2*iterations+1)*complex_of_real \<theta>))\<^sup>2"
    by auto
  then have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 = 1/(2^n-1) * (cos((2*iterations+1)*\<theta>))\<^sup>2" 
    by (smt \<open>((1::real) / sqrt ((2::real) ^ (n::nat) - (1::real)))\<^sup>2 = (1::real) / ((2::real) ^ n - (1::real))\<close> \<open>complex_of_real ((cmod (complex_of_real ((1::real) / sqrt ((2::real) ^ (n::nat) - (1::real))) * cos (of_nat ((2::nat) * iterations + (1::nat)) * complex_of_real (\<theta>::real))))\<^sup>2) = complex_of_real (((1::real) / sqrt ((2::real) ^ n - (1::real)))\<^sup>2) * (cos (of_nat ((2::nat) * iterations + (1::nat)) * complex_of_real \<theta>))\<^sup>2\<close> cos_of_real of_real_eq_iff of_real_mult of_real_of_nat_eq of_real_power)
  then have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<le> 1/(2^n-1) * (sin(\<theta>))\<^sup>2"
    using f7 mult_left_mono[of "(cos((2*iterations+1)*\<theta>))\<^sup>2" "(sin(\<theta>))\<^sup>2" "1/(2^n-1)"] by auto
  then have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<le> 1/(2^n-1) * (1/sqrt(2)^n)\<^sup>2"
    using \<theta>_def sin_arcsin by (smt divide_le_eq_1_pos one_le_power real_sqrt_ge_1_iff zero_le_divide_1_iff)
  then have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<le> 1/(2^n-1) * 1/2^n"
   by simp
  then have "(2^n-1) * (cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<le> (2^n-1) * (1/(2^n-1) * 1/2^n)" 
    by (smt mult_left_mono one_le_power)
  then have "(2^n-1) * (cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<le> ((2^n-1) * 1/(2^n-1)) * 1/2^n" 
    by auto
  moreover have "((2::real)^n-1) * 1/(2^n-1) = 1" 
    by (smt aux_calculation_pow_2(2) diff_le_self div_by_1 divide_self one_le_power power_increasing)
  ultimately show "(2^n-1) * (cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<le> 1/2^n" by auto
qed




(*There are several possibilities to solve that we don't want grover_algo $$ (x,0) here but only the first n qubits. *)
lemma (in grover) prob_success:
  fixes \<theta> :: real
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  assumes "n \<ge> 4" and "(cos((2*iterations+1)*\<theta>)) \<ge> 0" 
  shows "1 - (2^n-1) * (cmod (grover_algo $$ (x,0)))\<^sup>2 \<ge> (2^n-1)/2^n"
proof-
  have "grover_algo $$ (x,0) = 1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)" sorry
  have "1 - (2^n-1) * (cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<ge> 1 - 1/2^n"
    using prob_no_success assms by auto
  then have "1 - (2^n-1) * (cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<ge> 2^n/2^n - 1/2^n"
    by auto
  then have "1 - (2^n-1) * (cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<ge> (2^n-1)/2^n"
    by (simp add: diff_divide_distrib)
  then show ?thesis using grover_algo_def sorry
qed














end
