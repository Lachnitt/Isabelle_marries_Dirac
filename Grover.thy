(*
Authors: 
  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
*)



(*TODO: delete all \<alpha>, \<beta> from lemma names*)

theory Grover
imports                           
  More_Tensor
  Binary_Nat
  Basics
  Deutsch_Jozsa (*Just for now so that I don't have to copy everything*)
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
  fixes f:: "nat \<Rightarrow> nat" and n::nat and x:: "nat" (*Would it be better to do it with *? *)
  fixes q_oracle :: "complex Matrix.mat" ("O")
  assumes fun_dom: "f \<in> ({(i::nat). i < 2^n} \<rightarrow>\<^sub>E {0,1})"
  assumes dim: "n\<ge>1"
  assumes searched_dom: "x \<in> {(i::nat). i < 2^n}"
  assumes searched: "\<forall>i < 2^n. f(i) = 1 \<longleftrightarrow> i=x" 
  assumes q_oracle_app: "\<forall>(A::complex Matrix.mat). dim_row A = 2^n \<and> dim_col A = 1 \<longrightarrow>   
                         O * (A \<Otimes> (H * |one\<rangle>)) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (A$$(i,j))))  \<Otimes> (H * |one\<rangle>)"
  assumes q_oracle_gate: "gate (n+1) O"

context grover
begin

definition iterations::nat where
"iterations = nat \<lceil>(pi/4 * sqrt(2^n))\<rceil>"

lemma iterations_nat [simp]:
  shows "nat \<lceil>(pi/4 * sqrt(2^n))\<rceil> = \<lceil>(pi/4 * sqrt(2^n))\<rceil>"
proof-
  have "sqrt(2^n) \<ge> 0" using dim by auto
  then have "(pi/4 * sqrt(2^n)) \<ge> 0" by auto
  then have "\<lceil>(pi/4 * sqrt(2^n))\<rceil> \<ge> 0" by linarith
  then show ?thesis by auto
qed

lemma f_ge_0: 
  shows "\<forall>x. (f x \<ge> 0)" by simp

lemma f_dom_not_zero: 
  shows "f \<in> ({i::nat. n \<ge> 1 \<and> i < 2^n} \<rightarrow>\<^sub>E {0,1})" 
  using fun_dom dim by simp

lemma f_values: "\<forall>x \<in> {(i::nat). i < 2^n} .(f x = 0 \<or> f x = 1)" 
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
  by blast

end (*context grover*)

lemma sum_without_x:
  fixes n i::nat
      and a::complex
  assumes "i<n"
  shows "(\<Sum> k \<in> ({0 ..< n}-{i}). a) = (of_nat n-1)*a " 
  by (metis assms(1) atLeast0LessThan card_atLeastLessThan diff_zero finite_atLeastLessThan lessThan_iff 
      linordered_field_class.sign_simps(20) mult_cancel_right1 sum_constant sum_diff1) 

lemma sum_without_x_and_i:
  fixes n i x::nat
      and a ::complex
  assumes "i<n" and "x<n"  and "i\<noteq>x" 
  shows "(\<Sum> k \<in> ({0 ..< n}-{i,x}). a) = (of_nat n-2)*a" 
proof-
  have "x \<in> {0..<n} - {i} - {}"
    by (metis Diff_insert2 assms(1) assms(2) assms(3) atLeast0LessThan insertE insert_Diff lessThan_iff)
  moreover have "finite ({0..<n} - {i} - {})"
    by blast
  ultimately have "(\<Sum>n\<in>{0..<n} - {i} - {} - {x}. a) = (\<Sum>n\<in>{0..<n} - {i} - {}. a) - a"
   by (meson sum_diff1)
  then have "(\<Sum> k \<in> ({0 ..< n}-{i,x}). a) = (\<Sum> k \<in> ({0 ..< n}-{i}). a) -a" 
    by (metis (no_types) Diff_insert2)
  then have "(\<Sum> k \<in> ({0 ..< n}-{i,x}). a) = (of_nat n-1)*a -a" 
    using assms(1) sum_without_x by auto
  then show "(\<Sum> k \<in> ({0 ..< n}-{i,x}). a) = (of_nat n-2)*a" 
    by (simp add: linordered_field_class.sign_simps(20))
qed

(*Do I need to show that this is 2 |psi><psi|-I? If so how? Show that they give same result on arbitrary vector?*)
definition(in grover) diffusion_operator::"complex Matrix.mat" where
"diffusion_operator = Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if i=j then ((1-2^(n-1))/2^(n-1)) else 1/(2^(n-1)))"

notation(in grover) diffusion_operator ("D")

lemma (in grover) diffusion_operator_values_hidden:
  assumes "i<2^n \<and> j<2^n" 
  shows "(k::nat) \<in> ({0..<2^n}-{i,j}) \<longrightarrow> D$$(i,k) = 1/(2^(n-1)) \<and> D$$(k,j) = 1/(2^(n-1))"
  by (simp add: assms diffusion_operator_def)
    
lemma (in grover) transpose_of_diffusion:
  shows "(D)\<^sup>t = D"
proof
  fix i j::nat
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

lemma (in grover) adjoint_of_diffusion: 
  shows "(D)\<^sup>\<dagger> = D"
proof
  show "dim_row (D\<^sup>\<dagger>) = dim_row D" by (simp add: diffusion_operator_def)
next
  show "dim_col (D\<^sup>\<dagger>) = dim_col D" by (simp add: diffusion_operator_def)
next
  fix i j:: nat
  assume a0: "i < dim_row D" and a1: "j < dim_col D"
  then have f0: "D\<^sup>\<dagger> $$ (i, j) = cnj(D $$ (j,i))" 
    using hermite_cnj_def by (metis case_prod_conv index_mat(1) index_transpose_mat(3) transpose_of_diffusion)
  show "D\<^sup>\<dagger> $$ (i, j) = D $$ (i, j)"
  proof(rule disjE)
    show "i=j \<or> i\<noteq>j" by auto
  next
    assume a2: "i=j"
    moreover have "D $$ (i, j) = (1 - 2 ^ (n - 1)) / 2 ^ (n - 1)"
        using a0 a2 diffusion_operator_def complex_cnj_cancel_iff by auto
    ultimately show "D\<^sup>\<dagger> $$ (i, j) = D $$ (i, j)" using f0 cnj_def by auto
  next
    assume a2: "i\<noteq>j"
    moreover have "D $$ (i, j) = 1/(2^(n-1))"
      using a0 a1 a2 diffusion_operator_def by auto
    moreover have "D $$ (j, i) = 1/(2^(n-1))"
      using a0 a1 a2 diffusion_operator_def by auto
    ultimately show "D\<^sup>\<dagger> $$ (i, j) = D $$ (i, j)" using f0 cnj_def by auto
  qed
qed
    
lemma (in grover) diffusion_is_gate:
  shows "gate n D"
proof
  show "dim_row D = 2^n" using diffusion_operator_def by auto
next
  show "square_mat D" using diffusion_operator_def by auto
next
  show "unitary D" 
  proof-
    have "D * D = 1\<^sub>m (dim_col D)"
    proof
      show "dim_row (D * D) = dim_row (1\<^sub>m (dim_col D))" by (simp add: diffusion_operator_def)
    next
      show "dim_col (D * D) = dim_col (1\<^sub>m (dim_col D))" by (simp add: diffusion_operator_def)
    next
      fix i j:: nat
      assume a0: "i < dim_row (1\<^sub>m (dim_col D))" and a1: "j < dim_col (1\<^sub>m (dim_col D))"
      then have f0: "i < 2^n \<and> j < 2^n" by (simp add: diffusion_operator_def)
      show "(D * D) $$ (i,j) = 1\<^sub>m (dim_col D) $$ (i, j)"
      proof(rule disjE)
        show "i=j \<or> i\<noteq>j" by auto
      next
        assume a2: "i=j"
        then have "(D * D) $$ (i,j) = (\<Sum>k<dim_row D. (D $$ (i,k)) * (D $$ (k,j)))"       
          using a0 a1 
          by (metis (no_types, lifting) index_matrix_prod index_one_mat(2) index_transpose_mat(3) sum.cong transpose_of_diffusion)
        also have "... = (\<Sum>k \<in> ({0..<2^n}). (D $$ (i,k)) * (D $$ (k,j)))"  
          by (simp add: atLeast0LessThan diffusion_operator_def)
        also have "... = (\<Sum>k \<in> ({0..<2^n}-{i}). (D $$ (i,k)) * (D $$ (k,j))) + (D $$ (i,i)) * (D $$ (i,j))" 
          using a1 a2
          by (metis (no_types, lifting) add.commute atLeast0LessThan diffusion_operator_def dim_col_mat(1) finite_atLeastLessThan index_one_mat(3) insert_Diff insert_Diff_single lessThan_iff sum.insert_remove)
        also have "... = (\<Sum>k \<in> ({0..<2^n}-{i}).1/(2^(n-1)) * 1/(2^(n-1))) + ((1-2^(n-1))/2^(n-1)) * ((1-2^(n-1))/2^(n-1)) "
          using diffusion_operator_def a1 a2 by auto
        also have "... = (2^n - 1) * (1 / 2^(n-1) * 1 / 2^(n-1)) + ((1-2^(n-1))/2^(n-1)) * ((1-2^(n-1))/2^(n-1))"
          using sum_without_x[of "i" "2^n" "1/(2^(n-1)) * 1/(2^(n-1))"] a0 a1 dim diffusion_operator_def by simp
        also have "... = ((2^n - 1) + (1-2^(n-1))\<^sup>2)/(2^(n-1))\<^sup>2" 
          by (simp add: power2_eq_square add_divide_distrib)
        also have "... = ((2^n - 1) + (1\<^sup>2+(2^(n-1))\<^sup>2-2*2^(n-1)))/(2^(n-1))\<^sup>2"
          using power2_diff[of 1 "2^(n-1)"]  mult.right_neutral by metis
        also have "... = (2^n +(2^(n-1))\<^sup>2-2*2^(n-1))/(2^(n-1))\<^sup>2" by simp
        also have "... = (2^n +(2^(n-1))\<^sup>2-2^n)/(2^(n-1))\<^sup>2" by (metis dim le_numeral_extra(2) power_eq_if)
        also have "... = 1" by simp
        finally have "(D * D) $$ (i,j) = 1" by auto
        then show "(D * D) $$ (i,j) = 1\<^sub>m (dim_col D) $$ (i, j)" 
          using a1 a2 by auto
      next
        assume a2: "i\<noteq>j"
        then have "(D * D) $$ (i,j) = (\<Sum>k<dim_row D. (D $$ (i,k)) * (D $$ (k,j)))"       
          using a0 a1 
          by (metis (no_types, lifting) index_matrix_prod index_one_mat(2) index_one_mat(3) index_transpose_mat(3) sum.cong 
              transpose_of_diffusion)
        also have "... = (\<Sum>k \<in> ({0..<2^n}). (D $$ (i,k)) * (D $$ (k,j)))"  
          by (simp add: atLeast0LessThan diffusion_operator_def)
        also have "... = (\<Sum>k \<in> ({0..<2^n}-{i,j}). (D $$ (i,k)) * (D $$ (k,j))) 
                       + (D $$ (i,i)) * (D $$ (i,j)) + (D $$ (i,j)) * (D $$ (j,j))"  
          using a0 a1 a2 diffusion_operator_def (*This might be replaceable*)
          by (smt Diff_insert add.commute atLeast0LessThan  dim_col_mat(1) 
              finite_Diff finite_atLeastLessThan index_one_mat(2) index_one_mat(3) insert_Diff insert_Diff_single 
              insert_iff lessThan_iff sum.insert_remove)
        also have "... = (\<Sum>k \<in> ({0..<2^n}-{i,j}). 1/(2^(n-1)) * 1/(2^(n-1))) 
                        + ((1-2^(n-1))/2^(n-1)) * 1/(2^(n-1)) + 1/(2^(n-1)) * ((1-2^(n-1))/2^(n-1))" 
          using diffusion_operator_values_hidden f0 sum.cong a2 diffusion_operator_def by auto
        also have "... = (2^n-2)* 1/2^(n-1) * 1/2^(n-1)
                       + (1-2^(n-1))/2^(n-1) * 1/2^(n-1) + 1/2^(n-1) * (1-2^(n-1))/2^(n-1)" 
          using sum_without_x_and_i[of "i" "2^n" "j" "(1/(2^(n-1)) * 1/(2^(n-1)))"] a0 a1 a2 diffusion_operator_def 
          by auto
        also have "... = (2^n-2) * (1/2^(n-1))\<^sup>2 + (1-2^(n-1)) * (1/2^(n-1))\<^sup>2 + (1-2^(n-1)) * (1/2^(n-1))\<^sup>2" 
          by (simp add: power2_eq_square)
        also have "... = ((2^n-2) + (1-2^(n-1)) + (1-2^(n-1))) * (1/2^(n-1))\<^sup>2" 
          by (metis comm_semiring_class.distrib)
        also have "... = (2^n-2*2^(n-1)) * (1/2^(n-1))\<^sup>2" by auto
        also have "... = (2^n-2^n) * (1/2^(n-1))\<^sup>2" 
          by (metis dim le_add_diff_inverse plus_1_eq_Suc power.simps(2))
        also have "... = 0" by auto
        finally have "(D * D) $$ (i,j) = 0" by auto
        then show "(D * D) $$ (i,j) = 1\<^sub>m (dim_col D) $$ (i, j)" 
          using a0 a1 a2 by auto
      qed
    qed
    then show "unitary D" 
      by (metis adjoint_of_diffusion index_transpose_mat(3) transpose_of_diffusion unitary_def)
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
  have "dim_row v = 2^n \<and> dim_col v = 1" using assms by auto
  then have "O * (v \<Otimes> (H * |one\<rangle>)) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) \<Otimes> (H * |one\<rangle>)"
    using q_oracle_app assms by blast
  moreover have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = w" 
  proof{
    fix i j::nat
    assume "i < dim_row w" 
    and    "j < dim_col w"
    then have f0: "i < 2^n \<and> j=0" using assms by auto
    moreover have "i=x \<longrightarrow> (-1)^f(i) = (-(1::real))" 
      using searched_dom grover_axioms by auto
    moreover have "i\<noteq>x \<and> i < 2^n  \<longrightarrow> (-1)^f(i) = 1" for i::nat
      using searched_dom grover_axioms search_function_zero by auto
    ultimately show "(Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) $$ (i,j) = w $$ (i,j)" 
      using assms f0 by auto
  next
    show "dim_row (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = dim_row w" 
      by (simp add: assms(2))
  next
    show "dim_col (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = dim_col w" 
      by (simp add: assms(2))
  }qed
  ultimately show "O * (v \<Otimes> (H * |one\<rangle>)) = (w \<Otimes> (H * |one\<rangle>))" by blast
qed

lemma (in grover) pow_2_n_half[simp]: (*Give better name*)
  shows "2^n-2^(n-1) = (2::complex)^(n-1)" 
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using dim by auto
next
  show "2^1-2^(1-1) = (2::complex)^(1-1)" by simp
next
  fix n
  assume a0: "n\<ge>1" and IH: "2^n-2^(n-1) = (2::complex)^(n-1)"  
  then have "2^(n+1)-2^n = (2::complex)*(2^n -2^(n-1))" by simp
  also have "... = (2::complex)* 2^(n-1)" using IH by simp
  also have "... = (2::complex)^n" 
    using IH le_add_diff_inverse2 by auto
  finally show "2^(Suc n)-2^((Suc n)-1) = (2::complex)^((Suc n)-1)" by simp
qed

lemma b1 [simp]:
  assumes "n \<ge> 1"
  shows "((2^(n-1)-(1::complex))/2^(n-1)) = (2^n-2)/(2::complex)^n" 
  by (smt One_nat_def Suc_diff_le assms diff_Suc_Suc diff_divide_distrib diff_zero div_self divide_divide_eq_left power.simps(2) power_not_zero zero_neq_numeral)


lemma h3[simp]: 
  assumes "n \<ge> 1"
  shows "(2::complex)/2^n = 1/2^(n-1)"
  sorry

lemma (in grover) app_diffusion_op:
  fixes \<alpha> \<beta>::complex 
  defines "v \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
    and "w \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^n-2)/2^n)*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>
                                             else 2/2^n*-\<alpha> + (2^n-2)/2^n*\<beta> ))"
  shows "D * v = w"
proof
  fix i j::nat
  assume a0: "i < dim_row w" and a1: "j < dim_col w"
  then have f0: "i < 2^n \<and> j=0" using assms by auto
  then have "(D * v) $$ (i,j) = (\<Sum> k \<in> {0 ..< 2^n}. (Matrix.row D i) $ k * (Matrix.col v j) $ k)"
    using assms atLeast0LessThan diffusion_operator_def by auto
  then have f1: "(D * v) $$ (i,j) =
                (\<Sum> k \<in> ({0 ..< 2^n}-{i}). (Matrix.row D i) $ k * (Matrix.col v j) $ k)
              + (Matrix.row D i) $ i * (Matrix.col v j) $ i" 
    by (simp add: f0 sum_diff1)
  show "(D * v) $$ (i,j) = w  $$ (i,j)" 
  proof(rule disjE) 
    show "i=x \<or> i\<noteq>x" by auto
  next
    assume a2: "i=x" 
    moreover have "(\<Sum> k \<in> ({0 ..< 2^n}-{i}).  1/(2^(n-1)) * \<beta>) = (2^n - 1) * \<beta> / 2 ^ (n-1)" 
      using sum_without_x[of i "2^n" "(1/(2^(n-1)) * \<beta>)::complex"] dim f0 
      by (simp add: of_nat_diff)
    moreover have  "((1-2^(n-1))/2^(n-1)) * (-\<alpha>) = ((2^(n-1)-1)/2^(n-1))*\<alpha>" 
      by (metis divide_minus_left minus_diff_eq minus_mult_minus)
    ultimately have f0: "(D * v) $$ (i,j) = ((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>"
      using assms diffusion_operator_def a2 f0 f1
      by (simp add: of_nat_diff)
    then have "(D * v) $$ (i,j) = ((2^n-2)/2^n)*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>" using dim b1 by (simp add: f0)
    then show "(D * v) $$ (i,j) = w $$ (i,j)" using assms a2 a0 a1 f1 by auto
  next
    assume a2: "i\<noteq>x "
    have "(\<Sum> k \<in> ({0 ..< 2^n}-{i}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) =
                   (\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k)
                   + ((Matrix.row D i) $ x * (Matrix.col v j) $ x)" 
      using sum_diff1 a2 f0
      by (smt Diff_insert2 add.commute atLeast0LessThan finite_Diff finite_atLeastLessThan 
          insertE insert_Diff_single insert_absorb lessThan_iff mem_Collect_eq searched_dom sum.insert_remove)
    moreover have "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) = (2^n - 2) /(2^(n-1)) * \<beta>" 
    proof-
      have "i < 2^n \<and> x < 2^n \<and> i \<noteq> x "
        using a2 f0 grover.searched_dom grover_axioms by fastforce
      then have "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). 1/(2^(n-1)) * \<beta>) = (2^n - 2) * (1/2^(n-1) * \<beta>)"
        using sum_without_x_and_i[of i "2^n" x "1/(2^(n-1)) * \<beta>"] assms by auto
      moreover have "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) =
                     (\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). 1/(2^(n-1)) * \<beta>)" 
        using diffusion_operator_def a2 f0 assms by auto
      ultimately show  "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) 
                        = (2^n - 2) /(2 ^ (n-1)) * \<beta>" 
        by simp
    qed
    moreover have "((Matrix.row D i) $ x * (Matrix.col v j) $ x) = 1/2^(n-1)*-\<alpha>" 
      using diffusion_operator_def a2 v_def f0 searched_dom by auto
    moreover have "(Matrix.row D i) $ i * (Matrix.col v j) $ i = ((1-2^(n-1))/2^(n-1))*\<beta>" 
      using diffusion_operator_def a2 f0 v_def searched_dom by auto
    ultimately have  "(D * v) $$ (i,j) = (2^n-2)/(2^(n-1)) * \<beta> + 1/2^(n-1)*-\<alpha> +((1-2^(n-1))/2^(n-1))*\<beta>" 
      using f1 by auto 
    moreover have "(2^n-2)/(2^(n-1)) * \<beta> + ((1-2^(n-1))/2^(n-1))*\<beta> = (2^n-2)/2^n*\<beta>" 
    proof-
      have "(2^n - 2) /(2^(n-1))+((1-2^(n-1))/2^(n-1)) = ((2^n - (2::complex)) + (1 - 2^(n-1))) * 1/(2^(n-1))"
        using comm_semiring_class.distrib[of "(2^n - (2::complex))" "(1-2^(n-1))" "1/(2^(n-1))"] by auto
      also have "... = (2^n-2^(n-1)-(2::complex)+1) * 1/(2^(n-1))" 
        by (simp add: dim)
      also have "... = (2^(n-1)-(1::complex)) * 1/(2^(n-1))" 
        using dim pow_2_n_half by auto
      also have "... = (2^n-(2::complex))/2 * 1/(2^(n-1))" 
        using b1 dim pow_2_n_half by auto
      also have "... = (2^n-(2::complex)) * 1/(2^n)" using b1 pow_2_n_half by auto
      finally show "(2^n - (2::complex)) /(2^(n-1)) * \<beta> + ((1-2^(n-1))/2^(n-1)) * \<beta> = (2^n-2)/2^n*\<beta>" 
        by (metis comm_semiring_class.distrib mult.right_neutral)
    qed
    moreover have "1/2^(n-1)*-\<alpha> = 2/2^n*-\<alpha>" using h3 dim by auto
    ultimately have "(D * v) $$ (i,j) = 2/2^n*-\<alpha> + (2^n-2)/2^n*\<beta>"
      by (metis (mono_tags, hide_lams) add_divide_distrib combine_common_factor power_one_over ring_class.ring_distribs(1) 
          semiring_normalization_rules(24) semiring_normalization_rules(7) uminus_add_conv_diff)
    then show "(D * v) $$ (i,j) = w $$ (i,j)" using assms a2 f0 by auto
  qed
next
  show "dim_row (D * v) = dim_row w" using assms diffusion_operator_def by auto 
next 
  show "dim_col (D * v) = dim_col w" using assms diffusion_operator_def by auto 
qed

lemma (in grover) app_diffusion_op_index_x_recurence:
  fixes \<alpha> \<beta>::complex
  shows "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> = 2 * ((-\<alpha> + (2^n-1)*\<beta>)/2^n) + \<alpha>" 
proof-
  have "((2^(n-1)-1)/2^(n-1))*\<alpha> = ((2^(n-1)-1)*\<alpha>)/2^(n-1)" by simp
  moreover have "(2^(n-1)-1)*\<alpha> = (2^(n-1)*\<alpha>) + (-1*\<alpha>)" 
    by (metis add.inverse_inverse comm_semiring_class.distrib diff_minus_eq_add)
  ultimately have "((2^(n-1)-1)/2^(n-1))*\<alpha> = \<alpha> + (-\<alpha>)/2^(n-1)" 
    by (simp add: diff_divide_distrib)
  then have "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> = \<alpha> + (-\<alpha>)/2^(n-1) + (2^n-1)/(2^(n-1))*\<beta>" 
    by auto
  then have "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> = ((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) + \<alpha>" 
    by (metis (no_types, hide_lams) diff_divide_distrib divide_minus_left is_num_normalize(1) 
        mult.commute semiring_normalization_rules(24) times_divide_eq_right uminus_add_conv_diff)
  then have "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> = 2/2 * ((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) + \<alpha>" by auto
  then show "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> = 2 * ((-\<alpha> + (2^n-1)*\<beta>)/2^n) + \<alpha>" 
    by (metis diff_add_cancel mult_2 pow_2_n_half times_divide_eq_right times_divide_times_eq)
qed


lemma (in grover) app_diffusion_op_res:
  fixes \<alpha> \<beta>::complex 
  defines "v \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
  defines "w \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^n-2)/2^n)*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>
                                             else 2/2^n*-\<alpha> + (2^n-2)/2^n*\<beta> ))"
  assumes "state n v" 
  shows "(D \<Otimes> Id 1) * (v \<Otimes> (H * |one\<rangle>)) = w \<Otimes> (H * |one\<rangle>)" 
proof-
  have "dim_col (Id 1) = dim_row (H * |one\<rangle>)" 
    using assms Id_def
    by (simp add: H_without_scalar_prod)
  moreover have "dim_col D = dim_row v" 
    using assms diffusion_operator_def by auto
  moreover have "dim_col D > 0" and "dim_col v > 0" and "dim_col (Id 1) > 0" and  "dim_col (H * |one\<rangle>) > 0" 
    using assms diffusion_operator_def Id_def ket_vec_def by auto
  ultimately have "(D \<Otimes> Id 1) * (v \<Otimes> (H * |one\<rangle>)) = (D * v) \<Otimes> (Id 1 * (H * |one\<rangle>))" 
    using mult_distr_tensor by auto
  moreover have "(Id 1 * (H * |one\<rangle>)) = (H * |one\<rangle>)" 
    using right_mult_one_mat H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1 Quantum.Id_def by auto
  ultimately show "(D \<Otimes> Id 1) * (v \<Otimes> (H * |one\<rangle>)) = w \<Otimes> (H * |one\<rangle>)" using app_diffusion_op assms by auto
qed


primrec (in grover) grover_iter::"nat\<Rightarrow>complex Matrix.mat" where
"grover_iter 0 = (\<psi>\<^sub>1\<^sub>0 n) \<Otimes> (H * |one\<rangle>)"|
"grover_iter (Suc m) = (D \<Otimes> Id 1) * (O * (grover_iter m))"


lemma h0[simp]:
  shows "(1/sqrt(2)^n)\<^sup>2 = 1/2^n" sorry

lemma[simp]:
  shows "1/sqrt(2)^n = sqrt(1/2^n)" sorry

lemma h1[simp]:
  shows "1/sqrt(2)^n * 1/sqrt(2)^n = 1/2^n" sorry


lemma h2[simp]:
  assumes "x \<ge> 0"
  shows "sqrt(x)/x = 1/sqrt(x)" and "x/sqrt(x) = sqrt(x)" 
   apply (metis (full_types) abs_of_nonneg assms div_by_0 divide_divide_eq_left divide_self_if 
real_sqrt_divide real_sqrt_mult_self real_sqrt_one real_sqrt_zero sqrt_divide_self_eq)
  by (simp add: assms real_div_sqrt)



lemma (in grover) double_sinus: (*Change name *)
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
  also have "... = 2 * sqrt(1-(1/sqrt(2)^n)\<^sup>2) * 1/sqrt(2)^n" using \<theta>_def cos_arcsin f0 by auto
  also have "... = 2 * sqrt((2^n-1)/2^n) * 1/sqrt(2)^n" by (simp add: diff_divide_distrib)
  also have "... = 2 * (sqrt(2^n-1) * sqrt(1/2^n)) * 1/sqrt(2)^n"
    by (metis mult.right_neutral real_sqrt_mult semigroup_mult_class.mult.assoc times_divide_eq_right)
  also have "... = 2 * sqrt(2^n-1) * (1/sqrt(2)^n * 1/sqrt(2)^n)" by auto
  also have "... = 2 * sqrt(2^n-1) * (1/sqrt(2)^n)\<^sup>2" 
    by (metis (no_types, hide_lams) power_divide power_even_eq power_one power_one_right semiring_normalization_rules(36) times_divide_eq_right)
  finally show ?thesis by simp
qed

lemma (in grover) double_cos: (*Change name *)
  fixes m
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  shows "cos(2*\<theta>) = ((2^n-2)/2^n)"
proof-
  have "cos(2*\<theta>) = (cos(\<theta>))\<^sup>2 - ((sin(\<theta>))\<^sup>2)" by (simp add: cos_double) 
  moreover have f0: "-1 \<le> 1/sqrt(2)^n" 
    by (meson le_minus_one_simps(1) order.trans real_sqrt_ge_0_iff zero_le_divide_1_iff zero_le_numeral zero_le_power)
  ultimately have "cos(2*\<theta>) = (cos(\<theta>))\<^sup>2 - ((1/(sqrt(2)^n))\<^sup>2)" using \<theta>_def sin_arcsin by auto
  also have "... = (cos(\<theta>))\<^sup>2 - (1/2^n)" using h0 by auto
  also have "... = (sqrt(1-(1/sqrt(2)^n)\<^sup>2))\<^sup>2 - (1/2^n)" using \<theta>_def cos_arcsin f0 by auto
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
    also have "... = sqrt(2^n-1) * 1/2^(n-1)" using dim h3 by auto
    also have "... = ((2^n-1)/sqrt(2^n-1)) * 1/2^(n-1)" by simp
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
  have "grover_iter 0 = (\<psi>\<^sub>1\<^sub>0 n) \<Otimes> (H * |one\<rangle>)" by auto
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


lemma (in grover) o1[simp]:
  shows "1/sqrt(2)^n \<le> (sin 1)" sorry

lemma (in grover) o2:
  fixes a b c d::real
  assumes "a \<ge> b" and "c \<ge> d" and "b\<ge>1" and "d\<ge>0"
  shows "a * c \<ge> b * d"  
  using assms using mult_mono by fastforce


lemma (in grover)
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  defines "it \<equiv> pi/4*\<theta>"
  shows "(cmod (1/sqrt(2^n-1)*cos((2*it+1)*complex_of_real \<theta>)))\<^sup>2 \<le> 1/(2^n-1) * 1/2^n"
proof-
  have f0: "-1 \<le> 1/(sqrt(2)^n)" 
    by (smt real_sqrt_ge_0_iff zero_le_divide_1_iff zero_le_power)
  moreover have f1: "1/(sqrt(2)^n) \<le> 1" by simp
  ultimately have f2: "\<theta> \<le> pi/2" and f2b: "\<theta> \<ge> -pi/2" using arcsin_bounded[of "1/(sqrt(2)^n)"] \<theta>_def by auto

  have f3: "\<theta> \<ge> 0" using \<theta>_def arcsin_le_mono[of 0] by simp
  moreover have "arcsin (sin (1/sqrt(2)^n)) = 1/sqrt(2)^n" 
    using f1 f2 f3
    by (smt abs_sin_x_le_abs_x arcsin_sin real_sqrt_ge_0_iff sin_pi_half zero_le_divide_1_iff zero_le_power)
  ultimately have f4: "\<theta> \<ge> 1/sqrt(2)^n" using \<theta>_def arcsin_le_mono
    using f0 f1 by (metis (full_types) abs_le_D1 abs_of_nonneg abs_sin_x_le_abs_x arcsin)

 have "arcsin (sin (1::real)) = 1"
    by (metis (full_types) arcsin_0 arcsin_1 arcsin_lt_bounded arcsin_minus_1 arcsin_sin le_less_linear 
        less_minus_one_simps(1) less_numeral_extra(1) not_less_iff_gr_or_eq sin_pi_half sin_x_ge_neg_x sin_x_le_x)
  moreover have "1/sqrt(2)^n \<le> (sin 1)" using o1 by auto
  ultimately have f5: "\<theta> \<le> 1" using \<theta>_def arcsin_le_mono[of "1/sqrt(2)^n" "sin (1)"] by auto
  
  have "-1/\<theta> \<le> -1"sorry

  have j2:"(2*((pi-2*\<theta>)/4*\<theta>)+1)*\<theta> = pi/2" sorry
  then have "abs ((2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta>) \<le> \<theta>"  
  proof-
    have "\<lfloor>it\<rfloor>-(pi-2*\<theta>)/4*\<theta> \<le> 1/2" 
    proof-
      have "-(pi-2*\<theta>)/4*\<theta> = (-pi+2*\<theta>)/4*\<theta>" by auto
      then have "-(pi-2*\<theta>)/4*\<theta> = -pi/4*\<theta>+2*\<theta>/4*\<theta>" 
        by (simp add: left_diff_distrib)
      then have "-(pi-2*\<theta>)/4*\<theta> = -pi/4*\<theta>+\<theta>\<^sup>2/2" sorry
      then have "\<lfloor>it\<rfloor>-(pi-2*\<theta>)/4*\<theta> \<le> \<lfloor>pi/4*\<theta>\<rfloor>-pi/4*\<theta>+\<theta>\<^sup>2/2" using it_def by (smt divide_minus_left mult_minus_left)
      moreover have "\<lfloor>pi/4*\<theta>\<rfloor>-pi/4*\<theta> \<le> 0" by linarith
      moreover have "\<theta>\<^sup>2 \<le> 1" using f5 by (simp add: f3 power_le_one)
      ultimately show "\<lfloor>it\<rfloor>-(pi-2*\<theta>)/4*\<theta> \<le> 1/2" by linarith
    qed
    then have "\<lfloor>it\<rfloor> \<le> 1/2+(pi-2*\<theta>)/4*\<theta>" by linarith
    then have "2*\<lfloor>it\<rfloor>*\<theta> \<le> 2*(1/2+(pi-2*\<theta>)/4*\<theta>)*\<theta>" 
      by (smt divide_nonneg_nonneg f3 f5 mult_mono mult_nonneg_nonneg of_int_add pi_ge_two)
    moreover have "(2*\<lfloor>it\<rfloor>+1)*\<theta> = 2*\<lfloor>it\<rfloor>*\<theta> + \<theta>" 
      by (metis (no_types, hide_lams) add.commute add.left_commute add.right_neutral add_left_cancel dbl_def diff_add_cancel diff_eq_eq distrib_left mult.right_neutral mult_2_right mult_hom.hom_add mult_zero_right of_int_add of_int_hom.hom_add of_int_hom.hom_one of_int_simps(1) semiring_normalization_rules(22) semiring_normalization_rules(7))
    ultimately have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> 2*(1/2+(pi-2*\<theta>)/4*\<theta>)*\<theta> + \<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta>"
      by auto
    then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> 2*(1/2+(pi-2*\<theta>)/4*\<theta>)*\<theta> + \<theta> - (2*(pi-2*\<theta>)/4*\<theta>*\<theta> + \<theta>)"
      using distrib_right[of "2*(pi-2*\<theta>)/4*\<theta>" 1 \<theta>]  by auto
    then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> 2*(1/2+(pi-2*\<theta>)/4*\<theta>)*\<theta> - 2*(pi-2*\<theta>)/4*\<theta>*\<theta>"
      by auto
    then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> (1+2*(pi-2*\<theta>)/4*\<theta>)*\<theta> - 2*(pi-2*\<theta>)/4*\<theta>*\<theta>"
      using distrib_left[of 2 "1/2" "(pi-2*\<theta>)/4*\<theta>"] sorry
    then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> \<theta>+2*(pi-2*\<theta>)/4*\<theta>*\<theta> - 2*(pi-2*\<theta>)/4*\<theta>*\<theta>"
      using distrib_right[of 1 "2*(pi-2*\<theta>)/4*\<theta>" \<theta>]  by auto
    then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> \<theta>"
      by auto


    then have "2*\<lfloor>it\<rfloor>*\<theta>+\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> 2*(1/2+(pi-2*\<theta>)/4*\<theta>)*\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> " 
    then have "2*\<lfloor>it\<rfloor>*\<theta>+\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> ((1+(pi-2*\<theta>)/2*\<theta>) - (2*(pi-2*\<theta>)/4*\<theta>+1)) *\<theta> " sorry
    then have "2*\<lfloor>it\<rfloor>*\<theta>+\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> ((1+(pi-2*\<theta>)/2*\<theta>) - (pi-2*\<theta>)/2*\<theta>-1) *\<theta> " sorry
    then have "2*\<lfloor>it\<rfloor>*\<theta>+\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> (((pi-2*\<theta>)/2*\<theta>) - (pi-2*\<theta>)/2*\<theta>) *\<theta> " sorry
    then have "2*\<lfloor>it\<rfloor>*\<theta>+\<theta> - (2*(pi-2*\<theta>)/4*\<theta>+1)*\<theta> \<le> 0*\<theta> " sorry






    then have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - pi/2 \<le> (1+(pi-2*\<theta>)/(2*\<theta>))*\<theta> - pi/2" sorry
    have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - pi/2 \<le> (\<theta>+(pi-2*\<theta>)/2) - pi/2" sorry
    have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - pi/2 \<le> \<theta>+pi/2-\<theta> - pi/2" sorry
    have "(2*\<lfloor>it\<rfloor>+1)*\<theta> - pi/2 \<le> 0" sorry

    have "-\<lfloor>it\<rfloor>+(pi-2*\<theta>)/(4*\<theta>) \<le> 1/2" sorry
    have "-\<lfloor>it\<rfloor> \<le> 1/2-(pi-2*\<theta>)/(4*\<theta>)" sorry
    have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + pi/2 = -2*\<lfloor>it\<rfloor>*\<theta>-\<theta>+pi/2" sorry
    have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + pi/2 \<le> 2*(1/2-(pi-2*\<theta>)/(4*\<theta>))*\<theta>-\<theta>+pi/2" sorry
    have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + pi/2 \<le> \<theta>-(pi-2*\<theta>)/2-\<theta>+pi/2" sorry
    have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + pi/2 \<le> \<theta>-pi/2+\<theta>-\<theta>+pi/2" sorry
    have "-(2*\<lfloor>it\<rfloor>+1)*\<theta> + pi/2 \<le> \<theta>" sorry


  have "abs ((pi/2*\<theta>+1)*\<theta> - pi/2) \<le> \<theta>" 
  proof-

    have "pi/2*\<theta>\<^sup>2+2*\<theta> \<ge> pi/2"















  have "(pi/2*\<theta>+1)*\<theta> - pi/2 \<le> \<theta>" sorry

  have "-(pi/2*\<theta>+1)*\<theta> + pi/2 \<le> \<theta>" sorry
  moreover have " - (pi / 2 * \<theta> + 1) * \<theta> + pi / 2 \<le> pi / 2" sorry
  moreover have "- (pi / 2) \<le> - (pi / 2 * \<theta> + 1) * \<theta> + pi / 2 " sorry (* siehe unten
  ultimately have "sin(-(pi/2*\<theta>+1)*\<theta> + pi/2) \<le> sin(\<theta>)"
     using sin_mono_le_eq[of "-(pi/2*\<theta>+1)*\<theta> + pi/2" "\<theta>" ] f2b f2 by auto
(*So SOLLTE es klappen *)


  have "(cos ((pi/2*\<theta>+1)*\<theta>))\<^sup>2 = 1/2*((cos(2*(pi/2*\<theta> + 1) * \<theta>))+1)" sorry
  have "(cos ((pi/2*\<theta>+1)*\<theta>))\<^sup>2 = 1/2*((cos(pi*\<theta>\<^sup>2 + 2*\<theta>))+1)" sorry

  have "pi*\<theta>\<^sup>2 + 2*\<theta>+pi/2 \<le> \<theta>" sorry
  have "sin(pi*\<theta>\<^sup>2 + 2*\<theta>+pi/2) \<le> sin(\<theta>)"
    using sin_mono_less_eq[of "pi*\<theta>\<^sup>2 + 2*\<theta>+pi/2" "\<theta>"]

 have "arcsin (sin (1::real)) = 1"
    by (metis (full_types) arcsin_0 arcsin_1 arcsin_lt_bounded arcsin_minus_1 arcsin_sin le_less_linear 
        less_minus_one_simps(1) less_numeral_extra(1) not_less_iff_gr_or_eq sin_pi_half sin_x_ge_neg_x sin_x_le_x)
  moreover have "1/sqrt(2)^n \<le> (sin 1)" using o1 by auto
  ultimately have f5: "\<theta> \<le> 1" using \<theta>_def arcsin_le_mono[of "1/sqrt(2)^n" "sin (1)"] by auto
  have "\<theta> \<ge> -1" sorry
 




  have "-pi/2 \<le> -((2*it+1)*\<theta>) + pi/2"
  proof-
    have "((2*it+1)*\<theta>) = (2*pi/4*\<theta>+1)*\<theta>" using it_def by auto
    moreover have "(2*pi/4*\<theta>+1) \<le> pi" 
    proof-
      have "2*pi/4*\<theta> \<le> pi/2" using f5 by auto
      moreover have "(pi/2+1) \<le> pi" using pi_ge_two by linarith
      ultimately show "(2*pi/4*\<theta>+1) \<le> pi" using f5 
        by (smt divide_le_eq_1_pos divide_nonneg_nonneg f3 mult_nonneg_nonneg nonzero_mult_div_cancel_left pi_ge_zero)
    qed
    ultimately have "((2*it+1)*\<theta>) \<le> pi" using f5  
      by (smt divide_le_eq_1_pos divide_nonneg_nonneg f3 mult_nonneg_nonneg nonzero_mult_div_cancel_left pi_ge_zero)
    then show ?thesis by auto
  qed
  moreover have "- ((2 * it + 1) * \<theta>) + pi / 2 \<le> \<theta>" 



  ultimately have "sin(-((2*it+1)*\<theta>)+pi/2) \<le> sin(\<theta>)" 
using sin_mono_le_eq[of "-((2*it+1)*\<theta>)+pi/2" "\<theta>"] f2 f2b by auto


  moreover have "cos((2*it+1)*\<theta>) = sin(-((2*it+1)*\<theta>)+pi/2)" 
    using cos_sin_eq[of "(2*it+1)*\<theta>"] by auto
  ultimately have t1: "cos((2*it+1)*\<theta>) \<le> sin \<theta>" by auto
  then have "(cmod (1/sqrt(2^n-1)*cos((2*it+1)*\<theta>)))\<^sup>2 = (sqrt ((Re (1/sqrt(2^n-1)*cos((2*it+1)*\<theta>)))\<^sup>2 + (Im (1/sqrt(2^n-1)*cos((2*it+1)*\<theta>)))\<^sup>2))\<^sup>2" 
    using cmod_def by auto
  moreover have "(Re (1/sqrt(2^n-1)*cos((2*it+1)*\<theta>)))\<^sup>2 \<le> 1/(2^n-1)*1/2^n" 
    using t1 sorry
  moreover have "(Im (1/sqrt(2^n-1)*cos((2*it+1)*\<theta>)))\<^sup>2 = 0" sorry
  ultimately have "(cmod (1/sqrt(2^n-1)*cos((2*it+1)*\<theta>)))\<^sup>2 \<le> (sqrt (1/(2^n-1)*1/2^n))\<^sup>2" 
    sorry
  then have "(cmod (1/sqrt(2^n-1)*cos((2*it+1)*\<theta>)))\<^sup>2 \<le> (1/(2^n-1)*1/2^n)" sorry 
  then have "(cmod (1/sqrt(2^n-1)*cos((2*it+1)*\<theta>)))\<^sup>2 \<le> (1/(2^n-1)*1/2^n)" sorry
  then show ?thesis sorry
qed



lemma (in grover)
  defines "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  shows "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*complex_of_real \<theta>)))\<^sup>2 \<le> 1/(2^n-1) * 1/2^n"
  sorry









(*O' is not a quantum gate.*)
(*Find better name*)
definition(in grover) q_oracel_fst::"complex Matrix.mat" ("O'") where
"q_oracel_fst = Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if (i=x \<and> i=j) then -1 else (if i=j then 1 else 0))"

lemma (in grover) q_oracel_fst_values:
  assumes "i<dim_row O' \<and> j<dim_col O'" and "i\<noteq>j" and "i\<noteq>x" 
  shows "(O' $$ (i,j)) = 0" 
  using assms q_oracel_fst_def by auto

lemma (in grover) app_oracle':
  fixes \<alpha> \<beta>::complex
  defines "v \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
  defines "w \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
  shows "O' * v = w"
proof
  fix i j
  assume a0: "i < dim_row w" and a1: "j < dim_col w" 
  then have f0: "i < dim_row O' \<and> j < dim_col v" and "dim_col O' = dim_row v"
    using q_oracel_fst_def w_def v_def by auto
  then have "(O' * v) $$ (i, j) = (\<Sum>k \<in> {0..<2^n}. (O' $$ (i,k)) * (v $$ (k,j)))" 
    using index_matrix_prod v_def by (simp add: atLeast0LessThan)
  then have "(O' * v) $$ (i, j) = (\<Sum>k \<in> ({0..<2^n}-{i}). (O' $$ (i,k)) * (v $$ (k,j))) + (O' $$ (i,i)) * (v $$ (i,j))" 
    by (metis (no_types, lifting) a0 add.commute atLeast0LessThan dim_row_mat(1) finite_atLeastLessThan insert_Diff insert_Diff_single lessThan_iff sum.insert_remove w_def)
  then have "(O' * v) $$ (i, j) = (\<Sum>k \<in> ({0..<2^n}-{i}). 0 * (v $$ (k,j))) + (O' $$ (i,i)) * (v $$ (i,j))" 
    using q_oracel_fst_def f0 v_def by auto
  then have f1: "(O' * v) $$ (i, j) =  (O' $$ (i,i)) * (v $$ (i,j))"  by auto
  show "(O' * v) $$ (i, j) = w $$ (i, j)"
  proof (rule disjE)
    show "i=x \<or> i\<noteq>x" by auto
  next
    assume a2: "i\<noteq>x"
    then have "(O' * v) $$ (i, j) = \<beta>" using f0 f1 q_oracel_fst_def v_def by auto
    then show "(O' * v) $$ (i, j) = w $$ (i, j)" 
      using w_def a2 f0 a1 dim_row_mat(1) index_mat(1) old.prod.case q_oracel_fst_def by auto
  next 
    assume a2: "i=x"
    then have "(O' * v) $$ (i, j) = (-1) * \<alpha>" using f0 f1 q_oracel_fst_def v_def by auto
    then show "(O' * v) $$ (i, j) = w $$ (i, j)" using w_def a2 f0 q_oracel_fst_def v_def by auto
  qed
next
  show "dim_row (O' * v) = dim_row w" 
    using v_def w_def q_oracel_fst_def by auto
next
  show "dim_col (O' * v) = dim_col w" 
    using v_def w_def q_oracel_fst_def by auto
qed

lemma(in grover) O_O'_relation: (*Rename*)
  fixes \<alpha> \<beta>
  defines "v \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
  shows "O * (v \<Otimes> (H * |one\<rangle>)) = (O' * v) \<Otimes> (H * |one\<rangle>)" 
proof-
  have "O * (v \<Otimes> (H * |one\<rangle>)) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>)) \<Otimes> (H * |one\<rangle>)"
    using app_oracle v_def by blast
  moreover have "(O' * v) \<Otimes> (H * |one\<rangle>) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>)) \<Otimes> (H * |one\<rangle>)" 
    using app_oracle' v_def by auto
  ultimately show "O * (v \<Otimes> (H * |one\<rangle>)) = (O' * v) \<Otimes> (H * |one\<rangle>)" by auto
qed

abbreviation(in grover) start_state:: "complex Matrix.mat" where
"start_state \<equiv> (\<psi>\<^sub>1 n)" (*(\<psi>\<^sub>1\<^sub>0 n)\<Otimes>(H * |one\<rangle>)"*)

primrec (in grover) grover_iter_fst::"nat\<Rightarrow>complex Matrix.mat" where
"grover_iter_fst 0 = (\<psi>\<^sub>1\<^sub>0 n)"|
"grover_iter_fst (Suc m) = D * (O' * (grover_iter_fst m))"

lemma (in grover) dim_grover_iter_fst:
  shows "dim_row (grover_iter_fst m) = 2^n \<and> dim_col (grover_iter_fst m) = 1"
proof(induction m)
  show "dim_row (grover_iter_fst 0) = 2^n \<and> dim_col (grover_iter_fst 0) = 1" by auto
next
  fix m
  assume IH: "dim_row (grover_iter_fst m) = 2^n \<and> dim_col (grover_iter_fst m) = 1"
  then show "dim_row (grover_iter_fst (Suc m)) = 2^n \<and> dim_col (grover_iter_fst (Suc m)) = 1" 
    by (simp add: IH diffusion_is_gate gate.dim_row)
qed

lemma (in grover) grover_iter_fst_res:
  shows "\<exists>\<alpha> \<beta>::complex. (grover_iter_fst m) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
proof(induction m)
  show "\<exists>\<alpha> \<beta>::complex. (grover_iter_fst 0) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
  proof(rule exI, rule exI)
    have "(grover_iter_fst 0) = Matrix.mat (2^n) 1 (\<lambda>(i,j). 1/(sqrt(2))^n)" by auto
    then have "(grover_iter_fst 0) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then  1/(sqrt(2))^n else 1/(sqrt(2))^n))" 
      by auto
    then show "(grover_iter_fst 0) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (1/(sqrt(2))^n) else (1/(sqrt(2))^n::complex)))"  
      by auto
  qed
next
  fix m 
  assume IH: "\<exists>\<alpha> \<beta>::complex. (grover_iter_fst m) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
  obtain \<alpha> \<beta> where  "(grover_iter_fst m) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
    using IH by auto
  then have "(grover_iter_fst (Suc m)) = D * (O' * (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>)))"
    by auto
  then have "(grover_iter_fst (Suc m)) = D * (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
    using app_oracle'[of "\<alpha>" "\<beta>"] by simp
  then have "(grover_iter_fst (Suc m)) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> 
                                                                          else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta>))"
    using app_diffusion_op by auto
  then show  "\<exists>\<alpha> \<beta>::complex. (grover_iter_fst (Suc m)) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
    by blast
qed


lemma (in grover) grover_iter_grover_iter_fst_relation:
  shows "grover_iter m = (grover_iter_fst m) \<Otimes> (H * |one\<rangle>)" 
proof(induction m)
  show  "grover_iter 0 = (grover_iter_fst 0) \<Otimes> (H * |one\<rangle>)" by auto
next
  fix m
  assume IH: "grover_iter m = (grover_iter_fst m) \<Otimes> (H * |one\<rangle>)" 
  have "grover_iter (Suc m) = (D \<Otimes> Id 1) * (O * (grover_iter m))" by auto
  then have "(D \<Otimes> Id 1) * (O * (grover_iter m)) = (D \<Otimes> Id 1) * (O * ((grover_iter_fst m) \<Otimes> (H * |one\<rangle>)))"
    using IH by auto
  moreover have "O * ((grover_iter_fst m) \<Otimes> (H * |one\<rangle>)) = (O' * (grover_iter_fst m)) \<Otimes> (H * |one\<rangle>)" 
    using O_O'_relation by (metis grover_iter_fst_res)
  then have "(D \<Otimes> Id 1) * (O * (grover_iter m)) = (D \<Otimes> Id 1) * ((O' * (grover_iter_fst m)) \<Otimes> (H * |one\<rangle>))"
     using  IH by auto
  then have "(D \<Otimes> Id 1) * (O * (grover_iter m)) = (D * (O' * (grover_iter_fst m))) \<Otimes> (Id 1 * (H * |one\<rangle>))"
    using mult_distr_tensor[of D "(O' * (grover_iter_fst m))" "Id 1" "(H * |one\<rangle>)"] ket_vec_def Id_def 
          diffusion_operator_def q_oracel_fst_def \<psi>\<^sub>1\<^sub>1_is_state state_def dim_grover_iter_fst by auto
  moreover have "(Id 1 * (H * |one\<rangle>)) = (H * |one\<rangle>)" 
    using H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1 Quantum.Id_def by auto
  ultimately have "(D \<Otimes> Id 1) * (O * (grover_iter m)) 
                 = (D * (O' * (grover_iter_fst m))) \<Otimes> (H * |one\<rangle>)" by auto
  then show "grover_iter (Suc m) = (grover_iter_fst (Suc m)) \<Otimes> (H * |one\<rangle>)" by auto
qed



lemma (in grover) aux_prob_not_successful:
  assumes "y < 2^n" and "x \<noteq> y"
  shows "(cmod ((grover_iter_fst iterations) $$ (y,0)))\<^sup>2 = 1/sqrt(n-1)*cos((2*m+1)*\<theta>)"
proof-
  define \<theta> where "\<theta> \<equiv> (arcsin((1/(sqrt(2)^n))))"
  then have "grover_iter_fst iterations = (Matrix.mat (2^n) 1 (\<lambda>(i,j). complex_of_real (if i=x then sin((2*iterations+1)*\<theta>) else 1/sqrt(2^n-1)*cos((2*iterations+1)*\<theta>)) ))"
    using t2 grover_iter_grover_iter_fst_relation sorry
  then have "(grover_iter_fst iterations) $$ (y,0)  = 1/sqrt(2^n-1)*cos((2*iterations+1)*\<theta>)" sorry
  moreover have "(cmod (1/sqrt(2^n-1)*cos((2*iterations+1)*\<theta>)))\<^sup>2 = 3" 
  proof




lemma (in grover) prob_not_successful:
  shows "(\<Sum>i \<in> {0..<2^n}-{x}. ((grover_iter iterations) $$ (i,0))\<^sup>2 ) = 1/2^n"












lemma (in grover) O'_res_is_state:
  fixes \<alpha> \<beta>
  defines "v \<equiv> (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
  assumes "state n v"
  shows "state n (O' * v)"
proof-
  have f0: "(O' * v) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))" 
    using app_oracle' v_def by blast
  then have "\<parallel>Matrix.col v 0\<parallel> = 1" using assms state.length by blast
  then have "1 = sqrt(\<Sum>i\<in>{0..<2^n}. (cmod ((Matrix.col v 0) $ i))\<^sup>2)"
    using cpx_vec_length_def atLeast0LessThan v_def by auto 
  then have "1 = sqrt((\<Sum>i\<in>{0..<2^n}-{x}. (cmod ((Matrix.col v 0) $ i))\<^sup>2) + (cmod ((Matrix.col v 0) $ x))\<^sup>2)" 
    using searched_dom by (simp add: sum_diff1)
  moreover have "(cmod ((Matrix.col v 0) $ x))\<^sup>2 = (cmod ((Matrix.col (O' * v) 0) $ x))\<^sup>2" using v_def searched_dom f0 by auto
  ultimately have "1 = sqrt((\<Sum>i\<in>{0..<2^n}-{x}. (cmod ((Matrix.col v 0) $ i))\<^sup>2) + (cmod ((Matrix.col (O' * v) 0) $ x))\<^sup>2)" 
    by simp
  moreover have "i<2^n\<and>i\<noteq>x \<longrightarrow> (cmod ((Matrix.col v 0) $ i))\<^sup>2 = (cmod ((Matrix.col (O' * v) 0) $ i))\<^sup>2" for i::nat  
    using v_def searched_dom f0 by auto 
  ultimately have "1 = sqrt((\<Sum>i\<in>{0..<2^n}-{x}. (cmod ((Matrix.col (O' * v) 0) $ i))\<^sup>2) + (cmod ((Matrix.col (O' * v) 0) $ x))\<^sup>2)" 
    by auto
  then have "1 = sqrt((\<Sum>i\<in>{0..<2^n}. (cmod ((Matrix.col (O' * v) 0) $ i))\<^sup>2))" 
    using searched_dom by (simp add: sum_diff1)
  then have "1 = \<parallel>Matrix.col (O' * v) 0\<parallel>"
    using assms state.length f0 atLeast0LessThan cpx_vec_length_def by auto
  moreover have "dim_col (O' * v) = 1" by (simp add: f0)
  moreover have "dim_row (O' * v) = 2^n" by (simp add: f0)
  ultimately show "state n (O' * v)" using state_def by auto
qed

lemma (in grover) is_state_grover_iter_fst:
  shows "state n (grover_iter_fst m)"
proof(induction m)
  show "state n (grover_iter_fst 0)" 
    using \<psi>\<^sub>1\<^sub>0_is_state dim by auto
next
  fix m 
  assume IH: "state n (grover_iter_fst m)"
  have "(grover_iter_fst (Suc m)) = D * (O' * (grover_iter_fst m))" by auto
  moreover have "state n (O' * (grover_iter_fst m))" using O'_res_is_state grover_iter_fst_res by (metis IH)
  ultimately show "state n (grover_iter_fst (Suc m))" 
    using diffusion_is_gate by auto
qed

lemma \<psi>\<^sub>1_different_rep:
  shows "(Matrix.mat (2^n) 1 (\<lambda>(i,j). 1/(sqrt(2))^n)) = 
                 (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then 1/(sqrt(2))^n else 1/(sqrt(2))^n))" by auto

lemma (in grover) grover_iter_fst_res_ex: (*Other lemma about result might be easier to proof with this, rename*)
  assumes "k<2^n" and "x\<noteq>k"
  shows "grover_iter_fst (Suc m)
      = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*((grover_iter_fst m) $$ (x,0)) 
                                               + (2^n-1)/(2^(n-1))*((grover_iter_fst m) $$ (k,0))
                                             else 1/2^(n-1)*-((grover_iter_fst m) $$ (x,0))                  
                                               + (-1+2^(n-1))/2^(n-1)*((grover_iter_fst m) $$ (k,0)) ))" 
proof(induction m)
  have "grover_iter_fst (Suc 0) = D * (O' *(Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (1/(sqrt(2))^n) else complex_of_real (1/(sqrt(2))^n) )))" 
    apply (auto simp: \<psi>\<^sub>1_different_rep)
    by (smt cong_mat of_real_divide prod.simps(2))
  then have "grover_iter_fst (Suc 0) = D * (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -complex_of_real(1/(sqrt(2))^n) else (1/sqrt(2)^n) ))"
    using app_oracle'[of "complex_of_real (1/sqrt(2)^n)" "(1/sqrt(2)^n)"]
    by auto
  then have "grover_iter_fst (Suc 0) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*(complex_of_real(1/(sqrt(2))^n)) 
                                                                            + (2^n-1)/(2^(n-1))*(1/sqrt(2)^n)
                                                                   else 1/2^(n-1)*-(complex_of_real(1/(sqrt(2))^n))
                                                                            + (-1+2^(n-1))/2^(n-1)*(1/sqrt(2)^n) ))"
    using app_diffusion_op by auto
  moreover have "((grover_iter_fst 0) $$ (x,0)) = (1/(sqrt(2))^n)" 
    using searched_dom by auto
  moreover have "((grover_iter_fst 0) $$ (k,0)) = (1/(sqrt(2))^n)" 
    by (simp add: assms(1))
  ultimately show  "grover_iter_fst (Suc 0)
      = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*((grover_iter_fst 0) $$ (x,0)) 
                                               + (2^n-1)/(2^(n-1))*((grover_iter_fst 0) $$ (k,0))
                                             else 1/2^(n-1)*-((grover_iter_fst 0) $$ (x,0))                  
                                               + (-1+2^(n-1))/2^(n-1)*((grover_iter_fst 0) $$ (k,0)) ))" 
    by auto
next
  fix m
  define \<alpha>m where "\<alpha>m = ((grover_iter_fst m)$$(x,0))"
  define \<beta>m where "\<beta>m = ((grover_iter_fst m)$$(k,0))"
  define \<alpha>m1 where "\<alpha>m1 = ((grover_iter_fst (Suc m))$$(x,0))"
  define \<beta>m1 where "\<beta>m1 = ((grover_iter_fst (Suc m))$$(k,0))"
  assume IH: "grover_iter_fst (Suc m)
      = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*((grover_iter_fst m) $$ (x,0)) 
                                               + (2^n-1)/(2^(n-1))*((grover_iter_fst m) $$ (k,0))
                                             else 1/2^(n-1)*-((grover_iter_fst m) $$ (x,0)) 
                                               + (-1+2^(n-1))/2^(n-1)*((grover_iter_fst m) $$ (k,0)) ))" 
  have f0: "\<alpha>m1 = ((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m" 
    using IH searched_dom \<alpha>m1_def \<alpha>m_def \<beta>m_def by auto
  have f1: "\<beta>m1 = 1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m" 
    using IH assms \<beta>m1_def \<alpha>m_def \<beta>m_def by auto

  have "grover_iter_fst (Suc (Suc m)) = D * (O' * (grover_iter_fst (Suc m)))" by auto
  then have "grover_iter_fst (Suc (Suc m))
             = D * (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -(((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)
                                                   else 1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m))"
    using app_oracle' IH \<alpha>m_def \<beta>m_def by auto
  then have "grover_iter_fst (Suc (Suc m))
          = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*((((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)) 
                                                     + (2^n-1)/(2^(n-1))*(1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m)
                                             else 1/2^(n-1)*-((((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)) 
                                                     + (-1+2^(n-1))/2^(n-1)*(1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m) ))"
      using app_diffusion_op by auto
  moreover have "((2^(n-1)-1)/2^(n-1))*((((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)) 
               + (2^n-1)/(2^(n-1))*(1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m)
               = ((2^(n-1)-1)/2^(n-1))*\<alpha>m1 + (2^n-1)/(2^(n-1))*\<beta>m1" 
    using f0 f1 by auto
  moreover have "1/2^(n-1)*-((((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)) 
               + (-1+2^(n-1))/2^(n-1)*(1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m)
               = 1/2^(n-1)*-\<alpha>m1 + (-1+2^(n-1))/2^(n-1)*\<beta>m1"  
    using f0 f1 by auto
  ultimately have "grover_iter_fst (Suc (Suc m))
              = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then  ((2^(n-1)-1)/2^(n-1))*\<alpha>m1 + (2^n-1)/(2^(n-1))*\<beta>m1
                                             else 1/2^(n-1)*-\<alpha>m1 + (-1+2^(n-1))/2^(n-1)*\<beta>m1 ))" 
    by auto
  then show "grover_iter_fst (Suc (Suc m))
      = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*((grover_iter_fst (Suc m)) $$ (x,0)) 
                                               + (2^n-1)/(2^(n-1))*((grover_iter_fst (Suc m)) $$ (k,0))
                                             else 1/2^(n-1)*-((grover_iter_fst (Suc m)) $$ (x,0)) 
                                               + (-1+2^(n-1))/2^(n-1)*((grover_iter_fst (Suc m)) $$ (k,0)) ))" 
     using \<alpha>m1_def \<beta>m1_def by auto
qed

lemma (in grover) grover_iter_fst_rec:
  assumes "k<2^n" and "x\<noteq>k"
  shows "grover_iter_fst m
      = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (grover_iter_fst m) $$ (x,0)
                                             else (grover_iter_fst m) $$ (k,0) ))" 
proof
  fix i j::nat
  assume "i < dim_row (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (grover_iter_fst m) $$ (x,0)
                                             else (grover_iter_fst m) $$ (k,0) ))" 
    and "j < dim_col (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (grover_iter_fst m) $$ (x,0)
                                             else (grover_iter_fst m) $$ (k,0) ))"  
  then have f0: "i < 2^n \<and> j = 0" by auto
  moreover have "i=x \<longrightarrow>  (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (grover_iter_fst m) $$ (x,0)
                                                 else (grover_iter_fst m) $$ (k,0) )) $$ (i,j)
                = (grover_iter_fst m) $$ (i,j)" using f0 by auto
  moreover have "i\<noteq>x \<longrightarrow>  (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (grover_iter_fst m) $$ (x,0)
                                                 else (grover_iter_fst m) $$ (k,0) )) $$ (i,j)
                = (grover_iter_fst m) $$ (i,j)" using f0 
    by (smt assms(1) assms(2) case_prod_conv grover_iter_fst_res index_mat(1) less_numeral_extra(1))
  ultimately show "grover_iter_fst m$$ (i,j) 
                = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (grover_iter_fst m) $$ (x,0)
                                                  else (grover_iter_fst m) $$ (k,0) )) $$ (i,j)" by auto
next
  show "dim_row (grover_iter_fst m)
      = dim_row (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (grover_iter_fst m) $$ (x,0)
                                             else (grover_iter_fst m) $$ (k,0) ))" 
    by (simp add: dim_grover_iter_fst)
next
  show "dim_col (grover_iter_fst m)
      = dim_col (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then (grover_iter_fst m) $$ (x,0)
                                             else (grover_iter_fst m) $$ (k,0) ))" 
    by (simp add: dim_grover_iter_fst)
qed


lemma (in grover) grover_iter_res_real:
  shows "\<forall>k. k<2^n \<longrightarrow> Im ((grover_iter_fst m) $$ (k,0)) = 0"
proof(induction m)
  have "\<forall>k. k<2^n \<longrightarrow> Im ((grover_iter_fst 0) $$ (k,0)) = Im ((Matrix.mat (2^n) 1 (\<lambda>(i,j).  1/(sqrt(2))^n))$$ (k,0))"
    using searched_dom by auto
  then show "\<forall>k. k<2^n \<longrightarrow>Im ((grover_iter_fst 0) $$ (k,0)) = 0" by auto
next
  fix m 
  assume IH: "\<forall>k. k<2^n \<longrightarrow>Im ((grover_iter_fst m) $$ (k,0)) = 0"
  show "\<forall>k. k<2^n \<longrightarrow> Im ((grover_iter_fst (Suc m)) $$ (k,0)) = 0"
  proof(rule allI, rule impI)
    fix k::nat
    assume a0: "k<2^n"
    show "Im ((grover_iter_fst (Suc m)) $$ (k,0)) = 0"
    proof(rule disjE)
      show "k=x \<or> k\<noteq>x" by auto
    next
      assume a1: "k\<noteq>x"
      then have "(grover_iter_fst (Suc m)) $$ (k,0) = 1/2^(n-1)*-((grover_iter_fst m) $$ (x,0)) 
                                               + (-1+2^(n-1))/2^(n-1)*((grover_iter_fst m) $$ (k,0))"  
        using grover_iter_fst_res_ex a0 by auto
      moreover have "Im((grover_iter_fst m) $$ (k,0)) = 0"  using IH a0 by blast
      moreover have "Im (1/2^(n-1)*-((grover_iter_fst m) $$ (x,0))) = 0" using searched_dom IH by simp
      ultimately show "Im ((grover_iter_fst (Suc m)) $$ (k,0)) = 0" by simp
    next
      assume a1: "k=x"
      then have "i\<noteq>x \<and> i<2^n \<longrightarrow> (grover_iter_fst (Suc m)) $$ (k,0) = ((2^(n-1)-1)/2^(n-1))*((grover_iter_fst m) $$ (x,0)) 
                                               + (2^n-1)/(2^(n-1))*((grover_iter_fst m) $$ (i,0))" for i::nat
        using grover_iter_fst_res_ex a0 by auto
      moreover have "Im (((2^(n-1)-1)/2^(n-1))*(grover_iter_fst m) $$ (x,0)) = 0" using IH searched_dom by simp
      moreover have "i\<noteq>x \<and> i<2^n \<longrightarrow> Im ((2^n-1)/(2^(n-1))*((grover_iter_fst m) $$ (i,0))) = 0" for i::nat 
        using IH by auto
      moreover have "\<exists>i. i\<noteq>x \<and> i<2^n"
        by (metis (full_types) dim less_le_trans less_numeral_extra(1) nat_less_le numeral_le_one_iff one_le_numeral 
            self_le_power semiring_norm(69))
      ultimately show "Im ((grover_iter_fst (Suc m)) $$ (k,0)) = 0" by auto
    qed
  qed
qed

lemma (in grover) grover_iter_res_re:
  shows "\<forall>k. k<2^n \<longrightarrow> Re ((grover_iter_fst m) $$ (k,0)) = (grover_iter_fst m) $$ (k,0)"
  using grover_iter_res_real by (simp add: complex_eqI)


lemma (in grover) grover_iter_res_pos:
  assumes "n\<ge>2"
  shows "\<forall>k. k<2^n \<longrightarrow> (grover_iter_fst m) $$ (k,0) \<ge> 0 \<and> (grover_iter_fst m) $$ (x,0) \<le> 1/2"
proof(induction m)
  fix m 
  assume IH: "\<forall>k. k<2^n \<longrightarrow> (grover_iter_fst m) $$ (k,0) \<ge> 0  \<and> (grover_iter_fst m) $$ (x,0) \<le> 1/2"
  show "\<forall>k. k<2^n \<longrightarrow> (grover_iter_fst (Suc m)) $$ (k,0) \<ge> 0  \<and> (grover_iter_fst (Suc m)) $$ (x,0) \<le> 1/2"
  proof(rule allI, rule impI)
    fix k::nat
    assume a0: "k<2^n"
    show "(grover_iter_fst (Suc m)) $$ (k,0)\<ge>0 \<and> (grover_iter_fst (Suc m)) $$ (x,0)\<le>1/2"
    proof
      show "(grover_iter_fst (Suc m)) $$ (k,0)\<ge>0"
        proof(rule disjE)
          show "k=x \<or> k\<noteq>x" by auto
        next
          assume a1: "k\<noteq>x"
          define \<alpha> where "\<alpha> = ((grover_iter_fst m) $$ (x,0))"
          define \<beta> where "\<beta> = ((grover_iter_fst m) $$ (k,0))"
          have "state n (grover_iter_fst m)" using is_state_grover_iter_fst[of "m"] by auto
          moreover have "grover_iter_fst m = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((grover_iter_fst m) $$ (x,0))
                                        else ((grover_iter_fst m) $$ (k,0)) ))" 
            using a1 a0 grover_iter_fst_rec by auto
          ultimately have  "state n (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))" using \<alpha>_def \<beta>_def by auto
        
          moreover have "(grover_iter_fst (Suc m)) $$ (k,0) = 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta>" 
            using grover_iter_fst_res_ex \<alpha>_def \<beta>_def a0 a1 by auto
          moreover have "\<alpha>\<ge>0" and "\<beta> \<ge> 0"  and "\<alpha> \<le> 1/2" using \<alpha>_def \<beta>_def IH searched_dom a0 by auto
          ultimately show "(grover_iter_fst (Suc m)) $$ (k,0) \<ge> 0" using u4 assms by auto
        next
          assume a1: "k=x"
          have f0: "i \<noteq> x \<and> i < 2^n \<longrightarrow> (grover_iter_fst (Suc m)) $$ (k,0) = ((2^(n-1)-1)/2^(n-1))*((grover_iter_fst m) $$ (x,0)) 
                                               + (2^n-1)/(2^(n-1))*((grover_iter_fst m) $$ (i,0))" for i::nat
            using grover_iter_fst_res_ex a0 a1 by auto
          have "((2^(n-1)-1)/2^(n-1)) \<ge> 0" sorry
          then have f1: "((2^(n-1)-1)/2^(n-1))*((grover_iter_fst m) $$ (x,0)) \<ge> 0" 
            using IH searched_dom by (smt a0 a1 le_cpx_mult_right mult_eq_0_iff)
          have "(2^n-1)/(2^(n-1)) \<ge> 0" sorry
          then have f2: "i \<noteq> x \<and> i < 2^n \<longrightarrow> ((grover_iter_fst m) $$ (i,0)) \<ge> 0" for i::nat  using IH by blast
          have "\<exists> i. i \<noteq> x \<and> i < 2^n " sorry
          then show "(grover_iter_fst (Suc m)) $$ (k,0) \<ge> 0" using f0 f1 f2 sorry
        qed
      next
         have f0: "i \<noteq> x \<and> i < 2^n \<longrightarrow> (grover_iter_fst (Suc m)) $$ (x,0) = ((2^(n-1)-1)/2^(n-1))*((grover_iter_fst m) $$ (x,0)) 
                                               + (2^n-1)/(2^(n-1))*((grover_iter_fst m) $$ (i,0))" for i::nat
            using grover_iter_fst_res_ex a0 searched_dom by auto
      qed


lemma (in grover) grover_iter_prob_inc:
  shows "(grover_iter_fst (Suc m)) $$ (x,0) \<le> (grover_iter_fst m) $$ (x,0) + 2/sqrt(2)^n" 
proof- 
  have "k<2^n \<and> x\<noteq>k \<longrightarrow> (grover_iter_fst (Suc m)) $$ (x,0) = ((2^(n-1)-1)/2^(n-1))*((grover_iter_fst m) $$ (x,0)) 
                                               + (2^n-1)/(2^(n-1))*((grover_iter_fst m) $$ (k,0))" sorry
  have "(grover_iter_fst (Suc m)) $$ (x,0) \<le> ((grover_iter_fst m) $$ (x,0)) + 2/sqrt(2^n)" sorry
  show  "(grover_iter_fst (Suc m)) $$ (x,0) \<le> (grover_iter_fst m) $$ (x,0) + 2/sqrt(2)^n"  sorry
qed



lemma (in grover) grover_iter_lower_bound:
  shows "(grover_iter_fst m) $$ (x,0) \<le> 1/2" sorry


lemma (in grover)
  shows "(grover_iter_fst iterations) $$ (x,0) > 0.1" sorry







definition(in grover) probx_it::"nat \<Rightarrow>  real" where
"probx_it m = (cmod ((grover_iter (Suc m))$$(2*x,0)))\<^sup>2 + (cmod ((grover_iter (Suc m))$$(2*x+1,0)))\<^sup>2"

lemma (in grover)
  shows "probx_it m = (cmod ((grover_iter_fst m) $$(x,0)))\<^sup>2"
  sorry

























































lemma (in grover) is_state_grover_iter_fst:
 shows "state n (grover_iter' m)" sorry







lemma (in grover)
  shows "\<exists> \<alpha> \<beta>. (grover_iter m start_state) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>)) \<Otimes> (H * |one\<rangle>)"
proof(induction m)
  show "\<exists> \<alpha> \<beta>. (grover_iter 0 start_state) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>)) \<Otimes> (H * |one\<rangle>)"
  proof (rule exI,rule exI)
    have "(grover_iter 0 start_state) = (\<psi>\<^sub>1\<^sub>0 n)\<Otimes>(H * |one\<rangle>)" sorry
    then have f0: "(grover_iter 0 start_state) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then 1/sqrt(2) else 1/sqrt(2))) \<Otimes>(H * |one\<rangle>)"
      sorry
    then show "(grover_iter 0 start_state) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>)) \<Otimes> (H * |one\<rangle>)"
      sorry
  qed
next
  fix m
  assume "\<exists> \<alpha> \<beta>. (grover_iter m start_state) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>)) \<Otimes> (H * |one\<rangle>)"
  show "\<exists> \<alpha> \<beta>. (grover_iter (Suc m) start_state) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>)) \<Otimes> (H * |one\<rangle>)"
    sorry
qed

lemma (in grover)
  shows "i<2^n \<longrightarrow> Im ((grover_iter m)$$(i,0)) = 0" sorry

(*The proof does not work this way? *)
lemma (in grover)
  assumes "k\<le>2^n" and "k\<noteq>x"
  shows "(grover_iter (Suc m))
       = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*(sqrt(2)*(grover_iter m)$$(x * 2,0)) 
                                                 + (2^n-1)/(2^(n-1))*(sqrt(2)*(grover_iter m)$$(k * 2,0))
                                              else 1/2^(n-1)*-(sqrt(2)*(grover_iter m)$$(x * 2,0))
                                                 + (-1+2^(n-1))/2^(n-1)*(sqrt(2)*(grover_iter m)$$(k * 2,0))
                               )) \<Otimes> (H * |one\<rangle>)" 
proof (induction m)
  fix m::nat
  assume IH:  "(grover_iter (Suc m))
             = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*(sqrt(2)*(grover_iter m)$$(x * 2,0)) 
                                                 + (2^n-1)/(2^(n-1))*(sqrt(2)*(grover_iter m)$$(k * 2,0))
                                              else 1/2^(n-1)*-(sqrt(2)*(grover_iter m)$$(x * 2,0))
                                                 + (-1+2^(n-1))/2^(n-1)*(sqrt(2)*(grover_iter m)$$(k * 2,0))
                )) \<Otimes> (H * |one\<rangle>)" 
  define \<alpha>m where "\<alpha>m = sqrt(2)*((grover_iter m)$$(x * 2,0))"
  define \<beta>m where "\<beta>m = sqrt(2)*((grover_iter m)$$(k * 2,0))"
  define \<alpha>m1 where "\<alpha>m1 = sqrt(2)*((grover_iter (Suc m))$$(x * 2,0))"
  define \<beta>m1 where "\<beta>m1 = sqrt(2)*((grover_iter (Suc m))$$(k * 2,0))"

   have "(grover_iter (Suc (Suc m))) = (D\<Otimes>Id 1) * (O * (grover_iter (Suc m)))" by auto
  have  "(grover_iter (Suc m))
             = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m
                                              else 1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m
                )) \<Otimes> (H * |one\<rangle>)" 
    using IH \<alpha>m_def \<beta>m_def by auto
  then have " (D\<Otimes>Id 1) * (O * (grover_iter (Suc m)))
            = (D\<Otimes>Id 1) * ((Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -(((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)
                                              else 1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m
                )) \<Otimes> (H * |one\<rangle>))"
    using app_oracle[of "(((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)" "1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m"] 
    by auto
  moreover have "state n (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -(((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)
                                              else 1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m))" sorry
  ultimately have "(D\<Otimes>Id 1) * (O * (grover_iter (Suc m)))
            = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*((((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)) 
                                                     + (2^n-1)/(2^(n-1))*(1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m)
                                             else 1/2^(n-1)*-((((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)) 
                                                     + (-1+2^(n-1))/2^(n-1)*(1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m) 
                                      )) \<Otimes> (H * |one\<rangle>)" 
    using app_diffusion_op_res by simp

  have "\<alpha>m1 = (((2^(n-1)-1)/2^(n-1))*\<alpha>m + (2^n-1)/(2^(n-1))*\<beta>m)" sorry
  have "\<beta>m1 = (1/2^(n-1)*-\<alpha>m + (-1+2^(n-1))/2^(n-1)*\<beta>m)" sorry



  show  "(grover_iter (Suc (Suc m)))
             = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*((grover_iter (Suc m))$$(x * 2,0)) 
                                                 + (2^n-1)/(2^(n-1))*((grover_iter (Suc m))$$(k * 2,0))
                                              else 1/2^(n-1)*-((grover_iter (Suc m))$$(x * 2,0))
                                                 + (-1+2^(n-1))/2^(n-1)*((grover_iter (Suc m))$$(k * 2,0))
                )) \<Otimes> (H * |one\<rangle>)" 




(*proof (induction m)
  fix m::nat  
  assume IH: "(grover_iter (Suc m) start_state)
       = ((Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> )) \<Otimes> (H * |one\<rangle>))"
  then have "(grover_iter m start_state)$$(x * 2,0) = 1/sqrt(2)*((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>" sorry
  then have "(grover_iter m start_state)$$(i * 2,0) = 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta>" sorry

  then have "(grover_iter (Suc (Suc m)) start_state) 
           = (D\<Otimes>Id 1) * (q_oracle * (grover_iter (Suc m) start_state))"
    by auto
  then have "((D \<Otimes> Id 1) * q_oracle * (grover_iter (Suc m) start_state))
           = ((D \<Otimes> Id 1) * q_oracle * ((Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> )) \<Otimes> (H * |one\<rangle>)))" 
    using IH by auto
  then have " (q_oracle * ((Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-(1::real))/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> )) \<Otimes> (H * |one\<rangle>)))
            = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -(((2^(n-1)-(1::real))/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>)
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> )) \<Otimes> (H * |one\<rangle>)" 
    using app_oracle by blast (*Problem with complex, change everything to complex above hard and causes problems at other points*)
  have "state (n+1) (grover_iter (Suc m) start_state)"
    using is_state_grover_iter[of "Suc m"] assms IH by auto
  then have "state (n+1) ((Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> )) \<Otimes> (H * |one\<rangle>))"
    using IH by auto
  then have "state n (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -(((2^(n-1)-(1::real))/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>)
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> ))" 
    using app_oracle_res_is_state[of "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>" "1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta>"] 
    by auto
  then have "(D \<Otimes> Id 1) * ((Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -(((2^(n-1)-(1::real))/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>)
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> )) \<Otimes> (H * |one\<rangle>))
            = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*(((2^(n-1)-(1::real))/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>) 
                                                     + (2^n-1)/(2^(n-1))*(1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta>)
                                             else 1/2^(n-1)*-(((2^(n-1)-(1::real))/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>) 
                                                     + (-1+2^(n-1))/2^(n-1)*(1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta>) ))
             \<Otimes> (H * |one\<rangle>)"
    using app_diffusion_op_res by auto
  then have "((2^(n-1)-1)/2^(n-1))*(((2^(n-1)-(1::real))/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>)                    
            =((2^(n-1)-1)/2^(n-1))*((2^(n-1)-(1::real))/2^(n-1))*\<alpha> + ((2^(n-1)-1)/2^(n-1))* (2^n-1)/(2^(n-1))*\<beta>"
    sorry
  then have "... = ((2^(n-1)-1)/2^(n-1))\<^sup>2*\<alpha> + (2^(n-1)-1)* (2^n-1)/(2^(n-1))\<^sup>2*\<beta>"
    sorry
  have "(2^n-1)/(2^(n-1))*(1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta>) = 
        (2^n-1)/(2^(n-1))*1/2^(n-1)*-\<alpha> + (2^n-1)/(2^(n-1))*(-1+2^(n-1))/2^(n-1)*\<beta>" sorry
  have "(2^n-1)/2^(n-1)*1/2^(n-1)*-\<alpha> + (2^n-1)/2^(n-1)*(-1+2^(n-1))/2^(n-1)*\<beta>
       =1/(2^(n-1))*-\<alpha> + (2^n-1)*(-1+2^(n-1))/(2^(n-1))\<^sup>2*\<beta>" sorry
  have "1/(2^(n-1))*-\<alpha> + ((2^(n-1)-1)/2^(n-1))\<^sup>2*\<alpha>
       =(-1/(2^(n-1)) + ((2^(n-1)-1)/2^(n-1))\<^sup>2)*\<alpha>" sorry
  have "(-1/(2^(n-1)) + ((2^(n-1)-1)/2^(n-1))\<^sup>2)*\<alpha>
       = (-(2^(n-1)+(2^(n-1)-1)\<^sup>2) /(2^(n-1))\<^sup>2)*\<alpha>" sorry
  have "((2^(n-1)-1)\<^sup>2 - 2^(n-1)) /((2^(n-1))\<^sup>2)*\<alpha>
       =((2^(n-1))\<^sup>2-2 *2^(n-1) + 1 - 2^(n-1))/((2^(n-1))\<^sup>2)*\<alpha>" sorry
  have "((2^(n-1))\<^sup>2-2 *2^(n-1) + 1 - 2^(n-1))/((2^(n-1))\<^sup>2)*\<alpha>
       =99 " sorry
*)

lemma (in grover)
  assumes "i\<le>2^n" and "i\<noteq>x"
  and "\<alpha> = (grover_iter m start_state)$$(x * 2,0) "
  and "\<beta> = (grover_iter m start_state)$$(i * 2,0) "
  shows "(grover_iter (Suc m) start_state)
       = ((Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> )) \<Otimes> (H * |one\<rangle>))"
  sorry

definition(in grover) probx_it::"nat \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where
"probx_it m v = (cmod ((grover_iter (Suc m) start_state)$$(2*x,0)))\<^sup>2 + (cmod ((grover_iter (Suc m) start_state)$$(2*x+1,0)))\<^sup>2"

lemma (in grover)
  shows "probx_it (Suc m) v \<ge> probx_it m v + 1/(sqrt(2)^n)" 
proof-
  have "probx_it (Suc m) v = (cmod ((grover_iter (Suc m) start_state)$$(2*x,0)))\<^sup>2 + (cmod ((grover_iter (Suc m) start_state)$$(2*x+1,0)))\<^sup>2"
    sorry
  have "(cmod ((grover_iter (Suc m) start_state)$$(2*x,0)))\<^sup>2 = 
(cmod  ((2^(n-1)-1)/2^(n-1))*((grover_iter m start_state)$$(x * 2,0)) 
                                                 + (2^n-1)/(2^(n-1))*((grover_iter m start_state)$$(i * 2,0)))\<^sup>2"
    sorry
qed


lemma (in grover)
  shows "probx_it (Suc m) v \<le> probx_it m v + 2/(sqrt(2)^n)" sorry

lemma (in grover)
  shows "probx_it iterations v \<ge> 2/3" sorry





lemma (in grover)
  shows "grover_iter n (D * (q_oracle v))$$(x * 2,0) \<le> 1/2" sorry



lemma (in grover)
  shows "(grover_iter iterations start_state) = end" (*Find out what end is*)
  sorry


(*
This is how it looked in the old version: 
(grover_iter iterations (((H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>))*(H * |one\<rangle>)))
I think its better but then everything
*)
definition(in grover) grover_algo::"complex Matrix.mat" where
"grover_algo = grover_iter iterations" 


lemma (in grover)
  shows "(cmod(grover_algo $$ (x,0)))\<^sup>2 \<ge> XXX" (*Put in right prob here*)
  sorry














(*Does not hold as it is now?*)
lemma (in grover)
  fixes v'::"complex Matrix.mat"
  defines "v \<equiv> sqrt(2) \<cdot>\<^sub>m v'"
  shows "state (n+1) (v \<Otimes> (H * |one\<rangle>)) = state n v'"
proof
  assume a0: "state (n+1) (v \<Otimes> (H * |one\<rangle>))"
  then have f0: "Matrix.dim_col v = 1"  using state_def by auto
  have IH2: "Matrix.dim_row (v \<Otimes> (H * |one\<rangle>)) = 2^(n+1)" using a0 state.dim_row by blast
  then have f1: "Matrix.dim_row v = 2^n"  using \<psi>\<^sub>1\<^sub>1_is_state state.dim_row by fastforce
  have IH3: "\<parallel>Matrix.col (v \<Otimes> (H * |one\<rangle>)) 0\<parallel> = 1" using a0 state.length by auto
  then have "1 = sqrt(\<Sum>i<dim_vec (Matrix.col (v \<Otimes> (H * |one\<rangle>)) 0). (cmod ((Matrix.col (v \<Otimes> (H * |one\<rangle>)) 0) $ i))\<^sup>2)" 
    by (simp add: cpx_vec_length_def)
  moreover have "sqrt(\<Sum>i<dim_vec (Matrix.col (v \<Otimes> (H * |one\<rangle>)) 0). (cmod ((Matrix.col (v \<Otimes> (H * |one\<rangle>)) 0) $ i))\<^sup>2 )
               = sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod ((Matrix.col (v \<Otimes> (H * |one\<rangle>)) 0) $ i))\<^sup>2)" 
    using IH2 atLeast0LessThan by auto
  moreover have "sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod ((Matrix.col (v \<Otimes> (H * |one\<rangle>)) 0) $ i))\<^sup>2)
               = sqrt(\<Sum>i\<in>({0..<2^(n+1)}). (cmod ((v \<Otimes> (H * |one\<rangle>)) $$ (i,0)))\<^sup>2)"  
    using IH2 a0 state.dim_col by fastforce
  moreover have "sqrt(\<Sum>i\<in>({0..<2^(n+1)}). (cmod ((v \<Otimes> (H * |one\<rangle>)) $$ (i,0)))\<^sup>2) 
                = sqrt(\<Sum>i\<in>({0..<2^(n+1)}). (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2)"  
    sorry
  have "{0..<2^(n+1)} = {k. k\<in>{0..<2^(n+1)} \<and> even k} \<union> {k. k\<in>{0..<2^(n+1)} \<and> odd k}" sorry
  moreover have "{k. k\<in>{0..<2^(n+1)} \<and> even k} \<union> {k. k\<in>{0..<2^(n+1)} \<and> odd k} = {}" sorry
  moreover have "{} = {bot::nat..<2 ^ (1 + n)}" sorry
  ultimately have "sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2)
                  = sqrt((\<Sum>i\<in>{k. k\<in>{0..<2^(n+1)} \<and> even k}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2) +
                    (\<Sum>i\<in>{k. k\<in>{0..<2^(n+1)} \<and> odd k}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2))"   
    by (simp add: bot_nat_def)
  then have "sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2)
           = sqrt((\<Sum>i\<in>{k. k\<in>{0..<2^(n+1)} \<and> even k}. (cmod (v $$ (i div 2,0) * 1/sqrt(2) ))\<^sup>2) +
             (\<Sum>i\<in>{k. k\<in>{0..<2^(n+1)} \<and> odd k}. (cmod (v $$ (i div 2,0) * -1/sqrt(2)))\<^sup>2))" sorry
  then have "sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2)
           = sqrt(1/2*(\<Sum>i\<in>{k. k\<in>{0..<2^(n+1)} \<and> even k}. (cmod (v $$ (i div 2,0)))\<^sup>2) +
             1/2*(\<Sum>i\<in>{k. k\<in>{0..<2^(n+1)} \<and> odd k}. (cmod (v $$ (i div 2,0)))\<^sup>2))" sorry
  then have "sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2)
           = 1/sqrt(2) * sqrt((\<Sum>i\<in>{k. k\<in>{0..<2^(n+1)} \<and> even k}. (cmod (v $$ (i div 2,0)))\<^sup>2) +
             (\<Sum>i\<in>{k. k\<in>{0..<2^(n+1)} \<and> odd k}. (cmod (v $$ (i div 2,0)))\<^sup>2))"sorry
  then have "sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2)
           = 1/sqrt(2) * sqrt((\<Sum>i\<in>{0..<2^(n+1)}. (cmod (v $$ (i div 2,0)))\<^sup>2))"sorry
  then have "sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2)
           = 1/sqrt(2) * sqrt((\<Sum>i\<in>{0..<2^n}. (cmod (v $$ (i,0)))\<^sup>2))"sorry
  then have "sqrt(\<Sum>i\<in>{0..<2^(n+1)}. (cmod (v $$ (i div 2,0) * (H * |one\<rangle>) $$ (i mod 2,0)) )\<^sup>2)
           = sqrt((\<Sum>i\<in>{0..<2^n}. (cmod (v' $$ (i,0)))\<^sup>2))"sorry

    have













end