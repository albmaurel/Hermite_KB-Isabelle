theory Hermite_KB
  imports Modular_arithmetic_LLL_and_HNF_algorithms.HNF_Mod_Det_Algorithm
begin



(*Multiplicar por -1 la fila k es simplemente "multrow k (-1) A". *)

value "let A = mat_of_rows_list 4 ([
[  1,   9,   1,   9::int],
[  0,  10,   2,   3],
[  0,   0,  -12,   8],
[  0,   0,   0,  12]]) in 
  show (multrow 2 (-1) A)" (*El show es solo para que se muestre más bonito*)

(*RESULTADO:
[[1,  9,  1,  9], 
 [0, 10,  2,  3], 
 [0,  0, 12, -8], 
 [0,  0,  0, 12]]*)

(*Mediante esta definición modificamos una matriz A a partir de la creación de otra matriz del mismo tamaño. En esta matriz los valores por encima de la fila k se ajustan mediante
A$$(i,j) - A$$(k,j) * (A$$(i,k) div A$$(k,k), el resto de valores quedan intactos*)
definition reduce_off_diagonal :: "nat \<Rightarrow> int mat \<Rightarrow> int mat" where
  "reduce_off_diagonal k A =
    Matrix.mat (dim_row A) (dim_col A) \<comment> \<open> Creamos una matriz de las mismas dimensiones \<close>
    (\<lambda>(i,j). if i < k then A$$(i,j) - A$$(k,j) * (A$$(i,k) div A$$(k,k)) 
             else A $$ (i,j))"


(*Aquí se encuentra la definición de que en caso de que sea necesario se haga positivo el elemento en el pivote k,k de A
y se multiplique por -1 toda la fila k de A*)

fun reduce_positive :: "nat \<Rightarrow> int mat \<Rightarrow> int mat" where
  "reduce_positive k A = 
    (if A $$ (k,k) < 0 then
     (multrow k (-1) A)
    else A)"

thm reduce_positive.simps (* Para trabajar con una definition enel contexto de demostraciones, se crea un teorema aplicando definition.simps.*)

(*Caso general para la explicacion de que se cumple correctamente el algoritmo y su funcionamiento*)
lemma reduce_positive_works:
  assumes A: "A \<in> carrier_mat n n"
  shows "reduce_positive k A = (if A $$ (k,k) < 0 then multrow k (-1) A else A)"
  by auto


(*Lema destinado a comprobar que se cumple correctamente el algoritmo y uno de los funcionamientos buscados
En este caso es que una vez aplicada la función reduce_off_diagonal -> (reduce_off_diagonal k A) $$ (i,k) < (reduce_off_diagonal k A) $$ (k,k)*)
lemma reduce_off_diagonal_works1:
  assumes A: "A \<in> carrier_mat n n" 
    and ik: "i < k" and kn: "k<n"
    and Akk: "A $$ (k, k) > 0"
  shows "(reduce_off_diagonal k A) $$ (i,k) < (reduce_off_diagonal k A) $$ (k,k)" (is "?R $$ (i,k) < ?R$$ (k,k)")
proof -
  let ?f = "(\<lambda>(i, j). if i < k then A $$ (i, j) - A $$ (k, j) * (A $$ (i, k) div A $$ (k, k)) 
            else A $$ (i, j))"
  have "?R $$ (i,k) = ?f (i,k)" 
    unfolding reduce_off_diagonal_def by (rule index_mat, insert A ik kn, auto)
  also have "... = A$$(i,k) - A$$(k,k) * (A$$(i,k) div A$$(k,k))" using ik by auto
  also have "... = A $$ (i, k) mod A $$ (k, k)" unfolding minus_mult_div_eq_mod ..
  also have "... < A$$(k,k)" by (rule pos_mod_bound[OF Akk])
  also have "... = ?f (k,k)" by simp
  also have "... = ?R $$ (k,k)" 
    unfolding reduce_off_diagonal_def by (rule index_mat[symmetric], insert A ik kn, auto)
  finally show ?thesis .
qed

(*Lema destinado a comprobar que se cumple correctamente el algoritmo y uno de los funcionamientos buscados
En este caso es que una vez aplicada la función reduce_off_diagonal -> (reduce_off_diagonal k A) $$ (i,k) \<ge> 0*)
lemma reduce_off_diagonal_works2:
  assumes A: "A \<in> carrier_mat n n" 
    and ik: "i < k" and kn: "k<n"
    and Akk: "A $$ (k, k) > 0"
  shows "(reduce_off_diagonal k A) $$ (i,k) \<ge> 0" (is "?R$$ (i,k) \<ge> 0")
proof -
  let ?f = "(\<lambda>(i, j). if i < k then A $$ (i, j) - A $$ (k, j) * (A $$ (i, k) div A $$ (k, k)) 
            else A $$ (i, j))"
  have "?R $$ (i,k) = ?f (i,k)" 
    unfolding reduce_off_diagonal_def by (rule index_mat, insert A ik kn, auto)
  also have "... = A$$(i,k) - A$$(k,k) * (A$$(i,k) div A$$(k,k))" using ik by auto
  also have "... = A $$ (i, k) mod A $$ (k, k)" unfolding minus_mult_div_eq_mod ..
  also have "... \<ge>0" by (rule pos_mod_sign[OF Akk]) (*0 < b \<Rightarrow> 0 ≤ a mod b //Regla*)
  finally show ?thesis .
qed

thm reduce_positive.simps

(*Hacemos pruebas de ambas definiciones para comprobar que el resultado es el qeu buscamos y tienen el funcionamiento correcto*)
value "let A = mat_of_rows_list 4 ([
[  1,   9, -41,   9::int],
[  0,  10,   2,   3],
[  0,   0,  12,   8],
[  0,   0,   0,  12]]) in 
  show (reduce_off_diagonal 2 A)"

(*RESULTADO:
[[1,  9,  7, 41], 
 [0, 10,  2,  3], 
 [0,  0, 12,  8], 
 [0,  0,  0, 12]]*)

value "let A = mat_of_rows_list 4 ([
[  1,   9, -41,   9::int],
[  0,  -10,   2,   3],
[  0,   0,  12,   8],
[  0,   0,   0,  12]]) in 
  show (reduce_positive 1 A)"

(*RESULTADO:
[[1,  9, -41,  9], 
 [0, 10,  -2, -3], 
 [0,  0,  12,  8], 
 [0,  0,   0, 12]]*)


(*Se define este lema cuyo significado es que el MCD entre dos números enteros es positivo. Este lema es necesario para la demostración de algunos lemas posteriores*)
lemma pq_times_Ajj_plus_q_Aij_strictly_positive:
  fixes A :: "int mat"
  assumes A: "A \<in> carrier_mat n n"
    and j_n: "j < n"
    and Ajj_pos: "A $$ (j,j) \<noteq> 0"
    and pquvd: "(p, q, u, v, d) = euclid_ext2 (A $$ (j, j)) (A $$ (i, j))"
  shows "p * A $$ (j, j) + q * A $$ (i, j) > 0" 

proof -
 let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)
  have p: "p= fst (bezout_coefficients  ?Ajj ?Aij)"  using pquvd unfolding euclid_ext2_def  
    by (simp add: bezout_coefficients_fst_snd)
  have q: "q= snd (bezout_coefficients ?Ajj ?Aij)"  using pquvd unfolding euclid_ext2_def  
    by (simp add: bezout_coefficients_fst_snd)
  hence "p * A $$ (j, j) + q * A $$ (i, j) = d" using euclid_ext2_def d q p by auto
  also have "... = gcd (A $$ (j, j)) (A $$ (i, j))" 
    using bezout_coefficients_fst_snd d by blast
  also have "... > 0" unfolding gcd_pos_int using Ajj_pos by simp
  finally show ?thesis .
qed


(*Función para hacer un cero en la entrada A_ij a partir del pivote Ajj. j debe ser < i.
En el algoritmo del TFG trabajamos con j+1 como filas e i como columnas. Aquí se pone lo más obvio:
i las filas y j las columnas (aunque como es Ajj pues también se toma la j como fila cuando
interesa). *)
(*Hacer fun o definition en este caso da lo mismo*)

definition reduce :: "nat \<Rightarrow> int mat \<Rightarrow> nat \<Rightarrow> int mat" where
  "reduce i A j = 
    (
       let Ajj = A$$(j,j); Aij = A$$(i,j);
         (p,q,u,v,d) = euclid_ext2 Ajj Aij;
           A' = Matrix.mat (dim_row A) (dim_col A) 
                    (\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b))
       in
         if j > 0 then reduce_off_diagonal j  (reduce_positive j A')
         else A')"

(*La diferencia entre function y definition es que si se hace function reduce por defecto se "despliega la definición" 
(gracias a reduce.simps) y si lo hago con definition tendría que estar haciendo unfolding reduce_def.*)
thm reduce_def

(*Vamos a hacer un 0 en la posición (3,0). Los índices empiezan en 0.*)
value "let A = mat_of_rows_list 5 ([
[  6,   9, -41,   9, 8::int],
[  0,  10,   2,   3, 10],
[  0,   0,  12,   8, 14],
[  3,   5,   2,  12, -5],
[  -8,   8,  12,  8, 14]]) in 
  show (reduce 3 A 0 )" 

(*RESULTADO:
[[3,  5,  2, 12,  -5], 
 [0, 10,  2,  3,  10], 
 [0,  0, 12,  8,  14], 
 [0,  1, 45, 15, -18], 
 [-8, 8, 12,  8,  14]]*)

(*Vamos a hacer un 0 en la posición (3,1). Como pivote usará el A_11 (es decir, el número 10).*)
value "let A = mat_of_rows_list 5 ([
[  6,   9, -41,   9, 8::int],
[  0,  10,   2,   3, 10],
[  0,   0,  12,   8, 14],
[  3,   5,   2,  12, -5],
[  -8,   8,  12,  8, 14]]) in 
  show (reduce 3 A 1)" 

(*RESULTADO:
[[3,  4, -43, -3,  13],
 [3,  5,  2,  12, - 5], 
 [0,  0,  12,  8,  14], 
 [6,  0,  2,  21, -20],
 [-8, 8,  12,  8,  14]]*)

thm foldl.simps (*Comprobamos el funcionamiento de la función foldl*)

(*Si suponemos que estamos en la fila i y queremos hacer cero hasta la componente A_ii (no incluida),
lo que hacemos es iterar la función haciendo recursividad.*)

definition "reduce_row A i = foldl (reduce i) A ([0..<i])"

(*Demostrar que el elemento que esta debajo de la diagonal es 0 
tras aplicar el metodo reduce para j=0 *)
lemma reduce_zero_below_diagonal:
  assumes A: "A \<in> carrier_mat n n"
    and kn: "k < n"
    and ik: "i > k"
    and i_n: "i<n"
  shows "(reduce i A 0) $$ (i, 0) = 0"
proof -
  let ?Ajj = "A $$ (0,0)"
  let ?Aij = "A $$ (i,0)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" unfolding euclid_ext2_def by auto
  let ?f=  "\<lambda>(a,b). if a = 0 then p*A$$(0,b) + q*A$$(i,b)
                             else if a = i then u*A$$(0,b) + v * A$$(i,b)
                             else A$$(a,b)"

  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"
  have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have 1: "(reduce i A 0) = ?A'"
    unfolding reduce_def Let_def using pquvd unfolding euclid_ext2_def by auto
  have 2: "?A' $$ (i,0) = ?f (i,0)" by ( rule index_mat, insert assms, auto)
  from this have 3:"?f (i,0) =  u * A $$ (0, 0) + v * A $$ (i, 0)" using assms by auto 
  also have 4: "... = 0" unfolding u v
    by (smt (verit, del_insts) Groups.mult_ac(2) ab_semigroup_mult_class.mult_ac(1) 
        comm_monoid_gcd_class.gcd_dvd1 comm_monoid_gcd_class.gcd_dvd2 dvd_div_mult_self dvd_minus_iff minus_mult_right)
  show ?thesis using 1 2 3 4 by presburger
qed


(*Demostrar que el elemento que esta debajo de la diagonal en la fila i  y la columna j es 0 
tras aplicar el metodo reduce para i y j menor que i // En este caso lo mezclamos con el anterior lema para tener un lema general y más sólido*)
lemma reduce_works1:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and i_j: "j<i"
    and jg: "j\<ge>0"
    and ij: "i \<noteq>0"
  shows "(reduce i A j) $$ (i, j) = 0"
proof (cases "j=0")
  case True
  then have j0: "j=0" by simp
  then show ?thesis 
    using reduce_zero_below_diagonal[OF A _ _] i_n i_j 
    by simp
next
  case False
  then have jgrand: "j>0" using jg by simp
  let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij"
    unfolding euclid_ext2_def by auto
  let ?f = "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                      else if a = i then u*A$$(j,b) + v * A$$(i,b)
                      else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"
  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"
  have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij" using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients ?Ajj ?Aij) * ?Ajj +
              snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"
    using pquvd unfolding euclid_ext2_def by (simp add: bezout_coefficients_fst_snd)
  have 1: "(reduce i A j) = ?A''"
    unfolding reduce_def Let_def using pquvd jgrand unfolding euclid_ext2_def by auto
  have 2: "?A'' $$ (i, j) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (i, j)"
    using assms pquvd by blast
  have 3: "(reduce_off_diagonal j (reduce_positive j ?A')) $$ (i, j) = (reduce_positive j ?A') $$ (i, j)"
    unfolding reduce_positive.simps reduce_off_diagonal_def Let_def 
    using assms reduce_positive_works by auto
  have 4: "(reduce_positive j ?A') $$ (i, j) = ?A' $$ (i, j)"
    unfolding reduce_positive.simps using assms reduce_positive_works by auto
  have 5: "?A' $$ (i, j) = u * A $$ (j, j) + v * A $$ (i, j)" using assms by auto
  also have 6: "... = 0" unfolding u v d
    by (smt (verit, del_insts) Groups.mult_ac(2) ab_semigroup_mult_class.mult_ac(1) 
        comm_monoid_gcd_class.gcd_dvd1 comm_monoid_gcd_class.gcd_dvd2 dvd_div_mult_self 
        dvd_minus_iff minus_mult_right)
  show "(reduce i A j) $$ (i, j) = 0" 
    using 1 2 3 4 5 6 by presburger
qed


(*Demostrar que los metodos reduce_off_diagonal y reduce_positive no modifican los valores de las entradas
de la fila i y columnas j con j<i en el caso del reduce*)
lemma reduce_works2:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and i_j: "j<i"
    and j0: "j>0"
  and ij: "i \<noteq>0"
  and pquvd: "(p, q, u, v, d) = euclid_ext2 (A $$(j, j)) (A $$(i, j))"
  defines "A' \<equiv> Matrix.mat (dim_row A) (dim_col A) (\<lambda>(a,b). if a = j then p * A$$(j,b) + q * A$$(i,b)
                                                        else if a = i then u * A$$(j,b) + v * A$$(i,b)
                                                        else A$$(a,b))"
  shows  "(reduce_off_diagonal j  (reduce_positive j A')) $$ (i, j) = A' $$ (i,j)"
proof -
  let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" unfolding euclid_ext2_def by auto
  let ?f=  "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"
  
  have 0 : "?A'= A'" using assms pquvd unfolding reduce_def
    by (metis (no_types, lifting) Pair_inject)

  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"
   have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)
  
  have 1: "(reduce i A j) = ?A''"
    unfolding reduce_def Let_def using pquvd j0 unfolding euclid_ext2_def by auto
  
  have 2: "?A'' $$ (i, j) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (i, j)" using assms pquvd 
    by blast

  have 3: "(reduce_off_diagonal j (reduce_positive j ?A')) $$ (i, j) = (reduce_positive j ?A') $$ (i, j)"
    unfolding reduce_positive.simps reduce_off_diagonal_def Let_def using assms reduce_positive_works by auto

  from this have 4: "(reduce_positive j ?A') $$ (i, j) = ?A' $$ (i, j)"
    unfolding reduce_positive.simps using assms reduce_positive_works by auto

  from this have 5: "?A' $$ (i, j) =  u * A $$ (j, j) + v * A $$ (i, j)" using assms by auto
  
  also have 6: "... = 0" unfolding u v d
    by (smt (verit, del_insts) Groups.mult_ac(2) ab_semigroup_mult_class.mult_ac(1) 
        comm_monoid_gcd_class.gcd_dvd1 comm_monoid_gcd_class.gcd_dvd2 dvd_div_mult_self dvd_minus_iff minus_mult_right)

  show "(reduce_off_diagonal j (reduce_positive j A')) $$ (i, j) = A' $$ (i,j)" 
    using 0 1 2 3 4 5 6 by presburger
qed

(*Demostrar que para el caso de aplicar reduce sobre la fila i y la columna j los elementos en la fila i y 
las columnas k<j se mantienen en 0 suponiendo que ya son 0. Este lema es importante para comprobar que los 0's obtenidos no se modifican al aplicar al reduce a otras columnas*)
lemma reduce_works3:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and i_j: "j<i"
    and jg: "j>0"
    and ij: "i \<noteq>0"
    and j_k: "k<j"
    and Ajk: "A $$ (i,k) = 0" 
    and Ajk: "A $$ (j,k) = 0" (*necesaria esta premisa, es obvia debido al orden en el que se hacen los 0's en nuestro algoritmo, teniendo en cuenta que k<j y j<i*)
  shows "(reduce i A j) $$ (i, k) = A $$ (i,k)" 
proof -
     let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" unfolding euclid_ext2_def by auto
  let ?f=  "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"

  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"
   have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)
  
  have 1: "(reduce i A j) = ?A''"
    unfolding reduce_def Let_def using pquvd assms unfolding euclid_ext2_def by auto
  
  have 2: "?A'' $$ (i, k) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (i, k)" using assms pquvd 
    by blast
  have 3: "(reduce_off_diagonal j (reduce_positive j ?A')) $$ (i, k) = ?A'$$ (i,k)" using assms pquvd 
    unfolding reduce_off_diagonal_def
    by auto
  have 4: "?A'$$ (i,k) = u*A$$(j,k) + v * A$$(i,k)" using assms pquvd unfolding reduce_def by auto
  have 5: "?A'$$ (i,k) = A$$ (i,k) " using assms by auto
  show ?thesis using 1 2 3 4 5 by presburger
qed

(*Demostración de reduce_works1 sobre el Sucesor de i*)
lemma reduce_works_Suc:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and i_n2: "(Suc i)<n"
    and i_j: "j<i"
    and i_j2:"j\<ge>0"
    and ij: "i\<noteq>0"
  shows "(reduce (Suc i) A j) $$ (Suc i, j) = 0"
  by (rule reduce_works1[OF A i_n2 _ i_j2 _], insert i_n i_j, auto)

(*Lema para comprobar que se mantienen las dimensiones de la matriz después de aplicar reduce i A j*)
lemma reduce_carrier_mat: 
  assumes A: "A \<in> carrier_mat n n"
  shows "reduce i A j \<in> carrier_mat n n"
proof -
  let ?Ajj = "A $$ (j,j)"
  let ?Aij = "A $$ (i,j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" 
    by (metis euclid_ext2_def)

  let ?f = "\<lambda>(a,b). if a = j then p * A$$(j,b) + q * A$$(i,b)
                    else if a = i then u * A$$(j,b) + v * A$$(i,b)
                    else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"
  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"
  have A'_in_carrier: "?A' \<in> carrier_mat n n"
  proof
    show "dim_row ?A' = n"
      using assms by simp
    show "dim_col ?A' = n"
      using assms by simp
  qed

  have reduce_positive_in_carrier: "reduce_positive j ?A' \<in> carrier_mat n n"
    using A'_in_carrier by (cases "A$$(j, j) < 0", auto)

  have reduce_off_diagonal_in_carrier: "reduce_off_diagonal j (reduce_positive j ?A') \<in> carrier_mat n n"
  proof
    show "dim_row (reduce_off_diagonal j (reduce_positive j ?A')) = n"
      using reduce_positive_in_carrier unfolding reduce_off_diagonal_def by simp
    show "dim_col (reduce_off_diagonal j (reduce_positive j ?A')) = n"
      using reduce_positive_in_carrier unfolding reduce_off_diagonal_def by simp
  qed

  show "reduce i A j \<in> carrier_mat n n"
  proof (cases "j > 0")
    case True
    have "reduce i A j =  ?A''" 
      unfolding reduce_def Let_def using pquvd True unfolding euclid_ext2_def by auto
    thus ?thesis using reduce_off_diagonal_in_carrier by presburger
  next
    case False
    have "reduce i A j = ?A'" 
      unfolding reduce_def Let_def using pquvd False unfolding euclid_ext2_def by auto    
    thus ?thesis using A by auto      
  qed
qed

(*Demostración de que al aplicar reduce sobre la fila i y columna j los elementos de la columna j de las filas k tal que k<j son positivos o iguales a 0*)
lemma reduce_preserves_positivity_above:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i < n"
    and j_i: "j < i"
    and j0: "j > 0"
    and k_j: "k < j"
    and Ajj:"A $$ (j, j) \<noteq> 0" (*Esta condición es cierta, ya que al asumir que los menores principales de la matriz A son no singulares esto es verdad*)
  shows "(reduce i A j) $$ (k, j) \<ge> 0"
proof -
  let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" 
    unfolding euclid_ext2_def by auto

  let ?f=  "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"

  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"
   have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)
  have 1: "(reduce i A j) = ?A''"
      unfolding reduce_def Let_def using pquvd j0 unfolding euclid_ext2_def by auto
   have 2: "?A'' $$ (k, j) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (k, j)" using assms pquvd 
     by blast
   have 3: "(reduce_off_diagonal j (reduce_positive j ?A')) $$ (k, j)\<ge>0"
   proof(rule reduce_off_diagonal_works2) (*Hacemos uso del lema desarrollado anteriormente para la demostración de 3*)
      show  "(reduce_positive j ?A') \<in> carrier_mat n n"
      using assms by simp
      show "j < n"
      using assms by simp
      show  "k < j"
      using reduce_positive_works assms by auto
    show "(reduce_positive j ?A')$$ (j,j)>0"
    proof- (*Esta demostración no se puede hacer directamente por lo que se crea un nuevo proof -*)
    have "reduce_positive j ?A' \<in> carrier_mat n n"
       using assms by simp
     have "(reduce_positive j ?A') $$ (j, j) \<ge> ?A' $$ (j, j)"  
       using reduce_positive_works[of  ?A' j] assms
           by auto
      show ?thesis using assms  1 2    
            pq_times_Ajj_plus_q_Aij_strictly_positive pquvd by auto
        qed
      qed 
  thus  "(reduce i A j) $$ (k, j) \<ge> 0"
    using 1 2 3 reduce_def  
    by metis
qed

(*Demostrar que los elementos del bloque j-1 x j-1 de la matriz A no se modifican al aplicar reduce sobre la fila i y la columna j*)
lemma reduce_preserves_elements:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i < n"
    and j_i: "j < i"
    and j0: "j > 0"
    and k_j: "k < j"
    and l_j: "l < j"
    and zero_above1:" A $$ (i, l) = 0"
    and zero_above2:" A $$ (j, l) = 0" (*Asumimos que por el orden en el que se producen los  0's en nuestro algoritmo los elementos en la fila j y las columnas m<j son 0*)
    and Ajj:"A $$ (j, j) \<noteq> 0"
   shows "(reduce i A j) $$ (k, l) = A $$ (k, l)"
proof-
 let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" 
    unfolding euclid_ext2_def by auto
  let ?f=  "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"

  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"

   have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)
  have 1: "(reduce i A j) = ?A''"
      unfolding reduce_def Let_def using pquvd j0 unfolding euclid_ext2_def by auto
 have 2: "?A'' $$ (k, l) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (k, l)" using assms pquvd 
   by blast
  have 3 :"(reduce_off_diagonal j (reduce_positive j ?A')) $$ (k, l) = (reduce_positive j ?A') $$ (k, l)"
    using assms  pquvd pq_times_Ajj_plus_q_Aij_strictly_positive[OF A _ _ pquvd] reduce_positive_works 
    unfolding  reduce_off_diagonal_def Let_def reduce_positive.simps by auto
   have 4: "(reduce_positive j ?A') $$ (k, l) = ?A'  $$ (k, l)"
     unfolding reduce_positive.simps using reduce_positive_works assms by auto
   have 5: " ?A'  $$ (k, l) = A  $$ (k, l) "
     unfolding  reduce_def using assms by auto
   show ?thesis using 1 2 3 4 5 by presburger
qed

(*Demostramos que el pivote Ajj tras aplicar reduce i A j es mayor que los elementos de la columna j en las filas k<j*)
lemma reduce_lower_than_diagonal:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i < n"
    and j_i: "j < i"
    and j0: "j > 0"
    and Ajj:"A $$ (j, j) \<noteq> 0"
    and k_j: "k < j"
  shows "(reduce i A j) $$ (k, j) < (reduce i A j) $$ (j, j) "
  using pq_times_Ajj_plus_q_Aij_strictly_positive
proof -
  let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" 
    unfolding euclid_ext2_def by auto
  let ?f=  "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"

  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"

   have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)

  have 1: "(reduce i A j) = ?A''"
    unfolding reduce_def Let_def using pquvd j0 unfolding euclid_ext2_def by auto
   have 2: "?A'' $$ (k, j) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (k, j)" using assms pquvd 
     by blast
   have 4: "?A'' $$ (j, j) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (j, j)"
    unfolding reduce_off_diagonal_def
    using assms pquvd by simp
   have 3 :"(reduce_off_diagonal j (reduce_positive j ?A')) $$ (k, j) < (reduce_off_diagonal j (reduce_positive j ?A')) $$ (j, j)"
   proof (rule reduce_off_diagonal_works1) (*Hacemos uso del lema desarrollado anteriormente para la demostración de 3*)
     show "(reduce_positive j ?A') \<in> carrier_mat n n" using assms by simp
     show "k<j" using assms by simp
     show "j < n" using assms by simp
     show " (reduce_positive j ?A') $$ (j, j) > 0" 
       using reduce_positive_works Ajj assms pq_times_Ajj_plus_q_Aij_strictly_positive[OF A _ _ pquvd] 
       unfolding reduce_positive.simps by auto
   qed 
   have "reduce i A j $$ (k, j) < ?A'' $$ (j, j)" using 1 2 3 4  by auto
   also have "... = reduce i A j $$ (j, j)" using 1 by auto
   finally show ?thesis .
qed

(*Demostramos que se mantiene la propiedad de que el pivote Ajj es distinto de 0 al aplicar reduce i A j*)
lemma reduce_preserves_diagonal_entry:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i < n"
    and j_i: "j < i"
    and j0: "j > 0"
    and Ajj:"A $$ (j, j) \<noteq> 0"
  shows "(reduce i A j) $$ (j, j) \<noteq> 0" 
proof -
 let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" 
    unfolding euclid_ext2_def by auto
  let ?f=  "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"

  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"

   have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)

  have 1: "(reduce i A j) = ?A''"
    unfolding reduce_def Let_def using pquvd j0 unfolding euclid_ext2_def by auto
  have 2: "?A'' $$ (j, j) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (j, j)" using assms pquvd 
    by blast
  have 3: "(reduce_off_diagonal j (reduce_positive j ?A')) $$ (j, j) = (reduce_positive j ?A') $$ (j,j)" 
    using assms pquvd unfolding reduce_off_diagonal_def by auto
  have 4: "(reduce_positive j ?A') $$ (j,j) \<ge> ?A' $$ (j,j)" using reduce_positive_works assms by auto
  have 5: " ?A' $$ (j,j) =  p*A$$(j,j) + q*A$$(i,j)"  unfolding reduce_def using pquvd assms by auto
  also have 6: "... \<noteq> 0" using  assms pq_times_Ajj_plus_q_Aij_strictly_positive[OF A _ _ pquvd] by auto

  show "(reduce i A j) $$ (j, j) \<noteq> 0" using 1 2 3 4 5 6 
    using assms(1) assms(2) assms(3) j0 by force
qed

(*Demostramos que se mantiene la propiedad de que los pivotes Akk, con j<k<i,  son distintos de 0 al aplicar reduce i A j*)
lemma reduce_preserves_diagonal_entry2:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i < n"
    and j_i: "j < i"
    and j0: "j \<ge> 0"
    and k_j: "k>j" and "k<i"
    and Ajj:"A $$ (k, k) \<noteq> 0"
  shows "(reduce i A j) $$ (k, k) \<noteq> 0"
proof (cases "j=0") (*Distinguimos j=0 ya que en este caso por la definición de reduce no se aplicarian las funciones reduce positive ni reduce_off_diagonal*)
  case True
  let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" 
    unfolding euclid_ext2_def by auto
  let ?f=  "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"
 have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)
 then have j000: "j = 0" using True by simp
  have 1: "(reduce i A j) = ?A'"  unfolding reduce_def Let_def using pquvd j000 unfolding euclid_ext2_def by auto
  have 5: " ?A' $$ (k,k) =  A $$ (k,k)"  unfolding reduce_def using pquvd assms by auto
  also have 6: "... \<noteq> 0" using  assms  by auto
  show ?thesis using 1 5 6 assms by presburger
next
  case False
  let ?Ajj = "A $$(j, j)"
  let ?Aij = "A $$(i, j)"
  obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 ?Ajj ?Aij" 
    unfolding euclid_ext2_def by auto
  let ?f=  "\<lambda>(a,b). if a = j then p*A$$(j,b) + q*A$$(i,b)
                             else if a = i then u*A$$(j,b) + v * A$$(i,b)
                             else A$$(a,b)"
  let ?A' = "Matrix.mat (dim_row A) (dim_col A) ?f"

  let ?A''= "(reduce_off_diagonal j (reduce_positive j ?A'))"

  have u: "u =  - ?Aij div gcd ?Ajj ?Aij"
    using pquvd unfolding euclid_ext2_def by simp
  have v: "v = ?Ajj div gcd ?Ajj ?Aij"  using pquvd unfolding euclid_ext2_def by simp
  have d: "d= fst (bezout_coefficients  ?Ajj ?Aij) * ?Ajj +
    snd (bezout_coefficients ?Ajj ?Aij) * ?Aij"  using pquvd unfolding euclid_ext2_def 
    by (simp add: bezout_coefficients_fst_snd)
   then have j00: "j > 0" using False by simp
  have 1: "(reduce i A j) = ?A''"
    unfolding reduce_def Let_def using pquvd j00 unfolding euclid_ext2_def by auto
  have 2: "?A'' $$ (k, k) = (reduce_off_diagonal j (reduce_positive j ?A')) $$ (k, k)" using assms pquvd 
    by blast
  have 3: "(reduce_off_diagonal j (reduce_positive j ?A')) $$ (k, k) = (reduce_positive j ?A') $$ (k,k)" 
    using assms pquvd unfolding reduce_off_diagonal_def by auto
  have 4: "(reduce_positive j ?A') $$ (k,k) = ?A' $$ (k,k)" using reduce_positive_works assms by auto
  have 5: " ?A' $$ (k,k) =  A $$ (k,k)"  unfolding reduce_def using pquvd assms by auto
  also have 6: "... \<noteq> 0" using  assms  by auto

  show "(reduce i A j) $$ (k, k) \<noteq> 0" using 1 2 3 4 5 6 
    by presburger
qed

(*Como se comento en la memoria para poder estudiar los lemas sobre la función reduce_row es necesario demostrarlos primero para el foldl hasta un determinado j*)

(*Demostramos que al iterar recursivamente reduce de las columnas 0 hasta la j-1 se mantienen las dimensiones nxn de la matriz*)
lemma foldl_reduce_carrier_mat:
  assumes A: "A \<in> carrier_mat n n"
  shows "foldl (reduce i) A [0..<j] \<in> carrier_mat n n"
proof (induction j)
  case 0
  then show ?case using A by auto
next
  case (Suc j)
  have 1: "foldl (reduce i) A [0..<Suc j] = reduce i (foldl (reduce i) A [0..<j]) j" by auto
  also have 2:  "...  \<in> carrier_mat n n" by (rule reduce_carrier_mat[OF Suc]) 
  finally show ?case .
qed

(*Demostramos que al iterar recursivamente reduce de las columnas 0 hasta la j-1, el pivote Ajj sigue siendo distinto de 0*)
(*No esta demostrado*)
lemma foldl_preserves_diagonal_entry:
 assumes A: "A \<in> carrier_mat n n"
    and i: "i < n"
    and j: "j > 0"
    and i_j: "j<i"
    and Ajj:"A $$ (j, j) \<noteq> 0"
  shows "foldl (reduce i) A [0..<j] $$ (j, j) \<noteq> 0" sorry
(*OTRA POSIBILIDAD : O trabajando en (k,k) donde el problema es que no se entre que valores meter k para que me sirva*)

(*Demostramos que al iterar recursivamente reduce de las columnas 0 hasta la j-1, los pivotes All, con l<j, son mayores que los elementos de su columna que están por encima*)
lemma foldl_reduce_lower_than_diagonal:
  assumes A: "A \<in> carrier_mat n n"
    and i: "i < n"
    and k: "k<j"
    and j: "j > 0"
    and i_j: "j\<le>i"
    and l_j: "l<j"
    and k_l: "k<l"
    and Ail:"A $$ (i, l)= 0"
    and Ajj:"A $$ (j, j) \<noteq> 0"
  shows "foldl (reduce i) A [0..<j] $$ (k, l) < foldl (reduce i) A [0..<j] $$ (l, l)" 
  using i_j  j l_j k k_l Ajj
proof (induction j)
  case 0
  then show ?case using A by simp 
next
  case (Suc j)
    let ?F = "foldl (reduce i) A [0..<j]"
  note hyp=Suc(1)
  note Suc_j_less_i = Suc(2)
  note less_Suc_j = Suc(3) 
  note l_le_Suc_j = Suc(4)
  note k_le_Suc_j = Suc(5)
  note k_le_l = Suc(6)
  note Ajj1 = Suc(7)
  have reduce_Suc:"foldl (reduce i) A [0..<Suc j]  = reduce i ?F j" by auto
  also have 1:"...$$ (k, l) < reduce i ?F j $$ (l,l)" 
  proof (cases "l = j")
    case True
      have 1: "reduce i ?F j $$ (k, j) < reduce i ?F j $$ (j,j)"
      proof (rule reduce_lower_than_diagonal)
        show "?F \<in> carrier_mat n n" by (rule foldl_reduce_carrier_mat[OF A])
        show "i < n" using i by simp
        show "j < i" using Suc_j_less_i by simp
        show "0 < j" using less_Suc_j  k_le_l l_le_Suc_j by simp
        show "k < j" using True Suc(6) by simp
        show "?F $$ (j, j) \<noteq> 0"   
         proof( rule foldl_preserves_diagonal_entry)(*NO ESTÁ DEMOSTRADO*)
          show "A ∈ carrier_mat n n " using assms by auto
          show "i < n" using i by simp
          show "0 < j" using less_Suc_j  k_le_l l_le_Suc_j by simp
          show "j < i" using Suc_j_less_i by auto
          show "A $$ (j, j) ≠ 0" using Suc.prems assms sorry
         qed
      qed
      show ?thesis using True 1 reduce_Suc unfolding reduce_def 
        by meson
  next
    case False
    then have l_less_j: "l < j" using l_le_Suc_j by simp
    have 4:"?F $$ (k, l) < ?F $$ (l, l)"
       proof (rule hyp) (*HIPOTESIS DE INDUCCIÓN*)
         show "j\<le>i" by (simp add: Suc(2) Suc_leD) 
         show "0< j"  using  less_Suc_j  k_le_l l_le_Suc_j by auto
         show "l < j" using Suc(4) 
           by (simp add: l_less_j)
         show " k < j" using  l_less_j  Suc(6) by auto
         show "k<l" using assms by auto
         show "A $$ (j, j) \<noteq> 0" sorry
       qed 
   have 5:"reduce i ?F j $$ (k, l) = ?F $$ (k, l)"
   proof(rule reduce_preserves_elements) (*LEMA DEMOSTRADO ANTES*)
     show "?F\<in> carrier_mat n n"  by (rule foldl_reduce_carrier_mat[OF A])
     show "i < n" using i by simp
     show "j < i" using Suc_j_less_i by simp
     show "0 < j" using less_Suc_j  k_le_l l_le_Suc_j by simp
     show "l < j" using Suc(4) 
       by (simp add: l_less_j)
     show " k < j" using  l_less_j  Suc(6) by auto
     show "foldl (reduce i) A [0..<j] $$ (i, l) = 0" sorry (*NO ESTÁ DEMOSTRADO*)
     show "foldl (reduce i) A [0..<j] $$ (j, l) = 0" sorry (*NO ESTÁ DEMOSTRADO*)
     show "?F $$ (j,j)\<noteq>0" sorry (*NO ESTÁ DEMOSTRADO*)
   qed
   have 6:"reduce i ?F j $$ (k, l) < ?F $$ (l,l)" using  False 4 5 l_less_j 
     by linarith
   also have 7:"reduce i ?F j $$ (l, l) = ..."  
   proof(rule reduce_preserves_elements) (*POSIBLE DEMOSTRACIÓN*)
     show "?F\<in> carrier_mat n n"  by (rule foldl_reduce_carrier_mat[OF A])
     show "i < n" using i by simp
     show "j < i" using Suc_j_less_i by simp
     show "0 < j" using less_Suc_j sledgehammer
       using l_less_j by auto
     show "l < j" using Suc(4) 
           by (simp add: l_less_j)
     show "l < j" using Suc(4) 
       by (simp add: l_less_j)
     show "foldl (reduce i) A [0..<j] $$ (i, l) = 0" sorry (*NO ESTÁ DEMOSTRADO*)
     show "foldl (reduce i) A [0..<j] $$ (j, l) = 0" sorry (*NO ESTÁ DEMOSTRADO*)
     show "?F $$ (j,j)\<noteq>0" sorry (*NO ESTÁ DEMOSTRADO*)
   qed
    finally show ?thesis using 4 5 6  7 False l_less_j by auto
  qed
  finally show ?case .
qed

(*Demostramos que al iterar recursivamente reduce de las columnas 0 hasta la j-1, los elementos de la fila i y de las columnas k, con k<j, son 0's*)
lemma foldl_reduce_0:
  assumes A: "A \<in> carrier_mat n n"
    and kj: "k < j"
    and i_n: "i<n"
    and i_j: "j\<le>i"
  and j: "j>0"
  shows  "foldl (reduce i) A [0..<j] $$ (i,k) = 0" 
  using  i_j  j kj
proof (induction j)
  case 0
  then show ?case by auto
next
  case (Suc j)
  let ?F = "foldl (reduce i) A [0..<j]"
  note hyp=Suc(1)
  note Suc_j_less_i = Suc(2)
  note less_Suc_j = Suc(3)
  note k_le_Suc_j = Suc(4)
  have "foldl (reduce i) A [0..<Suc j]  = reduce i ?F j" by auto
  also have "...$$(i, k) = 0" 
  proof (cases "k=j")
    case True
    have "reduce i ?F j $$ (i,j) = 0" 
    proof (rule reduce_works1) 
      show "foldl (reduce i) A [0..<j] \<in> carrier_mat n n" by (rule foldl_reduce_carrier_mat[OF A])
      show "i < n" using i_n by auto
      show "j < i"  using Suc(2) le_simps(3) by blast
      show "0 \<le> j" by simp
      show "i \<noteq> 0" using Suc(2) by linarith
    qed
    thus ?thesis using True by simp
  next
    case False
    hence k_less_j: "k<j"
      using Suc(4) less_SucE by blast
    have hyp: "?F $$ (i,k) = 0" 
    proof (rule hyp) (*HIPOTESIS DE INDUCCIÓN*)
      show "j\<le>i" by (simp add: Suc(2) Suc_leD) 
      show "0 < j" using k_less_j by linarith
      show "k < j" using k_less_j .
    qed
    have "reduce i ?F j $$ (i, k) = ?F $$ (i, k)"       
    proof (rule reduce_works3) (*LEMA DEMOSTRADO ANTES*)
      show "foldl (reduce i) A [0..<j] \<in> carrier_mat n n" by (rule foldl_reduce_carrier_mat[OF A])
      show "i < n" using i_n by auto
      show "j < i"  using Suc(2) le_simps(3) by blast
      show "0 < j"  using k_less_j by linarith
      show "i \<noteq> 0" using Suc(2) by linarith
      show "k < j" using k_less_j .
      show "?F  $$ (i, k) = 0"  using hyp by simp
      show "?F  $$ (j, k) = 0" sorry (*NO ESTÁ DEMOSTRADO*)
    qed
    also have "?F $$ (i, k) = 0" using hyp by simp
    finally show ?thesis .
  qed
  finally show ?case .
qed

(*Demostramos que al iterar recursivamente reduce de las columnas 0 hasta la j-1, las entradas del bloque j-1 x j-1 son mayores o iguales a 0*)
lemma foldl_reduce_positive_elements:
  assumes A: "A \<in> carrier_mat n n"
    and i: "i < n"
    and k: "k < j"
    and j: "j > 0"
    and i_j: "j \<le> i"
    and l_j: "l < j"
  shows "foldl (reduce i) A [0..<j] $$ (k, l) \<ge> 0"
  using i_j  j l_j k  
proof (induction j) (*Distinguimos 4 casos, las combinaciones posibles de k=j l=j l<j y k<j*)
  case 0
  then show ?case using A by simp 
next
  case (Suc j)
  let ?F = "foldl (reduce i) A [0..<j]"
  note hyp = Suc(1)
  note Suc_j_less_i = Suc(2)
  note less_Suc_j = Suc(3) 
  note l_le_Suc_j = Suc(4)
  note k_le_Suc_j = Suc(5)

  have reduce_Suc: "foldl (reduce i) A [0..<Suc j] = reduce i ?F j" by simp
  also have "... $$ (k, l) \<ge> 0"
  proof (cases "l = j")
    case True
    then show ?thesis
    proof (cases "k < j")
      case True
      from `l = j` have l_j: "l = j" .
      hence k_less_j: "k<j"
        using Suc(4) less_SucE 
        using True by linarith
      have 1: "reduce i ?F j $$ (k, j) \<ge> 0"
      proof (rule reduce_preserves_positivity_above)
        show "?F \<in> carrier_mat n n" by (rule foldl_reduce_carrier_mat[OF A])
        show "i < n" using i by simp
        show "j < i" using Suc_j_less_i by simp
        show "0 < j" using k_less_j by auto
        show "k < j" using True by simp
        show "?F $$ (j, j) \<noteq> 0"   using reduce_Suc unfolding reduce_def 
          sorry (*NO ESTÁ DEMOSTRADO*)   
      qed
      show ?thesis using  True 1 reduce_Suc k_less_j l_j unfolding reduce_def
        by fastforce   
      next
      case False
      then have "k = j" using k_le_Suc_j by simp
      have 2: "reduce i ?F j $$ (j, j) > 0" using pq_times_Ajj_plus_q_Aij_strictly_positive reduce_Suc
            False unfolding reduce_def 
        sorry  (*NO ESTÁ DEMOSTRADO*)   
      then show ?thesis using 2 False reduce_Suc unfolding reduce_def 
        using True \<open>k = j\<close> by presburger
      qed
  next
    case False
    then have l_less_j: "l < j" using l_le_Suc_j by simp
    show ?thesis
    proof (cases "k < j")
      case True
      hence k_less_j: "k<j"
      using Suc(4) less_SucE by blast
      have hyp:"?F $$ (k, l) \<ge> 0"
       proof (rule hyp)
         show "j\<le>i" by (simp add: Suc(2) Suc_leD) 
         show "0< j"  using k_less_j by auto
         show "l < j" using Suc(4) 
           by (simp add: l_less_j)
         show " k < j" using Suc(5) less_SucE  True by auto
       qed  
    have 3:"reduce i ?F j $$ (k, l) = ?F $$ (k, l)"
    proof (rule reduce_preserves_elements)
       show "?F \<in> carrier_mat n n" by (rule foldl_reduce_carrier_mat[OF A])
       show "i < n" using i by simp
       show "j < i" using Suc_j_less_i by simp
       show "0 < j" using k_less_j by simp
       show "k < j" using True by simp
       show " l < j" using Suc(4) 
           by (simp add: l_less_j)
       show "?F $$ (j, j) \<noteq> 0"   using reduce_Suc unfolding reduce_def 
         sorry (*NO ESTÁ DEMOSTRADO*)
       show "foldl (reduce i) A [0..<j] $$ (i, l) = 0" sorry (*NO ESTÁ DEMOSTRADO*)
       show "foldl (reduce i) A [0..<j] $$ (j, l) = 0" sorry (*NO ESTÁ DEMOSTRADO*)
     qed
    also have "?F $$ (k, l) \<ge> 0" using hyp by simp
    then show ?thesis using True reduce_Suc  3 hyp
      by linarith   
    next
      case False
      then have 3: "k = j" using k_le_Suc_j by simp
      have 4:" reduce i ?F j  $$ (j, l) = ?F $$ (j, l)" sorry (*NO ESTÁ DEMOSTRADO*)
      also have 5:"... = 0" using False 3 reduce_Suc foldl_reduce_0[OF A] unfolding reduce_def 
        using Suc(3) sorry (*NO ESTÁ DEMOSTRADO*)
      then show ?thesis using False reduce_Suc 3 4  
        using assms(2) by auto
    qed
  qed
  finally show ?case .
qed

(*A continuación demostraremos lemas aplicados a la función reduce_row*)

(*Demostramos que se mantienen la dimensiones de la matriz al aplicar reduce_row A sobre la fila i*)
lemma reduce_row_carrier:
  assumes A: "A \<in> carrier_mat n n"
  shows "(reduce_row A i) \<in> carrier_mat n n"
proof -
  have "reduce_row A i = foldl (reduce i) A [0..<i]"
    unfolding reduce_row_def by simp
  also have "... \<in> carrier_mat n n"
    by (rule foldl_reduce_carrier_mat[OF A]) (*Hacemos uso del lema foldl_reduce_carrier_mat demostrado anteriormente*)
  finally show ?thesis .
qed

(*Demostramos que se tienen ceros en la fila i hasta la posición i (no incluida) al aplicar reduce_row sobre la fila i en la matriz A*)
lemma reduce_row_induction:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and i_j: "j<i"
  shows  "(reduce_row A i) $$ (i,j) = 0" 
proof -
  have "(reduce_row A i) $$ (i,j) = foldl (reduce i) A [0..<i] $$ (i, j) " 
    unfolding reduce_row_def ..
  also have "... = 0" 
  proof (rule foldl_reduce_0[OF A i_j i_n]) (*Hacemos uso del lema foldl_reduce_0 demostrado anteriormente*) (*Al no tener este lema demostrado entero no podemos asegurar esto*)
    show "i \<le> i" by simp
    show "0 < i" using i_j by auto
  qed
  finally show ?thesis .
qed

(*Demostramos que depués de aplicar reduce_row sobre A y la fila i, las entradas del bloque i-1 x i-1 de la matriz son positivas o iguales a 0*)
lemma reduce_row_positive:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and i_j: "j<i"
    and ki: "k<i"
  shows  "(reduce_row A i) $$ (k,j)\<ge> 0" 
proof -
  have "(reduce_row A i) $$ (k,j) = foldl (reduce i) A [0..<i] $$ (k, j) " 
    unfolding reduce_row_def ..
  also have "...\<ge> 0" 
  proof (rule foldl_reduce_positive_elements[OF A i_n ki])(*Hacemos uso del lema foldl_reduce_positive_elements demostrado anteriormente*) 
  (*Al no tener este lema demostrado entero no podemos asegurar esto*)
    show "0<i" using assms by simp
    show "i \<le> i" by simp
    show "j<i" using assms by simp
  qed
  finally show ?thesis .
qed

(*Demostramos que al aplicar reduce_row sobre la matriz A y la fila i, los pivotes Ajj, con j<i, son mayores que los elementos de la columna j por encima de este*)
lemma reduce_row_lower_diagonal:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and i_j: "j<i"
    and ki: "k<i"
    and kj:"k<j"
    and "A$$ (i,j) = 0"
    and "A $$ (i, i) \<noteq> 0"
  shows  "(reduce_row A i) $$ (k,j)<(reduce_row A i) $$ (j,j)" 
proof -
  have 1:"(reduce_row A i) $$ (k,j) = foldl (reduce i) A [0..<i] $$ (k, j) " 
    unfolding reduce_row_def ..
  have 2: "(reduce_row A i) $$ (j,j) = foldl (reduce i) A [0..<i] $$ (j, j) "
    unfolding reduce_row_def..
  also have 3: "foldl (reduce i) A [0..<i] $$ (k, j) < foldl (reduce i) A [0..<i] $$ (j, j)" 
  proof (rule foldl_reduce_lower_than_diagonal[OF A i_n ki]) (*Hacemos uso del lema foldl_reduce_positive_elements demostrado anteriormente*)
  (*Al no tener este lema demostrado entero no podemos asegurar esto*)
    show "0<i" using assms by simp
    show "i \<le> i" by simp
    show "j<i" using assms by simp
    show "k<j" using assms by simp
    show "A $$ (i, j) = 0" using assms by simp
    show "A $$ (i, i) \<noteq> 0" using assms by simp
  qed
  finally show ?thesis using 1 2 3 by presburger
qed

(*Final_reduce tiene como objetivo realizar las operaciones del bucle principal*)
definition final_reduce :: "int mat \<Rightarrow> nat \<Rightarrow> int mat" where
    "final_reduce A i = 
        (let A' = reduce_row A i;
             A'' = reduce_positive i A'
         in reduce_off_diagonal i  A'') "


(*Demostramos que al aplicar final_reduce A i la matriz A mantiene las dimensiones y es una matriz cuadrada nxn*)
lemma final_reduce_carrier_mat:
  assumes A: "A \<in> carrier_mat n n"
  shows "final_reduce A i \<in> carrier_mat n n"
proof -
  let ?A' = "reduce_row A i"
  let ?A'' = "reduce_positive i ?A'"
  let ?A''' = "reduce_off_diagonal i ?A''"
  
  have A'_in_carrier: "?A' \<in> carrier_mat n n"
    by (rule reduce_row_carrier[OF A]) (*Hacemos uso del lema reduce_row_carrier demostrado anteriormente*)
  have reduce_positive_in_carrier: "reduce_positive i ?A' \<in> carrier_mat n n"
    using A'_in_carrier by (cases "A$$(i, i) < 0", auto)

  have A''_in_carrier: "?A'' \<in> carrier_mat n n"
    by (meson reduce_positive_in_carrier)

  have reduce_off_diagonal_in_carrier: "reduce_off_diagonal i (reduce_positive i ?A') \<in> carrier_mat n n"
  proof
    show "dim_row (reduce_off_diagonal i (reduce_positive i ?A')) = n"
      using reduce_positive_in_carrier unfolding reduce_off_diagonal_def by simp
    show "dim_col (reduce_off_diagonal i (reduce_positive i ?A')) = n"
      using reduce_positive_in_carrier unfolding reduce_off_diagonal_def by simp
  qed

  have A'''_in_carrier: "?A''' \<in> carrier_mat n n"
    using reduce_off_diagonal_in_carrier by auto

  show ?thesis
    by (metis A'''_in_carrier final_reduce_def)
qed

(*Este lema es necesario para la demostración de final_reduce_induction*)
(*Demostramos que al aplicar reduce_off_diagonal y reduce_positive sobre i las entradas A $$ (i,j) = 0 (estas son 0 por la naturaleza del algoritmo) siguen siendo 0*)
lemma reduce_off_pos_works:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i < n"
    and i_j: "j < i"
    and A_ij_zero: "A $$ (i,j) = 0"
  shows "(reduce_off_diagonal i (reduce_positive i A)) $$ (i, j) = A $$ (i,j)"
proof -
  let ?A' = "reduce_positive i A"
  let ?A'' = "reduce_off_diagonal i ?A'"

  have A'_ij_eq: "?A' $$ (i, j) = A $$ (i, j)"
    unfolding reduce_positive.simps using assms reduce_positive_works by auto

  have A''_ij_eq: "?A'' $$ (i, j) = ?A' $$ (i, j)"
       unfolding reduce_positive.simps reduce_off_diagonal_def Let_def using assms reduce_positive_works by auto
  show ?thesis
    using A''_ij_eq A'_ij_eq A_ij_zero by simp
qed

(*Demostramos que al aplicar final_reduce A sobre la fila i, los elementos de la fila i i de las columnas j, con j<i, son 0*)
lemma final_reduce_induction:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and i_j: "j<i"
  shows  "(final_reduce A i) $$ (i,j) = 0"
proof-
  let ?A' = "reduce_row A i"
  let ?A'' = "reduce_positive i ?A'"
  let ?A''' = "reduce_off_diagonal i ?A''"

  have 1: "(final_reduce A i) =  ?A'''"
    using final_reduce_def by auto
  have 2: "?A'''=reduce_off_diagonal i ?A''" by auto
  have 3 :"(reduce_off_diagonal i (reduce_positive i ?A')) $$ (i, j) =  ?A' $$ (i, j)"
  proof (rule reduce_off_pos_works) (*Hacemos uso del lema anterior*)
    show "?A' \<in> carrier_mat n n" 
      by (simp add: assms(1) reduce_row_carrier)
    show "i<n" using assms by auto
    show "j<i" using assms by auto
    show "?A' $$ (i, j) = 0"
      by (rule reduce_row_induction[OF A i_n i_j]) (*Hacemos uso del lema reduce_row_induction demostrado anteriormente*)
	  (*Al no poder asegurar el lema reduce_row_induction, tampoco podemos asegurar que este es cierto*)
  qed
  have 4:"?A' $$ (i, j) = 0"
    by (rule reduce_row_induction[OF A i_n i_j])

  show ?thesis using 1 2 3 4 by presburger
qed

(*Demostramos que final_reduce A  sobre la fila i, consigue que las entradas A(k,i) de la matriz resultante so positivas o iguales a 0  *)
lemma final_reduce_row_positive:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and ki: "k<i"
    and Aii:"A $$ (i, i) \<noteq> 0"
  shows "(final_reduce A i) $$ (k,i) \<ge> 0" 
proof-
  let ?A' = "reduce_row A i"
  let ?A'' = "reduce_positive i ?A'"
  let ?A''' = "reduce_off_diagonal i ?A''"

  have 1: "(final_reduce A i) =  ?A'''"
    using final_reduce_def by auto
  have 2: "?A'''=reduce_off_diagonal i ?A''" by auto
  have 3 : "(reduce_off_diagonal i (reduce_positive i ?A')) $$ (k, i)\<ge>0"
   proof(rule reduce_off_diagonal_works2)
      show  "(reduce_positive i ?A') \<in> carrier_mat n n"
      using assms by (simp add: assms(1) reduce_row_carrier)
      show "i < n"
      using assms by simp
      show  "k < i"
      using  assms by auto
    show "(reduce_positive i ?A')$$ (i,i) > 0"
    proof-
    have 4:"reduce_positive i ?A' \<in> carrier_mat n n"
       using assms by (simp add: assms(1) reduce_row_carrier)
     have 5:"(reduce_positive i ?A') $$ (i, i) \<ge> ?A' $$ (i, i)"  
       using reduce_positive_works[of  ?A' i] assms 
            reduce_positive.simps 4  by auto
     have 6:  "?A' $$ (i, i) = A $$ (i, i)" using assms 1 2 4 5 unfolding reduce_row_def sorry (*NO ESTÁ DEMOSTRADO*)
      show ?thesis using assms  1 2 4 5 6 by auto
        qed
      qed   

  show ?thesis using 1 2 3  by presburger
qed


(*Demostramos que final_reduce A  sobre la fila i, el pivote Aii es mayor que la entradas de la columna i por encima de este*)
lemma final_reduce_lower_diagonal:
  assumes A: "A \<in> carrier_mat n n"
    and i_n: "i<n"
    and ki: "k<i"
    and "A $$ (i, i) \<noteq> 0"
  shows  "(final_reduce A i) $$ (k,i) < (final_reduce A i) $$ (i,i)" 
proof-
  let ?A' = "reduce_row A i"
  let ?A'' = "reduce_positive i ?A'"
  let ?A''' = "reduce_off_diagonal i ?A''"

  have 1: "(final_reduce A i) =  ?A'''"
    using final_reduce_def by auto
  have 2: "?A'''=reduce_off_diagonal i ?A''" by auto
  have 3 :"(reduce_off_diagonal i (reduce_positive i ?A')) $$ (k, i) < (reduce_off_diagonal i (reduce_positive i ?A')) $$ (i, i)"
   proof (rule reduce_off_diagonal_works1) (*Hacemos uso del lema desarrollado anteriormente para la demostración de 3*)
     show "(reduce_positive i ?A') \<in> carrier_mat n n"
       using assms by (simp add: assms(1) reduce_row_carrier)
     show "k<i" using assms by simp
     show "i < n" using assms by simp
     show " (reduce_positive i ?A') $$ (i, i) > 0" 
        proof-
        have 4:"reduce_positive i ?A' \<in> carrier_mat n n"
            using assms by (simp add: assms(1) reduce_row_carrier)
        have 5:"(reduce_positive i ?A') $$ (i, i) \<ge> ?A' $$ (i, i)"  
            using reduce_positive_works[of  ?A' i] assms 
            reduce_positive.simps 4  by auto
        have 6:  "?A' $$ (i, i) = A $$ (i, i)" using assms 1 2 4 5 unfolding reduce_row_def sorry (*NO ESTÁ DEMOSTRADO*)
      show ?thesis using assms  1 2 4 5 6 by auto
        qed
   qed 
   have "(final_reduce A i) $$ (k,i) < ?A''' $$ (i, i)" using 1 2 3  by auto
   also have "... = (final_reduce A i) $$ (i,i)" using 1 by auto
   finally show ?thesis .
 qed


(*Y ahora itero el proceso desde la primera fila hasta la última (suponemos que es cuadrada):*)
definition "HNF_Kannan_Bachem A = foldl (final_reduce) A [0..<dim_row A]"



(*Voy a hacer ceros hasta  la fila 3 (la cuarta fila porque empieza en 0)*)
value "let A = mat_of_rows_list 5 ([
[  6,   9, -41,   9, 8::int],
[  0,  10,   2,   3, 10],
[  0,   0,  12,   8, 14],
[  3,   5,   2,  12, -5],
[  -8,   8,  12,  8, 14]]) in 
  show (reduce_row A 3)" 

(*RESULTADO
[[3,  0,  1, -8407, -39563], 
 [0,  1,  1,  1654,   7770], 
 [0,  0,  4,  -149,   -708], 
 [0,  0,  0,  -455,  -2138], 
 [-8, 8, 12,     8,     14]]*)

value "let A = mat_of_rows_list 3 ([
        [3, 6, -9::int],
        [1, 4, -7],
        [0, 5, -8]]) in 
  show (final_reduce A 2)" 

(*RESULTADO:
[[4,  0, 0], 
 [-6, 1, 2], 
 [-5, 0, 3]]*)

(*Si ahora cojo una matriz 5x5 llena de números:*)
value "let A = mat_of_rows_list 5 ([
[  6,   9, -41,   9, 8::int],
[  0,  10,   2,   3, 10],
[  0,   0,  12,   8, 14],
[  3,   5,   2,  12, -5],
[  -8,   8,  12,  8, 14]]) in
  show (HNF_Kannan_Bachem A)" 

(*RESULTADO:
[[1, 0, 3, 1,  6247], 
 [0, 1, 1, 2,   466], 
 [0, 0, 4, 5, 12856], 
 [0, 0, 0, 7,  8746], 
 [0, 0, 0, 0, 29808]]*)

definition is_in_Hermite :: "int mat \<Rightarrow> bool"
  where "is_in_Hermite A = (
  (\<forall>i<dim_row A. \<forall>j<dim_col A. A $$ (i, j) \<ge> 0) \<comment> \<open> Todas las entradas son no negativas\<close>
  \<and> echelon_form_JNF A \<comment> \<open>Está en forma escalonada\<close>
  \<and> (\<forall>i<dim_row A. (\<forall>j. j<i \<longrightarrow> A $$ (j, i) < A $$(i,i) \<comment> \<open>Las cosas por encima de la diagonal están reducidas\<close>
  )))"


lemma Final:
  assumes A: "A \<in> carrier_mat n n"
  and inv_A: "invertible_mat A"
 shows "is_in_Hermite (HNF_Kannan_Bachem A)"
  sorry
end