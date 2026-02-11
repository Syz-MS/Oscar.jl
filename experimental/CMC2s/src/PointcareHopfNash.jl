export _PHN_locus
export global_PHN_index
export local_PHN_index

# M is the perturbed matrix, assuming M to define a EIDS of type t
function _PHN_locus(M::MatElem{<:MPolyRingElem}, t::Integer, f::MPolyRingElem)
  R = parent(f)
  @req R == base_ring(M) "The polynomial rings corresponding to f and M do not match."
  @req t >= 0 "t must be non-negative."
  (n, m) = size(M)
  @req t <= min(n, m) "t must be smaller than the number of rows resp. columns of M."
  I_M_gens = minors(M, t)
  J_total = jacobian_matrix(vcat(I_M_gens, f))
  polys_crit = minors(J_total, (n - t + 1) * (m - t + 1) + 1)
  I = ideal(R, vcat(I_M_gens, polys_crit))
  return quo(R, I)[1]
end

function global_PHN_index(M::MatElem{<:MPolyRingElem}, t::Integer, f::MPolyRingElem)
  return vector_space_dim(_PHN_locus(M, t, f))
end

function local_PHN_index(
  M::MatElem{<:MPolyRingElem}, t::Integer, f::MPolyRingElem, point::Array{<:FieldElem}
)
  Q = _PHN_locus(M, t, f)
  LQ_p, _ = localization(Q, complement_of_point_ideal(base_ring(Q), point))
  return vector_space_dim(LQ_p)
end


export _global_and_local_PHN_for
function _global_and_local_PHN_for(M::MatElem{<:MPolyRingElem}, t::Integer, f::MPolyRingElem, dist::MPolyRingElem)
  # f_pert = f + dist
  # f_pert_PHN = global_PHN_index(M,t,f_pert)
  # println("Global PHN-index f+dist: \t", f_pert_PHN)
  # f_PHN = global_PHN_index(M,t,f)
  # println("Global PHN-index f: \t", f_PHN)

  # println("Euler-obstruction f: \t", f_pert_PHN-f_PHN)

  Q = _PHN_locus(M,t,f)
  println("Global PHN-index: \t", vector_space_dim(Q))
  # println("\nAbsolute primary decomposition:")
  # APD = absolute_primary_decomposition(modulus(Q))
  # println(APD)

  points = rational_solutions(ideal(minors(M,1)));
  
  println("\nLocal PHN-index at rational points of singular locus of X_M:")
  for p in points
    LQ_p, _ = localization(Q, complement_of_point_ideal(base_ring(Q), p))
    println("\t", p, "\t", vector_space_dim(LQ_p))
  end
end

export PHN_test_const_pert_C6
function PHN_test_const_pert_C6(upper_bound::Integer)
  # Setup for J^51 and J52 in CC^6
  R,x = polynomial_ring(QQ, :x => (1:2, 1:3))
  t = 2
  pert_factor = QQ(1//10)

  f = 2*x[1,1]+5*x[1,2] + 3*x[1,3] - 5*x[2,1] - 7*x[2,2] + 11*x[2,3] 
  dist = x[1,1]^2 + x[1,2]^2 + x[1,3]^2 + x[2,1]^2 + x[2,2]^2 + x[2,3]^2


  println("Calculating global and local (at rational points) PHN-index for:")
  println("f = ", f)


  println("\n\n\nSingularity: Omega1")
    M = matrix(copy(x))
    # M[2,3] = x[2,3] - pert_factor^2#*x[2,3]
    _global_and_local_PHN_for(M,t,f,dist)


  println("\n\n\n\nSeries: Omega_{k+1} / Ak^dagger")
  for k in 1:upper_bound
    k_inc = k+1
    K,_ = cyclotomic_field(k_inc, "ζ_$k_inc")
    R,y = polynomial_ring(K, :x => (1:2, 1:3))
    # y = x
    M = matrix(copy(y))
    M[2,3] = y[1,1] + y[2,3]^(k+1) - pert_factor^(k+1) #*x[2,3]
    println("\n\nSingularity: Omega$(k+1) / A$k^dagger")
    _global_and_local_PHN_for(M,t, 
      change_coefficient_ring(K,f), change_coefficient_ring(K,dist)
      # f, dist
    )
  end


  println("\n\n\n\nSeries: Ak^#")
  for k in 1:upper_bound
    M = matrix(copy(x))
    M[2,3] = x[1,1]^(k+1) + x[1,2]^2 + x[2,3]^2 - pert_factor^2#*x[2,3]
    println("\n\nSingularity: A$k^#")
    _global_and_local_PHN_for(M,t,f,dist)
  end


  println("\n\n\n\nSeries: Dk^#")
  for k in 4:upper_bound
    M = matrix(copy(x))
    M[2,3] = x[1,1]^(k-1) + x[1,1]*x[1,2]^2 + x[2,3]^2 - pert_factor^2#*x[2,3]
    println("\n\n\nSingularity: D$k^#")
    _global_and_local_PHN_for(M,t,f,dist)
  end


  println("\n\n\n\nSeries: Ek^#")
    M = matrix(copy(x))
    #E6^#
    M[2,3] = x[1,1]^3 + x[1,2]^4 + x[2,3]^2 - pert_factor^2#*x[2,3]
    println("\n\nSingularity: E6^#")
    _global_and_local_PHN_for(M,t,f,dist)
    #E7^#
    M[2,3] = x[1,1]^3 + x[1,1]*x[1,2]^3 + x[2,3]^2 - pert_factor^2#*x[2,3]
    println("\n\nSingularity: E7^#")
    _global_and_local_PHN_for(M,t,f,dist)
    #E8^#
    M[2,3] = x[1,1]^3 + x[1,2]^5 + x[2,3]^2 - pert_factor^2#*x[2,3]
    println("\n\nSingularity: E8^#")
    _global_and_local_PHN_for(M,t,f,dist)


  println("\n\n\n\nSingularity: Q")
  K,_ = cyclotomic_field(3, "ζ_3")
  R,y = polynomial_ring(K, :x => (1:2, 1:3))
  M = matrix(copy(y))
  M[2,3] = y[1,1]^2 + y[1,2]^2 + y[2,3]^3 - pert_factor^3#*x[2,3]
  _global_and_local_PHN_for(M,t, change_coefficient_ring(K,f), change_coefficient_ring(K,dist))


  println("\n\n\n\nSeries: S_k,l")
  for l in 3:upper_bound
    for k in 2:upper_bound
    K,_ = cyclotomic_field(l, "ζ_$l")
    R,y = polynomial_ring(K, :x => (1:2, 1:3))
    # y = x
    M = matrix(copy(y))
    M[2,3] = y[1,1]*y[2,3] + y[1,2]^k + y[2,3]^l - pert_factor^l #*x[2,3]
    println("\n\nSingularity: S_$k,$l")
    _global_and_local_PHN_for(M,t, 
      change_coefficient_ring(K,f), change_coefficient_ring(K,dist)
      # f, dist
    )
    end
  end
    
end