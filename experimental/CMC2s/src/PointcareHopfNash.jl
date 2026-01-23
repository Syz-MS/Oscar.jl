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
function _global_and_local_PHN_for(M::MatElem{<:MPolyRingElem}, t::Integer, f::MPolyRingElem)
  Q = _PHN_locus(M,t,f)
  println("Global PHN-index: \t", vector_space_dim(Q))
  # println("\nAbsolute primary decomposition:")
  # APD = absolute_primary_decomposition(modulus(Q))
  # display(APD)

  points = rational_solutions(modulus(Q));
  
  println("\n\nLocal PHN-index at rational points:")
  for p in points
    LQ_p, _ = localization(Q, complement_of_point_ideal(base_ring(Q), p))
    println(p, "\t", vector_space_dim(LQ_p))
  end
end

export PHN_test_const_pert_C6
function PHN_test_const_pert_C6(upper_bound::Integer)
  # Setup for J^51 and J52 in CC^6
  R,x = polynomial_ring(QQ, :x => (1:2, 1:3))
  t = 2
  M = matrix(copy(x))
  pert_factor = QQ(-1//100)

  f = 2*x[1,1]+5*x[1,2] + 3*x[1,3] - 5*x[2,1] - 7*x[2,2] + 11*x[2,3] + x[1,1]^2 + x[1,2]^2 + x[1,3]^2 + x[2,1]^2 + x[2,2]^2 + x[2,3]^2


  display("Calculating global and local (at rational points) PHN-index for 'f':")
  display(f)

  display("Series: Ak^#")
  for k in 1:upper_bound
    M[2,3] = x[1,1]^(k+1) + x[1,2]^2 + x[2,3]^2 + pert_factor
    println()
  end

end