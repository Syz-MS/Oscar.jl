export GL_determinacy_bound
export weighted_initial_order
export weighted_initial_degree_matrix
export weighted_initial_jet
export weighted_k_jet
export is_quasihomogeneous
export relative_matrix_weight
export weighted_GL_determinacy

function GL_determinacy_bound(M::MatElem{<:MPolyRingElem})
  L = base_ring(parent(M))
  F = free_module(L, number_of_rows(M) * number_of_columns(M))
  m = ideal(L, gens(L))
  # transpose is important for rowwise linear index of vec()
  JM, _ = sub(F, F.(vec.(Array.(_J(transpose(M))))))
  Im_g, _ = sub(F, F.(vec.(Array.(vcat(_S_2(transpose(M)), _S_3(transpose(M)))))))
  S = (m^2 * JM)[1] + (m^2 * Im_g)[1]
  ord = invlex(ambient_free_module(S)) * negdeglex(base_ring(S))
  LS = leading_module(S, ord)
  Q, _ = quo(F, LS)
  d = vector_space_dim(Q)
  d == -1 && return PosInf()
  mkF = (m * F)[1]
  for k in 1:d
    mkF = (m * mkF)[1]
    if is_subset(mkF, LS)
      return k
    end
  end
end

################# Quasihomogeneous GL-determinacy

# TODO: better relative rows and columns check for 0 entries

function weighted_initial_order(f::MPolyRingElem, w::Vector{<:Integer})
  !is_zero(f) || return PosInf()
  return minimum([sum(e .* w) for e in exponents(f)])
end

function weighted_initial_degree_matrix(M::MatElem{<:MPolyRingElem}, w::Vector{<:Integer})
  @req all(>(0), w) "Entries of 'w' must be positive"
  @req ngens(base_ring(M)) == length(w) "Number of variables of the polynomial ring of the entries of 'M' and length of weight vector 'w' do not match."
  D = Array{Any}(undef, size(M))
  for pos in eachindex(M)
    D[pos] = weighted_initial_order(M[pos], w)
  end
  return D
end

function weighted_initial_jet(f::MPolyRingElem, w::Vector{<:Integer})
  @req all(>(0), w) "Entries of 'w' must be positive"
  @req ngens(parent(f)) == length(w) "Number of variables of the polynomial ring of 'f' and length of weight vector 'w' do not match."
  !is_zero(f) || return f
  v_w = weighted_initial_order(f, w)
  in_w = MPolyBuildCtx(parent(f))
  for (coeff, exp) in coefficients_and_exponents(f)
    if sum(exp .* w) == v_w
      push_term!(in_w, coeff, exp)
    end
  end
  return finish(in_w)
end

function weighted_initial_jet(M::MatElem{<:MPolyRingElem}, w::Vector{<:Integer})
  @req all(>(0), w) "Entries of 'w' must be positive"
  @req ngens(base_ring(M)) == length(w) "Number of variables of the polynomial ring of the entries of 'M' and length of weight vector 'w' do not match."
  in_w(f::MPolyRingElem) = weighted_initial_jet(f, w)
  return in_w.(M)
end

function weighted_k_jet(f::MPolyRingElem, k::Integer, w::Vector{<:Integer})
  @req all(>(0), w) "Entries of 'w' must be positive"
  @req ngens(parent(f)) == length(w) "Number of variables of the polynomial ring of 'f' and length of weight vector 'w' do not match."
  !is_zero(f) || return f
  jet_w = MPolyBuildCtx(parent(f))
  for (coeff, exp) in coefficients_and_exponents(f)
    if sum(exp .* w) <= k
      push_term!(jet_w, coeff, exp)
    end
  end
  return finish(jet_w)
end

function weighted_k_jet(M::MatElem{<:MPolyRingElem}, k::Integer, w::Vector{<:Integer})
  @req all(>(0), w) "Entries of 'w' must be positive"
  @req ngens(base_ring(M)) == length(w) "Number of variables of the polynomial ring of the entries of 'M' and length of weight vector 'w' do not match."
  jet_w_k(f::MPolyRingElem) = weighted_k_jet(f, k, w)
  return jet_w_k.(M)
end

function is_quasihomogeneous(f::MPolyRingElem, w::Vector{<:Integer})
  @req all(>(0), w) "Entries of 'w' must be positive"
  @req ngens(parent(f)) == length(w) "Number of variables of the polynomial ring of 'f' and length of Weight vector 'w' do not match."
  f != zero(f) || return true
  wdegs = [sum(e .* w) for e in exponents(f)]
  return all(==(wdegs[1]), wdegs)
end

# TODO: Fix it
# function is_quasihomogeneous(M::MatElem{<:MPolyRingElem}, w::Vector{<:Integer})
#   @req all(>(0), w) "Entries of 'w' must be positive"
#   @req ngens(base_ring(M)) == length(w) "Number of variables of the polynomial ring of the entries of 'M' and length of weight vector 'w' do not match."
#   # has_relative_row_and_column_entries(_degree_matrix(M, w)) || return false weighted_initial_order(M[i, j], w)    TODO: find solution
#   for a in M
#     is_quasihomogeneous(a, w) || return false
#   end
#   return true
# end

# function has_relative_row_and_column_entries(D::Matrix{<:Integer})
#   M = copy(D)
#   ones_col = ones(Int64, nrows(D), 1)
#   for j in 2:ncols(D)
#     M[:, j] = (D[1, j] - D[1, 1]) * ones_col + D[:, 1]
#   end
#   return D == M
# end

function is_quasihomogeneous(
  M::MatElem{<:MPolyRingElem}, D::Matrix{<:Integer}, w::Vector{<:Integer}
)
  @req size(M) == size(D) "Size of degree matix 'D' does not match size of 'M'."
  @req all(>(0), D) "Entries of degree matrix 'D' must be positive"
  @req has_relative_row_and_column_entries(D) "Degree matrix 'D' must have relative row and column entries."
  @req all(>(0), w) "Entries of weight vector 'w' must be positive"
  @req ngens(base_ring(M)) == length(w) "Number of variables of the polynomial ring of the entries of 'M' and length of weight vector 'w' do not match."
  D == weighted_initial_degree_matrix(M, w) || return false
  M == weighted_initial_jet(M, w) || return false
  return true
end

function relative_matrix_weight(
  M::MatElem{<:MPolyRingElem}, D::Matrix{<:Integer}, w::Vector{<:Integer}
)
  @req size(M) == size(D) "Size of degree matix 'D' does not match size of 'M'."
  @req all(>(0), D) "Entries of degree matrix 'D' must be positive"
  @req has_relative_row_and_column_entries(D) "Degree matrix 'D' must have relative row and column entries."
  @req all(>(0), w) "Entries of weight vector 'w' must be positive"
  @req ngens(base_ring(M)) == length(w) "Number of variables of the polynomial ring of the entries of 'M' and length of weight vector 'w' do not match."
  v_M = PosInf()
  for pos in eachindex(M)
    tmp = weighted_initial_order(M[pos], w) - D[pos]
    if tmp < v_M
      v_M = tmp
    end
  end
  return v_M
end

function weighted_GL_determinacy(
  M::MatElem{<:MPolyRingElem}, D::Matrix{<:Integer}, w::Vector{<:Integer}
)
  # @req size(M) == size(D) "Size of degree matix 'D' does not match size of 'M'."
  # @req all(>(0), D) "Entries of degree matrix 'D' must be positive"
  # @req has_relative_row_and_column_entries(D) "Degree matrix 'D' must have relative row and column entries."
  # @req all(>(0), w) "Entries of weight vector 'w' must be positive"
  # @req ngens(base_ring(M)) == length(w) "Number of variables of the polynomial ring of the entries of 'M' and length of weight vector 'w' do not match."
  @req is_quasihomogeneous(M, D, w) "Matrix 'M' must be quasihomogeneous w.r.t. (D,w)."
  tjurina_number(M) != PosInf() || return (PosInf(), PosInf())
  B = T1_GL_basis(M)
  !is_empty(B) || return (NegInf(), 0)  #B defines a rigid singularity
  (n, m) = size(M)
  B_mat = [
    matrix(transpose(reshape([B[i][j] for j in 1:(n * m)], m, n))) for i in eachindex(B)
  ]
  h(M) = relative_matrix_weight(M, D, w)
  alpha = maximum(h.(B_mat))
  beta = maximum([0, alpha])
  return (alpha, beta)
end