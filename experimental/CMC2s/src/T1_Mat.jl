export _modulus_T1_Gl
export converted_modulus_T1_Gl
export T1_Gl_module
export tjurina_Gl_number
export T1_Gl_basis
export T1_Gl_sheaf
export has_only_rigid_singularities
export non_rigid_locus

function _R_ij(A::MatElem, i::Integer, j::Integer)
  R_ij = zero(A)
  R_ij[i, :] = A[j, :]
  return R_ij
end

function _S_2(A::MatElem)
  n_rows = number_of_rows(A)
  return [_R_ij(A, i, j) for i in 1:n_rows for j in 1:n_rows]
end

function _C_ij(A::MatElem, i::Integer, j::Integer)
  C_ij = zero(A)
  C_ij[:, i] = A[:, j]
  return C_ij
end

function _S_3(A::MatElem)
  n_cols = number_of_columns(A)
  return [_C_ij(A, i, j) for i in 1:n_cols for j in 1:n_cols]
end

function _J(A::MatElem{<:MPolyRingElem})
  return [derivative.(A, i) for i in 1:ngens(parent(A[1, 1]))]
end

function _modulus_T1_Gl(M::MatElem{<:MPolyRingElem})
  return vcat(_J(M), _S_2(M), _S_3(M))
end

function converted_modulus_T1_Gl(M::MatElem{<:MPolyRingElem})
  L = base_ring(parent(M))
  F = free_module(L, number_of_rows(M) * number_of_columns(M))
  # transpose is important for rowwise linear index of vev
  mod_T1_Gl = _modulus_T1_Gl(transpose(M))
  S, _ = sub(F, F.(vec.(Array.(mod_T1_Gl))))
  return S
end

function T1_Gl_module(M::MatElem{<:MPolyRingElem}, reorder=false)
  S = converted_modulus_T1_Gl(M)
  F = ambient_free_module(S)
  if reorder
    k = ngens(F)
    F_gens = gens(F)
    reordered_gens = vcat(
      [F_gens[k - 1]], [F_gens[j] for j in 2:(k - 2)], [F_gens[1], F_gens[k]]
    )
    sigma = hom(F, F, reordered_gens)
    S_gens = ambient_representatives_generators(S)
    S_gens_reordered = sigma.(S_gens)
    S, _ = sub(F, S_gens_reordered)
  end
  LS = leading_module(S, invlex(F) * negdeglex(base_ring(F)))
  T1_Gl, _ = quo(F, LS)
  return T1_Gl
end

# S = converted_modulus_T1_Gl(M)
# F = ambient_free_module(S)
# LS_reordered = leading_module(S_reordered, invlex(F) * negdeglex(base_ring(F)))
# T1_Gl, _ = quo(F, LS_reordered)

function tjurina_Gl_number(M::MatElem{<:MPolyRingElem}, reorder=false)
  tau = vector_space_dim(T1_Gl_module(M, reorder))
  return tau == -1 ? PosInf() : tau
end

function T1_Gl_basis(M::MatElem{<:MPolyRingElem}, reorder=false)
  return vector_space_basis(T1_Gl_module(M, reorder))
end
#  ord = invlex(ambient_free_module(S))*negdeglex(base_ring(S))

# matrix(transpose(reshape([S[i] for i in 1:6], 3,2)))



function T1_Gl_sheaf(M::MatElem{<:MPolyRingElem})
  S = converted_modulus_T1_Gl(M)
  F = ambient_free_module(S)
  T1_Gl_sheaf, _ = quo(F, S)
  return T1_Gl_sheaf
end

function has_only_rigid_singularities(M::MatElem{<:MPolyRingElem})
  return vector_space_dim(T1_Gl_sheaf(M)) == 0
end


function non_rigid_locus(M::MatElem{<:MPolyRingElem}, t::Integer)       #Integer t necessary?
  T1_Gl = T1_Gl_sheaf(M)
  Ann_T1_Gl = annihilator(T1_Gl)  #TODO: add radical????? to be able to count points??
  return AffineScheme(quo(base_ring(Ann_T1_Gl), ideal(minors(M,t)) + Ann_T1_Gl)[1])
end