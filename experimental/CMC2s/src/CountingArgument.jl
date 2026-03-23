export has_relative_row_and_column_entries
export number_of_monomials_of_degree
export pos_var_mon_table
export counting_argument
export can_be_simple

# Added due to its removal by #5416
function Oscar.binomial(a::RingElem, k::Int)
  @req k > 0 "'k' must be positive."
  p = parent(a)
  return prod([a - i for i in 0:(k - 1)]) * inv(p(factorial(k)))
end

function has_relative_row_and_column_entries(D::Matrix{<:Integer})
  M = copy(D)
  ones_col = ones(Int64, nrows(D), 1)
  for j in 2:ncols(D)
    M[:, j] = (D[1, j] - D[1, 1]) * ones_col + D[:, 1]
  end
  return D == M
end

export _count_dict
function _count_dict(v::Union{Vector{<:Integer},Matrix{<:Integer}})
  # display("dict")
  count_dict = Dict{Integer,Integer}()
  for obj in unique(v)
    count_dict[obj] = count(==(obj), v)
  end
  return count_dict
end

function number_of_monomials_of_degree(d::Integer, w::Vector{<:Integer})
  @req all(>(0), w) "Entries of w must be positive"
  return _num_mons_of_deg(d, _count_dict(w))
end

# where {T<: Union{Integer, QQPolyRingElem, QQMPolyRingElem}}
function _num_mons_of_deg(d::Integer, num_vars_of_weight::Dict{<:Integer,<:Any})
  d < 0 && return 0
  d == 0 && return 1
  num_mons_of_deg = 0
  P = partitions(d, sort!(collect(keys(num_vars_of_weight))))
  try #try catch for empty Iterator -- Why error?
    is_empty(P)
  catch
    return 0
  end
  for partition in P
    num_mons_with_deg_partition = 1
    for deg in unique(partition)
      num_vars_to_choose = count(==(deg), partition)
      num_mons_with_deg_partition *= binomial(
        num_vars_of_weight[deg] + num_vars_to_choose - 1, num_vars_to_choose
      )
    end
    num_mons_of_deg += num_mons_with_deg_partition
  end
  return num_mons_of_deg
end

function _calc_pos_vars_mons(
  pos_dict::Dict{<:Integer,<:Any}, var_dict::Dict{<:Integer,<:Any}
)
  d_max = maximum([maximum(keys(pos_dict)), maximum(keys(var_dict))])
  T = Dict{Integer,Dict{Symbol,<:Any}}()
  T[0] = Dict{Symbol,Any}(:pos => 0, :var => 0, :mon => 1)
  for d in 1:d_max
    T[d] = Dict{Symbol,Any}()
    T[d][:pos] = get(pos_dict, d, 0)
    T[d][:var] = get(var_dict, d, 0)
    T[d][:mon] = _num_mons_of_deg(d, var_dict)
  end
  return T
end

function pos_var_mon_table(D::Matrix{<:Integer}, w::Vector{<:Integer})
  return _calc_pos_vars_mons(_count_dict(D), _count_dict(w))
end

function _calc_dim_Q_minus_S_1(T::Dict{Integer,Dict{Symbol,<:Any}})
  return sum([(T[d][:pos] - T[d][:var]) * T[d][:mon] for d in keys(T)])
end

export calc_dim_Q_minus_S_1
function calc_dim_Q_minus_S_1(D::Matrix{<:Integer}, w::Vector{<:Integer})
  return _calc_dim_Q_minus_S_1(pos_var_mon_table(D, w))
end

function _calc_S_1(T::Dict{Integer,Dict{Symbol,<:Any}})
  return sum([T[d][:var] * T[d][:mon] for d in keys(T)])
end

export calc_S_1
function calc_S_1(D::Matrix{<:Integer}, w::Vector{<:Integer})
  return _calc_S_1(pos_var_mon_table(D, w))
end

function _calc_dim_Q(T::Dict{<:Integer,Dict{Symbol,<:Any}})
  return sum([T[d][:pos] * T[d][:mon] for d in keys(T)])
end

export calc_dim_Q
function calc_dim_Q(D::Matrix{<:Integer}, w::Vector{<:Integer})
  return _calc_dim_Q(pos_var_mon_table(D, w))
end

function _S23_helper(T::Dict{<:Integer,Dict{Symbol,<:Any}}, row_dict::Dict{<:Integer,<:Any})
  S_23 = 0
  weights = sort!(collect(keys(row_dict)))
  for i in eachindex(weights)
    for j in i:lastindex(weights)
      S_23 +=
        T[(weights[j] - weights[i])][:mon] * row_dict[weights[i]] * row_dict[weights[j]]
    end
  end
  return S_23
end

export calc_S_2
function calc_S_2(D::Matrix{<:Integer}, w::Vector{<:Integer})
  return _S23_helper(pos_var_mon_table(D, w), _count_dict(D[:, 1]))
end

export calc_S_3
function calc_S_3(D::Matrix{<:Integer}, w::Vector{<:Integer})
  return _S23_helper(pos_var_mon_table(D, w), _count_dict(D[1, :]))
end

function _counting_argument(
  T::Dict{<:Integer,Dict{Symbol,<:Any}},
  row_dict::Dict{<:Integer,<:Any},
  column_dict::Dict{<:Integer,<:Any},
  r=2::Integer,
)
  @req r >= 2 "Number of independent relations r is at least 2"
  return _calc_dim_Q_minus_S_1(T) - _S23_helper(T, row_dict) - _S23_helper(T, column_dict) +
         r
end

function counting_argument(D::Matrix{<:Integer}, w::Vector{<:Integer}, r=2::Integer)
  @req all(>(0), D) "Entries of D must be positive"
  @req all(>(0), w) "Entries of w must be positive"
  has_relative_row_and_column_entries(D) ||
    error("Degree matrix D must have relative row and column degrees")
  # @req r >= 2 "Number of independent relations r is at least 2"
  return _counting_argument(
    pos_var_mon_table(D, w), _count_dict(D[:, 1]), _count_dict(D[1, :]), r
  )
end

function can_be_simple(D::Matrix{<:Integer}, w::Vector{<:Integer}, r=2::Integer)
  return counting_argument(D, w, r) <= 0
end

# LaTeX print functions
# function _matrix_calc_pos_vars_mons(
#   pos_dict::Dict{<:Integer,QQMPolyRingElem}, var_dict::Dict{<:Integer,QQMPolyRingElem}
# )
#   dict = _calc_pos_vars_mons(pos_dict, var_dict)
#   d_max = maximum(keys(dict))
#   M = Array{QQMPolyRingElem}(undef, d_max + 1, 4)
#   for d in 1:(d_max + 1)
#     M[d, 1] = d + 1
#     M[d, 2] = dict[d - 1][:pos]
#     M[d, 3] = dict[d - 1][:var]
#     M[d, 4] = dict[d - 1][:mon]
#   end
#   return M
# end

export _matrix_calc_pos_vars_mons
function _matrix_calc_pos_vars_mons(D::Matrix{<:Integer}, w::Vector{<:Integer})
  dict = pos_var_mon_table(D, w)
  d_max = maximum(keys(dict))
  M = zero_matrix(ZZ, d_max + 1, 4)
  for d in 1:(d_max + 1)
    M[d, 1] = d - 1
    M[d, 2] = dict[d - 1][:pos]
    M[d, 3] = dict[d - 1][:var]
    M[d, 4] = dict[d - 1][:mon]
  end
  show(stdout, "text/latex", M)
  return M
end