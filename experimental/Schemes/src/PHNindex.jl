export T1_GL_sheaf, has_only_determinantal_rigid_singularities, global_PHN_index, local_PHN_index, components, count_origin_roots,local_PHN_index_at_the_origin

#TODO temporary export, remove it later

export _modulus_T1_Gl, converted_modulus_T1_Gl, T1_Gl_module, tjurina_Gl_number, T1_Gl_basis, T1_Gl_sheaf, has_only_rigid_singularities
export global_PHN_index, local_PHN_multiplicity, components, count_origin_roots,local_PHN_index_at_the_origin, converted_modulus_T1_Gl, PHN_index,local_PHN_index

#TODO temporary export, remove it later

function _S_2(A::MatElem)
  n_rows = number_of_rows(A)
  return [_R_ij(A, i, j) for i in 1:n_rows for j in 1:n_rows]
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
  return quo(F, S)[1]
end

T1_GL_sheaf(X::DeterminantalGerm) = pre_saturated_module(T1_GL_module(X))

has_only_determinantally_rigid_singularities(X::DeterminantalGerm) = is_zero(T1_GL_sheaf(X))

function has_only_rigid_singularities(M::MatElem{<:MPolyRingElem})
  return vector_space_dim(T1_Gl_sheaf(M)) == 0
end



function _PHN_locus(X::DeterminantalGerm, f::MPolyRingElem)
  OO_repr = underlying_quotient(OO(X))
  R = base_ring(OO_repr)
  @assert R === parent(f)
  n, m, t = determinantal_type(X) 
  I_X = modulus(OO_repr)
  J_total = jacobian_matrix(vcat(gens(I_X), f))
  polys_crit = minors(J_total, codim(X) + 1)
  I = I_X + ideal(R, polys_crit)
  return quo(R, I)[1]
end


 function global_PHN_index(X::DeterminantalGerm, f::MPolyRingElem)
   return vector_space_dim(_PHN_locus(X, f))
 end

function local_PHN_multiplicity(
     X::DeterminantalGerm{<:BRT, <:RT, <:AST}, f::MPolyRingElem, p::Vector
  ) where {BRT<:Field, RT, AST}
   Q = _PHN_locus(X, f)
   LQ_p, _ = localization(Q, complement_of_point_ideal(base_ring(Q), p))
   return vector_space_dim(LQ_p)
 end

 function PHN_index(
    X::DeterminantalGerm{<:BRT, <:RT, <:AST}, 
    f::MPolyRingElem, 
    p::Vector
) where {BRT<:Field, RT, AST}

    idx_global = global_PHN_index(X, f)
    
    # Extração do representante e do lugar singular nativo
    Xrep = representative(X)
    Xrep_sing, _ = singular_locus(Xrep)
    dim_sing = vector_space_dim(OO(Xrep_sing))
    
    idx_local = local_PHN_multiplicity(X, f, p)
    
    return idx_global - (dim_sing * idx_local)
end


function _PHN_primary_decomposition(X::DeterminantalGerm, f::MPolyRingElem)
    return primary_decomposition(modulus(_PHN_locus(X, f)))
end

"""
    components(X::DeterminantalGerm, f::MPolyRingElem)

Prints information about the primary components of the PHN locus.
This function is intended for side effects (printing) and does not return a value.
"""
function components(X::DeterminantalGerm, f::MPolyRingElem)
    pd = _PHN_primary_decomposition(X, f)
    for (i, (q, p)) in enumerate(pd)
        println("\n--- Component $i with multiplicity $(degree(q)) ---")
        
         #'p' is the prime ideal where the point is 
         #'q' is the primary ideal giving the multiplicity of that point 
        println("Coordinates:")
        for gerador in gens(p)
           println("  ", gerador, " = 0")
        end
    end
end


function _PHN_critical_roots(X::DeterminantalGerm, f::MPolyRingElem)
    pd = _PHN_primary_decomposition(X, f)
    
    C = AcbField(512)
    all_roots = elem_type(C)[] 
    
    R = parent(f)
    n = nvars(R)
    R_uni, T = polynomial_ring(QQ, :T, cached=false)
    
    # Construção do ideal singular
    anel_base = base_ring(underlying_quotient(OO(X)))
    I_X = modulus(underlying_quotient(OO(X)))
    J_X = jacobian_matrix(gens(I_X))
    I_sing = I_X + ideal(anel_base, minors(J_X, codim(X)))
    
    for (q, p) in pd
        # Filtro Algébrico: Destrói a componente se ela for a singularidade
        I_teste = saturation(p, I_sing)
        anel_comp = quo(R, I_teste)[1]
        
        if vector_space_dim(anel_comp) == 0
            continue
        end
        
        # Lógica de extração de coordenadas originais preservada
        geradores = gens(p)
        poly_mult = geradores[1]
        
        vetor_subst = fill(R_uni(0), n)
        vetor_subst[n] = T
        
        poly_uni = evaluate(poly_mult, vetor_subst)
        poly_C = change_base_ring(C, poly_uni)
        
        append!(all_roots, roots(poly_C))
    end
    
    return all_roots
end






function count_origin_roots(X::DeterminantalGerm, f::MPolyRingElem, epsilon::Real = 1e-4, origin_tol::Real = 1e-30)
    # Agora a contagem chama a função passando o germe e a função diretamente
    root_list = _PHN_critical_roots(X, f)
    total_roots = length(root_list)
    points_close_to_origin = 0
    
    println("global_PHN_index: ", total_roots)
    
    for (i, value_root) in enumerate(root_list)
        distance = abs(value_root)
        dist_float = Float64(distance)
        
        # Filtra: Menor que epsilon (local) MAS maior que origin_tol (não é a singularidade base)
        if dist_float < epsilon && dist_float > origin_tol
            points_close_to_origin += 1
            println("Root $i: critical point of f (Module = $distance)")
            
        # Captura o caso em que a raiz é a própria singularidade da variedade
        elseif dist_float <= origin_tol
            println("Root $i: REJECTED (Singularity of the variety detected at $distance)")
            
        # Raízes globais distantes
        else
            println("Root $i: not close to the origin (Module = $distance)")
        end
    end
    
    println("local_PHN_index: ", points_close_to_origin) 
end



function local_PHN_index(X::DeterminantalGerm, f::MPolyRingElem, epsilon::Real = 1e-4)
    # Recebe as coordenadas complexas (AcbFieldElem)
    raizes = _PHN_critical_roots(X, f)
    
    indice_local = 0
    
    for raiz in raizes
        # 1. Extrai o módulo geométrico da raiz (transforma o complexo em real)
        distancia_real = abs(raiz)
        
        # 2. Agora a conversão para Float64 funciona perfeitamente
        if Float64(distancia_real) < epsilon
            indice_local += 1
        end
    end
    
    return indice_local
end

