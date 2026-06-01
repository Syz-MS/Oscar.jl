export T1_GL_sheaf, has_only_determinantal_rigid_singularities, global_PHN_index, local_PHN_index, components, count_origin_roots,local_PHN_index_at_the_origin

#TODO temporary export, remove it later

function T1_GL_sheaf(M::MatElem{<:MPolyRingElem})
  S = converted_modulus_T1_Gl(M)
  F = ambient_free_module(S)
  return quo(F, S)[1]
end
T1_GL_sheaf(X::DeterminantalGerm) = pre_saturated_module(T1_GL_module(X))

has_only_determinantally_rigid_singularities(X::DeterminantalGerm) = is_zero(T1_GL_sheaf(X))
function has_only_determinantally_rigid_singularities(M::MatElem{<:MPolyRingElem})
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

 function local_PHN_index(
     X::DeterminantalGerm{<:BRT, <:RT, <:AST}, point::Array{<:BRT}
   ) where {BRT, RT, AST}
   Q = _PHN_locus(X, f)
   LQ_p, _ = localization(Q, complement_of_point_ideal(base_ring(Q), point))
   return vector_space_dim(LQ_p)
 end


function _PHN_primary_decomposition(X::DeterminantalGerm, f::MPolyRingElem)
    return primary_decomposition(modulus(_PHN_locus(X, f)))
end

function components(X::DeterminantalGerm, f::MPolyRingElem)
    pd = _PHN_primary_decomposition(X, f)
    for (i, (q, p)) in enumerate(pd)
        println("\n--- Component $i with multiplicity ", degree(q), " ---")
        
        
        
        # 'p' is the prime ideal where the point is 
        # 'q' is the primary ideal giving the multiplicity of that point 
       # println("Coordinates:")
        #for gerador in gens(p)
         #   println("  ", gerador, " = 0")
        #end
    end
end


function _PHN_critical_roots(X::DeterminantalGerm, f::MPolyRingElem)
    pd = _PHN_primary_decomposition(X, f)
    
    # Prepara o corpo complexo e uma lista vazia segura para guardar as raízes
    C = AcbField(512)
    all_roots = elem_type(C)[] 
    
    # Define a variável T fora do laço para não recriá-la à toa
    R_uni, T = polynomial_ring(QQ, :T, cached=false)
    
    for (q, p) in pd
        geradores = gens(p)
        poly_mult = geradores[1]
        n = nvars(parent(poly_mult))
        
        vetor_subst = fill(R_uni(0), n)
        vetor_subst[n] = T
        
        poly_uni = evaluate(poly_mult, vetor_subst)
        poly_C = change_base_ring(C, poly_uni)
        
        # Extrai as raízes desta componente e anexa à lista geral
        append!(all_roots, roots(poly_C))
    end
    
    return all_roots
end

function count_origin_roots(X::DeterminantalGerm, f::MPolyRingElem, epsilon::Real = 1e-4)
    # Agora a contagem chama a função passando o germe e a função diretamente
    root_list = _PHN_critical_roots(X, f)
    total_roots = length(root_list)
    points_close_to_origin = 0
    
    println("global_PHN_index: ", total_roots)
    
    for (i, value_root) in enumerate(root_list)
        distance = abs(value_root)
        
        # Converte a distância para comparar com o raio
        if Float64(distance) < epsilon
            points_close_to_origin += 1
            println("Root $i: close to the origin (Module = $distance)")
        else
            println("Root $i: not close to the origin (Module = $distance)")
        end
    end
    
    println("local_PHN_index: ", points_close_to_origin) 
end

function local_PHN_index_at_the_origin(X::DeterminantalGerm, f::MPolyRingElem, epsilon::Real = 1e-4)
    root_list = _PHN_critical_roots(X, f)
    points_close_to_origin = 0
    
    for value_root in root_list
        distance = abs(value_root)
        
        # Converte a distância para comparar com o raio
        if Float64(distance) < epsilon
            points_close_to_origin += 1
        end
    end
    
    return points_close_to_origin
end

