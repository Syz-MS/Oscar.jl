## literature:
##        Greuel, Lossen, Shustin: 'Introduction to Singularities and Deformations'

##    for positive characteristic the following papers
##        Greuel, Pham: 'Mather-Yau Theorem in Positive Characteristic'
##        Boubakri, Greuel, Markwig: 'Invariants of Hypersurface Singularities in Positive Characteristic'


################################################################################

#####                           Tjurina algebra                            #####

################################################################################

@doc raw"""
    tjurina_algebra(f::MPolyRingElem)

Return the global Tjurina algebra of the affine hypersurface `V(f)`.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> f = x^3 - y^2;

julia> tjurina_algebra(f)
Quotient
  of multivariate polynomial ring in 2 variables x, y
    over rational field
  by ideal (x^3 - y^2, 3*x^2, -2*y)
```
"""
function tjurina_algebra(f::MPolyRingElem)
  R = parent(f)
  return MPolyQuoRing(R, ideal(R, f) + jacobian_ideal(f))
end



@doc raw"""
    tjurina_algebra(X::AffineScheme{<:Field,<:MPolyQuoRing})

Return the global Tjurina algebra of the affine scheme `X`, if `X` is a hypersurface.
Throws an error otherwise.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> X = AffineScheme(quo(R, ideal(R, x^3-y^2))[1])
Spectrum
  of quotient
    of multivariate polynomial ring in 2 variables x, y
      over rational field
    by ideal (x^3 - y^2)

julia> tjurina_algebra(X)
Quotient
  of multivariate polynomial ring in 2 variables x, y
    over rational field
  by ideal (x^3 - y^2, 3*x^2, -2*y)
```
"""
function tjurina_algebra(X::AffineScheme{<:Field,<:MPolyQuoRing})
  ngens(modulus(OO(X))) == 1 || error("not a hypersurface (or unnecessary generators in specified generating set)")
  return tjurina_algebra(gen(modulus(OO(X)),1))
end



@doc raw"""
    tjurina_algebra(X::HypersurfaceGerm, k::Integer = 0)

Return the `k`-th local Tjurina algebra of `(X,p)` at `p`. 
By default computes the local Tjurina algebra (`k=0`) at `p`.
Higher Tjurina algebras are of interest in positive characteristic.
!!! note
    For better readability and for saving memory the Tjurina algebra of the corresponding HypersurfaceGerm shifted to the origin '0' is actually computed and returned.

# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> f = x^3-y^2;

julia> X = HypersurfaceGerm(AffineScheme(quo(R, ideal(R, f))[1]), [0, 0]);

julia> tjurina_algebra(X)
Localization
  of quotient
    of multivariate polynomial ring in 2 variables x, y
      over rational field
    by ideal (x^3 - y^2, 3*x^2, -2*y)
  at complement of maximal ideal of point (0, 0)
```
"""
function tjurina_algebra(X::HypersurfaceGerm, k::Integer = 0)  
  k >= 0 || error("Integer must be non-negative.")
  R = localized_ring(OO(X))
  ## tjurina algebra independent of choice of representative
  ## hence choose a polynomial representative for easier computation
  f_poly = numerator(defining_ideal(X)[1])
  m = ideal(R, gens(R)-point(X))
  I = ideal(R, f_poly) + m^k*ideal(R, R.([derivative(f_poly, i) for i=1:nvars(base_ring(R))]))
  return quo(R,I)[1]
end



@doc raw"""
    tjurina_algebra(f::MPolyLocRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}, k::Integer = 0)

Return the `k`-th local Tjurina algebra of `(V(f),p)` at `p`. 
By default computes the local Tjurina algebra (`k=0`) at `p`.
Higher Tjurina algebras are of interest in positive characteristic.
# Examples
```jldoctest
julia> R,(x,y) = GF(2)[:x, :y];

julia> L,_  = localization(R, complement_of_point_ideal(R, [0, 0]));

julia> tjurina_algebra(L(x^3-y^2))
Localization
  of quotient
    of multivariate polynomial ring in 2 variables x, y
      over prime field of characteristic 2
    by ideal (x^3 + y^2, x^2, 0)
  at complement of maximal ideal of point (0, 0)

julia> tjurina_algebra(L(x^3-y^2), 1)
Localization
  of quotient
    of multivariate polynomial ring in 2 variables x, y
      over prime field of characteristic 2
    by ideal (x^3 + y^2, x^3, 0, x^2*y, 0)
  at complement of maximal ideal of point (0, 0)
```
"""
function tjurina_algebra(f::MPolyLocRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}, k::Integer = 0)
  X = HypersurfaceGerm(quo(parent(f), ideal(parent(f), f))[1])
  return tjurina_algebra(X, k)
end



###############################################################################

#####                           Tjurina number                            #####

###############################################################################

@doc raw"""
    tjurina_number(f::MPolyRingElem)

Return the global Tjurina number of a polynomial `f`.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> f = x*(x-1)*y;

julia> tjurina_number(f)
2
```
"""
function tjurina_number(f::MPolyRingElem)
  isa(coefficient_ring(f), AbstractAlgebra.Field) || error("The polynomial requires a coefficient ring that is a field.")
  R = tjurina_algebra(f)
  return dim(modulus(R)) <= 0 ? vector_space_dim(R) : PosInf()
end

@doc raw"""
    tjurina_number(X::AffineScheme{<:Field,<:MPolyQuoRing})

Return the global Tjurina number of the affine scheme `X`, if `X` is a hypersurface.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> f = x^3 - y^2;

julia> X = AffineScheme(quo(R, ideal(R, x^3-y^2))[1])
Spectrum
  of quotient
    of multivariate polynomial ring in 2 variables x, y
      over rational field
    by ideal (x^3 - y^2)

julia> tjurina_number(X)
2
```
"""
function tjurina_number(X::AffineScheme{<:Field,<:MPolyQuoRing}) 
  R = tjurina_algebra(X)
  return dim(modulus(R)) <= 0 ? vector_space_dim(R) : PosInf()
end



@doc raw"""
    tjurina_number(X::HypersurfaceGerm, k::Integer = 0)

Return the `k`-th local Tjurina number of `(X,p)` at `p`. 
By default computes the local Tjurina number (`k=0`) at `p`.
Higher Tjurina numbers are of interest in positive characteristic.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> f = x^3 - y^2;

julia> X = HypersurfaceGerm(AffineScheme(quo(R, ideal(R, f))[1]), [0, 0]);

julia> tjurina_number(X)
2
```
"""
function tjurina_number(X::HypersurfaceGerm, k::Integer = 0)                                    
  # Fix for infinite dimensional vector space
  R = tjurina_algebra(X, k)
  return dim(modulus(R)) <= 0 ? vector_space_dim(R) : PosInf()
end



@doc raw"""
    tjurina_number(f::MPolyLocRingElem{<:Field, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}, k::Integer = 0)

Return the `k`-th local Tjurina number of `(V(f),p)` at `p`. 
By default computes the local Tjurina number (`k=0`) at `p`.
Higher Tjurina numbers are of interest in positive characteristic. 
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> L,_  = localization(R, complement_of_point_ideal(R, [0, 0]));

julia> f = L(x*y*(x-1));

julia> tjurina_number(f)
1
```
"""
function tjurina_number(f::MPolyLocRingElem{<:Field, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}, k::Integer = 0)
  X = HypersurfaceGerm(quo(parent(f), ideal(parent(f), [f]))[1])
  return tjurina_number(X, k)
end



################################################################################

#####                                 Order                                #####

################################################################################

function _order(f::MPolyRingElem)
  !is_zero(f) || return PosInf()
  n = nvars(parent(f))
  return minimum(sum(e) for e in AbstractAlgebra.exponent_vectors(f))
end

@doc raw"""
    order_as_series(f::MPolyLocRingElem{<:Field, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal})

Return the order of the series expansion of an element of a local ring at the localized point.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> L0,_  = localization(R, complement_of_point_ideal(R, [0, 0]));

julia> L1,_  = localization(R, complement_of_point_ideal(R, [1, 0]));

julia> f = (x-1)^3
x^3 - 3*x^2 + 3*x - 1

julia> order_as_series(L0(f))
0

julia> order_as_series(L1(f))
3
```
"""
function order_as_series(f::MPolyLocRingElem{<:Field, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal})                       
  shift,_ = base_ring_shifts(parent(f))
  return _order(shift(numerator(f)))           
end



###############################################################################

#####                         Finite determinacy                          #####

###############################################################################
@doc raw"""
    is_finitely_determined(f::MPolyLocRingElem{<:Field, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}, equivalence::Symbol = :contact)

Return if 'f' is finitely determined with respect to ':right' or ':contact' equivalence.
By default computes with respect to contact equivalence.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> L,_  = localization(R, complement_of_point_ideal(R, [0, 0]));

julia> is_finitely_determined(L(x^3-y^2))
true

julia> is_finitely_determined(L(x^3-y^2), :right)
true
```
"""
function is_finitely_determined(f::MPolyLocRingElem{<:Field, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}, equivalence::Symbol = :contact)
  equivalence == :right || equivalence == :contact || error("Equivalence typ must be ':right' or ':contact'.")
  !iszero(f) || return false
  ord_f = order_as_series(f)
  ## smooth case, 1-determined
  ord_f != 1 || return true 
  if equivalence == :right
    if ord_f == 0   
      ## A unit has the same right-determinacy as the power series without the constant term.
      ## Therefore remove constant term.
      R = base_ring(parent(f))
      shift,_ = base_ring_shifts(parent(f))
      a = shift(numerator(f))  
      b = shift(denominator(f))    
      L,_ = localization(R, complement_of_point_ideal(R, [coefficient_ring(R)(0) for i = 1:ngens(R)]))
      f_shifted = L(a//b) 
      f_new = f_shifted-(constant_coefficient(a)//constant_coefficient(b))
      return is_finitely_determined(f_new, equivalence)
    end
    X = HypersurfaceGerm(quo(parent(f), ideal(parent(f), f))[1])
    return dim(modulus(milnor_algebra(X))) <= 0 ? true : false
  else  ## equivalence == :contact
    return tjurina_number(f) != PosInf()
  end
end



@doc raw"""
    is_finitely_determined(X::HypersurfaceGerm, equivalence::Symbol = :contact)

Return if the hypersurface germ 'X' is finitely determined with respect to ':right' or ':contact' equivalence. 
By default computes with respect to contact equivalence.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> f = x^2 - y^2;

julia> X = HypersurfaceGerm(AffineScheme(quo(R, ideal(R, f))[1]), [0, 0]);

julia> is_finitely_determined(X)
true

julia> is_finitely_determined(X, :right)
true
```
"""
function is_finitely_determined(X::HypersurfaceGerm, equivalence::Symbol = :contact)
  f = defining_ideal(X)[1]
  return is_finitely_determined(f, equivalence)
end



###############################################################################
@doc raw"""
    determinacy_bound(f::MPolyLocRingElem, equivalence::Symbol = :contact)

Compute some determinacy bound of 'f' with respect to ':right' or ':contact' equivalence.
Return infinity if not finitely determined. 
By default computes with respect to contact equivalence.
This computation is based on the Milnor number respectively Tjurina number.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> L,_  = localization(R, complement_of_point_ideal(R, [0, 0]));

julia> f = L(x^3 - y^2);

julia> determinacy_bound(f)
3

julia> determinacy_bound(f, :right)
3
```
"""
function determinacy_bound(f::MPolyLocRingElem, equivalence::Symbol = :contact)
  equivalence == :right || equivalence == :contact || error("Equivalence typ must be ':right' or ':contact'.")
  ord_f = order_as_series(f)
  ## if the order of f is 1, then f is right and contact equivalent to its 1-jet (smooth case)
  ord_f != 1 || return 1
  is_finitely_determined(f, equivalence) || return PosInf()
  if equivalence == :right
    if ord_f == 0     
      ## A unit has the same right-determinacy as the power series without the constant term.
      ## Therefore remove constant term.
      R = base_ring(parent(f))
      shift,_ = base_ring_shifts(parent(f))
      a = shift(numerator(f))
      b = shift(denominator(f)) 
      L,_ = localization(R, complement_of_point_ideal(R, [coefficient_ring(R)(0) for i = 1:ngens(R)]))
      f_shifted = L(a//b) 
      f_new = f_shifted-(constant_coefficient(a)//constant_coefficient(b))
      return determinacy_bound(f_new, equivalence)
    end
    X = HypersurfaceGerm(quo(parent(f), ideal(parent(f), f))[1])
    k = milnor_number(X)
  else  ## equivalence == :contact
    ord_f != 0 || return 0
    k = tjurina_number(f)
  end
  return characteristic(parent(f)) == 0 ? k + 1 : 2*k - ord_f + 2
end



@doc raw"""
    determinacy_bound(X::HypersurfaceGerm, equivalence::Symbol = :contact)

Compute some determinacy bound of the hypersurface germ 'X' with respect to ':right' or ':contact' equivalence.
Return infinity if not finitely determined. 
By default computes with respect to contact equivalence.
This computation is based on the Milnor number respectively Tjurina number.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> f = x^5 + y^5 + x^2*y^2;

julia> X = HypersurfaceGerm(AffineScheme(quo(R, ideal(R, f))[1]), [0, 0]);

julia> determinacy_bound(X)
11

julia> determinacy_bound(X, :right)
12
```
"""
function determinacy_bound(X::HypersurfaceGerm, equivalence::Symbol = :contact)
  f = defining_ideal(X)[1]
  return determinacy_bound(f, equivalence)
end



@doc raw"""
    sharper_determinacy_bound(f::MPolyLocRingElem, equivalence::Symbol = :contact)

Compute some determinacy bound of 'f' with respect to ':right' or ':contact' equivalence.
Return infinity if not finitely determined. 
By default computes with respect to contact equivalence.
At the cost of a higher computation time this function computes in general 
some sharper determinacy bound than the function determinacy_bound. 
In characteristic 0 the computed bound is the determinacy or the determinacy plus one.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> L,_  = localization(R, complement_of_point_ideal(R, [0, 0]));

julia> f = L(x^3+y^6);

julia> determinacy_bound(f, :right)
11

julia> sharper_determinacy_bound(f, :right)
6
```
"""
function sharper_determinacy_bound(f::MPolyLocRingElem, equivalence::Symbol = :contact)
  equivalence == :right || equivalence == :contact || error("Equivalence typ must be ':right' or ':contact'.")
  ord_f = order_as_series(f)
  ## if the order of f is 1, then f is right and contact equivalent to its 1-jet (smooth case)
  ord_f != 1 || return 1  
  is_finitely_determined(f::MPolyLocRingElem, equivalence) ||  return PosInf()
  R = base_ring(parent(f))
  m = ideal(gens(R))
  ## shift to 0 for computation w.r.t. local order  
  shift,_ = base_ring_shifts(parent(f))
  a = shift(numerator(f))  
  b = shift(denominator(f)) 
  if equivalence == :right
    if ord_f == 0     
      ## A unit has the same right-determinacy as the power series without the constant term.
      ## Therefore remove constant term. 
      L,_ = localization(R, complement_of_point_ideal(R, [coefficient_ring(R)(0) for i = 1:ngens(R)]))
      f_shifted = L(a//b) 
      f_new = f_shifted-(constant_coefficient(a)//constant_coefficient(b))
      return sharper_determinacy_bound(f_new, equivalence)
    end
    J = ideal(R,[derivative(a, R[i])*b - a*derivative(b, R[i]) for i in 1:nvars(R)])
    I = m^2*J
  else  ## equivalence == :contact
    ord_f != 0 || return 0
    I = m*a + m^2*jacobian_ideal(a)
  end
  G = standard_basis(I, ordering = negdeglex(parent(a)))
  h = Singular.highcorner(G.gensBiPolyArray.S)   # TODO: should this use singular_generators(G)?
  l = total_degree(R(h))  
  ## m^(l+1) \subseteq I  
  ## char. 0: l
  ## pos. char.: 2*(l-1) - order_as_series(f) + 2
  return characteristic(R) == 0 ? l : 2*l - order_as_series(f)
end



@doc raw"""
    sharper_determinacy_bound(X::HypersurfaceGerm, equivalence::Symbol = :contact)

Compute some determinacy bound of the hypersurface germ 'X' with respect to ':right' or ':contact' equivalence.
Return infinity if not finitely determined. 
By default computes with respect to contact equivalence.
At the cost of a higher computation time this function computes in general 
some sharper determinacy bound than the function determinacy_bound. 
In characteristic 0 the computed bound is the determinacy or the determinacy plus one.
# Examples
```jldoctest
julia> R,(x,y) = QQ[:x, :y];

julia> f = x^5 + y^5;

julia> X = HypersurfaceGerm(AffineScheme(quo(R, ideal(R, f))[1]), [0, 0]);

julia> determinacy_bound(X)
17

julia> sharper_determinacy_bound(X)
6
```
"""
function sharper_determinacy_bound(X::HypersurfaceGerm, equivalence::Symbol = :contact)
  f = defining_ideal(X)[1]
  return sharper_determinacy_bound(f, equivalence)
end


#################################################################################

#####                         Contact Equivalence                           #####           

#################################################################################
# Currently for internal use only
function _is_isomorphic_as_K_algebra(A::MPolyQuoLocRing{<:Field, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal},
                                      B::MPolyQuoLocRing{<:Field, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}
) 
  R = base_ring(A)
  R == base_ring(B) || error("A and B must have the same base ring")  
  ## shift to origin   
  L,_ = localization(R, complement_of_point_ideal(R, [coefficient_ring(R)(0) for i = 1:ngens(R)]))  
  A,_ = quo(L, L(shifted_ideal(modulus(A))))
  B,_ = quo(L, L(shifted_ideal(modulus(B))))   
  ## check id isomorphism
  modulus(underlying_quotient(A)) != modulus(underlying_quotient(B)) || return true
  ## basic dimension checks
  d = dim(modulus(A))
  d == dim(modulus(B)) || return false
  if d <= 0
    n = vector_space_dim(A)
    n == vector_space_dim(B) || return false
    n != 0 || return true
    n != 1 || return true
  else
    n = PosInf()
  end     
  ## calculate bases and check if A and B have the same vector_space_dim modulo m^k
  k = 1
  mA = ideal(A, gens(A))
  mB = ideal(B, gens(B))
  mA_basis = minimal_generating_set(mA)
  mB_basis = minimal_generating_set(mB)
  length(mA_basis) == length(mB_basis) || return false
    ## edim(A) == 1 
  length(mA_basis) != 1 || return true
  ## can't do more for infinite dimensional vectorspaces
  n != PosInf() || error("infinite dimensional vectorspaces") 
  ## Save minimalngens of m^k during calculation
  ngens_m_k = [length(mA_basis)]  
  while length(mA_basis) != n-1
    k += 1
    gens_mA_k = minimal_generating_set(mA^k)
    push!(ngens_m_k, length(gens_mA_k))
    append!(mA_basis, gens_mA_k)
    append!(mB_basis, minimal_generating_set(mB^k))
    length(mA_basis) == length(mB_basis) || return false
  end
  ## lift bases
  mA_basis = lifted_numerator.(mA_basis)
  mB_basis = lifted_numerator.(mB_basis)
  ## check if isomorphism exists
  S, t = polynomial_ring(coefficient_ring(R), ngens_m_k[1]*length(mB_basis), :t)
  P, iota = change_base_ring(S, R)    
  I_A = shifted_ideal(ideal(L, minimal_generating_set(modulus(A)))) 
  I_B = ideal(standard_basis(shifted_ideal(modulus(B)), ordering = negdeglex(R))) 
  ## construct homomorphism with parameters
  phi = elem_type(P)[]  
  for i in 0:ngens_m_k[1]-1
    img = P()
    for j in 1:length(mB_basis)
      img += t[(i*length(mB_basis)+j)]*iota(mB_basis[j])
    end
    phi = push!(phi, img)
  end 
  ## calculate det of transformation matrix by using its block structure
  detM = S(1)
  l = 0  
  for k in 1:length(ngens_m_k)
    start = l+1
    stop = l+ngens_m_k[k]    
    N = matrix_ring(S, ngens_m_k[k])()
    for j in start:stop
      h = normal_form(evaluate(mA_basis[j], phi), iota(I_B), ordering = negdeglex(P))
      for i in start:stop
        N[i-l,j-l] = coeff(h, iota(mB_basis[i]))
      end
    end
    detM *= det(N)
    l = stop
  end
  ## calculate requirements for parameters, so that phi(I_A) \subseteq I_B 
  I = elem_type(S)[]
  for f in gens(I_A)
    h = normal_form(evaluate(f, phi), iota(I_B), ordering = negdeglex(P))
    for c in coefficients(h, ordering=negdeglex(P))
      I = push!(I, c)
    end
  end
  ## check if det(M) \neq 0 possible for some parameters in V(I)
  return !(detM in radical(ideal(S,I)))
end



@doc raw"""
    is_contact_equivalent(f::MPolyLocRingElem, g::MPolyLocRingElem)

Return if 'f' and 'g' are contact equivalent. 
Throws an error if method was unable to determine contact equivalence.
# Examples
```jldoctest
julia> R, (x,y) = QQ[:x, :y];

julia> L,_  = localization(R, complement_of_point_ideal(R, [0, 0]));

julia> is_contact_equivalent(L(x^2+y^2), L(x*y))
true

julia> is_contact_equivalent(L(x^5+y^2), L(x^3+x*y^2))
false
```
"""
function is_contact_equivalent(f::MPolyLocRingElem, g::MPolyLocRingElem)
  R = base_ring(parent(f))
  R == base_ring(parent(g)) || error("f and g must have the same MPolyRing as base ring.")
  ## checks via order
  ## order is invariant under contact equivalence
  ord_f = order_as_series(f)
  ord_f == order_as_series(g) || return false
  ## units are contact equivalent
  ord_f != 0 || return true
  ## power series of order 1 are contact equivalent to each other
  ord_f != 1 || return true
  ## f = g = 0
  ord_f != PosInf() || return true 
  ## tjurina number is invariant under contact equivalence
  tjurina_number(f) == tjurina_number(g) || return false
  ## Switching to polynomial representatives and shifting to origin for computations w.r.t. local ordering
  shift_f,_ = base_ring_shifts(parent(f))
  shift_g,_ = base_ring_shifts(parent(g))
  L,_ = localization(R, complement_of_point_ideal(R, [coefficient_ring(R)(0) for i = 1:ngens(R)]))
  f_poly = L(shift_f(numerator(f)))
  g_poly = L(shift_g(numerator(g)))
  ## check if f = u*g for some unit u with the help of the principal ideals generated by f and g.
  ideal(L, f_poly) != ideal(L, g_poly) || return true  
  ## checking contact equivalence via finite determinacy
  if is_finitely_determined(f_poly)    
    k_f = sharper_determinacy_bound(f_poly)
    k_g = sharper_determinacy_bound(g_poly)
    ## sharper_determinacy_bound returns the same determinancy bound if f and g are contact equivalent
    k_f == k_g || return false    
    ## switch to k-jet w.r.t. to determinancy bound
    m = ideal(R, gens(R))
    Q = MPolyQuoRing(R, m^(k_f+1))
    f_poly = L(lifted_numerator(simplify(Q(numerator(f_poly)))))    
    g_poly = L(lifted_numerator(simplify(Q(numerator(g_poly)))))
    ## check if same k-Jet
    f_poly != g_poly || return true    
    ## check tjurina number again, since it could have changed due to taking the k-jet, if not contact equivalent   
    tjurina_number(f_poly) == tjurina_number(g_poly) || return false    
  end
  ## check via Mather-Yau Theorem
  ## characteristic 0 
  characteristic(base_ring(parent(f))) != 0 || return _is_isomorphic_as_K_algebra(tjurina_algebra(f_poly), tjurina_algebra(g_poly))
  ## positive characteristic  
  tjurina_number(f_poly) != PosInf() || error("Unable to determine if is contact equivalent. (Singularities are not isolated)")
  ## calculate smallest k such that m^(deg(highcorner) + 1) = m^([k/2] + ord_f) \subseteq I
  a = numerator(f_poly)
  I = m*a + m^2*jacobian_ideal(a)
  G = standard_basis(I, ordering = negdeglex(parent(a)))
  h = Singular.highcorner(G.gensBiPolyArray.S)   # TODO: should this use singular_generators(G)?
  k = 2*(total_degree(R(h)) + 1 - ord_f)
  ## check k-th tjurina number
  tjurina_number(f_poly, k) == tjurina_number(g_poly, k) || return false
  ## check via Mather-Yau-Theorem for positive characteristic
  return _is_isomorphic_as_K_algebra(tjurina_algebra(f_poly, k), tjurina_algebra(g_poly, k))
end

@doc raw"""
    is_contact_equivalent(X::HypersurfaceGerm, Y::HypersurfaceGerm)

Return if the hypersurface germs 'X' and 'Y' are contact equivalent. 
Throws an error if method was unable to determine contact equivalence.
# Examples
```jldoctest
julia> R, (x,y) = QQ[:x, :y];

julia> X = HypersurfaceGerm(AffineScheme(quo(R, ideal(R, x^3+y^2))[1]), [0, 0]);

julia> Y = HypersurfaceGerm(AffineScheme(quo(R, ideal(R, x^3+x^2+y^2))[1]), [0, 0]);

julia> Z = HypersurfaceGerm(AffineScheme(quo(R, ideal(R, x^2+y^2))[1]), [0, 0]);

julia> is_contact_equivalent(X, Y)
false

julia> is_contact_equivalent(Y, Z)
true
```
"""
function is_contact_equivalent(X::HypersurfaceGerm, Y::HypersurfaceGerm)
  f = defining_ideal(X)[1]
  g = defining_ideal(Y)[1]
  return is_contact_equivalent(f, g)
end



################################################################################

#####                           Tjurina module                             #####

################################################################################


@doc raw"""
    tjurina_module(X::CompleteIntersectionGerm) 

Return the Tjurina module of the complete intersection germ `(X,p)` at the point `p`.
!!! note
    For better readability and for saving memory the Tjurina module of the corresponding CompleteIntersectionGerm shifted to the origin '0' is actually computed and returned.
!!! note
    When dealing with with a Hypersurface use the type 'HypersurfaceGerm' and the function 'tjurina_algebra' to also receive the algebra structure of the Tjurina module.

# Examples
```jldoctest
julia> R, (x,y,z) = QQ[:x,:y,:z];

julia> I = ideal(R, [x^2+y^2-z^2, x*y]);

julia> X = CompleteIntersectionGerm(spec(R, I), [0,0,0])
Spectrum
  of localization
    of quotient
      of multivariate polynomial ring in 3 variables x, y, z
        over rational field
      by ideal (x^2 + y^2 - z^2, x*y)
    at complement of maximal ideal of point (0, 0, 0)

julia> T = tjurina_module(X)
Subquotient of submodule with 2 generators
  1: e[1]
  2: e[2]
by submodule with 7 generators
  1: 2*x*e[1] + y*e[2]
  2: 2*y*e[1] + x*e[2]
  3: -2*z*e[1]
  4: (x^2 + y^2 - z^2)*e[1]
  5: (x^2 + y^2 - z^2)*e[2]
  6: x*y*e[1]
  7: x*y*e[2]

julia> vector_space_basis(T)
5-element Vector{FreeModElem{QQMPolyRingElem}}:
 e[1]
 e[2]
 y*e[1]
 y*e[2]
 z*e[2]
```
"""
@attr SubquoModule function tjurina_module(X::CompleteIntersectionGerm) 
  I = shifted_ideal(defining_ideal(X))
  R = base_ring(I)
  L,_ = localization(R, complement_of_point_ideal(R, [coefficient_ring(R)(0) for i = 1:ngens(R)]))  
  I = L(I)
  M = free_module(L, ngens(I))
  J = jacobian_matrix(gens(I))
  S = sub(M,J)[1] + (I*M)[1]
  return quo(M, S)[1]
end



@doc raw"""
    tjurina_number(X::CompleteIntersectionGerm)

Return Tjurina number of the complete intersection germ `(X,p)` at the point `p`. 
# Examples
```jldoctest
julia> R, (x,y,z) = QQ[:x,:y,:z];

julia> I = ideal(R, [x^2+y^2-z^2, x*y]);

julia> X = CompleteIntersectionGerm(spec(R, I), [0,0,0])
Spectrum
  of localization
    of quotient
      of multivariate polynomial ring in 3 variables x, y, z
        over rational field
      by ideal (x^2 + y^2 - z^2, x*y)
    at complement of maximal ideal of point (0, 0, 0)

julia> tjurina_number(X)
5
```
"""
@attr Union{<:Integer, PosInf} function tjurina_number(X::CompleteIntersectionGerm)
  d = vector_space_dim(tjurina_module(X))
  return d == -1 ? PosInf() : d
end



################################################################################

#####                             T^1 module                               #####

################################################################################


@doc raw"""
    T1_module(X::SpaceGerm)

Return the module $T^1_{X,p}$ of infinitinfinitesimal deformations for the space germ `(X,p)` at the point `p`. 
!!! note
    For better readability and for saving memory the Tjurina module of the corresponding SpaceGerm shifted to the origin '0' is actually computed and returned.
!!! note
    When dealing with with a Hypersurface use the type 'HypersurfaceGerm' and the function 'tjurina_algebra' to also receive the algebra structure of the Tjurina module.
# Examples
```jldoctest
```
"""
@attr Tuple{<:SubquoModule, <:SubquoModule, <:ModuleFPHom} function T1_module(X::SpaceGerm)
  # shifting to 0
  I_poly = Oscar.shifted_ideal(defining_ideal(X))  
  P_poly = base_ring(I_poly)
  n = ngens(P_poly)
  P,_ = localization(P_poly, complement_of_point_ideal(P_poly, zeros(coefficient_ring(P_poly), n))) 
  I = P(I_poly)
  # presentation of I:     A
  #                   P^p ––> P^k ––> I ––> 0     #k is ngens(I)
  # index:             1       0     -1    -2

  Ipres = presentation(ideal_as_module(I))
  # Ires = free_resolution(ideal_as_module(I), length=2)
  # Ipres = minimize(Ires)

  @show k = rank(Ipres[0])
  @show p = rank(Ipres[1])

  # Im(A^T) as an R=P/I-module
  R,_ = quo(P, I)
  At = change_base_ring(R, transpose(matrix(map(Ipres,1))))
  Im_At = image(At)
  # presentation of Im(A^T): 
  # index: 1       0        -1       -2
  #                         R^p 
  #            B1     A^T    U|     
  #       R^r ––> R^k –—> Im(A^T) ––> 0
  #        ^       ^
  #       l \      | Df
  #          `––– R^n

  Im_At_pres = presentation(Im_At)
  # Im_At_res = free_resolution(Im_At, length=2)
  # Im_At_pres = minimize(Im_At_res)

  @show k = rank(Im_At_pres[0])
  @show r = rank(Im_At_pres[1])

  B1 = map(Im_At_pres, 1) 
  Df = hom(FreeMod(R,n), Im_At_pres[0], change_base_ring(R, jacobian_matrix(gens(I))))

  T1_as_SubQuo = 
    simplify_light(
      quo(image(B1)[1], image(Df)[1])[1]
    )[1]       #abstract version from Matthias
  
  # Fix for the case when T^1 = 0 and simplify_light removes all generators
  # if is_zero(T1_as_SubQuo)
  #   F = free_module(P,0)
  #   return T1_as_SubQuo, quo_object(F, sub_object(F, [zero(F)]))
  # end
  
  # Now more explicit representation for versal family following Greuel, Lossen, Shustin
  # Lift to finitly presented R-modul

  T1_pres_as_RMod = presentation(T1_as_SubQuo)
  # T1_res_as_RMod = free_resolution(T1_as_SubQuo, length = 2)
  # T1_pres_as_RMod = minimize(T1_res_as_RMod)
  
  M = lift.(matrix(map(T1_pres_as_RMod, 1)))
  rel = image(M)
  Pr = ambient_free_module(rel)

  @show ngens(rel)
  @show rank(Pr)
  @show ngens(I)
  @show ngens(rel) + rank(Pr)*ngens(I)

  T1 = quo(Pr, (rel + (I*Pr)[1]))[1]
  ##### Wie weit Darstellung vereinfachen???
  #T1_simpler = simplify(T1)[1]   or  #simplify_light(T1)[1]
  #relations(T1_simpler)


  return T1_as_SubQuo, T1, B1  #_as_SubQuo  or #_simpler

  ##Test
  ###ab hier alt (löschen, wenn fertig)
  T1_as_R_coker = simplify_light(present_as_cokernel(T1_as_SubQuo))[1]
  # simplify_light(present_as_cokernel(simplify_light(T1_abstr)[1]))[1]
end


# Matthias Versions, aber vergessene Lokalisierung von mir hinzugefügt
function manualT1(X::SpaceGerm)
  I = Oscar.shifted_ideal(defining_ideal(X))
  P_poly = base_ring(I)
  P,_ = localization(P_poly, complement_of_point_ideal(P_poly, zeros(coefficient_ring(P_poly), n)))  
  F1 = FreeMod(P, 1)
  Imod,_ = sub(F1, [g*F1[1] for g in gens(I)])
  PmodI,_ = quo(F1, Imod)
  N, m = hom(Imod, PmodI)
  Df = change_base_ring(P,jacobian_matrix(gens(I)))
  F = ambient_free_module(N)
  spanDf,_ = sub(F, Df)
  T1, map_from_normal_module = quo(N, ambient_representatives_generators(spanDf))
  return T1, map_from_normal_module, m
end



@doc raw"""
    tjurina_number(X::SpaceGerm)

Return Tjurina number of the space germ `(X,p)` at the point `p`. 
# Examples
```jldoctest
julia> R, (x,y,z) = QQ[:x,:y,:z];

julia> I = ideal(R, [x*y, x*z, y*z]);

julia> X = SpaceGerm(spec(R, I), [0,0,0])
Spectrum
  of localization
    of quotient
      of multivariate polynomial ring in 3 variables x, y, z
        over rational field
      by ideal (x*y, x*z, y*z)
    at complement of maximal ideal of point (0, 0, 0)

julia> tjurina_number(X)
3
```
"""
@attr Union{<:Integer, PosInf} function tjurina_number(X::SpaceGerm)
  d = vector_space_dim(T1_module(X)[2])
  return d == -1 ? PosInf() : d
end



@doc raw"""
    is_rigid(X::HypersurfaceGerm)
    is_rigid(X::CompleteIntersectionGerm)
    is_rigid(X::SpaceGerm)

Return whether 'X' is a rigid singularity. 
# Examples
```jldoctest
julia> R, (x,y,z) = QQ[:x,:y,:z];

julia> I = ideal(R, [x*z, y*z]);

julia> X = SpaceGerm(spec(R, I), [0,0,0])
Spectrum
  of localization
    of quotient
      of multivariate polynomial ring in 3 variables x, y, z
        over rational field
      by ideal (x*z, y*z)
    at complement of maximal ideal of point (0, 0, 0)

julia> is_rigid(X)
true

julia> J = ideal(R, [x^3 + y^5 + z^2])
Ideal generated by
  x^3 + y^5 + z^2

julia> Y = HypersurfaceGerm(spec(R, J), [0,0,0])
Spectrum
  of localization
    of quotient
      of multivariate polynomial ring in 3 variables x, y, z
        over rational field
      by ideal (x^3 + y^5 + z^2)
    at complement of maximal ideal of point (0, 0, 0)

julia> is_rigid(Y)
false
```
"""
@attr Bool is_rigid(X::HypersurfaceGerm) = is_trivial(tjurina_algebra(X))
@attr Bool is_rigid(X::CompleteIntersectionGerm) = is_zero(tjurina_module(X))
@attr Bool is_rigid(X::SpaceGerm) = is_zero(T1_module(X)[1]) 



function T2_module(X::SpaceGerm)
  I_poly = Oscar.shifted_ideal(defining_ideal(X))  #k is ngens(I)
  P_poly = base_ring(I_poly)
  n = ngens(P_poly)
  P,_ = localization(P_poly, complement_of_point_ideal(P_poly, [coefficient_ring(P_poly)(0) for i = 1:n])) 
  I = P(I_poly)
  # presentation of I:     A
  #                   P^p ––> P^k ––> I ––> 0
  # index:             1       0     -1    -2
  Ipres = presentation(ideal_as_module(I))
  # Syz(I) = Im(A) as R=P/I-module
  Syz = image(matrix(map(Ipres,1)))
  #manually constructing the Koszulmodule since the entire Koszulcomplex is not needed
  O_Cnk = ambient_module(Syz)
  
  [gen(I,i)*O_Cnk[j] - gen(I,j)*O_Cnk[i] for j in 1:rank(O_Cnk) for i in 1:j-1]
  Kos = SubquoModule(OXk, [gen(I,i)*O_Cnk[j] - gen(I,j)*O_Cnk[i] for j in 1:rank(O_Cnk) for i in 1:j-1])
end



