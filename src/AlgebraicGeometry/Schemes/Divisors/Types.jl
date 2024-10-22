########################################################################
#
# AlgebraicCycle
#
# A minimal implementation of AbsAlgebraicCycle.
########################################################################
 
@attributes mutable struct AlgebraicCycle{
                                          CoveredSchemeType<:AbsCoveredScheme, 
                                          CoefficientRingType<:AbstractAlgebra.Ring, 
                                          CoefficientRingElemType<:AbstractAlgebra.RingElem
                                         } <: AbsAlgebraicCycle{CoveredSchemeType, 
                                                                CoefficientRingType}

  X::CoveredSchemeType # the parent
  R::CoefficientRingType # the ring of coefficients
  coefficients::IdDict{AbsIdealSheaf, CoefficientRingElemType} # the formal linear combination

  function AlgebraicCycle(
      X::AbsCoveredScheme,
      R::CoefficientRingType, 
      coefficients::IdDict{<:AbsIdealSheaf, CoefficientRingElemType};
      check::Bool=true
    ) where {CoefficientRingType, CoefficientRingElemType}
    for D in keys(coefficients)
      space(D) === X || error("component of divisor does not lie in the given scheme")
      parent(coefficients[D]) === R || error("coefficients do not lie in the given ring")
    end
    @check begin
      is_integral(X) || error("scheme must be integral") 
      #is_separated(X) || error("scheme must be separated") # We need to test this somehow, but how?
      d = isempty(coefficients) ? 0 : dim(first(keys(coefficients)))
      for D in keys(coefficients)
        (is_equidimensional(D) && dim(D) == d) || error("components of a cycle must be sheaves of equidimensional ideals of the same dimension")
      end
      true
    end
    return new{typeof(X), CoefficientRingType, CoefficientRingElemType}(X, R, coefficients)
  end
end


# The following has been moved to src/forward_declarations.jl
#abstract type AbsWeilDivisor{CoveredSchemeType, CoefficientRingType} <: AbsAlgebraicCycle{CoveredSchemeType, CoefficientRingType} end

@doc raw"""
    WeilDivisor <: AbsWeilDivisor

A Weil divisor on an integral `AbsCoveredScheme` ``X``; 
stored as a formal linear combination over some ring ``R`` of 
ideal sheaves on ``X``.
"""
@attributes mutable struct WeilDivisor{
    CoveredSchemeType<:AbsCoveredScheme, 
    CoefficientRingType<:AbstractAlgebra.Ring, 
    CoefficientRingElemType<:AbstractAlgebra.RingElem
   } <: AbsWeilDivisor{CoveredSchemeType, CoefficientRingType}
  C::AlgebraicCycle{CoveredSchemeType, CoefficientRingType, CoefficientRingElemType}

  function WeilDivisor(
      X::AbsCoveredScheme,
      R::CoefficientRingType, 
      coefficients::IdDict{<:AbsIdealSheaf, CoefficientRingElemType};
      check::Bool=true
    ) where {CoefficientRingType, CoefficientRingElemType}
    @check begin
      for D in keys(coefficients)
        is_equidimensional(D) || error("components of a divisor must be sheaves of equidimensional ideals")
        dim(X) - dim(D) == 1 || error("components of a divisor must be of codimension one")
      end
    end
    return new{typeof(X), CoefficientRingType, CoefficientRingElemType}(AlgebraicCycle(X, R, coefficients, check=check))
  end

  function WeilDivisor(C::AlgebraicCycle; check::Bool=true)
    X = ambient_scheme(C)
    @check begin
      for D in keys(coefficient_dict(C))
        is_equidimensional(D) || error("components of a divisor must be sheaves of equidimensional ideals")
        dim(X) - dim(D) == 1 || error("components of a divisor must be of codimension one")
      end
    end
    return new{typeof(X), coefficient_ring_type(C), coefficient_ring_elem_type(C)}(C)
  end
end


@doc raw"""
    LinearSystem

A linear system of a Weil divisor ``D`` on a variety ``X``, 
generated by rational functions ``f₁,…,fᵣ ∈ K(X)``.
"""
@attributes mutable struct LinearSystem{DivisorType<:AbsWeilDivisor}
  D::DivisorType
  f::Vector{<:VarietyFunctionFieldElem}

  function LinearSystem(f::Vector, D::AbsWeilDivisor; check::Bool=true)
    length(f) == 0 && return new{typeof(D)}(D, Vector{VarietyFunctionFieldElem}())
    KK = parent(f[1])
    all(g -> (parent(g) === KK), f[2:end]) || error("elements must have the same parent")
    X = ambient_scheme(D)
    X === variety(KK) || error("input not compatible")

    @check begin
      all(is_prime, components(D)) || error("components of the divisor must be prime")
      all(g->is_in_linear_system(g, D), f) || error("element not in linear system")
    end
    f = Vector{VarietyFunctionFieldElem}(f)
    return new{typeof(D)}(D, f)
  end
end

@doc raw""" 
    EffectiveCartierDivisor{CoveredSchemeType<:AbsCoveredScheme}

An effective Cartier divisor on a scheme $X$ is a closed subscheme $D \subseteq X$ whose ideal sheaf $\mathcal{I}_D \subseteq \mathcal{O}_X$ is an invertible $\mathcal{O}_X$-module. In particular, $\mathcal{I}_D$ is locally principal.

Internally, $C$ stores a [`trivializing_covering(C::EffectiveCartierDivisor)`](@ref).
The scheme $X$ is of type `CoveredSchemeType`.
"""
@attributes mutable struct EffectiveCartierDivisor{
                                                   CoveredSchemeType<:AbsCoveredScheme
                                                  }
  X::CoveredSchemeType
  I::AbsIdealSheaf
  C::Covering

  function EffectiveCartierDivisor(
      X::AbsCoveredScheme, 
      D::IdDict{<:AbsAffineScheme, <:RingElem};
      trivializing_covering::Covering=begin
        C = Covering(collect(keys(D)), IdDict{Tuple{AbsAffineScheme, AbsAffineScheme}, AbsGluing}())
        inherit_gluings!(C, default_covering(X))
        C
      end,
      check::Bool=true
    )
    for U in patches(trivializing_covering)
      U in keys(D) || error("the divisor must be prescribed on all patches of its trivializing covering")
    end
    ID = IdDict{AbsAffineScheme, Ideal}()
    for U in keys(D)
      ID[U] = ideal(OO(U), D[U])
    end
    I = IdealSheaf(X, ID, check=check)
    @check begin
      for U in keys(D)
        is_zero_divisor(OO(U)(D[U])) && error("local elements must not be zero divisors")
      end
      # TODO: 
      # - Check that every affine chart is covered
    end
    return new{typeof(X)}(X, I, trivializing_covering)
  end
end

@doc raw"""
    CartierDivisor{CoveredSchemeType<:AbsCoveredScheme, CoeffType<:RingElem}

A Cartier divisor $C$ on a scheme $X$ with coefficients $a_i$ in a ring $R$ is a formal linear combination 
$\sum_i a_i D_i$ of effective Cartier divisors $D_i$.

The scheme $X$ is of type `CoveredSchemeType`.
The coefficients $a_i$ are of type `CoeffType`.
"""
@attributes mutable struct CartierDivisor{
                                          CoveredSchemeType<:AbsCoveredScheme,
                                          CoeffType<:RingElem
                                         }
  X::CoveredSchemeType
  R::Ring
  coeff_dict::IdDict{EffectiveCartierDivisor, CoeffType}

  function CartierDivisor(X::AbsCoveredScheme, R::Ring, coeff_dict::IdDict{<:EffectiveCartierDivisor, CoeffType}) where {CoeffType<:RingElem}
    all(x->(ambient_scheme(x)===X), keys(coeff_dict)) || error("all effective divisors must be defined over the same scheme")
    all(x->(parent(x) === R), values(coeff_dict)) || error("all coefficients must belong to the same parent")
    return new{typeof(X), CoeffType}(X, R, coeff_dict)
  end
end
