
###############################################################################
#
# AbstractBundle
#
@doc raw"""
    abstract_bundle(X::AbstractVariety, ch::Union{MPolyDecRingElem, MPolyQuoRingElem})
    abstract_bundle(X::AbstractVariety, r::RingElement, c::Union{MPolyDecRingElem, MPolyQuoRingElem})

Return a bundle on `X` by specifying its Chern character. Equivalently, specify its rank and
total Chern class.

# Examples

We show two ways of constructing the Horrocks-Mumford bundle `F` [HM73](@cite). First, we create `F` as the
cohomology bundle of its Beilinson monad

$0 \rightarrow \mathcal O_{\mathbb P^4} ^5(2)\rightarrow \Lambda^2 T^*_{\mathbb P^4}(5)
\rightarrow \mathcal O_{\mathbb P^4}^5(3)\rightarrow 0.$

Then, we show the constructor above at work.

# Examples
```jldoctest
julia> T, (d,) = polynomial_ring(QQ, ["d"])
(Multivariate polynomial ring in 1 variable over QQ, QQMPolyRingElem[d])

julia> QT = fraction_field(T)
Fraction field
  of multivariate polynomial ring in 1 variable over QQ

julia> P4 = abstract_projective_space(4, base = QT)
AbstractVariety of dim 4

julia> A = 5*line_bundle(P4, 2)
AbstractBundle of rank 5 on AbstractVariety of dim 4

julia> B = 2*exterior_power(cotangent_bundle(P4), 2)*OO(P4, 5)
AbstractBundle of rank 12 on AbstractVariety of dim 4

julia> C = 5*line_bundle(P4, 3)
AbstractBundle of rank 5 on AbstractVariety of dim 4

julia> F = B-A-C
AbstractBundle of rank 2 on AbstractVariety of dim 4

julia> chern_class(F, 1)
5*h

julia> chern_class(F, 2)
10*h^2

julia> rank(F)
2

julia> total_chern_class(F)
10*h^2 + 5*h + 1

julia> h = gens(P4)[1]
h

julia> F == abstract_bundle(P4, 2, 10*h^2 + 5*h + 1)
true

```
"""
abstract_bundle(X::AbstractVariety, ch::MPolyDecRingOrQuoElem) = AbstractBundle(X, ch)
abstract_bundle(X::AbstractVariety, r::RingElement, c::MPolyDecRingOrQuoElem) = AbstractBundle(X, r, c)

==(F::AbstractBundle, G::AbstractBundle) = chern_character(F) == chern_character(G)

@doc raw"""
    chern_character(F::AbstractBundle)

Return the Chern character of `F`.

# Examples
```jldoctest
julia> G = abstract_grassmannian(3,5)
AbstractVariety of dim 6

julia> Q = tautological_bundles(G)[2]
AbstractBundle of rank 2 on AbstractVariety of dim 6

julia> chern_character(Q)
-1//2*c[1]^2 + 1//6*c[1]*c[2] - 1//24*c[1]*c[3] - c[1] + c[2] - 1//3*c[3] + 2

```
"""
chern_character(F::AbstractBundle) = (
  if !isdefined(F, :ch) F.ch = F.rank + _logg(F.chern) end;
  F.ch)

@doc raw"""
    total_chern_class(F::AbstractBundle)

Return the total Chern class of `F`.

# Examples
```jldoctest
julia> G = abstract_grassmannian(3,5)
AbstractVariety of dim 6

julia> Q = tautological_bundles(G)[2]
AbstractBundle of rank 2 on AbstractVariety of dim 6

julia> total_chern_class(Q)
c[1]^2 - c[1] - c[2] + 1

```
"""
total_chern_class(F::AbstractBundle) = (
  if !isdefined(F, :chern) F.chern = _expp(F.ch) end;
  F.chern)

@doc raw"""
    chern_class(F::AbstractBundle, k::Int)

Return the `k`-th Chern class of `F`.
"""
chern_class(F::AbstractBundle, k::Int) = (
  isdefined(F, :chern) && return total_chern_class(F)[k];
  _expp(F.ch, truncate=k)[k])

@doc raw"""
    top_chern_class(F::AbstractBundle)

Compute Return the top Chern class of `F`.
"""
top_chern_class(F::AbstractBundle) = chern_class(F, F.rank)

@doc raw"""
    segre_class(F::AbstractBundle)

Return the total Segre class of `F`.
"""
segre_class(F::AbstractBundle) = inv(total_chern_class(F))

@doc raw"""
    segre_class(F::AbstractBundle, k::Int)

Retuen the `k`-th Segre class of `F`.
"""
segre_class(F::AbstractBundle, k::Int) = segre_class(F)[k]

@doc raw"""
    todd_class(F::AbstractBundle)

Return the Todd class of `F`.
"""
todd_class(F::AbstractBundle) = _todd_class(chern_character(F))

@doc raw"""
    total_pontryagin_class(F::AbstractBundle)

Return the total Pontryagin class of `F`.
"""
function total_pontryagin_class(F::AbstractBundle)
  n = F.parent.dim
  x = total_chern_class(F) * total_chern_class(dual(F))
  comps = x[0:n]
  sum([(-1)^i*comps[2i+1] for i in 0:n÷2])
end

@doc raw"""
    pontryagin_class(F::AbstractBundle, k::Int)

Return the `k`-th Pontryagin class of `F`.
"""
pontryagin_class(F::AbstractBundle, k::Int) = total_pontryagin_class(F)[2k]

@doc raw"""
    euler_characteristic(F::AbstractBundle)
    euler_pairing(F::AbstractBundle, G::AbstractBundle)

Return the holomorphic Euler characteristic $\chi(F)$ and the Euler pairing
$\chi(F,G)$, respectively.
"""
Oscar.euler_characteristic(F::AbstractBundle) = integral(chern_character(F) * todd_class(F.parent)) # Hirzebruch-Riemann-Roch
euler_pairing(F::AbstractBundle, G::AbstractBundle) = begin
  F, G = _coerce(F, G)
  integral(chern_character(dual(F)) * chern_character(G) * todd_class(F.parent))
end

###############################################################################
#
# AbstractVarietyMap
#
@doc raw"""
    hom(X::AbstractVariety, Y::AbstractVariety, fˣ::Vector, fₓ = nothing; inclusion::Bool = false, symbol::String = "x")

Return an abstract variety morphism from `X` to `Y` by specifying the pullbacks of
the generators of the Chow ring of `Y`. 

!!! note
    The corresponding pushforward can be automatically computed in certain cases.

In case of an inclusion $i:X\hookrightarrow Y$ where the class of `X` is not
present in the Chow ring of `Y`, use the argument `inclusion = true`. Then,
a copy of `Y` will be created, with extra classes added so that one can
pushforward all classes on `X`.
"""
function hom(X::AbstractVariety, Y::AbstractVariety, fˣ::Vector, fₓ = nothing; inclusion::Bool = false, symbol::String = "x")
  AbstractVarietyMap(X, Y, fˣ, fₓ)
  # !inclusion && return AbstractVarietyMap(X, Y, fˣ, fₓ)
  # _inclusion(AbstractVarietyMap(X, Y, fˣ), symbol=symbol)
end

@doc raw"""
    dim(f::AbstractVarietyMap)

Return the relative dimension of `f`.
"""
dim(f::AbstractVarietyMap) = f.dim

@doc raw"""
    tangent_bundle(f::AbstractVarietyMap)

Return the relative tangent bundle.
"""
tangent_bundle(f::AbstractVarietyMap) = f.T

@doc raw"""
    cotangent_bundle(f::AbstractVarietyMap)

Return the relative cotangent bundle.
"""
cotangent_bundle(f::AbstractVarietyMap) = dual(f.T)

@doc raw"""
    todd_class(f::AbstractVarietyMap)

Compute the Todd class of the relative tangent bundle.
"""
todd_class(f::AbstractVarietyMap) = todd_class(f.T)

@doc raw"""
    pullback(f::AbstractVarietyMap, x::MPolyDecRingElem)
    pullback(f::AbstractVarietyMap, F::AbstractBundle)

Compute the pullback of a Chow ring element $x$ or a bundle $F$ by a morphism $f$.
"""
pullback(f::AbstractVarietyMap, x::MPolyDecRingOrQuoElem) = f.pullback(x)
pullback(f::AbstractVarietyMap, F::AbstractBundle) = AbstractBundle(f.domain, f.pullback(chern_character(F)))

@doc raw"""
    pushforward(f::AbstractVarietyMap, x::MPolyDecRingElem)
    pushforward(f::AbstractVarietyMap, F::AbstractBundle)

Compute the pushforward of a Chow ring element $x$ or a bundle $F$ by a
morphism $f$. For abstract bundles, the pushforward is derived, e.g., for a
bundle $F$ it is understood as the alternating sum of all direct images.
"""
pushforward(f::AbstractVarietyMap, x::MPolyDecRingOrQuoElem) = f.pushforward(x)
pushforward(f::AbstractVarietyMap, F::AbstractBundle) = AbstractBundle(f.codomain, f.pushforward(chern_character(F) * todd_class(f))) # Grothendieck-Hirzebruch-Riemann-Roch

function identity_hom(X::V) where V <: AbstractVarietyT
  AbstractVarietyMap(X, X, gens(X.ring), map_from_func(identity, X.ring, X.ring))
end

@doc raw"""
    *(f::AbstractVarietyMap, g::AbstractVarietyMap)

Construct the composition morphism $g\circ f: X\to Z$ for $f: X\to Y$ and $g:Y\to Z$.
"""
function *(f::AbstractVarietyMap, g::AbstractVarietyMap)
  X, Y = f.domain, f.codomain
  @assert g.domain == Y
  Z = g.codomain
  gofₓ = nothing
  if isdefined(f, :pushforward) && isdefined(g, :pushforward)
    gofₓ = map_from_func(g.pushforward ∘ f.pushforward, X.ring, Z.ring)
  end
  gof = AbstractVarietyMap(X, Z, g.pullback * f.pullback, gofₓ)
  return gof
end

###############################################################################
#
# AbstractVariety
#
# generic abstract_variety with some classes in given degrees
@doc raw"""
    abstract_variety(n::Int, symbols::Vector{String}, degs::Vector{Int})

Construct a generic abstract variety of dimension $n$ with some classes in given degrees.

Return the abstract variety and the list of classes.
"""
function abstract_variety(n::Int, symbols::Vector{String}, degs::Vector{Int}; base::Ring=QQ)
  @assert length(symbols) > 0
  R, x = graded_polynomial_ring(base, symbols, degs)
  return AbstractVariety(n, R), x
end

# generic abstract_variety with some bundles in given ranks
@doc raw"""
    abstract_variety(n::Int, bundles::Vector{Pair{Int, T}}) where T

Construct a generic abstract variety of dimension $n$ with some bundles of given ranks.

Return the abstract variety and the list of bundles.
"""
function abstract_variety(n::Int, bundles::Vector{Pair{Int, T}}; base::Ring=QQ) where T
  symbols = vcat([_parse_symbol(s,1:r) for (r,s) in bundles]...)
  degs = vcat([collect(1:r) for (r,s) in bundles]...)
  X = abstract_variety(n, symbols, degs, base=base)[1]
  i = 1
  X.bundles = AbstractBundle[]
  for (r,s) in bundles
    push!(X.bundles, AbstractBundle(X, r, 1 + sum(gens(X.ring)[i:i+r-1])))
    i += r
  end
  return X, X.bundles
end

# generic abstract variety with tangent bundle
@doc raw"""
    abstract_variety(n::Int)

Construct a generic abstract variety of dimension $n$ and define its tangent bundle.

Return the abstract_variety.
"""
function abstract_variety(n::Int; base::Ring=QQ)
  n == 0 && return abstract_point()
  X, (T,) = abstract_variety(n, [n=>"c"], base=base)
  X.T = T
  return X
end

# abstract_variety with dimension and Chow ring
@doc raw"""
     abstract_variety(n::Int, A::Union{MPolyDecRing, MPolyQuoRing{<:MPolyDecRingElem}})

Return an abstract variety of dimension `n` with Chow ring `A`.

# Examples
```jldoctest
julia> R, (h,) = graded_polynomial_ring(QQ, ["h"])
(Graded multivariate polynomial ring in 1 variable over QQ, MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}[h])

julia> A, _ = quo(R, ideal(R, [h^3]))
(Quotient of multivariate polynomial ring by ideal (h^3), Map: R -> A)

julia> P2 = abstract_variety(2, A)
AbstractVariety of dim 2
```

!!! note
    The example above shows one way of setting up a version of the abstract projective plane. A more convenient way is to use the built-in command `abstract_projective_space` which implements additional data such as the tangent bundle:

```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> TP2 = tangent_bundle(P2)
AbstractBundle of rank 2 on AbstractVariety of dim 2

julia> chern_character(TP2)
3//2*h^2 + 3*h + 2
```
"""
function abstract_variety(n::Int, R::MPolyDecRingOrQuo)
  return AbstractVariety(n::Int, R::MPolyDecRingOrQuo)
end

###############################################
### getter functions
###############################################

@doc raw"""
    chow_ring(X::AbstractVariety)

Return the Chow ring of `X`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> P3 = abstract_projective_space(3, symbol = "H")
AbstractVariety of dim 3

julia> chow_ring(P2*P3)
Quotient
  of multivariate polynomial ring in 2 variables over QQ graded by
    h -> [1]
    H -> [1]
  by ideal (h^3, H^4)

```
"""
chow_ring(X::AbstractVariety) = X.ring


(X::AbstractVariety)(f::RingElement) = X.ring(f)
gens(X::AbstractVariety) = gens(X.ring)

@doc raw"""
    base(X::AbstractVariety)

Return the coefficient ring of the polynomial ring underlying the Chow ring of `X`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> chow_ring(P2)
Quotient
  of multivariate polynomial ring in 1 variable over QQ graded by
    h -> [1]
  by ideal (h^3)

julia> base(P2)
Rational field

```
"""
base(X::AbstractVariety) = X.base

@doc raw"""
    point_class(X::AbstractVariety)

Return the point class of `X`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> P3 = abstract_projective_space(3, symbol = "H")
AbstractVariety of dim 3

julia> point_class(P2*P3)
h^2*H^3

```
"""
point_class(X::AbstractVariety) = X.point

@doc raw"""
    trivial_line_bundle(X::AbstractVariety)

Return the trivial line bundle $\mathcal O_X$ on `X`. Alternatively, use `OO`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> OX = trivial_line_bundle(P2)
AbstractBundle of rank 1 on AbstractVariety of dim 2

julia> chern_character(OX)
1

```
"""
trivial_line_bundle(X::AbstractVariety) = AbstractBundle(X, X(1))
(OO)(X::AbstractVariety) = trivial_line_bundle(X)

@doc raw"""
    tautological_bundles(X::AbstractVariety)

Return the tautological_bundles of `X` (if applicable).

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> TB = tautological_bundles(P2)
2-element Vector{AbstractBundle}:
 AbstractBundle of rank 1 on AbstractVariety of dim 2
 AbstractBundle of rank 2 on AbstractVariety of dim 2

julia> TB[1] == OO(P2, -1)
true

julia> TB[2] == tangent_bundle(P2)*OO(P2, -1)
true

```

```jldoctest
julia> G = abstract_grassmannian(3, 5)
AbstractVariety of dim 6

julia> tautological_bundles(G)
2-element Vector{AbstractBundle}:
 AbstractBundle of rank 3 on AbstractVariety of dim 6
 AbstractBundle of rank 2 on AbstractVariety of dim 6

```
"""
tautological_bundles(X::AbstractVariety) = X.bundles

@doc raw"""
    structure_map(X::AbstractVariety)

Return the structure map of `X`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> structure_map(P2)
AbstractVarietyMap from AbstractVariety of dim 2 to AbstractVariety of dim 0

julia> T = tangent_bundle(P2)
AbstractBundle of rank 2 on AbstractVariety of dim 2

julia> E = abstract_projective_bundle(T, symbol = "H")
AbstractVariety of dim 3

julia> chow_ring(E)
Quotient
  of multivariate polynomial ring in 2 variables over QQ graded by
    H -> [1]
    h -> [1]
  by ideal (h^3, H^2 + 3*H*h + 3*h^2)

julia> structure_map(E)
AbstractVarietyMap from AbstractVariety of dim 3 to AbstractVariety of dim 2

```
"""
structure_map(X::AbstractVariety) = X.struct_map


@doc raw"""
    line_bundle(X::AbstractVariety, n::RingElement)
    line_bundle(X::AbstractVariety, D::MPolyDecRingElem)

Return the line bundle $\mathcal O_X(n)$ on `X` if `X` has been given a
polarization, or a line bundle $\mathcal O_X(D)$ with first Chern class $D$.
Alternatively, use `OO`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> tautological_bundles(P2)[1] == OO(P2, -1)
true

```
"""
line_bundle(X::AbstractVariety, n::RingElement) = AbstractBundle(X, 1, 1+n*X.O1)
line_bundle(X::AbstractVariety, D::MPolyDecRingElem) = AbstractBundle(X, 1, 1+D[1])

(OO)(X::AbstractVariety, n::RingElement) = line_bundle(X, n)
OO(X::AbstractVariety, D::MPolyDecRingElem) = line_bundle(X, D)

@doc raw"""
    degree(X::AbstractVariety)

Compute the degree of `X` with respect to its polarization (if given).

# Examples
```jldoctest
julia> G = abstract_grassmannian(2,5)
AbstractVariety of dim 6

julia> degree(G)
5

```
"""
degree(X::AbstractVariety) = integral(X.O1^X.dim)

@doc raw"""
    tangent_bundle(X::AbstractVariety)

Return the tangent bundle of `X`.

# Examples
```jldoctest
julia> G = abstract_grassmannian(2,5)
AbstractVariety of dim 6

julia> TG = tangent_bundle(G)
AbstractBundle of rank 6 on AbstractVariety of dim 6

julia> chern_character(TG)
-5//6*c[1]^3 + 5//24*c[1]^2*c[2] + 3//2*c[1]^2 + 5//2*c[1]*c[2] - 5*c[1] + 7//72*c[2]^3 - 25//24*c[2]^2 - c[2] + 6

```
"""
tangent_bundle(X::AbstractVariety) = X.T

@doc raw"""
    cotangent_bundle(X::AbstractVariety)

Return the cotangent bundle of `X`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> cotangent_bundle(P2) == dual(tangent_bundle(P2)) 
true

```
"""
cotangent_bundle(X::AbstractVariety) = dual(X.T)

@doc raw"""
    canonical_class(X::AbstractVariety)

Return the canonical class of `X`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> canonical_class(P2) == chern_class(cotangent_bundle(P2), 1)
true

julia> canonical_class(P2) 
-3*h

```
"""
canonical_class(X::AbstractVariety) = -chern_class(X.T, 1)

@doc raw"""
    canonical_bundle(X::AbstractVariety)

Return the canonical bundle of `X`.

```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> canonical_bundle(P2) == det(cotangent_bundle(P2))
true

```
"""
canonical_bundle(X::AbstractVariety) = det(cotangent_bundle(X))

@doc raw"""
    total_chern_class(X::AbstractVariety)
    total_chern_class(X::TnVariety)

Return the total Chern class of the tangent bundle of `X`.
"""
total_chern_class(X::AbstractVariety) = total_chern_class(X.T)

@doc raw"""
    chern_class(X::AbstractVariety, k::Int)
    chern_class(X::TnVariety, k::Int)

Return the `k'-th Chern class of the tangent bundle of `X`.
"""
chern_class(X::AbstractVariety, k::Int) = chern_class(X.T, k)

@doc raw"""
    euler(X::AbstractVariety)
    euler(X::TnVariety)

Return the Euler number of `X`.
"""
euler(X::AbstractVariety) = integral(total_chern_class(X.T))

@doc raw"""
    todd_class(X::AbstractVariety)

Compute the Todd class of the tangent bundle of `X`.
"""
todd_class(X::AbstractVariety) = todd_class(X.T)

@doc raw"""
    total_pontryagin_class(X::AbstractVariety)

Compute the total Pontryagin class of the tangent bundle of `X`.
"""
total_pontryagin_class(X::AbstractVariety) = total_pontryagin_class(X.T)

@doc raw"""
    pontryagin_class(X::AbstractVariety, k::Int)

Compute the `k`-th Pontryagin class of the tangent bundle of `X`.
"""
pontryagin_class(X::AbstractVariety, k::Int) = pontryagin_class(X.T, k)

chi(p::Int, X::AbstractVariety) = chi(exterior_power(dual(X.T), p)) # generalized Todd genus

function todd_polynomial(n::Int)
  X = abstract_variety(n)
  R, z = X.ring["z"]
  sum(chi(p, X) * (z-1)^p for p in 0:n)
end

@doc raw"""
    chern_number(X::AbstractVariety, λ::Int...)
    chern_number(X::AbstractVariety, λ::Vector{Int})
    chern_number(X::AbstractVariety, λ::Partition)

Compute the Chern number $c_\lambda (X):=\int_X c_{\lambda_1}(X)\cdots
c_{\lambda_k}(X)$, where $\lambda:=(\lambda_1,\dots,\lambda_k)$ is a partition
of the dimension of `X`.
"""
chern_number(X::AbstractVariety, λ::Int...) = chern_number(X, collect(λ))
chern_number(X::AbstractVariety, λ::Partition) = chern_number(X, Vector(λ))
function chern_number(X::AbstractVariety, λ::Vector{Int})
  @assert sum(λ) == X.dim
  c = total_chern_class(X)[1:X.dim]
  integral(prod([c[i] for i in λ]))
end

@doc raw"""
    chern_numbers(X::AbstractVariety)

Compute all the Chern numbers of `X` as a list of pairs $\lambda\Rightarrow
c_\lambda(X)$.
"""
function chern_numbers(X::AbstractVariety)
  c = total_chern_class(X)[1:X.dim]
  [λ => integral(prod([c[i] for i in λ])) for λ in partitions(X.dim)]
end

for g in [:a_hat_genus, :l_genus]
  @eval function $g(k::Int, X::AbstractVariety)
    R = X.ring
    k == 0 && return R(1)
    p = total_pontryagin_class(X.T)[1:2k]
    R isa MPolyDecRing && return R($g(k).f([p[2i].f for i in 1:k]...))
    R isa MPolyQuoRing && return R(base_ring(R)($g(k).f([p[2i].f.f for i in 1:k]...)))
  end
  @eval function $g(X::AbstractVariety)
    !iseven(X.dim) && error("the abstract_variety is not of even dimension")
    integral($g(X.dim÷2, X))
  end
end

@doc raw"""
    a_hat_genus(k::Int, X::AbstractVariety)

Compute the `k`-th $\hat A$ genus of a abstract_variety `X`.
"""
a_hat_genus(k::Int, X::AbstractVariety)

@doc raw"""
    l_genus(k::Int, X::AbstractVariety)

Compute the `k`-th L genus of a abstract_variety `X`.
"""
l_genus(k::Int, X::AbstractVariety)

@doc raw"""
    a_hat_genus(X::AbstractVariety)

Compute the top $\hat A$ genus of a abstract_variety `X` of even dimension.
"""
a_hat_genus(X::AbstractVariety)

@doc raw"""
    l_genus(X::AbstractVariety)

Compute the top L genus of a abstract_variety `X` of even dimension.
"""
l_genus(X::AbstractVariety)

@doc raw"""
    signature(X::AbstractVariety)

Compute the signature of a abstract_variety `X` of even dimension.
"""
signature(X::AbstractVariety) = l_genus(X) # Hirzebruch signature theorem

@doc raw"""
    hilbert_polynomial(F::AbstractBundle)
    hilbert_polynomial(X::AbstractVariety)

Compute the Hilbert polynomial of a bundle $F$ or the Hilbert polynomial of `X`
itself, with respect to the polarization $\mathcal O_X(1)$ on `X`.
"""
function hilbert_polynomial(F::AbstractBundle)
  !isdefined(F.parent, :O1) && error("no polarization is specified for the abstract_variety")
  X, O1 = F.parent, F.parent.O1
  # extend the coefficient ring to QQ(t)
  # TODO should we use FunctionField here?
  Qt, t = polynomial_ring(QQ, "t")
  @assert X.ring isa MPolyQuoRing
  R = parent(change_base_ring(Qt, base_ring(X.ring).R()))
  GR = grade(R, gradings(base_ring(X.ring)))[1]
  toR = x -> GR(change_base_ring(Qt, x, parent=R))
  I = ideal(toR.(gens(X.ring.I)))
  R_ = quo(GR, I)[1]
  set_attribute!(R_, :abstract_variety_dim => X.dim)
  ch_O_t = 1 + _logg(1 + t * R_(toR(O1.f)))
  ch_F = R_(toR(chern_character(F).f))
  td = R_(toR(todd_class(X).f))
  pt = R_(toR(X.point.f))
  hilb = constant_coefficient(div(simplify(ch_F * ch_O_t * td).f, simplify(pt).f))
  return hilb
end
hilbert_polynomial(X::AbstractVariety) = hilbert_polynomial(trivial_line_bundle(X))

# find canonically defined morphism from X to Y
function _hom(X::AbstractVariety, Y::AbstractVariety)
  X == Y && return identity_hom(X)
  # first handle the case where X is a (fibered) product
  projs = get_attribute(X, :projections)
  if projs !== nothing
    for p in projs
      p.codomain == Y && return p
    end
  else
    # follow the chain of structure maps to see if we can arrive at Y
    homs = AbstractVarietyMap[]
    while isdefined(X, :struct_map) && X != Y
      push!(homs, X.struct_map)
      X = X.struct_map.codomain
    end
    X == Y && return reduce(*, homs)
  end
  error("no canonical homomorphism between the given varieties")
end

# morphisms for points are convenient, but are not desired when doing coercion
@doc raw"""
    hom(X::AbstractVariety, Y::AbstractVariety)

Return a canonicallly defined morphism from `X` to `Y`.
"""
function hom(X::AbstractVariety, Y::AbstractVariety)
  get_attribute(Y, :point) !== nothing && return hom(X, Y, [X(0)]) # Y is a point
  get_attribute(X, :point) !== nothing && return hom(X, Y, repeat([X(0)], length(gens(Y.ring)))) # X is a point
  _hom(X, Y)
end

# product abstract_variety
@doc raw"""
    product(X::AbstractVariety, Y::AbstractVariety)

Return the product $X\times Y$. If both `X` and `Y` have a
polarization, $X\times Y$ will be endowed with the polarization of the Segre
embedding. Alternatively, use `*`.

```jldoctest
julia> P2 = abstract_projective_space(2);

julia> P3 = abstract_projective_space(3, symbol = "H");

julia> P2xP3 = P2*P3
AbstractVariety of dim 5

julia> chow_ring(P2xP3)
Quotient
  of multivariate polynomial ring in 2 variables over QQ graded by
    h -> [1]
    H -> [1]
  by ideal (h^3, H^4)

```
"""
function product(X::AbstractVariety, Y::AbstractVariety)
  prod_cache = get_attribute(X, :prod_cache)
  prod_cache !== nothing && Y in keys(prod_cache) && return prod_cache[Y]
  if prod_cache === nothing
    prod_cache = Dict{AbstractVariety, AbstractVariety}()
    set_attribute!(X, :prod_cache => prod_cache)
  end
  @assert X.base == Y.base
  base = X.base
  A, B = X.ring, Y.ring
  symsA, symsB = string.(gens(A)), string.(gens(B))
  a = length(symsA)
  R, x = graded_polynomial_ring(base, vcat(symsA, symsB), vcat(gradings(A), gradings(B)))
  # TODO: fails with check = true
  AtoR = hom(A, R, x[1:a], check = false)
  BtoR = hom(B, R, x[a+1:end], check = false)
  IA = ideal(A isa MPolyQuoRing ? AtoR.(A.(gens(A.I))) : [R()])
  IB = ideal(B isa MPolyQuoRing ? BtoR.(B.(gens(B.I))) : [R()])
  AXY, _ = quo(R, IA + IB)
  XY = AbstractVariety(X.dim+Y.dim, AXY)
  if isdefined(X, :point) && isdefined(Y, :point)
    XY.point = XY(AtoR(X.point) * BtoR(Y.point))
  end
  p = AbstractVarietyMap(XY, X, XY.(x[1:a]))
  q = AbstractVarietyMap(XY, Y, XY.(x[a+1:end]))
  if isdefined(X, :T) && isdefined(Y, :T)
    XY.T = pullback(p, X.T) + pullback(q, Y.T)
  end
  if isdefined(X, :O1) && isdefined(Y, :O1) # Segre embedding
    XY.O1 = p.pullback(X.O1) + q.pullback(Y.O1)
  end
  if get_attribute(X, :alg) == true && get_attribute(Y, :alg) == true
    set_attribute!(XY, :alg => true)
  end
  set_attribute!(XY, :projections => [p, q])
  set_attribute!(XY, :description => "Product of $X and $Y")
  prod_cache[Y] = XY
  return XY
end
*(X::AbstractVariety, Y::AbstractVariety) = product(X, Y)

@doc raw"""
    graph(f::AbstractVarietyMap)

Given a morphism $f: X\to Y$, construct $i:\Gamma_f\to X\times Y$, the
inclusion of the graph into the product.
"""
function graph(f::AbstractVarietyMap)
  X, Y = f.domain, f.codomain
  hom(X, X * Y, vcat(gens(X), f.pullback.image))
end

###############################################################################
#
# Operators on AbstractBundle
#
function adams(k::Int, x::MPolyDecRingOrQuoElem)
  R = parent(x)
  n = get_attribute(R, :abstract_variety_dim)
  comps = x[0:n]
  sum([ZZ(k)^i*comps[i+1] for i in 0:n])
end

@doc raw"""
    dual(F::AbstractBundle)

Return the dual bundle of `F`.

# Examples
```jldoctest
julia> P4 = abstract_projective_space(4)
AbstractVariety of dim 4

julia> h = gens(P4)[1]
h

julia> F = abstract_bundle(P4, 2, 10*h^2 + 5*h + 1) # Horrocks-Mumford bundle
AbstractBundle of rank 2 on AbstractVariety of dim 4

julia> c1 = chern_class(F, 1)
5*h

julia> Fd = dual(F)
AbstractBundle of rank 2 on AbstractVariety of dim 4

julia> chern_class(Fd, 1)
-5*h

julia> F == Fd*OO(P4, 5) # self-duality up to twist
true

```
"""
function dual(F::AbstractBundle)
  Fdual = AbstractBundle(F.parent, adams(-1, chern_character(F)))
  if isdefined(F, :chern)
    Fdual.chern = adams(-1, total_chern_class(F))
  end
  return Fdual
end

@doc raw"""
    -(F::AbstractBundle)
    *(n::RingElement, F::AbstractBundle)
    +(F::AbstractBundle, G::AbstractBundle)
    *(F::AbstractBundle, G::AbstractBundle)
    
Return `-F`, the sum `F` $+ \dots +$ `F` of `n` copies of `F`, `F` $+$ `G`, `F` $-$ `G`, and the tensor product of `F` and `G`, respectively.

# Examples
```jldoctest
julia> P3 = abstract_projective_space(3)
AbstractVariety of dim 3

julia> 4*OO(P3)-OO(P3, -1) == tangent_bundle(P3)*OO(P3, -1) # Euler sequence
true

```
"""
-(F::AbstractBundle) = AbstractBundle(F.parent, -chern_character(F))
+(n::RingElement, F::AbstractBundle) = AbstractBundle(F.parent, n + chern_character(F))
*(n::RingElement, F::AbstractBundle) = AbstractBundle(F.parent, n * chern_character(F))
+(F::AbstractBundle, n::RingElement) = n + F
*(F::AbstractBundle, n::RingElement) = n * F
^(F::AbstractBundle, n::Int) = AbstractBundle(F.parent, chern_character(F)^n)

for O in [:(+), :(-), :(*)]
  @eval ($O)(F::AbstractBundle, G::AbstractBundle) = (
    (F, G) = _coerce(F, G);
    AbstractBundle(F.parent, $O(chern_character(F), chern_character(G))))
end

@doc raw"""
    det(F::AbstractBundle)

Return the determinant bundle of `F`.

# Examples
```jldoctest
julia> P3 = abstract_projective_space(3)
AbstractVariety of dim 3

julia> T = tangent_bundle(P3)
AbstractBundle of rank 3 on AbstractVariety of dim 3

julia> chern_class(T, 1)
4*h

julia> det(T) == OO(P3, 4)
true

```
"""
det(F::AbstractBundle) = AbstractBundle(F.parent, 1, 1 + chern_class(F, 1))
function _coerce(F::AbstractBundle, G::AbstractBundle)
  X, Y = F.parent, G.parent
  X == Y && return F, G
  try
    return F, pullback(_hom(X, Y), G)
  catch
    try
      return pullback(_hom(Y, X), F), G
    catch
      error("the sheaves are not on compatible varieties")
    end
  end
end


hom(F::AbstractBundle, G::AbstractBundle) = dual(F) * G

@doc raw"""
    exterior_power(F::AbstractBundle, k::Int)

Return the `k`-th exterior power of `F`.
"""
function exterior_power(F::AbstractBundle, k::Int)
  AbstractBundle(F.parent, _wedge(k, chern_character(F))[end])
end

function exterior_power(F::AbstractBundle)
  AbstractBundle(F.parent, sum([(-1)^(i-1) * w for (i, w) in enumerate(_wedge(F.rank, chern_character(F)))]))
end

@doc raw"""
    symmetric_power(F::AbstractBundle, k::Int)
    symmetric_power(F::AbstractBundle, k::RingElement)
    
Return the `k`-th symmetric power of `F`. Here, `k` can contain parameters.
"""
function symmetric_power(F::AbstractBundle, k::Int)
  AbstractBundle(F.parent, _sym(k, chern_character(F))[end])
end

function symmetric_power(F::AbstractBundle, k::RingElement)
  X = F.parent
  PF = abstract_projective_bundle(dual(F))
  p = PF.struct_map
  AbstractBundle(X, p.pushforward(sum((chern_character(line_bundle(PF, k)) * todd_class(p))[0:PF.dim])))
end

@doc raw"""
    schur_functor(F::AbstractBundle, λ::Vector{Int})
    schur_functor(F::AbstractBundle, λ::Partition)

Return the result of the Schur functor $\mathbf S^\lambda$.
"""
function schur_functor(F::AbstractBundle, λ::Vector{Int}) schur_functor(F, partition(λ)) end
function schur_functor(F::AbstractBundle, λ::Partition)
  λ = conjugate(λ)
  X = F.parent
  w = _wedge(sum(λ), chern_character(F))
  S, ei = polynomial_ring(QQ, ["e$i" for i in 1:length(w)])
  e = i -> i < 0 ? S() : ei[i+1]
  M = [e(λ[i]-i+j) for i in 1:length(λ), j in 1:length(λ)]
  sch = det(matrix(S, M)) # Jacobi-Trudi
  R = X.ring
  if R isa MPolyQuoRing
    # StoX = hom(S, R.R.R, [wi.f.f for wi in w])
    StoX = hom(S, base_ring(R).R, [wi.f.f for wi in w])
    # return AbstractBundle(X, X(R.R(StoX(sch))))
    return AbstractBundle(X, X(base_ring(R)(StoX(sch))))
  else
    StoX = hom(S, R.R, [wi.f for wi in w])
    return AbstractBundle(X, X(StoX(sch)))
  end
end

function giambelli(F::AbstractBundle, λ::Vector{Int})
  R = F.parent.ring
  M = [chern_class(F, λ[i]-i+j).f for i in 1:length(λ), j in 1:length(λ)]
  R(det(matrix(R, M)))
end

###############################################################################
#
# Various computations
#
@doc raw"""
    basis(X::AbstractVariety)

Return an additive basis of the Chow ring of `X`, grouped by increasing
degree (i.e., increasing codimension).
"""
function basis(X::AbstractVariety)
  # it is important for this to be cached!
  return get_attribute!(X, :basis) do
    R = X.ring
    try_trim = "Try use `trim!`."
    !(R isa MPolyQuoRing) && error("the ring has no ideal. "*try_trim)
    dim(R.I) > 0 && error("the ideal is not 0-dimensional. "*try_trim)
    b = Oscar._kbase(R)
    ans = [MPolyQuoRingElem[] for i in 0:X.dim]
    for bi in b
      push!(ans[_total_degree(bi)+1], R(bi))
    end
    return ans
  end
end

@doc raw"""
    basis(k::Int, X::AbstractVariety)

Return an additive basis of the Chow ring of `X` in codimension `k`.
"""
basis(X::AbstractVariety, k::Int) = basis(X)[k+1]

@doc raw"""
    betti(X::AbstractVariety)

Return the Betti numbers of the Chow ring of `X`. Note that these are not
necessarily equal to the usual Betti numbers, i.e., the dimensions of
(co)homologies.
"""
betti(X::AbstractVariety) = length.(basis(X))

@doc raw"""
    integral(x::MPolyDecRingElem)

Compute the integral of a Chow ring element.

If the abstract_variety `X` has a (unique) point class `X.point`, the integral will be a
number (an `QQFieldElem` or a function field element). Otherwise the 0-dimensional
part of $x$ is returned.
"""
function integral(x::MPolyDecRingOrQuoElem)
  X = get_attribute(parent(x), :abstract_variety)
  if isdefined(X, :point) && length(basis(X, X.dim)) == 1
    return constant_coefficient(div(simplify(x).f, simplify(X.point).f))
  else
    return x[X.dim]
  end
end

@doc raw"""
    intersection_matrix(a::Vector)
    intersection_matrix(a::Vector, b::Vector)
    intersection_matrix(X::AbstractVariety)

Compute the intersection matrix among entries of a vector $a$ of Chow ring
elements, or between two vectors $a$ and $b$. For a abstract_variety `X`, this computes
the intersection matrix of the additive basis given by `basis(X)`.
"""
function intersection_matrix(X::AbstractVariety) intersection_matrix(vcat(basis(X)...)) end
function intersection_matrix(a::Vector{}, b=nothing)
  if b === nothing b = a end
  matrix([integral(ai*bj) for ai in a, bj in b])
end

@doc raw"""
    dual_basis(k::Int, X::AbstractVariety)

Compute the dual basis of the additive basis in codimension `k` given by
`basis(X, k)` (the returned elements are therefore in codimension
$\dim X-k$).
"""
function dual_basis(X::AbstractVariety, k::Int)
  d = get_attribute!(X, :dual_basis) do
    d = Dict{Int, Vector{elem_type(X.ring)}}()
    return d
  end
  if !(k in keys(d))
    B = basis(X)
    b_k = B[k+1]
    b_comp = B[X.dim-k+1]
    M = Matrix(inv(intersection_matrix(b_comp, b_k)))
    d[k] = M * b_comp
    d[X.dim-k] = transpose(M) * b_k
  end
  return d[k]
end

@doc raw"""
    dual_basis(X::AbstractVariety)

Compute the dual basis with respect to the additive basis given by `basis(X)`,
grouped by decreasing degree (i.e., decreasing codimension).
"""
dual_basis(X::AbstractVariety) = [dual_basis(X, k) for k in 0:X.dim]

# the parameter for truncation is usually the dimension, but can also be set
# manually, which is used when computing particular Chern classes (without
# computing the total Chern class)
function _expp(x::MPolyDecRingOrQuoElem; truncate::Int=-1)
  R = parent(x)
  n = truncate < 0 ? get_attribute(R, :abstract_variety_dim) : truncate
  comps = x[0:n]
  p = [(-1)^i * factorial(ZZ(i)) * comps[i+1] for i in 0:n]
  e = repeat([R(0)], n+1)
  e[1] = R(1)
  for i in 1:n
    e[i+1] = QQ(-1, i) * sum(p[j+1] * e[i-j+1] for j in 1:i)
  end
  simplify(sum(e))
end

function _logg(x::MPolyDecRingOrQuoElem)
  R = parent(x)
  n = get_attribute(R, :abstract_variety_dim)
  n == 0 && return R()
  e = x[1:n]
  p = pushfirst!(repeat([R()], n-1), -e[1])
  for i in 1:n-1
    p[i+1] = -ZZ(i+1)*e[i+1] - sum(e[j] * p[i-j+1] for j in 1:i)
  end
  simplify(sum((-1)^i//factorial(ZZ(i))*p[i] for i in 1:n))
end

# returns all the wedge from 0 to k
function _wedge(k::Int, x::MPolyDecRingOrQuoElem)
  R = parent(x)
  k == 0 && return [R(1)]
  n = get_attribute(R, :abstract_variety_dim)
  wedge = repeat([R(0)], k+1)
  wedge[1] = R(1)
  wedge[2] = x
  for j in 2:k
    wedge[j+1] = 1//ZZ(j) * sum(sum((-1)^(j-i+1) * wedge[i+1] * adams(j-i, x) for i in 0:j-1)[0:n])
  end
  wedge
end

# returns all the sym from 0 to k
function _sym(k::Int, x::MPolyDecRingOrQuoElem)
  R = parent(x)
  k == 0 && return [R(1)]
  n = get_attribute(R, :abstract_variety_dim)
  r = min(k, Int(ZZ(QQ(constant_coefficient(x.f)))))
  wedge = _wedge(r, x)
  sym = repeat([R(0)], k+1)
  sym[1] = R(1)
  sym[2] = x
  for j in 2:k
    sym[j+1] = sum(sum((-1)^(i+1) * wedge[i+1] * sym[j-i+1] for i in 1:min(j,r))[0:n])
  end
  sym
end

function _genus(x::MPolyDecRingOrQuoElem, taylor::Vector{})
  R = parent(x)
  iszero(x) && return R(1)
  n = get_attribute(R, :abstract_variety_dim)
  R, (t,) = graded_polynomial_ring(QQ, ["t"])
  set_attribute!(R, :abstract_variety_dim, n)
  lg = _logg(R(sum(taylor[i+1] * t^i for i in 0:n)))
  comps = lg[1:n]
  lg = [iszero(comps[i].f) ? zero(coefficient_ring(comps[i].f)) : leading_coefficient(comps[i].f) for i in 1:n]
  comps = x[1:n]
  _expp(sum(factorial(ZZ(i)) * lg[i] * comps[i] for i in 1:n))
end

function _todd_class(x::MPolyDecRingOrQuoElem)
  n = get_attribute(parent(x), :abstract_variety_dim)
  # the Taylor series of t/(1-exp(-t))
  taylor = [(-1)^i//factorial(ZZ(i))*bernoulli(i) for i in 0:n]
  _genus(x, taylor)
end

function _l_genus(x::MPolyDecRingOrQuoElem)
  n = get_attribute(parent(x), :abstract_variety_dim)
  # the Taylor series of sqrt(t)/tanh(sqrt(t))
  taylor = [ZZ(2)^2i//factorial(ZZ(2i))*bernoulli(2i) for i in 0:n]
  _genus(x, taylor)
end

function _a_hat_genus(x::MPolyDecRingOrQuoElem)
  n = get_attribute(parent(x), :abstract_variety_dim)
  # the Taylor series of (sqrt(t)/2)/sinh(sqrt(t)/2)
  R, t = power_series_ring(QQ, 2n+1, "t")
  s = divexact(t, exp(QQ(1//2)*t)-exp(-QQ(1//2)*t))
  taylor = [coeff(s, 2i) for i in 0:n]
  _genus(x, taylor)
end

for (g,s) in [:a_hat_genus=>"p", :l_genus=>"p", :todd_class=>"c"]
  _g = Symbol("_", g)
  @eval function $g(n::Int)
    n == 0 && return QQ(1)
    R, p = graded_polynomial_ring(QQ, _parse_symbol($s, 1:n), collect(1:n))
    set_attribute!(R, :abstract_variety_dim, n)
    $_g(_logg(R(1+sum(p))))[n]
  end
end

@doc raw"""
    todd_class(n::Int)

Compute the (generic) $n$-th Todd genus.
"""
todd_class(n::Int)

@doc raw"""
    l_genus(n::Int)

Compute the (generic) $n$-th L genus.
"""
l_genus(n::Int)

@doc raw"""
    a_hat_genus(n::Int)

Compute the (generic) $n$-th $\hat A$ genus.
"""
a_hat_genus(n::Int)

@doc raw"""
    zero_locus_section(F::AbstractBundle; class::Bool = false)

Return the zero locus of a general section of `F`.

Use the argument `class = true` to only compute the class of the zero locus (same
as `top_chern_class(F)`).

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> C = zero_locus_section(OO(P2, 3)) # a plane cubic curve
AbstractVariety of dim 1

julia> dim(C)
1

julia> degree(C)
3

```
```
julia> P3 = abstract_projective_space(3)
AbstractVariety of dim 3

julia> C = zero_locus_section(OO(P3, 2) + OO(P3, 2)) # a complete intersection
AbstractVariety of dim 1

julia> dim(C)
1

julia> degree(C)
4

```

```
julia> P4 = abstract_projective_space(4)
AbstractVariety of dim 4

julia> h = gens(P4)[1]
h

julia> F = abstract_bundle(P4, 2, 10*h^2 + 5*h + 1) # Horrocks-Mumford bundle
AbstractBundle of rank 2 on AbstractVariety of dim 4

julia> A = zero_locus_section(F) # abelian surface
AbstractVariety of dim 2

julia> dim(A)
2

julia> degree(A)
10

```
"""
function zero_locus_section(F::AbstractBundle; class::Bool=false)
  X = parent(F)
  R = X.ring
  cZ = top_chern_class(F)
  # return only the class of Z in the chow ring of X
  class && return cZ
  if R isa MPolyQuoRing
    I = quotient(modulus(R), ideal(base_ring(R), [cZ.f]))
    AZ = quo(base_ring(R), I)[1]
  else
    AZ = R
  end
  Z = AbstractVariety(X.dim - F.rank, AZ)
  if isdefined(X, :point)
    ps = basis(Z, Z.dim) # the 0-cycles
    @assert length(ps) == 1 # make sure that the 0-cycle is unique
    p = ps[1]
    degp = integral(R(p.f) * cZ) # compute the degree of iₓp
    Z.point = Z(inv(degp) * p.f)
  end
  if isdefined(X, :T)
    Z.T = AbstractBundle(Z, Z((chern_character(X.T) - chern_character(F)).f))
  end
  if isdefined(X, :O1)
    Z.O1 = Z(X.O1.f)
  end
  iₓ = x -> x.f * cZ
  iₓ = map_from_func(iₓ, Z.ring, X.ring)
  @assert R isa MPolyQuoRing
  i = AbstractVarietyMap(Z, X, Z.(gens(base_ring(R))), iₓ)
  i.T = pullback(i, -F)
  Z.struct_map = i
  set_attribute!(Z, :description, "Zero locus of a section of $F")
  return Z
end

@doc raw"""
    complete_intersection(X::AbstractVariety, degs::Int...)
    complete_intersection(X::AbstractVariety, degs::Vector{Int})

Return the complete intersection in `X` of general hypersurfaces with
the given degrees.

# Examples
```jldoctest
julia> P3 = abstract_projective_space(3)
AbstractVariety of dim 3

julia> CI = complete_intersection(P3, 2, 2)
AbstractVariety of dim 1

julia> dim(CI)
1

julia> degree(CI)
4

```
"""
complete_intersection(X::AbstractVariety, degs::Int...) = complete_intersection(X, collect(degs))
complete_intersection(X::AbstractVariety, degs::Vector{Int}) = (
  Y = zero_locus_section(sum(line_bundle(X, d) for d in degs));
  set_attribute!(Y, :description => "Complete intersection of degree $(tuple(degs...)) in $X");
  Y)

@doc raw"""
    degeneracy_locus(F::AbstractBundle, G::AbstractBundle, k::Int; class::Bool=false)

Return the `k`-th degeneracy locus of a general map from `F` to `G`.

Use the argument `class = true` to only compute the class of the degeneracy locus (Porteous' formula).

# Examples
```jldoctest
julia> P4 = abstract_projective_space(4, symbol = "H")
AbstractVariety of dim 4

julia> F = 2*OO(P4, -1)
AbstractBundle of rank 2 on AbstractVariety of dim 4

julia> G = OO(P4)+2*OO(P4, 1)
AbstractBundle of rank 3 on AbstractVariety of dim 4

julia> CZ = degeneracy_locus(F, G, 1, class = true) # only class of degeneracy locus
8*H^2

julia> CZ == chern_class(G-F, 2) # Porteous' formula
true

```
"""
function degeneracy_locus(F::AbstractBundle, G::AbstractBundle, k::Int; class::Bool=false)
  F, G = _coerce(F, G)
  m, n = rank(F), rank(G)
  @assert k < min(m,n)
  if class
    # return only the class of D in the chow ring of X
    if (m-k)*(n-k) <= F.parent.dim # Porteous' formula
      return chern_character(schur_functor(G-F, repeat([m-k], n-k)))[(m-k)*(n-k)]
    else # expected dimension is negative
      return F.parent.ring(0)
    end
  end
  Gr = (m-k == 1) ? abstract_projective_bundle(F) : abstract_flag_variety(F, m-k)
  S = Gr.bundles[1]
  D = zero_locus_section(dual(S) * G)
  D.struct_map = hom(D, F.parent) # skip the flag abstract_variety
  set_attribute!(D, :description, "Degeneracy locus of rank $k from $F to $G")
  return D
end

###############################################################################
@doc raw"""
    abstract_point()

Return an abstract variety consisting of a point.

# Examples
```jldoctest
julia> p = abstract_point()
AbstractVariety of dim 0

julia> chow_ring(p)
Quotient
  of multivariate polynomial ring in 1 variable over QQ graded by
    p -> [1]
  by ideal (p)
```
"""
function abstract_point(; base::Ring=QQ)
  R, (p,) = graded_polynomial_ring(base, ["p"])
  I = ideal([p])
  pt = AbstractVariety(0, quo(R, I)[1])
  pt.point = pt(1)
  pt.T = AbstractBundle(pt, pt(0))
  pt.O1 = pt(0)
  set_attribute!(pt, :description, "Point")
  set_attribute!(pt, :point, true)
  return pt
end

@doc raw"""
    abstract_projective_space(n::Int; base::Ring = QQ, symbol::String = "h")

Return the abstract projective space of lines in an `n+1`-dimensional vector space.

# Examples
```jldoctest
julia> P3 = abstract_projective_space(3)
AbstractVariety of dim 3

julia> chow_ring(P3)
Quotient
  of multivariate polynomial ring in 1 variable over QQ graded by
    h -> [1]
  by ideal (h^4)
```

```jldoctest
julia> T, (s,t) = polynomial_ring(QQ, ["s", "t"])
(Multivariate polynomial ring in 2 variables over QQ, QQMPolyRingElem[s, t])

julia> QT = fraction_field(T)
Fraction field
  of multivariate polynomial ring in 2 variables over QQ

julia> P3 = abstract_projective_space(3, base = QT)
AbstractVariety of dim 3

julia> chow_ring(P3)
Quotient
  of multivariate polynomial ring in 1 variable over QT graded by
    h -> [1]
  by ideal (h^4)

julia> TB = tangent_bundle(P3)
AbstractBundle of rank 3 on AbstractVariety of dim 3

julia> CTB = cotangent_bundle(P3)
AbstractBundle of rank 3 on AbstractVariety of dim 3

julia> chern_character((s*TB)*(t*CTB))
-4*s*t*h^2 + 9*s*t

```
"""
function abstract_projective_space(n::Int; base::Ring=QQ, symbol::String="h")
  R, (h,) = graded_polynomial_ring(base, [symbol])
  I = ideal([h^(n+1)])
  AP = quo(R, I)[1]
  P = AbstractVariety(n, AP)
  h = P(h)
  P.point = h^n
  P.O1 = h
  chTP = P(n)
  for i in 1:n chTP += ZZ(n+1)//factorial(ZZ(i))*h^i end
  P.T = AbstractBundle(P, chTP)
  P.T.chern = (1+h)^(n+1)
  S = AbstractBundle(P, 1, 1-h)
  Q = trivial_line_bundle(P)*(n+1) - S
  P.bundles = [S, Q]
  P.struct_map = hom(P, abstract_point(base=base), [P(1)])
  set_attribute!(P, :description => "Projective space of dim $n")
  set_attribute!(P, :grassmannian => :absolute)
  set_attribute!(P, :alg => true)
  return P
end

@doc raw"""
    abstract_projective_bundle(F::AbstractBundle; symbol::String = "h")

Return the projective bundle of 1-dimensional subspaces in the fibers of `F`.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> T = tangent_bundle(P2)
AbstractBundle of rank 2 on AbstractVariety of dim 2

julia> E = abstract_projective_bundle(T, symbol = "H")
AbstractVariety of dim 3

julia> chow_ring(E)
Quotient
  of multivariate polynomial ring in 2 variables over QQ graded by
    H -> [1]
    h -> [1]
  by ideal (h^3, H^2 + 3*H*h + 3*h^2)

julia> [chern_class(T, i) for i = 1:2]
2-element Vector{MPolyQuoRingElem{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}}:
 3*h
 3*h^2

```

```jldoctest
julia> G = abstract_grassmannian(3, 5)
AbstractVariety of dim 6

julia> USBd = dual(tautological_bundles(G)[1])
AbstractBundle of rank 3 on AbstractVariety of dim 6

julia> F = symmetric_power(USBd, 2)
AbstractBundle of rank 6 on AbstractVariety of dim 6

julia> PF = abstract_projective_bundle(F)
AbstractVariety of dim 11

julia> A = symmetric_power(USBd, 5) - symmetric_power(USBd, 3)*OO(PF, -1)
AbstractBundle of rank 11 on AbstractVariety of dim 11

julia> integral(top_chern_class(A))
609250

```
"""
function abstract_projective_bundle(F::AbstractBundle; symbol::String = "h")
  X, r = F.parent, F.rank
  !(r isa Int) && error("expect rank to be an integer")
  R = X.ring
  syms = vcat([symbol], string.(gens(R)))
  # FIXME add product ordering
  # ord = ordering_dp(1) * R.R.ord
  # construct the ring
  w = vcat([1], gradings(R))
  R1, (h,) = graded_polynomial_ring(X.base, syms, w)
  # TODO: why does this fail with check = true
  pback = hom(R, R1, gens(R1)[2:end], check = false)
  pfwd = hom(R1, R, pushfirst!(gens(R), R()))
  # construct the ideal
  rels = [sum(pback(chern_class(F, i)) * h^(r-i) for i in 0:r)]
  if R isa MPolyQuoRing rels = vcat(pback.(R.(gens(R.I))), rels) end
  APF = quo(R1, ideal(rels))[1]
  h = APF(h)
  # construct the abstract_variety
  PF = AbstractVariety(X.dim+r-1, APF)
  pₓ = x -> X(pfwd(div(simplify(x).f, simplify(PF(h^(r-1))).f)))
  pₓ = map_from_func(pₓ, PF.ring, X.ring)
  p = AbstractVarietyMap(PF, X, PF.(gens(R1)[2:end]), pₓ)
  if isdefined(X, :point) PF.point = p.pullback(X.point) * h^(r-1) end
  p.O1 = PF(h)
  PF.O1 = PF(h)
  S = AbstractBundle(PF, 1, 1-h)
  Q = pullback(p, F) - S
  p.T = dual(S)*Q
  if isdefined(X, :T) PF.T = pullback(p, X.T) + p.T end
  PF.bundles = [S, Q]
  PF.struct_map = p
  set_attribute!(PF, :description => "Projectivization of $F")
  set_attribute!(PF, :grassmannian => :relative)
  return PF
end

@doc raw"""
    abstract_grassmannian(k::Int, n::Int; base::Ring = QQ, symbol::String = "c")

Return the abstract Grassmannian $\mathrm{Gr}(k, n)$ of `k`-dimensional subspaces of an 
`n`-dimensional vector space.

# Examples
```jldoctest
julia> G = abstract_grassmannian(2,4)
AbstractVariety of dim 4

julia> chow_ring(G)
Quotient
  of multivariate polynomial ring in 2 variables over QQ graded by
    c[1] -> [1]
    c[2] -> [2]
  by ideal (-c[1]^3 + 2*c[1]*c[2], c[1]^4 - 3*c[1]^2*c[2] + c[2]^2)

```
"""
function abstract_grassmannian(k::Int, n::Int; base::Ring = QQ, symbol::String = "c")
  @assert k < n
 
  d = k*(n-k)
  R, c = graded_polynomial_ring(base, _parse_symbol(symbol, 1:k), collect(1:k))
  inv_c = sum((-sum(c))^i for i in 1:n) # this is c(Q) since c(S)⋅c(Q) = 1
  # Q is of rank n-k: the vanishing of Chern classes in higher degrees provides all the relations for the Chow ring
  AGr = quo(R, ideal(inv_c[n-k+1:n]))[1]
  c = gens(AGr)
  Gr = AbstractVariety(d, AGr)
  Gr.O1 = Gr(-c[1])
  S = AbstractBundle(Gr, k, 1 + sum(c))
  Q = trivial_line_bundle(Gr)*n - S
  Q.chern = 1 + Gr(sum(inv_c[1:n-k]))
  Gr.point = Gr((-1)^d*c[end]^(n-k))
  Gr.T = dual(S) * Q
  Gr.bundles = [S, Q]
  Gr.struct_map = hom(Gr, abstract_point(base=base), [Gr(1)])
  set_attribute!(Gr, :description => "Grassmannian Gr($k, $n)")
  set_attribute!(Gr, :grassmannian => :absolute)
  set_attribute!(Gr, :alg => true)
  return Gr
end

@doc raw"""
    abstract_flag_variety(dims::Int...; base::Ring = QQ, symbol::String = "c")
    abstract_flag_variety(dims::Vector{Int}; base::Ring = QQ, symbol::String = "c")

Given integers, say, $d_1, \dots, d_{k}, n$ or a vector of such integers, return the abstract 
flag variety $\mathrm{F}(d_1, \dots, d_{k}; n)$ of nested sequences of subspaces of dimensions 
$d_1; \dots, d_{k}$ of an $n$-dimensional vector space.

# Examples
```jldoctest
julia> F = abstract_flag_variety(1,3,4)
AbstractVariety of dim 5

julia> chow_ring(F)
Quotient
  of multivariate polynomial ring in 4 variables over QQ graded by
    c[1, 1] -> [1]
    c[2, 1] -> [1]
    c[2, 2] -> [2]
    c[3, 1] -> [1]
  by ideal with 4 generators

```
"""
function abstract_flag_variety(dims::Int...; bott::Bool=false, weights=:int, base::Ring=QQ, symbol::String="c")
  abs_flag(collect(dims), base=base, symbol=symbol)
end

function abstract_flag_variety(dims::Vector{Int}; bott::Bool=false, weights=:int, base::Ring=QQ, symbol::String="c")
  abs_flag(dims, base=base, symbol=symbol)
end

function abs_flag(dims::Vector{Int}; base::Ring=QQ, symbol::String="c")
  n, l = dims[end], length(dims)
  ranks = pushfirst!([dims[i+1]-dims[i] for i in 1:l-1], dims[1])
  @assert all(r->r>0, ranks)
  d = sum(ranks[i] * sum(dims[end]-dims[i]) for i in 1:l-1)
  syms = vcat([_parse_symbol(symbol, i, 1:r) for (i,r) in enumerate(ranks)]...)
  # FIXME ordering
  # ord = prod(ordering_dp(r) for r in ranks)
  R = graded_polynomial_ring(base, syms, vcat([collect(1:r) for r in ranks]...))[1]
  c = pushfirst!([1+sum(gens(R)[dims[i]+1:dims[i+1]]) for i in 1:l-1], 1+sum(gens(R)[1:dims[1]]))
  gi = prod(c)[0:n]
  # XXX cannot mod using graded ring element
  Rx, x = R.R["x"]
  g = sum(gi[i+1].f * x^(n-i) for i in 0:n)
  q = mod(x^n, g)
  rels = [R(coeff(q, i)) for i in 0:n-1]
  AFl = quo(R, ideal(rels))[1]
  c = AFl.(c)
  Fl = AbstractVariety(d, AFl)
  Fl.bundles = [AbstractBundle(Fl, r, ci) for (r,ci) in zip(ranks, c)]
  Fl.O1 = simplify(sum((i-1)*chern_class(Fl.bundles[i], 1) for i in 1:l))
  Fl.point = prod(top_chern_class(E)^dims[i] for (i,E) in enumerate(Fl.bundles[2:end]))
  Fl.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  Fl.struct_map = hom(Fl, abstract_point(base=base), [Fl(1)])
  set_attribute!(Fl, :description => "Flag abstract_variety Flag$(tuple(dims...))")
  if l == 2 set_attribute!(Fl, :grassmannian => :absolute) end
  set_attribute!(Fl, :alg => true)
  # if all(r->r==1, ranks)
  #   set_attribute!(Fl, :weyl_group => WeylGroup("A$(n-1)"))
  #   set_attribute!(Fl, :roots => -[c[i] - c[i+1] for i in 1:n-1])
  # end
  return Fl
end

@doc raw"""
    abstract_flag_variety(F::AbstractBundle, dims::Int...; symbol::String = "c")
    abstract_flag_variety(F::AbstractBundle, dims::Vector{Int}; symbol::String = "c")

Given integers, say, $d_1, \dots, d_{k}$ or a vector of such integers, and given an
abstract bundle $F$, return the abstract flag variety (flag bundle) of nested sequences 
of subspaces of dimensions $d_1; \dots, d_{k}$ in the fibers of $F$.
"""
function abstract_flag_variety(F::AbstractBundle, dims::Int...; symbol::String = "c")
  abstract_flag_variety(F, collect(dims), symbol=symbol)
end

function abstract_flag_variety(F::AbstractBundle, dims::Vector{Int}; symbol::String="c")
  X, n = F.parent, F.rank
  !(n isa Int) && error("expect rank to be an integer")
  # compute the ranks and relative dim
  l = length(dims)
  ranks = pushfirst!([dims[i+1]-dims[i] for i in 1:l-1], dims[1])
  @assert all(r->r>0, ranks) && dims[end] <= n
  if dims[end] < n # the last dim can be omitted
    dims = vcat(dims, [n])
    push!(ranks, n-dims[l])
    l += 1
  end
  d = sum(ranks[i] * sum(dims[end]-dims[i]) for i in 1:l-1)
  # FIXME ordering
  # construct the ring
  R = X.ring
  if R isa MPolyQuoRing
    PR = base_ring(R)
  else
    PR = R
  end
  # syms = vcat([_parse_symbol(symbol, i, 1:r) for (i,r) in enumerate(ranks)]..., string.(gens(R.R)))
  syms = vcat([_parse_symbol(symbol, i, 1:r) for (i,r) in enumerate(ranks)]..., string.(gens(PR)))
  # ord = prod(ordering_dp(r) for r in ranks) * ordering(X.ring.R.R)
  w = vcat([collect(1:r) for r in ranks]..., gradings(R))
  R1 = graded_polynomial_ring(X.base, syms, w)[1]
  pback = hom(R, R1, gens(R1)[n+1:end])   # FIXME should always be well-defined
  pfwd = hom(R1, R, vcat(repeat([R()], n), gens(R)))
  
  # compute the relations
  c = pushfirst!([1+sum(gens(R1)[dims[i]+1:dims[i+1]]) for i in 1:l-1], 1+sum(gens(R1)[1:dims[1]]))
  # XXX cannot mod using graded ring element
  Rx, x = R1.R["x"]
  fi = pback(total_chern_class(F))[0:n]
  f = sum(fi[i+1].f * x^(n-i) for i in 0:n)
  gi = prod(c)[0:n]
  g = sum(gi[i+1].f * x^(n-i) for i in 0:n)
  rels = [R1(coeff(mod(f, g), i)) for i in 0:n-1]
  if R isa MPolyQuoRing rels = vcat(pback.(R.(gens(R.I))), rels) end
  AFl = quo(R1, ideal(rels))[1]
  c = AFl.(c)
  Fl = AbstractVariety(X.dim + d, AFl)
  
  Fl.bundles = [AbstractBundle(Fl, r, ci) for (r,ci) in zip(ranks, c)]
  section = prod(top_chern_class(E)^sum(dims[i]) for (i, E) in enumerate(Fl.bundles[2:end]))
  if isdefined(X, :point)
    Fl.point = pback(X.point) * section
  end
  pˣ = Fl.(gens(R1)[n+1:end])
  pₓ = x -> (@warn("possibly wrong ans"); X(pfwd(div(simplify(x).f, simplify(section).f))))
  pₓ = map_from_func(pₓ, Fl.ring, X.ring)
  p = AbstractVarietyMap(Fl, X, pˣ, pₓ)
  p.O1 = simplify(sum((i-1)*chern_class(Fl.bundles[i], 1) for i in 1:l))
  Fl.O1 = p.O1
  p.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  if isdefined(X, :T)
    Fl.T = pullback(p, X.T) + p.T
  end
  Fl.struct_map = p
  set_attribute!(Fl, :description => "Relative flag abstract_variety Flag$(tuple(dims...)) for $F")
  set_attribute!(Fl, :section => section)
  if l == 2 set_attribute!(Fl, :grassmannian => :relative) end
  return Fl
end

@doc raw"""
    schubert_class(G::AbstractVariety, λ::Int...)
    schubert_class(G::AbstractVariety, λ::Vector{Int})
    schubert_class(G::AbstractVariety, λ::Partition)

Return the Schubert class $\sigma_\lambda$ on a (relative) Grassmannian $G$.
"""
function schubert_class(G::AbstractVariety, λ::Int...) schubert_class(G, collect(λ)) end
function schubert_class(G::AbstractVariety, λ::Partition) schubert_class(G, Vector(λ)) end
function schubert_class(G::AbstractVariety, λ::Vector{Int})
  get_attribute(G, :grassmannian) === nothing && error("the abstract_variety is not a Grassmannian")
  (length(λ) > rank(G.bundles[1]) || sort(λ, rev=true) != λ) && error("the Schubert input is not well-formed")
  giambelli(G.bundles[2], λ)
end

@doc raw"""
    schubert_classes(m::Int, G::AbstractVariety)

Return all the Schubert classes in codimension $m$ on a (relative) Grassmannian $G$.
"""
function schubert_classes(G::AbstractVariety, m::Int)
  get_attribute(G, :grassmannian) === nothing && error("the abstract_variety is not a Grassmannian")
  S, Q = G.bundles
  res = elem_type(G.ring)[]
  for i in 0:rank(S)
    append!(res, [schubert_class(G, l) for l in partitions(m, i, 1, rank(Q))])
  end
  return res
end

