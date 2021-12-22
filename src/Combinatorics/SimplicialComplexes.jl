using Markdown
import Oscar: Polymake, pm_object

export
    SimplicialComplex,
    betti_numbers,
    dim,
    euler_characteristic,
    facets,
    f_vector,
    h_vector,
    minimal_nonfaces,
    nvertices,
    stanley_reisner_ideal,
    stanley_reisner_ring,
    load_simplicialcomplex,
    save_simplicialcomplex,
    complexprojectiveplane,
    realprojectiveplane,
    klein_bottle,
    torus # requires a distinction from, e.g., an algebraic group

################################################################################
##  Constructing
################################################################################

struct SimplicialComplex
    pm_simplicialcomplex::Polymake.BigObject
end

pm_object(K::SimplicialComplex) = K.pm_simplicialcomplex


@doc Markdown.doc"""
    SimplicialComplex(generators::Vector{Vector{Int}})

Construct an abstract simplicial complex from a set of faces.
While arbitrary nonnegative integers are allowed as vertices, they will be relabeled to consecutive integers starting at 1.

# Example
```jldoctest
julia> K = SimplicialComplex([[1,2,3],[2,3,4]])
Abstract simplicial complex of dimension 2 on 4 vertices
```
# Example with relabeling
The original vertices can be recovered later.
```jldoctest
julia> L = SimplicialComplex([[0,2,17],[2,17,90]]);

julia> facets(L)
2-element Vector{Vector{Int64}}:
 [1, 3, 2]
 [3, 4, 2]

julia> Oscar._vertexindices(Oscar.pm_object(L))
4-element Vector{Int64}:
  0
  2
 17
 90
```
"""
function SimplicialComplex(generators::Vector{Vector{Int}})
    K = Polymake.topaz.SimplicialComplex(INPUT_FACES=generators)
    SimplicialComplex(K)
end

function SimplicialComplex(generators::Vector{Set{Int}})
    K = Polymake.topaz.SimplicialComplex(INPUT_FACES=generators)
    SimplicialComplex(K)
end

################################################################################
##  Auxiliary
################################################################################

function _vertexindices(K::Polymake.BigObject)
    if Polymake.exists(K,"VERTEX_INDICES")
        return Vector{Int}(K.VERTEX_INDICES)
    else
        return Vector{Int}(1:K.N_VERTICES)
    end
end

_reindexset(M::Set{Int}, ind::Vector{Int}) = [ ind[x+1] for x in M ]

function _characteristic_vector(M::Set{Int}, n::Int)
    chi = zeros(Int, n)
    for x in M
        chi[x] = 1
    end
    return chi
end

################################################################################
##  Properties
################################################################################

@doc Markdown.doc"""
    nvertices(K::SimplicialComplex)

Number of vertices of the abstract simplicial complex `K`.
"""
nvertices(K::SimplicialComplex) = pm_object(K).N_VERTICES

@doc Markdown.doc"""
    facets(K::SimplicialComplex)

Maximal (by inclusion) faces of the abstract simplicial complex `K`.
"""
function facets(K::SimplicialComplex)
    bigobject = pm_object(K)
    the_facets = Vector{Set{Int}}(bigobject.FACETS)
    return Polymake.to_one_based_indexing(the_facets)
end

@doc Markdown.doc"""
    dim(K::SimplicialComplex)

Dimension of the abstract simplicial complex `K`.
"""
dim(K::SimplicialComplex) = pm_object(K).DIM

@doc Markdown.doc"""
    f_vector(K::SimplicialComplex)

Face vector (number of faces per dimension) of the abstract simplicial complex `K`.
"""
f_vector(K::SimplicialComplex) = Vector{Int}(pm_object(K).F_VECTOR)

@doc Markdown.doc"""
    f_vector(K::SimplicialComplex)

H-vector of the abstract simplicial complex `K`.
"""
h_vector(K::SimplicialComplex) = Vector{Int}(pm_object(K).H_VECTOR)

@doc Markdown.doc"""
    betti_numbers(K::SimplicialComplex)

Rational Betti numbers of the abstract simplicial complex `K`.
"""
betti_numbers(K::SimplicialComplex) = Polymake.topaz.betti_numbers(pm_object(K))

@doc Markdown.doc"""
    euler_characteristic(K::SimplicialComplex)

Reduced Euler characteristic of the abstract simplicial complex `K`.
"""
euler_characteristic(K::SimplicialComplex) = pm_object(K).EULER_CHARACTERISTIC

@doc Markdown.doc"""
    minimal_nonfaces(K::SimplicialComplex)

Minimal non-faces of the abstract simplicial complex `K`.

# Example
```jldoctest
julia> K = SimplicialComplex([[1,2,3],[2,3,4]]);

julia> minimal_nonfaces(K)
1-element Vector{Vector{Int64}}:
 Set([4, 1])
```
"""
minimal_nonfaces(K::SimplicialComplex) = Vector{Set{Int}}(Polymake.to_one_based_indexing(pm_object(K).MINIMAL_NON_FACES))

@doc Markdown.doc"""
    stanley_reisner_ideal(K::SimplicialComplex)

Stanley-Reisner ideal of the abstract simplicial complex `K`.

# Example
```jldoctest
julia> stanley_reisner_ideal(realprojectiveplane())
ideal(x1*x2*x3, x1*x2*x4, x1*x5*x6, x2*x5*x6, x1*x3*x6, x1*x4*x5, x3*x4*x5, x3*x4*x6, x2*x3*x5, x2*x4*x6)
```
"""
function stanley_reisner_ideal(K::SimplicialComplex)
    n = nvertices(K)
    R, () = PolynomialRing(ZZ, n)
    return stanley_reisner_ideal(R, K)
end

@doc Markdown.doc"""
    stanley_reisner_ideal(R::FmpzMPolyRing, K::SimplicialComplex)

Stanley-Reisner ideal of the abstract simplicial complex `K`, in the given ring `R`.

# Example
```jldoctest
julia> R, () = ZZ["a","b","c","d","e","f"];

julia> stanley_reisner_ideal(R, realprojectiveplane())
ideal(a*b*c, a*b*d, a*e*f, b*e*f, a*c*f, a*d*e, c*d*e, c*d*f, b*c*e, b*d*f)
```
"""
function stanley_reisner_ideal(R::FmpzMPolyRing, K::SimplicialComplex)
    n = nvertices(K)
    return ideal([ R([1], [_characteristic_vector(f,n)]) for f in minimal_nonfaces(K) ])
end

@doc Markdown.doc"""
    stanley_reisner_ring(K::SimplicialComplex)

Stanley-Reisner ring of the abstract simplicial complex `K`.

# Example
```jldoctest
julia> K = SimplicialComplex([[1,2,3],[2,3,4]]);

julia> stanley_reisner_ring(K)
(Quotient of Multivariate Polynomial Ring in x1, x2, x3, x4 over Integer Ring by ideal(x1*x4), Map from
Multivariate Polynomial Ring in x1, x2, x3, x4 over Integer Ring to Quotient of Multivariate Polynomial Ring in x1, x2, x3, x4 over Integer Ring by ideal(x1*x4) defined by a julia-function with inverse)
```
"""
function stanley_reisner_ring(K::SimplicialComplex)
    n = nvertices(K)
    R, () = PolynomialRing(ZZ, n)
    return stanley_reisner_ring(R, K)
end

@doc Markdown.doc"""
    stanley_reisner_ring(R::FmpzMPolyRing, K::SimplicialComplex)

Stanley-Reisner ring of the abstract simplicial complex `K`, as a quotient of a given ring `R`.

# Example
```jldoctest
julia>  R, () = ZZ["a","b","c","d","e","f"];

julia> stanley_reisner_ring(R, realprojectiveplane())
(Quotient of Multivariate Polynomial Ring in 6 variables a, b, c, d, ..., f over Integer Ring by ideal(a*b*c, a*b*d, a*e*f, b*e*f, a*c*f, a*d*e, c*d*e, c*d*f, b*c*e, b*d*f), Map from
Multivariate Polynomial Ring in 6 variables a, b, c, d, ..., f over Integer Ring to Quotient of Multivariate Polynomial Ring in 6 variables a, b, c, d, ..., f over Integer Ring by ideal(a*b*c, a*b*d, a*e*f, b*e*f, a*c*f, a*d*e, c*d*e, c*d*f, b*c*e, b*d*f) defined by a julia-function with inverse)
```
"""
stanley_reisner_ring(R::FmpzMPolyRing, K::SimplicialComplex) = quo(R, stanley_reisner_ideal(R, K))

################################################################################
##  Standard examples
################################################################################

"""
    torus()

Császár's 7-vertex triangulation of the torus (surface).
"""
torus() = SimplicialComplex(Polymake.topaz.torus())

"""
    klein_bottle()

9-vertex triangulation of the Klein bottle.
"""
klein_bottle() = SimplicialComplex(Polymake.topaz.klein_bottle())

"""
    realprojectiveplane()

6-vertex triangulation of the real projective plane.
"""
realprojectiveplane() = SimplicialComplex(Polymake.topaz.real_projective_plane())

"""
    complexprojectiveplane()

9-vertex triangulation of the complex projective plane.
"""
complexprojectiveplane() = SimplicialComplex(Polymake.topaz.complex_projective_plane())

###############################################################################
### Display
###############################################################################

function Base.show(io::IO, K::SimplicialComplex)
    d = dim(K)
    n = nvertices(K)
    print(io, "Abstract simplicial complex of dimension $(d) on $(n) vertices")
end

###############################################################################
### Serialization
###############################################################################

"""
    save_simplicialcomplex(K::SimplicialComplex, filename::String)

Save a SimplicialComplex to a file in JSON format.
"""
function save_simplicialcomplex(K::SimplicialComplex, filename::String)
    bigobject = pm_object(K)
    Polymake.save_bigobject(bigobject, filename)
end

"""
    load_simplicialcomplex(filename::String)

Load a SimplicialComplex stored in JSON format, given the filename as input.
"""
function load_simplicialcomplex(filename::String)
   bigobject = Polymake.load_bigobject(filename)
   typename = Polymake.type_name(bigobject)
   if typename[1:17] != "SimplicialComplex"
      throw(ArgumentError("Loaded object is not of type SimplicialComplex but rather " * typename))
   end
   return SimplicialComplex(bigobject)
end
