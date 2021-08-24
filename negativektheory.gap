LoadPackage("wedderga");



###############################################################################################################################################


MyPartitionSet := function( S, rel )
# This function exists to make the code more readable
# It takes a set S and an equivalence relation on elements of S as input
# rel should be given as a function in two variables
# The output is a list of rel-equivalence classes of elements of S
# This ONLY WORKS if rel is an equivalence relation
# MyPartitionSet does not check if rel is an equivalence relation

local Sprime, classes, s, allobjectsequivtos;
Sprime := S;
classes := [];
while not IsEmpty(Sprime) do
     s:= First(Sprime);
     allobjectsequivtos := Filtered ( Sprime , sprime -> rel(s,sprime) );
     Add(classes, allobjectsequivtos);
     SubtractSet(Sprime, allobjectsequivtos);
od;
return classes;
end;




###############################################################################################################################################


# The following computes the Galois group of Qp(zeta_m) over Qp, where Qp is the field of p-adic rationals and zeta_m is an m-th root of unity.
# The action of an element sigma on Qp(zeta_m) is determined by its image of zeta_m, which must again be a root of unity and hence a power zeta_m^t.
# In order for sigma to be an automorphism, t must be invertible mod p
# This means Gal(Qp(zeta_m) over Qp) can be identified with a subgroup Tm of Units(Z/mZ)
# Gap can compute Units(Z/mZ) with the function PrimeResidues(m)
# If m = p^k * mu, with mu being indivisible by p, there is a natural projection Units(Z/mZ) -> Units(Z/muZ)
# Gal(Qp(zeta_m) over Qp) is given as the preimage of the cyclic subgroup generate by p in Units(Z/muZ)

GaloisGroupOfQpZetamOverQp := function(m, p)    # Gives the Galois group as a subset of prime residues of m
local q, mu, PowersOfPModmu, ZmUnits;
q := p^Length(Filtered(FactorsInt(m) , x -> x = p));
mu := BestQuoInt(m,q);
PowersOfPModmu := List( [1..OrderMod(p,mu)], i -> PowerModInt(p,i,mu) );
return Filtered( PrimeResidues(m), i -> i mod mu in PowersOfPModmu);
end;





###############################################################################################################################################



RationalConjugacyClasses := function(cc)
# This function takes a set of conjugacyclasses as input
# The output is a list of sets of Q-conjugate conjugacy classes of G
# Two elements are rationally conjugate iff the cyclic subgroups they generate are conjugate
# Note: this function has the same functionality as RationalClasses

local orders, m, galoisgroup, ccsortedbyorder, classesoforderi, kconjugate, rationalconjugacyclasses, c, t, allconjugatestoc;
orders := Set(List(cc, c->Order(First(c)) )); # The set of all appearing orders of elements of G
m := Lcm(orders);                             # This is the exponent of G
galoisgroup := PrimeResidues(m);

rationalconjugacyclasses := [];
ccsortedbyorder := List( orders, i -> Filtered( cc , c -> Order(First(c)) = i ) );  # ccSortedByOrder is a list with entries the set of all conjugacy classes of given order i.
for classesoforderi in ccsortedbyorder do
    UniteSet(rationalconjugacyclasses, MyPartitionSet(classesoforderi, {c,d} -> ForAny( galoisgroup , t -> First(c)^t in d ) ));
# We now partition all classes of order i into the set of equivalence classes of conjugacy classes with respect to k conjugacy
od;
return rationalconjugacyclasses;
end;



###############################################################################################################################################


# Suppose G is a group with exponent m. Two elements g and h are Qp-conjugate if g^t is conjugate to h for some t in Tm as computed above
# Since Qp-conjugacy is a coarser relation than conjugacy, we will use the already existing function ConjugacyClasses and compare conjugacy classes in its output.
# Two conjugacy classes c and d merge iff there exists a representative g of c such that g^t is in d for some t in Tm
# We only need to check this for a single given representative

QpConjugate := function(p, c, d, m )
# QpConjugate is an equivalence relation of conjugacy classes of G
# The inputs are a prime p, two conjugacy classes of G (as given by the function ConjugacyClasses), and the exponent m of the group G
local Tm;
# The output is either true or false

Tm := GaloisGroupOfQpZetamOverQp(m,p);        # Gives the Galois group as a subset of prime residues of m
return ForAny( Tm, t->First(c)^t in d) ;      # First(c) is any representative of the conjugacy class c. 
end;


###############################################################################################################################################


QpConjugacyClasses := function(cc,p)
# This function takes a set of conjugacyclasses and a prime p as input
# The output is a list of sets of Qp-conjugate conjugacy classes of G
# An element g is p-singular if p divides its order

local orders, m, ccsortedbyorder, classesoforderi, qpconjugacyclasses;
orders := Set(List(cc, c->Order(First(c)) )); # The set of all appearing orders of elements of G
m := Lcm(orders);                             # This is the exponent of G

qpconjugacyclasses := [];
ccsortedbyorder := List( orders, i -> Filtered( cc , c -> Order(First(c)) = i ) );   # ccSortedByOrder is a list with entries the set of all conjugacy classes of given order i.
for classesoforderi in ccsortedbyorder do
    UniteSet(qpconjugacyclasses, MyPartitionSet(classesoforderi, {c,d} -> QpConjugate(p,c,d,m)) );
# We now partition all classes of order i into the set of equivalence classes of conjugacy classes with respect to Qp conjugacy
od;
return qpconjugacyclasses;
end;



###############################################################################################################################################



SingularQpConjugacyClasses := function(cc,p)
# This function takes a set of conjugacyclasses and a prime p as input
# The output is a list of sets of Qp-conjugate conjugacy classes of G with p-singular order
# An element g is p-singular if p divides its order

local orders, singularorders, m, ccsortedbyorder, classesoforderi, singularqpconjugacyclasses;
orders := Set(List(cc, c->Order(First(c)) )); # The set of all appearing orders of elements of G
m := Lcm(orders);                             # This is the exponent of G

singularorders := Filtered(List(cc, c->Order(First(c)) ), i -> i mod p = 0 );  # We will only look at orders that are multiples of p
                                                                               # First(c) picks a representative element of the conjugacy class c
singularqpconjugacyclasses := [];
ccsortedbyorder := List( singularorders, i -> Filtered( cc , c -> Order(First(c)) = i ) );  # ccSortedByOrder is a list with entries the set of all conjugacy classes of given order i. We only care about orders divisible by p, hence SingularOrders
for classesoforderi in ccsortedbyorder do
    UniteSet(singularqpconjugacyclasses, MyPartitionSet(classesoforderi, {c,d} -> QpConjugate(p,c,d,m) ) );
# We now partition all classes of order i into the set of equivalence classes of conjugacy classes with respect to Qp conjugacy
od;
return singularqpconjugacyclasses;
end;










###############################################################################################################################################

# r is given as 1 - rQ + Sum( # singular Qp conjugacy classes ), where the sum goes over all primes dividing the order of G
# The bottleneck seems to be the computation of the list of conjugacy classes. To save computational time, we compute conjugacyclasses cc of G once and only use cc as input for RationalConjugacyClasses and SingularQpConjugacyClasses
# Any method can be used here. We prefer RandomSearch, since the standard method(used by ConjugacyClasses) seemed to make problems for some of the groups we tested


rOfGroup := function(G)
local primes, rQ, rsingQp, cc;
cc := ConjugacyClassesByRandomSearch(G);
primes := PrimeDivisors(Order(G));
rQ := Length( RationalConjugacyClasses(cc) );
rsingQp := List( primes, p -> Length(SingularQpConjugacyClasses(cc,p)) );
return 1-rQ + Sum(rsingQp);
end;

# SeachAllGroupsForR goes through all groups of order n using the small groups library and prints their values of r
# It refers to the group SmallGroup(n,j) as "Group with index j"
SearchAllGroupsForR := function(n)
local j, r;
for j in [1..Length(AllSmallGroups(n))] do
r := rOfGroup(SmallGroup(n,j));
if r>0 then Print("Group with index ", j, " has r = ", r,"\n"); fi;
od;
end;




###############################################################################################################################################

# s is the number of algebras A appearing in the Wedderburn decomposition of QG that have even Schur index, but odd Schur index at every prime dividing the order of G
# AlgebraContributesToS checks this condition for a single algebra
# The Algebra must be in the form of an output of the function WedderburnDecompositionInfo of the package wedderga
# primes is a list of primes to be checked against

AlgebraContributesToS := function(A,primes)
local RelevantIndices;
if IsEvenInt(SchurIndex(A)) then
RelevantIndices := Filtered( LocalIndicesOfCyclotomicAlgebra(A) , l -> l[1] in primes );
return ForAll(RelevantIndices, l -> IsOddInt( l[2] ) );
else return false; fi;
end;


###############################################################################################################################################


sOfGroup := function(G)
local n, primes, ww, s;
n := Order(G);
primes := PrimeDivisors(n);
ww := WedderburnDecompositionInfo( GroupRing( Rationals, G ) );
s := Number( ww, A -> AlgebraContributesToS(A,primes) );
return s;
end;


# SeachAllGroupsForS goes through all groups of order n using the small groups library and prints their values of s
# It refers to the group SmallGroup(n,j) as "Group with index j"
SearchAllGroupsForS := function(n)
local j, s;
for j in [1..Length(AllSmallGroups(n))] do
s := sOfGroup(SmallGroup(n,j));
if s>0 then Print("Group with index ", j, " has s = ", s,"\n"); fi;
od;
end;



###############################################################################################################################################


IsPHyperElementary := function(G)
local CyclicNormalSubgroups;
CyclicNormalSubgroups := Filtered(NormalSubgroups(G), H -> IsCyclic(H));
return ForAny( CyclicNormalSubgroups, N -> IsPGroup( FactorGroupNC(G,N)) );
end;



KMinusOne := function(G)
return rec(r := rOfGroup(G), s := sOfGroup(G) );
end;


# SeachAllGroupsForKMinusOne goes through all groups of order n using the small groups library and prints their negative K theory as the coefficients r and s
# It refers to the group SmallGroup(n,j) as "Group with index j"
# We added the command StructureDescription to make the list more easily understandable by a human. This can be costly for bigger groups
SearchAllGroupsForKMinusOne := function(n)
local j, r, K, G;
for j in [1..Length(AllSmallGroups(n))] do
G:= SmallGroup(n,j);
K := KMinusOne(G);
Print("Group with index ", j, " has r = ", K.r," and s = ", K.s,"       ", StructureDescription(G),"\n");
od;
end;


# Same as SeachAllGroupsForKMinusOne, but goes through all groups of size in the range specified
# Range must be of the form [k..l] with k = minimum of orders, l = maximum of orders
SearchAllGroupsForKMinusOneInRange := function( range )
local i;
for i in range do
Print("Size of group is ",i,"\n");
SearchAllGroupsForKMinusOne(i);
od;
end;