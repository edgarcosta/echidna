////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  P-ADIC SPINOR GROUP AND CHARACTERS                //
//                          AND SPINOR KERNEL                         //
//                            David Kohel                             //
//                       Created November 1999                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := Rationals();

////////////////////////////////////////////////////////////////////////

import "genus_common.m" : LatticeContent, RLattice;
import "neighbors.m" : HasEvenNeighbor; // Is this really necessary?

////////////////////////////////////////////////////////////////////////
//              CHARACTERS ASSOCIATED TO SPINOR GROUP                 //
////////////////////////////////////////////////////////////////////////

// This implements in a trivial way the multiplicative groups <1,-1>^n
// and coset reductions relative to this group; these are the dual 
// groups to the Dirichlet groups Z/DZ^* -> <1,-1>.

function PruneCharacters(G,chars)
    // Remove the chars which are trivial.
    k := 1;
    while k le #chars do 
	I := [ 1 : i in [1..#chars] ];
	I[k] := -1;
	if I in G then
	    Exclude(~chars,chars[k]);
	    G := {@ Remove(g,k) : g in G @};
	else 
	    k +:= 1;
	end if;
    end while;
    return G, chars;      
end function;

function CokernelReduction(G,chars)
    repeat
	G1 := G join {@ [ a[i]*b[i] : i in [1..#chars] ] : a, b in G @};
	G, chars := PruneCharacters(G1,chars);
    until G1 eq G;
    return G, chars;
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
////////////////////////////////////////////////////////////////////////

function GenusGenerators(L, depth)
    // A small prime p for forming p-neighbor closure, and a 
    // sequence of primes (generally empty) generating the group of 
    // spinor operators, over p (modulo the spinor genus).
    
    D := Determinant(L);
    G, chars := SpinorKernel(L);
    chi := func< p,q | q eq -1
	select KroneckerSymbol(q,p) else KroneckerSymbol(p,q) > ;
    if -1 in chars or 2 in chars then
	p := 3;
    elif D mod 2 eq 0 then
	p := 3;
    elif IsOdd(L) and not HasEvenNeighbor(L, depth) then
	p := 3;
    else 
	p := 2;
    end if;
    while D mod p eq 0 do
	p := NextPrime(p);
    end while;
    gens := [ p ];
    g := [ chi(p,q) : q in chars ];
    G, chars := CokernelReduction(G join {@ g @},chars);
    while #chars gt 0 do
	p := NextPrime(p);
	while D mod p eq 0 do
	    p := NextPrime(p);
	end while;
	g := [ chi(p,q) : q in chars ];
	if g notin G then
	    Append(~gens,p);
	    I := [ k : k in [1..#chars] | g[k] eq -1 ];
	    if #I eq 1 then
		k := I[1];
		Remove(~chars,k);
		G := {@ Remove(g,k) : g in G @};
	    end if; 
	    G, chars := CokernelReduction(G,chars);
	end if;
	while D mod p eq 0 do
	    p := NextPrime(p);
	end while;
    end while;
    return gens;
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsSpinorNorm(G::SymGen,r::RngIntElt) -> BoolElt
    {True if and only if r is coprime to 2 and the determinant
    is the norm of an element of the spinor kernel.}
    _, _, m, n, q := SpinorKernel(Representative(G));
    xgens := [ m(x) : x in Generators(Domain(m)) ];
    return &and[ Evaluate(x,r) eq 1 : x in xgens ];
end intrinsic; 

function BinarySpinorGenerators(D)
    // The goal is to compute primes p such that PrimeForm(Q,p)^2's
    // generate Cl(Q)^2/Cl(Q)^4, where Q is QuadraticForms(D).  We 
    // reduce to the 2-subgroup Cl2(Q) of Cl(Q), compute the order h2 
    // of the subgroup Cl2(Q)^2, and enumerate the set of elements S of
    // Cl2(Q)^4.  For each new generator found, we expand the set S.
    Q := QuadraticForms(D);
    A, f := ClassGroup(Q);
    r := #[ i : i in [1..Ngens(A)] | Order(A.i) mod 4 eq 0 ];
    gens := [ ZZ | ];
    if r eq 0 then return gens; end if;
    // Compute the order of Cl2(Q)^2.
    h2 := &*[ n div 2^Max(0,Valuation(n,2)-1) 
	where n is Order(A.i) : i in[1..Ngens(A)] ];
    // Compute the exponents for Cl2(Q)^4, and the abelian 
    // subgroup mapping to Cl2(Q)^4.
    e4 := [ n div 2^Max(0,Valuation(n,2)-2) 
	where n is Order(A.i) : i in[1..Ngens(A)] ];
    A4 := sub< A | [ e4[i]*A.i : i in [1..Ngens(A)] ] >;
    S := [ f(x) : x in A4 ];
    p := 2;
    c2 := #A div 2^(Valuation(#A,2)-1);
    while #gens lt r do   
	if KroneckerSymbol(D,p) eq 1 then
	    f := PrimeForm(Q,p)^c2;
	    if f notin S then
		Append(~gens,p); 
		if #gens lt r then
		    S cat:= [ f*g : g in S ]; 
		end if;
	    end if;
	end if;
	p := NextPrime(p);
    end while;
    return gens;
end function;

intrinsic SpinorGenerators(G::SymGen) -> SeqEnum
    {A sequence of primes which generate the spinor group.}
    if Rank(G) eq 2 then
	return BinarySpinorGenerators(-Determinant(G));
    end if;
    _, _, m, n, q := SpinorKernel(Representative(G));
    xgens := [ Codomain(m) | m(x) : x in Generators(Domain(m)) ];
    X := Universe(xgens); 
    if #xgens eq 1 and xgens[1] eq X!1 then
	return [ ZZ | ];
    end if; 
    m := Modulus(Universe(xgens));
    d := Determinant(G);
    if m mod 2 eq 0 and d mod 2 eq 1 then
	d *:= 2;
    end if;
    V := VectorSpace(GF(2),#xgens);
    U := sub< V | V!0 >;
    pgens := [ ZZ | ];   
    p := 2;
    while U ne V do
	if m mod p ne 0 then
	    w := V![ (1-Evaluate(x,p)) div 2 : x in xgens ];
	    if w notin U then
		U := sub< V | Basis(U) cat [ w ] >; 
		Append(~pgens,p);
	    end if;
	end if;
	p := NextPrime(p);
    end while;
    return pgens;
end intrinsic;

intrinsic SpinorKernel(L::Lat) -> GrpAb, Map
    {}
    // The image of the spinor kernel, followed by the sequence of 
    // primes p defining coordinatewise characters 
    //     r |-> KroneckerSymbol(r,p),
    // or, if p = -1,
    //     r |-> KroneckerSymbol(-1,r).
    TYPE := Type(L); 
    c := LatticeContent(L);
    if c notin {QQ|0,1} then
	L := RLattice(TYPE,(1/c)*GramMatrix(L));
    end if;
    prms := [ -1 ] cat [ p[1] : p in Factorization(2*Determinant(L)) ];
    imgs := {@ [ 1 : i in [1..#prms] ] @};
    for p in prms[[2..#prms]] do 
	A := AutomorphousClasses(L,p);
	// Remove "irrelevant" primes. 
	if p eq 2 and A eq {1,3,5,7} then
	    k := Index(prms,-1);
	    if k ne 0 then
		Remove(~prms,k);
		imgs := {@ Remove(g,k) : g in imgs @};
	    end if;
	    k := Index(prms,2);
	    if k ne 0 then
		Remove(~prms,k);
		imgs := {@ Remove(g,k) : g in imgs @};
	    end if;
	elif IsOdd(p) and #A eq 2 and 
	    0 notin { a mod p : a in A } then
	    k := Index(prms,p);
	    if k ne 0 then
		Remove(~prms,k);
		imgs := {@ Remove(g,k) : g in imgs @};
	    end if;
	else
	    // Remove "tractable" characters.
	    if IsOdd(p) and #A eq 4 then
		k := Index(prms,p);
		if k ne 0 then
		    Remove(~prms,k);
		    imgs := {@ Remove(g,k) : g in imgs @};
		end if;
	    end if;
	    for a in Exclude(A,1) do
		e := Valuation(a,p);
		u := a div p^e;
		g := [ 1 : i in [1..#prms] ];
		for j in [1..#prms] do
		    q := prms[j];
		    if q eq -1 and p eq 2 then
			g[j] := KroneckerSymbol(-1,a);
		    elif q eq -1 then
			g[j] := KroneckerSymbol(-1,p)^e;
		    elif q ne p then
			g[j] := KroneckerSymbol(p,q)^e;
		    else
			g[j] := KroneckerSymbol(u,q);
		    end if;
		end for;
		I := [ k : k in [1..#prms] | g[k] eq -1 ];
		if #I eq 1 then
		    k := I[1];
		    Remove(~prms,k);
		    imgs := {@ Remove(g,k) : g in imgs @};
		elif #I ge 2 then
		    Include(~imgs,g);
		end if; 
	    end for;
	end if;
    end for;
    imgs, prms := CokernelReduction(imgs,prms);
    N := &*prms;
    if N mod 2 eq 0 then
	N *:= 4; // Represents a character mod 8
    end if;
    if N lt 0 then
	// Make positive and congruent to 0 mod 4;
	N *:= N mod 4 eq 0 select -1 else -4;
    end if;
    vecs := [ [ (1-e) div 2 : e in chi ] : chi in imgs ];
    inds := [ Integers() | p in {-1,2} select 1 else (p-1) div 2 : p in prms ];
    A := AbelianGroup([ 2 : i in [1..#prms] ]);
    B := sub< A | [ A!v : v in vecs ] >;
    G := DirichletGroup(N,Integers());
    m := map< B->G | [ CartesianProduct(B,G) | 
	<B!A!v,G![ Integers() | inds[i]*v[i] : i in [1..#prms] ]> : v in vecs ] >; 
    n := map< A->G | [ CartesianProduct(A,G) | 
	<x,G![ Integers() | inds[i]*e[i] : i in [1..#prms] ]>
	where e := Eltseq(x) : x in A ] >; 
    C, q := quo< A | B >;
    return imgs, prms, m, n, q;
end intrinsic;

