////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       P-ADIC DIAGONALIZATION                       //
//                            David Kohel                             //
//                       Created November 1999                        //
//                       Last modified May 2000                       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := Rationals();

////////////////////////////////////////////////////////////////////////

forward pAdicDiagonals, FindRootVector; 

////////////////////////////////////////////////////////////////////////

import "genus_common.m" : LatticeContent, RLattice;
import "genus_common.m" : FieldSquareClass, UnitSquareClass;
import "2-adic_diagonal.m" : Jordan2Reduction, twoAdicDiagonals;

////////////////////////////////////////////////////////////////////////
//                                                                    //
////////////////////////////////////////////////////////////////////////

function pAdicDiagonalizationCommon(TYPE,L,p)
    if Rank(L) eq 0 then return L; end if;
    K := BaseRing(L);
    if p eq 2 then
	D1, D2 := twoAdicDiagonals(L);
	if #D1 eq 0 then
	    return Jordan2Reduction( DirectSum(
		[ RLattice(TYPE,Matrix(2,M)) : M in D2 ]) );  
	else 
	    L1 := RLattice(TYPE,DiagonalMatrix(D1));
	end if;
	if #D2 eq 0 then
	    return Jordan2Reduction(L1);
	else 
	    L2 := DirectSum([ RLattice(TYPE,Matrix(2,M)) : M in D2 ]);
	end if;
	return Jordan2Reduction(DirectSum(L1,L2));
    end if;
    D := Sort([ UnitSquareClass(a,p) : a in pAdicDiagonals(L,p) ]); 
    for i in [2..#D] do
	if D[i-1] eq D[i] then
	    q := p^Valuation(D[i],p); 
	    D[i] := UnitSquareClass(D[i-1]*(D[i]/q),p);  
	    D[i-1] := q;
	end if; 
    end for;
    return RLattice(TYPE,DiagonalMatrix(D));
end function;

intrinsic pAdicDiagonalization(L::Lat,p::RngIntElt) -> Lat
    {}
    require IsPrime(p) : "Argument 2 must be prime";
    return pAdicDiagonalizationCommon(Lat,L,p);
end intrinsic;

intrinsic pAdicDiagonalization(L::ModTupRng,p::RngIntElt) -> ModTupRng
    {A diagonalized lattice or module p-adically equivalent to L. If p 
    is 2 then the diagonalization may have Jordan blocks of dimension 2.}
    require Type(BaseRing(L)) in {RngInt,FldRat} :
	"Argument 1 must be a module over the integers or rationals.";
    require IsPrime(p) : "Argument 2 must be prime";
    return pAdicDiagonalizationCommon(ModTupRng,L,p);
end intrinsic;

function pAdicDiagonals(L,p) 
    // PRE: A lattice L over the integers and a prime p.
    // POST: The diagonal entries of the diagonalization
    // of the Gram matrix of L.
    TYPE := Type(L); 
    error if not IsPrime(p), "Argument 2 must be prime";
    if p eq 2 then
	return twoAdicDiagonals(L);
    end if;
    dim := Rank(L);
    if dim eq 1 then
	return [QQ|Norm(L.1)];
    end if;
    c := LatticeContent(L);
    L := RLattice(TYPE,(1/c)*GramMatrix(L));
    c := UnitSquareClass(c,p);
    v := L.1;
    n := (v,v);
    if (n mod p) ne 0 then
	B := [ n*L.i-(L.i,v)*v : i in [2..dim] ];
    else
	v := FindRootVector(L,p);
	n := (v,v);
	G, f := quo< L | v >;
	B := [ n*u-(u,v)*v : u in { g@@f : g in Generators(G) } ];
    end if;
    M := RLattice(TYPE,Matrix(dim-1,[ (B[i],B[j]) : i,j in [1..dim-1]]));
    return Sort([ QQ | UnitSquareClass(c*n,p) : 
	n in [Norm(v)] cat pAdicDiagonals(M,p) ]);
end function;

function FindRootVector(L,p)
    n := Rank(L); 
    for i in [1..n] do
	if ((L.i,L.i) mod p) ne 0 then
	    return L.i;
	end if;
	for j in [i+1..n] do
	    t := (L.i,L.j);
	    if (t mod p) ne 0 then
		if ((2*t + (L.j,L.j)) mod p) ne 0 then 
		    return L.i + L.j; 
		else 
		    return L.i - L.j; 
		end if;
	    end if;
	end for;
    end for;
end function;

