////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     P-ADIC AUTOMORPHOUS NUMBERS                    //
//                            David Kohel                             //
//                       Created November 1999                        //
//                       Last modified May 2000                       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "genus_common.m" : FieldSquareClass, UnitSquareClass, RLattice;
import "p-adic_diagonal.m" : pAdicDiagonals;

////////////////////////////////////////////////////////////////////////

intrinsic AutomorphousClasses(G::SymGen,p::RngIntElt) -> SetEnum
    {A set of integer representatives of the p-adic automorphous 
    square classes for the genus G (see Conway & Sloane).}
    require IsPrime(p) : "Argument 2 is not a prime";
    return AutomorphousClasses(G`Representative,p);
end intrinsic;

intrinsic AutomorphousClasses(L::Lat,p::RngIntElt) -> SetEnum
    {A set of integer representatives of the p-adic automorphous 
    square classes for the lattice L (see Conway & Sloane).}
    // This follows Conway-Sloane p.390-392 (section 9.4).
    
    require IsExact(L) : "Argument 1 must be an exact lattice";
    require IsPrime(p) : "Argument 2 is not a prime";
    if p lt 0 then p *:= -1; end if;
    
    L := CoordinateLattice(LLL(L));
    L := RLattice(Type(L),(1/Content(L))*GramMatrix(L));
    if IsOdd(p) then
	D := pAdicDiagonals(L,p);
	S := &join [ { FieldSquareClass(D[i]/D[j],p) 
	    : j in [i+1..#D] } : i in [1..#D] ];
	if #{ Valuation(a,p) : a in D } lt Rank(L) then
	    for u in [1..p] do
		if KroneckerSymbol(u,p) eq -1 then
		    S join:= { 1, u };
		    break u;
		end if;
	    end for;  
	end if;
    else 
	if p eq 8 then p := 2; end if;
	D1, D2 := pAdicDiagonals(L,2);
	V1 := [ Valuation(a,2) : a in D1 ];
	V2 := [ Valuation(s[2],2)  : s in D2 ];
	List1 := D1;
	List2 := [ u*2^(n+1) : n in V2, u in {1,3,5,7} ];
	TotList := List1 cat List2;
	// Ratio square classes of total list.
	S := { FieldSquareClass(a,2) : a in &cat[ [ TotList[j]/TotList[i] 
	    : j in [i+1..#TotList] ] : i in [1..#TotList] ] };
	// Supplementary rules depend only on List1.
	R1 := { UnitSquareClass(a,2) : a in &cat[ [ List1[j]/List1[i] 
	    : j in [i+1..#List1] ] : i in [1..#List1] ] };
	U1 := [ Valuation(a,2) : a in R1 ]; 
	for i in [1..#V1-2] do
	    if V1[i+2] le (V1[i] + 3) then
		S join:= { 1, 3, 5, 7 }; 
	    end if;
	end for;    
	if 1 in R1 then
	    S join:= { 2 }; 
	end if;
	if 5 in R1 then
	    S join:= { 6 }; 
	end if;
	if &or[ a in R1 : a in [2,8,10,40] ] then
	    S join:= { 3 }; 
	end if;
	if &or[ n in U1 : n in [0,2,4] ] then
	    S join:= { 5 }; 
	end if;
	if &or[ a in R1 : a in [6,14,24,56] ] then
	    S join:= { 7 }; 
	end if;
    end if;     
    return { FieldSquareClass(a*b,p) : a, b in S };
end intrinsic;
