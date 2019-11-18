//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                    CLASSICAL MODULAR POLYNOMIALS                         //
//         Copyright (C) 2008 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare verbose ModularPolynomial, 2;

forward BalancedMod;

intrinsic ClassicalModularPolynomial(N::RngIntElt :
    Database := true, Al := "Modular")-> RngMPolElt
    {The classical modular polynomial of level N relating the jinvariants
    j(q) and j(q^N).} 
    
    require N ge 1 : "Argument must be a positive integer.";
    if Database then
	DBMP := ModularPolynomialDatabase();
        require <"Classical",N> in DBMP :  
            "Argument has no corresponding database entry.";
	return ModularPolynomial(DBMP,"Classical",N);
    elif Al eq "Modular" then
	ZZ := Integers();
	if N eq 1 then
	    return P.1 - P.2 where P := PolynomialRing(ZZ,2);
	end if;
	mods := [ ZZ | ];
	r := &*[ ZZ | (p+1)*p^Valuation(N div p,p) : p in PrimeDivisors(N) ];
	exps := [ [0,r] ] cat [ [i,j] : i, j in [0..r-1] | i le j ];
	rems := [ ]; 
	vprint ModularPolynomial : "Number of terms =", #exps;
	m := 1;
	p := PreviousPrime(Floor(2^23.5));
	stable := false;
	zz_coeffs := [ 0 : i in [1..#exps] ];
	while not stable do
	    while N mod p eq 0 do p := PreviousPrime(p); end while;
	    vprint ModularPolynomial : "Modular prime =", p;
	    m *:= p;
	    tyme := Cputime();
	    Phi := ClassicalModularPolynomial(N,GF(p));
	    vprint ModularPolynomial :
   	       "Modular computation time:", Cputime(tyme);
	    P2 := Parent(Phi);
	    X := P2.1; Y := P2.2;
	    ff_coeffs := [ ZZ |
	        MonomialCoefficient(Phi,X^n[1]*Y^n[2]) : n in exps ];
	    Append(~rems,ff_coeffs);
	    Append(~mods,p);
	    new_coeffs := [
	        BalancedMod( CRT([ coeffs[i] : coeffs in rems ],mods), m )
	            : i in [1..#exps] ];
            stable := &and[ zz_coeffs[i] eq new_coeffs[i] : i in [1..#exps] ];
	    zz_coeffs := new_coeffs;
	    coeff_size := Max([ Ceiling(Log(10,1+Abs(c))) : c in zz_coeffs ]);
	    modulus_size := Ceiling(Log(10,m));
	    if coeff_size le modulus_size - 4 then
		stable := true;
	    end if;
	    vprintf ModularPolynomial :
	        "Modulus size is %o digits.\n", modulus_size;
	    vprintf ModularPolynomial :
	        "Max coefficient size is %o digits.\n", coeff_size;
	    vprintf ModularPolynomial, 2 :
   	        "Completed %o coefficients, %o remaining.\n", 
 	        &+[ Integers() | 1 : c in zz_coeffs |
	                Ceiling(Log(10,1+Abs(c))) le modulus_size - 4 ],
	        &+[ Integers() | 1 : c in zz_coeffs |
	                Ceiling(Log(10,1+Abs(c))) gt modulus_size - 4 ];
 	    p := PreviousPrime(p);
	end while;
	P2 := PolynomialRing(Integers(),2);
	X := P2.1; Y := P2.2;
	return &+[ zz_coeffs[j]*(
	    exps[j][1] eq exps[j][2] select X^exps[j][1]*Y^exps[j][2] 
            else X^exps[j][1]*Y^exps[j][2] + Y^exps[j][1]*X^exps[j][2] ) 
	        : j in [1..#exps] ];
    end if;
    require Al eq "Integral" :
        "Al parameter must be either \"Modular\" or \"Integral\".";
    return ClassicalModularPolynomial(N,Integers()); 
end intrinsic;  
 
intrinsic ClassicalModularPolynomial(N::RngIntElt,K::Rng : Database := false) -> RngMPolElt 
    {The classical modular polynomial over K relating j(q) and j(q^N).} 

    require N ge 1 : "Argument 1 must be positive.";
    P2<X,Y> := PolynomialRing(K,2 : Global);
    if Database then
	DBMP := ModularPolynomialDatabase();
	p := Characteristic(K);
	if p ne 0 and <"Classical",N,p> in DBMP then  
	    return P2!ModularPolynomial(DBMP,"Classical",N);
	end if;
	require <"Classical",N> in DBMP :  
            "Argument 1 has no corresponding database entry.";
	return P2!ModularPolynomial(DBMP,"Classical",N);
    end if;
    X := P2.1; Y := P2.2;
    if N eq 1 then return X-Y; end if;
    PS := LaurentSeriesRing(K);
    q := PS.1;
    r := &*[ (p+1)*p^Valuation(N div p,p) : p in PrimeDivisors(N) ]; 
    oerr := O(q^(2*r^2+r));
    tyme := Cputime();
    j1 := jInvariant(q + oerr); 
    vprint ModularPolynomial : "Generator 1 time:", Cputime(tyme);
    tyme := Cputime();
    j2 := jInvariant(q^N + oerr);
    vprint ModularPolynomial : "Generator 1 time:", Cputime(tyme);
    exps := [ [0,r] ] cat [ [i,j] : i, j in [0..r-1] | i le j ];
    vprint ModularPolynomial : "Number of terms =", #exps;
    j1s := [ 1 + oerr ];
    tyme := Cputime();
    for i in [1..r] do
	Append(~j1s,j1s[i]*j1 + oerr);
    end for;
    vprint ModularPolynomial : "Power sequence 1 time:", Cputime(tyme);
    tyme := Cputime();
    j2s := [ 1 + oerr ];
    for i in [1..r] do
	Append(~j2s,j2s[i]*j2 + oerr);
    end for;
    vprint ModularPolynomial : "Power sequence 2 time:", Cputime(tyme);
    tyme := Cputime();
    PowerTerms := [ n[1] eq n[2] select j1s[n[1]+1]*j2s[n[2]+1]
        else j1s[n[1]+1]*j2s[n[2]+1] + j2s[n[1]+1]*j1s[n[2]+1] : n in exps ]; 
    vprint ModularPolynomial : "Series computation time:", Cputime(tyme);
    tyme := Cputime();
    V := LinearRelations(PowerTerms); 
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n",
	    Dimension(V), Degree(V);
    require Dimension(V) ne 0 : "Failed to find a dependency."; 
    require Dimension(V) eq 1 : "Found too many dependencies."; 
    coeffs := Eltseq(Basis(V)[1]);
    Phi := &+[ coeffs[j]*(
             exps[j][1] eq exps[j][2] select X^exps[j][1]*Y^exps[j][2] 
	     else X^exps[j][1]*Y^exps[j][2] + Y^exps[j][1]*X^exps[j][2] ) 
                 : j in [1..#exps] ];
    if MonomialCoefficient(Phi,P2.1^r) eq -K!1 then
	Phi *:= -1;
    end if;
    return Phi;
end intrinsic;  
 
function BalancedMod(a,m)
    t := m div 2;
    a mod:= m;
    if a le t then return a;
    else return a-m;
    end if;
end function;

