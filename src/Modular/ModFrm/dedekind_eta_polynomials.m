//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                     DEDEKIND ETA MODULAR POLYNOMIALS                     //
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


forward DMPIntegralCompute, DMPModularCompute, DMPLocalCompute;

//////////////////////////////////////////////////////////////////////////////

function BalancedMod(a,m)
    t := m div 2;
    a mod:= m;
    if a le t then return a;
    else return a-m;
    end if;
end function;

function DMPMonomialExponents(N)
    t := GCD(N-1,12);
    s := 12 div t;
    // Valuation of f and degree of Phi in J : 
    u := ((N-1)*s) div 12;   
    I := [ [N+1,0] ] cat [ [0,0] ] cat [ [i,j] : i in [1..N], j in [0..u] | i + t*j le N ];
    return I, s, t, u;
end function;

//////////////////////////////////////////////////////////////////////////////
//                        Relation computations                             //
//////////////////////////////////////////////////////////////////////////////

function MonomialRelations(fncs,I,prec)
    PS := Universe(fncs); q := PS.1;
    f, j := Explode(fncs);
    oerr := O(q^prec);
    p := Max([ n[1] : n in I ]) - 1;
    u := Max([ n[2] : n in I ]);
    tyme := Cputime();
    fs := [ PS!1 ];
    for k in [1..p+1] do
	Append(~fs,fs[k]*f + oerr);
    end for;
    vprint ModularPolynomial : "Function 1 powers time:", Cputime(tyme);
    tyme := Cputime();
    js := [ PS!1 ];
    for k in [1..u] do
	Append(~js,js[k]*j);
    end for;
    vprint ModularPolynomial : "Function 2 powers time:", Cputime(tyme);
    tyme := Cputime();
    S := [ fs[n[1]+1]*js[n[2]+1] + O(q^(u*(p+1)+1)) : n in I ];
    vprint ModularPolynomial : "Power series sequence time:", Cputime(tyme);
    tyme := Cputime();
    V := LinearRelations(S);
    vprint ModularPolynomial : "Linear algebra time:", Cputime(tyme);
    return V;
end function;   

function DedekindEtaFunction(N,R,prec);
    PS := LaurentSeriesRing(R); q := PS.1;
    oerr := O(q^prec);
    // num := &*[ 1-q^(k*N) + oerr : k in [1..prec div N] ];
    num := PS!1;
    for k in [1..prec div N] do
	num -:= q^(k*N)*num + oerr;
    end for;
    // den := &*[ 1-q^k + oerr : k in [1..prec-1] ];
    den := PS!1;
    for k in [1..prec-1] do
	den -:= q^k*den + oerr;
    end for;
    u := LCM(N-1,12) div 12;   
    s := 12 div GCD(N-1,12);
    return q^u * N^s * (num/den)^(2*s);
end function;

//////////////////////////////////////////////////////////////////////////////
//                     Modular Polynomial Computations                      //
//////////////////////////////////////////////////////////////////////////////

intrinsic DedekindEtaModularPolynomial(N::RngIntElt :
    Database := false, Repository := "Echidna", Al := "Modular", InitialPrime := 0) -> RngMPolElt
    {The Dedekind eta modular polynomial over the ring R relating 
    (eta(q)/eta(N*q))^e and j(q) where e = 24/GCD(N-1,12) (for N prime?).}
    require IsPrime(N : Proof := false) : "Argument 1 must be prime.";
    P2<X,J> := PolynomialRing(IntegerRing(),2 : Global);
    if Database then
	if Repository eq "Echidna" then
	    DBMP := ModularPolynomialDatabase();
	    require <"Dedekind eta",N> in DBMP :  
		"Argument has no corresponding database entry.";
	    return P2!ModularPolynomial(DBMP,"Dedekind eta",N);
	elif Repository eq "Export" then
	    require ExistsModularCurveDatabase("Canonical") : 
		"Argument has no corresponding database entry.";
	    DBMC := ModularCurveDatabase("Canonical");
	    require N in DBMC :
		"Argument has no corresponding database entry.";
	    return P2!Polynomial(ModularCurve(DBMC,N));
	else
	    require Repository in {"Export","Echidna"} :
		"Parameter \"Database\" must be \"Export\" or \"Echidna\".";
	end if;
    elif Al eq "Modular" then
	char := InitialPrime;
	require char eq 0 or IsPrime(char : Proof := false) :
	    "Parameter \"InitialPrime\" must be prime.";
        return P2!DMPModularCompute(N : InitialPrime := char);
    elif Al eq "Integral" then
	return P2!DMPIntegralCompute(N);
    else
	require false : "Parameter \"Al\" must be \"Modular\" or \"Integral\".";
    end if;
end intrinsic;

intrinsic DedekindEtaModularPolynomial(N::RngIntElt,R::Rng :
    Database := false, Repository := "Echidna", Al := "Modular", InitialPrime := 0) -> RngMPolElt
    {The Dedekind eta modular polynomial over the ring R.}
    require IsPrime(N : Proof := false) : "Argument 1 must be prime.";
    P2<X,J> := PolynomialRing(R,2 : Global);
    if Database then
	if Repository eq "Echidna" then
	    DBMP := ModularPolynomialDatabase();
	    if Type(R) eq FldFin then
		require <"Dedekind eta",N,Characteristic(R)> in DBMP :  
		    "Argument 1 has no corresponding database entry.";
	    else
		require <"Dedekind eta",N> in DBMP :  
		    "Argument 1 has no corresponding database entry.";
	    end if;
	    return ModularPolynomial(DBMP,"Dedekind eta",N,R);
	elif Repository eq "Export" then
	    require ExistsModularCurveDatabase("Canonical") : 
		"Argument 1 has no corresponding database entry.";
	    DBMC := ModularCurveDatabase("Canonical");
	    require N in DBMC :
		"Argument 1 has no corresponding database entry.";
	    return P2!Polynomial(ModularCurve(DBMC,N));
	else
	    require Repository in {"Export","Echidna"} :
		"Parameter \"Database\" must be \"Export\" or \"Echidna\".";
	end if;
    elif Type(R) in {FldFin,RngIntRes,RngPadRes} then
	require Characteristic(R) mod N ne 0 :
	    "Argument 1 must be coprime to the characteristic of argument 2.";
	cffs := DMPLocalCompute(N,R);
	mons := DMPMonomialExponents(N);
	return &+[ cffs[j]*X^mons[j][1]*J^mons[j][2] : j in [1..#mons] ];
    elif Al eq "Modular" then
	char := InitialPrime;
	require char eq 0 or IsPrime(char : Proof := false) :
	    "Parameter \"InitialPrime\" must be prime.";
        return P2!DMPModularCompute(N : InitialPrime := char);
    elif Al eq "Integral" then
	return P2!DMPIntegralCompute(N);
    else
	require false : "Parameter \"Al\" must be \"Modular\" or \"Integral\".";
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                  Modular Equations Computations                    //
////////////////////////////////////////////////////////////////////////

function DMPLocalCompute(N,R)
    I, s, t, u := DMPMonomialExponents(N);
    prec := (N+1)*u + N + 32;
    vprint ModularPolynomial : "Degree in f =", N+1;
    vprint ModularPolynomial : "Degree in j =", u;
    vprint ModularPolynomial : "Precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #I;
    tyme := Cputime();
    PS<q> := LaurentSeriesRing(R); oerr := O(q^prec);
    f := DedekindEtaFunction(N,R,prec);
    j := jInvariant(q + oerr);
    vprint ModularPolynomial : "Generator series time:", Cputime(tyme);
    V := MonomialRelations([f,j],I,prec);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n", Dimension(V), Degree(V);
    error if Dimension(V) ne 1, "Precision error.";
    return ChangeUniverse(Eltseq(Basis(V)[1]),Integers());
end function;   

function DMPModularCompute(p : InitialPrime := 0)
    I := DMPMonomialExponents(p);
    rems := [ ]; 
    mods := [ Integers() | ];
    m := 1;
    if InitialPrime ne 0 then
	char := InitialPrime;
	NextModularPrime := NextPrime;
    else
	char := PreviousPrime(Floor(2^23.5));
	NextModularPrime := PreviousPrime;
    end if;
    stable := false;
    zz_coeffs := [ 0 : i in [1..#I] ];
    while not stable do
	if p eq char then
	    char := NextModularPrime(char);
	end if;
	vprint ModularPolynomial : "Modular prime =", char;
	m *:= char;
	tyme := Cputime();
	ff_coeffs := DMPLocalCompute(p,FiniteField(char));
	vprint ModularPolynomial : "Modular computation time:", Cputime(tyme);
	Append(~rems,ff_coeffs);
	Append(~mods,char);
	new_coeffs := [ BalancedMod( CRT(
    	    [ coeffs[i] : coeffs in rems ],mods), m ) : i in [1..#I] ];
	vprintf ModularPolynomial : "(#NonZero, #Zero) = (%o,%o)\n",
 	    #[ I[i] : i in [1..#I] | new_coeffs[i] ne 0 ],	
	    #[ I[i] : i in [1..#I] | new_coeffs[i] eq 0 ];	
        stable := &and[ zz_coeffs[i] eq new_coeffs[i] : i in [1..#I] ];
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
        char := NextModularPrime(char);
    end while;
    P2<X,J> := PolynomialRing(Integers(),2 : Global);
    return &+[ zz_coeffs[j]*X^I[j][1]*J^I[j][2] : j in [1..#I] ];
end function;

function DMPIntegralCompute(p)
    I, s, t, u := DMPMonomialExponents(p);
    prec := (p+1)*u + p + 32;
    vprint ModularPolynomial : "Degree in f =", p+1;
    vprint ModularPolynomial : "Degree in j =", u;
    vprint ModularPolynomial : "Precision =", prec;
    vprint ModularPolynomial : "Number of terms =", #I;
    tyme := Cputime();
    PS := LaurentSeriesRing(RationalField()); q := PS.1;
    oerr := O(q^prec);
    f := p^s*(DedekindEta(q^p + oerr)/DedekindEta(q + oerr))^(2*s);
    j := jInvariant(q + oerr);
    vprint ModularPolynomial : "Series computation time:", Cputime(tyme);
    V := MonomialRelations([f,j],I,prec);
    vprintf ModularPolynomial :
        "Found solution space of dimension %o and degree %o.\n",
        Dimension(V), Degree(V);
    error if Dimension(V) ne 1, "Precision error.";
    c0 := Eltseq(Basis(V)[1]);
    ChangeUniverse(~c0,Integers());
    P2<X,J> := PolynomialRing(Integers(),2 : Global);
    return &+[ c0[j]*X^I[j][1]*J^I[j][2] : j in [1..#I] ];
end function;   

