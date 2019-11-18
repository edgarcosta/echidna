////////////////////////////////////////////////////////////////////////
//               Defining Polynomials for Modular Curves              //
////////////////////////////////////////////////////////////////////////

intrinsic ModularPolynomial(M::ModSS) -> RngMPolElt
    {}
    R<x,y> := PolynomialRing(GF(Prime(M)^2),2);
    table := [* x-y,    // N=1
	x*y-2^12, // N=2 
	x*y-3^6,  // N=3
	0,        
	x*y-5^3,  // N=5
	0,
	x*y-7^2,  // N=7
	0,
	0,
	0, 
	0,
	0,
	x*y-13    // N=13
	*];
    
    N := AuxiliaryLevel(M);  
    require N le #table : "The model is not known.";
    require table[N] ne 0: "The model is not known.";
    return table[N];                  
end intrinsic;

intrinsic jInvariantMap(M::ModSS) -> RngUPolElt, RngUPolElt
    {}
    R<x> := PolynomialRing(GF(Prime(M)^2));
    table := [* <x, 1>,  // N = 1
	<(x+16)^3, x>,  // N = 2
	<(x+27)*(x+3)^3, x>, // N=3
	<>, 
	<(x^2+10*x+5)^3, x>, // N=5
	<>,
	<(x^2+13*x+49)*(x^2+5*x+1)^3, x>, // N=7
	<>,
	<>,
	<>,
	<>,
	<>,
	<(x^2+5*x+13)*(x^4+7*x^3+20*x^2+19*x+1)^3, x>, //N=13
	<>
	*];
    N := AuxiliaryLevel(M);  
    
    require N le #table : "The j-invariant map is not known.";
    require table[N] cmpne <> : "The j-invariant map is not known.";
    return table[N][1], table[N][2];   
end intrinsic;

intrinsic HeckeCorrespondence(M::ModSS, p::RngIntElt) -> RngMPolElt
    {Polynomial that defines the p-th modular correspondence on M.}
    
    N := AuxiliaryLevel(M);
    require N in {1,2,3,5,7,13} :
	"Auxiliary level of argument 1 must be 1, 2, 3, 5, 7, or 13.";
    require p ge 2 and IsPrime(p) : "Argument 2 must be prime.";
    
    P2 := PolynomialRing(GF(Prime(M)^2),2);
    if N eq 1 then
	D := ModularCurveDatabase("Classical");
	require p in D : 
	    "Argument 2 must be in the database of classical modular equations.";
	return P2!Polynomial(ModularCurve(D,p));
    else 
	D := ModularCurveDatabase("Hecke",N);
	require p in D :
	    "Argument 2 must be in the database of Hecke correspondences.";
	return P2!Polynomial(ModularCurve(D,p));
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                      Supersingular Points                          //
////////////////////////////////////////////////////////////////////////

/*
This functionality will change according to the models use for the
modular curves X_0(N) above.
*/

function RootsAfterSpecializeX(F, alpha)
    R<x,y> := Parent(F);
    G := UnivariatePolynomial(Evaluate(F,[alpha,y]));
    return Roots(G);
end function;

function RootsAfterSpecializeY(F, beta)
    R<x,y> := Parent(F);
    G := UnivariatePolynomial(Evaluate(F,[x,beta]));
    return Roots(G);
end function;

intrinsic SupersingularPoints(M::ModSS) -> SeqEnum
    {The sequence [ j(E_i) ] of j-invariants with respect to the basis [ E_i ] 
    of elliptic curves for the module M. }

    if assigned M`ss_points then 
	return M`ss_points;
    end if;
    
    if UsesBrandt(M) then
	M`ss_points := ["I"*IntegerToString(n) : n in [1..Dimension(M)]];
	return M`ss_points;
    end if;
    
    p := Prime(M);
    N := AuxiliaryLevel(M);
    ss := SupersingularInvariants(p);   // in mestre.m, uses N=1 case.
    F := ModularPolynomial(M);
    R<x,y> := Parent(F);
    points := [];
    j_num, j_denom := jInvariantMap(M);
    // j_num(x) / j_denom(x) = j.
    for j in ss do   // find the fibers
	f := j_num - j*j_denom;
	for r in Roots(f) do
	    // solve for y-coordinates
	    y_coords := RootsAfterSpecializeX(F,r[1]);
	    assert #y_coords ge 1;
	    for s in y_coords do
		Append(~points, <r[1],s[1]>);
	    end for;
	end for;
    end for;
    M`ss_points := points;
    return points;
end intrinsic;

intrinsic SupersingularPolynomials(M::ModSS) -> SeqEnum, SeqEnum
    {The sequence [ \chi_i(x) ] minimal polynomials of the sequence [ j(E_i) ]
    of j-invariants of the basis elliptic curves E_i for the module M.
    Elements of the sequence are represented only once, with the sequence
    of index sets [i_1,i_2] returned as a second value.}

    require IsPrime(Level(M)) : "Argument must have prime level.";
    require not M`uses_brandt : "Argument must be defined in terms of j-invariants";

    if assigned M`ss_polynomials then
	return M`ss_polynomials, M`ss_polynomial_indices;
    end if;
    
    SS := {@ @};
    ii := [   ];
    JJ := SupersingularPoints(M);
    for i in [1..#JJ] do
	chi := MinimalPolynomial(JJ[i][1]);
	k := Index(SS,chi);
	if k eq 0 then
	    Include(~SS,chi);
	    Append(~ii,{i});
	else
	    Include(~ii[k],i);
	end if;
    end for;
    M`ss_polynomials := SS;
    M`ss_polynomial_indices := ii;
    return SS, ii;
end intrinsic;

function MatchIntegerSequences(XX,YY)
    YY := {@ J : J in YY @};
    return [ Index(YY,I) : I in XX ];
end function;

function MatchDiscriminantForms(DD,SS,mm)
    num := #DD;
    P := Universe(SS);
    N := Characteristic(BaseRing(P));
    n := 1;
    D := -2;
    DBCP := ClassPolynomialDatabase();
    hh_seq := [ [] : i in [1..num] ];
    cc_seq := [ [] : i in [1..num] ];
    while true do
	D -:= 1;
	if D mod 4 notin {0,1} then continue; end if;
	if -D gt 2^n then
	    n +:= 1;
	    TT := [ ThetaSeries(L,2^n) : L in DD ];
	    vprint SupersingularModule : "TT:"; TT;
	    vprint SupersingularModule : "hh:", hh_seq;
	    vprint SupersingularModule : "cc:", cc_seq;
	end if;
	wD := D eq -3 select 3 else D eq -4 select 2 else 1;
	DK := FundamentalDiscriminant(D);
	mK := Isqrt(D div DK);
	if KroneckerSymbol(DK,N) eq 1 then continue; end if;
	if mK mod N eq 0 then continue;	end if;
	eD := DK mod N eq 0 select 1 else 1/2;
	if mK ne 1 then continue; end if;
	HD := P!HilbertClassPolynomial(DBCP,D);
	vprintf SupersingularModule : "h(%o) = %o\n", D, Degree(HD);
	for i in [1..#SS] do
	    chi := SS[i];
	    hi := Valuation(HD,chi);
	    Append(~hh_seq[i],hi);
	    ai := eD * wD * Coefficient(TT[i],-D)/mm[i];
	    Append(~cc_seq[i],ai);
	end for;
	if #SequenceToSet(hh_seq) eq num then
	    break;
	end if;
	D +:= -1;
    end while;
    jj := MatchIntegerSequences(hh_seq,cc_seq);
    return DD[jj];
end function;

intrinsic DiscriminantForms(M:ModSS) -> SeqEnum, SeqEnum
    {}
    if assigned M`discriminant_forms then
	return M`discriminant_forms, M`ss_polynomial_indices;
    end if;
    N := Level(M);
    require IsPrime(N) : "Argument must have prime level.";
    require not M`uses_brandt : "Argument must be defined in terms of j-invariants";
    SS, ii := SupersingularPolynomials(M);
    // Despite the fact that the Brandt module is not used here in its construction
    // we construct it here to make a call to discriminant forms.  
    X := BrandtModule(N);
    mm := MonodromyWeights(X);
    DD := {@ LatticeWithGram(A) : A in DiscriminantForms(X) @};
    DD := MatchDiscriminantForms(DD,SS,mm);
    M`discriminant_forms := DD; 
    return DD, ii;
end intrinsic;
