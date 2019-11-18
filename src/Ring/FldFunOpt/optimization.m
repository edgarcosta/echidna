/*
Optimized representations of function fields over the rationals  
Original Kash program by Juergen Klueners, ported and adapted by
David Kohel, October 2001
*/

declare verbose FldFunOpt, 4;

////////////////////////////////////////////////////////////////////////

function Specialization(f,a)
    return Polynomial([ Evaluate(c,a) : c in Eltseq(f) ]);
end function;

function RationalFactorization(r)
    return Factorization(Numerator(r)) cat
	[ <f[1],-f[2]> : f in Factorization(Denominator(r)) ];
end function;

////////////////////////////////////////////////////////////////////////

function RoundPolynomial(g) // ::RngUPolElt) -> RngUPolElt
    // {Given a polynomial over a ring of real or complex coefficients,
    // sufficiently close to a polynomial with integral coefficients,
    // returns the rounding to this polynomial.}
    eps := 10^-4;
    coeffs := Eltseq(g);
    CC := Universe(coeffs);
    if Type(CC) in {FldRe,FldCom} then
	if &+[ Abs(Im(c)) : c in coeffs ] gt eps then
	    error "Polynomial is not well-approximated " *
	       "by an integral polynomial.";
        end if;
	zzcoeffs := [ Round(Re(c)) : c in coeffs ];
	if &+[ Abs(coeffs[i]-zzcoeffs[i]) : i in [1..#coeffs] ] gt eps then
	    error "Polynomial is not well-approximated " *
	        "by an integral polynomial."; 
        end if;
	return Polynomial(zzcoeffs);
    elif Type(CC) eq RngUPol then
	return Polynomial([ RoundPolynomial(c) : c in coeffs ]);
    end if;
    error "No real or complex structure determined for argument.";
end function;

////////////////////////////////////////////////////////////////////////
//  Integral Defining Polynomial for Function Fields
////////////////////////////////////////////////////////////////////////

function IntegralPolynomial(f);
    F := BaseRing(Parent(f));
    if Type(F) eq RngUPol then return f; end if;
    coeffs := Eltseq(f);
    nums := [ Numerator(F!c) : c in coeffs ];
    dens := [ Denominator(F!c) : c in coeffs ];
    d0 := LCM(dens);
    sg := Sign(LeadingCoefficient(nums[#nums]));
    ncoeffs := [ sg*nums[i]*(d0 div dens[i]) : i in [1..#coeffs] ];
    return Polynomial(ncoeffs);
end function;

////////////////////////////////////////////////////////////////////////
// Optimized Representations of Function Fields.
////////////////////////////////////////////////////////////////////////

intrinsic OptimizedSpecializations(
    f::RngUPolElt, MP::SeqEnum, S::[RngIntElt]) -> SeqEnum
    {}
    f := IntegralPolynomial(f);
    vprint FldFunOpt, 4 : "Integral polynomial:", f;
    optspec := [ ];
    for i in S do
	gi := Specialization(f,i);
	if IsMonic(gi) and IsIrreducible(gi) then
	    Oi := EquationOrder(gi);
	    if #MP ne 0 then 
		LL := [ Evaluate(r,i) : r in MP ];
		M := Setseq(Seqset(&cat[ [ q[1] : q in
		    RationalFactorization(r) ] : r in LL ]));
		M := [ q : q in M | q gt Degree(gi) ];
		// Restore this is not broken:
		// Om := MaximalOrder(Oi : Ramification := M);
		Om := MaximalOrder(Oi);
	    else
		Om := Oi;
	    end if;
	    bool, Oo := OptimizedRepresentation(Om);
	    xi := NumberField(Oo)!Oo!(Oi.2);
	    vprintf FldFunOpt, 4 :
	       "Ord %o: %o\n", i, DefiningPolynomial(Oi);
	    if bool then
		vprintf FldFunOpt, 1 :
		    "Opt %o: %o\n", i, DefiningPolynomial(Oo);
		Append(~optspec,<i,DefiningPolynomial(Oo),Eltseq(xi)>);
	    else
		vprint FldFunOpt : "No optimized representation found.";
	    end if;
	end if;
    end for;
    return optspec;
end intrinsic;

////////////////////////////////////////////////////////////////////////
// Critical primes -- those primes dividing the index in the integral
// closure.
////////////////////////////////////////////////////////////////////////

function CriticalPrimes(f)
    vprint FldFunOpt, 2 : "Computing nonmaximal primes";
    P := Parent(f);
    disc := Discriminant(f);
    if Type(disc) eq FldFunRatUElt then
	disc := Numerator(disc)*Denominator(disc);
    end if;
    resx := Resultant(f,Polynomial([ Derivative(c) : c in Eltseq(f)]));
    if Type(resx) eq FldFunRatUElt then
	resx := Numerator(resx)*Denominator(resx);
    end if;
    crit := GCD(disc,resx);
    // So crit should contain only the singular (i.e. primes dividing
    // the index in the integral closure), while disc also includes
    // the ramifying primes. 
    RamPrms := [];
    for fac in Factorization(disc) do
	w := true;
	f := fac[1];
	e := fac[2];
	vprint FldFunOpt, 3 : "e =", e;
	vprint FldFunOpt, 3 : "f =", f;
	if Degree(f) gt 0 and e eq 2 then
	    w := crit mod f ne 0;
	    vprintf FldFunOpt, 3 : "Dedekind test: %o\n", w;
	end if;
	if w then Append(~RamPrms,f); end if;
    end for;
    return [ p : p in RamPrms |
        Degree(p) ne 0 or Coefficient(p,0) gt Degree(f) ], crit;
end function;

////////////////////////////////////////////////////////////////////////
//  Optimimal representation combine
////////////////////////////////////////////////////////////////////////

function ReducedSequence(L,M)
    // INPUT:
    // L is a sequence of tuples whose first entry are ring elements
    // and whose second entry is a sequence of evaluations.
    // M is a sequence of tuples whose first entry is an integer and
    // whose second entry is polynomial 
    // OUPUT:
    // A sequence of polynomials. 
    Retseq := [];
    deg := Degree(L[1][2]);
    for p in L do
	s := 0;
	for F in M do 
	    f := F[2]; 
	    r := Evaluate(f,p[1]);
	    if r ne Coefficient(p[2],F[1]) then
		s +:= 1;
	    end if;
	end for;
	if s eq 0 then
	    Append(~Retseq,p);
	end if;
    end for;
    return Retseq;
end function;

function PartitionSequence(L,co)
    M := []; N := []; Z := [];
    deg := Degree(L[1][2]);
    // Partition into positive, negative, and zero sequences
    for K in L do
	p := Coefficient(K[2],co);
	if p gt 0 then
	    Append(~M,K);
	elif p lt 0 then
	    Append(~N,K);
	else
	    Append(~Z,K);
	end if;
    end for;
    // Sort positive sequence M
    for i in [1..#M] do
	for j in [i+1..#M] do
	    if Coefficient(M[i][2],co) gt Coefficient(M[j][2],co) then
		p := M[i]; M[i] := M[j]; M[j] := p;
	    end if;
	end for;
    end for;
    // Sort negative sequence M
    for i in [1..#N] do
	for j in [i+1..#N] do
	    if Coefficient(N[i][2],co) lt Coefficient(N[j][2],co) then
		p := N[i]; N[i] := N[j]; N[j] := p;
	    end if;
	end for;
    end for;
    return [M,N,Z];
end function;

function AbundanceSequence(Matches)
    S := {@ f[1] : f in Matches @};
    // Form the sequence of <poly,indices>.
    AbundPolys := [ <p,{Integers()|}> : p in S ];
    for x in Matches do
	k := Index(S,x[1]);
	AbundPolys[k][2] join:= x[2];
    end for;
    // Sort the sequence of abundant polynomials 
    // according to their frequencies.
    for i in [1..#AbundPolys] do
	for j in [i+1..#AbundPolys] do
	    if #AbundPolys[i][2] lt #AbundPolys[j][2] then 
		tmp := AbundPolys[i];
		AbundPolys[i] := AbundPolys[j];
		AbundPolys[j] := tmp;
	    end if;
	end for;
    end for;
    return AbundPolys;
end function;

function BlockList(L,deg)
    n := #L;
    M := [];
    for i in [1..n-deg+1] do
	s := 0;
	for j in [i..i+deg-2] do
	    if L[j][1] gt L[j+1][1] then s +:= 1; end if;
	end for;
	Append(~M,[i,s]);
    end for;
    for i in [1..#M] do
	for j in [i+1..#M] do
	    if M[i][2] gt M[j][2] then
		tmp := M[i];
		M[i] := M[j];
		M[j] := tmp;
	    end if;
	end for;
    end for;
    return M;
end function;

function HasIntegralCoefficient(L,co)
    // Not sure what this does...
    n := #L;
    deg := Degree(L[1][2]);
    F := FieldOfFractions(Parent(L[1][2]));
    M := [ <p[1],Coefficient(p[2],co)> : p in L ];
    dens := [ &*[ F | M[i][1]-M[j][1] : j in [1..n] | j ne i ] : i in [1..n] ];
    sum := &+[ F | M[i][2]/dens[i] : i in [1..n] ];
    return sum eq 0;
end function;

function InterpolateSequence(L,co)
    P := PolynomialRing(RationalField()); t := P.1;
    X := [ P | Coefficient(p[2],co) : p in L ];
    M := [ P | t-p[1] : p in L ];
    // return Evaluate(CRT(X,M),x);
    g := CRT(X,M);
    vprint FldFunOpt, 4 : "CRT lifting problem with input data:";
    if GetVerbose("FldFunOpt") ge 4 then
	for i in [1..#X] do
	    printf "  <%o,%o>\n", X[i], M[i];
	end for;
    end if;
    vprint FldFunOpt, 4 : "  Solved by g =", g;
    return CRT(X,M);
end function;

function EstimatedCoefficientDegree(L,co,e)
    m, j := Max([ Abs(Coefficient(p[2],co)) : p in L ]);
    return m eq 0 select -1 else
	Floor(Log(Abs(m))/(1+Log(1+Abs(L[j][1]))))+e+1;
end function;

function HasCoefficientLift(L,co,deg)
    // c.f. ListPolyCombineSpec 
    if #L eq 1 then
	return true, Parent(L[1][2])!Coefficient(L[1][2],co);
    end if;
    test := false;
    polys := [];
    for j in [1..#L] do
	M := [ L[i] : i in [1..#L] | i ne j ];
	if HasIntegralCoefficient(M,co) then
	    g := InterpolateSequence(M,co); 
	    if Degree(g) le deg then
		Append(~polys,g);
	    end if;
	else
	    vprint FldFunOpt, 4 :
	        "Skipping this one which fails Lagrange interpolation.";
	end if;
    end for;
    if #polys gt 0 then
	vprint FldFunOpt, 3 : "Found interpolating polynomial sequence:";
	vprint FldFunOpt, 3 : polys;
	n, i := Min([ Degree(g) : g in polys]);
	return true, polys[i];
    else
	return false, _;
    end if;
end function;

function OptimizedList(MM)
    D := [];
    G := [];
    K := Sort(Setseq(Seqset(&cat[ [ p[2] : p in S ] : S in MM ])));
    for i in K do
	H := [];
	for S in MM do
	    s := 0;
	    for T in S do
		if T[2] eq i then s +:= 1; end if;
	    end for;
	    Append(~H,s);
	end for;
	Append(~G,<i,H>);
    end for;
    GG := [];
    for H in G do
	T := H[2];
	HH := [1,2,3];
	for i in [1..3] do
	    for j in [i+1..3] do
		if T[i] lt T[j] then 
		    k := HH[i];
		    HH[i] := HH[j];
		    HH[j] := k;
		end if;
	    end for;
	end for;
	Append(~GG,<H[1],HH>);
    end for;
    for S in GG do
	i := S[1];
	HH := S[2];
	for j in HH do
	    for H in MM[j] do
		if H[2] eq i then
		    Append(~D,<j,H>);
		end if;
	    end for;
	end for;
    end for;
    return D;
end function;

function AbundantPolynomials(SpecPoly,k,deg)
    Qt := PolynomialRing(RationalField());
    if deg eq -1 then return [<Qt!0,1>]; end if;
    j := deg;
    while j ge 1 do
	Matches := [ CartesianProduct(Qt,Parent({Integers()|})) | ];
	M := PartitionSequence(SpecPoly,k);
	N := OptimizedList([ BlockList(M[i],j+3) : i in [1..3] ]);
	for p in N do
	    n := p[2][1];
	    G := M[p[1]][[n..n+j+2]];
	    vprintf FldFunOpt, 3 :
	        "Looking for degree %o lift of coefficient %o " * 
		"in polynomial data G:\n", deg, k;
	    vprint FldFunOpt, 3 : [ <tup[1],tup[2]> : tup in G ];
	    bool, fc := HasCoefficientLift(G,k,deg);
	    if bool then 
		Append(~Matches,<fc,{s[1] : s in G}>);
	    end if;
	end for;
	AbundMatches := AbundanceSequence(Matches);
	if #AbundMatches gt 0 then break; end if;
	j -:= 1;
    end while;
    return AbundMatches;
end function;

function PolynomialMatchRecursion(SpecPolys,CoeffRecur,k,extra)
    if k eq -1 then
	// Success! pass back the coefficients and the sequence
	// of specializations which give rise to it.
	return true, CoeffRecur, SpecPolys;
    end if;
    if #SpecPolys eq 0 then return false, _, _; end if;
    vprint FldFunOpt, 3 : "************************";
    vprint FldFunOpt, 3 : "PolynomialMatchRecursion:";
    vprint FldFunOpt, 3 : "Finding coefficient matches for:";
    vprint FldFunOpt, 3 : SpecPolys;
    vprint FldFunOpt, 2 : "Coefficient:", k;
    maxdeg := EstimatedCoefficientDegree(SpecPolys,k,extra);
    vprint FldFunOpt, 2 : "Max coefficient degree =", maxdeg;
    AbundPolys := AbundantPolynomials(SpecPolys,k,maxdeg);
    vprint FldFunOpt, 2 : "Found abundant polynomial sequence:";
    vprint FldFunOpt, 2 : AbundPolys;
    if #AbundPolys eq 0 then
	vprint FldFunOpt, 3 : "Returning false.";
	vprint FldFunOpt, 3 : "************************";
	return false, _, _;
    end if;
    for h in AbundPolys do
	CoeffRecur1 := [h[1]] cat CoeffRecur;
	vprint FldFunOpt, 3 : "Matched coefficients:";
	vprint FldFunOpt, 3 : CoeffRecur1;
	SpecPolys1 := ReducedSequence(SpecPolys,[<k,h[1]>]);
	vprint FldFunOpt, 3 : "Recursion with k =", k-1;
	vprint FldFunOpt, 3 : "************************";
	bool, Coeffs, GoodSpecs :=
	    PolynomialMatchRecursion(SpecPolys1,CoeffRecur1,k-1,extra);
	if bool then
	    vprint FldFunOpt, 3 : "Returning true.";
	    vprint FldFunOpt, 3 : "************************";
	    return true, Coeffs, GoodSpecs;
	end if;
    end for;
    vprint FldFunOpt, 3 : "Returning false.";
    vprint FldFunOpt, 3 : "************************";
    return false, _, _;
end function;

function HasGoodPolynomial(SpecPolys,extra)
    // SpecPolys is a sequence of tuples <y0,f(x,y0)>
    vprint FldFunOpt, 3 : "************************";
    vprint FldFunOpt, 3 : "HasGoodPolynomial:";
    vprint FldFunOpt, 3 : "";
    vprint FldFunOpt, 3 : "Specialized sequence:";
    vprint FldFunOpt, 3 : SpecPolys;
    vprint FldFunOpt, 3 : "";
    vprint FldFunOpt, 3 : "************************";
    if #SpecPolys eq 0 then return false, _, _; end if;
    deg := Degree(SpecPolys[1][2]);
    bool, Coeffs, GoodSpecs :=
	PolynomialMatchRecursion(SpecPolys,[],deg-1,extra);
    vprintf FldFunOpt, 3 :
       "****** Found %o in polynomial recursion ******\n", bool;
    if not bool then return false, _, _; end if;
    return true, Polynomial(Coeffs cat [1]), GoodSpecs;
    // Formerly call to: NormalizedPolynomial(poly);
end function;

intrinsic OptimizedRepresentation(K::FldFun :
    SieveSize := 20,
    SieveIterations := 8,
    InitialSpecialization := 50,
    SpecializationValues := [ Integers() | ],
    ComputeIsomorphism := false
    ) -> RngFunOrdElt
    {}
    f := DefiningPolynomial(K);
    require Degree(K) lt Infinity() :
       "Argument must be a finite degree extension.";
    F := BaseRing(Parent(f));
    require Type(BaseRing(F)) eq FldRat :
        "Argument must be an element of the polynomial ring over " *
        "the univariate function field over the rationals.";
    P := PolynomialRing(FunctionField(Rationals()));
    /*
    if ComputeIsomorphism then
        DO SOMETHING HERE.
    end if;
    */
    return OptimizedRepresentation(P!f);
end intrinsic;

intrinsic OptimizedRepresentation(f::RngMPolElt :
    SieveSize := 20,
    SieveIterations := 8,
    InitialSpecialization := 50,
    SpecializationValues := [ Integers() | ],
    ComputeIsomorphism := false
    ) -> RngMPolElt
    {}
    Pxy := Parent(f);
    QQ := BaseRing(Pxy);
    require Rank(Pxy) eq 2 and Type(QQ) eq FldRat : 
	"Argument must be a bivariate polynomial over the rationals.";
    require IsIrreducible(f) : "";
    Px := PolynomialRing(QQ); x := Px.1;
    Py := PolynomialRing(Px); y := Py.1;
    g, m := OptimizedRepresentation(Evaluate(f,[x,y]) :
	SieveSize := SieveSize,
	SieveIterations := SieveIterations,
	InitialSpecialization := InitialSpecialization,
	SpecializationValues := SpecializationValues,
	ComputeIsomorphism := true // seems required below
	// ComputeIsomorphism := ComputeIsomorphism
    );
    if g eq Evaluate(f,[x,y]) then m := hom< Py->Py | y >; end if;  
    X := Pxy.1; Y := Pxy.2;
    T := m(y);
    T := &+[ Evaluate(Coefficient(T,i),X)*Y^i : i in [0..Degree(T)] ];
    g := &+[ Evaluate(Coefficient(g,i),X)*Y^i : i in [0..Degree(g)] ];
    if ComputeIsomorphism then
	return g, hom< Pxy->Pxy | [X,T] >;
    end if;
    return g, _;
end intrinsic;

intrinsic OptimizedRepresentation(f::RngUPolElt :
    SieveSize := 20,
    SieveIterations := 8,
    InitialSpecialization := 50,
    SpecializationValues := [ Integers() | ],
    ExtraDegree := 0,
    ComputeIsomorphism := false
    ) -> RngUPolElt
    {}
    r := SieveSize;
    n := SieveIterations;
    k := InitialSpecialization;
    K := BaseRing(Parent(f));
    require Type(K) in {RngUPol,FldFun,FldFunRat} : 
	"Argument should be a polynomial over a rational function field.";
    require Type(BaseRing(K)) eq FldRat : 
        "Argument should be a polynomial over a " * 
        "rational function field over Q.";
    require Type(r) eq RngIntElt and r gt 0 :
	"Parameter SieveSize must be a positive integer.";
    require Type(n) eq RngIntElt and n gt 0 :
	"Parameters SieveIterations must be a positive integer.";
    require Type(k) eq RngIntElt :
	"Parameter InitialSpecializataion must be an integer.";
    require Type(SpecializationValues) eq SeqEnum and
	Type(Universe(SpecializationValues)) eq RngInt :
	"Parameter SpecializataionValues must an integer sequence.";
    if #SpecializationValues eq 0 then
	specvals := [ [k+r*(i-1)..k+r*i-1] : i in [1..n] ];
    else
	specvals := [ SpecializationValues ];
    end if;
    SpecPolys := [];
    crit_prms, crit := CriticalPrimes(f);
    if GetVerbose("FldFunOpt") ge 4 then
	print "Found critical primes:";
	for mp in crit_prms do print mp; end for;
    end if;
    for vals in specvals do
	vprint FldFunOpt : "Specializing...";
	SpecPolys cat:= OptimizedSpecializations(f,crit_prms,vals);
	vprint FldFunOpt : "Combining...";
	bool, g, specs := HasGoodPolynomial(SpecPolys,ExtraDegree);
	if bool then
	    //
	    vprint FldFunOpt : "Matching specializations:";
	    vprint FldFunOpt : specs;
	    if ComputeIsomorphism then
		vprint FldFunOpt : "Computing isomorphism.";
		x0 := specs[1][1]; y0 := specs[1][3];
		Py := Parent(f); Px := BaseRing(Py); x := Px.1;
		OL := EquationOrderFinite(FunctionField(g));
		bool, y1 := InternalLiftEmbedding(OL!y0,f,x-x0,crit);
		require bool : "Failed to compute isomorphism";
		return g, hom< Py->Py | Py!Eltseq(y1) >;
	    end if;
	    return g, _;
	else
	    vprintf FldFunOpt :
	        "No good polynomial found at iteration %o\n",
		    Index(specvals, vals);
	end if;
    end for;
    vprint FldFunOpt : "No good polynomial found, returning original.";
    return f, _;
end intrinsic;
