//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                        CLASS POLYNOMIALS                                 //
//                       Created November 1999                              //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// Intrinsics:
// HilbertClassPolynomial, WeberClassPolynomial
// AtkinClassPolynomial, DedekindEtaClassPolynomial
 
declare verbose ClassPolynomial, 2;

forward NormalizedWeber;

intrinsic WeberToHilbertClassPolynomial(
    f::RngUPolElt,D::RngIntElt : Al := "Roots") -> RngUPolElt
    {}
    r := 24 div GCD(D,3);
    if Al eq "Roots" then
	CC := ComplexField();
	fseq := Roots(f,CC);
	jseq := [ (f-16)^3/f where f := rt[1]^r : rt in fseq ];
	prec := Ceiling(1.1*Log(10,1+Abs(Real(&*jseq))));
	if Precision(CC) lt prec then
	    vprint ClassPolynomial : "Setting new precision to ", prec;
	    CC := ComplexField(prec);
	    fseq := Roots(f,CC);
	    jseq := [ (f-16)^3/f where f := rt[1]^r : rt in fseq ];
	end if;
	PC := PolynomialRing(CC);
	h := &*[ X - j : j in jseq ] where X := PC.1;
	return Parent(f)![ Round(Real(c)) : c in Eltseq(h) ];
    end if;
    P2<X,J> := PolynomialRing(RationalField(),2);
    I := ideal< P2 | J*X^r - (X^r-16)^3, Evaluate(f,X) >;
    H := UnivariatePolynomial(Basis(EliminationIdeal(I,1))[1]);
    return PolynomialRing(Integers())!H;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                   HILBERT CLASS POLYNOMIAL                         //
////////////////////////////////////////////////////////////////////////

function VerifyHilbertClassPolynomialSupersingularPrime(f,D,p)
    P := PolynomialRing(FiniteField(p));
    prms := [ fac[1] : fac in Factorization(P!f) ];
    // This is a very crude test...
    return &and[ Degree(pp) le 2 : pp in prms ];
end function;

function VerifyHilbertClassPolynomialOrdinaryPrime(f,D,p)
    r := Order(PrimeForm(QuadraticForms(D),p));
    FF := FiniteField(p);
    PF := PolynomialRing(FF);
    fact := Factorization(PF!f);
    DK := FundamentalDiscriminant(D);
    if D mod p ne 0 then
	bool := &and[ pp[2] eq 1 : pp in fact ];
    else
	m := Isqrt(D div DK);
	v := Valuation(m,p);
	c := KroneckerSymbol(DK,p);
	e := (p-c)*p^(v-1);
	bool := &and[ pp[2] eq e : pp in fact ];
    end if;
    assert bool;
    if not bool then return bool; end if;
    // This is a very crude test...
    bool := &and[ Degree(pp[1]) eq r : pp in fact ];
    assert bool;
    if not bool then return bool; end if;
    if Degree(f) gt 2 then
	return bool;
    end if;
    // Too expensive:
    KK := FiniteField(p,r);
    PK := PolynomialRing(KK);
    j := Roots(PK!fact[1][1])[1][1];
    E := EllipticCurveWithjInvariant(j);
    t := TraceOfFrobenius(E);
    return IsSquare((t^2-4*#KK) div DK);
end function;

intrinsic VerifyHilbertClassPolynomial(
    f::RngUPolElt,D::RngIntElt : Trials := 8) -> BoolElt
    {Given a putative Hilbert class polynomial f with resepct to
    a discriminant D, determine if f verifies conditions to be
    ordinary or supersingular at randomly chosen primes.  This
    does not verify or distinguish between class polynomials of
    orders in the same imaginary quadratic field.}
    DK := FundamentalDiscriminant(D);
    for p in [2,3,5,7,13] do
	if KroneckerSymbol(DK,p) ne 1 then
	    FF := FiniteField(p);
	    PF := PolynomialRing(FF); x := PF.1;
	    s := SupersingularPolynomial(FF);
	    if PF!f ne s^Degree(f) then
		vprint ClassPolynomial :
		    "Failed class polynomial verification at supersingular prime", p;
		return false;
	    end if;
	    vprint ClassPolynomial :
		"Verified class polynomial at supersingular prime", p;
	end if;
    end for;
    for i in [1..Trials] do
	p := RandomPrime(32);
	if KroneckerSymbol(DK,p) ne 1 then
	    bool := VerifyHilbertClassPolynomialSupersingularPrime(f,D,p);
	    if not bool then
		vprint ClassPolynomial :
		    "Failed class polynomial verification at supersingular prime", p;
		return bool;
	    end if;
	    vprint ClassPolynomial :
		"Verified class polynomial at supersingular prime", p;
	else
	    bool := VerifyHilbertClassPolynomialOrdinaryPrime(f,D,p);
	    if not bool then
		vprint ClassPolynomial :
		    "Failed class polynomial verification at ordinary prime", p;
		return bool;
	    end if;
	    vprint ClassPolynomial :
		"Verified class polynomial at ordinary prime", p;
	end if;
    end for;
    return true;
end intrinsic;

intrinsic HilbertClassPolynomial(D::RngIntElt) -> RngUPolElt 
    {Returns the Hilbert class polynomial for D.} 
    require D lt 0 : "Argument must be negative"; 
    require D mod 4 in {0,1} : "Argument is not a discriminant."; 
    CC := ComplexField(); 
    ClassForms := ReducedForms(D);
    sqrtD := Sqrt(D);
    prec := Ceiling( &+ [ Log(10,1+Abs( jInvariant(
         (q[2] + sqrtD)/(2*q[1]) ) ) ) : q in ClassForms ] ) + 8;
    CC := ComplexField(prec);
    sqrtD := Sqrt(CC!D);
    PC := PolynomialRing(CC); Y := PC.1;
    h := &*[ Y - jInvariant( (q[2] + sqrtD)/(2*q[1]) ) : q in ClassForms ]; 
    PZ := PolynomialRing(Integers()); X := PZ.1;
    return &+[ Round(Real(Coefficient(h,i)))*X^i : i in [0..Degree(h)] ]; 
end intrinsic; 
 
////////////////////////////////////////////////////////////////////////
//                     WEBER CLASS POLYNOMIAL                         //
////////////////////////////////////////////////////////////////////////

intrinsic WeberClassPolynomial(D::RngIntElt : Lambda := 1.1) 
   -> RngUPolElt
   {The class polynomial of binary quadratic forms of discrimant D, 
   in terms of Weber functions.}

   require D lt 0: "Argument must be negative.";
   require (D mod 4) in {0,1} : "Argument is not a discrimiant."; 
   require (D mod 8) eq 1: "Argument not congruent to 1 mod 8.";
   require Lambda gt 1 : "Parameter Lambda must be greater than 1";
   prec := Max(16,Ceiling(Sqrt(-D/4)));
   CC := ComplexField(prec);
   PC := PolynomialRing(CC); Y := PC.1;
   ClassForms := ReducedForms(D);
   e := GCD(D,3);
   coeffs := Coefficients( 
      &*[ Y - NormalizedWeber(CC,F)^e : F in ClassForms ] );
   MaxImag := Max([ Abs(Imaginary( coeffs[i] )) : i in [1..#coeffs] ]); 
   MaxReal := Max([ Abs(Real( coeffs[i] )) : i in [1..#coeffs] ]); 
   LogMaxReal := Ceiling(Log(10,1+MaxReal));
   while prec lt Lambda*LogMaxReal or 0.1 lt MaxImag do
      prec := Ceiling(Lambda*Max(LogMaxReal,prec));
      CC := ComplexField(prec);
      coeffs := Coefficients( 
         &*[ Y - NormalizedWeber(CC,F)^e : F in ClassForms ] );
      MaxImag := Max([ Abs(Imaginary( coeffs[i] )) : i in [1..#coeffs] ]); 
      prec := Ceiling(Lambda*prec);
   end while;
   PZ := PolynomialRing(Integers()); X := PZ.1;
   return &+[ Round( Real( coeffs[i] ) )*X^(i-1) : i in [1..#coeffs] ]; 
end intrinsic;

function NormalizedWeber(CC,F)
   // A normalized Weber function on binary quadratic forms.
   D := Discriminant(F);
   // assert D mod 8 eq 1;
   zta := Exp(2*Pi(CC)*CC.1/48);
   eps := (-1)^((D-1) div 8);
   a, b, c := Explode(Eltseq(F));
   tau := (-b+Sqrt(CC!(b^2-4*a*c)))/(2*a);
   if a mod 2 eq 0 and c mod 2 eq 0 then
      r := (b*(a-c-a*c^2)) mod 48;
      return zta^r*WeberF(tau);
   elif a mod 2 eq 0 then
      r := (b*(a-c-a*c^2) + 1) mod 48;
      return eps*zta^r*WeberF(tau+1);
   else
      r := (b*(a-c+a^2*c)+1) mod 48;
      return eps*zta^r*WeberF(-1/tau+1);
   end if;
end function;

////////////////////////////////////////////////////////////////////////
//                       ATKIN CLASS POLYNOMIALS                      //
////////////////////////////////////////////////////////////////////////

intrinsic AtkinClassPolynomial(N::RngIntElt,D::RngIntElt :
    Epsilon := 0.0001,
    Precision := 100,
    AtkinSeries := 0,
    AtkinModularPolynomial := 0,
    SeriesPrecision := 400,
    PowerSeries := 0,
    Al := "LLL" ) -> RngUPolElt
    {}
    require IsPrime(N) : "Argument 1 must be prime.";
    require D mod 4 in {0,1} and D lt 0 :
       "Argument 2 must be a negative discriminant.";
    msq := D div FundamentalDiscriminant(D);
    require KroneckerSymbol(D,N) ne -1 and msq mod N ne 0 :
       "Argument 1 must not be an inert prime " *
       "nor divide the conductor of argument 2.";
    require Al in {"Analytic","LLL","Resultant"} : 
       "Parameter Al must be \"Analytic\", \"LLL\", or \"Resultant\".";
    discs := [-3,-4,-7,-8,-11,-12,-16,-19,-27,-28,-43,-67,-163];
    DBMP := ModularPolynomialDatabase();
    if D in discs and (Al eq "Resultant" or
	(Al eq "LLL" and N gt 10*Abs(D))) then
	i := Index(discs,D);
	j := [0,1728,-3375,8000,-32768,54000,287496,-884736,-12288000,
             16581375,-884736000,-147197952000,-262537412640768000][i];
        tyme := Cputime();
	vprintf ClassPolynomial: "Reading in modular polynomial: ";
	if AtkinModularPolynomial ne 0 then
	    Phi := AtkinModularPolynomial;
	else
	    Phi := ModularPolynomial(DBMP,"Atkin", N);
	end if;
        vprintf ClassPolynomial: "%o secs\n", Cputime(tyme);
	tyme := Cputime();
	rts := Roots(Evaluate(Phi,[x,j]))
	    where x := PolynomialRing(Integers()).1;      
	vprintf ClassPolynomial : "Roots time: %o secs\n", Cputime(tyme);
	if #rts gt 1 then
	    vprintf ClassPolynomial :
	       "Found %o roots of modular polynomial.\n", #rts;
	end if;
	return PolynomialRing(Integers())![-rts[1][1],1];
    end if;
    if Al eq "Resultant" then 
        vprintf ClassPolynomial: "Reading in modular polynomial: ";
	tyme := Cputime();
	if AtkinModularPolynomial ne 0 then
	    Phi := AtkinModularPolynomial;
	else
	    Phi := ModularPolynomial(DBMP,"Atkin", N);
	end if;
        vprintf ClassPolynomial: "%o secs\n", Cputime(tyme);
	P2 := PolynomialRing(RationalField(),2);
	x := P2.1; j := P2.2;
	Phi := P2!Phi;
	DBCP := ClassPolynomialDatabase();
	if <"Hilbert",D> in DBCP then
	    hD := Evaluate(ClassPolynomial(DBCP,"Hilbert",D),j);
	else
	    hD := Evaluate(HilbertClassPolynomial(D),j);
	end if;
	tyme := Cputime();
	res := UnivariatePolynomial(Resultant(hD,Phi,2));
	vprintf ClassPolynomial : "Resultant time: %o secs\n", Cputime(tyme);
	tyme := Cputime();
	facs := Factorization(res);
	vprintf ClassPolynomial :
	    "Factorization time: %o secs\n", Cputime(tyme);
	vprint ClassPolynomial :
	    "Factorization degrees:", [ <Degree(f[1]),f[2]> : f in facs ] ;
	h := ClassNumber(D);
	e := D mod N eq 0 select 1 else 2; 
	n := #[ 1 : f in facs |
	    (h mod Degree(f[1]) eq 0) and (f[2] mod e eq 0) ];
	if n ne 1 then
	    vprintf ClassPolynomial :
		"Failed to find unique factor in resultant method:";
	    print "D =", D;
	    print "h =", h;
	    print "Factorization degrees:",
		[ <Degree(f[1]),f[2]> : f in facs ] ;
	    assert false;
	end if;
	return PolynomialRing(Integers())!facs[1][1];
    elif Al eq "Analytic" then
	CC := ComplexField(Precision);
	i := CC.1;
        pi := Pi(CC);
	DBAS := AtkinModularFunctionDatabase();
	good_prec := false;
	while good_prec eq false do
	    qmax := 0;
	    if AtkinSeries ne 0 then
		q := Parent(AtkinSeries).1;
		u := AtkinSeries + O(q^(N+1));
	    else
		u := AtkinModularFunction(DBAS,N);
	    end if;
	    //,SeriesPrecision : Extend := true);
	    Q := QuadraticForms(D);
	    pp := PrimeForm(Q,N);
	    rts := [ CC | ];
	    for qq in ReducedForms(Q) do
		if (pp[2]-qq[2]) mod (2*N) eq 0 then
		    rr := qq;
		elif (pp[2]+qq[2]) mod (2*N) eq 0 then
		    rr := Q![qq[3],-qq[2],qq[1]];
		else 
		    s := ((pp[2]-qq[2])*InverseMod(2*qq[1],N)) mod N;
		    a := qq[1];
		    b := 2*s*qq[1]+qq[2];
		    c := qq[1]*s^2+s*qq[2]+qq[3];
		    rr := Q![a,b,c];
		end if;
		ff := Composition(pp,rr);
		assert (ff[2]-pp[2]) mod (2*N) eq 0; 
		tau := (-ff[2]+Sqrt(CC!D))/(2*ff[1]);
		vprintf ClassPolynomial : "%o: %o\n",
	            ff, ComplexField(16)!Evaluate(u,Exp(2*pi*i*tau));
 	        q := Exp(2*pi*i*tau);
		qmax := Max(Abs(q),qmax);
		Append(~rts,Evaluate(u,q));
	    end for;
	    PC := PolynomialRing(CC); X := PC.1;
	    hC := Eltseq(&*[ X - r : r in rts ]);
  	    hI := [ Round(Real(c)) : c in hC ];
	    test := Max([ Abs(hC[i]-hI[i]) : i in [1..#hC] ]);
	    if test lt Epsilon then
		good_prec := true;
		vprint ClassPolynomial, 2 :
		    "Epsilon test =", ComplexField(16)!test;
	    else
		vprint ClassPolynomial : 
		    "Failed epsilon test with test =",
  		        ComplexField(16)!test;
  	        Precision +:= 20;
		SeriesPrecision +:= 20;
		vprint ClassPolynomial : 
		    "Extending Precision to", Precision, "\n" *
		    "Extending SeriesPrecision to", SeriesPrecision;
		vprint ClassPolynomial : "qmax =", RealField(20)!qmax; 
	    end if;
	end while;
	return Polynomial(hI);
    elif Al eq "LLL" then
	QD := QuadraticForms(D);
	hD := ClassNumber(QD); 
	CC := ComplexField();
	CC64 := ComplexField(19);
	RR64 := RealField(19);
	pi64 := Pi(RR64);
	lg10 := Log(RR64!10);
        DBAS := AtkinModularFunctionDatabase();
	lambda := pi64*Sqrt(RR64!Abs(D))/N;
	prec_lll := Round(hD*lambda*N/3/lg10+19);
	prec_real := Round(3/2*prec_lll);
	prec_series := Round(lg10*prec_real/lambda+200);
	vprint ClassPolynomial: "lambda:", lambda;
	vprint ClassPolynomial: "Using LLL precision:", prec_lll;
	vprint ClassPolynomial: "Using real precision:", prec_real;
	// Now set the correct series precision...
	tail := 1;
	while tail ge 10^-prec_real do
	    vprint ClassPolynomial:
	        "Reading in series to precision", prec_series;
	    if Type(PowerSeries) eq RngSerLaur and
		RelativePrecision(PowerSeries) le prec_series then
		n := prec_series + Valuation(PowerSeries);
		q := Parent(PowerSeries).1;
		f := PowerSeries + O(q^n);
	    else
		f := AtkinModularFunction(DBAS,N); //,prec_series);
	    end if;
	    n := Valuation(f) + prec_series - 1;
	    tail := Coefficient(f,n)*Exp(-lambda)^n;
	    vprint ClassPolynomial: "tail:", tail;
	    if tail lt 10^-prec_real then
		qf := PrimeForm(QD,N);
		CC := ComplexField(prec_real);
		qtau := Exp(2*Pi(CC)*CC.1*(-qf[2] + Sqrt(D))/(2*qf[1]));
		utau := Evaluate(f,qtau);
		vprint ClassPolynomial: "Abs(qtau):", Exp(-lambda);
		vprint ClassPolynomial: "utau =", CC64!utau;
		vprint ClassPolynomial: "Class number:", hD;
		if hD eq 1 then
		    HD := PolynomialRing(Integers())![-Round(Real(utau)),1]; 
		else 
		    HD := PowerRelation(ComplexField(prec_lll)!utau,hD : Al := "LLL");
		end if;	                            
		if HD eq 1 then HD := PolynomialRing(Integers())![0,1]; end if;
		if Degree(HD) ne ClassNumber(QD) then
		    fac := Factorization(HD);
		    u0 := ComplexField(19)!utau;
		    _, i := Min([ Abs(Evaluate(f[1],u0)) : f in fac ]);
		    HD := fac[i][1];
		end if;     
		if LeadingCoefficient(HD) ne 1 then
		    vprint ClassPolynomial: "Leading coefficient is not 1!!!";
		    vprint ClassPolynomial: "    N =", N;
		    vprint ClassPolynomial: "    D =", D;
		    vprint ClassPolynomial: "    h =", hD;
		    vprint ClassPolynomial: HD;
		    tail := 1;
		    prec_lll := Round(1.1*prec_lll);
		    prec_real := Round(3/2*prec_lll);
		    vprint ClassPolynomial: "Increasing LLL precision...";
		    vprint ClassPolynomial: "Using LLL precision:", prec_lll;
		    vprint ClassPolynomial: "Using real precision:", prec_real;
		end if;
	    else
		deficiency := (prec_real+Log(10,tail)+19)/lambda;
		increment := Round(Max(0.05*prec_series,deficiency));
		vprint ClassPolynomial:
		   "Incrementing series precision by", increment;
		prec_series +:= increment;
	    end if;
	end while;
	return HD;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                    CANONICAL CLASS POLYNOMIALS                     //
////////////////////////////////////////////////////////////////////////

intrinsic DedekindEtaClassPolynomial(N::RngIntElt,D::RngIntElt :
    Epsilon := 0.001, Al := "Resultant" ) -> RngUPolElt
    {}
    require IsPrime(N) : "Argument 1 must be prime.";
    require D mod 4 in {0,1} and D lt 0 :
       "Argument 2 must be a negative discriminant.";
    msq := D div FundamentalDiscriminant(D);
    require KroneckerSymbol(D,N) ne -1 and msq mod N ne 0 :
       "Argument 1 must not be an inert prime " *
       "nor divide the conductor of argument 2.";
    require Al in {"Analytic","Resultant"} : 
       "Parameter Al must be \"Analytic\" or \"Resultant\".";
    Phi := CanonicalModularPolynomial(N);
    if Al eq "Resultant" then 
	P2 := PolynomialRing(RationalField(),2);
	x := P2.1; j := P2.2;
	Phi := P2!Phi;
	DBCP := ClassPolynomialDatabase();
	if <"Hilbert",D> in DBCP then
	    hD := Evaluate(ClassPolynomial(DBCP,"Hilbert",D),j);
	else
	    hD := Evaluate(HilbertClassPolynomial(D),j);
	end if;
	h1 := Factorization(UnivariatePolynomial(Resultant(hD,Phi,2)))[1][1];
	return PolynomialRing(Integers())!h1;
    end if;
    require false : "Analytic method not implemented.";
end intrinsic;

intrinsic ReducedDedekindEtaClassPolynomial(N::RngIntElt,D::RngIntElt :
    Epsilon := 0.001, Al := "Resultant" ) -> RngUPolElt
    {}
    require IsPrime(N) : "Argument 1 must be prime.";
    require D mod 4 in {0,1} and D lt 0 :
       "Argument 2 must be a negative discriminant.";
    msq := D div FundamentalDiscriminant(D);
    require KroneckerSymbol(D,N) ne -1 and msq mod N ne 0 :
       "Argument 1 must not be an inert prime " *
       "nor divide the conductor of argument 2.";
    require Al in {"Analytic","Resultant"} : 
       "Parameter Al must be \"Analytic\" or \"Resultant\".";
    P2<x,y> := PolynomialRing(RationalField(),2);
    hD := DedekindEtaClassPolynomial( N, D : Epsilon := Epsilon, Al := Al);
    s := 12 div GCD(N-1,12);
    I := ideal< P2 | Evaluate(hD,x), x*y - (x^2+N^s) >;
    hred := Basis(EliminationIdeal(I,{y}))[1];
    return PolynomialRing(Integers())!UnivariatePolynomial(hred);
end intrinsic;
