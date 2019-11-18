////////////////////////////////////////////////////////////////////////
//                                                                    //
//            REPRESENTATIONS OF RATIONAL QUADRATIC SPACES            //
//                            David Kohel                             //
//                            April 2000                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic CommonRepresentationsTest() 
    {}
    function BadPrimes(a,b,c)
	prms := Sort(SetToSequence(SequenceToSet(
	    &cat[ PrimeDivisors(x) : x in [a,b,c] ])));
	return [ p : p in prms | HilbertSymbol(-a*c,-b*c,p) eq -1 ];
    end function;
    TestPairs := [ 
	[ [ 34, 510 ], [ 1, -185 ] ],
	[ [ 33, 1155 ], [ 1, -2345 ] ], 
	[ [ 3, 3 ], [ 19, 11 ] ],
	[ [ 7, 77 ], [ 5, 86 ] ],
	[ [ 7, 7 ], [ 3, 58 ] ],
	[ [ 51, 6 ], [ 74, 73 ] ],
	[ [ 23, 838 ], [ 21, 413 ] ],
	[ [ 105, 105 ], [ 1, -22 ] ]
	];
    for Pair in TestPairs do
	S1, S2 := Explode(Pair);
	n := CommonRepresentation(S1,S2);
	print "Input:";
	print "S1:", S1;
	print "S2:", S2;
	print "Output:";
	print "n =", n;
	P1 := BadPrimes(a,b,-n) where a,b := Explode(S1);
	P2 := BadPrimes(a,b,-n) where a,b := Explode(S2);
	"Bad primes:", P1;
	"Bad primes:", P2;
	assert #P1 eq 0 and #P2 eq 0;
    end for;
end intrinsic;

forward NormalizeSquareAndGCD, NormalizeSwap, SplitPrimeBase;
forward CharacterVector, pAdic2Representations; 

////////////////////////////////////////////////////////////////////////

function RationalSquareFree(x)
    if Type(x) eq RngIntElt then return SquareFree(x); end if;
    s1, m1 := SquareFree(Numerator(x));
    s2, m2 := SquareFree(Denominator(x));
    return s1*s2, m1*m2;
end function;

function ConicPoint(S)
    PP := ProjectivePlane(Rationals());
    C := Conic(PP,S[1]*PP.1^2+S[2]*PP.2^2+S[3]*PP.3^2);
    bool, P := HasPoint(C);
    error if not bool,
	"Failed to find point on conic.";
    return Eltseq(P);
end function; 

////////////////////////////////////////////////////////////////////////

/*
intrinsic Representation(V::ModTupFld,n::RngIntElt) -> ModTupFldElt
    {A vector representing the integer a.}
    require Type(BaseRing(V)) eq FldRat :
	"Argument 1 must be defined over the rationals";
    if n eq 0 then
	require IsIsotropic(V) : 
	    "Argument 1 does not represent argument 2";
    end if;
    r := Dimension(V);
    if r eq 1 then
	if n eq 0 then
	    return V.1;
	else
	    _, m := IsSquare(n/Norm(V.1));
	    return m*V.1;
	end if;  
    elif n ne 0 then
	W := RSpace(RationalField(),r+1,
	    DirectSum(GramMatrix(V),
	    MatrixAlgebra(RationalField(),1)![-n]));
	require IsIsotropic(W) : 
	    "Argument 1 does not represent argument 2";
	v := Representation(W,0);
	return &+[ v[i]*B[i]/v[r+1] : i in [1..r] ] where B is Basis(V);
    end if;
    D, N := OrthogonalizeGram(GramMatrix(V));
    if r eq 2 then
	if D[1,1] eq 0 then
	    return V.1*N[1,1] + V.2*N[1,2];
	end if;
	_, a := IsSquare(-D[2,2]/D[1,1]);
	a1 := Numerator(a);
	a2 := Denominator(a);
	return (a1*N[1,1] + a2*N[2,1])*V.1 
	    + (a1*N[1,2] + a2*N[2,2])*V.2;
    elif r eq 3 then
	N[1] *:= 1/Denominator(D[1,1]);
	N[2] *:= 1/Denominator(D[2,2]);
	N[3] *:= 1/Denominator(D[3,3]);
	a := Numerator(D[1,1])*Denominator(D[1,1]); 
	b := Numerator(D[2,2])*Denominator(D[2,2]);
	c := Numerator(D[3,3])*Denominator(D[3,3]);
	return (V!Eltseq(ConicPoint([a,b,c])))*N;
    elif r eq 4 then
	a,b,c,d := Explode([ D[i,i] : i in [1..r] ]);
	a1, r1 := RationalSquareFree(a);
	b1, r2 := RationalSquareFree(b);
	c1, r3 := RationalSquareFree(c);
	d1, r4 := RationalSquareFree(d);
	N[1] *:= r1;   
	N[2] *:= r2;   
	N[3] *:= r3;   
	N[4] *:= r4;   
	m := GCD([a1,b1,c1,d1]);
	a1 div:= m; b1 div:= m; c1 div:= m; d1 div:= m;
	t := CommonRepresentation([a1,b1],[-c1,-d1]);
	P1 := ConicPoint([a1,b1,-t]);
	P2 := ConicPoint([c1,d1,t]);
	S := [ P1[1]*P2[3], P1[2]*P2[3], P2[1]*P1[3], P2[2]*P1[3] ]; 
	return (V![ x div GCD(S) : x in S ])*N;
    end if;
    S := [ Numerator(D[i,i])*Denominator(D[i,i]) : i in [1..r] ];
    for i in [1..r] do
	N[i] *:= 1/Denominator(D[i,i]);
    end for;
    S1, N1 := WittReduction(S);
    N := N*N1;
    print "S1 =", S1;
    print "N =", N;
    require false : "Not implemented";
end intrinsic;
*/

////////////////////////////////////////////////////////////////////////

function Chi(p,q)
    // assume p is square free and q prime
    if q in {1,2} and p mod 2 eq 0 then p div:= 2; end if;
    case q:
    when 0:
	e := -(-1)^(p mod 2);
    when 1:
	e := KroneckerSymbol(-1,p);
    else
	e := KroneckerSymbol(p,q);
    end case;
    return (1-e) div 2;
end function;

intrinsic CommonRepresentation(S1::[RngIntElt],S2::[RngIntElt] : 
    MaxPrimeBase := 128) -> RngIntElt
    {For sequences of integers S1 = [a,b] and S2 = [c,d] returns
    an integer n such that there exists rational numbers x, y, z, 
    and w with a*x^2 + b*y^2 = n and c*z^2 + d*w^2 = n.}
    
    // Begin normalization. 
    vprint QuadraticForm, 1 :
	"  Searching for common representation of rational forms:";
    vprint QuadraticForm, 1 : "    S1:", S1;
    vprint QuadraticForm, 1 : "    S2:", S2;
    vprint QuadraticForm, 1 : "  Renormalising:";
    S1, S2, m0 := NormalizeSquareAndGCD(S1,S2);
    vprint QuadraticForm, 1 : "    S1:", S1;
    vprint QuadraticForm, 1 : "    S2:", S2;
    require m0 ne 0 : "Arguments have no common representation";
    m1 := GCD(S1); m2 := GCD(S2);
    vprint QuadraticForm, 1 : "    m0:", m0;
    vprint QuadraticForm, 1 : "    m1:", m1;
    vprint QuadraticForm, 1 : "    m2:", m2;
    // End normalization. 
    qq1 := Sort(Exclude(&cat[ PrimeDivisors(x div m1) : x in S1 ],2));
    qq2 := Sort(Exclude(&cat[ PrimeDivisors(x div m2) : x in S2 ],2));
    ch1 := CharacterVector(S1,qq1);
    ch2 := CharacterVector(S2,qq2);
    val := true;
    NormalizeSwap(~S1,~S2,~ch1,~ch2,~m0,~val,qq1,qq2);
    vprint QuadraticForm, 1 : "  Swapping to:";
    vprint QuadraticForm, 1 : "    S1:", S1;
    vprint QuadraticForm, 1 : "    S2:", S2;
    vprint QuadraticForm, 1 : "    m0:", m0;
    require val : "Arguments have no common representation";
    R2 := pAdic2Representations(S1) meet pAdic2Representations(S2);
    require #R2 ne 0 : "Arguments have no common representation";
    qq := Sort(SetToSequence(SequenceToSet([0,1,2] cat qq1 cat qq2)));
    V2 := RSpace(GF(2),#qq);
    Z2 := [ 0 : j in [4..#qq] ];
    G2 := [ V2!([ Chi(p,q) : q in [0,1,2] ] cat Z2) : p in R2 ];
    B2 := Basis(sub< V2 | [ G2[1] - G2[i] : i in [2..#G2] ] >);
    v1 := G2[1];
    for k in [4..#qq] do
	q := qq[k];
	i1 := Index(qq1,q);
	i2 := Index(qq2,q);
	v1[k] := i1 ne 0 select ch1[i1] else ch2[i2];
	// if i1 ne 0 and i2 ne 0 then assert ch1[i1] eq ch2[i2]; end if;
    end for;
    D1 := D eq 1 select 1 else FundamentalDiscriminant(D) where D := -&*S1;
    D2 := D eq 1 select 1 else FundamentalDiscriminant(D) where D := -&*S2;
    vprint QuadraticForm, 1 : "  Discriminant D1:", D1;
    vprint QuadraticForm, 1 : "  Discriminant D2:", D2;
    qrms1 := PrimeDivisors(m1);
    qrms2 := PrimeDivisors(m2);
    P1 := [ Integers() | p : p in qrms1 | KroneckerSymbol(D2,p) eq 1 ];
    P2 := [ Integers() | p : p in qrms2 | KroneckerSymbol(D1,p) eq 1 ];
    vprint QuadraticForm, 1 : "  Auxilliary primes P1:", P1;
    vprint QuadraticForm, 1 : "  Auxilliary primes P2:", P2;
    vprint QuadraticForm, 1 : "  Ramified primes qq:", qq;
    assert &and[ Booleans() |
	p mod q ne 0 : p in P1, q in qq | q notin {0,1,2} ];
    assert &and[ Booleans() |
	p mod q ne 0 : p in P2, q in qq | q notin {0,1,2} ];
    prm_num := #qq-2;
    repeat
	prm_num +:= 2;
	PB := SplitPrimeBase([D1,D2],prm_num); // +merge P1 & P2:
	PB := Sort(SetToSequence(SequenceToSet(&cat[ P1,P2,PB ])));
	CharMat := Matrix(
	    [ V2 | [ Chi(p,q) : q in qq ] : p in PB ] cat B2);
	val, u1 := IsConsistent(CharMat,v1);
	error if prm_num ge MaxPrimeBase, "Excessive prime base size.";
    until val;
    vprint QuadraticForm, 1 : "  Found consistent vector:", u1;
    n := &*[ Integers() | PB[j] : j in [1..#PB] | u1[j] ne 0 ];
    if GetVerbose("QuadraticForm") ge 2 then
	function BadPrimes(a,b,c)
	    prms := Sort(SetToSequence(SequenceToSet(
		&cat[ PrimeDivisors(x) : x in [a,b,c] ])));
	    return [ p : p in prms | HilbertSymbol(-a*c,-b*c,p) eq -1 ];
	end function;
	print "  qq:", qq;
	print "  Target vector:", v1;
	print "      S1 vector:", CharacterVector(S1,qq);
	print "      S1 mask v:",
	    V2![ p in {0,1,2} or p in qq1 select 1 else 0 : p in qq ];
	print "      S2 vector:", CharacterVector(S2,qq);
	print "      S2 mask v:",
	    V2![ p in {0,1,2} or p in qq2 select 1 else 0 : p in qq ];
	for j in [1..#PB] do
	    if u1[j] ne 0 then
		printf "  PB vector %3o: %o\n",
		    PB[j], V2![ Chi(PB[j],q) : q in qq ];
	    end if;
	end for;
	print "  Nimage vector:", V2![ Chi(n,q) : q in qq ];
	print "  BadPrimes S1:",
	    BadPrimes(a,b,-n) where a,b := Explode(S1);
	print "  BadPrimes S2:",
	    BadPrimes(a,b,-n) where a,b := Explode(S2);
    end if;
    vprint QuadraticForm, 1 : "  Found n =", n;
    vprint QuadraticForm, 1 : "  with cofactor m0 =", m0;
    return m0*n;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                        ACCESSORY FUNCTIONS                         //
////////////////////////////////////////////////////////////////////////

function NormalizeSquareAndGCD(S1,S2) 
    S := S1 cat S2;
    S := [ RationalSquareFree(x) : x in S ];
    m0 := GCD(S);
    S := [ x div m0 : x in S ];
    u1 := &+[ Sign(x) : x in S1 ];
    u2 := &+[ Sign(x) : x in S2 ];
    if u1*u2 eq -4 then
	m0 := 0;
    elif (u1 + u2) lt 0 then
	S := [ -x : x in S ];
	m0 *:= -1; 
    end if;
    for I in Subsets({1,2,3,4},3) do
	n1 := GCD([ S[i] : i in I ]);
	if n1 ne 1 then
	    for i in I do
		S[i] div:= n1; 
	    end for;
	    j := Rep({ k : k in [1..4] | k notin I });
	    S[j] *:= n1;
	    m0 *:= n1;
	end if;
    end for;
    return [ S[1], S[2] ], [ S[3], S[4] ], m0;
end function;

procedure NormalizeSwap(~S1,~S2,~char1,~char2,~m0,~val,prms1,prms2)
    common_prms := SequenceToSet(prms1) meet SequenceToSet(prms2);
    for p in common_prms do
	i := Index(prms1,p);
	j := Index(prms2,p);
	if char1[i] ne char2[j] then
	    if S1[1] mod p eq 0 then
		S1[1] div:= p; 
		S1[2] *:= p; 
	    else 
		S1[1] *:= p; 
		S1[2] div:= p; 
	    end if;
	    if S2[1] mod p eq 0 then
		S2[1] div:= p; 
		S2[2] *:= p; 
	    else 
		S2[1] *:= p; 
		S2[2] div:= p; 
	    end if;
	    char1 := CharacterVector(S1,prms1);
	    char2 := CharacterVector(S2,prms2);
	    m0 *:= p;
	    if char1[i] ne char2[j] then
		val := false;
	    end if;
	end if;
    end for;
end procedure;

function CharacterVector(S,prms)
    // The sequence of characters at the primes in prms.
    char := [ FiniteField(2) | ];
    for p in prms do 
	if p in {0,1,2} then
	    G2 := pAdic2Representations(S);
	    e := Chi(Representative(G2),p);
	    Append(~char,e);
	elif S[1] mod p eq 0 then
	    assert S[2] mod p ne 0;
	    e := Chi(S[2],p);
	    Append(~char,e);
	else 
	    e := Chi(S[1],p);
	    Append(~char,e);
	end if;
    end for;
    return Vector(char);
end function;

function SplitPrimeBase(D,n)
    p := 2;
    prmbase := [ p ];
    while #prmbase lt n do
	p := NextPrime(p);
	if &and [ KroneckerSymbol(D[i],p) eq 1 : i in [1,2] ] then
	    Append(~prmbase,p);
	end if;
    end while;
    return prmbase;
end function;

function pAdic2Class(x)
    while x mod 4 eq 0 do
	x div:= 4; 
    end while;
    if x mod 2 eq 1 then 
	return x mod 8;
    end if;
    return x mod 16;
end function;

function pAdic2Representations(S)
    a := pAdic2Class(S[1]);
    b := pAdic2Class(S[2]);
    c := pAdic2Class(a*b);
    case c:
    when 1: return { pAdic2Class(a*5^i*2^j) : i,j in [0,1] };
    when 3: return { pAdic2Class(a*3^i*5^j) : i,j in [0,1] };
    when 5: return { pAdic2Class(a*5^i*6^j) : i,j in [0,1] };
    when 7: return { 1,3,5,7,2,6,10,14 };
    when 2: return { pAdic2Class(a*3^i*2^j) : i,j in [0,1] };
    when 6: return { pAdic2Class(a*7^i*6^j) : i,j in [0,1] };
    when 10: return { pAdic2Class(a*3^i*10^j) : i,j in [0,1] };
    when 14: return { pAdic2Class(a*7^i*2^j) : i,j in [0,1] };
    end case;
end function;
