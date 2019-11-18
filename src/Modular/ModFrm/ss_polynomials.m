////////////////////////////////////////////////////////////////////
//                                                                // 
//               ATKIN'S SUPERSINGULAR POLYNOMIALS                //
//                 Created sometime in 1998-99                    //
//                                                                // 
//////////////////////////////////////////////////////////////////// 

// intrinsics: SupersingularPolynomial(s)  

//////////////////////////////////////////////////////////////////// 
//                        Preliminaries                           //
//////////////////////////////////////////////////////////////////// 

function ModularGenusPrimeX0(p)
    n, r := Quotrem(p,12);
    if r in {2,3,5,7} then
	return n;
    elif r eq 11 then
	return n+1;
    end if;
    return n-1;
end function;

// Instead using built-in functions Eistenstein and Delta, despite 
// bugs when the base ring of power series is not the rationals. 

function EisensteinSeries(k,prec)
    // (k::RngIntElt,prec::RngIntElt) -> RngSerElt
    // {Returns the rational power series expansion of the kth 
    // Eisenstein series.} 
    q := LaurentSeriesRing(RationalField()).1; 
    return 1 + -2*k*(1/Bernoulli(k)) * 
    ( &+[ n^(k-1)*q^n/(1 - q^n + O(q^(prec+1))) 
    : n in [1..prec]] ) + O(q^(prec+1)); 
end function;

function PeterssonInnerProduct(f,g)
    // (f::RngSerElt,g::RngSerElt) -> Rng 
    // {Returns the Petersson inner product of weight zero modular 
    // functions f and g.}
    
    prec := Max(20,-Valuation(f*g)+1); 
    q := PowerSeriesRing(Integers()).1;
    E2 := Parent(f)!Eisenstein(2,q+O(q^prec)); 
    return Coefficient(f*g*E2,0); 
end function;

//////////////////////////////////////////////////////////////////// 
//                      End Preliminaries                         //
//////////////////////////////////////////////////////////////////// 

ClassNumberOne := [
    <-3,0>,
    <-4,1728>,
    <-8,8000>,
    <-7,16581375>,
    <-11,-32768>,
    <-19,-884736>,
    <-43,-884736000>,
    <-67, -147197952000^3>,
    <-163, -262537412640768000>
    ];
ClassNumberThree := [
    <-23, [ 12771880859375, -5151296875, 3491750, 1 ]>,
    <-31, [ 1566028350940383, -58682638134, 39491307, 1 ]>,
    <-59, [ 374643194001883136, -140811576541184, 30197678080, 1 ]>,
    <-83, [ 549755813888000000000,
    -41490055168000000, 2691907584000, 1 ]>,
    <-107, [ 337618789203968000000000,
    -6764523159552000000, 129783279616000, 1 ]>,
    <-139, [ 67408489017571610198016,
    -53041786755137667072, 12183160834031616, 1 ]>,
    <-211, [ 5310823021408898698117644288,
    277390576406111100862464, 65873587288630099968, 1 ]>,
    <-283, [ 201371843156955365375999999995,
    90839236535446929408000000, 89611323386832801792000, 1 ]>,
    <-307, [ 8987619631060626702335999999976,
    -5083646425734146162688000000, 805016812009981390848000, 1 ]>,
    <-331, [ 56176242840389398230218488592596992,
    368729929041040103875232661494, 6647404730173793386463232, 1 ]>,
    <-379, [ 15443600047689011948024601807532589056,
    -121567791009880876719538528324224, 364395404104624239018246144, 1 ]>,
    <-499, [ 4671133182399954782798673154503412008615936,
    -6063717825494266394722392560011051008, 
    3005101108071026200706725969876, 1 ]>,
    <-547, [ 83303937570678403968635240446255169536,
    -139712328431787827943469744130621440,
    81297395539631654721637478401920, 1 ]>,
    <-643, [ 308052554652302847380880841296488755349159936,
    -6300378505047247876499651797363778912256,
    39545575162726134099492467010830336, 1 ]>,
    <-883, [ 167990285381627318187575520797616325470810275840,
    -151960111125245282033875619526254370301673472,
    34903934341011819039224295011121589387264, 1 ]>,
    <-907, [ 149161274746524841328545894963365284840889909248,
    39181594208014819617565811573066584035426304,
    123072080721198402394477590503130537132032, 1 ]>
    ];

intrinsic SupersingularjInvariant(FF:FldFin) -> FldFinElt
    {A supersingular j-invariant over FF.} 
    p := Characteristic(FF);
    for disc in ClassNumberOne do
	if KroneckerSymbol(disc[1],p) ne 1 then
	    return FF!disc[2], disc[1];
	end if;
    end for;
    // The above covers the class number one fundamental discriminants.
    /*
    > discs1 := [ D : D in [-3..-1000 by -1] |
    >      D mod 4 in {0,1} and IsFundamental(D) and ClassNumber(D) eq 1 ];
    > discs1;
    [ -3, -4, -7, -8, -11, -19, -43, -67, -163 ]
    */
    // Next we can cover the class number three:
    /*
    > discs3 := [ D : D in [-3..-1000 by -1] |
    >      D mod 4 in {0,1} and IsFundamental(D) and ClassNumber(D) eq 3 ];
    > discs3;
    [ -23, -31, -59, -83, -107, -139, -211, -283, -307, -331, -379, -499,
    -547, -643, -883, -907 ]
    */
    // This guarantees a root in an odd degree extension if supersingular.
    // The first primes which are split in all discriminants of class number
    // one  appear above 10^4:
    /*
    > [ p : p in Primes([1..10^5]) |
    >     &and[ KroneckerSymbol(D,p) eq 1 : D in discs1 ] ];
    [ 15073, 18313, 38833, 69337, 71593 ]
    */
    // The first primes which are split in all discriminants of class number
    // three appear above 10^6:
    /*
    > [ p : p in Primes([1..10^7]) |
    >     &and[ KroneckerSymbol(D,p) eq 1 : D in discs3 ] ];
    [ 1848983, 1994983, 2388223, 2910329, 3443963, 3791093, 5693881, 6017399,
    6179311, 6395651, 7921229, 8290523 ]
    */
    P := PolynomialRing(FF);
    for disc in ClassNumberThree do
	if KroneckerSymbol(disc[1],p) ne 1 then
	    return Roots(P!disc[2])[1][1], disc[1];
	end if;
    end for;
    // This loop is unlikely to be visited, but will eventually catch any
    // other input prime: 
    D := -15;
    while true do
	if IsFundamental(D) and KroneckerSymbol(D,p) ne 1 then 
	    jinvs := Roots(P!HilbertClassPolynomial(D));
	    if #jinvs ne 0 then
		return jinvs[1][1], D;
	    end if;
	end if;
	D -:= D mod 4 eq 0 select 3 else 1;
    end while;	
end intrinsic; 

intrinsic SupersingularPolynomial(F::FldFin) -> RngUPolElt 
    {The supersingular polynomial over F.} 
    p := Characteristic(F);
    n := ModularGenusPrimeX0(p) + 1;
    K := FiniteField(p^2);
    j := K!SupersingularjInvariant(F);
    P<X,Y> := PolynomialRing(K,2);
    Phi := X^3 - X^2*Y^2 + Y^3 + 1488*(X^2*Y + X*Y^2) - 162000*(X^2+Y^2) 
	+ 40773375*X*Y + 8748000000*(X + Y) - 157464000000000;
    PK := PolynomialRing(K); x := PK.1;
    SS := {@ j @};
    j := 0;
    while #SS lt n do
	k := #SS;
	for i in [j+1..k] do
	    rts := Roots(Evaluate(Phi,[x,SS[i]]));
	    SS join:= {@ a[1] : a in rts @};
	end for;
	j := k;
    end while;
    PF := PolynomialRing(F);
    return PF!&*[ x-j : j in SS ];
end intrinsic; 

intrinsic SupersingularPolynomial(n::RngIntElt) -> RngUPolElt 
    {The nth Atkin supersingular polynomial.} 
    return SupersingularPolynomials(n,RationalField())[n+1]; 
end intrinsic; 

intrinsic SupersingularPolynomial(n::RngIntElt,R::Rng) -> RngUPolElt 
    {The nth Atkin supersingular polynomial.} 
    return SupersingularPolynomials(n,R)[n+1]; 
end intrinsic; 

intrinsic SupersingularPolynomials(n::RngIntElt) -> SeqEnum
    {The initial n Atkin supersingular polynomials.} 
    return SupersingularPolynomials(n,RationalField()); 
end intrinsic; 

intrinsic SupersingularPolynomials(n::RngIntElt,R::Rng) -> SeqEnum
    {The initial n Atkin supersingular polynomials over R.} 
    prec := 2*n+2;
    P := LaurentSeriesRing(R);
    q := LaurentSeriesRing(RationalField()).1;
    x := PolynomialRing(R).1;
    E4 := P!Eisenstein(4,q+O(q^prec)); 
    DD := P!Delta(q+O(q^prec)); 
    j := E4^3/DD;
    SSeq := [ x^0 ]; 
    for k in [1..n] do 
	ss := x^k; 
	for si in SSeq do 
	    f := Evaluate(si,j); 
	    g := Evaluate(ss,j); 
	    ss +:= -PeterssonInnerProduct(f,g) * si
		/ PeterssonInnerProduct(f,f); 
	end for; 
	Append(~SSeq,ss); 
    end for; 
    return SSeq;
end intrinsic; 

intrinsic SupersingularPolynomials(n::RngIntElt,R::Rng) -> SeqEnum
    {The initial n Atkin supersingular polynomials over R.} 
    
    prec := 2*n+2;
    P := LaurentSeriesRing(R);
    q := LaurentSeriesRing(RationalField()).1;
    x := PolynomialRing(R).1;
    E4 := P!Eisenstein(4,q+O(q^prec)); 
    DD := P!Delta(q+O(q^prec)); 
    j := E4^3/DD;
    SSeq := [ x^0 ]; 
    for k in [1..n] do 
	ss := x^k; 
	for si in SSeq do 
	    f := Evaluate(si,j); 
	    g := Evaluate(ss,j); 
	    ss +:= -PeterssonInnerProduct(f,g) * si
		/ PeterssonInnerProduct(f,f); 
	end for; 
	Append(~SSeq,ss); 
    end for; 
    return SSeq;
end intrinsic; 



