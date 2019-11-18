//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//           Algebraic Relations among Real and Complex Numbers             //
//         Copyright (C) 2010 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
David R. Kohel, 30/11/2005, creation
David R. Kohel, 20/07/2006, CommonAlgebraicRelations
David R. Kohel, 04/10/2010, GaloisDescentAlgebraicRelations
*/

declare verbose RealRelations, 2;

//////////////////////////////////////////////////////////////////////////////
// Algebraic relation in one variable.
//////////////////////////////////////////////////////////////////////////////

intrinsic AlgebraicRelation(x::FldReElt,n::RngIntElt : Al := "") -> RngUPolElt
    {An integral algebraic relation f(x) [= 0] for x; correct 
    nomenclature for builtin magma function PowerRelation.}
    if Al eq "" then
	Al := "LLL";
    end if;
    require Al in {"Hastad", "LLL"} :
	"Parameter Al must be on of \"Hastad\" or \"LLL\".";
    return PowerRelation(x,n : Al := Al);
end intrinsic;

intrinsic AlgebraicRelation(x::FldComElt,n::RngIntElt : Al := "") -> RngUPolElt
    {An integral algebraic relation f(x) [= 0] for x; correct 
    nomenclature for builtin magma function PowerRelation.}
    if Al eq "" then
	Al := "LLL";
    end if;
    require Al in {"Hastad", "LLL"} :
	"Parameter Al must be on of \"Hastad\" or \"LLL\".";
    if Abs(Imaginary(x)) lt Precision(x)-8 then
	x := Real(x);
    end if;
    return PowerRelation(x,n : Al := Al);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Real Fields
//////////////////////////////////////////////////////////////////////////////

intrinsic AlgebraicRelations(
    S::[FldReElt],degs::[RngIntElt] : Epsilon := 0) -> RngMPol
    {The ideal of relations between the elements of S, of coordinate degrees degs.}
    require Epsilon ge 0 and Epsilon lt 1 :
	"Parameter \"Epsilon\" must be in (0,1).";
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    r := #S;
    require #degs eq r : "Arguments must have the same length.";
    R := IntegerRing();
    P := PolynomialRing(R,r : Global := true);
    pows := [ [Universe(S)|1] : i in [1..r] ];
    for j in [1..r] do
	g := Universe(S)!1;
	for i in [1..degs[j]] do
	    g *:= S[j];
	    Append(~pows[j],g);
	end for;
    end for;
    Cdeg := CartesianProduct([{0..degs[j]}: j in [1..r]]);
    exps := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons,epsilon));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(
    S::[FldReElt],degs::[RngIntElt],tot::RngIntElt : Epsilon := 0)-> RngMPol
    {The ideal of relations between the elements of S, of total degree
    at most tot and coordinate degrees degs.}
    require Epsilon ge 0 and Epsilon lt 1 :
	"Parameter \"Epsilon\" must be in (0,1).";
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    r := #S;
    require #degs eq r : "Arguments must have the same length.";
    R := IntegerRing();
    P := PolynomialRing(R,r : Global := true);
    pows := [ [Universe(S)|1] : i in [1..r] ];
    for j in [1..r] do
	g := Universe(S)!1;
	for i in [1..degs[j]] do
	    g *:= S[j];
	    Append(~pows[j],g);
	end for;
    end for;
    Cdeg := CartesianProduct([{0..degs[j]}: j in [1..r]]);
    vecs := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    exps := [ e : e in vecs | &+e le tot ];
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons, epsilon));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(S::[FldReElt],deg::RngIntElt : Epsilon := 0)-> RngMPol
    {The ideal of relations between the elements of S, of degree at most deg.}
    require Epsilon ge 0 and Epsilon lt 1 :
	"Parameter \"Epsilon\" must be in (0,1).";
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    r := #S;
    R := IntegerRing();
    P := PolynomialRing(R,r : Global := true);
    pows := [ [Universe(S)|1] : i in [1..r] ];
    for j in [1..r] do
	g := Universe(S)!1;
	for i in [1..deg] do
	    g *:= S[j];
	    Append(~pows[j],g);
	end for;
    end for;
    Cdeg := CartesianPower({0..deg},r);
    vecs := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    exps := [ e : e in vecs | &+e le deg ];
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons, epsilon));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(x::FldReElt,y::FldReElt,deg::RngIntElt : Epsilon := 0) -> RngMPolElt 
    {}
    require Epsilon ge 0 and Epsilon lt 1 :
	"Parameter \"Epsilon\" must be in (0,1).";
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    R := IntegerRing();
    P := PolynomialRing(R,2 : Global := true);
    X := P.1; Y := P.2;
    for n1 in [1..deg] do
	for n2 in [1..deg] do
	    combs := [ x^(n1-i)*y^(n2-j) : j in [0..n2], i in [0..n1] ];
	    V := LinearRelations(combs,epsilon);
	    if Dimension(V) gt 0 then
		return [ &+[ c[(n2+1)*i+j+1]*X^(n1-i)*Y^(n2-j) 
		    : j in [0..n2], i in [0..n1] ] : c in Basis(V) ];
	    end if;
	end for;
    end for;
    return [ P | ];
end intrinsic;

intrinsic AlgebraicRelations(
    x::FldReElt,y::FldReElt,z::FldReElt,deg::RngIntElt : Epsilon := 0) -> RngMPolElt
    {}
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    R := IntegerRing();
    P := PolynomialRing(R,3 : Global := true);
    X := P.1; Y := P.2; Z := P.3; 
    for n1 in [1..deg] do
	for n2 in [1..deg] do
	    for n3 in [1..deg] do
		V := LinearRelations([ x^(n1-i)*y^(n2-j)*z^(n3-k) : 
		    i in [0..n1], j in [0..n2], k in [0..n3] ], epsilon);
		if Dimension(V) gt 0 then
		    return [ &+[ c[i+(n1+1)*j+(n2+1)*(n1+1)*k+1]
			*X^(n1-i)*Y^(n2-j)*Z^(n3-k)  
			: i in [0..n1], j in [0..n2], k in [0..n3] ]
			: c in Basis(V) ];       
		end if;
	    end for;
	end for;
    end for;
    return [ P | ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Complex Fields
//////////////////////////////////////////////////////////////////////////////

intrinsic AlgebraicRelations(S::[FldComElt],degs::[RngIntElt] : Epsilon := 0) -> RngMPol
    {The ideal of relations between the elements of S, of coordinate degrees degs.}
    require Epsilon ge 0 and Epsilon lt 1 :
	"Parameter \"Epsilon\" must be in (0,1).";
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    r := #S;
    require #degs eq r : "Arguments must have the same length.";
    R := IntegerRing();
    P := PolynomialRing(R,r : Global := true);
    pows := [ [Universe(S)|1] : i in [1..r] ];
    for j in [1..r] do
	g := Universe(S)!1;
	for i in [1..degs[j]] do
	    g *:= S[j];
	    Append(~pows[j],g);
	end for;
    end for;
    Cdeg := CartesianProduct([{0..degs[j]}: j in [1..r]]);
    exps := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons,epsilon));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(S::[FldComElt],degs::[RngIntElt],tot::RngIntElt : Epsilon := 0)-> RngMPol
    {The ideal of relations between the elements of S, of total degree
    at most tot and coordinate degrees degs.}
    require Epsilon ge 0 and Epsilon lt 1 :
	"Parameter \"Epsilon\" must be in (0,1).";
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    r := #S;
    require #degs eq r : "Arguments must have the same length.";
    R := IntegerRing();
    P := PolynomialRing(R,r : Global := true);
    pows := [ [Universe(S)|1] : i in [1..r] ];
    for j in [1..r] do
	g := Universe(S)!1;
	for i in [1..degs[j]] do
	    g *:= S[j];
	    Append(~pows[j],g);
	end for;
    end for;
    Cdeg := CartesianProduct([{0..degs[j]}: j in [1..r]]);
    vecs := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    exps := [ e : e in vecs | &+e le tot ];
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons, epsilon));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(S::[FldComElt],deg::RngIntElt : Epsilon := 0)-> RngMPol
    {The ideal of relations between the elements of S, of degree at most deg.}
    require Epsilon ge 0 and Epsilon lt 1 :
	"Parameter \"Epsilon\" must be in (0,1).";
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    r := #S;
    R := IntegerRing();
    P := PolynomialRing(R,r : Global := true);
    pows := [ [Universe(S)|1] : i in [1..r] ];
    for j in [1..r] do
	g := Universe(S)!1;
	for i in [1..deg] do
	    g *:= S[j];
	    Append(~pows[j],g);
	end for;
    end for;
    Cdeg := CartesianPower({0..deg},r);
    vecs := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    exps := [ e : e in vecs | &+e le deg ];
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons, epsilon));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(x::FldComElt,y::FldComElt,deg::RngIntElt : Epsilon := 0) -> RngMPolElt 
    {}
    require Epsilon ge 0 and Epsilon lt 1 :
	"Parameter \"Epsilon\" must be in (0,1).";
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    R := IntegerRing();
    P := PolynomialRing(R,2 : Global := true);
    X := P.1; Y := P.2;
    for n1 in [1..deg] do
	for n2 in [1..deg] do
	    combs := [ x^(n1-i)*y^(n2-j) : j in [0..n2], i in [0..n1] ];
	    V := LinearRelations(combs,epsilon);
	    if Dimension(V) gt 0 then
		return [ &+[ c[(n2+1)*i+j+1]*X^(n1-i)*Y^(n2-j) 
		    : j in [0..n2], i in [0..n1] ] : c in Basis(V) ];
	    end if;
	end for;
    end for;
    return [ P | ];
end intrinsic;

intrinsic AlgebraicRelations(
    x::FldComElt,y::FldComElt,z::FldComElt,deg::RngIntElt : Epsilon := 0) -> RngMPolElt
    {}
    if Epsilon ne 0 then
	epsilon := Epsilon;
    else
	epsilon := 0.10^6;
    end if;
    R := IntegerRing();
    P := PolynomialRing(R,3 : Global := true);
    X := P.1; Y := P.2; Z := P.3; 
    for n1 in [1..deg] do
	for n2 in [1..deg] do
	    for n3 in [1..deg] do
		V := LinearRelations([ x^(n1-i)*y^(n2-j)*z^(n3-k) : 
		    i in [0..n1], j in [0..n2], k in [0..n3] ], epsilon);
		if Dimension(V) gt 0 then
		    return [ &+[ c[i+(n1+1)*j+(n2+1)*(n1+1)*k+1]
			*X^(n1-i)*Y^(n2-j)*Z^(n3-k)  
			: i in [0..n1], j in [0..n2], k in [0..n3] ]
			: c in Basis(V) ];       
		end if;
	    end for;
	end for;
    end for;
    return [ P | ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Common algebraic relations
//////////////////////////////////////////////////////////////////////////////

intrinsic CommonAlgebraicRelations(
    S::SeqEnum[SeqEnum[FldReElt]],n::RngIntElt : RelativePrecision := 4) -> SeqEnum
    {}
    require RelativePrecision ge 0 :
	"Parameter RelativePrecision must be positive.";
    Epsilon := 10^RelativePrecision;
    m := #S;
    require m gt 0 : "Argument 1 must be nonempty.";
    t := #S[1]; 
    RR := Universe(S[1]);
    PR := PolynomialRing(Integers(),t : Global);
    prec := Precision(RR) - 8;
    mons := &join[ MonomialsOfDegree(PR,i) : i in [0..n] ];
    // Or for homogeneous relations:
    //mons := MonomialsOfDegree(PR,n);
    ScaledInteger := func< x,r | Round(x*10^r) >;
    M := Matrix([ [ ScaledInteger(Evaluate(m,x),prec) : x in S ] : m in mons ]);
    // append a row of zeros to remove trivial precision:
    N := VerticalJoin(M,IdentityMatrix(Integers(),m));
    R := LLL(BasisMatrix(Kernel(N)));
    B := [];
    for i in [1..Nrows(R)] do
	v := Vector(Eltseq(R[i])[[1..#mons]]);
	if Norm(v*M) lt Epsilon then
	    Append(~B,v);
	end if;
    end for;
    return [ &+[ v[i]*mons[i] : i in [1..#mons] ] : v in B ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Galois descent algebraic relations
//////////////////////////////////////////////////////////////////////////////

/*
H1 := 2518902144129206153928896785198150904361770126557942653025*x^10
  - 628143425894924040722454241386930124944720511350040582086334314124592949573120*x^9
  - 11677041788980528563059303692433056514290151963624804205916035287236952619421496692858551279661056*x^8
  + 17531494536683026019718717496920136874797952577156261116479653274645043350144735394315179447364402716724428800*x^7
  - 487284567309551342209963423894664011621536078130483159416783915485163357013743320901414773404443341534133935732097716060160*x^6
  + 2656720670708565568850655223551839124882268664353815629455415344768633270894175051332437344013180319981503290852559767964417313996800*x^5 
  - 2312830671476719986444161007705385651042156348725151972763876721279144908630687663600172549489903665314197062158580416816621866266797530372322099200*x^4 
  - 64164178885684838098802771643579643848510963721994735265042430158056744929363619473143985861631823862646339320121550721966419298226349502331822800896000*x^3 
  - 81542710296406490436836240326477119544903789809212981693787858867047773419799420114938922806303176639504663662295147262731907720117908657227848324086759424000*x^2 
  - 75402118618233414347496990362844919200834633488636152397107832307958583985059308211317178286286097785032923068900458051752607134773639479218287175837134356480000*x 
  - 17438345335260485163861868719284585291772064463385611326398228870931987199836874983741555280900149092290930906423387283333866101699861617265102407873561215631360000;
CC := ComplexField(512);
rts := [ r[1] : r in Roots(H1,CC) ];
GaloisDescentAlgebraicRelations(rts);
*/

intrinsic GaloisDescentAlgebraicRelation(
    roots::SeqEnum[FldComElt]) -> RngUPolElt
    {Given a complete sequence roots of approximations in R (real, complex,
    or p-adic) to the roots of a polynomial f in ZZ[x], computes f.}
    n := #roots;
    R := Universe(roots);
    ZZ := IntegerRing();
    PR := PolynomialRing(R);
    PZ := PolynomialRing(ZZ);
    symm := Eltseq(&*[ PR.1 - a : a in roots ]);
    cffs := [ ZZ | ];
    dens := [ ZZ | ];
    base := [ R!1 ];
    for i in [1..n] do
	Vi := LinearRelations([-Real(symm[i]),1]);
	vi := Eltseq(Vi.1);
	require vi[1] ne 0 : "Given input has insufficient precision.";
	Append(~dens,vi[1]);
	Append(~cffs,vi[2]);
    end for;
    N := LCM(dens);
    for i in [1..n] do
	cffs[i] *:= N div dens[i];
    end for;
    Append(~cffs,N);
    return PZ!cffs;
end intrinsic;

intrinsic GaloisDescentAlgebraicRelation(roots::SeqEnum[FldComElt],phi::Map) -> RngUPolElt
    {Given a complete sequence roots of approximations in R (real, complex,
    or p-adic) to the roots of a polynomial f in S[x], where S is finite
    over Z, with a map S -> R, computes f.}
    
    n := #roots;
    R := Universe(roots);
    require Codomain(phi) cmpeq R or Codomain(phi) cmpeq RealField(R) :
        "Argument 2 must have codomain contained in the universe of argument 1.";
    PR := PolynomialRing(R);
    symm := Eltseq(&*[ PR.1 - a : a in roots ]);
    if Codomain(phi) cmpeq RealField(R) then
        // Sanity check:
        require &and[ Abs(Im(si)) lt 0.01 : si in symm ] :
            "Argument 1 must contain all roots in complex conjugate pairs.";
        symm := [ Real(si) : si in symm ]; 
    end if;
    S := Domain(phi);
    PS := PolynomialRing(S);
    B := Type(S) eq RngInt select [1] else Basis(S);
    r := #B;
    ZZ := IntegerRing();
    cffs := [ RSpace(ZZ,r) | ];
    dens := [ ZZ | ];
    base := [ phi(b) : b in B ];
    for i in [1..n] do
	Vi := LinearRelations([-symm[i]] cat base);
        vi := Eltseq(Vi.1);
        print "c =", -symm[i];
        print Vi;
	require vi[1] ne 0 : "Given input has insufficient precision.";
	Append(~dens,vi[1]);
	Append(~cffs,vi[[2..#vi]]);
    end for;
    N := LCM(dens);
    for i in [1..n] do
	cffs[i] *:= N div dens[i];
    end for;
    cffs := [ S!Eltseq(c) : c in cffs ] cat [N];
    return PS!cffs;
end intrinsic;
