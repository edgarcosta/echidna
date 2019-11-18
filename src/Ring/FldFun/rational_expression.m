//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//    Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu.au>              //
//                                                                          //
//    Distributed under the terms of the GNU General Public License (GPL)   //
//    Full text of the GPL is available at: http://www.gnu.org/licenses/    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
EXAMPLE 1 (Univariate):

P<x> := PolynomialRing(Integers());
K<i> := NumberField(x^2+1);
F<t> := FunctionField(K);
s := (t^3-3*i*t-i-1)/(t^2+(-i+1)*t-i);
d1 := 5/2^6/3^2*s*(s+1/5*(6*i - 6))/(s+1/2*(3*i - 3))^2;
d2 := 2^6*3^3*(79*s^5+63*(i-1)*s^4+4134*i*s^3 - 11880*(i+1)*s^2+46737/2*s
  + 1/2*15633*(i-1))/(s+1/2*(3*i-3))^3/(s^2-3*(i-1)*s+9*i);
d3 := -2^5*3^2*7*(11*s+15*(i-1))^2*(s+3*(i-1))*(s^3
  - 1/7*33*(i-1)*s^2+162/7*i*s-81/7*(i+1))/(s+3/2*(i-1))^4/(s^2-3*(i-1)*s+9*i);
d4 := -2^12*3^4*(s^3+63/2*(i-1)*s^2-135*i*s
 + 297/4*(i+1))*(74*s^4-2151*(i-1)*s^3+2*7650*i*s^2
 - 34425/2*(i+1)*s+12717)/(s+3/2*(i-1))^5/(s^2-3*(i-1)*s+9*i);
d5 := -2^12*3^5*(11*s+15*(i-1))*(169*s^9-129*(i-1)*s^8-116277/2*i*s^7
 + 140355*(i+1)*s^6+2677239/2*s^5+1/2*13581999*(i-1)*s^4
 - 197072271/8*i*s^3+1/4*90568773*(i+1)*s^2-84831543/4*s
 - 4035015*(i-1))/(s+3/2*(i-1))^6/(s^2-3*(i-1)*s+9*i)^2;
d6 := -2^32*3^28*(s-5/3*(i-1))*(s+i-1)^6/(s+3/2*(i-1))^9/(s^2-3*(i-1)*s+9*i)^3;
dd := [ d1, d2, d3, d4, d5, d6 ];
Q<s> := FunctionField(K : Global := false);
s := (t^3-3*i*t-i-1)/(t^2+(-i+1)*t-i);
[ RationalExpression(di, s : RelationFunctionField := Q) : di in [d1,d2,d3] ];

EXAMPLE 2 (Multivariate):

F<a,b,c> := FunctionField(RationalField(),3);
PP<X,Y,Z> := PolynomialRing(F,3);
PolyX2 := (X^2-Y*Z)^2+Y*Z*(-2*X+Y+Z)*(a*X+b*Y+c*Z);
DD := DixmierInvariants(PolyX2);
rels := [ a+2*b+2*c, -a^2+4*b*c, a*(a+2*b)*(a+2*c) ];
R<u,v,w> := FunctionField(RationalField(),3);
[ 
   RationalExpression(ii,rels :
       RelationFunctionField := R) : ii in DD 
];

EXAMPLE 3 (Multivariate):

P<x> := PolynomialRing(RationalField());
K<i> := NumberField(x^2+1);
F<a,b,c> := FunctionField(K,3);
PP<X,Y,Z> := PolynomialRing(F,3);
PolyX3 := X^4-Y*Z*(2*X-Y)*(2*X-Z) +
    Y*Z*(-2*X+(1+i)*Y + (1-i)*Z)*(a*X+b*Y+c*Z);
DD := DixmierInvariants(PolyX3);
aa := a;
bb := -i*a + (1-i)*c;
cc := i*a + (1+i)*b;
rels := [
    aa+bb+cc,
    aa*bb + bb*cc + aa*cc,
    aa*bb*cc,
    aa^2*bb + bb^2*cc + aa*cc^2
];
R<s1,s2,s3,t3> := FunctionField(K,4);
RationalExpression(DD[1],rels : RelationFunctionField := R);
[ 
   RationalExpression(ii,rels :
       RelationFunctionField := R) : ii in DD 
];
*/

intrinsic RationalExpression(f::FldFunRatMElt,rels::[FldFunRatMElt] :
    RelationFunctionField := false) -> FldFunRatMElt
    {Express f as a rational expression in the elements of rels.}
    Q := Parent(f);
    require Q eq Universe(rels) :
	"Parent of argument 1 must equal the universe of argument 2.";
    n := Rank(Q);
    m := #rels;
    P := PolynomialRing(BaseRing(Q),n+m+1);
    mons := [ P.i : i in [1..n] ];
    numf := Evaluate(Numerator(f),mons);
    denf := Evaluate(Denominator(f),mons);
    nums := [ Evaluate(Numerator(g),mons) : g in rels ];
    dens := [ Evaluate(Denominator(g),mons) : g in rels ];
    I := ideal< P |
	[ nums[i] - dens[i]*P.(n+i) : i in [1..m] ] cat 
	[ numf - denf*P.(n+m+1) ] >;
    J := EliminationIdeal(I,{ P.(n+i) : i in [1..m+1] });
    B := [ f : f in Basis(J) | Degree(f,n+m+1) eq 1 ];
    if #B eq 0 then
	//P<a,b,c,u,v,w,F> := P;
	Qnames := [ Sprint(Name(Q,i)) : i in [1..n] ];
	Rnames := [ "X" * Sprint(j) : j in [1..m] ] cat ["F"];
	AssignNames(~P,Qnames cat Rnames);
	print "Basis of elimination ideal:";
	print Basis(J);
	print "Factorization:";
	print Factorization(Basis(J)[1]);
	print "Base ring:", BaseRing(Q);
	require false : 
	    "Argument 1 does not have a rational expression in argument 2.";
    end if;
    rat := B[1];
    num := Evaluate(rat,[ P.i : i in [1..n+m] ] cat [0]);
    den := (num-rat) div P.(n+m+1);
    if Type(RelationFunctionField) eq FldFunRat then
	R := RelationFunctionField;
    else
	R := FunctionField(BaseRing(Q),m : Global);
    end if;
    new_mons := [ 0 : i in [1..n] ] cat [ R.i : i in [1..m] ] cat [0];
    return Evaluate(num,new_mons)/Evaluate(den,new_mons);
end intrinsic;

intrinsic RationalExpression(f::FldFunRatUElt,y::FldFunRatUElt :
    Al := "Resultant", RelationFunctionField := false) -> FldFunRatUElt
    {Express f as a rational expression in y.}
    Q := Parent(f);
    require Q eq Parent(y):
	"Parent of argument 1 must equal the parent of argument 2.";
    require Al in {"EliminationIdeal","Resultant"}:
	"Parameter 'Al' must be 'EliminationIdeal' or 'Resultant'.";
    P := PolynomialRing(BaseRing(Q),3);
    numf := Evaluate(Numerator(f),P.1);
    denf := Evaluate(Denominator(f),P.1);
    numy := Evaluate(Numerator(y),P.1);
    deny := Evaluate(Denominator(y),P.1);
    F1 := numy - deny*P.2;
    F2 := numf - denf*P.3;
    if Al eq "EliminationIdeal" then
	I := ideal< P | F1, F2 >;
	J := EliminationIdeal(I,{ P.2, P.3 });
	B := [ f : f in Basis(J) | Degree(f,3) eq 1 ];
    else
	assert Al eq "Resultant";
	Res := Resultant(F1,F2,1);
	fac := Factorization(Res);
	B := [ f[1] : f in fac | Degree(f[1],3) eq 1 ];
    end if;
    require #B ge 1 :
	"Argument 1 does not have a rational expression in argument 2.";
    rat := B[1];
    num := Evaluate(rat,[ P.1, P.2, 0 ]);
    den := (num-rat) div P.3;
    if Type(RelationFunctionField) eq FldFunRat then
	R := RelationFunctionField;
    else
	R := FunctionField(BaseRing(Q) : Global);
    end if;
    return Evaluate(num,[0,R.1,0])/Evaluate(den,[0,R.1,0]);
end intrinsic;
