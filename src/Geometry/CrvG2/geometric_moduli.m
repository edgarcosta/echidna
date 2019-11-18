//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare attributes Sch:
    ModuliSpaceType,
    ThetaNullType,
    ProjectionMorphisms; // for correspondence moduli spaces

//////////////////////////////////////////////////////////////////////////////
// Theta Null Moduli Spaces                                                 //
//////////////////////////////////////////////////////////////////////////////

intrinsic ThetaNullSpace(
    R::Rng,g::RngIntElt,N::RngIntElt,r::RngIntElt) -> Sch
    {The moduli space over R of theta null values for abelian varieties
    of dimension g and type (Z/NZ)^r; the prime 2 must be invertible in
    the base ring R.}
    require IsInvertible(R!2) :
	"The prime 2 must be invertible in argument 1.";
    require g eq 2 : "Argument 2 must be 2.";
    require [N,r] in {[2,2],[2,4],[4,2],[4,4]} :
	"Arguments 3 and 4 must be among the pairs {(2,2),(2,4),(4,2)}.";
    case [N,r]:
    when [2,2]:
	PP<t01,t02,t03,t04> := ProjectiveSpace(R,3);
	MM := Scheme(PP,[Parent(t01)|]);
    when [4,2]:
	/*
        The Riemann relations defining the theta null space of type (Z/4Z)^2
        are determined by the compatibility maps of the quotient to the
        theta null space of type (Z/2Z)^2.
	*/
	PP<a00,a02,a20,a22,a01,a21,a10,a12,a13,a11> := ProjectiveSpace(R,9);
	eqns := [ ];
	M4toM2 := [
	    [
	    a00^2 + a02^2 + a20^2 + a22^2, // b00*b00
	    2*(a01^2 + a21^2), // b00*b01
	    2*(a12^2 + a10^2), // b00*b10
	    2*(a11^2 + a13^2) // b00*b11
	    ],
	    [
	    2*(a01^2 + a21^2), // b00*b01
	    2*(a00*a02 + a20*a22), // b01*b01
	    4*a11*a13, // b01*b10
	    4*a10*a12 // b01*b11
	    ],
	    [
	    2*(a12^2 + a10^2), // b00*b10
	    4*a11*a13, // b01*b10
	    2*(a00*a20 + a02*a22), // b10*b10
	    4*a01*a21 // b10*b11
	    ],
	    [
	    2*(a11^2 + a13^2), // b00*b11
	    4*a10*a12, // b01*b11
	    4*a01*a21, // b10*b11
	    2*(a00*a22 + a02*a20) // b11*b11
	    ]
	    ];
	RiemannEQs := [ ];
	for i in [1..3] do
	    for j in [i+1..4] do
		RiemannEQs cat:= [
		    M4toM2[i][m]*M4toM2[j][n] -
		    M4toM2[i][n]*M4toM2[j][m] :
		    n, m in [1..4] | n lt m ];
	    end for;
	end for;
	MM := Scheme(PP,RiemannEQs);
    when [2,4]:
	/*
        Here we have the labelling of theta constants by characteristics:
            t01 : [(0,0),(0,0)]; t02 : [(0,0),(1,1)]
            t03 : [(0,0),(1,0)]; t04 : [(0,0),(0,1)]
        then
            t05 : [(1,0),(0,0)]; t06 : [(1,0),(0,1)]
            t07 : [(0,1),(0,0)]; t08 : [(1,1),(0,0)]
            t09 : [(0,1),(1,0)]; t10 : [(1,1),(1,1)]
        The remaining theta characteristics t11,...,t16 satisfy linear
        relations with the first 10 (by symmetric condition) and will
        not be represented by the projective coordinate functions.

        Note that the coordinate functions are the squares of the
        associated theta null values.

        See Gaudry "Fast genus 2 arithmetic based on Theta functions"
        for the definitions and conventions followed here.          
        */
	PP<t01,t02,t03,t04,t05,t06,t07,t08,t09,t10> := ProjectiveSpace(R,9);
	FrobeniusEQs := [
	    t01^2-t02^2-t03^2+t04^2-t05^2-t06^2,
	    t01*t04-t02*t03-t05*t06,
	    t03^2-t04^2+t05^2-t07^2,
	    t01*t05-t04*t06-t07*t08,
	    t01*t03-t02*t04-t07*t09,
	    t02*t05-t03*t06-t07*t10
	    ];
	MM := Scheme(PP,FrobeniusEQs);
    when [4,4]:
	/*
        These are exactly as above for the space of type (2,4), except
        that the theta null values are not the square values.

        See Gaudry "Fast genus 2 arithmetic based on Theta functions"
        for the definitions and conventions followed here.          
        */
	PP<t01,t02,t03,t04,t05,t06,t07,t08,t09,t10> := ProjectiveSpace(R,9);
	FrobeniusEQs := [
	    t01^4-t02^4-t03^4+t04^4-t05^4-t06^4,
	    t01^2*t04^2-t02^2*t03^2-t05^2*t06^2,
	    t03^4-t04^4+t05^4-t07^4,
	    t01^2*t05^2-t04^2*t06^2-t07^2*t08^2,
	    t01^2*t03^2-t02^2*t04^2-t07^2*t09^2,
	    t02^2*t05^2-t03^2*t06^2-t07^2*t10^2
	    ];
	MM := Scheme(PP,FrobeniusEQs);
    end case;
    MM`ModuliSpaceType := "ThetaNull";
    MM`ThetaNullType := <[N,r],1>;
    return MM;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Points over a modular correspondence X -> Mg x Mg -> Mg                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic ThetaNullCorrespondencePoints(P::Pt,p::RngIntElt) -> SetIndx
    {}
    return {@ @};
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Equations representing a modular correspondence X -> Mg x Mg.            //
//////////////////////////////////////////////////////////////////////////////

intrinsic ThetaNullCorrespondenceSpace(MM::Sch,p::RngIntElt :
    Model := "CKL") -> Sch
    {The (p,..,p)-correspondence moduli space of the moduli space over
    the theta null space M.}
    require assigned MM`ModuliSpaceType and MM`ModuliSpaceType eq "ThetaNull" : 
	"Argument must be a theta null moduli space.";
    require assigned MM`ThetaNullType and MM`ThetaNullType[2] eq 1 : 
	"Argument must be a theta null base moduli space.";
    require p in {2,3} : "Arguments 5 must be in {2,3}.";
    N, r := Explode(MM`ThetaNullType[1]); // [N,r]
    require [N,r] in {[2,2],[2,4],[4,2]} :
	"Arguments 3 and 4 must be among the pairs {(2,2),(2,4),(4,2)}.";
    case <[N,r],p>:
    when <[2,2],2>:
	/*
        We use (b00:b01:b10:b11) and (a00:a02:a20:a22) as defined in
        Carls, Kohel, and Lubicz.

        Gaudry defines an alternative set of four "fundamental theta
        constants" which are the permutation
               (t01:t02:t03:t04) = (b00:b11:b10:b01)
        relative to our four values here. The codomain correspondence
        is then of the form (t01:t08:t07:t05), evaluated at 2.Omega,
        in terms of the theta constants of type (Z/2Z)^4.

        Van Wamelen distiguishes a completely different set of six of
        the ten theta constants.
        */
	if Model eq "Gaudry" then
	    PP := AmbientSpace(MM);
	    PPxPP, prjs := DirectProduct(PP,PP);
	    PPxPP<b01,b02,b03,b04,a01,a02,a03,a04> := PPxPP;
	    CrrEQs1 := [
		b01^2+b02^2+b03^2+b04^2,
		b01^2+b02^2-b03^2-b04^2,
		b01^2-b02^2+b03^2-b04^2,
		b01^2-b02^2-b03^2+b04^2
		];
	    CrrEQs2 := [a01^2,a02^2,a03^2,a04^2];
	    XX := Scheme(PPxPP,[
		CrrEQs1[i]*CrrEQs2[j]-
		CrrEQs1[j]*CrrEQs2[i] : i, j in [1..4] | i lt j ]);
	    pi_1, pi_2 := Explode(prjs);
	    XX`ProjectionMorphisms := [
		<MM,DefiningPolynomials(pi_1)>,
		<MM,DefiningPolynomials(pi_2)> ];
	elif Model eq "CKL" then
	    PP := AmbientSpace(MM);
	    PPxPP, prjs := DirectProduct(PP,PP);
	    PPxPP`ProjectionMorphisms := [
		<PP,DefiningPolynomials(prjs[1])>, 
		<PP,DefiningPolynomials(prjs[2])> ];
	    PPxPP<b00,b01,b10,b11,a00,a02,a20,a22> := PPxPP;
	    CrrEQs1 := [
		b00^2+b01^2+b10^2+b11^2,
		b00^2-b01^2+b10^2+b11^2,
		b00^2+b01^2-b10^2+b11^2,
		b00^2-b01^2-b10^2+b11^2
		];
	    CrrEQs2 := [
		(a00+a02+a20+a22)^2, 
		(a00-a02+a20+a22)^2, 
		(a00+a02-a20+a22)^2, 
		(a00-a02-a20+a22)^2 
		];
	    XX := Scheme(PPxPP,[
		CrrEQs1[i]*CrrEQs2[j]-
		CrrEQs1[j]*CrrEQs2[i] : i, j in [1..4] | i lt j ]);
	    pi_1, pi_2 := Explode(prjs);
	    XX`ProjectionMorphisms := [
		<MM,DefiningPolynomials(pi_1)>,
		<MM,DefiningPolynomials(pi_2)> ];
	end if;
    when <[2,2],3>:
	/*
        DRK: Here we don't know how to reduce the set of polynomials
        determining the (3,3)-correspondence from those on theta type
        (Z/4Z)^2 to type (Z/2Z)^2.
        */
	error if true, "Not implemented error.";
    when <[4,2],2>:
	/*
        DRK: Here if (b_ij) -> (a_2i2j) = (b_ij') gives a (2,2)-isogeny 
        correspondence, then we can construction (a_ij') from (b_ij'),
        to determine the correspondence.
        */
	error if true, "Not implemented error.";
    when <[4,2],3>:
	/*
        The Riemann relations defining the theta null space of type (Z/4Z)^2
        are determined by the compatibility maps of the quotient to the theta
        null space of type (Z/2Z)^2.
	*/
	PP := AmbientSpace(MM);
	PPxPP<
	    x00,x02,x20,x22,x01,x21,x10,x12,x13,x11,
	    y00,y02,y20,y22,y01,y21,y10,y12,y13,y11>,
	    prjs := DirectProduct(PP,PP);
	xx := [x00,x02,x20,x22,x01,x21,x10,x12,x13,x11];
	yy := [y00,y02,y20,y22,y01,y21,y10,y12,y13,y11];
	CrrEQs := 
	    [ Evaluate(f,xx) : f in DefiningPolynomials(MM) ] cat 
	    [ Evaluate(f,yy) : f in DefiningPolynomials(MM) ] cat [
	    x00*y02 + x02*y00 + x20*y22 + x22*y20 - 2*(x01*y01 + x21*y21),
	    x00*y20 + x02*y22 + x20*y00 + x22*y02 - 2*(x10*y10 + x12*y12),
	    x00*y22 + x02*y20 + x20*y02 + x22*y00 - 2*(x11*y11 + x13*y13),
	    x01*y21 - x10*y12 - x12*y10 + x21*y01,
	    x01*y21 - x11*y13 - x13*y11 + x21*y01
	    ];
	XX := Scheme(PPxPP,CrrEQs);
	pi_1, pi_2 := Explode(prjs);
	XX`ProjectionMorphisms := [
	    <MM,DefiningPolynomials(pi)> : pi in prjs ];
    end case;
    XX`ModuliSpaceType := "ThetaNullCorrespondence";
    XX`ThetaNullType := <[N,r],p>;
    return XX;
end intrinsic;

intrinsic ThetaNullCorrespondenceSpace(
    R::Rng,g::RngIntElt,N::RngIntElt,r::RngIntElt,p::RngIntElt :
    Model := "CKL") -> Sch
    {The (p,..,p)-correspondence moduli space of the moduli space over R
    of theta null values for abelian varieties of dimension g and type
    (Z/NZ)^r; the prime 2 must be invertible in the base ring R.}
    require IsInvertible(R!2) :
	"The prime 2 must be invertible in argument 1.";
    require g eq 2 : "Argument 2 must be 2.";
    require [N,r] in {[2,2],[2,4],[4,2]} :
	"Arguments 3 and 4 must be among the pairs {(2,2),(2,4),(4,2)}.";
    require p in {2,3} : "Arguments 5 must be in {2,3}.";
    return ThetaNullCorrespondenceSpace(ThetaNullSpace(R,g,N,r),p);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic ProjectionMorphism(X::Sch,i::RngIntElt) -> MapSch
    {}
    require i in [1,2] : "Argument 2 must in be {1,2}.";
    if assigned X`ProjectionMorphisms then
	return X`ProjectionMorphisms[i];
    end if;
    PP := AmbientSpace(X);
    bool := assigned PP`ProjectionMorphisms;
    if not bool then
	if Type(PP) eq PrjProd then
	    R := BaseRing(PP);
	    gr := Gradings(PP); assert #gr eq 2;
	    I1 := [ i : i in [1..#gr[1]] | gr[1][i] ne 0 ]; 
	    I2 := [ i : i in [1..#gr[2]] | gr[2][i] ne 0 ]; 
	    PP_1 := ProjectiveSpace(R,gr[1][I1]); 
	    PP_2 := ProjectiveSpace(R,gr[2][I2]);
	    PP`ProjectionMorphisms := [ 
		<PP_1,[ PP.i : i in I1 ]>,
		<PP_2,[ PP.i : i in I2 ]> ];
	else
	    require false : "Argument 1 has no projections defined.";
	end if;
    end if;
    pi := PP`ProjectionMorphisms[i];
    return map< X->pi[1] | pi[2] : Check := false >;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Theta Null Moduli Spaces To Rosenhain Invariants of Curves               //
//////////////////////////////////////////////////////////////////////////////

intrinsic RosenhainModuliSpace(R::Rng) -> Sch
    {}
    PP<e0,e1,e2,e3> := ProjectiveSpace(R,3);
    M2 := Scheme(PP,[Parent(e0)|]);
    M2`ModuliSpaceType := "Rosenhain";
    return M2;
end intrinsic;

intrinsic ThetaNullSpaceToRosenhain(M1::Sch,M2::Sch) -> MapSch
    {}
    require assigned M1`ModuliSpaceType and assigned M2`ModuliSpaceType : 
	"Arguments must be a moduli spaces.";
    require M1`ModuliSpaceType in {"ThetaNull","ThetaNullCorrespondence"} : 
	"Argument 1 must be a Theta null moduli space.";
    require M2`ModuliSpaceType eq "Rosenhain" : 
	"Argument 2 must be a Rosenhain moduli space.";
    if M1`ThetaNullType eq <[4,2],1> then
	PP := AmbientSpace(M1);
	aa := [ PP.i^2 : i in [1..10] ];
	a00,a02,a20,a22,a01,a21,a10,a12,a13,a11 := Explode(aa);
	// ???
	t01 := a00; t02 := a22;	t03 := a20; t04 := a02;
	t05 := a01; t06 := a21;	t07 := a10; t09 := a12;	t08 := a11; t10 := a13;
	// ???
	print "THIS IS WRONG";
	ee := [ t02*t04*t10, t01*t03*t10, t02*t03*t08, t01*t04*t08 ];
    elif M1`ThetaNullType eq <[2,4],1> then
	PP := AmbientSpace(M1);
	tt := [ PP.i : i in [1..10] ];
	t01,t02,t03,t04,t05,t06,t07,t08,t09,t10 := Explode(tt);
	ee := [ t02*t04*t10, t01*t03*t10, t02*t03*t08, t01*t04*t08 ];
    elif M1`ThetaNullType eq <[4,4],1> then
	PP := AmbientSpace(M1);
	tt := [ PP.i^2 : i in [1..10] ];
	t01,t02,t03,t04,t05,t06,t07,t08,t09,t10 := Explode(tt);
	ee := [ t02*t04*t10, t01*t03*t10, t02*t03*t08, t01*t04*t08 ];
    end if;
    return map< M1->M2 | ee : Check := false >;
end intrinsic;
