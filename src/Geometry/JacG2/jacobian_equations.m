//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Scheme Theoretic Equations for Genus 2 Jacobians                        //
//  Copyright (C) 2004 Geordie Williamson and                               //
//                     David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare attributes JacHyp:
    GeometricObject, // This is the realisation of the Jacobian as a variety.
    aInject; 	     // The polynomials defining the injection.

declare verbose JacG2Relations, 2;

//////////////////////////////////////////////////////////////////////////////

/*
The main reference for this work is:

E. V. Flynn, The Jacobian and formal group of a curve of genus 2 over an arbitrary ground field,
  Math. Proc. Camb. Phil. Soc. 107(1990), 425-441.

This work is intended to supplement Flynn's paper and we recommend that the interested reader
has at least a precursory knowledge of Flynn before trying to understand our implementation!

Computationally, there are four main tasks needed in order to obtain the formal group:

  1. Obtain a set of defining relations for the Jacobian. The algorithms that achieve a set of
     relations are in jacobian_equations.m (at bottom) and a hard-coded set or relations is 
     returned by JacobianG2Relations.

and in ../GrpFrml, one finds the first steps toward:

  2. Calculate the local power series expansions for the embedding in this Jacobian. This is
     achieved by the intrinsic JacobianG2FormalGroupEmbedding.

  3. a) Given two points s = (1 : s1 : s2 : ... ) and t = (1 : t1 : t2 : ...) calculate,
     projectively, the last three coordinates of s + t. This is achieved by the 
     inrinsic [???]

     b) Complete the last three coordinates of s + t to a point on the Jacobian, achieved
     by the intrinsic [???]. 

    Together this should determine an intrinsic JacobianG2FormalGroupLaw [incomplete].

Comparatively, (2) and (3) are reasonably straightforward, whilst (1) and (4) are more
difficult. An algorithm that achieves (1) is given a reasonably explicit description
in Flynn. The main purpose of this document is to explain an algorithm that achieves (4).
*/

intrinsic JacobianG2Relations(J::JacHyp) -> SeqEnum
    {}
    return JacobianG2Relations(Curve(J));
end intrinsic;

intrinsic JacobianG2Relations(C::CrvHyp) -> SeqEnum
    {}
    f, h := HyperellipticPolynomials(C);
    require h eq 0 :
	"Argument must be a simplified model (see SimplifiedModel).";
    require Genus(C) eq 2 : "Argument must have genus 2.";
    require Degree(f) eq 6 :
	"Argument must be an even degree model (not implemented error).";
    fs := Eltseq(f);
    return JacobianG2Relations(fs);
end intrinsic;

intrinsic JacobianG2Relations(K::Fld) -> SeqEnum
    {}
    F<f0,f1,f2,f3,f4,f5,f6> := FunctionField(K,7 : Global); 
    return JacobianG2Relations([f0,f1,f2,f3,f4,f5,f6]);
end intrinsic;

intrinsic JacobianG2Relations(ff::[RngElt]) -> SeqEnum
    {}
    require #ff eq 7 : "Argument must have length 7.";
    F := Universe(ff);
    f0,f1,f2,f3,f4,f5,f6 := Explode(ff);
    K<x1,x2,y1,y2> := FunctionField(F,4 : Global);
    t12 := x1 + x2; 
    n12 := x1 * x2; 
    m00 := (y1-y2)/(x1-x2);
    m01 := (x2*y1-x1*y2)/(x1-x2);
    m02 := (x2^2*y1-x1^2*y2)/(x1-x2);
    m03 := (x2^3*y1-x1^3*y2)/(x1-x2);
    a := [ K | 0 : i in [0..15] ];
    a[15+1] := 1;
    a[14+1] := t12;
    a[13+1] := n12;
    a[12+1] := t12^2 - 2*n12;
    a[11+1] := t12 * n12;
    a[10+1] := n12^2;
    a[09+1] := m00;
    a[08+1] := m01;
    a[07+1] := m02;
    a[06+1] := m03;
    //
    F0 := 2*f0 + f1*(x1+x2) + 2*f2*(x1*x2) + f3*(x1*x2)*(x1+x2)
	+ 2*f4*(x1*x2)^2 + f5*(x1*x2)^2*(x1+x2) + 2*f6*(x1*x2)^3;
    //
    a[05+1] := (Evaluate(F0,[x1,x2,y1,y2])-2*y1*y2)/(x1-x2)^2;
    //
    F1 := f0*(x1+x2) + 2*f1*(x1*x2) + f2*(x1*x2)*(x1+x2) + 2*f3*(x1*x2)^2
	+ f4*(x1*x2)^2*(x1+x2) + 2*f5*(x1*x2)^3 + f6*(x1*x2)^3*(x1+x2);
    a[04+1] := (Evaluate(F1,[x1,x2,y1,y2])-(x1+x2)*y1*y2)/(x1-x2)^2;
    //
    a[03+1] := a[05+1]*(x1*x2);
    //
    G0 := 4*f0 + f1*(x1+3*x2) + 2*f2*(x1+x2)*x2 + f3*(3*x1+x2)*x2^2
	+ 4*f4*(x1*x2)*x2^2 + f5*(x1*x2)*(x1+3*x2)*x2^2
	+ 2*f6*(x1*x2)*(x1+x2)*x2^3;
    a[02+1] := (Evaluate(G0,[x1,x2,y1,y2])*y1-Evaluate(G0,[x2,x1,y2,y1])*y2)/(x1-x2)^3;
    //
    G1 := 2*f0*(x1+x2) + f1*(3*x1+x2)*x2 + 4*f2*(x1*x2)*x2
	+ f3*(x1*x2)*(x1+3*x2)*x2 + 2*f4*(x1*x2)*(x1+x2)*x2^2
	+ f5*(x1*x2)*(3*x1+x2)*x2^3 + 4*f6*(x1*x2)^2*x2^3;
    a[01+1] := (Evaluate(G1,[x1,x2,y1,y2])*y1-Evaluate(G1,[x2,x1,y2,y1])*y2)/(x1-x2)^3;
    //
    a[00+1] := a[05+1]^2;
    //
    P<X00,X01,X02,X03,X04,X05,X06,X07,
      X08,X09,X10,X11,X12,X13,X14,X15> := PolynomialRing(F,16 : Global);
    rels := [
	X00*X03 - X01^2 + f4*X03^2 + (-4*f2*f6 + f3*f5)*X03*X10 -
	8*f1*f6*X04*X10 - 8*f0*f6*X04*X11 - 4*f0*f5*X04*X13 + f0*X05^2 -
	f1*f5*X05*X10 + (-4*f1*f5*f6 - 4*f2*f4*f6 + f2*f5^2 + f3^2*f6)*X10^2
	+ (-4*f0*f5*f6 - 4*f1*f4*f6 + f1*f5^2)*X10*X11 + (-2*f0*f5^2 -
	6*f1*f3*f6)*X10*X13 + (-4*f0*f2*f6 - 2*f0*f3*f5 - 3*f1^2*f6)*X10*X15
	+ (-4*f0*f4*f6 + f0*f5^2)*X11^2 - 8*f0*f3*f6*X11*X13 -
	4*f0*f1*f6*X11*X15 - 2*f0*f1*f5*X13*X15,

	X00*X04 - X01*X02 - f3*f6*X03*X10 + (-9*f0*f5 - f1*f4)*X03*X15 -
	4*f2*f6*X04*X10 + (-20*f0*f6 - 3*f1*f5)*X04*X13 +
	(-7*f1*f6 - f2*f5)*X05*X10 - 2*f0*f4*X05*X14 - f0*f3*X05*X15 -
	4*f1*f6*X06*X08 - 4*f0*f6*X06*X09 + 2*f1*f6*X07^2 +
	4*f0*f6*X07*X08 - 4*f0*f5*X07*X09 + 4*f0*f5*X08^2 +
	(-2*f1*f6^2 - 2*f2*f5*f6)*X10^2 +
	(-4*f0*f6^2 - 2*f1*f5*f6)*X10*X11 - 2*f0*f5*f6*X10*X12 +
	(-18*f0*f5*f6 -	6*f1*f4*f6 - f1*f5^2 - 2*f2*f3*f6)*X10*X13 +
	(-8*f0*f4*f6 - f0*f5^2 - 3*f1*f3*f6)*X10*X14 -
	4*f0*f3*f6*X12*X13 +
	(-20*f0*f3*f6 - 4*f0*f4*f5 - 4*f1*f2*f6 - 2*f1*f3*f5)*X13^2 +
	(-8*f0*f2*f6 - 3*f0*f3*f5 + f1^2*f6)*X13*X14 +
	(-14*f0*f1*f6 - 6*f0*f2*f5 - f1^2*f5)*X13*X15 +
	(-4*f0^2*f6 - 2*f0*f1*f5)*X14*X15 - 4*f0^2*f5*X15^2,

	X00*X05 - X02^2 + f6*X03^2 - f1*f5*X03*X15 - 8*f0*f6*X04*X14 +
	f2*X05^2 - 4*f0*f5*X05*X14 + (-4*f0*f4 + f1*f3)*X05*X15 -
	4*f1*f6*X07*X08 + 4*f1*f6^2*X10*X11 + 2*f1*f5*f6*X10*X13 -
	4*f0*f5*f6*X10*X14 + (-4*f0*f4*f6 + f0*f5^2 -
	2*f1*f3*f6)*X10*X15 - 8*f0*f3*f6*X11*X15 + (-4*f0*f2*f6 +
	f1^2*f6)*X12*X15 + (-8*f0*f2*f6 - 2*f0*f3*f5 +
	4*f1^2*f6)*X13*X15 + (-4*f0*f2*f5 + f1^2*f5)*X14*X15 +
	(-4*f0*f2*f4 + f0*f3^2 + f1^2*f4)*X15^2,
	
	X00*X06 - X01*X03 - f3*X04*X06 - 2*f2*X05*X06 - 3*f1*X05*X07 - 
	4*f0*X05*X08 - 4*f2*f6*X06*X10 - 4*f1*f6*X06*X11 - 
        4*f0*f6*X06*X12 + (-2*f2*f5 + f3*f4)*X07*X10 + (-4*f0*f6 - 
        4*f1*f5)*X07*X11 - 4*f0*f5*X07*X12 + (4*f0*f6 + 2*f1*f5 + 
        f3^2)*X08*X10 + (-4*f0*f5 - 4*f1*f4 + 3*f2*f3)*X08*X11 - 
        4*f0*f4*X08*X12 + (-8*f0*f4 - 2*f1*f3 + 4*f2^2)*X08*X13 + 
        (-4*f0*f3 + 2*f1*f2)*X08*X14 + (-4*f0*f2 + 2*f1^2)*X08*X15 + 
        (6*f0*f5 + 4*f1*f4 - 2*f2*f3)*X09*X10 + (4*f0*f4 + 
        f1*f3)*X09*X11 + f0*f3*X09*X12 + (3*f0*f3 + 2*f1*f2)*X09*X13 + 
        4*f0*f2*X09*X14 + 2*f0*f1*X09*X15,
	X01*X10 - X03*X06 + f3*X07*X10 + 2*f2*X08*X10 + f1*X08*X11 + 
        f1*X09*X10 + 2*f0*X09*X11,

	X01*X11 - 2*X04*X06 - f5*X06*X10 + f3*X08*X10 + 2*f2*X08*X11 + 
        f1*X08*X13 + 2*f1*X09*X11 + 2*f0*X09*X12 + 4*f0*X09*X13,
	X01*X12 - 2*X05*X06 - 4*f6*X06*X10 - f5*X06*X11 - 2*f5*X07*X10 - 
        2*f4*X07*X11 - f3*X08*X11 + f1*X08*X14 + 2*f0*X09*X14,

	X01*X13 - X05*X06 + f3*X08*X11 + 2*f2*X08*X13 + f1*X08*X14 - 
        f3*X09*X10 + f1*X09*X13 + 2*f0*X09*X14,

	X01*X14 - 2*X05*X07 - f5*X07*X11 + f5*X08*X10 - 2*f4*X08*X11 - 
        f3*X08*X13 + f1*X08*X15 + 2*f4*X09*X10 + 2*f0*X09*X15,

	X01*X15 - X05*X08 + 2*f6*X07*X11 - 2*f6*X08*X10 + f5*X08*X11 - 
        f5*X09*X10,

	X02*X10 - X04*X06 + f4*X07*X10 + f3*X08*X10 + f2*X08*X11 + 
        f1*X08*X13 + f1*X09*X11 + f0*X09*X12 + 3*f0*X09*X13,

	X02*X11 - 2*X05*X06 - 2*f6*X06*X10 - f5*X07*X10 + f3*X08*X11 + 
        2*f2*X08*X13 + 2*f1*X08*X14 - f3*X09*X10 + f1*X09*X13 + 
        4*f0*X09*X14,

	X02*X12 - 2*X05*X07 - 2*f6*X06*X11 - 3*f5*X07*X11 + 2*f5*X08*X10 - 
        4*f4*X08*X11 - f3*X08*X12 - 4*f3*X08*X13 - 2*f2*X08*X14 + 
        4*f4*X09*X10 + f3*X09*X11 - f1*X09*X14,

	X02*X13 - X05*X07 + f1*X08*X15 + 2*f0*X09*X15,

	X02*X14 - 2*X05*X08 + 2*f6*X07*X11 - 2*f6*X08*X10 + f5*X08*X11 - 
        f3*X08*X14 - 2*f2*X08*X15 - f5*X09*X10 + f3*X09*X13 - 
        f1*X09*X15,

	X03*X07 - X04*X06 + f4*X07*X10 + f3*X08*X10 + f2*X08*X11 + 
        f1*X09*X11 + f0*X09*X12 + f0*X09*X13,

	X03*X08 - X05*X06 - 2*f6*X06*X10 - f5*X07*X10 + f3*X08*X11 + 
        2*f2*X08*X13 + f1*X08*X14 - f3*X09*X10 + f1*X09*X13 + 
        2*f0*X09*X14,

	X03*X09 - X05*X07 - 2*f6*X06*X11 - 2*f5*X07*X11 + f5*X08*X10 - 
        2*f4*X08*X11 - f3*X08*X13 + f1*X08*X15 + 2*f4*X09*X10 + 
        2*f0*X09*X15,

	X04*X07 - X05*X06 - f6*X06*X10 + f3*X08*X11 + f2*X08*X13 + 
        f1*X08*X14 - f3*X09*X10 + f0*X09*X14,

	X04*X08 - X05*X07 - f6*X06*X11 - f5*X07*X11 + f5*X08*X10 - 
        f4*X08*X11 + f1*X08*X15 + f4*X09*X10 + f0*X09*X15,

	X04*X09 - X05*X08 - f6*X06*X12 - f6*X07*X11 - f5*X07*X12 + 
        f6*X08*X10 - f5*X08*X11 - f4*X08*X12 - 2*f4*X08*X13 - f3*X08*X14
        - f2*X08*X15 + 2*f5*X09*X10 + f4*X09*X11 + f3*X09*X13,

	X06*X13 - X07*X11 + X08*X10,

	X06*X14 - X07*X12 - X08*X11 + 2*X09*X10,

	X06*X15 - X08*X12 - X08*X13 + X09*X11,

	X07*X13 - X08*X11 + X09*X10,

	X07*X14 - X08*X12 - 2*X08*X13 + X09*X11,

	X07*X15 - X08*X14 + X09*X13,

	X00*X07 - X02*X03 - f1*X05*X08 - 2*f0*X05*X09,

	X01*X04 - X02*X03 - f4*X04*X06 - f0*X05*X09 - f3*f6*X06*X10 + 
        (-f3*f5 + f4^2)*X07*X10 - f1*f6*X07*X11 + (f1*f6 - f2*f5 + 
        f3*f4)*X08*X10 + (-f1*f5 + f2*f4)*X08*X11 + (-f0*f5 + 
        f1*f4)*X09*X11 + f0*f4*X09*X12 + f0*f4*X09*X13,

	X02*X15 - X05*X09 + 2*f6*X07*X12 + 2*f6*X08*X11 + 2*f5*X08*X12 + 
        3*f5*X08*X13 + 2*f4*X08*X14 + f3*X08*X15 - 4*f6*X09*X10 - 
        2*f5*X09*X11 - 2*f4*X09*X13,

	X00*X08 - X02*X04 - f6*X03*X06 - f5*X04*X06 + f2*X05*X08 + 
        f4*f5*X07*X10 + f1*f6*X07*X12 + f3*f5*X08*X10 + (f1*f6 + 
        f2*f5)*X08*X11 + f1*f5*X08*X12 + 2*f1*f5*X08*X13 + f1*f4*X08*X14
        + f1*f3*X08*X15 - 2*f1*f6*X09*X10 + f0*f5*X09*X12 + (2*f0*f5 - 
        f1*f4)*X09*X13 + f0*f3*X09*X15,

	X01*X05 - X02*X04 + f6*X03*X06 + f2*X05*X08 + f1*f6*X07*X12 + 
        f1*f6*X08*X11 + f1*f5*X08*X12 + 2*f1*f5*X08*X13 + f1*f4*X08*X14 
        + f1*f3*X08*X15 - 2*f1*f6*X09*X10 - f1*f5*X09*X11 + (f0*f5 - 
        f1*f4)*X09*X13 + f0*f3*X09*X15,

	X00*X09 - X02*X05 - 4*f6*X04*X06 - 3*f5*X05*X06 - 2*f4*X05*X07 - 
        f3*X05*X08 - 4*f5*f6*X06*X10 - f5^2*X07*X10 - 2*f3*f6*X07*X11 + 
        2*f3*f6*X08*X10 + f3*f5*X08*X11 - 2*f1*f6*X08*X12 + (-2*f1*f6 + 
        2*f2*f5)*X08*X13 + f1*f5*X08*X14 - f3*f5*X09*X10 + 
        2*f1*f6*X09*X11 + f1*f5*X09*X13 + 2*f0*f5*X09*X14,

	X00*X10 - X03^2,

	X01*X06 - X03^2 - f4*X06^2 - f3*X06*X07 - 2*f2*X07^2 - 3*f1*X07*X08 
        - 2*f0*X07*X09 - 3*f0*X08^2 + (2*f2*f6 - f3*f5 + f4^2)*X10^2 + 
        (3*f1*f6 - f2*f5 + f3*f4)*X10*X11 + (-2*f0*f6 + 2*f1*f5 - 
        2*f2*f4 + f3^2)*X10*X13 + (5*f0*f6 - f1*f5 + f2*f4)*X11^2 + 
        (-f0*f5 + f1*f4)*X11*X12 + (3*f0*f5 - f1*f4 + f2*f3)*X11*X13 + 
        f0*f4*X12^2 + f1*f3*X12*X13 + f0*f3*X12*X14 + (-f1*f3 + 
        2*f2^2)*X13^2 + (-2*f0*f3 + 2*f1*f2)*X13*X14 + (-4*f0*f2 + 
        2*f1^2)*X13*X15 + 2*f0*f2*X14^2 + 2*f0*f1*X14*X15 + 
        3*f0^2*X15^2,

	X03*X10 - X06^2 + f4*X10^2 + f3*X10*X11 + f2*X11^2 + f1*X11*X12 + 
        f1*X11*X13 + f0*X12^2 + 2*f0*X12*X13 + f0*X13^2,

	X03*X11 - 2*X06*X07 - f5*X10^2 + f3*X10*X13 + 2*f2*X11*X13 + 
        2*f1*X12*X13 + 2*f0*X12*X14 + 3*f1*X13^2 + 2*f0*X13*X14,

	X03*X12 - 2*X06*X08 - f5*X10*X11 - 2*f4*X10*X13 - f3*X11*X13 + 
        f1*X13*X14 - 2*f0*X13*X15 + 2*f0*X14^2,

	X03*X13 - X07^2 + f6*X10^2 + f2*X13^2 + f1*X13*X14 + f0*X14^2,

	X03*X14 - 2*X07*X08 + 2*f6*X10*X11 + f5*X10*X13 - f3*X13^2 + 
        f1*X13*X15 + 2*f0*X14*X15,

	X03*X15 - X08^2 + f6*X11^2 + f5*X11*X13 + f4*X13^2 + f0*X15^2,

	X04*X10 - X06*X07 + f3*X10*X13 + f2*X11*X13 + f1*X12*X13 + 
        f0*X12*X14 + 2*f1*X13^2 + f0*X13*X14,

	X04*X11 - X06*X08 - X07^2 + f6*X10^2 - f4*X10*X13 + f2*X13^2 + 
        2*f1*X13*X14 - f0*X13*X15 + 2*f0*X14^2,

	X04*X12 - X06*X09 - X07*X08 + f6*X10*X11 - f4*X11*X13 - 2*f3*X13^2 -
        f2*X13*X14 + f0*X14*X15,

	X04*X13 - X07*X08 + f6*X10*X11 + f5*X10*X13 + f1*X13*X15 + 
        f0*X14*X15,

	X04*X14 - X07*X09 - X08^2 - f6*X10*X13 + 2*f6*X11^2 + 2*f5*X11*X13 +
        f4*X13^2 - f2*X13*X15 + f0*X15^2,

	X05*X10 - X07^2 + f6*X10^2 + f2*X13^2 + f1*X13*X14 + f0*X14^2,

	X05*X11 - 2*X07*X08 + 2*f6*X10*X11 + f5*X10*X13 - f3*X13^2 + 
        f1*X13*X15 + 2*f0*X14*X15,

	X05*X12 - 2*X07*X09 - 2*f6*X10*X13 + 2*f6*X11^2 + f5*X11*X13 - 
        f3*X13*X14 - 2*f2*X13*X15 - f1*X14*X15,

	X05*X13 - X08^2 + f6*X11^2 + f5*X11*X13 + f4*X13^2 + f0*X15^2,

	X10*X12 + 2*X10*X13 - X11^2,

	X10*X14 - X11*X13,

	X10*X15 - X13^2,

	X11*X14 - X12*X13 - 2*X13^2,

	X11*X15 - X13*X14,

	X12*X15 + 2*X13*X15 - X14^2,

	X00*X11 - 2*X03*X04 - f5*X06^2 - f3*X07^2 - f1*X08^2 + (f3*f6 + 
        f4*f5)*X10^2 + f3*f5*X10*X11 + (f1*f6 + f2*f5)*X11^2 + 
        f1*f5*X11*X12 + 2*f1*f5*X11*X13 + f0*f5*X12^2 + 2*f0*f5*X12*X13 
        + (f0*f5 + f1*f4 + f2*f3)*X13^2 + f1*f3*X13*X14 + f0*f3*X14^2 + 
        f0*f1*X15^2,

	X01*X07 - X03*X04 - f1*X08^2 - 2*f0*X08*X09 + f3*f6*X10^2 + 
        2*f2*f6*X10*X11 + (-f1*f6 + f2*f5)*X10*X13 + 3*f1*f6*X11^2 + 
        4*f0*f6*X11*X12 + (4*f0*f6 + 2*f1*f5)*X11*X13 + 3*f0*f5*X12*X13 
        + (5*f0*f5 + f1*f4)*X13^2 + 2*f0*f4*X13*X14 + f0*f3*X13*X15,

	X02*X06 - X03*X04 - f3*X07^2 - 2*f2*X07*X08 - f1*X07*X09 - 
        2*f1*X08^2 - 4*f0*X08*X09 + f3*f6*X10^2 + 2*f2*f6*X10*X11 + 
        (-f1*f6 + f2*f5)*X10*X13 + 3*f1*f6*X11^2 + 4*f0*f6*X11*X12 + 
        (4*f0*f6 + 2*f1*f5)*X11*X13 + 3*f0*f5*X12*X13 + (5*f0*f5 + 
        f1*f4)*X13^2 + 2*f0*f4*X13*X14 + f0*f3*X13*X15,

	X04*X15 - X08*X09 + f6*X11*X12 + f6*X11*X13 + f5*X12*X13 + 
        2*f5*X13^2 + f4*X13*X14 + f3*X13*X15,

	X05*X14 - 2*X08*X09 + 2*f6*X11*X12 + 2*f6*X11*X13 + 2*f5*X12*X13 + 
        3*f5*X13^2 + 2*f4*X13*X14 + f3*X13*X15 - f1*X15^2,

	X00*X12 - 2*X04^2 - 2*f6*X06^2 - 4*f5*X06*X07 - 2*f4*X07^2 - 
        4*f3*X07*X08 - 2*f2*X08^2 - 4*f1*X08*X09 - 2*f0*X09^2 + (2*f4*f6
        - f5^2)*X10^2 + 4*f3*f6*X10*X11 + 4*f3*f5*X10*X13 + 
        2*f2*f6*X11^2 + 4*f1*f6*X11*X12 + (4*f1*f6 + 4*f2*f5)*X11*X13 + 
        2*f0*f6*X12^2 + (4*f0*f6 + 6*f1*f5)*X12*X13 + 4*f0*f5*X12*X14 + 
        (2*f0*f6 + 10*f1*f5 + 2*f2*f4 - f3^2)*X13^2 + (4*f0*f5 + 
        4*f1*f4)*X13*X14 + 4*f1*f3*X13*X15 + 2*f0*f4*X14^2 + 
        4*f0*f3*X14*X15 + (2*f0*f2 - f1^2)*X15^2,

	X00*X13 - X04^2 + f6*X06^2 + f4*X07^2 + f2*X08^2 + f0*X09^2 - 
        f4*f6*X10^2 + f3*f5*X10*X13 - f2*f6*X11^2 - f0*f6*X12^2 + 
        (-2*f0*f6 + f1*f5)*X12*X13 + (-f0*f6 + 2*f1*f5 - f2*f4)*X13^2 + 
        f1*f3*X13*X15 - f0*f4*X14^2 - f0*f2*X15^2,

	X01*X08 - X04^2 - f6*X06^2 - f5*X06*X07 + f2*X08^2 + f3*f6*X10*X11 +
        f3*f5*X10*X13 + f2*f6*X11^2 + 2*f1*f6*X11*X12 + (3*f1*f6 + 
        f2*f5)*X11*X13 + 2*f0*f6*X12^2 + (6*f0*f6 + 2*f1*f5)*X12*X13 + 
        2*f0*f5*X12*X14 + (4*f0*f6 + 4*f1*f5)*X13^2 + (3*f0*f5 + 
        f1*f4)*X13*X14 + f1*f3*X13*X15 + f0*f4*X14^2 + f0*f3*X14*X15,

	X02*X07 - X04^2 + f4*X07^2 - f1*X08*X09 - f0*X09^2 + f3*f6*X10*X11 +
        f3*f5*X10*X13 + f2*f6*X11^2 + 2*f1*f6*X11*X12 + (3*f1*f6 + 
        f2*f5)*X11*X13 + 2*f0*f6*X12^2 + (6*f0*f6 + 2*f1*f5)*X12*X13 + 
        2*f0*f5*X12*X14 + (4*f0*f6 + 4*f1*f5)*X13^2 + (3*f0*f5 + 
        f1*f4)*X13*X14 + f1*f3*X13*X15 + f0*f4*X14^2 + f0*f3*X14*X15,

	X03*X05 - X04^2 + f6*X06^2 + f4*X07^2 + f2*X08^2 + f0*X09^2 - 
        f4*f6*X10^2 + f3*f5*X10*X13 - f2*f6*X11^2 - f0*f6*X12^2 + 
        (-2*f0*f6 + f1*f5)*X12*X13 + (-f0*f6 + 2*f1*f5 - f2*f4)*X13^2 + 
        f1*f3*X13*X15 - f0*f4*X14^2 - f0*f2*X15^2,

	X05*X15 - X09^2 + f6*X12^2 + 2*f6*X12*X13 + f5*X12*X14 + f6*X13^2 + 
        f5*X13*X14 + f4*X14^2 + f3*X14*X15 + f2*X15^2,

	X00*X14 - 2*X04*X05 - f5*X07^2 - f3*X08^2 - f1*X09^2 + f5*f6*X10^2 +
        f3*f6*X11^2 + f3*f5*X11*X13 + f1*f6*X12^2 + 2*f1*f6*X12*X13 + 
        f1*f5*X12*X14 + (f1*f6 + f2*f5 + f3*f4)*X13^2 + 2*f1*f5*X13*X14 
        + (f0*f5 + f1*f4)*X14^2 + f1*f3*X14*X15 + (f0*f3 + f1*f2)*X15^2,

	X01*X09 - X04*X05 - 4*f6*X06*X07 - f5*X06*X08 - 2*f5*X07^2 - 
        2*f4*X07*X08 - f3*X08^2 + f3*f6*X10*X13 + 2*f2*f6*X11*X13 + 
        3*f1*f6*X12*X13 + 4*f0*f6*X12*X14 + (5*f1*f6 + f2*f5)*X13^2 + 
        (4*f0*f6 + 2*f1*f5)*X13*X14 + (-f0*f5 + f1*f4)*X13*X15 + 
        3*f0*f5*X14^2 + 2*f0*f4*X14*X15 + f0*f3*X15^2,

	X02*X08 - X04*X05 - 2*f6*X06*X07 - f5*X07^2 + f3*f6*X10*X13 + 
        2*f2*f6*X11*X13 + 3*f1*f6*X12*X13 + 4*f0*f6*X12*X14 + (5*f1*f6 +
        f2*f5)*X13^2 + (4*f0*f6 + 2*f1*f5)*X13*X14 + (-f0*f5 + 
        f1*f4)*X13*X15 + 3*f0*f5*X14^2 + 2*f0*f4*X14*X15 + f0*f3*X15^2,

	X00*X15 - X05^2,

	X02*X09 - X05^2 - 2*f6*X06*X08 - 3*f6*X07^2 - 3*f5*X07*X08 - 
        2*f4*X08^2 - f3*X08*X09 - f2*X09^2 + 3*f6^2*X10^2 + 
        2*f5*f6*X10*X11 + (-4*f4*f6 + 2*f5^2)*X10*X13 + 2*f4*f6*X11^2 + 
        f3*f6*X11*X12 + (-2*f3*f6 + 2*f4*f5)*X11*X13 + f2*f6*X12^2 + 
        f3*f5*X12*X13 + (-f1*f6 + f2*f5)*X12*X14 + (-f3*f5 + 
        2*f4^2)*X13^2 + (3*f1*f6 - f2*f5 + f3*f4)*X13*X14 + (-2*f0*f6 + 
        2*f1*f5 - 2*f2*f4 + f3^2)*X13*X15 + (5*f0*f6 - f1*f5 + 
        f2*f4)*X14^2 + (3*f0*f5 - f1*f4 + f2*f3)*X14*X15 + (2*f0*f4 - 
        f1*f3 + f2^2)*X15^2

	];
    return a, rels;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//  Code specific to solving for relations in the genus 2 Jacobian          //
//////////////////////////////////////////////////////////////////////////////

intrinsic JacobianG2MonomialWeights() -> SeqEnum
    {This function is specific to Jacobian surface construction.}
    wts1 := [ 4, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0];
    wts2 := [-4,-2,-3, 0,-1,-2, 2, 1, 0,-1, 4, 3, 2, 2, 1, 0];
    M := RSpace(Integers(),2);
    return [ M![wts1[i],wts2[i]] : i in [1..16] ],
	[ M![2,-i] : i in [0..6] ] cat [ M!0 ];
end intrinsic;

intrinsic JacobianG2MonomialsOfWeight(W::[RngIntElt] : Prune := true) -> SeqEnum
    {This function is specific to Jacobian surface construction.}
    require #W eq 2 : "Argument must be a sequence of two integers.";
    wts, cfs := JacobianG2MonomialWeights();
    w := Universe(wts)!W;
    wghts := [ [i,j,m,n] : i, j in [1..8], m, n in [1..16]
	| (cfs[i]+cfs[j]+wts[m]+wts[n]) eq w
	and i le j and m le n ];
    a, r := JacobianRelations(Rationals());
    F := Universe(a);
    K<f0,f1,f2,f3,f4,f5,f6> := BaseRing(F);
    ff := [f0,f1,f2,f3,f4,f5,f6,1];
    P := Universe(r);
    if not Prune then
	return
	    [ ff[w[1]]*ff[w[2]]*a[w[3]]*a[w[4]] : w in wghts ],
	    [ ff[w[1]]*ff[w[2]]*P.w[3]*P.w[4] : w in wghts ];
    end if;
    ainvs := [ ];
    terms := [ ];
    mons := {@ @};
    for w in wghts do
	x, y, i, j := Explode(w);
	m := P.i*P.j;
	if m notin mons then
	    Append(~ainvs,ff[x]*ff[y]*a[i]*a[j]);
	    Append(~terms,ff[x]*ff[y]*m);
	    Include(~mons,m);
	end if;
    end for;
    return ainvs, terms;
end intrinsic;

intrinsic JacobianG2MonomialWeight(m::RngMPolElt) -> SeqEnum
    {This function is specific to Jacobian surface construction.}
    I := [ ];
    E := Exponents(m);
    for i in [1..16] do
	if E[i] ge 1 then Append(~I,i); end if;
	if E[i] ge 2 then Append(~I,i); end if;
    end for;
    i, j := Explode(I);
    wts, cfs := JacobianG2MonomialWeights();
    wi1 := wts[i][1]; wj1 := wts[j][1]; 
    wi2 := wts[i][2]; wj2 := wts[j][2];
    c := Coefficients(m); assert #c eq 1;
    E := Exponents(Monomials(Numerator(c[1]))[1]);
    F := Exponents(Monomials(Denominator(c[1]))[1]);
    c1 := 2*&+E - 2*&+F;
    c2 := &+[ -(i-1)*(E[i]-F[i]) : i in [1..7] ];
    vprintf JacG2Relations, 2 :
	"W = [%2o,%2o] + [%2o,%2o] + [%2o,%2o]\n",
	wts[i][1], wts[i][2], wts[j][1], wts[j][2], c1, c2;
    W := [ wi1+wj1+c1, wi2+wj2+c2 ];
    return W;
end intrinsic;

intrinsic JacobianG2MonomialRelationsOfWeight(W::[RngIntElt] :
    Relations := [], StrictWeight := true) -> SetIndx
    {This function is specific to Jacobian surface construction.}
    require #W eq 2 : "Argument must have length 2.";
    ainvs, mons := JacobianG2MonomialsOfWeight(W);
    V := LinearRelations(ainvs : Relations := Relations);
    WghtRels := {@ @};
    wts, cfs := JacobianG2MonomialWeights();
    for v in Basis(V) do
	f := &+[ v[i]*mons[i] : i in [1..#mons] ];
	k := Random([ i : i in [1..Degree(V)] | v[i] ne 0 ]);
	wghtf := JacobianG2MonomialWeight(v[k]*mons[k]);
	if not StrictWeight or W eq wghtf then
	    Include(~WghtRels,f);
	else
	    vprintf JacG2Relations : 
		"Found relation of weight [%2o,%2o] (not [%2o,%2o]):\n",
		wghtf[1], wghtf[2], W[1], W[2];
	    vprint JacG2Relations : f;
	end if;
    end for;
    return WghtRels;
end intrinsic;

/*
F<f0,f1,f2,f3,f4,f5,f6> := FunctionField(Rationals(),7 : Global);
P<X00,X01,X02,X03,X04,X05,X06,X07,
  X08,X09,X10,X11,X12,X13,X14,X15> := PolynomialRing(F,16 : Global);
a, r := JacobianRelations([f0,f1,f2,f3,f4,f5,f6]);
R<x1,x2,y1,y2> := PolynomialRing(F,4 : Global);
F1 := y1^2-(f6*x1^6 + f5*x1^5 + f4*x1^4 + f3*x1^3 + f2*x1^2 + f1*x1 + f0);
F2 := y2^2-(f6*x2^6 + f5*x2^5 + f4*x2^4 + f3*x2^3 + f2*x2^2 + f1*x2 + f0);
DomRels := [F1,F2];
I := ideal< R | DomRels >;
//time MonomialRelationsOfWeight([4,0] : Relations := DomRels);
//
TotRels := {@ @};
for i in [5..0 by -1] do
    if i eq 6 then jInt := [-4..-6 by -1];
    elif i eq 5 then jInt := [-2..-5 by -1];
    elif i eq 4 then jInt := [ 0..-4 by -1];
    elif i eq 3 then jInt := [ 2..-3 by -1];
    elif i eq 2 then jInt := [ 4..-2 by -1];
    elif i eq 1 then jInt := [ 3.. 1 by -1];
    elif i eq 0 then jInt := [ 6.. 2 by -1];
    end if;
    for j in jInt do
        printf "Weight: [%2o,%2o]\n", i, j;
        NewRels := MonomialRelationsOfWeight([i,j] : Relations := DomRels);
        print NewRels;
        TotRels join:= {@ Factorization(f)[1][1] : f in NewRels @};
        print "Total relations:", #TotRels;
    end for;
end for;
*/

intrinsic GeometricObject(J::JacHyp) -> Sch
    {}
    if assigned J`GeometricObject then
	return J`GeometricObject;
    end if;
    C := Curve(J);
    f, h := HyperellipticPolynomials(C);
    require h eq 0 : "Hyperelliptic Curve must be a simplified model. See SimplifiedModel()";
    require Genus(C) eq 2 : "Hyperelliptic Curve must have genus 2";
    require Degree(f) eq 6 : "At the moment the curve must be defined as y^2 = sextic";
    fs := Eltseq(f);
    J`aInject, JacRels := JacobianRelations(fs);
    P15 := ProjectiveSpace(BaseRing(C), 15);
    I := ideal < CoordinateRing(P15) | JacRels >;
    J`GeometricObject := Scheme(P15, I);
    return J`GeometricObject;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

function PointPair(j) // JacHypPt -> SeqEnum
    C := Curve(Parent(j));
    if IsIdentity(j) then
	return IndexedSetToSequence(PointsAtInfinity(C));
    end if;
    a, b := Explode(Eltseq(j));
    K := BaseField(C);
    if Degree(a) eq 2 and IsIrreducible(a) then
        L := ext < K | a >;
        x := Roots(a, L);
    else
        L := K;
        x := Roots(a);
    end if;
    // In case we have a repeated root:
    if #x eq 2 then
	x1 := x[1][1];
	x2 := x[2][1]; 
    else
	// really assuming a sextic model
	assert Degree(a) eq 2;
	x1 := x[1][1];
	x2 := x1;
    end if;
    y1 := Evaluate(b, x1); y2 := Evaluate(b, x2);
    return [ C(L)![x1,y1,1], C(K)![x2,y2,1] ];
end function;

//////////////////////////////////////////////////////////////////////////////
// Hack to create a map from the Pic^0(C) = Jacobian(C) to the Jacobian
// defined as a scheme.
//////////////////////////////////////////////////////////////////////////////

/*
intrinsic Inject(j::JacHypPt) -> Pt
    {}
    K := BaseField(Curve(Parent(j)));
    J := Parent(j);
    S := GeometricObject(Parent(j));
    if IsIdentity(j) then return S![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    end if;
    // A crude hack to get the map going.
    P4 := ProjectiveSpace(K,4);
    a := [ FunctionField(P4)!J`aInject[i] : i in [1..#(J`aInject)]];
    f := ProjectiveMap(a,P4);
    PtOne, PtTwo := Explode(PointPair(j));
    return S!Eltseq(f([PtOne[1],PtTwo[1], PtOne[2], PtTwo[2],1]));
end intrinsic;
*/

intrinsic CrudeJacobianInjection(j::JacHypPt) -> SeqEnum
    {}
    K := BaseField(Curve(Parent(j)));
    S := GeometricObject(Parent(j));
    PtOne, PtTwo := Explode(PointPair(j));
    return [ Evaluate(Parent(j)`aInject[i],[PtOne[1],PtTwo[1],PtOne[2],PtTwo[2]]) : i in [1..16]];
end intrinsic;
