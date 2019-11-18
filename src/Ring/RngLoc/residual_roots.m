// residual_roots.m  Root Finding over Local Artin Rings 
// Copyright (C) 2002 David R. Kohel.
    
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA


////////////////////////////////////////////////////////////////////////
//              Root Finding over Local Artin Rings                   //
//                         David R. Kohel                             //
//                    kohel@maths.usyd.edu.au                         //
//                          August 2002                               //
////////////////////////////////////////////////////////////////////////

declare verbose ResidualRoots, 2;

/*
// Example:
Z2 := pAdicRing(2,8);
PZ<x> := PolynomialRing(Z2);
R2 := LocalRing(Z2,x^2+2*x+2);
PR<x> := PolynomialRing(R2);
f := 5*x^2 - 88*x - 112;
ResidualRoots(f,16);
*/

function ResidueReductionRoots(f,i)
    R := BaseRing(Parent(f));
    pi := UniformizingElement(R);
    F, phi := ResidueClassField(R);
    P := PolynomialRing(F);
    vprint ResidualRoots, 2 : "pi^i =", pi^i;
    g := P![ phi(c div pi^i) : c in Coefficients(f) ];
    vprint ResidualRoots, 2 : "(g/pi^i) mod pi =", g;
    if g eq 0 then
	return [ a@@phi : a in F ];
    end if;
    return [ r[1]@@phi : r in Roots(g) ];
end function;

intrinsic ResidualRoots(f::RngUPolElt,n::RngIntElt) -> SeqEnum
    {}
    R := BaseRing(Parent(f));
    P := PolynomialRing(R); x := P.1;
    pi := UniformizingElement(R);
    rts := ResidueReductionRoots(f,0);
    for i in [1..n-1] do
	vprint ResidualRoots : "i =", i;
	vprint ResidualRoots : "Current number of roots:", #rts;
	rtsi := rts;
	rts := [ R | ];
	for r in rtsi do
	    vprint ResidualRoots, 2 : "Root =", r;
	    vprint ResidualRoots, 2 :
	       "Current valuation: ", Valuation(Evaluate(f,r));
	    assert Valuation(Evaluate(f,r)) ge i;
	    g := Evaluate(f,x*pi^i+r);
	    vprint ResidualRoots, 2 : "g =", g;
	    qtsi := ResidueReductionRoots(g,i);
	    rts cat:= [ R | r + pi^i*q : q in qtsi ];
	end for;
    end for;
    return rts;
end intrinsic;

function HasResidualRootRecursion(f,x0,i,n)
    R := BaseRing(Parent(f));
    P := PolynomialRing(R); x := P.1;
    pi := UniformizingElement(R);
    F, phi := ResidueClassField(R);
    P := PolynomialRing(F);
    vprintf ResidualRoots, 2 : "(i,n) = (%o,%o)\n", i, n;
    vprint ResidualRoots, 2 : "pi^i =", pi^i;
    g := P![ phi(c div pi^i) : c in Coefficients(Evaluate(f,x0+x*pi^i)) ];
    vprint ResidualRoots, 2 : "(g/pi^i) mod pi =", g;
    if g eq 0 then
	extrts := [ x0 + (a@@phi)*pi^i : a in F ];
    else
        extrts := [ x0 + (r[1]@@phi)*pi^i : r in Roots(g) ];
    end if;
    vprintf ResidualRoots, 2 : "Found %o extension roots\n", #extrts;
    if #extrts eq 0 then
	return false, _;
    elif i+1 eq n then
	return true, extrts[1];
    else
	for x1 in extrts do
	    bool, x2 := HasResidualRootRecursion(f,x1,i+1,n);
	    if bool then return true, x2; end if;
	end for;
    end if;
    return false, _;
end function;

intrinsic HasResidualRoot(f::RngUPolElt,n::RngIntElt) -> SeqEnum
    {}
    R := BaseRing(Parent(f));
    P := PolynomialRing(R); x := P.1;
    rts := ResidualRoots(f,1);
    if n eq 1 and #rts ge 1 then return true, rts[1]; end if;
    for x0 in rts do
	bool, x1 := HasResidualRootRecursion(f,x0,1,n);
	if bool then
	    vprint ResidualRoots : "Found residual root.";
	    return true, x1;
	end if;
    end for;
    return false, _;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//         Repeat everything with multiple polynomials                // 
////////////////////////////////////////////////////////////////////////

function ResidueReductionSequenceRoots(S,i)
    // S is a polynomial sequence
    R := BaseRing(Universe(S));
    pi := UniformizingElement(R);
    F, phi := ResidueClassField(R);
    P := PolynomialRing(F);
    vprint ResidualRoots, 2 : "i =", i;
    T := [ P![ phi(c div pi^i) : c in Eltseq(f) ] : f in S ];
    vprint ResidualRoots, 2 : "[(g/pi^i) mod pi ] =", T;
    if &and[ g eq 0 : g in T ] then
	return [ a@@phi : a in F ];
    end if;
    i := 1; g0 := 0;
    while g0 eq 0 do g0 := T[i]; i +:= 1; end while;
    return [ r[1]@@phi : r in Roots(g0) |
        &and[ Evaluate(g,r[1]) eq 0 : g in T ] ];
end function;

intrinsic ResidualRoots(S::[RngUPolElt],N::[RngIntElt]) -> SeqEnum
    {}
    R := BaseRing(Universe(S));
    P := PolynomialRing(R); x := P.1;
    pi := UniformizingElement(R);
    rts := ResidueReductionSequenceRoots(S,0);
    n := Max(N);
    for i in [1..n-1] do
	vprint ResidualRoots : "i =", i;
	vprint ResidualRoots : "Current number of roots:", #rts;
	rtsi := rts;
	rts := [ R | ];
	for r in rtsi do
	    vprint ResidualRoots, 2 : "Root =", r;
	    vprint ResidualRoots, 2 : "Current valuations: ",
  	        [ Valuation(Evaluate(f,r)) : f in S ];
	    vprint ResidualRoots, 2 : "Target valuations: ", N;
	    assert
  	        &and[ Valuation(Evaluate(S[j],r))
	            ge Min(i,N[j]) : j in [1..#S] ];
	    T := [ Evaluate(S[j],x*pi^i+r) : j in [1..#S] | i le N[j] ];
	    vprint ResidualRoots, 2 : "T =", T;
	    qtsi := ResidueReductionSequenceRoots(T,i);
	    rts cat:= [ R | r + pi^i*q : q in qtsi ];
	end for;
    end for;
    return rts;
end intrinsic;
/*
function HasResidualRootRecursion(S,x0,i,n)
    R := BaseRing(Universe(S));
    P := PolynomialRing(R); x := P.1;
    pi := UniformizingElement(R);
    F, phi := ResidueClassField(R);
    P := PolynomialRing(F);
    vprint ResidualRoots, 2 : "pi^i =", pi^i;
    T := [ P![ phi(c div pi^i) :
      c in Coefficients(Evaluate(f,x0+x*pi^i)) ] : f in S ];
    vprint ResidualRoots, 2 : "[(g/pi^i) mod pi ] =", T;
    if &and[ g eq 0 : g in T ] then
	extrts := [ x0 + (a@@phi)*pi^i : a in F ];
    else
	extrts := [ x0 + (r[1]@@phi)*pi^i : r in Roots(T[1]) |
	   &and[ Evaluate(g,r[1]) eq 0 : g in T ] ];
    end if;
       if #extrts eq 0 then
	return false, _;
    elif i+1 eq n then
	return true, extrts[1];
    else
	for x1 in extrts do
	    bool, x2 := HasResidualRootRecursion(S,x0,i+1,n);
	    if bool then return true, x2; end if;
	end for;
    end if;
    return false, _;
end function;

intrinsic HasResidualRoot(S::[RngUPolElt],n::RngIntElt) -> SeqEnum
    {}
    R := BaseRing(Parent(f));
    P := PolynomialRing(R); x := P.1;
    rts := ResidualRoots(S,1);
    if n eq 1 and #rts ge 1 then return true, rts[1]; end if;
    for x0 in rts do
	bool, x1 := HasResidualRootRecursion(S,x0,1,n);
	if bool then return true, x1; end if;
    end for;
    return false, _;
end intrinsic;
*/




