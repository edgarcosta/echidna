//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//              Algebraic Relations among Power Series                      //
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare verbose SeriesRelations, 2;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

/*
Note that for the return value we use the unique global polynomial ring
of the correct rank.  This allows for one to assign variables names and
compare results of repeated function calls. 
*/

intrinsic AlgebraicRelations(
    S::[RngSerElt],degs::[RngIntElt]) -> RngMPol
    {The ideal of relations between the elements of S, of coordinate
    degrees degs.}
    
    r := #S;
    require #degs eq r : "Arguments must have the same length.";
    R := BaseRing(Universe(S));
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
    exps := Reverse([ [ v[j] : j in [1..r] ] : v in Cdeg ]);
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(
    S::[RngSerElt],degs::[RngIntElt],tot::RngIntElt)-> RngMPol
    {The ideal of relations between the elements of S, of total degree
    at most tot and coordinate degrees degs.}
    
    r := #S;
    require #degs eq r : "Arguments must have the same length.";
    R := BaseRing(Universe(S));
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
    exps := Reverse([ e : e in vecs | &+e le tot ]);
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(
    S::[RngSerElt],deg::RngIntElt)-> RngMPol
    {The ideal of relations between the elements of S,
    of degree at most deg.}
    
    r := #S;
    R := BaseRing(Universe(S));
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
    exps := Reverse([ e : e in vecs | &+e le deg ]);
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := Basis(LinearRelations(smons));
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    return [ P | &+[ c[k]*xmons[k] : k in [1..#exps] ] : c in B ];
end intrinsic;

intrinsic AlgebraicRelations(
    f::RngSerElt,g::RngSerElt,deg::RngIntElt) -> RngMPolElt 
    {}
    R := BaseRing(Parent(f));
    P := PolynomialRing(R,2 : Global := true);
    X := P.1; Y := P.2;
    for n1 in [1..deg] do
	for n2 in [1..deg] do
	    series := [ f^(n1-i)*g^(n2-j) : j in [0..n2], i in [0..n1] ];
	    V := LinearRelations(series);
	    if Dimension(V) gt 0 then
		return [ &+[ c[(n2+1)*i+j+1]*X^(n1-i)*Y^(n2-j) 
		    : j in [0..n2], i in [0..n1] ] : c in Basis(V) ];
	    end if;
	end for;
    end for;
    return [ P | ];
end intrinsic;

intrinsic AlgebraicRelations(
    f::RngSerElt,g::RngSerElt,h::RngSerElt,deg::RngIntElt) -> RngMPolElt
    {}
    R := BaseRing(Parent(f));
    P := PolynomialRing(R,3 : Global := true);
    X := P.1; Y := P.2; Z := P.3; 
    for n1 in [1..deg] do
	for n2 in [1..deg] do
	    for n3 in [1..deg] do
		V := LinearRelations([ f^(n1-i)*g^(n2-j)*h^(n3-k) : 
		    i in [0..n1], j in [0..n2], k in [0..n3] ]);
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

