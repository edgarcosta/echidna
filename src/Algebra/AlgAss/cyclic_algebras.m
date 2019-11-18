////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic CyclicAlgebra(L::FldNum,g::Map) -> AlgAss
    {For a degree n cylic number field L/K and automorphism g
    of order n, form the cyclic twisted algebra L<g> over K.}
    K := BaseField(L);
    require Domain(g) cmpeq L and Codomain(g) cmpeq L : 
	"Argument 2 must be an automorphism of argument 1.";
    B := Basis(L);
    M := Matrix([ Eltseq(g(x)) : x in B ]);
    m := Order(M);
    n := Degree(L);
    N := Parent(M)!1;
    MPow := [ N ];
    for i in [1..m-1] do
	N *:= M;
	Append(~MPow,N);
    end for;
    StrcCnsts := [ K | ]; 
    for i in [0..m-1], x in B do
	for j in [0..m-1], y in B do
	    z := x*L!Eltseq(Vector(Eltseq(y))*MPow[i+1]);
	    for k in [0..m-1] do
		StrcCnsts cat:= k eq (i+j) mod m
		    select Eltseq(z) else [ K | 0 : i in [1..n] ];
	    end for;
	end for;
    end for;
    return AssociativeAlgebra< K, n^2 | StrcCnsts >;
end intrinsic;

intrinsic CyclicAlgebra(L::FldNum,g::Map,a::RngIntElt) -> AlgAss
    {For a degree n cylic number field L/K and automorphism g
    of order n, form the cyclic twisted algebra L<g> over K.}
    K := BaseField(L);
    require Domain(g) cmpeq L and Codomain(g) cmpeq L : 
	"Argument 2 must be an automorphism of argument 1.";
    B := Basis(L);
    M := Matrix([ Eltseq(g(x)) : x in B ]);
    m := Order(M);
    n := Degree(L);
    N := Parent(M)!1;
    MPow := [ N ];
    for i in [1..m-1] do
	N *:= M;
	Append(~MPow,N);
    end for;
    StrcCnsts := [ K | ]; 
    for i in [0..m-1], x in B do
	for j in [0..m-1], y in B do
	    z := x*L!Eltseq(Vector(Eltseq(y))*MPow[i+1]);
	    for k in [0..m-1] do
		if k eq i+j then
		    StrcCnsts cat:= Eltseq(z);
		elif k eq i+j-m then
		    StrcCnsts cat:= Eltseq(a*z);
		else
		    StrcCnsts cat:= [ K | 0 : i in [1..n] ];
		end if;
	    end for;
	end for;
    end for;
    return AssociativeAlgebra< K, n^2 | StrcCnsts >;
end intrinsic;
