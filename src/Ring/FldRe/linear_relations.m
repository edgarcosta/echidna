//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//            Linear Relations among Real and Complex Numbers               //
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

//////////////////////////////////////////////////////////////////////////////
// Rational approximation of a real number.
//////////////////////////////////////////////////////////////////////////////

intrinsic RationalApproximation(x::FldReElt,e::FldReElt : Al := "LLL") -> FldRatElt
    {A rational approximation r to x to precision |x-r| < e; correct
    nomenclature for builtin magma function BestApproximation.}
    require e gt 0 and e lt 1 :
        "Argument 2 must be in the range 0 < e < 1.";
    case Al:
    when "Magma":
	return BestApproximation(x,Ceiling(1/e));
    when "LLL":
	v := LinearRelations([-1,x],e).1;
        if v[2] eq 0 then
            print "Log(x) =", Log(10,Abs(x));
            print "Log(e) =", Log(10,e);
            print v;
        end if;
        return v[1]/v[2];
    else
	require false: "Parameter \"Al\" must be \"Magma\" or \"LLL\".";
    end case;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Linear relations among a sequence of real numbers.
//////////////////////////////////////////////////////////////////////////////

intrinsic LinearRelations(S::[FldReElt]) -> ModTupRng
    {}
    RR := Universe(S);
    return LinearRelations(S,0.1^6);
end intrinsic;

intrinsic LinearRelations(S::[FldComElt]) -> ModTupRng
    {}
    CC := Universe(S);
    return LinearRelations(S,0.1^6);
end intrinsic;

intrinsic LinearRelations(S::[FldReElt], e::FldReElt) -> ModTupRng
    {}
    require e gt 0 and e lt 1 :
        "Argument 2 must be in the range 0 < e < 1.";
    n := #S;
    V := RSpace(IntegerRing(),n);
    if true then
	RR := Universe(S);
	CC := ComplexField(Precision(RR));
	v := LinearRelation(ChangeUniverse(S,CC) : Al := "LLL");
	return sub< V | v >;
    end if;
    assert false; // Need to intersect the rowspace with ZZ^n.
    M := RMatrixSpace(Universe(S),n-1,n)!0;
    for i in [1..n-1] do
	M[i,i] := S[i+1];
	M[i,i+1] := -S[i];
    end for;
    return M;
    M := LLL(M);
    B := [ V | ];
    for i in [1..Nrows(M)] do
	v := V![ Round(M[i,j]) : j in [1..n] ];
	err := Abs(&+[ v[j]*S[j] : j in [1..n] ]);
	if v ne 0 and err le e then
	    vprint RealRelations : "Rounding error:", RealField(8)!
		Sqrt(&+[ Abs(v[j]-M[i,j])^2 : j in [1..n] ]);
	    vprint RealRelations : "         error:", err;
	end if;
	if err le e then Append(~B,v); end if;
    end for;
    return sub< V | B >;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Linear relations among a sequence of complex numbers.
//////////////////////////////////////////////////////////////////////////////

intrinsic LinearRelations(S::[FldComElt], e::FldReElt) -> ModTupRng
    {Linear relations OVER THE INTEGERS of a sequence of complex numbers.}
    require e gt 0 and e lt 1 :
        "Argument 2 must be in the range 0 < e < 1.";
    n := #S;
    V := RSpace(IntegerRing(),n);
    if true then
	// Use the built-in Magma function:
	CC := ComplexField(Precision(Universe(S))-16);
	v := LinearRelation(ChangeUniverse(S,CC) : Al := "LLL");
	return sub< V | v >;
    end if;
    if false then
	// Behaves badly if the elements are pairwise linearly dependent:
	require n ge 3 : "Argument 1 must have length at least 3.";
	V := RSpace(IntegerRing(),n);
	M := RMatrixSpace(RealField(Universe(S)),n-2,n)!0;
	for i in [1..n-2] do
	    M[i,i] := -Re(S[i+1])*Im(S[i+2]) + Re(S[i+2])*Im(S[i+1]);
	    M[i,i+1] := Re(S[i])*Im(S[i+2]) + Re(S[i+2])*Im(S[i]);
	end for;
    else
	V := RSpace(IntegerRing(),n);
	M := RMatrixSpace(RealField(Universe(S)),n-1,n)!0;
	for i in [1..n-1] do
	    M[i,i] := -Re(S[i+1]);
	    M[i,i+1] := Re(S[i]);
	end for;
    end if;
    M := LLL(M);
    B := [ V | ];
    for i in [1..Nrows(M)] do
	v := V![ Round(M[i,j]) : j in [1..n] ];
	err := Abs(&+[ v[j]*S[j] : j in [1..n] ]);
	if v ne 0 and err le e then
	    vprint RealRelations : "Rounding error:", RealField(8)!
		Sqrt(&+[ Abs(v[j]-M[i,j])^2 : j in [1..n] ]);
	    vprint RealRelations : "         error:", err;
	end if;
	if err le e then Append(~B,v); end if;
    end for;
    return sub< V | B >;
end intrinsic;

