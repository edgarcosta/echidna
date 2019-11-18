////////////////////////////////////////////////////////////////////////
//                                                                    //
//      Complementation, Puncturing, and Subcodes with Support        //
//                         David Kohel                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Complement(C::Code, D::Code) -> Code
    {The subcode of C with complementary support to D.}
    require D subset C : "Argument 2 must be a subcode of argument 1";
    n := Length(C);
    S := { i : i in [1..n] | i notin Support(D) };
    return SupportedSubcode(C,S);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                       Punctured Codes                              //
// N.B. Provides the noun form where the verb form exists.            //
////////////////////////////////////////////////////////////////////////

intrinsic PuncturedCode(C::Code, i::RngIntElt) -> Code, Map
    {}
    return PuncturedCode(C,{i});
end intrinsic;

intrinsic PuncturedCode(C::Code, S::{RngIntElt}) -> Code, Map
    {}
    if #S eq 0 then 
	return C, hom< C -> C | x :-> x, x :-> x >;
    end if;
    n := Length(C);
    k := Dimension(C);
    FF := BaseField(C); 
    G := GeneratorMatrix(C);
    M := Matrix(k,n-#S,
	&cat[ Parent([ FF | ]) | [ G[j,i] : i in [1..n] 
	| i notin S ] : j in [1..k] ] );
    D := PunctureCode(C,S);
    h := hom< C->D | 
	v :-> [ v[i] : i in [1..n] | i notin S ],
	u :-> &+[ v[i]*C.i : i in [1..k] ] where v := Solution(M,u) >; 
    return D, h;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                       Supported Subcodes                           //
////////////////////////////////////////////////////////////////////////

intrinsic SupportedSubcode(C::Code, S::{RngIntElt}) -> Code
    {The subcode of C with support in S.}
    V := AmbientSpace(C);
    return sub< C | 
	VectorSpace(C) meet sub< V | [ V.i : i in S ] > >;
end intrinsic;

intrinsic SupportedSubcode(C::Code, S::[RngIntElt]) -> Code
    {The subcode of C with support in S.}
    return SupportedSubcode(C,SequenceToSet(S));
end intrinsic;

