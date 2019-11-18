////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     ABELIAN MONOID STRUCTURE                       //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();

////////////////////////////////////////////////////////////////////////

import "genus_common.m" : RLattice;

////////////////////////////////////////////////////////////////////////

intrinsic '+'(G1::SymGen,G2::SymGen) -> SymGen
    {}
    require not G1`IsSpinor xor G2`IsSpinor : 
            "Arguments must both be genera or spinor genera.";
    L1 := Representative(G1);
    L2 := Representative(G2);
    if Type(L1) eq Type(L2) then  
	L := DirectSum(Representative(G1),Representative(G2));
    else
	A := DirectSum(GramMatrix(L1),GramMatrix(L2));
	L := RLattice(ModTupRng,A);
    end if;
    if G1`IsSpinor then return SpinorGenus(L); end if;
    return Genus(L);
end intrinsic;

intrinsic '+'(G1::SymGenLoc,G2::SymGenLoc) -> SymGenLoc
    {}
    p := Prime(G1);
    require Prime(G2) eq p :
        "Arguments must be p-local genera with respect to the same p.";
    L := DirectSum(Representative(G1),Representative(G2));
    return LocalGenus(L,p);
end intrinsic;

intrinsic '+:='(G1::SymGen,G2::SymGen)
    {}
    require not G1`IsSpinor xor G2`IsSpinor : 
        "Arguments must both be genera or spinor genera.";
    G1`Representative :=
        DirectSum(Representative(G1),Representative(G2));
    prms := Sort([ p : p in 
        { Prime(Gp) : Gp in LocalGenera(G1) } join 
	{ Prime(Gp) : Gp in LocalGenera(G2) } ]);
    locgens := [];
    for p in prms do
	Append(~locgens,LocalGenus(G1,p)+LocalGenus(G2,p));
    end for;
    G1`LocalGenera := locgens;
end intrinsic;

intrinsic '&+'(S::[SymGenLoc]) -> SymGenLoc
    {}
    require #S gt 0 : "Argument must be nonempty.";
    require #{ Prime(Gp) : Gp in S } eq 1 :
        "Arguments must be p-local genera with respect to the same p.";
    G := S[1]; 
    for i in [2..#S] do
	G +:= S[i];
    end for;
    return G;
end intrinsic;

intrinsic '&+'(S::[SymGen]) -> SymGen
    {}
    G := S[1];
    for i in [2..#S] do
	G +:= S[i];
    end for;
    return G;
end intrinsic;

