////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        SIMILARITY OF LATTICES                      //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "genus_common.m" : RLattice;

////////////////////////////////////////////////////////////////////////

intrinsic ScaledGenus(G::SymGen,c::RngElt) -> SymGen
    {}
    require Type(c) in {RngIntElt,FldRatElt} :
       "Argument must be an integer or rational.";
    L := Representative(G);
    return Genus(RLattice(Type(L),c*GramMatrix(L)));
end intrinsic;

intrinsic ScaledGenus(G::SymGenLoc,c::RngElt) -> SymGenLoc
    {}
    require Type(c) in {RngIntElt,FldRatElt} :
       "Argument must be an integer or rational.";
    p := Prime(G);
    L := Representative(G);
    return LocalGenus(RLattice(Type(L),c*GramMatrix(L)),p);
end intrinsic;

////////////////////////////////////////////////////////////////////////
