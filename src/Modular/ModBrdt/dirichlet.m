////////////////////////////////////////////////////////////////////////
//                                                                    //  
//                    Dimensions of Brandt Modules                    //
//                            David Kohel                             // 
//                                                                    // 
////////////////////////////////////////////////////////////////////////

intrinsic DirichletCharacter(M::ModBrdt) -> GrpDrchElt
    {}
    return DirichletGroup(1,BaseRing(M))!1;
end intrinsic;
