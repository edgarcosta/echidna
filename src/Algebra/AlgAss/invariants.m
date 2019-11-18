////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic DimensionOfCenter(A::AlgAss) -> SeqEnum
    {}
    if not assigned A`DimensionOfCenter then
	A`DimensionOfCenter := Dimension(Center(A));
    end if;
    return A`DimensionOfCenter;
end intrinsic;

