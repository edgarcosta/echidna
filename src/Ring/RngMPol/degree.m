////////////////////////////////////////////////////////////////////////
//                           Degree of Ideals                         //
////////////////////////////////////////////////////////////////////////

intrinsic Degree(I::RngMPol) -> RngIntElt
    {The degree of a zero dimensional ideal.}
    require Dimension(I) le 0 :
        "Argument must be a prime ideal of dimension 0.";
    return Dimension(quo< Generic(I) | I >);
end intrinsic;
