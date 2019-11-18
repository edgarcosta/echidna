////////////////////////////////////////////////////////////////////////
//                            Printing                                //
////////////////////////////////////////////////////////////////////////

intrinsic Print(M::ModSS, level::MonStgElt)
    {}
    printf "Supersingular module associated to ";
    printf "X_0(%o)/GF(%o) of dimension %o",
	AuxiliaryLevel(M), Prime(M), Dimension(M);
end intrinsic;

intrinsic Print(P::ModSSElt, level::MonStgElt)
    {}
    printf "%o", P`element;
end intrinsic;

