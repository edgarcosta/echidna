///////////////////////////////////////////////////////////////////////
// Based on: LinearSys/elt_linsys.m
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
// Lines
///////////////////////////////////////////////////////////////////////

function DefinesLine(S)
    if #S eq 0 then
	return false, "Argument must be nonempty";
    end if;
    PP := Ambient(Scheme(Universe(S)));
    if Ring(Universe(S)) ne BaseRing(PP) then
	return false,
   	   "Elements of argument must be defined
	    over the base ring of their scheme";
    end if;
    L := LinearSystem(PP,1);
    C := Scheme(PP,Sections(LinearSystem(L,S)));
    if Dimension(C) ne 1 then
	return false, "Argument does not define a line.";
    elif Dimension(PP) eq 2 then
	_, C := IsRationalCurve(C);
    end if;
    return true, C;
end function;

intrinsic Line(S::{Pt}) -> Sch
    {The unique line in the projective space P through the
    points of S if it exists}

    bool, C := DefinesLine(SetToSequence(S));
    require bool : C;
    return C;
end intrinsic;
    
intrinsic Line(S::[Pt]) -> Sch
    {The unique line in the projective space P through the
    points of S if it exists}

    bool, C := DefinesLine(S);
    require bool : C;
    return C;
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Conics
///////////////////////////////////////////////////////////////////////

function DefinesHypersurface(PP,S,d)
    // The unique hypersurface of degree d of S passing
    // through the points of P.
    if Dimension(PP) ne 2 or Gradings(PP) ne [ [1,1,1] ] then
	return false,
	   "Universe of argument must be an ordinary projective plane.";
    end if;
    PPSet := PP(BaseRing(PP));
    bool, S := CanChangeUniverse(S,PPSet);
    if not bool then
	return false,
	   "Elements of argument be points over the base ring of scheme.";
    end if;
    L2 :=  LinearSystem(LinearSystem(PP,d),[ PPSet | P : P in S ]);
    secs := Sections(L2);
    if #secs ne 1 then
	return false, "Argument does not define a unique conic.";
    end if;
    return true, Scheme(PP,secs);
end function;

intrinsic Conic(S::{Pt}) -> Crv
    {The unique conic in the projective plane P through
    the points of S if it exists.}
    PP := Ambient(Scheme(Universe(S)));
    bool, X := DefinesHypersurface(PP,S,2);
    require bool : X;
    return Conic(PP,DefiningPolynomial(X));
end intrinsic;

intrinsic Conic(S::[Pt]) -> Crv
    {The unique conic in the projective plane P through
    the points of S if it exists.}
    PP := Ambient(Scheme(Universe(S)));
    bool, X := DefinesHypersurface(PP,S,2);
    require bool : X;
    return Conic(PP,DefiningPolynomial(X));
end intrinsic;
