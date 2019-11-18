//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2010 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function AffineSchemeProduct(X,Y : Names := [])
    KK := BaseRing(X);
    assert KK eq BaseRing(Y);
    AX := AmbientSpace(X); nX := Dimension(AX);
    RX := CoordinateRing(AX);
    AY := AmbientSpace(Y); nY := Dimension(AY);
    RY := CoordinateRing(AY);
    nn := nX + nY;
    AA := AffineSpace(KK,nn);
    if #Names eq 0 then
	sX := [ Sprint(Name(AX,i)) : i in [1..nX] ];
	sY := [ Sprint(Name(AY,j)) : j in [1..nY] ];
	ss := [ s * "1" : s in sX ] cat [ s * "2" : s in sY ];
    else
	ss := Names;
    end if;
    RR := CoordinateRing(AA);
    mX := hom< RX->RR | [ RR.i : i in [1..nX] ] >;
    mY := hom< RY->RR | [ RR.i : i in [nX+1..nn] ] >;
    AssignNames(~AA,ss);
    rels := [ ];
    if X ne AX then
	rels cat:= [ mX(f) : f in DefiningPolynomials(X) ];
    end if;
    if Y ne AY then
	rels cat:= [ mY(g) : g in DefiningPolynomials(Y) ];
    end if;
    if #rels eq 0 then
	return AA;
    else
	return Scheme(AA,rels);
    end if;
end function;

function ProjectiveSchemeProduct(X,Y : Names := [])
    KK := BaseRing(X);
    assert KK eq BaseRing(Y);
    PX := AmbientSpace(X);
    boolX := true;
    if Type(PX) eq Prj then
	nX := Dimension(PX) + 1;
	if IsOrdinaryProjective(PX) then
	    gX := [ Dimension(PX) ];
	else
	    boolX := false;
	end if;
    elif  Type(PX) eq PrjProd then
	GX := Gradings(PX); 
	nX := #GX[1];
	if not &and [ GX[i][j] in {0,1} : i in [1..#GX], j in [1..nX] ] then
	    sX := [0] cat [ Max([ j : j in [1..nX] | GX[i][j] ne 0 ]) : i in [1..#GX] ];
	    gX := [ sX[i+1] - sX[i] - 1 : i in [1..#sX-1] ];
	else
	    boolX := false;
	end if;
    else
	nX := Length(PX);
	boolX := false;
    end if;
    PY := AmbientSpace(Y);
    boolY := true;
    if Type(PY) eq Prj then
	nY := Dimension(PY) + 1;
	if IsOrdinaryProjective(PY) then
	    gY := [ Dimension(PY) ];
	else
	    boolY := false;
	end if;
    elif Type(PY) eq PrjProd then
	GY := Gradings(PY);
	nY := #GY[1];
	if &and [ GY[i][j] in {0,1} : i in [1..#GY], j in [1..nY] ] then
	    sY := [0] cat [ Max([ j : j in [1..nY] | GY[i][j] ne 0 ]) : i in [1..#GY] ];
	    gY := [ sY[i+1] - sY[i] - 1 : i in [1..#sY-1] ];
	else
	    boolY := false;
	end if;
    else
	nY := Length(PY);
	boolY := false;
    end if;
    if boolX and boolY then
	PXxPY := ProductProjectiveSpace(KK,gX cat gY);
    else
	PXxPY := DirectProduct(PX,PY);
    end if;
    RXxRY := CoordinateRing(PXxPY);
    RX := CoordinateRing(PX);
    RY := CoordinateRing(PY);
    mX := hom< RX->RXxRY | [ RXxRY.i : i in [1..nX] ] >;
    mY := hom< RY->RXxRY | [ RXxRY.i : i in [nX+1..nX+nY] ] >;
    if #Names eq 0 then
	sX := [ Sprint(Name(PX,i)) : i in [1..nX] ];
	sY := [ Sprint(Name(PY,j)) : j in [1..nY] ];
	ss := [ s * "1" : s in sX ] cat [ s * "2" : s in sY ];
    else
	ss := Names;
    end if;
    AssignNames(~PXxPY,ss);
    rels := [ ];
    if X ne PX then
	rels cat:= [ mX(f) : f in DefiningPolynomials(X) ];
    end if;
    if Y ne PY then
	rels cat:= [ mY(g) : g in DefiningPolynomials(Y) ];
    end if;
    if #rels eq 0 then
	return PXxPY;
    else
	return Scheme(PXxPY,rels);
    end if;
end function;

intrinsic ProductScheme(X::Sch,n::RngIntElt : Names := []) -> Sch
    {}
    require n gt 0 : "Argument 2 must be positive integer.";
    nX := Dimension(Ambient(X));
    if Type(Ambient(X)) in {Prj,PrjProd} then
	nX +:= NumberOfGradings(X);
    end if;
    sX := [ Sprint(Name(X,i)) : i in [1..nX] ];
    if &and[ s[[1..Min(2,#s)]] eq "$." : s in sX ] then
	if IsAffine(X) then
	    sX := [ "x" * s[[3..#s]] : s in sX ];
	else
	    sX := [ "X" * s[[3..#s]] : s in sX ];
	end if;
    end if;
    if n eq 1 then return X; end if;
    if #Names gt 0 then
	sXprod := Names;
    else
	sXprod := &cat[ [ s * Sprint(i) : s in sX ] : i in [1..n] ];
    end if;
    if n eq 2 then
	return ProductScheme(X,X : Names := sXprod);
    end if;
    X1 := ProductScheme(X,n div 2);
    if n mod 2 eq 0 then
	X2 := X1;
    else
	X2 := ProductScheme(X1,X);
    end if;
    return ProductScheme(X1,X2 : Names := sXprod);
end intrinsic;

intrinsic ProductScheme(X::Sch,Y::Sch : Names := []) -> Sch
    {}
    require BaseRing(X) eq BaseRing(Y) :
	"Arguments must be defined over the same ring.";
    if Type(X) in {Prj,PrjProd} and Type(Y) in {Prj,PrjProd} then
	if #Names eq 0 then
	    nX := Dimension(X) + NumberOfGradings(X);
	    sX := [ Sprint(Name(X,i)) : i in [1..nX] ];
	    if &and[ s[[1..Min(2,#s)]] eq "$." : s in sX ] then
		sX := [ "X" * s[[3..#s]] : s in sX ];
	    end if;
	    nY := Dimension(Y) + NumberOfGradings(Y);
	    sY := [ Sprint(Name(Y,j)) : j in [1..nY] ];
	    if &and[ s[[1..Min(2,#s)]] eq "$." : s in sY ] then
		sY := [ "Y" * s[[3..#s]] : s in sY ];
	    end if;
	    sXxY := sX cat sY;
	    if #SequenceToSet(sXxY) lt nX + nY then
		sXxY := [ s * "1" : s in sX ] cat [ s * "2" : s in sY ];
	    end if;
	else
	    sXxY := Names;
	end if;
	return ProjectiveSchemeProduct(X,Y : Names := sXxY);
    elif Type(X) eq Aff and Type(Y) eq Aff then
	if #Names eq 0 then
	    nX := Dimension(X);
	    sX := [ Sprint(Name(X,i)) : i in [1..nX] ];
	    if &and[ s[[1..Min(2,#s)]] eq "$." : s in sX ] then
		sX := [ "x" * s[[3..#s]] : s in sX ];
	    end if;
	    nY := Dimension(Y);
	    sY := [ Sprint(Name(Y,j)) : j in [1..nY] ];
	    if &and[ s[[1..Min(2,#s)]] eq "$." : s in sY ] then
		sY := [ "y" * s[[3..#s]] : s in sY ];
	    end if;
	    sXxY := sX cat sY;
	    if #SequenceToSet(sXxY) lt nX + nY then
		sXxY := [ s * "1" : s in sX ] cat [ s * "2" : s in sY ];
	    end if;
	else
	    sXxY := Names;
	end if;
	return AffineSchemeProduct(X,Y : Names := sXxY);
    end if;
    PX := AmbientSpace(X);
    PY := AmbientSpace(Y);
    aff_prod := Type(PX) eq Aff and Type(PY) eq Aff;
    prj_prod := Type(PX) in {Prj,PrjProd,TorVar} and Type(PY) in {Prj,PrjProd,TorVar};
    if aff_prod then
	return AffineSchemeProduct(X,Y);
    elif prj_prod then
	return ProjectiveSchemeProduct(X,Y);
    end if;
    require false : "Arguments must be both affine or projective.";
end intrinsic;

intrinsic MorphismGraph(f::MapSch) -> MapSch
    {}
    X := Domain(f);
    A := AmbientSpace(X);
    n := Length(A);
    one := map< X->X | [ A.i : i in [1..n] ] >;
    return MorphismGraph(one,f);
end intrinsic;

intrinsic MorphismGraph(f::MapSch,g::MapSch) -> MapSch
    {This isn't quite the right function name -- want f:X -> Y, g:X -> Z,
    and construct the function X -> XxX -> YxZ composing the diagonal
    map with f x g.}
    X := Domain(f);
    require X eq Domain(g) : "Arguments 1 and 2 must have the same domain.";
    YxZ := ProductScheme(Codomain(f),Codomain(g));
    return Image(map< X->YxZ | [ S1 cat S2 :
	S1 in AllDefiningPolynomials(f), S2 in AllDefiningPolynomials(g) ] >); 
end intrinsic;
