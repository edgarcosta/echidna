//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//               MORPHISMS OF SINGULAR HYPERELLIPTIC CURVES                 //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare type HomPicCrv[MapPicCrv];

declare attributes HomPicCrv:
    Codomain,
    Domain;

declare attributes MapPicCrv:
    Parent,
    CurveMap;

intrinsic Hom(C::CrvGrp,D::CrvGrp) -> HomPicCrv
    {}
    H := New(HomPicCrv);
    H`Domain := C;
    H`Codomain := D;
    return H;
end intrinsic;

intrinsic Hom(C::CrvGrp,J::PicHypSng) -> HomPicCrv
    {}
    H := New(HomPicCrv);
    H`Domain := C;
    H`Codomain := J;
    return H;
end intrinsic;

intrinsic Hom(J::PicHypSng,C::CrvGrp) -> HomPicCrv
    {}
    H := New(HomPicCrv);
    H`Domain := J;
    H`Codomain := C;
    return H;
end intrinsic;

intrinsic Hom(C::PicHypSng,J::PicHypSng) -> HomPicCrv
    {}
    H := New(HomPicCrv);
    H`Domain := C;
    H`Codomain := J;
    return H;
end intrinsic;

intrinsic IsCoercible(M::HomPicCrv,phi::.)
    -> BoolElt, MapPicCrv
    {}
    if ISA(Type(phi),Map) then
	C1 := Type(M`Domain) eq PicHypSng
	    select Curve(M`Domain) else M`Domain;
	C2 := Type(M`Codomain) eq PicHypSng
	    select Curve(M`Codomain) else M`Codomain;
	if C1 eq Domain(phi) and C2 eq Codomain(phi) then
	    m := New(MapPicCrv);
	    m`Parent := M;
	    m`CurveMap := phi;
	    return true, m;
	end if;
    else
	"NOT";
    end if;
    return false, "Invalid coercion";
end intrinsic;

intrinsic Print(H::HomPicCrv, level::MonStgElt)
    {}
    J1 := H`Domain;
    J2 := H`Codomain;
    if J1 cmpeq J2 then
	printf "Endomomorphism ring of %o", J1;
    else
	printf "Module of homomorphisms from %o to %o", J1, J2;
    end if;
end intrinsic;

intrinsic Print(f::MapPicCrv, level::MonStgElt)
    {}
    printf "%o", f`CurveMap;
end intrinsic;

intrinsic 'eq'(H1::HomPicCrv,H2::HomPicCrv) -> BoolElt
    {}
    return Domain(H1) cmpeq Domain(H1) and Codomain(H2) cmpeq Codomain(H2);
end intrinsic;

intrinsic 'eq'(f::MapCrvEll,g::MapCrvEll) -> BoolElt
    {}
    if f`Parent ne g`Parent then return false; end if;
    require assigned f`CurveMap and assigned g`CurveMap :
	"Arguments must be defined by curve maps";
    return f`CurveMap eq g`CurveMap;
end intrinsic;

intrinsic Domain(H::HomPicCrv) -> Crv
    {The domain of H.}
    return H`Domain;
end intrinsic;

intrinsic Codomain(H::HomPicCrv) -> Crv
    {The codomain of H.}
    return H`Codomain;
end intrinsic;

