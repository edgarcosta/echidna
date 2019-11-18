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

function AmbientProductSpace(C)
    PP := AmbientSpace(C);
    ss := Names(PP); ns := #ss;
    K := BaseRing(PP);
    if Type(PP) eq Prj then
	if not IsOrdinaryProjective(PP) then
            err_str := "Argument 1 must be a curve in an unweighted (product) projective space.";
            return false, err_str;
        end if;
	PPxPP := ProductProjectiveSpace(K,[ns-1,ns-1]);
    elif Type(PP) eq PrjProd then
	Gr := Gradings(PP); 
	ng := #Gr;
	if not &and [ Gr[i,j] in {0,1} : i in [1..ns], j in [1..ng] ] then
            err_str := "Argument 1 must be a curve in a unweighted (product) projective space.";
            return false, err_str;
        end if;
	si := [0] cat [ Max([ i : i in [1..ns] | Gr[j][i] ne 0 ]) : j in [1..ng] ];
	dims := [ si[i+1] - si[i] : i in [1..#si-1] ];
	PPxPP := ProductProjectiveSpace(K,dims cat dims);
    else
        err_str := "Argument 1 must be embedded in a projective space or product projective space.";
        return false, err_str;
    end if;
    if &and[ s[1] eq "X" : s in ss ] then
        ssxss := ss cat [ "Y" * s[[2..#s]] : s in ss ];
    elif &and[ s[1] eq "U" : s in ss ] then
        ssxss := ss cat [ "V" * s[[2..#s]] : s in ss ];
    else
        ssxss := [ s * "1" : s in ss ] cat [ s * "2" : s in ss ];
    end if;
    AssignNames(~PPxPP,ssxss);
    return true, PPxPP;
end function;

intrinsic InstallEllipticCurveStructure(C::Crv,O::Pt :
    WeierstrassMorphism := 0, ExtendMorphisms := true)
    {}
    K := BaseRing(C);
    require IsNonsingular(C) and IsProjective(C) : 
	"Argument 1 must be a nonsingular projective curve.";
    require Genus(C) eq 1 : "Argument 1 must be a genus 1 curve.";
    require O in C(K) : "Argument 2 must be a rational point of argument 1.";
    // Morphism to elliptic curve
    if Type(WeierstrassMorphism) eq RngIntElt then
	E, phi := EllipticCurve(C,O);
	if ExtendMorphisms then
	    phi := Extend(phi);
	end if;
	bool, phi_inv := IsInvertible(phi);
	require bool : "Unable to determine inverse of morphism to elliptic curve.";
	if ExtendMorphisms then
	    phi_inv := Extend(phi_inv);
	end if;
	phi := map< C->E | AllDefiningPolynomials(phi), AllDefiningPolynomials(phi_inv) >;
    else
	phi := WeierstrassMorphism;
	E := Codomain(phi);
	if ExtendMorphisms then
	    phi := Extend(phi);
	end if;
	require phi(O) eq E!0 :
	    "Parameter WeierstrassMorphism must take argument to the group identity.";
	if HasKnownInverse(phi) then
	    phi_inv := Inverse(phi);
	else
	    bool, phi_inv := IsInvertible(phi); 
	    require bool : "Parameter WeierstrassMorphism must be invertible.";
	end if;
	if ExtendMorphisms then
	    phi_inv := Extend(phi_inv);
	end if;
	phi := map< C->E | AllDefiningPolynomials(phi), AllDefiningPolynomials(phi_inv) >;
    end if;
    InstallEllipticCurveStructure(C,phi);
end intrinsic;

intrinsic InstallEllipticCurveStructure(C::Crv,phi::MapSch)
    {}
    K := BaseRing(C);
    require Domain(phi) cmpeq C :
        "Argument 2 must be an isomorphism of argument 1 with an elliptic curve.";
    E := Codomain(phi);
    require IsEllipticCurve(E):
        "Argument 2 must be an isomorphism of argument 1 with an elliptic curve.";
    require IsNonsingular(C) and IsProjective(C) : 
	"Argument 1 must be a nonsingular projective curve.";
    bool, phi_inv := IsInvertible(phi);
    require bool: 
        "Argument 2 must be an isomorphism of argument 1 with an elliptic curve.";
    // Define CxC -> ExE:
    bool, PPxPP := AmbientProductSpace(C); require bool : PPxPP; 
    ns := #Names(Ambient(C));
    X1 := [ PPxPP.i : i in [1..ns] ];
    X2 := [ PPxPP.i : i in [ns+1..2*ns] ];
    polys := DefiningPolynomials(C);
    CxC := Scheme(PPxPP,[ Evaluate(f,X1) : f in polys ] cat [ Evaluate(f,X2) : f in polys ]);
    ExE := Domain(AdditionMorphism(E));
    polys := AllDefiningPolynomials(phi);
    phi_CxC_ExE := map< CxC->ExE |
	[ [ Evaluate(f,X1) : f in polys[i] ] cat [ Evaluate(f,X2) : f in polys[j] ] : i,j in [1..#polys] ] >;
    // Addition morphism:
    mu_E := AdditionMorphism(E);
    mu_C := phi_CxC_ExE * mu_E * phi_inv;
    // Inverse morphism:
    invC := phi * InverseMorphism(E) * phi_inv;
    // Initialize the elliptic curve structure:
    C`IdentityElement := phi_inv(E!0);
    C`InverseMorphism := invC;
    C`AdditionMorphism := mu_C;
    C`WeierstrassMorphism := Type(E) eq CrvEll select phi else phi * WeierstrassMorphism(E);
    C`KummerMorphism := phi * KummerMorphism(E);
    C`EllipticModelType := "Elliptic curve by isomorphism pullback";
end intrinsic;

intrinsic InverseMorphism(E::CrvEll) -> MapAutSch
    {The inverse morphism of the elliptic curve E.}
    a1, _, a3 := Explode(Eltseq(E));
    return Automorphism(E,[0,-a1,-a3,-1]);
end intrinsic;

intrinsic AdditionMorphism(E::CrvEll) -> MapSch
    {}
    if assigned E`AdditionMorphism then
	return E`AdditionMorphism;
    end if;
    FF := BaseField(E);
    KK<x1,x2> := FunctionField(FF,2);
    PK<y1,y2> := PolynomialRing(KK,2);
    fE := DefiningPolynomial(E);
    LL<y1,y2> := quo< PK | Evaluate(fE,[x1,y1,1]), Evaluate(fE,[x2,y2,1]) >;
    P1 := E(LL)![x1,y1,1]; P2 := E(LL)![x2,y2,1];
    bool, PExPE := AmbientProductSpace(E); assert bool;
    X1,Y1,Z1,X2,Y2,Z2 := Explode([ PExPE.i : i in [1..6] ]);
    ExE := Scheme(PExPE,[ Evaluate(fE,[X1,Y1,Z1]), Evaluate(fE,[X2,Y2,Z2]) ]);
    IxI := DefiningIdeal(ExE);
    BxB := Eltseq(P1+P2);
    function LLToFunFld(c)
	c_poly := PK!c;
	c_mons := Monomials(c_poly);
	c_cffs := Coefficients(c_poly);
	return &+[ Evaluate(c_cffs[i],[X1/Z1,X2/Z2])*Evaluate(c_mons[i],[Y1/Z1,Y2/Z2]) : i in [1..#c_cffs] ];
    end function;
    AddCffs := [ (x1-x2)^3*c : c in Eltseq(P1+P2) ];
    AddFunFlds := [ LLToFunFld(c) : c in AddCffs ]; 
    mExE := map< ExE->E | AddFunFlds >;
    pExE := AllDefiningPolynomials(mExE);
    pExE := [ [ NormalForm(f,IxI) : f in S ] : S in pExE ];
    pExE := [ [ f div den : f in S ] where den := GCD(S) : S in pExE ];
    mExE := map< ExE->E | pExE >;
    E`AdditionMorphism := mExE;
    return mExE;
end intrinsic;
