//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2015 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic QuadraticTwist(C::Crv[FldFin]) -> Crv
    {The quadratic twist of the given elliptic curve over a finite field.}
    require IsEllipticCurve(C):
        "Argument must be an elliptic curve model.";
    K := BaseField(C);
    require Type(K) eq FldFin:
        "Argument must be an elliptic curve model over a finite field.";
    if Characteristic(K) ne 2 then
        // Construct quadratic twist by x^2 = d:
        return QuadraticTwist(C,Nonsquare(K));
    else
        // Construct Artin-Schreier twist by x^2 - x = a:
        if IsOdd(Degree(K)) then
            return ArtinSchreierTwist(C,K!1); // a = 1
        else
            repeat a := Random(K); until Trace(a) ne 0;
            return ArtinSchreierTwist(C,a);
        end if;
    end if;
end intrinsic;

intrinsic QuadraticTwist(C::Crv,d::RngElt) -> Crv
    {The quadratic twist of the given elliptic curve by x^2 = d.}
    require IsEllipticCurve(C):
        "Argument 1 must be an elliptic curve model.";
    K := BaseField(C);
    bool, d := IsCoercible(K,d); 
    require bool:
        "Argument 2 must be coercible into the base field of argument 1.";
    // CrvEll will be caught elsewhere.
    case C`EllipticModelType:
    when "Hessian":
        error if true, "Not implemented error.";
    when "Symmetric triangular":
        error if true, "Not implemented error.";
    when "Huff normal form":
        PP := AmbientSpace(C);
        a,b := Explode(C`EllipticModelInvariants);
        return EllipticCurve_Huff_NormalForm(PP,a*d,b*d);
    when "Edwards normal form":
        PP := AmbientSpace(C);
        a,b := Explode(C`EllipticModelInvariants);
        return EllipticCurve_Twisted_Edwards_NormalForm(PP,a*d,b*d);
    when "Mu_4 normal form":
        error if true, "Not implemented error.";
    when "Semisplit mu_4 normal form":
        error if true, "Not implemented error.";
    when "Split mu_4 normal form":
        error if true, "Not implemented error.";
    when "Twisted mu_4 normal form":
        error if true, "Not implemented error.";
    when "Twisted semisplit mu_4 normal form":
        error if true, "Not implemented error.";
    when "Twisted split mu_4 normal form":
        error if true, "Not implemented error.";
    when "Jacobi":
        error if true, "Not implemented error.";
    when "Z/4Z-normal form":
        error if true, "Not implemented error.";
    when "Semisplit Z/4Z-normal form":
        error if true, "Not implemented error.";
    when "Split Z/4Z-normal form":
        error if true, "Not implemented error.";
    when "Twisted Z/4Z-normal form":
        error if true, "Not implemented error.";
    when "Split (mu_2 x Z/2Z)-normal form":
        error if true, "Not implemented error.";
    end case;
end intrinsic;

intrinsic ArtinSchreierTwist(C::Crv,a::RngElt) -> Crv
    {The quadratic twist of the given elliptic curve by x^2 - x = a.}
    require IsEllipticCurve(C):
        "Argument 1 must be an elliptic curve model.";
    K := BaseField(C);
    bool, a := IsCoercible(K,a); 
    require bool:
        "Argument 2 must be coercible into the base field of argument 1.";
    // CrvEll will be caught elsewhere.
    case C`EllipticModelType:
    when "Hessian":
        require false: "Not implemented error.";
    when "Symmetric triangular":
        require false: "Not implemented error.";
    when "Huff normal form":
        PP := AmbientSpace(C);
        a,b := Explode(C`EllipticModelInvariants); D := 4*a+1;
        return EllipticCurve_Huff_NormalForm(PP,a*D,b*D);
    when "Edwards normal form":
        PP := AmbientSpace(C);
        d,b := Explode(C`EllipticModelInvariants); D := (4*a+1);
        return EllipticCurve_Twisted_Edwards_NormalForm(PP,d*D,b*D);
    when "Mu_4 normal form":
        PP := AmbientSpace(C);
        b := Explode(C`EllipticModelInvariants);
        return EllipticCurve_Twisted_Mu4_NormalForm(b,a);
    when "Semisplit mu_4 normal form":
        PP := AmbientSpace(C);
        s := Explode(C`EllipticModelInvariants);
        return EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(s,a);
    when "Split mu_4 normal form":
        PP := AmbientSpace(C);
        c := Explode(C`EllipticModelInvariants);
        return EllipticCurve_Twisted_Split_Mu4_NormalForm(c,a);
    when "Twisted mu_4 normal form":
        PP := AmbientSpace(C);
        c, a0 := Explode(C`EllipticModelInvariants); a1 := a;
        return EllipticCurve_Twisted_Mu4_NormalForm(c,4*a0*a1+a0+a1);
    when "Twisted semisplit mu_4 normal form":
        PP := AmbientSpace(C);
        c, a0 := Explode(C`EllipticModelInvariants); a1 := a;
        return EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(c,4*a0*a1+a0+a1);
    when "Twisted split mu_4 normal form":
        PP := AmbientSpace(C);
        c, a0 := Explode(C`EllipticModelInvariants); a1 := a;
        return EllipticCurve_Twisted_Split_Mu4_NormalForm(c,4*a0*a1+a0+a1);
    when "Jacobi":
        require false: "Not implemented error.";
    when "Z/4Z-normal form":
        require false: "Not implemented error.";
    when "Semisplit Z/4Z-normal form":
        require false: "Not implemented error.";
    when "Split Z/4Z-normal form":
        require false: "Not implemented error.";
    when "Twisted Z/4Z-normal form":
        require false: "Not implemented error.";
    when "Split (mu_2 x Z/2Z)-normal form":
        require false: "Not implemented error.";
    end case;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//         Copyright (C) 2011 David Kohel <kohel@iml.univ-mrs.fr>           //
//////////////////////////////////////////////////////////////////////////////

/*
FF<e> := FunctionField(ZZ);
P2<X,Y,Z> := ProjectiveSpace(FF,2);
E0 := P2!!EllipticCurve([1,2*e,0,(1 + 8*e)^2*e^2,0]);
a1 := 2*e;
// This gives a model with minimal twist:
E1 := ArtinSchreierTwist(E0,a1);
// The double twist is again isomorphic to E0:
E2 := ArtinSchreierTwist(E1,a1);
ii := map< E0->E2 | [ 1/(1 + 8*e)^2*X, 1/(1 + 8*e)^3*(Y - 4*e*X), Z ] >;
// In general the inverse twist is given by -a/(1 + 4*a):
a2 := -a1/(1 + 4*a1);
assert E0 eq ArtinSchreierTwist(E1,a2);

// The Artin-Schreier twist scales the discriminant by 1/(1 + 4*a),
// hence a composition scales by
//     (1 + 4*a1)*(1 + 4*a2) = 1 + 4*((a1 + a2) + 4*a1*a2).
// Thus the composition of Artin-Schreier twists by a1 & a2
// is an Artin-Schreier twist by a3 = a1 + a2 + 4*a1*a2:
FF<a,b,c,a1,a2> := FunctionField(ZZ,5);
P2<X,Y,Z> := ProjectiveSpace(FF,2);
E0 := P2!!EllipticCurve([1,a,0,b,c]);
E1 := ArtinSchreierTwist(E0,a1);
E2 := ArtinSchreierTwist(E1,a2);
a3 := a1 + a2 + 4*a1*a2;
E3 := ArtinSchreierTwist(E0,a3);
E3 eq E2;
*/

intrinsic ArtinSchreierTwist(E::CrvEll,a::RngElt) -> CrvEll
    {Given an elliptic curve y^2 + h(x)y = f(x), and an element a
    of the base ring, returns the twist by the (locally at 2)
    Artin-Schreier extension z^2 - z = a, given by y^2 + h_a(x)y
    = f_a(x) - a/(1+4a) h_a(x)^2, where
    g_a(x) = g((1+4a)*x)/(1+4a)^deg(g).
    The twisting isomorphism is the compositum of the translation
    (x,y) -> (x,y+zh(x)) and the renormalization (x,y) -> ((1-2z)^2*x,(1-2z)^3*y),
    noting that (1-2z)^2 = 1+4a.}
    /*
    Translation: (x,y) -> (x,y-h(x)z)

    (y - h(x)z)^2 + h(x)(y - h(x)z)
	= y^2 + (1 - 2*z)h(x)y + (z^2 - z)*h(x)^2 
	= y^2 + (1 - 2*z)h(x)y + a*h(x)^2 = f(x)

    Normalization: (x,y) -> (x*(1+4a), y*(1-2z)^3) and dividing
    through by 1/(a + 4a)^3:

    y^2 + h(x*(1+4a))/(1+4a)*y + a/(1+4a)^3h(x*(1+4a))^2
        = y^2 + h_a(x)*y + a/(1+4a)*h_a(x)^2 = 1/(1 + 4a)^3*f(x*(1 + 4a)) = f_a(x).
                                     
    */
    K := BaseRing(E);
    bool, a := IsCoercible(K,a);
    require bool : "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(1+4*a) :
	"Argument 1 must be defined over a ring of characteristic 2 or 1 + 4*a (a = argumen 2) be invertible.";
    f, h := HyperellipticPolynomials(E);
    if Characteristic(K) eq 2 then
	return EllipticCurve(f+a*h^2,h);
    else
	x := Parent(f).1;
	fa := 1/(1+4*a)^3*Evaluate(f,x*(1+4*a));
	ha := 1/(1+4*a)*Evaluate(h,x*(1+4*a));
	return EllipticCurve(fa-a/(1+4*a)*ha^2,ha);
    end if;
end intrinsic;

