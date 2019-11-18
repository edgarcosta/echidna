////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      ELLIPTIC MODULAR ISOGENIES                    //
//                             David Kohel                            //
//                           September 2000                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "lercier.m" : Lercier;
import "elkies.m" : ElkiesKernel;
import "velu_isogenies.m" : VeluRecursion;

forward AtkinCodomainCurve, AtkinIsogeny;
forward ClassicalCodomainCurve, ClassicalIsogeny;
forward CanonicalIsogeny, DefaultIsogeny;

////////////////////////////////////////////////////////////////////////
//                 MODULI POINTS FOR ELLIPTIC CURVES                  //
////////////////////////////////////////////////////////////////////////
 
intrinsic ModuliPoints(X::CrvMod,E::CrvEll) -> SeqEnum 
    {Returns the sequence of points on X specifying isogenies  
    of the elliptic curve E over its base field.} 

    require Indices(X)[[2,3]] eq [1,1] :
        "Argument 1 must be a modular curve of type X_0(N).";
    require CanChangeUniverse([BaseRing(X)|],BaseRing(E)) :
        "Base ring of arguments are incompatible.";
    if ModelType(X) in {"Atkin","Canonical","Classical"} then
	j := jInvariant(E);
	P := PolynomialRing(BaseRing(E)); x := P.1;
	f := Evaluate(Polynomial(X),[x,j]);
	return [ X ! [x[1],j] : x in Roots(f) ];
    elif ModelType(X) eq "Default" then
	j := jInvariant(E);
	PP, mj := ModularQuotient(X,[1,1,1]); 
	return [ X!P : P in RationalPoints((PP![j,j,1])@@mj) ];
    end if;
    require false :
	"Argument 1 must be modular curve of recognized type.";
end intrinsic; 
 
intrinsic ModularQuotient(X,M::[RngIntElt]) -> CrvMod, MapSch
    {The quotient curve X(M), following by the scheme map.}
    i := Index(X`QuotientLevels,M cat [1]);
    require i ne 0 :
	"Argument 2 does not specify a known quotient of argument 1.";
    Y := ModularCurve(ModularCurveDatabase(),M);
    return Y, map< X->Y | X`QuotientImages[i] >;
end intrinsic;

intrinsic ModularQuotient(X,M::[RngIntElt],m::RngIntElt) -> CrvMod, MapSch
    {The quotient curve X(M), following by the scheme map.}
    i := Index(X`QuotientLevels,M cat [m]);
    require i ne 0 :
	"Argument 2 does not specify a known quotient of argument 1.";
    Y := ModularCurve(ModularCurveDatabase(),M);
    return Y, map< X->Y | X`QuotientImages[i] >;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                    MODULAR KERNEL POLYNOMIALS                      //
////////////////////////////////////////////////////////////////////////
 
/*
intrinsic KernelPolynomial(X::CrvMod) -> RngUPolElt
   {The kernel polynomial for the elliptic surface over X.}

   K := FunctionField(X); 
   u := K.1; v := K.2; 
   if assigned X`ModularInvariants then
      return PolynomialRing(K) ! [ 
         Evaluate(c[1],[u,v])/Evaluate(c[2],[u,v]) : 
            c in X`ModularInvariants ];
   end if;
   ell := Level(X);
   e2 := EisensteinFunction(X,2);
   e4 := EisensteinFunction(X,4);
   e6 := EisensteinFunction(X,6);
   f4 := EisensteinFunction(X,4,-1);
   f6 := EisensteinFunction(X,6,-1);
   P := PolynomialRing(Parent(e2));
   return P!(Reverse(VeluRecursion(e2,e4,e6,f4,f6,ell)) cat [1]);   
end intrinsic;

intrinsic KernelPolynomial(X::CrvMod,R::Fld) -> RngUPolElt
   {The kernel polynomial for the elliptic surface over X
   base extended to the field R.}

   if assigned X`ModularInvariants then
      K := FunctionField(X,R); 
      u := K.1; v := K.2; 
      return PolynomialRing(K) ! [ 
         Evaluate(c[1],[u,v])/Evaluate(c[2],[u,v]) : 
            c in X`ModularInvariants ];
   end if;
   l := Level(X);
   e2 := EisensteinFunction(X,R,2);
   e4 := EisensteinFunction(X,R,4);
   e6 := EisensteinFunction(X,R,6);
   f4 := EisensteinFunction(X,R,4,-1);
   f6 := EisensteinFunction(X,R,6,-1);
   P := PolynomialRing(Parent(e2)); x := P.1;
   n := l div 2;
   S := VeluRecursion(e2,e4,e6,f4,f6,l);
   return x^n + &+[ (-1)^i*S[i]*x^(n-i) : i in [1..n] ];
end intrinsic;

intrinsic KernelPolynomial(E::CrvEll,P::Pt) -> RngUPolElt
   {The kernel polynomial for an isogeny E -> F defined 
   by the point P on the modular curve X_0(N).}

   X0 := Scheme(P);
   require Type(X0) eq CrvMod :
      "Argument 2 must be a point on a modular curve.";
   R := BaseRing(E);
   require Characteristic(R) notin {2,3} : 
      "Base characteristic of argument 1 must be " *
      "different from 2 and 3.";
   require jInvariant(E) notin {BaseRing(E)|0,12^3} :
      "Argument 1 must have j-invariant different " *
      "from 0 and 12^3.";

   a1, a2 := Explode(aInvariants(E));
   c2 := (a1^2+4*a2)/12;
   c4, c6 := Explode(cInvariants(E));
   e4 := EisensteinFunction(P,4);
   e6 := EisensteinFunction(P,6);
   X := Scheme(P);
   PR := PolynomialRing(Universe(Eltseq(P))); x := PR.1;
   if assigned X0`ModularInvariants then
      f := PR![ Evaluate(c[1],S)/Evaluate(c[2],S) 
                 : c in X0`ModularInvariants ] where S is Eltseq(P);
   else 
      l := Level(X);
      n := l div 2;
      e2 := EisensteinFunction(P,2);
      f4 := EisensteinFunction(P,4,-1);
      f6 := EisensteinFunction(P,6,-1);
      si := VeluRecursion(e2,e4,e6,f4,f6,l);
      f := x^n + &+[ (-1)^i*si[i]*x^(n-i) : i in [1..n] ];
   end if;
   mu := (e4*c6)/(c4*e6);
   return mu^Degree(f)*Evaluate(f,(x+c2)/mu);
end intrinsic;
*/

////////////////////////////////////////////////////////////////////////
//                       MODULAR ISOGENIES                            //
////////////////////////////////////////////////////////////////////////
 
intrinsic Isogeny(E::CrvEll,P::Pt) -> MapCrvEll 
    {Returns the isogeny E -> F corresponding to the point P on the
    modular curve X_0(N).}

    X0 := Scheme(P);
    type := ModelType(X0);
    K := BaseRing(E);
    require Characteristic(K) notin {2,3} :
        "Argument 1 must not have base characteristic 2 or 3.";
    require K cmpeq Universe(Eltseq(P)) :
	"Arguments have incompatible base rings.";
    require Type(X0) eq CrvMod and not IsSingular(P) :
        "Argument 2 must be a nonsingular point on a modular curve.";
    require Indices(X0)[2..3] eq [1,1] :
	"The parent of argument 2 must be a modular curve of type X_0(N).";
    require type in {"Atkin","Canonical","Classical","Default"} :
        "Model type of parent of argument 2 must be \"Atkin\", " *
        "\"Canonical\", \"Classical\", or \"Default\".";
    if type eq "Atkin" then
	return AtkinIsogeny(E,P);
    elif type eq "Canonical" then
	return CanonicalIsogeny(E,P);
    elif type eq "Classical" then
	return ClassicalIsogeny(E,P);
    else
	return DefaultIsogeny(E,P);
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                     ATKIN MODULAR ISOGENIES                        //
////////////////////////////////////////////////////////////////////////

function AtkinIsogeny(E,P)
   // The curve defined by the Velu isogeny of E defined by P.

   X0 := Scheme(P);
   u, j := Explode(Eltseq(P));
   error if jInvariant(E) ne j, "Argument 1 and 2 are inconsistent.";

   K := BaseRing(E);
   error if Characteristic(K) in {2,3}, "Argument 1 must be defined
       over a field of characteristic other than 2 or 3.";
   p := Level(X0);
   PK := PolynomialRing(K);
   if p eq 2 then
       if u eq -23 then
	   error if j eq -15^3,
	       "Failed codomain isomorphism in Atkin model isogeny (D = -7).";
	   assert j eq -15^3; // don't arrive here.
       elif u eq 544 then
	   error if j eq 12^3,
	       "Failed codomain isomorphism in Atkin model isogeny (D = -4).";
	   error if j eq 287496,
	       "Failed codomain isomorphism in Atkin model isogeny (D = -16).";
	   assert j eq 12^3 or j eq 287496; // don't arrive here.
       end if;
       x := PK.1; 
       A := 1/(4*(u - 544)*(u + 23));
       c := (j-12^3)^-1;
       if Eltseq(E) eq [1,0,0,-36*c,-1*c] then
	   // Magma default constructor from j-invariant
	   E1 := E;
	   PP := AmbientSpace(E);
	   m0 := map< E->E | [PP.i : i in [1..3] ] >;
	   psi := x - A*(j - (u^2 - 8*u - 4088));
       else
	   cc := j/(j-12^3);
	   c4, c6 := Explode(cInvariants(E));
	   // [ lam^2*c4, lam^3*c6] = [cc, -cc];
	   lam := -c6/c4;
	   E1 := EllipticCurve([1,(lam-1)/4,0,-36*cc/j*lam^2,-cc/j*lam^3]);
	   bool, m0 := IsIsomorphic(E,E1); assert bool;
	   psi := x - A*lam*(j - (u^2 - 8*u - 4088));
       end if;
       F1, m1 := IsogenyFromKernel(E1,psi);
       return m0*m1;
   end if;
   E1, m1 := WeierstrassModel(E);
   a1,a2,a3,a4,a6 := Explode(aInvariants(E1));
   Phi := DefiningPolynomial(X0);
   J := PK.1;
   f := Evaluate(Phi,[u,J]) div (J-j);
   jCandidates := [ r[1] : r in Roots(f) ];
   vprint ModularCurve :
      "Candidate j-invariants of codomain curve:", jCandidates;
    for j_tilde in jCandidates do
	vprint ModularCurve : "Trying j-invariant", j_tilde;
	F1, p1, success := AtkinCodomainCurve(E1,p,Phi,u,j_tilde);
	if success then
	    psi, success := ElkiesKernel(E1,F1,p,p1);
	end if;
	if success then
	    vprint ModularCurve : "Correct involution image j-invariant";
	    break;
	else
	    vprint ModularCurve : "Computing with alternate j-invariant.";
	end if;
    end for;
    error if not success, "Failed to find isogeny for Atkin model.";
    F2, m0 := IsogenyFromKernel(E1,psi);
    if F1 ne F2 then
	bool, m2 := IsIsomorphic(F2,F1);
	error if not bool,
	    "Failed codomain isomorphism in Atkin model isogeny.";
	F2 := F1;
        m0 := m0*m2;
    end if;
    i2 := IsomorphismData(Inverse(m1));
    _, m2 := Transformation(F2,i2);
    return m1*m0*m2;
end function;

function AtkinCodomainCurve(E,p,Phi,u,j_tilde)
    // The isogeous curve F, and the sum of the x-coordinates 
    // of the points in the kernel of the isogeny E -> F
 
    j := jInvariant(E);
    s := 12 div GCD(12, p-1);
    _, _, _, e4, e6 := Explode(Coefficients(E));

    E4 := -e4 / 3;       // set lambda = 1
    E6 := -e6 / 2;       // set lambda = 1

    P2 := Parent(Phi);
    U := P2.1; J := P2.2;

    DuPhi := Derivative(Phi, U);
    DuuPhi := Derivative(DuPhi, U);
    DjPhi := Derivative(Phi, J);
    DjjPhi := Derivative(DjPhi, J);
    DujPhi := Derivative(DjPhi, U);

    Du := u * Evaluate(DuPhi, [u,j]);
    DuStar := u * Evaluate(DuPhi, [u,j_tilde]);
    Dj := j * Evaluate(DjPhi, [u,j]);
    DjStar := p * j_tilde * Evaluate(DjPhi, [u,j_tilde]);

    error if Du eq 0 or E4 eq 0,
	"Argument 2 is represents a singular point of modular curve model.";

	
    u_prime := (u * E6 * Dj) / (E4 * Du);

    // This is clearly an invalid state, so return.
    if DjStar eq 0 then
	return E, 0, false;
    end if;
    
    E4_tilde := (DuStar^2 * Dj^2 * E6^2 * j_tilde) /
		(DjStar^2 * Du^2 * E4^2 * (j_tilde - 1728));
    E6_tilde := (DuStar^3 * Dj^3 * E6^3 * j_tilde) /
		(DjStar^3 * Du^3 * E4^3 * (j_tilde - 1728));

    a_tilde := -3 * p^4 * E4_tilde;
    b_tilde := -2 * p^6 * E6_tilde;

    F := EllipticCurve([a_tilde,b_tilde]);

    pu := Evaluate(DuPhi, [u,j]);
    pj := Evaluate(DjPhi, [u,j]);
    puStar := Evaluate(DuPhi, [u,j_tilde]);
    pjStar := Evaluate(DjPhi, [u,j_tilde]);

    u1 := (1/pu) * 
	  ( - u_prime * Evaluate(DuuPhi, [u,j])
            + 2 * j * Evaluate(DujPhi, [u,j]) * E6 / E4
            - ( E6^2 / (u_prime * E4^2))
            *  ( j * pj  + j^2 * Evaluate(DjjPhi, [u,j]) ) )
          +  (E6 / (3 * E4)) - (E4^2 / (2 * E6));
    u2 := (1/puStar) * 
	  ( - u_prime * Evaluate(DuuPhi, [u,j_tilde])
            + 2 * p * j_tilde * Evaluate(DujPhi, [u,j_tilde]) 
              * E6_tilde / E4_tilde
            - p^2 * (E6_tilde^2 / (u_prime * E4_tilde^2)) 
	      * (j_tilde * pjStar + j_tilde^2 
              * Evaluate(DjjPhi, [u,j_tilde]) ) )
            + p * ( E6_tilde / (3 * E4_tilde)
	            - E4_tilde^2 / (2 * E6_tilde) );
   p1 := (u1 - u2) * 6 * p / 2; 
   return F, p1, true;
end function;

////////////////////////////////////////////////////////////////////////
//                   CANONICAL MODULAR ISOGENIES                      //
////////////////////////////////////////////////////////////////////////

function CanonicalIsogeny(E,P)
    // The Velu isogeny of E defined by P.

    K := BaseRing(E);
    error if Characteristic(K) in {2,3}, "Argument 1 must be defined
	over a field of characteristic other than 2 or 3.";

    E1, m1 := WeierstrassModel(E);
    _, _, _, a4, a6 := Explode(aInvariants(E1));

    X0 := Scheme(P);
    N := Level(X0);
    P2 := PolynomialRing(K,2);
    U := P2.1; J := P2.2;
    Psi := P2!Polynomial(X0);   
    u, j := Explode(Eltseq(P));

    error if jInvariant(E) ne j, "Argument 1 and 2 are inconsistent.";

    s := 12 div GCD(12, N-1);
    u_tilde := N^s / u; // Canonical involution.

    // Not reached -- this should determine the correct isogeny.
    if Characteristic(K) eq 2 then
	P := PolynomialRing(K); x := P.1;
	rts := Roots(Evaluate(Psi,[u_tilde,x]));
	for j_tilde in rts do
	    F := EllipticCurve(j_tilde[1]);
	    bool, psi := Lercier(E,F,N);
	    if bool then break; end if;
	end for;
	error if not bool, "No kernel polynomial found in Lercier.";
	_, m := IsogenyFromKernel(E,psi);
	return m;
    end if;
	
    DuPsi := Derivative(Psi, U);
    DuuPsi := u^2 * Derivative(DuPsi, U);
    DjPsi := Derivative(Psi, J);
    DujPsi := u * j * Derivative(DjPsi, U);
    DjjPsi := j^2 * Derivative(DjPsi, J);

    Du := u * Evaluate(DuPsi, [u,j]);
    Dj := j * Evaluate(DjPsi, [u,j]);
    Duu := Du + Evaluate(DuuPsi, [u,j]);
    Duj := Evaluate(DujPsi, [u,j]);
    Djj := Dj + Evaluate(DjjPsi, [u,j]);

    _, _, _, a4, a6 := Explode(Coefficients(E1));
    E4 := -a4 / 3; // set lambda = 1
    E6 := -a6 / 2; // set lambda = 1

    error if Du eq 0 or E4 eq 0,
        "Argument 1 is a singular point on the parent of argument 2.";

    E4_tilde := ( E4 
        + ( (144 * Dj^2 * E6^2) / (s^2 * Du^2 * E4^2) ) 
	- ( (48 * Dj * E6^2) / (s * Du * E4^2) ) 
	- ( (288 * Dj * Duj * E6^2) / (s * Du^2 * E4^2) ) 
        + ( (144 * Djj * E6^2) / (s * Du * E4^2) ) 
        + ( (72 * Dj * E4) / (s * Du) ) 
        + ( (144 * Dj^2 * Duu * E6^2) / (s * Du^3 * E4^2) )
    ) / N^2;
    Delta := (E4^3 - E6^2)/1728;
    Delta_tilde := u^(12 div s) * Delta / N^12;

    j_tilde := E4_tilde^3 / Delta_tilde;
    E6_tilde := (-E4_tilde) * ( u_tilde 
        * Evaluate(DuPsi, [u_tilde,j_tilde]) * Dj * E6 ) /
        ( N * j_tilde * Evaluate(DjPsi, [u_tilde,j_tilde]) * Du * E4 );

    a_tilde := -3 * N^4 * E4_tilde;
    b_tilde := -2 * N^6 * E6_tilde;

    F1 := EllipticCurve([a_tilde, b_tilde]);

    if N eq 2 then
	p1 := (12*N*E6*Dj)/(s*E4*Du); 
    else
	p1 := (6*N*E6*Dj)/(s*E4*Du); 
    end if;
    
    psi := ElkiesKernel(E1,F1,N,p1);
    F2, m0 := IsogenyFromKernel(E1,psi);
    if F1 ne F2 then
	bool, m2 := IsIsomorphic(F2,F1);
	error if not bool,
	    "Failed codomain isomorphism in canonical model isogeny.";
	F2 := F1;
        m0 := m0*m2;
    end if;
    i2 := IsomorphismData(Inverse(m1));
    _, m2 := Transformation(F2,i2);
    return m1*m0*m2;
end function;

////////////////////////////////////////////////////////////////////////
//                   CLASSICAL MODULAR ISOGENIES                      //
////////////////////////////////////////////////////////////////////////

function ClassicalIsogeny(E,P)
    // The Velu isogeny of E defined by P.

    X0 := Scheme(P);
    p := Level(X0);
    Phi := Polynomial(X0);
    j_p, j := Explode(Eltseq(P));
    error if jInvariant(E) ne j, "Argument 1 and 2 are inconsistent.";
    K := BaseRing(E);
    error if Characteristic(K) in {2,3}, "Argument 1 must be defined
	over a field of characteristic other than 2 or 3.";

    E1, m1 := WeierstrassModel(E);
    _, _, _, a4, a6 := Explode(aInvariants(E1));

    // Not reached -- this should determine the correct isogeny.
    if Characteristic(K) eq 2 then
	F := EllipticCurve(j_p);
	bool, psi := Lercier(E,F,p);
	error if not bool, "Failed to find kernel polynomial in Lercier.";
	F, m := IsogenyFromKernel(E,psi);
	return m;
    end if;
    E4, E6 := Explode(cInvariants(E));
    error if j eq 0,
	"Domain curve must not have j-invariant 0.";
    error if j eq 12^3,
	"Domain curve must not have j-invariant 12^3.";
    error if j_p eq 0,
	"Codomain curve must not have j-invariant 0.";
    error if j_p eq 12^3,
	"Codomain curve must not have j-invariant 12^3.";
    error if Characteristic(BaseRing(E)) in {2,3},
	"Argument 1 must be defined over a field " *
	"of characteristic different from 2 and 3.";

    P2 := Parent(Phi); X := P2.1; Y := P2.2;
    DxPhi := Derivative(Phi, X);

    DxPhiJJ := Evaluate(DxPhi, [j,j_p]);
    DyPhiJJ := Evaluate(DxPhi, [j_p,j]);
    error if DyPhiJJ eq 0,
        "Argument 1 must not be a singularity of curve model.";

    j_prime := -E6*j/E4;
    j_p_prime := -j_prime*DxPhiJJ/(p*DyPhiJJ);
	
    lambda := -j_p_prime/j_p;
    E4_p := lambda^2*j_p/(j_p-12^3);
    E6_p := lambda*E4_p;

    DxxPhi := Derivative(DxPhi, X);
    DxyPhi := Derivative(DxPhi, Y);

    DxxPhiJJ := Evaluate(DxxPhi, [j,j_p]);
    DxyPhiJJ := Evaluate(DxyPhi, [j,j_p]);
    DyyPhiJJ := Evaluate(DxxPhi, [j_p,j]);

    j_pp := -( j_prime^2*DxxPhiJJ +
               2*p*j_prime*j_p_prime*DxyPhiJJ +
               p^2*j_p_prime^2*DyyPhiJJ ) / (j_prime*DxPhiJJ);
    c2 := 6*j_pp + (3*E4^3 + 4*E6^2)/(E4*E6) 
	         - p * (3*E4_p^3 + 4*E6_p^2)/(E4_p*E6_p);
		  
    F1 := EllipticCurve([-p^4*E4_p/48,-p^6*E6_p/864]);

    if p ne 2 then
	psi, bool := ElkiesKernel(E1,F1,p,-p*c2/24);
	error if not bool, "Failure in Elkies kernel.";
    else
	psi := PolynomialRing(K)![p*c2/12,1];
    end if;

    F2, m0 := IsogenyFromKernel(E1,psi);
    if F1 ne F2 then
	bool, m2 := IsIsomorphic(F2,F1);
	error if not bool,
	    "Failed codomain isomorphism in classical model isogeny.";
	F2 := F1;
        m0 := m0*m2;
    end if;
    i2 := IsomorphismData(Inverse(m1));
    _, m2 := Transformation(F2,i2);
    return m1*m0*m2;
end function;

////////////////////////////////////////////////////////////////////////
//                     DEFAULT MODULAR ISOGENIES                      //
////////////////////////////////////////////////////////////////////////

function DefaultIsogeny(E,P)
    assert false;
end function;
