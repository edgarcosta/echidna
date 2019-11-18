// minimal.m  computes local minimal models at a place over 2 or 3
// Copyright (C) 2002, 2003 Martine Girard.
    
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307
// USA

////////////////////////////////////////////////////////////////////////
//              Local minimal model at a place over 2 or 3            //
//                         Martine Girard                             //
//                       girard@math.jussieu.fr                       //
//                          February 2003                             //
//                                                                    //
// Compute the local minimal models for an elliptic curve at a place  //
// absolute number field                                              //
// Uses the paper of Alain Kraus "Quelques remarques a propos des     //
// invariants c_4, c_6 et delta d'une courbe elliptique",             //
// Acta Arithmetica     LIV (1989) p75-80                             //
////////////////////////////////////////////////////////////////////////


QQ := Rationals();
QN := NumberField(x-1 : DoLinearExtension := true)
            where x := PolynomialRing(QQ).1;

forward DeuxMinimal, TroisMinimal, CinqMinimal, ModeleLocalMinimal;

intrinsic LocalMinimalModels(E::CrvEll,p::RngIntElt :
    Extension := QN, PrimeDecomposition := [], Principal := false)
    -> SeqEnum
    {Local minimal models for an elliptic curve defined over an absolute
    number field at the places above p prime.}
        
    R := BaseRing(E);
    if Type(R) eq FldRat then
        R := QN;
    end if;
    require Type(R) in {FldNum, FldQuad, FldCyc} :
        "Argument 1 must be defined over a number field.";
    require IsPrime(p) :
        "Argument 2 must be prime.";
    require IsAbsoluteField(R) :
        "Argument 1 must be defined over an absolute field.";
    if Degree(Extension) eq 1 then K := R;
    else K := Extension;
        require IsSubfield(R,K) :
            "Extension must be an extension of base ring of argument 1.";
    end if;
    plcs := #PrimeDecomposition eq 0 select Decomposition(K,p)
        else PrimeDecomposition;
    return [ <LocalMinimalModel(E,pp[1]: Principal := Principal),
        Ideal(pp[1])> : pp in plcs];
end intrinsic;


intrinsic LocalMinimalModel(E::CrvEll, pp::PlcNumElt : 
    Principal := false) -> CrvEll, Map, Map
    {Local minimal model of the elliptic curve at the place pp, over an
    absolute number field.}
        
    R := BaseRing(E);
    if Type(R) eq FldRat then
        R := QN;
    end if;
    K:= NumberField(pp);
    require IsSubfield(R,K):
        "Argument 1 must be a subfield of " *
        "the number field of argument 2.";
    require IsAbsoluteField(K) :
        "Argument 2 must be a place of an absolute field.";
    EK := E(K); 
    EK`EK := EK; // to get the attribute to work

    p := Generator(Integers() meet Ideal(pp)); 

    aInv,trans:=ModeleLocalMinimal(E,pp,Principal);
    F := EllipticCurve(aInv);
    G, iso := Transformation(BaseExtend(E,K),trans);
    assert aInvariants(G) eq aInvariants(F);
    return F,iso;
end intrinsic; 

function ModeleLocalMinimal(E,pp,pcp)
    //Local minimal model of the elliptic curve at the place pp, over an
    //absolute number field.
        
    R := BaseRing(E);
    if Type(R) eq FldRat then
        R := QN;
    end if; 
    K:= NumberField(pp);
    EK := E(K); 
    EK`EK := EK; // to get the attribute to work
    
    p := Generator(Integers() meet Ideal(pp)); 
    if p eq 2 then
        if not assigned EK`MinimalModels2 then 
            aInv, trans := DeuxMinimal(E,pp,pcp);
            EK`MinimalModels2:=[<aInv,trans,Ideal(pp)>];
        else 
            bol:= exists(t,u){ <s[1],s[2]> :
                s in EK`MinimalModels2 | Place(s[3]) eq pp };
            if bol then
                aInv := t; trans := u; 
            else
                aInv, trans := DeuxMinimal(E,pp,pcp);
                EK`MinimalModels2 cat:= [<aInv,trans,Ideal(pp)>];
            end if;
        end if;
    elif p eq 3 then
        if not assigned EK`MinimalModels3 then
            aInv, trans := TroisMinimal(E,pp,pcp);
            EK`MinimalModels3:=[<aInv,trans,Ideal(pp)>];
        else 
            bol:= exists(t,u){ <s[1],s[2]> :
                s in EK`MinimalModels3 | Place(s[3]) eq pp };
            if bol then
                aInv := t; trans := u;
            else
                aInv, trans := TroisMinimal(E,pp,pcp);
                EK`MinimalModels3 cat:= [<aInv,trans,Ideal(pp)>];
            end if;
        end if;
    else  aInv, trans := CinqMinimal(E,pp,pcp);
    end if;
    return aInv, trans;
end function;

function TroisMinimal(E,pp,pcp);
    // Local minimal model of the elliptic curve at the place pp above 3.
    R := BaseRing(E);
    K := NumberField(pp);
    a1,a2,a3,a4,a6 := Explode(aInvariants(E));
    c4,c6 := Explode(cInvariants(E));
    Delta := Discriminant(E);
    vc4 := Valuation(K!c4,pp);
    vc6 := Valuation(K!c6,pp);
    e := Valuation(K!3,pp);
    vd := Valuation(K!Delta,pp);
    m := Min(vc6*2, Min(vc4*3, vd)) div 12;
    n := 0;
    x0 := 0;
    if m eq 0 then
        // print "model was already locally minimal";
        aInv := [K|a1,a2,a3,a4,a6];
        r:=0; s:=0; t:=0; u:=1;
    else
        ip := Ideal(pp);
        if pcp and IsPrincipal(ip) then
            _, pi := IsPrincipal(ip);
        else 
            pi := UniformizingElement(ip);
        end if;
        if e eq 1 then
            vprintf LocalMinimalModels, 1 :
                "3 unramified";
            if (vc6 mod 6 eq 2) then n:=1;
            elif vc6 eq 6*m then 
                x0 := -(c6/c4)/pi^(2*m);
            elif (vc6 mod 6 ge 3) then x0:=0;
            end if;
        else  
            if vc6 eq 6*m then
                // never happens if c4 = 0
                vprintf LocalMinimalModels, 1 :
                    "c6/pi^(6*m) is a unit";
                x0 := -(c6/c4)/pi^(2*m); n:=0;
            elif vc6 eq Infinity() or (vc6 mod 6 ge 3*e) then
                vprintf LocalMinimalModels, 1 :
                    "Valuation(c'6) greater than or equal to 3*e";
                x0 :=0; n:=0;
            elif (vc6 mod 3 eq 0) then
                vprintf LocalMinimalModels, 1 :
                    "0 < Valuation(c'6) < 3*e";
                n := 0; x0 := 0; 
                K3,phi := Completion(K,ip);
                while 6*n lt (3*e - vc6 + 6*m) do
                    l := (vc6-6*(m-n)) div 3;
                    R3 := ChangePrecision(Integers(K3),3*(e-l));
                    PR3<x> := PolynomialRing(R3);
                    bol,x0 := HasResidualRoot(x^3 -
                        3*R3!phi(c4/pi^(4*(m-n)+2*l))*x - 
                        2*R3!phi(c6/pi^(6*(m-n)+3*l)),3*(e-l));  
                    if bol then x0 *:= phi(pi^l); break;
                    end if;
                    n +:= 1;
                end while;
                x0 := x0 @@ phi;
            end if;
        end if;
        if n eq m then
            aInv := [K|a1,a2,a3,a4,a6];
            r:=0; s:=0; t:=0; u:=1;
        else
            a := c4/pi^(4*(m-n));
            b := c6/pi^(6*(m-n));
            aInv := [0,x0,0,(x0^2-a)/3,(x0^3-3*x0*a-2*b)/27];
            v := 1/pi^(m-n);
            s := a1*v;
            r := ((a1^2+4*a2)*v^2 - x0)/3;
            t := 4*a3*v^3;
            u := 2*v;
        end if;
    end if;
    return aInv, [r,s,t,u];
end function;

function DeuxMinimal(E,pp,pcp);
    //Local minimal model of the elliptic curve at the place pp above 2
    R := BaseRing(E);
    K := NumberField(pp);
    d := AbsoluteDegree(K);
    a1,a2,a3,a4,a6 := Explode(aInvariants(E));
    c4,c6 := Explode(cInvariants(E));
    Delta := Discriminant(E);
    vc4 := Valuation(K!c4,pp);
    vc6 := Valuation(K!c6,pp);
    e := Valuation(K!2,pp);
    vd := Valuation(K!Delta,pp);
    m := Min(vc6*2, Min(vc4*3, vd)) div 12;
    n0:=0;
    vprint LocalMinimalModels, 1 : pp;
    if m eq 0 then
        vprintf LocalMinimalModels, 1 :
            "Model was already locally minimal \n";
        aInv := [K|a1,a2,a3,a4,a6];
        r:=0; s:=0; t:=0; u:=1;
    else
        ip := Ideal(pp);
        if pcp and IsPrincipal(ip) then 
            _, pi := IsPrincipal(ip);
        else 
            pi := UniformizingElement(ip);
        end if;
        K2,phi := Completion(K,ip : Precision := Max(60,4*d));
        // too much precision to make completion work
        vprint LocalMinimalModels, 1 :K2;
        if (vc4 eq 4*m) then
            vprintf LocalMinimalModels, 1 :
                "Valuation(c'4) equal to 4*m \n";
            R2 := ChangePrecision(Integers(K2),2*e);
            PR2<x>:=PolynomialRing(R2);
            bol,x0:=HasResidualRoot(x^2+R2!phi(c6/pi^(6*m)),2*e);
            if bol then n:=0;
                x1 := K2!(phi(c4/pi^(4*m))/x0);
                u := K2!(phi(c6/pi^(6*m))+x1^6)/4;
                x2 := K2!(u/x1^3);
            end if;
        end if;
        if (vc4 ne 4*m) or not bol then
            for n in [0..m] do
                vprintf LocalMinimalModels, 1 : "n = %o \n",n;
                if (vc4-4*m+4*n ge 4*e) then
                    vprintf LocalMinimalModels, 1 :
                    "Valuation(c'4) greater than or equal to 4*e \n";
                    R2:=ChangePrecision(Integers(K2),5*e);
                    PR2<x>:=PolynomialRing(R2);
                    vprint LocalMinimalModels, 1 : R2;
                    vprint LocalMinimalModels, 1 : 
                        x^2-R2!phi(c6/pi^(6*(m-n))/8); 
                    vprint LocalMinimalModels, 1 : "valuation of 2", e;
                    bol,x2:= HasResidualRoot(
                        x^2-R2!phi(c6/pi^(6*(m-n))/8),2*e);
                    if bol then
                        n0:=n;
                        x1:=0;
                        break n;
                    end if;
                else
                    if (e gt 1) and (vc4 mod 4 eq 0)
                        and (vc4-4*m+4*n lt 4*e)
                        and (vc4-4*m+4*n gt 0) then
                        vprintf LocalMinimalModels, 1 :
                        "Valuation(c'4) smaller than 4*e \n";  
                        l := (vc4-4*(m-n)) div 4;
                        R2:=ChangePrecision(Integers(K2),8*(e-l)); 
                        vprint LocalMinimalModels, 1 : R2;
                        PR2<x>:=PolynomialRing(R2);
                        poly := 5*x^4 - 14*R2!phi(c4/pi^(4*(m-n+l)))*x^2 -
                            R2!(8*phi(c6/pi^(6*(m-n+l))))*x +
                            R2!phi(c4/pi^(4*(m-n+l)))^2;
                        vprint LocalMinimalModels, 1 : poly;
                         
                        if 6*l ge 4*e then //second condition always holds
                            vprint LocalMinimalModels, 1 : 
                                "Computing roots to precision", 8*(e-l);
                            sol := ResidualRoots(poly,8*(e-l));
                        else // Valuation(c'6) greater than 6*l
                            vprintf LocalMinimalModels, 1 : 
                                "Computing roots to precisions " *
                                "%o and %o \n", 8*(e-l),4*e-6*l;
                            sol := ResidualRoots(
                                [poly,
                                x^3 - 3*R2!phi(c4/pi^(4*(m-n+l)))*x -
                                R2!(2*phi(c6/pi^(6*(m-n+l))))
                                ],
                                [
                                8*(e-l),
                                4*e-6*l
                                ]);
                        end if;
                        vprint LocalMinimalModels, 1 : 
                            "Looking for a square";
                        for x0 in sol do 
                            bol,xx0:= HasResidualRoot(x0-x^2,8*(e-l));
                            if bol then n0:=n;
                                vprint LocalMinimalModels, 1 : 
                                    "Looking for x2";   
                                poly0 := x^3 - R2!phi(3*c4/pi^(4*(m-n)))*x
                                    - 2*R2!phi(c6/pi^(6*(m-n)));
                                poly1 := R2!(Evaluate(poly0,
                                    R2!(x0*R2!phi(pi^(2*l)))));  
                                bol,x2:=HasResidualRoot(poly1+16*x^2,6*e);
                                if bol then x1 := phi((xx0 @@ phi)*pi^l);
                                    break n;
                                end if;
                            end if;
                        end for;
                    end if;
                end if;
            end for;
        end if;
        v := 1/pi^(m-n0);
        a := c4/pi^(4*(m-n0));
        b := c6/pi^(6*(m-n0));
        x1 := (x1 @@ phi);
        x2 := x2 @@ phi;
        x3 := Valuation(x1^4-a-24*x1*x2,pp) gt 4*e select x2 else -x2;
        x4 := (x1^4-a-24*x1*x3)/48;
        x6 := (- b - x1^6+36*x1^2*(x1*x3+2*x4))/216/4-x3^2/4;
        if Valuation(Rationals()!Norm(x4),3) ge 0 and
            Valuation(Rationals()!Norm(x6),3) ge 0 then 
            aInv := [x1,0,x3,x4,x6];
            s := (a1*v-x1)/2;
            r := (a1^2*v^2+4*a2*v^2-x1^2)/12;
            t := (-a1^2*v^2*x1-4*a2*v^2*x1+12*a3*v^3+x1^3-12*x3)/24;
            u := v ;
        else
            aInv := [3*x1,0,27*x3,81*x4,27^2*x6];
            s := 3/2*(a1*v-x1);
            r := 3/4*(a1^2*v^2+4*a2*v^2-x1^2);
            t := 9/8*(-a1^2*v^2*x1-4*a2*v^2*x1+12*a3*v^3+x1^3-12*x3);
            u := 3*v;
        end if;
    end if;
    return  aInv, [r,s,t,u];
end function;


function CinqMinimal(E,pp,pcp);
    //Local minimal model of the elliptic curve at a place pp above a
    //prime greater than 3
    R := BaseRing(E);
    K := NumberField(pp);

    a1,a2,a3,a4,a6 := Explode(aInvariants(E));
    c4,c6 := Explode(cInvariants(E));
    Delta := Discriminant(E);
    vd := Valuation(K!Delta,pp);
    vc4 := Valuation(K!c4,pp);
    m := Min(vd , 3*vc4 ) div 12 ;
    if m eq 0 then
        aInv:=[K|a1,a2,a3,a4,a6];
        r:=0;s:=0;t:=0;u:=1;
    else
        ip := Ideal(pp);
        if pcp and IsPrincipal(ip) then
            _, pi := IsPrincipal(ip);
        else 
            pi := UniformizingElement(ip);
        end if;
        aInv:= [K|0,0,0,-27*c4/pi^(4*m),-54*c6/pi^(6*m)];
        v:=1/pi^m;
        s:=3*a1*v;
        r:=3*a1^2*v^2 + 12*a2*v^2;
        t:=108*a3*v^3;
        u:=6*v;
    end if;
    return aInv, [r,s,t,u];
end function;
