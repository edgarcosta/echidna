// heights_fldnum.m 
// Copyright (C) 2002,2003 Martine Girard, David R. Kohel.
    
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


////////////////////////////////////////////////////////////////////
///       Heights on elliptic curves over number fields           //
//                      Martine Girard                            //
//                  girard@math.jussieu.fr                        //
//                       February 2003                            //
//                                                                //
//      Uses the paper of Silverman                               //
//      "Computing heights on elliptic curves"                    // 
//      Math Comp 51 (1988) p 339-358                             //  
//      The height we define is twice Silverman's                 //
////////////////////////////////////////////////////////////////////

import "minimal.m": ModeleLocalMinimal;

forward InfiniteHeightContribution, HauteurLocaleArchimedienne;

function DenominatorIdeal(x)
    // Input: Number field element.
    // Output: Integral denominator ideal
    O := MaximalOrder(Parent(x));
    I := ideal< O | x >;
    G := Parent(I);
    n := Denominator(I);
    J := ideal< O | Generators(n*I), n >;
    H := Parent(J);
    return H!IdealQuotient(G!ideal<O|n>,G!J);
end function;

intrinsic Hauteur(P::PtEll,prec::RngIntElt :
    Extra := 8, Multiplier := 2) -> FldReElt
    {Canonical height on a number field}
    E := Scheme(P);
    K := Ring(Parent(P));
    if P eq E(K)!0 then
	return RealField(prec)!0;
    end if;
    deg := Degree(K);
    if Type(K) eq FldRat then
        // We lose some performance in working over a number field,
        // but can apply the machineary of places.
        K := NumberField(x-1 : DoLinearExtension := true)
            where x := PolynomialRing(K).1;
        E := BaseExtend(E,K);
        P := E(K)!P;
    end if;
    require Type(K) in {FldQuad, FldCyc, FldNum} :
        "Argument 1 must be defined over a number field.";
    extra := Extra;
    RR := RealField(prec);
    RR_plus := RealField(prec+extra);
    mult := Multiplier;
    require mult ge 2 : "Parameter Multiplier must be at least 2.";
    x := P[1]; y := P[2]; 
    J := DenominatorIdeal(x);
    logdenom := Log(RR_plus!Norm(J));
    hauteurfinie := &+[ RR_plus | Degree(pp) *
        HauteurLocale(P,pp : Precision := prec+extra)  
        - Valuation(J,pp) * Log(RR_plus!Norm(Ideal(pp))) : pp in BadPlaces(E,K) ];
    hauteurinfinie := InfiniteHeightContribution(P,prec,extra,mult);
    hauteur := (logdenom + hauteurfinie + hauteurinfinie)/deg;
    return RR!hauteur;
end intrinsic;

intrinsic HauteurLocale(P::PtEll, pp::PlcNumElt :
    Extra := 0, Precision := 0, Multiplier := 2) -> FldReElt
    {Local height on a number field.}
    E := Scheme(P);
    K := Ring(Parent(P));
    if Type(K) eq FldRat then
        K := NumberField(x-1 : DoLinearExtension := true)
            where x := PolynomialRing(K).1;
        E := BaseExtend(E,K);
        P := E(K)!P;
    end if;
    require Type(K) in {FldQuad, FldCyc, FldNum} :
        "Argument 1 must be a point over a number field.";
    require K cmpeq NumberField(pp) : 
        "Argument 1 must be defined over the number field of argument 2.";
    require Type(Precision) eq RngIntElt and Precision ge 0 :
        "Parameter Precision must be an integer at least equal to 4.";
    require IsAbsoluteField(K) :
        "Argument 2 must be defined over an absolute field";
    prec := Precision;
    extra := Extra;
    RR := RealField(prec);
    mult := Multiplier;
    require mult ge 2 : "Parameter Multiplier must be at least 2.";
    EK := E(K); 
    EK`EK := EK; // to get the attribute to work
    if IsInfinite(pp) then
        x := Evaluate(P[1],pp : Precision := prec+extra);
        binvs := [ Evaluate(b,pp : Precision := prec+extra) : b in bInvariants(E)];
        if mult eq 2 then
            b2,b4,b6,b8 := Explode(binvs);
            if assigned EK`Translations then
                r1,r2 := Signature(K);
                i := SequenceToInteger([i : i in [1..r1+r2] | pp eq InfinitePlaces(K)[i]]) ;
                r0 := EK`Translations[i];
            else
                PQ := PolynomialRing(ComplexField(prec+extra)); r := PQ.1; 
                poly := 4*r^3+b2*r^2+2*b4*r+b6;
                m,e := MantissaExponent(
                    Min({Real(r[1]) : r in Roots(poly)}));
                r0 := e le 0 select -100 else
                    (Floor(m-1/2))*10^(e-Sign(m));
            end if;
            b8 +:= b2*r0^3 + 3*b4*r0^2 + 3*b6*r0 + 3*r0^4;
            b6 +:= b2*r0^2 + 2*b4*r0 + 4*r0^3;
            b4 +:= 6*r0^2 + b2*r0;
            b2 +:= 12*r0;
            binvs := [b2,b4,b6,b8];
            x -:= r0;
        end if;
        hauteur := HauteurLocaleArchimedienne(binvs,x,prec+extra,mult);
        return RR!hauteur;
    else
        // Finite place:
        vprint Hauteur : pp;
        aInv, trans := ModeleLocalMinimal(E,pp,false);
        r,s,t,u := Explode(trans);
        a1,a2,a3,a4,a6 := Explode(aInv);
        b2 := a1^2 + 4*a2;
        b4 := a1*a3 + 2*a4;
        b6 := a3^2 + 4*a6;
        b8 := a1^2*a6 - a1*a3*a4 + a2*a3^2 + 4*a2*a6 - a4^2;
        c4 := b2^2 - 24*b4;
        delta := -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6;
        vd := Valuation(K!delta,pp);
        vc4 := Valuation(K!c4,pp);
        x := u^2*P[1]+r;
        y := u^3*P[2]+u^2*s*P[1]+t;
        f2 := Valuation(K!2*y+a1*x+a3,pp);
        f3 := Valuation(K!3*x^4+b2*x^3+3*b4*x^2+3*b6*x+b8,pp);
	p := Generator(Integers() meet Ideal(pp));
	if Valuation(K!3*x^2+2*a2*x+a4-a1*y,pp) le 0 or f2 le 0 then
            vprintf Hauteur : "Non-singular reduction\n", p;
            lambda := Max(0,-Valuation(K!x,pp));
        elif vd gt 0 and vc4 eq 0 then
            vprintf Hauteur : "Multiplicative reduction\n", p;
            alpha := Min(1/2,f2/vd);
            lambda := vd * alpha * (alpha-1);
        elif vd gt 0 and vc4 gt 0 then
            vprintf Hauteur : "Additive reduction\n", p;
            lambda := (f3 ge 3*f2 select -2*f2/3 else -f3/4);
        end if;
        logp := Log(RR!p);
        return RR!(lambda + vd/6) * logp;
    end if;
end intrinsic;

function InfiniteHeightContribution(P,prec,extra,mult)
    RR := RealField(prec);
    RR_plus := RealField(prec+extra);
    CC_plus := ComplexField(prec+extra);
    E := Scheme(P);
    K := Ring(Parent(P));
    EK := E(K); 
    EK`EK := EK; // to get the attribute to work
    if Type(K) in {FldQuad,FldCyc,FldNum} then
        SetKantPrecision(K,prec+extra);
        r1,r2 := Signature(K);
        bInvs := [ Parent([CC_plus|]) | ];
        for b in bInvariants(E) do
            if b eq 0 then
                zero := 1-(1+10.0^-prec);
                Append(~bInvs,[zero : i in [1..r1+2*r2]]);
            else
                Append(~bInvs,Conjugates(K!b));
            end if;
        end for; 
        bInvs := [ Conjugates(K!b) : b in bInvariants(E)];
        xcoords := Conjugates(P[1]);
        hautinf := RR_plus!0; 
        if not assigned EK`Translations then
            EK`Translations := [];
            for i in [1..r1] cat [r1+1..r1+2*r2 by 2] do
                binvs := [ b[i] : b in bInvs ];
                b2,b4,b6,b8 := Explode(binvs);
                PQ := PolynomialRing(CC_plus); r := PQ.1; 
                poly := 4*r^3+b2*r^2+2*b4*r+b6;
                m, e := MantissaExponent(Min({Real(r[1]) : r in Roots(poly)}));
                r0 := e le 0 select -100 else (Floor(m-1/2))*10^(e-Sign(m));
                Append(~EK`Translations,r0); 
            end for;
        end if;
        for i in [1..r1] cat [r1+1..r1+2*r2 by 2] do
            j := i le r1 select i else Integers()!((i+r1+1)/2);
            vprint Hauteur : InfinitePlaces(K)[j];
            binvs := [ b[i] : b in bInvs ];
            b2,b4,b6,b8 := Explode(binvs);
            r0 := EK`Translations[j];
            b8 +:= b2*r0^3 + 3*b4*r0^2 + 3*b6*r0 + 3*r0^4;
            b6 +:= b2*r0^2 + 2*b4*r0 + 4*r0^3;
            b4 +:= 6*r0^2 + b2*r0;
            b2 +:= 12*r0;
            binvs := [b2,b4,b6,b8];
            xcoords[i] -:= r0;
            np := i gt r1 select 2 else 1;
            hautinf +:= np * HauteurLocaleArchimedienne(binvs,xcoords[i],prec,mult);
        end for;
    else // Type(K) eq FldRat
        binvs := [ RR | RR_plus!b : b in bInvariants(E) ];
        x := RR_plus!P[1];
        hautinf := HauteurLocaleArchimedienne(binvs,x,prec+extra,mult);
    end if;
    return RR!hautinf;
end function;

function zwIteration(b2,b4,b6,b8,t,r,m)
    if r ne 0 then
        b2,b4,b6,b8 := Explode([
            b2-12*r^2, b4-b2*r^2+6*r^4,
            b6-2*b4*r^2+b2*r^4-4*r^6,
            b8-3*b6*r^2+3*b4*r^4-b2*r^6+3*r^8 ]);
    end if;
    xi2 := 4+b2*t+2*b4*t^2+b6*t^3;
    if m eq 2 then
        z := 1-b4*t^2-2*b6*t^3-b8*t^4;
        w := t*xi2;
    else 
        xi := [ Parent(t) | 1, 1,
            3+b2*t+3*b4*t^2+3*b6*t^3+b8*t^4,
            2+b2*t+5*b4*t^2+10*b6*t^3+10*b8*t^4+
            (b2*b8-b4*b6)*t^5+(b4*b8-b6^2)*t^6 ];
        for n in [5..m+1] do
            k := n div 2;
            if IsOdd(n) then
                if IsOdd(k) then
                    Append(~xi,xi[k+2]*xi[k]^3-xi2^2*xi[k-1]*xi[k+1]^3);
                else
                    Append(~xi,xi2^2*xi[k+2]*xi[k]^3-xi[k-1]*xi[k+1]^3);
                end if;
            else
                Append(~xi,xi[k]*(xi[k+2]*xi[k-1]^2-xi[k-2]*xi[k+1]^2));
            end if;
        end for;
        z := IsOdd(m) select xi[m]^2-xi2*xi[m-1]*xi[m+1]
            else xi2*xi[m]^2-xi[m-1]*xi[m+1];
        w := IsOdd(m) select t*xi[m]^2 else t*xi2*xi[m]^2;
    end if;
    return z, w;
end function;

function HauteurLocaleArchimedienne(binvs,x,prec,m)
    // {Local height at an archimedean place}
    b2,b4,b6,b8 := Explode(binvs);
    disc := -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6;
    H := Max([4, Abs(b2), 2*Abs(b4), 2*Abs(b6), Abs(b8) ]);
    N := (5*prec/3+1/2+3/4*Log(7+4/3*Log(H)
        - 1/3*Log(Min(1,Abs(disc)))))/Log(2,m);
    if Abs(x) ge 1/2 then
        t := 1/x;
        r1 := 0; 
    else
        t := 1/(x+1);
        r1 := 1; 
    end if; 
    vprint Hauteur, 2 : "t :=", t;
    n := 0;
    delta := 1;
    mu := 0;
    vd := -Log(Abs(disc));
    lambda := -Log(Abs(t)) + vd/6;
    denom := 1; 
    while n lt N do
        vprint Hauteur, 2 : "n :=", n; 
        z, w := zwIteration(b2,b4,b6,b8,t,r1,m);
        abz := Abs(z); 
        abw := Abs(w); 
        denom *:= m^2;
        vprintf Hauteur, 3:
            " t = %o\n r = %o\n z = %o\n w = %o\n", t, r1, z, w;
        if abw le 2*abz then 
            r2 := r1; d := 0;
        else
            r2 := 1-r1; d := r2-r1;
        end if;
        if GetVerbose("Hauteur") ge 3 then
            initprec := RelativePrecision(t);
            "Precision(t) =", initprec;
            "Precision(z) =", RelativePrecision(abz);
            "Precision(w) =", RelativePrecision(abw);
        end if;
        t := r1 eq r2 select w/z else w/(z+(r2-r1)*w);
        delta := (r1 eq r2 select Log(abz)
            else Log(Abs(z+(r2-r1)*w)))/denom;
        if GetVerbose("Hauteur") ge 3 then
            finprec := RelativePrecision(t);
            "Precision(t) =", finprec;
            "!!! Precision loss:", initprec-finprec;
        end if;
        n +:= 1;
        r1 := r2;
        lambda +:= delta;
        vprint Hauteur, 2 : "delta =", RealField(29)!delta;
    end while;
    return lambda;
end function;
