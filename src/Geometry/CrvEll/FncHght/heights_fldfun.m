// heights_fldfun.m 
// Copyright (C) 2001 Martine Girard.
    
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
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
// USA


////////////////////////////////////////////////////////////////////
///       Heights on elliptic curves over function fields         //
//                       Martine Girard                           //
//                    girard@math.jussieu.fr                      //
//                       November 2001                            //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic Hauteur(P::PtEll : Precision := 20) -> FldElt
    {Hauteur globale sur un corps de fonctions ou corps de nombres.}

    E := Scheme(P);
    if Type(BaseRing(E)) in {FldRat,FldQuad,FldCyc,FldNum} then
        return Hauteur(P,Precision);
    end if;
    require Type(BaseRing(E)) in {FldFun,FldFunRat} :
        "Scheme of argument must be defined over " *
        "number field or function field.";  
    if P eq E!0 then return Rationals()!0; end if;
    poles := (P[1] eq 0) select [] else Poles(P[1]);    
    places := SequenceToSet(Poles(Discriminant(E)) cat  
    Zeroes(Discriminant(E)) cat poles)  ;
    hauteur := &+[Rationals() | 
                    Degree(p)*HauteurLocale(P,p) : p in places]; 
    return hauteur;
end intrinsic;


intrinsic HauteurLocale(P::PtEll, p::PlcFunElt) -> FldRatElt
    {Hauteur locale sur un corps de fonctions}
    E := Scheme(P);
    require Type(BaseRing(E)) in {FldFun,FldFunRat} :
       "Scheme of argument must be defined over a function field.";  
    require FunctionField(p) eq BaseRing(E) :
        "Function field of argument 2 must be the " *
        "base ring of the curve of argument 1.";
    a1,a2,a3,a4,a6:=Explode(aInvariants(E));
    b2,b4,b6,b8:=Explode(bInvariants(E));
    c4,_:=Explode(cInvariants(E));
    Delta:=Discriminant(E);
    x:=P[1]; y:=P[2];
    c:=Sign(Valuation(Delta,p))*Abs(Floor(Valuation(Delta,p)/12));
    vd:=Valuation(Delta,p)-12*c;
    f2:=Valuation(2*y+a1*x+a3,p)-3*c;
    f3:=Valuation(3*x^4+b2*x^3+3*b4*x^2+3*b6*x+b8,p)-8*c;
    if Valuation(3*x^2+2*a2*x+a4-a1*y,p)-4*c le 0 or f2 le 0 then
        vprint Hauteur : "Reduction nonsinguliere";
        lambda := Max(0,-Valuation(x,p)+2*c) + vd/6;
    elif vd gt 0 and Valuation(c4,p)-4*c eq 0 then
        vprint Hauteur : "Reduction multiplicative";    
        alpha := Min(1/2,f2/vd);
        lambda := vd*(alpha^2-alpha+1/6);
    elif vd gt 0 and Valuation(c4,p)-4*c gt 0 then
        vprint Hauteur : "Reduction additive";
        lambda:= (f3 ge 3*f2 ) select -2*f2/3+vd/6
            else -f3/4 +vd/6; 
    end if;
    return lambda;
end intrinsic;


function HauteurNaive(P) 
     x:=P[1];n:=Degree(Numerator(x));d:=Degree(Denominator(x));
     return Max(n,d);
end function;
