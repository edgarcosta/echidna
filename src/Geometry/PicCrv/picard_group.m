//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                       Picard Groups of Curves                            //
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

declare verbose PicardGroup, 2;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Attribute declarations                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare type PicCrv[PicCrvElt];

declare attributes PicCrv:  // Picard group
    Curve,                  // Nonsingular curve
    Place;                  // Degree one place for divisor reduction

declare attributes PicCrvElt:
    Parent,
    Element;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            Coercions                               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function PicCrvCreate(J,D)
    P := New(PicCrvElt);
    P`Parent := J;
    P`Element := D + r*O
        where D, r := Reduction(D,O)
        where O := Parent(P)`Place;
    return P;
end function;

intrinsic IsCoercible(J::PicCrv,P::.) -> BoolElt, PicCrvElt
    {}
    if Parent(P) cmpeq J then
        return true, P;
    elif Type(P) eq RngIntElt then
        if P eq 0 then
            K := AlgorithmicFunctionField(FunctionField(J`Curve));
            return true, PicCrvCreate(J,DivisorGroup(K)!0);
        end if;
    elif ISA(Type(P),Pt) then
        if Scheme(P) ne Curve(J) then
            return false, "Argument 2 must be on curve of argument 1.";
        elif Ring(Parent(P)) ne BaseRing(Curve(J)) then
            return false,
                "Argument 2 must be a rational point of curve.";
        end if;
        O := ReductionDivisor(J);
        if IsNonsingular(P) then
            P := FunctionFieldPlace(Place(P));
            return true, PicCrvCreate(J,P-O);
        else
            plcs := Places(P);
            vals := &+[ Valuation(P,p) : p in plcs ];
            plcs := [ FunctionFieldPlace(p) : p in plcs ];
            D := &+[ vals[i]*plcs[i] : i in [1..#plcs]] - (&+vals)*O;
        end if;
    elif Type(P) eq PlcCrvElt then
        if Curve(P) ne Curve(J) then
            return false, "Argument 2 must be on curve of argument 1.";
        end if;
        D := 1*FunctionFieldPlace(P) - Degree(P)*ReductionDivisor(J);
    elif Type(P) eq PlcFunElt then
        if FunctionField(P) ne AlgorithmicFunctionField(FunctionField(Curve(J))) then
            return false, "Argument 2 must be on curve of argument 1.";
        end if;
        D := P - Degree(P)*ReductionDivisor(J);
    elif Type(P) eq DivCrvElt then
        if Curve(P) ne Curve(J) then
            return false, "Argument 2 must be on curve of argument 1.";
        end if;
        D := FunctionFieldDivisor(P) - Degree(P)*ReductionDivisor(J);
    elif Type(P) eq DivFunElt then
        if FunctionField(P) ne
            AlgorithmicFunctionField(FunctionField(Curve(J))) then
            return false, "Argument 2 must be on curve of argument 1.";
        end if;
        D := P - Degree(P)*ReductionDivisor(J);
    else
        return false, "Invalid coercion";
    end if;
    return true, PicCrvCreate(J,D);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Creation Functions                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic PicardGroup(C::Crv,P::Pt) -> PicCrv
    {}
    require IsProjective(C) and IsField(BaseRing(C)) :
        "Argument 1 must be a projective curve over a field.";
    require Scheme(P) eq C and Ring(Parent(P)) cmpeq BaseRing(C) :
        "Argument 2 must be a point of argument 1 over its base ring.";
    J := New(PicCrv);
    J`Curve := C;
    J`Place := 1*FunctionFieldPlace(Place(P));
    return J;
end intrinsic;

intrinsic PicardGroup(C::Crv,P::PlcCrvElt) -> PicCrv
    {}
    require IsProjective(C) : "Argument 1 must be a projective curve.";
    require Degree(P) eq 1 : "Argument 2 must be of degree one.";
    require C eq Curve(P) :
        "Argument 1 must be the curve of argument 2.";
    J := New(PicCrv);
    J`Curve := C;
    J`Place := 1*FunctionFieldPlace(P);
    return J;
end intrinsic;

intrinsic PicardGroup(P::PlcCrvElt) -> PicCrv
    {}
    require Degree(P) eq 1 : "Argument must be of degree one.";
    J := New(PicCrv);
    J`Curve := Curve(P);
    J`Place := 1*FunctionFieldPlace(P);
    return J;
end intrinsic;

intrinsic PicardGroup(P::PlcFunElt) -> PicCrv
    {}
    require Degree(P) eq 1 : "Argument 2 must be of degree one.";
    J := New(PicCrv);
    J`Curve := Curve(FunctionField(P));
    J`Place := 1*P;
    return J;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Printing                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function SprintDivisor(C,D)
    if IsZero(D) then
        S := "0";
    else
        fcns := GroebnerBasis(Ideal(CurveDivisor(C,D)));
        S := "(";
        for i in [1..#fcns] do
            S *:= Sprint(fcns[i]);
            S *:= i lt #fcns select ", " else ")";
        end for;
    end if;
    return S;
end function;

intrinsic Print(J::PicCrv, level::MonStgElt)
    {}
    printf "Picard group of %o", J`Curve;
end intrinsic;

intrinsic Print(P::PicCrvElt, level::MonStgElt)
    {}
    D := Reduction(P`Element,Parent(P)`Place);
    C := Parent(P)`Curve;
    printf "%o", SprintDivisor(C,D);
end intrinsic;

intrinsic Parent(P::PicCrvElt) -> PicCrv
   {}
   return P`Parent;
end intrinsic;

intrinsic 'eq' (J1::PicCrv,J2::PicCrv) -> BoolElt
   {}
   return J1`Curve cmpeq J2`Curve and J1`Place cmpeq J2`Place;
end intrinsic;

intrinsic 'eq' (P::PicCrvElt,Q::PicCrvElt) -> BoolElt
   {}
   J := P`Parent;
   require J eq Q`Parent : "Arguments must have the same parent.";
   D, r := Reduction(P`Element-Q`Element,J`Place);
   return r eq 0;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Structure Attributes                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Divisor(P::PicCrvElt) -> DivCrvElt
    {}
    return CurveDivisor(P`Element);
end intrinsic;

intrinsic Curve(J::PicCrv) -> Crv
    {}
    return J`Curve;
end intrinsic;

intrinsic ReductionDivisor(J::PicCrv) -> Crv
    {}
    return J`Place;
end intrinsic;

intrinsic Zero(J::PicCrv) -> Crv
    {}
    return J!(DivisorGroup(J`Curve)!0);
end intrinsic;

intrinsic IsZero(P::PicCrvElt) -> Crv
    {}
    return IsZero(P`Element);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    Arithmetic operations, etc.                     //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function BinaryExpansion(n)
    if n in {0,1} then return [n]; end if;
    return [ n mod 2 ] cat BinaryExpansion(n div 2);
end function;

intrinsic '*'(n::RngIntElt,P::PicCrvElt) -> PicCrvElt
    {}
    Q := Zero(Parent(P));
    if n eq 0 then
        return Q;
    elif n lt 0 then
        P := -P;
        n *:= -1;
    end if;
    if n eq 1 then
        return P;
    elif n eq 2 then
        O := Parent(P)`Place;
        Q`Element := D + r*O where D, r := Reduction(2*P`Element,O);
        return Q;
    end if;
    b := BinaryExpansion(n);
    for i in [1..#b] do
        if b[i] eq 1 then Q := P+Q; end if;
        P := 2*P;
    end for;
    return Q;
end intrinsic;

intrinsic '+'(P::PicCrvElt,Q::PicCrvElt) -> PicCrvElt
    {}
    require Parent(P) eq Parent(Q) :
        "Arguments must have the same parent.";
    if IsZero(Q`Element) then return P; end if;
    if IsZero(P`Element) then return Q; end if;
    return Parent(P)!(P`Element + Q`Element);
end intrinsic;

intrinsic '-'(P::PicCrvElt) -> PicCrvElt
    {}
    if IsZero(P`Element) then return P; end if;
    return Parent(P)!(-P`Element);
end intrinsic;

intrinsic '-'(P::PicCrvElt,Q::PicCrvElt) -> PicCrvElt
    {}
    require Parent(P) eq Parent(Q) :
        "Arguments must have the same parent.";
    if IsZero(Q`Element) then return P; end if;
    if IsZero(P`Element) then return -Q; end if;
    return Parent(P)!(P`Element - Q`Element);
end intrinsic;


