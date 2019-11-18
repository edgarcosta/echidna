/*****************************************************************************
#  Supersingular polynomials and divisors 
#  Copyright (C) 2005 David Kohel <kohel@maths.usyd.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty
#    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
#
#  See the GNU General Public License for more details; the full text
#  is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************/

function IsInertOrRamified(D,p)
    e := KroneckerSymbol(D,p);
    if e eq 0 then
	v := Valuation(D,p) div 2;
	D div:= p^(2*v);
	if p eq 2 and D mod 4 ne 1 then
	    return true; // ramified 
	end if;
	e := KroneckerSymbol(D,p);
    end if;
    return e ne 1;
end function;
	    
intrinsic HeegnerDivisor(SS::SetIndx[RngUPolElt[FldFin]], D::RngIntElt)
    -> SeqEnum
    {An integral vector giving the multiplicities of the supersingular
    factors of the Hilbert class polynomial of discriminant D with
    respect to their complete list SS.}
    P := Universe(SS);
    p := Characteristic(BaseRing(P));
    require IsInertOrRamified(D,p) : 
	"Argument 2 must be inert or ramified with respect to in argument 1.";
    H := P!HilbertClassPolynomial(D);
    v := RSpace(Integers(),#SS)!0;
    for fac in Factorization(H) do
	v[Index(SS,fac[1])] +:= fac[2];
    end for;
    return v;
end intrinsic;

function RationalHeegnerDivisor(SS,D,p)
    n := #SS;
    v := RSpace(RationalField(),n)!0;
    for i in [1..n] do
	f := SS[i];
	v[i] := Coefficient(f,-D)/2;
	if Coefficient(f,3) ne 0 then
	    v[i] /:= 3;
	elif Coefficient(f,4) ne 0 then
	    v[i] /:= 2;
	end if;
    end for;
    return v;
end function;

intrinsic HeegnerDivisor(
    SS::SetIndx[RngSerPowElt[RngInt]],D::RngIntElt,p::RngIntElt) -> SeqEnum
    {An integral vector giving the multiplicities of the supersingular
    factors of the Hilbert class polynomial of discriminant D with
    respect to their complete list SS.}
    require IsInertOrRamified(D,p) : 
	"Argument 2 must be inert or ramified with respect to in argument 1.";
    DK := FundamentalDiscriminant(D);
    m := Isqrt(D div DK);
    if m eq 1 then
	v := RationalHeegnerDivisor(SS,D,p);
    else
	v := &+[ MoebiusMu(m div r) *
	    RationalHeegnerDivisor(SS,r^2*DK,p) : r in Divisors(m) ];
    end if;
    if D eq -3 then
	v *:= 3;
    elif D eq -4 then
	v *:= 2;
    end if;
    return v;
end intrinsic;
