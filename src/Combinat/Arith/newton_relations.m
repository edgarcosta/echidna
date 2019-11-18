//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//         Copyright (C) 2008 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
EXAMPLES:

> ////////////////////////////////////////////////////////////////////////////
> // #1: Verify the conversions between power and symmetric sums.
> ////////////////////////////////////////////////////////////////////////////
> SS<s1,s2,s3,s4,s5,s6> := FunctionField(ZZ,6);
> RR<p1,p2,p3,p4,p5,p6> := FunctionField(ZZ,6);
> ss := [s1,s2,s3,s4,s5,s6];
> pp := [p1,p2,p3,p4,p5,p6];
> PowerSumsToSymmetricSums(pp);
[
    p1,
    (p1^2 - p2)/2,
    (p1^3 - 3*p1*p2 + 2*p3)/6,
    (p1^4 - 6*p1^2*p2 + 8*p1*p3 + 3*p2^2 - 6*p4)/24,
    (p1^5 - 10*p1^3*p2 + 20*p1^2*p3 + 15*p1*p2^2 - 30*p1*p4 - 20*p2*p3 + 24*p5)/120,
    (p1^6 - 15*p1^4*p2 + 40*p1^3*p3 + 45*p1^2*p2^2 - 90*p1^2*p4 - 120*p1*p2*p3 + 144*p1*p5 - 15*p2^3 + 90*p2*p4 + 40*p3^2 - 120*p6)/720
]
> SymmetricSumsToPowerSums(ss);
[
    s1,
    s1^2 - 2*s2,
    s1^3 - 3*s1*s2 + 3*s3,
    s1^4 - 4*s1^2*s2 + 4*s1*s3 + 2*s2^2 - 4*s4,
    s1^5 - 5*s1^3*s2 + 5*s1^2*s3 + 5*s1*s2^2 - 5*s1*s4 - 5*s2*s3 + 5*s5,
    s1^6 - 6*s1^4*s2 + 6*s1^3*s3 + 9*s1^2*s2^2 - 6*s1^2*s4 - 12*s1*s2*s3 + 6*s1*s5 - 2*s2^3 + 6*s2*s4 + 3*s3^2 - 6*s6
]
> ss eq PowerSumsToSymmetricSums(SymmetricSumsToPowerSums(ss));
True
> pp eq SymmetricSumsToPowerSums(PowerSumsToSymmetricSums(pp));
True

> ////////////////////////////////////////////////////////////////////////////
> // #2: Power sums extend indefinitely but reversion to symmetric sums gives
> // trailing zeros (which verifies the number of terms in power sums).
> ////////////////////////////////////////////////////////////////////////////
> SS<s1,s2,s3,s4> := FunctionField(ZZ,4);
> ss := [s1,s2,s3,s4];
> pp := SymmetricSumsToPowerSums(ss,6);
> pp;
[
    s1,
    s1^2 - 2*s2,
    s1^3 - 3*s1*s2 + 3*s3,
    s1^4 - 4*s1^2*s2 + 4*s1*s3 + 2*s2^2 - 4*s4,
    s1^5 - 5*s1^3*s2 + 5*s1^2*s3 + 5*s1*s2^2 - 5*s1*s4 - 5*s2*s3,
    s1^6 - 6*s1^4*s2 + 6*s1^3*s3 + 9*s1^2*s2^2 - 6*s1^2*s4 - 12*s1*s2*s3 - 2*s2^3 + 6*s2*s4 + 3*s3^2
]
> PowerSumsToSymmetricSums(pp);
[
    s1,
    s2,
    s3,
    s4,
    0,
    0
]

> ////////////////////////////////////////////////////////////////////////////
> // #3:
> ////////////////////////////////////////////////////////////////////////////

> FF<x1,x2,x3,x4> := FunctionField(ZZ,4);
> PP<T> := PowerSeriesRing(FF);
> xx := [x1,x2,x3,x4];
> f := &*[ 1 - xi * T : xi in xx ];
> f;
> ss := [ (-1)^k * Coefficient(f,k) : k in [1..6] ];
> ss;
[
    x1 + x2 + x3 + x4,
    x1*x2 + x1*x3 + x1*x4 + x2*x3 + x2*x4 + x3*x4,
    x1*x2*x3 + x1*x2*x4 + x1*x3*x4 + x2*x3*x4,
    x1*x2*x3*x4,
    0,
    0
]
> pp := SymmetricSumsToPowerSums(ss);
> pp;
[
    x1 + x2 + x3 + x4,
    x1^2 + x2^2 + x3^2 + x4^2,
    x1^3 + x2^3 + x3^3 + x4^3,
    x1^4 + x2^4 + x3^4 + x4^4,
    x1^5 + x2^5 + x3^5 + x4^5,
    x1^6 + x2^6 + x3^6 + x4^6
]
> g := -T * Derivative(f)/(f + O(T^6));
> pp eq [ Coefficient(g,k) : k in [1..6] ];
True
> PowerSumsToSymmetricSums(pp);
[
    x1 + x2 + x3 + x4,
    x1*x2 + x1*x3 + x1*x4 + x2*x3 + x2*x4 + x3*x4,
    x1*x2*x3 + x1*x2*x4 + x1*x3*x4 + x2*x3*x4,
    x1*x2*x3*x4,
    0,
    0
]
*/

intrinsic PowerSumsToSymmetricSums(pp::SeqEnum[RngElt]) -> SeqEnum
    {Given a sequence of power sums pp = [p1,p2,p3,..,pn[,...]],
    supposed to be in n terms, returns the first n power sums
    determined by the Newton-Girard relations.  Note that zeroth
    terms (p0 = n and s0 = 1) are not included in the input or
    output sequences.  All primes up to n must be invertible.}
    X := Universe(pp);
    ss := [pp[1]];
    for m in [2..#pp] do
        ss[m] := -(&+[ X | (-1)^k*pp[k]*ss[m-k] : k in [1..m-1] ] + (-1)^m*pp[m])/m;
    end for;
    return ss;
end intrinsic;

intrinsic SymmetricSumsToPowerSums(ss::SeqEnum[RngElt]) -> SeqEnum
    {Given a sequence of symmetric sums ss = [s1,s2,s3,..,sn], returns
    the first n power sums determined by the Newton-Girard relations.
    determined by the Newton-Girard relations.  Note that zeroth terms
    (s0 = 1 and p0 = n) are not included in the input or output sequences.}
    X := Universe(ss);
    pp := [ss[1]];
    for m in [2..#ss] do
        pp[m] := -((-1)^m*(m*ss[m]) + &+[ X | (-1)^k*pp[m-k]*ss[k] : k in [1..m-1] ]);
    end for;
    return pp;
end intrinsic;

intrinsic SymmetricSumsToPowerSums(ss::SeqEnum,r::RngIntElt) -> SeqEnum
    {Given a sequence of symmetric sums ss = [s1,s2,s3,...], returns
    the first r power sums determined by the Newton-Girard relations.
    Note that zeroth terms (s0 = 1 and p0 = n) are not included in the
    input or output sequences.}
    X := Universe(ss);
    pp := [ss[1]];
    n := #ss;
    for m in [2..r] do
        if m le n then
            pp[m] := -((-1)^m*(m*ss[m]) + &+[ X | (-1)^k*pp[m-k]*ss[k] : k in [1..m-1] ]);
        else
            pp[m] := -&+[ X | (-1)^k*pp[m-k]*ss[k] : k in [1..n] ];
        end if;
    end for;
    return pp;
end intrinsic;

