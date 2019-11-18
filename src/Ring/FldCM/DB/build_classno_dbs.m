//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                        CLASS NUMBER DATABASE                             //
//                                                                          //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildClassNumberDatabase(Dat::DBUser,N1::RngIntElt, N2::RngIntElt) 
    {Build the database of class numbers h(D) of imaginary
    quadratic orders, for D in the range N1 < |D| <= N2, where
    N1 and N2 are congruent to 0 mod 10000.}
    require Dat`DBIdentifier eq "Class number" :
        "Argument 1 must be the database of class numbers.";
    range := 10000;
    require N1 mod range eq 0 and N2 mod range eq 0 :
        "Arguments 2 and 3 must be congruent to 0 mod 10000.";
    n := N1 div range;
    while range*n lt N2 do
        N0 := range*n;
        D1 := -N0-3;
        D2 := -N0-range;
        if D2 in Dat then
            printf "Already computed range %o < |D| <= %o.\n", N0, N0+range;
        else
            discs := [ D : D in [D1..D2 by -1] | D mod 4 in {0,1} ]; 
            Classnos := [ ClassNumber(D) : D in discs ];
            Write(Dat,Classnos,Abs(D2));
            printf "Completed range %o < |D| <= %o.\n", N0, N0+range;
        end if;
        n +:= 1;
    end while;
end intrinsic;

