//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                        QUADRATIC CM DATABASE                             //
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

import "quadratic_cm_fields.m": range, QuadraticCMOrderDataFile;

//////////////////////////////////////////////////////////////////////////////

function IntegerSequenceToString(S)
    case #S:
    when 0:
	return "";
    when 1:
	return Sprint(S[1]);
    else
	return &*[ Sprint(n) * " " : n in S[1..#S-1] ] * Sprint(S[#S]);
    end case;
end function;

//////////////////////////////////////////////////////////////////////////////

intrinsic BuildQuadraticCMFieldsDatabase(
    Dat::DBUser,N1::RngIntElt, N2::RngIntElt : Overwrite := false)
    {Build the database of class invariants of orders in quadratic CM fields,
    for all discriminants D in the range N1 < |D| <= N2, where N1 and N2 are
    congruent to 0 mod 10000.}
    require Dat`DBIdentifier eq "Quadratic CM fields" :
        "Argument 1 must be the database of quadratic CM fields.";
    require N1 mod range eq 0 and N2 mod range eq 0 :
        "Arguments 2 and 3 must be congruent to 0 mod 10000.";
    n := N1 div range;
    while range*n lt N2 do
        N0 := range*n;
        D1 := -N0-3;
        D2 := -N0-range;
        if not Overwrite and D2 in Dat then
            printf "Already computed range %o < |D| <= %o.\n", N0, N0+range;
        else
	    tyme := Cputime();
	    Class_list := [ ];
	    for D in [D1..D2 by -1] do
		if D mod 4 in {0,1} then
		    Q := QuadraticForms(D);
		    G, m := ClassGroup(Q);
		    // Check:
		    if #G ne ClassNumber(Q) then
			print "|G| != ClassNumber(Q) for D =", D;
			assert false;
		    end if;
		    // Check:
		    if #G ne #{ m(g) : g in G } then
			print "|G| != |{ m(g) : g in G }| for D =", D;
			assert false;
		    end if;
		    //
		    h_invs := AbelianInvariants(ClassGroup(Q));
		    if h_invs eq [] then
			h_invs := [1];
		    end if;
		    Append(~Class_list, h_invs);
		end if;
	    end for;
	    filename, index := QuadraticCMOrderDataFile(D2);
	    assert index eq range div 2;
	    file := Open(filename,"w");  Flush(file);
	    for h_invs in Class_list do
		Puts(file,IntegerSequenceToString(h_invs));
	    end for;
	    delete file;
	    System("bzip2 -c " * filename * " > " * filename * "z");
	    System("chmod a+r " * filename * "z");
	    System("rm " * filename);
            printf "Completed range %o < |D| <= %o [Time: %o]\n", N0, N0+range, Cputime(tyme);
        end if;
        n +:= 1;
    end while;
end intrinsic;

