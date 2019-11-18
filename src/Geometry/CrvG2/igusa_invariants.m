//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic AbsoluteIgusaInvariants(C::CrvHyp) -> SeqEnum
    {The absolute Igusa invariants of C.}
    // Bad Magma syntax, fixed by this function.
    if Characteristic(BaseField(C)) ne 2 then
	return AbsoluteInvariants(C);
    else
	return IgusaToAbsoluteIgusaInvariants(IgusaInvariants(C));
    end if;
end intrinsic;

intrinsic IgusaToNormalizedIgusaInvariants(JJ::SeqEnum[FldElt]) -> SeqEnum
    {A projectively normalized sequence of Igusa invariants, where
    the input is defined over a field.}
    J2,J4,J6,J8,J10 := Explode(JJ);
    if J2 ne 0 then
	u := 1/J2;
    elif J4 ne 0 then
	if J6 ne 0 then
	    u := J4/J6;
	else
	    u := J8/J10;
	end if;
    elif J6 ne 0 then
	if J8 ne 0 then
	    u := J6/J8; // char == 2 only
	else
	    u := J10/J6^2;
	end if;
    elif J8 ne 0 then
	u := J8/J10; // char == 2 only 
    else
	return [ Universe(JJ) | 0, 0, 0, 0, 1 ];
    end if;
    return [ u^i*JJ[i] : i in [1..5] ];
end intrinsic;

intrinsic AbsoluteIgusaToNormalizedIgusaInvariants(jj::SeqEnum[FldElt]) -> SeqEnum
    {A projectively normalized sequence of Igusa invariants, where
    the input is defined over a field.}
    K := Universe(jj);
    require #jj in {5,10} : "Argument must be a sequence of 5 or 10 absolute Igusa invariants.";
    j1,j2,j3,j4,j5 := Explode(jj[[1..5]]);
    if j1 ne 0 then
	J10 := 1/j1;
	J2 := 1;
	J4 := j2 * J10;
	J6 := j3 * J10;
	J8 := j4 * J10;
	return [J2,J4,J6,J8,J10];
    end if;
    require #jj eq 10 : "Argument must have nonzero first entry or consist of 10 absolute Igusa invariants.";
    j6,j7,j8,j9,j10 := Explode(jj[[6..10]]);
    if j5 ne 0 then
	// J4 != 0 and J6 != 0
	if Characteristic(K) eq 2 then
	    J2 := K!0;
	    J4 := (j5^3*j10^2)/(j7*j9^3);
	    J6 := J4;
	    J8 := (j5^4*j7)/j8^2;
	    J10 := j5^5/j8^2;
	else
	    J2 := K!0;
	    J4 := -4*j6^2/(j5*j9);
	    J6 := J4;
	    J8 := -J4^2/4;
	    J10 := 16*j6/j8;
	end if;
    elif j6 ne 0 then
	// J4 != 0 and J8 != 0 (J6 == 0)
	J2 := K!0; J4 := j6; J6 := K!0;	J8 := -J4^2/4; J10 := J8;
    elif j7 ne 0 then
	// J6 != 0 and J8 != 0 (J4 == 0)
	assert K!2 eq 0;
	J2 := K!0; J4 := K!0; J6 := j8/j9; J8 := J6; J10 := j8/j10;
    elif j8 ne 0 then
	// J6 != 0 (J4 == J8 == 0)
	J2 := K!0; J4 := K!0; J6 := 1/j8; J8 := K!0; J10 := J6^2;
    elif j10 ne 0 then
	// J8 != 0 (J4 == J6 == 0)
	assert K!2 eq 0;
	J2 := K!0; J4 := K!0; J6 := K!0; J8 := j10; J10 := j10;
    else // jj = [0,0,...,0]
	J2 := K!0; J4 := K!0; J6 := K!0; J8 := K!0; J10 := K!1;
    end if;
    return [J2,J4,J6,J8,J10];
end intrinsic;

