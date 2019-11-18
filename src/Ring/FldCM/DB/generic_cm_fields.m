//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                           GENERIC CM FIELDS                              //
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

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic CMFieldDatabase(deg::RngIntElt) -> DBUser
    {The database of quartic CM fields.}
    Dat := New(DBUser);
    Dat`Invariant := deg;
    if deg eq 4 then
	Dat`DBIdentifier := "Quartic CM fields";
    elif deg eq 6 then
	Dat`DBIdentifier := "Sextic CM fields";
    elif deg eq 8 then
	Dat`DBIdentifier := "Octic CM fields";
    else
	Dat`DBIdentifier := "CM fields";
    end if;
    return Dat;
end intrinsic;

