//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        USER DATABASE OBJECTS                             //
//                                                                          //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                  Original version: June 2000                             //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare type DBUser;
declare attributes DBUser :
    DBIdentifier,
    ExistsFunction,
    DeleteFunction,
    WriteFunction,
    IsInDomainFunction,
    Invariant;

//////////////////////////////////////////////////////////////////////////////
//                               PRINTING                                   //
//////////////////////////////////////////////////////////////////////////////

intrinsic Print(Dat::DBUser, level::MonStgElt)
    {}
    printf Dat`DBIdentifier cat " database";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                            EQUALITY TESTING                              //
//////////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(DB1::DBUser,DB2::DBUser) -> BoolElt
    {}
    if assigned DB1`Invariant then
	if not assigned DB2`Invariant then
	    return false;
	elif DB1`Invariant ne DB2`Invariant then
	    return false;
	end if;
    elif assigned DB2`Invariant then
	return false;
    end if;
    return DB1`DBIdentifier eq DB2`DBIdentifier;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                          MEMBERSHIP TESTING                              //
//////////////////////////////////////////////////////////////////////////////

intrinsic 'in'(X::.,Dat::DBUser) -> BoolElt
    {Returns true if and only if the object specified by X is in the database Dat.}
    bool, errstr := Dat`IsInDomainFunction(X);
    require bool : errstr;
    return Dat`ExistsFunction(X);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                         WRITING TO DATABASE                              //
//////////////////////////////////////////////////////////////////////////////

/*
Note: that we have two generic write functions, in one argument and two; the
former would be used is the object (X below) can be used as the key for its
own database lookup.  When a key K and an object X are required, the second
write function should be used.
*/

intrinsic Write(Dat::DBUser,X::. : Overwrite := false)
    {Give a user database Dat, write X to the database.}
    if Overwrite or not X in Dat then
	Dat`WriteFunction(X);
    end if;
end intrinsic;

intrinsic Write(Dat::DBUser,K::., X::. : Overwrite := false)
    {Give a user database Dat and lookup key K, write X to the database
    at position K.}
    if Overwrite or not K in Dat then
	Dat`WriteFunction(K,X);
    end if;
end intrinsic;
