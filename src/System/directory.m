//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                ECHIDNA Share Packages Root Directory                     //
//         Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu.au>         //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic GetEchidnaRoot() -> MonStgElt
    {}
    EchidnaRoot := GetEnv("ECHIDNA_ROOT");
    require #EchidnaRoot gt 0:
	"You must set the environment variable ECHIDNA_ROOT to the full pathname of the Echidna repository.";
    return EchidnaRoot;
end intrinsic;

intrinsic GetEchidnaPackageRoot() -> MonStgElt
    {}
    EchidnaRoot := GetEnv("ECHIDNA_ROOT");
    require #EchidnaRoot gt 0:
	"You must set the environment variable ECHIDNA_ROOT to the full pathname of the Echidna repository.";
    return EchidnaRoot * "/src";
end intrinsic;

intrinsic GetEchidnaDatabaseRoot() -> MonStgElt
    {}
    EchidnaRoot := GetEnv("ECHIDNA_ROOT");
    require #EchidnaRoot gt 0:
	"You must set the environment variable ECHIDNA_ROOT to the full pathname of the Echidna repository.";
    return EchidnaRoot * "/dbs";
end intrinsic;

