//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                       ATKIN POWER SERIES DATABASE                        //
//                                                                          //
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildAtkinModularFunctionDatabase(
    Dat::DBUser, S::[RngIntElt], prec::RngIntElt)
    {Build the database of Atkin power series for N in S.}
    require Dat`DBIdentifier eq "Atkin modular function" :
        "Argument 1 must be the database of Atkin modular functions.";
    for N in S do
        computed := false;
        if N in Dat then
            printf "Level %o ", N;
            curr := DatabasePrecision(Dat,N);
            if curr ge prec then
                printf "already represented in database " *
                    "to precision %o.\n", prec;
            else
                printf "represented in database " *
                    "to precision %o, extending to %o\n", curr, prec;
                f := AtkinModularFunction(N,prec);
                computed := true;
            end if;
        else
            printf "Computing Atkin power series of level %o.\n", N;
            f := AtkinModularFunction(N,prec);
            computed := true;
        end if;
        if computed then
            Write(Dat,f,N : Overwrite := true);
            print "Completed Atkin power series for level", N;
        end if;
    end for;
end intrinsic;
