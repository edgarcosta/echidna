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

function Level2ThetaNullHumbertPolynomials44(R)
    P<a00,a02,a20,a22> := PolynomialRing(R, 4 : Global);
    //print "Warning: returning only one component.";
    return {@
        4194304*a00^22*a02^3*a20^3 - 3145728*a00^20*a02^5*a20*a22^2 + 37748736*a00^20*a02^4*a20^4 -
        1048576*a00^20*a02^4*a22^4 - 3145728*a00^20*a02*a20^5*a22^2 - 
        1048576*a00^20*a20^4*a22^4 - 262144*a00^18*a02^8*a22^2 - 9961472*a00^18*a02^7*a20^3 -
        27262976*a00^18*a02^6*a20^2*a22^2 + 174587904*a00^18*a02^5*a20^5 - 
        9437184*a00^18*a02^5*a20*a22^4 - 4456448*a00^18*a02^4*a20^4*a22^2 - 
        9961472*a00^18*a02^3*a20^7 + 1310720*a00^18*a02^3*a20^3*a22^4 - 
        27262976*a00^18*a02^2*a20^6*a22^2 + 1835008*a00^18*a02^2*a20^2*a22^6 - 
        9437184*a00^18*a02*a20^5*a22^4 + 262144*a00^18*a02*a20*a22^8 - 
        262144*a00^18*a20^8*a22^2 + 131072*a00^16*a02^10*a20^2 + 
        4718592*a00^16*a02^9*a20*a22^2 - 81461248*a00^16*a02^8*a20^4 + 
        2097152*a00^16*a02^8*a22^4 - 198311936*a00^16*a02^7*a20^3*a22^2 + 
        480903168*a00^16*a02^6*a20^6 - 39780352*a00^16*a02^6*a20^2*a22^4 - 
        4194304*a00^16*a02^5*a20^5*a22^2 + 1572864*a00^16*a02^5*a20*a22^6 - 
        81461248*a00^16*a02^4*a20^8 - 53870592*a00^16*a02^4*a20^4*a22^4 + 
        262144*a00^16*a02^4*a22^8 - 198311936*a00^16*a02^3*a20^7*a22^2 + 
        15990784*a00^16*a02^3*a20^3*a22^6 + 131072*a00^16*a02^2*a20^10 - 
        39780352*a00^16*a02^2*a20^6*a22^4 + 2359296*a00^16*a02^2*a20^2*a22^8 + 
        4718592*a00^16*a02*a20^9*a22^2 + 1572864*a00^16*a02*a20^5*a22^6 + 
        2097152*a00^16*a20^8*a22^4 + 262144*a00^16*a20^4*a22^8 + 524288*a00^14*a02^12*a22^2 +
        9256960*a00^14*a02^11*a20^3 + 44580864*a00^14*a02^10*a20^2*a22^2 - 
        300154880*a00^14*a02^9*a20^5 + 74678272*a00^14*a02^9*a20*a22^4 - 
        756744192*a00^14*a02^8*a20^4*a22^2 + 19070976*a00^14*a02^8*a22^6 + 
        910540800*a00^14*a02^7*a20^7 - 115212288*a00^14*a02^7*a20^3*a22^4 + 
        175095808*a00^14*a02^6*a20^6*a22^2 + 57016320*a00^14*a02^6*a20^2*a22^6 - 
        300154880*a00^14*a02^5*a20^9 - 268025856*a00^14*a02^5*a20^5*a22^4 + 
        18808832*a00^14*a02^5*a20*a22^8 - 756744192*a00^14*a02^4*a20^8*a22^2 + 
        105725952*a00^14*a02^4*a20^4*a22^6 + 9256960*a00^14*a02^3*a20^11 - 
        115212288*a00^14*a02^3*a20^7*a22^4 + 9093120*a00^14*a02^3*a20^3*a22^8 + 
        44580864*a00^14*a02^2*a20^10*a22^2 + 57016320*a00^14*a02^2*a20^6*a22^6 - 
        606208*a00^14*a02^2*a20^2*a22^10 + 74678272*a00^14*a02*a20^9*a22^4 + 
        18808832*a00^14*a02*a20^5*a22^8 - 147456*a00^14*a02*a20*a22^12 + 
        524288*a00^14*a20^12*a22^2 + 19070976*a00^14*a20^8*a22^6 - 16384*a00^14*a22^14 - 
        233472*a00^12*a02^14*a20^2 - 1081344*a00^12*a02^13*a20*a22^2 + 
        58269696*a00^12*a02^12*a20^4 + 3457024*a00^12*a02^12*a22^4 + 
        267665408*a00^12*a02^11*a20^3*a22^2 - 608821248*a00^12*a02^10*a20^6 + 
        370245632*a00^12*a02^10*a20^2*a22^4 - 1729028096*a00^12*a02^9*a20^5*a22^2 + 
        119865344*a00^12*a02^9*a20*a22^6 + 1241702400*a00^12*a02^8*a20^8 - 
        195776512*a00^12*a02^8*a20^4*a22^4 + 1835008*a00^12*a02^8*a22^8 + 
        1315078144*a00^12*a02^7*a20^7*a22^2 + 541376512*a00^12*a02^7*a20^3*a22^6 - 
        608821248*a00^12*a02^6*a20^10 + 472211456*a00^12*a02^6*a20^6*a22^4 + 
        88240128*a00^12*a02^6*a20^2*a22^8 - 1729028096*a00^12*a02^5*a20^9*a22^2 + 
        484818944*a00^12*a02^5*a20^5*a22^6 - 4743168*a00^12*a02^5*a20*a22^10 + 
        58269696*a00^12*a02^4*a20^12 - 195776512*a00^12*a02^4*a20^8*a22^4 + 
        3268608*a00^12*a02^4*a20^4*a22^8 - 28672*a00^12*a02^4*a22^12 + 
        267665408*a00^12*a02^3*a20^11*a22^2 + 541376512*a00^12*a02^3*a20^7*a22^6 - 
        33718272*a00^12*a02^3*a20^3*a22^10 - 233472*a00^12*a02^2*a20^14 + 
        370245632*a00^12*a02^2*a20^10*a22^4 + 88240128*a00^12*a02^2*a20^6*a22^8 - 
        5464064*a00^12*a02^2*a20^2*a22^12 - 1081344*a00^12*a02*a20^13*a22^2 + 
        119865344*a00^12*a02*a20^9*a22^6 - 4743168*a00^12*a02*a20^5*a22^10 - 
        147456*a00^12*a02*a20*a22^14 + 3457024*a00^12*a20^12*a22^4 + 
        1835008*a00^12*a20^8*a22^8 - 28672*a00^12*a20^4*a22^12 + 1024*a00^10*a02^17*a20 - 
        323584*a00^10*a02^16*a22^2 - 4390912*a00^10*a02^15*a20^3 - 
        19898368*a00^10*a02^14*a20^2*a22^2 + 133039104*a00^10*a02^13*a20^5 - 
        52273152*a00^10*a02^13*a20*a22^4 + 819289088*a00^10*a02^12*a20^4*a22^2 - 
        18546688*a00^10*a02^12*a22^6 - 777039872*a00^10*a02^11*a20^7 + 
        1100957696*a00^10*a02^11*a20^3*a22^4 - 2710802432*a00^10*a02^10*a20^6*a22^2 + 
        247298048*a00^10*a02^10*a20^2*a22^6 + 1283231744*a00^10*a02^9*a20^9 - 
        1102585856*a00^10*a02^9*a20^5*a22^4 - 219274240*a00^10*a02^9*a20*a22^8 + 
        3111700480*a00^10*a02^8*a20^8*a22^2 + 616734720*a00^10*a02^8*a20^4*a22^6 - 
        69489664*a00^10*a02^8*a22^10 - 777039872*a00^10*a02^7*a20^11 + 
        3000184832*a00^10*a02^7*a20^7*a22^4 - 159592448*a00^10*a02^7*a20^3*a22^8 - 
        2710802432*a00^10*a02^6*a20^10*a22^2 + 1167200256*a00^10*a02^6*a20^6*a22^6 - 
        58617856*a00^10*a02^6*a20^2*a22^10 + 133039104*a00^10*a02^5*a20^13 - 
        1102585856*a00^10*a02^5*a20^9*a22^4 - 447358976*a00^10*a02^5*a20^5*a22^8 - 
        4743168*a00^10*a02^5*a20*a22^12 + 819289088*a00^10*a02^4*a20^12*a22^2 + 
        616734720*a00^10*a02^4*a20^8*a22^6 - 340834304*a00^10*a02^4*a20^4*a22^10 - 
        4390912*a00^10*a02^3*a20^15 + 1100957696*a00^10*a02^3*a20^11*a22^4 - 
        159592448*a00^10*a02^3*a20^7*a22^8 - 33718272*a00^10*a02^3*a20^3*a22^12 - 
        19898368*a00^10*a02^2*a20^14*a22^2 + 247298048*a00^10*a02^2*a20^10*a22^6 - 
        58617856*a00^10*a02^2*a20^6*a22^10 - 606208*a00^10*a02^2*a20^2*a22^14 + 
        1024*a00^10*a02*a20^17 - 52273152*a00^10*a02*a20^13*a22^4 - 
        219274240*a00^10*a02*a20^9*a22^8 - 4743168*a00^10*a02*a20^5*a22^12 - 
        323584*a00^10*a20^16*a22^2 - 18546688*a00^10*a20^12*a22^6 - 
        69489664*a00^10*a20^8*a22^10 + 128000*a00^8*a02^18*a20^2 - 
        413696*a00^8*a02^17*a20*a22^2 - 15319808*a00^8*a02^16*a20^4 - 
        4505600*a00^8*a02^16*a22^4 - 63443968*a00^8*a02^15*a20^3*a22^2 + 
        144203264*a00^8*a02^14*a20^6 - 270336512*a00^8*a02^14*a20^2*a22^4 + 
        1262054400*a00^8*a02^13*a20^5*a22^2 - 268686336*a00^8*a02^13*a20*a22^6 - 
        595029248*a00^8*a02^12*a20^8 + 2073945088*a00^8*a02^12*a20^4*a22^4 - 
        72262400*a00^8*a02^12*a22^8 - 3171589120*a00^8*a02^11*a20^7*a22^2 + 
        575840256*a00^8*a02^11*a20^3*a22^6 + 906558464*a00^8*a02^10*a20^10 - 
        3809996288*a00^8*a02^10*a20^6*a22^4 - 538337792*a00^8*a02^10*a20^2*a22^8 + 
        4017383424*a00^8*a02^9*a20^9*a22^2 - 1799080960*a00^8*a02^9*a20^5*a22^6 - 
        219274240*a00^8*a02^9*a20*a22^10 - 595029248*a00^8*a02^8*a20^12 + 
        5491644416*a00^8*a02^8*a20^8*a22^4 - 1318530304*a00^8*a02^8*a20^4*a22^8 + 
        1835008*a00^8*a02^8*a22^12 - 3171589120*a00^8*a02^7*a20^11*a22^2 + 
        1400651776*a00^8*a02^7*a20^7*a22^6 - 159592448*a00^8*a02^7*a20^3*a22^10 + 
        144203264*a00^8*a02^6*a20^14 - 3809996288*a00^8*a02^6*a20^10*a22^4 - 
        1703533568*a00^8*a02^6*a20^6*a22^8 + 88240128*a00^8*a02^6*a20^2*a22^12 + 
        1262054400*a00^8*a02^5*a20^13*a22^2 - 1799080960*a00^8*a02^5*a20^9*a22^6 - 
        447358976*a00^8*a02^5*a20^5*a22^10 + 18808832*a00^8*a02^5*a20*a22^14 - 
        15319808*a00^8*a02^4*a20^16 + 2073945088*a00^8*a02^4*a20^12*a22^4 - 
        1318530304*a00^8*a02^4*a20^8*a22^8 + 3268608*a00^8*a02^4*a20^4*a22^12 + 
        262144*a00^8*a02^4*a22^16 - 63443968*a00^8*a02^3*a20^15*a22^2 + 
        575840256*a00^8*a02^3*a20^11*a22^6 - 159592448*a00^8*a02^3*a20^7*a22^10 + 
        9093120*a00^8*a02^3*a20^3*a22^14 + 128000*a00^8*a02^2*a20^18 - 
        270336512*a00^8*a02^2*a20^14*a22^4 - 538337792*a00^8*a02^2*a20^10*a22^8 + 
        88240128*a00^8*a02^2*a20^6*a22^12 + 2359296*a00^8*a02^2*a20^2*a22^16 - 
        413696*a00^8*a02*a20^17*a22^2 - 268686336*a00^8*a02*a20^13*a22^6 - 
        219274240*a00^8*a02*a20^9*a22^10 + 18808832*a00^8*a02*a20^5*a22^14 + 
        262144*a00^8*a02*a20*a22^18 - 4505600*a00^8*a20^16*a22^4 - 72262400*a00^8*a20^12*a22^8
        + 1835008*a00^8*a20^8*a22^12 + 262144*a00^8*a20^4*a22^16 - 1280*a00^6*a02^21*a20 + 
        61440*a00^6*a02^20*a22^2 + 892608*a00^6*a02^19*a20^3 + 
        3374528*a00^6*a02^18*a20^2*a22^2 - 10410752*a00^6*a02^17*a20^5 - 
        16153024*a00^6*a02^17*a20*a22^4 - 104164864*a00^6*a02^16*a20^4*a22^2 - 
        15689920*a00^6*a02^16*a22^6 + 67730688*a00^6*a02^15*a20^7 - 
        475097600*a00^6*a02^15*a20^3*a22^4 + 911505664*a00^6*a02^14*a20^6*a22^2 - 
        670575104*a00^6*a02^14*a20^2*a22^6 - 258600960*a00^6*a02^13*a20^9 + 
        2245152512*a00^6*a02^13*a20^5*a22^4 - 268686336*a00^6*a02^13*a20*a22^8 - 
        2288833024*a00^6*a02^12*a20^8*a22^2 + 1776900864*a00^6*a02^12*a20^4*a22^6 - 
        18546688*a00^6*a02^12*a22^10 + 398469248*a00^6*a02^11*a20^11 - 
        5402895872*a00^6*a02^11*a20^7*a22^4 + 575840256*a00^6*a02^11*a20^3*a22^8 + 
        3048043136*a00^6*a02^10*a20^10*a22^2 - 4869088768*a00^6*a02^10*a20^6*a22^6 + 
        247298048*a00^6*a02^10*a20^2*a22^10 - 258600960*a00^6*a02^9*a20^13 + 
        7257339264*a00^6*a02^9*a20^9*a22^4 - 1799080960*a00^6*a02^9*a20^5*a22^8 + 
        119865344*a00^6*a02^9*a20*a22^12 - 2288833024*a00^6*a02^8*a20^12*a22^2 + 
        5711264640*a00^6*a02^8*a20^8*a22^6 + 616734720*a00^6*a02^8*a20^4*a22^10 + 
        19070976*a00^6*a02^8*a22^14 + 67730688*a00^6*a02^7*a20^15 - 
        5402895872*a00^6*a02^7*a20^11*a22^4 + 1400651776*a00^6*a02^7*a20^7*a22^8 + 
        541376512*a00^6*a02^7*a20^3*a22^12 + 911505664*a00^6*a02^6*a20^14*a22^2 - 
        4869088768*a00^6*a02^6*a20^10*a22^6 + 1167200256*a00^6*a02^6*a20^6*a22^10 + 
        57016320*a00^6*a02^6*a20^2*a22^14 - 10410752*a00^6*a02^5*a20^17 + 
        2245152512*a00^6*a02^5*a20^13*a22^4 - 1799080960*a00^6*a02^5*a20^9*a22^8 + 
        484818944*a00^6*a02^5*a20^5*a22^12 + 1572864*a00^6*a02^5*a20*a22^16 - 
        104164864*a00^6*a02^4*a20^16*a22^2 + 1776900864*a00^6*a02^4*a20^12*a22^6 + 
        616734720*a00^6*a02^4*a20^8*a22^10 + 105725952*a00^6*a02^4*a20^4*a22^14 + 
        892608*a00^6*a02^3*a20^19 - 475097600*a00^6*a02^3*a20^15*a22^4 + 
        575840256*a00^6*a02^3*a20^11*a22^8 + 541376512*a00^6*a02^3*a20^7*a22^12 + 
        15990784*a00^6*a02^3*a20^3*a22^16 + 3374528*a00^6*a02^2*a20^18*a22^2 - 
        670575104*a00^6*a02^2*a20^14*a22^6 + 247298048*a00^6*a02^2*a20^10*a22^10 + 
        57016320*a00^6*a02^2*a20^6*a22^14 + 1835008*a00^6*a02^2*a20^2*a22^18 - 
        1280*a00^6*a02*a20^21 - 16153024*a00^6*a02*a20^17*a22^4 - 
        268686336*a00^6*a02*a20^13*a22^8 + 119865344*a00^6*a02*a20^9*a22^12 + 
        1572864*a00^6*a02*a20^5*a22^16 + 61440*a00^6*a20^20*a22^2 - 
        15689920*a00^6*a20^16*a22^6 - 18546688*a00^6*a20^12*a22^10 + 
        19070976*a00^6*a20^8*a22^14 - 24400*a00^4*a02^22*a20^2 - 64608*a00^4*a02^21*a20*a22^2 
        + 268000*a00^4*a02^20*a20^4 - 498000*a00^4*a02^20*a22^4 + 
        394880*a00^4*a02^19*a20^3*a22^2 - 737552*a00^4*a02^18*a20^6 - 
        12560800*a00^4*a02^18*a20^2*a22^4 - 64670432*a00^4*a02^17*a20^5*a22^2 - 
        16153024*a00^4*a02^17*a20*a22^6 - 2616704*a00^4*a02^16*a20^8 - 
        303409424*a00^4*a02^16*a20^4*a22^4 - 4505600*a00^4*a02^16*a22^8 + 
        347173376*a00^4*a02^15*a20^7*a22^2 - 475097600*a00^4*a02^15*a20^3*a22^6 + 
        1069152*a00^4*a02^14*a20^10 + 1398757504*a00^4*a02^14*a20^6*a22^4 - 
        270336512*a00^4*a02^14*a20^2*a22^8 - 739248320*a00^4*a02^13*a20^9*a22^2 + 
        2245152512*a00^4*a02^13*a20^5*a22^6 - 52273152*a00^4*a02^13*a20*a22^10 + 
        5311808*a00^4*a02^12*a20^12 - 3357298080*a00^4*a02^12*a20^8*a22^4 + 
        2073945088*a00^4*a02^12*a20^4*a22^8 + 3457024*a00^4*a02^12*a22^12 + 
        918122240*a00^4*a02^11*a20^11*a22^2 - 5402895872*a00^4*a02^11*a20^7*a22^6 + 
        1100957696*a00^4*a02^11*a20^3*a22^10 + 1069152*a00^4*a02^10*a20^14 + 
        4400710208*a00^4*a02^10*a20^10*a22^4 - 3809996288*a00^4*a02^10*a20^6*a22^8 + 
        370245632*a00^4*a02^10*a20^2*a22^12 - 739248320*a00^4*a02^9*a20^13*a22^2 + 
        7257339264*a00^4*a02^9*a20^9*a22^6 - 1102585856*a00^4*a02^9*a20^5*a22^10 + 
        74678272*a00^4*a02^9*a20*a22^14 - 2616704*a00^4*a02^8*a20^16 - 
        3357298080*a00^4*a02^8*a20^12*a22^4 + 5491644416*a00^4*a02^8*a20^8*a22^8 - 
        195776512*a00^4*a02^8*a20^4*a22^12 + 2097152*a00^4*a02^8*a22^16 + 
        347173376*a00^4*a02^7*a20^15*a22^2 - 5402895872*a00^4*a02^7*a20^11*a22^6 + 
        3000184832*a00^4*a02^7*a20^7*a22^10 - 115212288*a00^4*a02^7*a20^3*a22^14 - 
        737552*a00^4*a02^6*a20^18 + 1398757504*a00^4*a02^6*a20^14*a22^4 - 
        3809996288*a00^4*a02^6*a20^10*a22^8 + 472211456*a00^4*a02^6*a20^6*a22^12 - 
        39780352*a00^4*a02^6*a20^2*a22^16 - 64670432*a00^4*a02^5*a20^17*a22^2 + 
        2245152512*a00^4*a02^5*a20^13*a22^6 - 1102585856*a00^4*a02^5*a20^9*a22^10 - 
        268025856*a00^4*a02^5*a20^5*a22^14 - 9437184*a00^4*a02^5*a20*a22^18 + 
        268000*a00^4*a02^4*a20^20 - 303409424*a00^4*a02^4*a20^16*a22^4 + 
        2073945088*a00^4*a02^4*a20^12*a22^8 - 195776512*a00^4*a02^4*a20^8*a22^12 - 
        53870592*a00^4*a02^4*a20^4*a22^16 - 1048576*a00^4*a02^4*a22^20 + 
        394880*a00^4*a02^3*a20^19*a22^2 - 475097600*a00^4*a02^3*a20^15*a22^6 + 
        1100957696*a00^4*a02^3*a20^11*a22^10 - 115212288*a00^4*a02^3*a20^7*a22^14 + 
        1310720*a00^4*a02^3*a20^3*a22^18 - 24400*a00^4*a02^2*a20^22 - 
        12560800*a00^4*a02^2*a20^18*a22^4 - 270336512*a00^4*a02^2*a20^14*a22^8 + 
        370245632*a00^4*a02^2*a20^10*a22^12 - 39780352*a00^4*a02^2*a20^6*a22^16 - 
        64608*a00^4*a02*a20^21*a22^2 - 16153024*a00^4*a02*a20^17*a22^6 - 
        52273152*a00^4*a02*a20^13*a22^10 + 74678272*a00^4*a02*a20^9*a22^14 - 
        9437184*a00^4*a02*a20^5*a22^18 - 498000*a00^4*a20^20*a22^4 - 
        4505600*a00^4*a20^16*a22^8 + 3457024*a00^4*a20^12*a22^12 + 2097152*a00^4*a20^8*a22^16
        - 1048576*a00^4*a20^4*a22^20 + 284*a00^2*a02^25*a20 - 1564*a00^2*a02^24*a22^2 - 
        1712*a00^2*a02^23*a20^3 + 178192*a00^2*a02^22*a20^2*a22^2 - 16072*a00^2*a02^21*a20^5 -
        64608*a00^2*a02^21*a20*a22^4 - 2286968*a00^2*a02^20*a20^4*a22^2 + 
        61440*a00^2*a02^20*a22^6 - 36848*a00^2*a02^19*a20^7 + 394880*a00^2*a02^19*a20^3*a22^4 
        + 1375696*a00^2*a02^18*a20^6*a22^2 + 3374528*a00^2*a02^18*a20^2*a22^6 - 
        15068*a00^2*a02^17*a20^9 - 64670432*a00^2*a02^17*a20^5*a22^4 - 
        413696*a00^2*a02^17*a20*a22^8 + 12735708*a00^2*a02^16*a20^8*a22^2 - 
        104164864*a00^2*a02^16*a20^4*a22^6 - 323584*a00^2*a02^16*a22^10 + 
        67232*a00^2*a02^15*a20^11 + 347173376*a00^2*a02^15*a20^7*a22^4 - 
        63443968*a00^2*a02^15*a20^3*a22^8 - 2541024*a00^2*a02^14*a20^10*a22^2 + 
        911505664*a00^2*a02^14*a20^6*a22^6 - 19898368*a00^2*a02^14*a20^2*a22^10 + 
        119056*a00^2*a02^13*a20^13 - 739248320*a00^2*a02^13*a20^9*a22^4 + 
        1262054400*a00^2*a02^13*a20^5*a22^8 - 1081344*a00^2*a02^13*a20*a22^12 - 
        22868624*a00^2*a02^12*a20^12*a22^2 - 2288833024*a00^2*a02^12*a20^8*a22^6 + 
        819289088*a00^2*a02^12*a20^4*a22^10 + 524288*a00^2*a02^12*a22^14 + 
        67232*a00^2*a02^11*a20^15 + 918122240*a00^2*a02^11*a20^11*a22^4 - 
        3171589120*a00^2*a02^11*a20^7*a22^8 + 267665408*a00^2*a02^11*a20^3*a22^12 - 
        2541024*a00^2*a02^10*a20^14*a22^2 + 3048043136*a00^2*a02^10*a20^10*a22^6 - 
        2710802432*a00^2*a02^10*a20^6*a22^10 + 44580864*a00^2*a02^10*a20^2*a22^14 - 
        15068*a00^2*a02^9*a20^17 - 739248320*a00^2*a02^9*a20^13*a22^4 + 
        4017383424*a00^2*a02^9*a20^9*a22^8 - 1729028096*a00^2*a02^9*a20^5*a22^12 + 
        4718592*a00^2*a02^9*a20*a22^16 + 12735708*a00^2*a02^8*a20^16*a22^2 - 
        2288833024*a00^2*a02^8*a20^12*a22^6 + 3111700480*a00^2*a02^8*a20^8*a22^10 - 
        756744192*a00^2*a02^8*a20^4*a22^14 - 262144*a00^2*a02^8*a22^18 - 
        36848*a00^2*a02^7*a20^19 + 347173376*a00^2*a02^7*a20^15*a22^4 - 
        3171589120*a00^2*a02^7*a20^11*a22^8 + 1315078144*a00^2*a02^7*a20^7*a22^12 - 
        198311936*a00^2*a02^7*a20^3*a22^16 + 1375696*a00^2*a02^6*a20^18*a22^2 + 
        911505664*a00^2*a02^6*a20^14*a22^6 - 2710802432*a00^2*a02^6*a20^10*a22^10 + 
        175095808*a00^2*a02^6*a20^6*a22^14 - 27262976*a00^2*a02^6*a20^2*a22^18 - 
        16072*a00^2*a02^5*a20^21 - 64670432*a00^2*a02^5*a20^17*a22^4 + 
        1262054400*a00^2*a02^5*a20^13*a22^8 - 1729028096*a00^2*a02^5*a20^9*a22^12 - 
        4194304*a00^2*a02^5*a20^5*a22^16 - 3145728*a00^2*a02^5*a20*a22^20 - 
        2286968*a00^2*a02^4*a20^20*a22^2 - 104164864*a00^2*a02^4*a20^16*a22^6 + 
        819289088*a00^2*a02^4*a20^12*a22^10 - 756744192*a00^2*a02^4*a20^8*a22^14 - 
        4456448*a00^2*a02^4*a20^4*a22^18 - 1712*a00^2*a02^3*a20^23 + 
        394880*a00^2*a02^3*a20^19*a22^4 - 63443968*a00^2*a02^3*a20^15*a22^8 + 
        267665408*a00^2*a02^3*a20^11*a22^12 - 198311936*a00^2*a02^3*a20^7*a22^16 + 
        178192*a00^2*a02^2*a20^22*a22^2 + 3374528*a00^2*a02^2*a20^18*a22^6 - 
        19898368*a00^2*a02^2*a20^14*a22^10 + 44580864*a00^2*a02^2*a20^10*a22^14 - 
        27262976*a00^2*a02^2*a20^6*a22^18 + 284*a00^2*a02*a20^25 - 64608*a00^2*a02*a20^21*a22^4
        - 413696*a00^2*a02*a20^17*a22^8 - 1081344*a00^2*a02*a20^13*a22^12 + 
        4718592*a00^2*a02*a20^9*a22^16 - 3145728*a00^2*a02*a20^5*a22^20 - 
        1564*a00^2*a20^24*a22^2 + 61440*a00^2*a20^20*a22^6 - 323584*a00^2*a20^16*a22^10 + 
        524288*a00^2*a20^12*a22^14 - 262144*a00^2*a20^8*a22^18 - a02^28 - 14*a02^26*a20^2 + 
        284*a02^25*a20*a22^2 - 91*a02^24*a20^4 - 1712*a02^23*a20^3*a22^2 - 364*a02^22*a20^6 - 
        24400*a02^22*a20^2*a22^4 - 16072*a02^21*a20^5*a22^2 - 1280*a02^21*a20*a22^6 - 
        1001*a02^20*a20^8 + 268000*a02^20*a20^4*a22^4 - 36848*a02^19*a20^7*a22^2 + 
        892608*a02^19*a20^3*a22^6 - 2002*a02^18*a20^10 - 737552*a02^18*a20^6*a22^4 + 
        128000*a02^18*a20^2*a22^8 - 15068*a02^17*a20^9*a22^2 - 10410752*a02^17*a20^5*a22^6 + 
        1024*a02^17*a20*a22^10 - 3003*a02^16*a20^12 - 2616704*a02^16*a20^8*a22^4 - 
        15319808*a02^16*a20^4*a22^8 + 67232*a02^15*a20^11*a22^2 + 67730688*a02^15*a20^7*a22^6
        - 4390912*a02^15*a20^3*a22^10 - 3432*a02^14*a20^14 + 1069152*a02^14*a20^10*a22^4 + 
        144203264*a02^14*a20^6*a22^8 - 233472*a02^14*a20^2*a22^12 + 
        119056*a02^13*a20^13*a22^2 - 258600960*a02^13*a20^9*a22^6 + 
        133039104*a02^13*a20^5*a22^10 - 3003*a02^12*a20^16 + 5311808*a02^12*a20^12*a22^4 - 
        595029248*a02^12*a20^8*a22^8 + 58269696*a02^12*a20^4*a22^12 + 
        67232*a02^11*a20^15*a22^2 + 398469248*a02^11*a20^11*a22^6 - 
        777039872*a02^11*a20^7*a22^10 + 9256960*a02^11*a20^3*a22^14 - 2002*a02^10*a20^18 + 
        1069152*a02^10*a20^14*a22^4 + 906558464*a02^10*a20^10*a22^8 - 
        608821248*a02^10*a20^6*a22^12 + 131072*a02^10*a20^2*a22^16 - 15068*a02^9*a20^17*a22^2 -
        258600960*a02^9*a20^13*a22^6 + 1283231744*a02^9*a20^9*a22^10 - 
        300154880*a02^9*a20^5*a22^14 - 1001*a02^8*a20^20 - 2616704*a02^8*a20^16*a22^4 - 
        595029248*a02^8*a20^12*a22^8 + 1241702400*a02^8*a20^8*a22^12 - 
        81461248*a02^8*a20^4*a22^16 - 36848*a02^7*a20^19*a22^2 + 67730688*a02^7*a20^15*a22^6 -
        777039872*a02^7*a20^11*a22^10 + 910540800*a02^7*a20^7*a22^14 - 
        9961472*a02^7*a20^3*a22^18 - 364*a02^6*a20^22 - 737552*a02^6*a20^18*a22^4 + 
        144203264*a02^6*a20^14*a22^8 - 608821248*a02^6*a20^10*a22^12 + 
        480903168*a02^6*a20^6*a22^16 - 16072*a02^5*a20^21*a22^2 - 10410752*a02^5*a20^17*a22^6 +
        133039104*a02^5*a20^13*a22^10 - 300154880*a02^5*a20^9*a22^14 + 
        174587904*a02^5*a20^5*a22^18 - 91*a02^4*a20^24 + 268000*a02^4*a20^20*a22^4 - 
        15319808*a02^4*a20^16*a22^8 + 58269696*a02^4*a20^12*a22^12 - 
        81461248*a02^4*a20^8*a22^16 + 37748736*a02^4*a20^4*a22^20 - 1712*a02^3*a20^23*a22^2 +
        892608*a02^3*a20^19*a22^6 - 4390912*a02^3*a20^15*a22^10 + 9256960*a02^3*a20^11*a22^14 -
        9961472*a02^3*a20^7*a22^18 + 4194304*a02^3*a20^3*a22^22 - 14*a02^2*a20^26 - 
        24400*a02^2*a20^22*a22^4 + 128000*a02^2*a20^18*a22^8 - 233472*a02^2*a20^14*a22^12 + 
        131072*a02^2*a20^10*a22^16 + 284*a02*a20^25*a22^2 - 1280*a02*a20^21*a22^6 + 
        1024*a02*a20^17*a22^10 - a20^28
        @};
end function;
