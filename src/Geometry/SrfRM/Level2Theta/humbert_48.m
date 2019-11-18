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

function Level2ThetaNullHumbertPolynomials48(R)
    P<a00,a02,a20,a22> := PolynomialRing(R, 4 : Global);
    //print "Warning: returning only one component.";
    return {@
        67108864*a00^26*a02^6 + 536870912*a00^25*a02^7 - 33554432*a00^25*a02^3*a20^4 - 
        33554432*a00^25*a02^3*a22^4 + 2281701376*a00^24*a02^8 - 268435456*a00^24*a02^4*a20^4 -
        100663296*a00^24*a02^4*a20^2*a22^2 - 268435456*a00^24*a02^4*a22^4 + 
        16777216*a00^24*a20^4*a22^4 + 6979321856*a00^23*a02^9 - 
        1140850688*a00^23*a02^5*a20^4 - 738197504*a00^23*a02^5*a20^2*a22^2 - 
        1140850688*a00^23*a02^5*a22^4 + 25165824*a00^23*a02*a20^6*a22^2 + 
        134217728*a00^23*a02*a20^4*a22^4 + 25165824*a00^23*a02*a20^2*a22^6 + 
        16978542592*a00^22*a02^10 - 3657433088*a00^22*a02^6*a20^4 - 
        2952790016*a00^22*a02^6*a20^2*a22^2 - 3657433088*a00^22*a02^6*a22^4 + 
        184549376*a00^22*a02^2*a20^6*a22^2 + 608174080*a00^22*a02^2*a20^4*a22^4 + 
        184549376*a00^22*a02^2*a20^2*a22^6 + 34359738368*a00^21*a02^11 - 
        9462349824*a00^21*a02^7*a20^4 - 10670309376*a00^21*a02^7*a20^2*a22^2 - 
        9462349824*a00^21*a02^7*a22^4 + 92274688*a00^21*a02^3*a20^8 + 
        752877568*a00^21*a02^3*a20^6*a22^2 + 2147483648*a00^21*a02^3*a20^4*a22^4 + 
        752877568*a00^21*a02^3*a20^2*a22^6 + 92274688*a00^21*a02^3*a22^8 + 
        59592671232*a00^20*a02^12 - 19864223744*a00^20*a02^8*a20^4 - 
        35668361216*a00^20*a02^8*a20^2*a22^2 - 19864223744*a00^20*a02^8*a22^4 + 
        543162368*a00^20*a02^4*a20^8 + 3510632448*a00^20*a02^4*a20^6*a22^2 + 
        6077546496*a00^20*a02^4*a20^4*a22^4 + 3510632448*a00^20*a02^4*a20^2*a22^6 + 
        543162368*a00^20*a02^4*a22^8 + 1048576*a00^20*a20^10*a22^2 - 
        41943040*a00^20*a20^8*a22^4 - 16777216*a00^20*a20^6*a22^6 - 
        41943040*a00^20*a20^4*a22^8 + 1048576*a00^20*a20^2*a22^10 + 
        90194313216*a00^19*a02^13 - 34795945984*a00^19*a02^9*a20^4 - 
        97710505984*a00^19*a02^9*a20^2*a22^2 - 34795945984*a00^19*a02^9*a22^4 + 
        1544552448*a00^19*a02^5*a20^8 + 14338228224*a00^19*a02^5*a20^6*a22^2 + 
        16682844160*a00^19*a02^5*a20^4*a22^4 + 14338228224*a00^19*a02^5*a20^2*a22^6 + 
        1544552448*a00^19*a02^5*a22^8 - 57671680*a00^19*a02*a20^10*a22^2 - 
        260571136*a00^19*a02*a20^8*a22^4 - 727711744*a00^19*a02*a20^6*a22^6 - 
        260571136*a00^19*a02*a20^4*a22^8 - 57671680*a00^19*a02*a20^2*a22^10 + 
        120393302016*a00^18*a02^14 - 52479131648*a00^18*a02^10*a20^4 - 
        214748364800*a00^18*a02^10*a20^2*a22^2 - 52479131648*a00^18*a02^10*a22^4 + 
        3175088128*a00^18*a02^6*a20^8 + 41137733632*a00^18*a02^6*a20^6*a22^2 + 
        51854180352*a00^18*a02^6*a20^4*a22^4 + 41137733632*a00^18*a02^6*a20^2*a22^6 + 
        3175088128*a00^18*a02^6*a22^8 - 524288*a00^18*a02^2*a20^12 - 
        305135616*a00^18*a02^2*a20^10*a22^2 - 1610088448*a00^18*a02^2*a20^8*a22^4 - 
        4829741056*a00^18*a02^2*a20^6*a22^6 - 1610088448*a00^18*a02^2*a20^4*a22^8 - 
        305135616*a00^18*a02^2*a20^2*a22^10 - 524288*a00^18*a02^2*a22^12 + 
        142807662592*a00^17*a02^15 - 69591891968*a00^17*a02^11*a20^4 - 
        387083927552*a00^17*a02^11*a20^2*a22^2 - 69591891968*a00^17*a02^11*a22^4 + 
        5157945344*a00^17*a02^7*a20^8 + 92580872192*a00^17*a02^7*a20^6*a22^2 + 
        142365163520*a00^17*a02^7*a20^4*a22^4 + 92580872192*a00^17*a02^7*a20^2*a22^6 + 
        5157945344*a00^17*a02^7*a22^8 - 95944704*a00^17*a02^3*a20^12 + 
        66322432*a00^17*a02^3*a20^10*a22^2 - 10040115200*a00^17*a02^3*a20^8*a22^4 - 
        16482041856*a00^17*a02^3*a20^6*a22^6 - 10040115200*a00^17*a02^3*a20^4*a22^8 + 
        66322432*a00^17*a02^3*a20^2*a22^10 - 95944704*a00^17*a02^3*a22^12 + 
        151129161728*a00^16*a02^16 - 82946555904*a00^16*a02^12*a20^4 - 
        582706266112*a00^16*a02^12*a20^2*a22^2 - 82946555904*a00^16*a02^12*a22^4 + 
        6845104128*a00^16*a02^8*a20^8 + 172352339968*a00^16*a02^8*a20^6*a22^2 + 
        332977405952*a00^16*a02^8*a20^4*a22^4 + 172352339968*a00^16*a02^8*a20^2*a22^6 + 
        6845104128*a00^16*a02^8*a22^8 - 276299776*a00^16*a02^4*a20^12 + 
        662700032*a00^16*a02^4*a20^10*a22^2 - 34217656320*a00^16*a02^4*a20^8*a22^4 - 
        51797557248*a00^16*a02^4*a20^6*a22^6 - 34217656320*a00^16*a02^4*a20^4*a22^8 + 
        662700032*a00^16*a02^4*a20^2*a22^10 - 276299776*a00^16*a02^4*a22^12 - 
        2359296*a00^16*a20^14*a22^2 + 35913728*a00^16*a20^12*a22^4 - 
        391380992*a00^16*a20^10*a22^6 + 1397293056*a00^16*a20^8*a22^8 - 
        391380992*a00^16*a20^6*a22^10 + 35913728*a00^16*a20^4*a22^12 - 
        2359296*a00^16*a20^2*a22^14 + 142807662592*a00^15*a02^17 - 
        91133837312*a00^15*a02^13*a20^4 - 740747640832*a00^15*a02^13*a20^2*a22^2 - 
        91133837312*a00^15*a02^13*a22^4 + 6548357120*a00^15*a02^9*a20^8 + 
        288672972800*a00^15*a02^9*a20^6*a22^2 + 641172766720*a00^15*a02^9*a20^4*a22^4 + 
        288672972800*a00^15*a02^9*a20^2*a22^6 + 6548357120*a00^15*a02^9*a22^8 - 
        293863424*a00^15*a02^5*a20^12 - 510394368*a00^15*a02^5*a20^10*a22^2 - 
        95965413376*a00^15*a02^5*a20^8*a22^4 - 131171090432*a00^15*a02^5*a20^6*a22^6 - 
        95965413376*a00^15*a02^5*a20^4*a22^8 - 510394368*a00^15*a02^5*a20^2*a22^10 - 
        293863424*a00^15*a02^5*a22^12 + 48693248*a00^15*a02*a20^14*a22^2 - 
        543227904*a00^15*a02*a20^12*a22^4 + 1006829568*a00^15*a02*a20^10*a22^6 + 
        6490554368*a00^15*a02*a20^8*a22^8 + 1006829568*a00^15*a02*a20^6*a22^10 - 
        543227904*a00^15*a02*a20^4*a22^12 + 48693248*a00^15*a02*a20^2*a22^14 + 
        120393302016*a00^14*a02^18 - 93885300736*a00^14*a02^14*a20^4 - 
        801548271616*a00^14*a02^14*a20^2*a22^2 - 93885300736*a00^14*a02^14*a22^4 + 
        8099201024*a00^14*a02^10*a20^8 + 420386701312*a00^14*a02^10*a20^6*a22^2 + 
        1045975531520*a00^14*a02^10*a20^4*a22^4 + 420386701312*a00^14*a02^10*a20^2*a22^6 + 
        8099201024*a00^14*a02^10*a22^8 + 770703360*a00^14*a02^6*a20^12 - 
        13176406016*a00^14*a02^6*a20^10*a22^2 - 213824569344*a00^14*a02^6*a20^8*a22^4 - 
        310483353600*a00^14*a02^6*a20^6*a22^6 - 213824569344*a00^14*a02^6*a20^4*a22^8 - 
        13176406016*a00^14*a02^6*a20^2*a22^10 + 770703360*a00^14*a02^6*a22^12 + 
        1064960*a00^14*a02^2*a20^16 + 87818240*a00^14*a02^2*a20^14*a22^2 - 
        1366786048*a00^14*a02^2*a20^12*a22^4 + 7572422656*a00^14*a02^2*a20^10*a22^6 + 
        28137127936*a00^14*a02^2*a20^8*a22^8 + 7572422656*a00^14*a02^2*a20^6*a22^10 - 
        1366786048*a00^14*a02^2*a20^4*a22^12 + 87818240*a00^14*a02^2*a20^2*a22^14 + 
        1064960*a00^14*a02^2*a22^16 + 90194313216*a00^13*a02^19 - 
        91133837312*a00^13*a02^15*a20^4 - 740747640832*a00^13*a02^15*a20^2*a22^2 - 
        91133837312*a00^13*a02^15*a22^4 + 9205448704*a00^13*a02^11*a20^8 + 
        544227721216*a00^13*a02^11*a20^6*a22^2 + 1394373296128*a00^13*a02^11*a20^4*a22^4 + 
        544227721216*a00^13*a02^11*a20^2*a22^6 + 9205448704*a00^13*a02^11*a22^8 + 
        1578893312*a00^13*a02^7*a20^12 - 38580518912*a00^13*a02^7*a20^10*a22^2 - 
        421600690176*a00^13*a02^7*a20^8*a22^4 - 624072065024*a00^13*a02^7*a20^6*a22^6 - 
        421600690176*a00^13*a02^7*a20^4*a22^8 - 38580518912*a00^13*a02^7*a20^2*a22^10 + 
        1578893312*a00^13*a02^7*a22^12 + 44924928*a00^13*a02^3*a20^16 - 
        1230602240*a00^13*a02^3*a20^14*a22^2 + 666107904*a00^13*a02^3*a20^12*a22^4 + 
        36014882816*a00^13*a02^3*a20^10*a22^6 + 80370270208*a00^13*a02^3*a20^8*a22^8 + 
        36014882816*a00^13*a02^3*a20^6*a22^10 + 666107904*a00^13*a02^3*a20^4*a22^12 - 
        1230602240*a00^13*a02^3*a20^2*a22^14 + 44924928*a00^13*a02^3*a22^16 + 
        59592671232*a00^12*a02^20 - 82946555904*a00^12*a02^16*a20^4 - 
        582706266112*a00^12*a02^16*a20^2*a22^2 - 82946555904*a00^12*a02^16*a22^4 + 
        12067012608*a00^12*a02^12*a20^8 + 588871892992*a00^12*a02^12*a20^6*a22^2 + 
        1544502116352*a00^12*a02^12*a20^4*a22^4 + 588871892992*a00^12*a02^12*a20^2*a22^6 + 
        12067012608*a00^12*a02^12*a22^8 + 2650275840*a00^12*a02^8*a20^12 - 
        79969648640*a00^12*a02^8*a20^10*a22^2 - 691413712896*a00^12*a02^8*a20^8*a22^4 - 
        1066521329664*a00^12*a02^8*a20^6*a22^6 - 691413712896*a00^12*a02^8*a20^4*a22^8 - 
        79969648640*a00^12*a02^8*a20^2*a22^10 + 2650275840*a00^12*a02^8*a22^12 - 
        46166016*a00^12*a02^4*a20^16 - 4104355840*a00^12*a02^4*a20^14*a22^2 + 
        13028081664*a00^12*a02^4*a20^12*a22^4 + 114187534336*a00^12*a02^4*a20^10*a22^6 + 
        196127449088*a00^12*a02^4*a20^8*a22^8 + 114187534336*a00^12*a02^4*a20^6*a22^10 + 
        13028081664*a00^12*a02^4*a20^4*a22^12 - 4104355840*a00^12*a02^4*a20^2*a22^14 - 
        46166016*a00^12*a02^4*a22^16 + 1744896*a00^12*a20^18*a22^2 - 
        38141952*a00^12*a20^16*a22^4 + 592822272*a00^12*a20^14*a22^6 - 
        980090880*a00^12*a20^12*a22^8 - 729726976*a00^12*a20^10*a22^10 - 
        980090880*a00^12*a20^8*a22^12 + 592822272*a00^12*a20^6*a22^14 - 
        38141952*a00^12*a20^4*a22^16 + 1744896*a00^12*a20^2*a22^18 + 
        34359738368*a00^11*a02^21 - 69591891968*a00^11*a02^17*a20^4 - 
        387083927552*a00^11*a02^17*a20^2*a22^2 - 69591891968*a00^11*a02^17*a22^4 + 
        9205448704*a00^11*a02^13*a20^8 + 544227721216*a00^11*a02^13*a20^6*a22^2 + 
        1394373296128*a00^11*a02^13*a20^4*a22^4 + 544227721216*a00^11*a02^13*a20^2*a22^6 + 
        9205448704*a00^11*a02^13*a22^8 + 4246732800*a00^11*a02^9*a20^12 - 
        121844793344*a00^11*a02^9*a20^10*a22^2 - 938931650560*a00^11*a02^9*a20^8*a22^4 - 
        1480525873152*a00^11*a02^9*a20^6*a22^6 - 938931650560*a00^11*a02^9*a20^4*a22^8 - 
        121844793344*a00^11*a02^9*a20^2*a22^10 + 4246732800*a00^11*a02^9*a22^12 + 
        55443456*a00^11*a02^5*a20^16 - 9130573824*a00^11*a02^5*a20^14*a22^2 + 
        59727937536*a00^11*a02^5*a20^12*a22^4 + 255528763392*a00^11*a02^5*a20^10*a22^6 + 
        434248876032*a00^11*a02^5*a20^8*a22^8 + 255528763392*a00^11*a02^5*a20^6*a22^10 + 
        59727937536*a00^11*a02^5*a20^4*a22^12 - 9130573824*a00^11*a02^5*a20^2*a22^14 + 
        55443456*a00^11*a02^5*a22^16 - 2048*a00^11*a02*a20^20 - 
        21700608*a00^11*a02*a20^18*a22^2 + 794212352*a00^11*a02*a20^16*a22^4 + 
        98353152*a00^11*a02*a20^14*a22^6 - 3570184192*a00^11*a02*a20^12*a22^8 - 
        14062927872*a00^11*a02*a20^10*a22^10 - 3570184192*a00^11*a02*a20^8*a22^12 + 
        98353152*a00^11*a02*a20^6*a22^14 + 794212352*a00^11*a02*a20^4*a22^16 - 
        21700608*a00^11*a02*a20^2*a22^18 - 2048*a00^11*a02*a22^20 + 16978542592*a00^10*a02^22 -
        52479131648*a00^10*a02^18*a20^4 - 214748364800*a00^10*a02^18*a20^2*a22^2 - 
        52479131648*a00^10*a02^18*a22^4 + 8099201024*a00^10*a02^14*a20^8 + 
        420386701312*a00^10*a02^14*a20^6*a22^2 + 1045975531520*a00^10*a02^14*a20^4*a22^4 + 
        420386701312*a00^10*a02^14*a20^2*a22^6 + 8099201024*a00^10*a02^14*a22^8 + 
        4314890240*a00^10*a02^10*a20^12 - 136816099328*a00^10*a02^10*a20^10*a22^2 - 
        1046817538048*a00^10*a02^10*a20^8*a22^4 - 1646176239616*a00^10*a02^10*a20^6*a22^6 - 
        1046817538048*a00^10*a02^10*a20^4*a22^8 - 136816099328*a00^10*a02^10*a20^2*a22^10 + 
        4314890240*a00^10*a02^10*a22^12 - 692224000*a00^10*a02^6*a20^16 - 
        2966290432*a00^10*a02^6*a20^14*a22^2 + 124255764480*a00^10*a02^6*a20^12*a22^4 + 
        508058664960*a00^10*a02^6*a20^10*a22^6 + 720458219520*a00^10*a02^6*a20^8*a22^8 + 
        508058664960*a00^10*a02^6*a20^6*a22^10 + 124255764480*a00^10*a02^6*a20^4*a22^12 - 
        2966290432*a00^10*a02^6*a20^2*a22^14 - 692224000*a00^10*a02^6*a22^16 - 
        688128*a00^10*a02^2*a20^20 + 71200768*a00^10*a02^2*a20^18*a22^2 + 
        1572847616*a00^10*a02^2*a20^16*a22^4 + 1154105344*a00^10*a02^2*a20^14*a22^6 - 
        35106799616*a00^10*a02^2*a20^12*a22^8 - 41614663680*a00^10*a02^2*a20^10*a22^10 - 
        35106799616*a00^10*a02^2*a20^8*a22^12 + 1154105344*a00^10*a02^2*a20^6*a22^14 + 
        1572847616*a00^10*a02^2*a20^4*a22^16 + 71200768*a00^10*a02^2*a20^2*a22^18 - 
        688128*a00^10*a02^2*a22^20 + 6979321856*a00^9*a02^23 - 
        34795945984*a00^9*a02^19*a20^4 - 97710505984*a00^9*a02^19*a20^2*a22^2 - 
        34795945984*a00^9*a02^19*a22^4 + 6548357120*a00^9*a02^15*a20^8 + 
        288672972800*a00^9*a02^15*a20^6*a22^2 + 641172766720*a00^9*a02^15*a20^4*a22^4 + 
        288672972800*a00^9*a02^15*a20^2*a22^6 + 6548357120*a00^9*a02^15*a22^8 + 
        4246732800*a00^9*a02^11*a20^12 - 121844793344*a00^9*a02^11*a20^10*a22^2 - 
        938931650560*a00^9*a02^11*a20^8*a22^4 - 1480525873152*a00^9*a02^11*a20^6*a22^6 - 
        938931650560*a00^9*a02^11*a20^4*a22^8 - 121844793344*a00^9*a02^11*a20^2*a22^10 + 
        4246732800*a00^9*a02^11*a22^12 + 764968960*a00^9*a02^7*a20^16 + 
        160169984*a00^9*a02^7*a20^14*a22^2 + 228468785152*a00^9*a02^7*a20^12*a22^4 + 
        692743962624*a00^9*a02^7*a20^10*a22^6 + 1072331030528*a00^9*a02^7*a20^8*a22^8 + 
        692743962624*a00^9*a02^7*a20^6*a22^10 + 228468785152*a00^9*a02^7*a20^4*a22^12 + 
        160169984*a00^9*a02^7*a20^2*a22^14 + 764968960*a00^9*a02^7*a22^16 - 
        6963200*a00^9*a02^3*a20^20 + 230248448*a00^9*a02^3*a20^18*a22^2 + 
        3397672960*a00^9*a02^3*a20^16*a22^4 - 24178262016*a00^9*a02^3*a20^14*a22^6 - 
        79646695424*a00^9*a02^3*a20^12*a22^8 - 153524150272*a00^9*a02^3*a20^10*a22^10 - 
        79646695424*a00^9*a02^3*a20^8*a22^12 - 24178262016*a00^9*a02^3*a20^6*a22^14 + 
        3397672960*a00^9*a02^3*a20^4*a22^16 + 230248448*a00^9*a02^3*a20^2*a22^18 - 
        6963200*a00^9*a02^3*a22^20 + 2281701376*a00^8*a02^24 - 
        19864223744*a00^8*a02^20*a20^4 - 35668361216*a00^8*a02^20*a20^2*a22^2 - 
        19864223744*a00^8*a02^20*a22^4 + 6845104128*a00^8*a02^16*a20^8 + 
        172352339968*a00^8*a02^16*a20^6*a22^2 + 332977405952*a00^8*a02^16*a20^4*a22^4 + 
        172352339968*a00^8*a02^16*a20^2*a22^6 + 6845104128*a00^8*a02^16*a22^8 + 
        2650275840*a00^8*a02^12*a20^12 - 79969648640*a00^8*a02^12*a20^10*a22^2 - 
        691413712896*a00^8*a02^12*a20^8*a22^4 - 1066521329664*a00^8*a02^12*a20^6*a22^6 - 
        691413712896*a00^8*a02^12*a20^4*a22^8 - 79969648640*a00^8*a02^12*a20^2*a22^10 + 
        2650275840*a00^8*a02^12*a22^12 + 966615040*a00^8*a02^8*a20^16 + 
        11608981504*a00^8*a02^8*a20^14*a22^2 + 242250711040*a00^8*a02^8*a20^12*a22^4 + 
        838142328832*a00^8*a02^8*a20^10*a22^6 + 1139676430336*a00^8*a02^8*a20^8*a22^8 + 
        838142328832*a00^8*a02^8*a20^6*a22^10 + 242250711040*a00^8*a02^8*a20^4*a22^12 + 
        11608981504*a00^8*a02^8*a20^2*a22^14 + 966615040*a00^8*a02^8*a22^16 + 
        47755264*a00^8*a02^4*a20^20 + 499892224*a00^8*a02^4*a20^18*a22^2 - 
        5250748416*a00^8*a02^4*a20^16*a22^4 - 53453733888*a00^8*a02^4*a20^14*a22^6 - 
        215837810688*a00^8*a02^4*a20^12*a22^8 - 249834438656*a00^8*a02^4*a20^10*a22^10 - 
        215837810688*a00^8*a02^4*a20^8*a22^12 - 53453733888*a00^8*a02^4*a20^6*a22^14 - 
        5250748416*a00^8*a02^4*a20^4*a22^16 + 499892224*a00^8*a02^4*a20^2*a22^18 + 
        47755264*a00^8*a02^4*a22^20 - 460800*a00^8*a20^22*a22^2 + 27342336*a00^8*a20^20*a22^4 -
        105879552*a00^8*a20^18*a22^6 + 459597824*a00^8*a20^16*a22^8 + 
        1104486400*a00^8*a20^14*a22^10 + 1324794880*a00^8*a20^12*a22^12 + 
        1104486400*a00^8*a20^10*a22^14 + 459597824*a00^8*a20^8*a22^16 - 
        105879552*a00^8*a20^6*a22^18 + 27342336*a00^8*a20^4*a22^20 - 
        460800*a00^8*a20^2*a22^22 + 536870912*a00^7*a02^25 - 9462349824*a00^7*a02^21*a20^4 -
        10670309376*a00^7*a02^21*a20^2*a22^2 - 9462349824*a00^7*a02^21*a22^4 + 
        5157945344*a00^7*a02^17*a20^8 + 92580872192*a00^7*a02^17*a20^6*a22^2 + 
        142365163520*a00^7*a02^17*a20^4*a22^4 + 92580872192*a00^7*a02^17*a20^2*a22^6 + 
        5157945344*a00^7*a02^17*a22^8 + 1578893312*a00^7*a02^13*a20^12 - 
        38580518912*a00^7*a02^13*a20^10*a22^2 - 421600690176*a00^7*a02^13*a20^8*a22^4 - 
        624072065024*a00^7*a02^13*a20^6*a22^6 - 421600690176*a00^7*a02^13*a20^4*a22^8 - 
        38580518912*a00^7*a02^13*a20^2*a22^10 + 1578893312*a00^7*a02^13*a22^12 + 
        764968960*a00^7*a02^9*a20^16 + 160169984*a00^7*a02^9*a20^14*a22^2 + 
        228468785152*a00^7*a02^9*a20^12*a22^4 + 692743962624*a00^7*a02^9*a20^10*a22^6 + 
        1072331030528*a00^7*a02^9*a20^8*a22^8 + 692743962624*a00^7*a02^9*a20^6*a22^10 + 
        228468785152*a00^7*a02^9*a20^4*a22^12 + 160169984*a00^7*a02^9*a20^2*a22^14 + 
        764968960*a00^7*a02^9*a22^16 - 151468032*a00^7*a02^5*a20^20 + 
        376229888*a00^7*a02^5*a20^18*a22^2 - 12994910208*a00^7*a02^5*a20^16*a22^4 - 
        124461105152*a00^7*a02^5*a20^14*a22^6 - 279579602944*a00^7*a02^5*a20^12*a22^8 - 
        442252009472*a00^7*a02^5*a20^10*a22^10 - 279579602944*a00^7*a02^5*a20^8*a22^12 - 
        124461105152*a00^7*a02^5*a20^6*a22^14 - 12994910208*a00^7*a02^5*a20^4*a22^16 + 
        376229888*a00^7*a02^5*a20^2*a22^18 - 151468032*a00^7*a02^5*a22^20 + 
        2816*a00^7*a02*a20^24 + 5797376*a00^7*a02*a20^22*a22^2 - 
        101981696*a00^7*a02*a20^20*a22^4 + 1010040320*a00^7*a02*a20^18*a22^6 + 
        2333005056*a00^7*a02*a20^16*a22^8 + 7760350208*a00^7*a02*a20^14*a22^10 + 
        12345310208*a00^7*a02*a20^12*a22^12 + 7760350208*a00^7*a02*a20^10*a22^14 + 
        2333005056*a00^7*a02*a20^8*a22^16 + 1010040320*a00^7*a02*a20^6*a22^18 - 
        101981696*a00^7*a02*a20^4*a22^20 + 5797376*a00^7*a02*a20^2*a22^22 + 
        2816*a00^7*a02*a22^24 + 67108864*a00^6*a02^26 - 3657433088*a00^6*a02^22*a20^4 - 
        2952790016*a00^6*a02^22*a20^2*a22^2 - 3657433088*a00^6*a02^22*a22^4 + 
        3175088128*a00^6*a02^18*a20^8 + 41137733632*a00^6*a02^18*a20^6*a22^2 + 
        51854180352*a00^6*a02^18*a20^4*a22^4 + 41137733632*a00^6*a02^18*a20^2*a22^6 + 
        3175088128*a00^6*a02^18*a22^8 + 770703360*a00^6*a02^14*a20^12 - 
        13176406016*a00^6*a02^14*a20^10*a22^2 - 213824569344*a00^6*a02^14*a20^8*a22^4 - 
        310483353600*a00^6*a02^14*a20^6*a22^6 - 213824569344*a00^6*a02^14*a20^4*a22^8 - 
        13176406016*a00^6*a02^14*a20^2*a22^10 + 770703360*a00^6*a02^14*a22^12 - 
        692224000*a00^6*a02^10*a20^16 - 2966290432*a00^6*a02^10*a20^14*a22^2 + 
        124255764480*a00^6*a02^10*a20^12*a22^4 + 508058664960*a00^6*a02^10*a20^10*a22^6 + 
        720458219520*a00^6*a02^10*a20^8*a22^8 + 508058664960*a00^6*a02^10*a20^6*a22^10 + 
        124255764480*a00^6*a02^10*a20^4*a22^12 - 2966290432*a00^6*a02^10*a20^2*a22^14 - 
        692224000*a00^6*a02^10*a22^16 + 252878848*a00^6*a02^6*a20^20 - 
        1301782528*a00^6*a02^6*a20^18*a22^2 - 22779289600*a00^6*a02^6*a20^16*a22^4 - 
        124650094592*a00^6*a02^6*a20^14*a22^6 - 379755315200*a00^6*a02^6*a20^12*a22^8 - 
        430799437824*a00^6*a02^6*a20^10*a22^10 - 379755315200*a00^6*a02^6*a20^8*a22^12 - 
        124650094592*a00^6*a02^6*a20^6*a22^14 - 22779289600*a00^6*a02^6*a20^4*a22^16 - 
        1301782528*a00^6*a02^6*a20^2*a22^18 + 252878848*a00^6*a02^6*a22^20 + 
        142720*a00^6*a02^2*a20^24 - 41934336*a00^6*a02^2*a20^22*a22^2 + 
        510540544*a00^6*a02^2*a20^20*a22^4 + 656775680*a00^6*a02^2*a20^18*a22^6 + 
        11233819264*a00^6*a02^2*a20^16*a22^8 + 29001401344*a00^6*a02^2*a20^14*a22^10 + 
        37537593856*a00^6*a02^2*a20^12*a22^12 + 29001401344*a00^6*a02^2*a20^10*a22^14 + 
        11233819264*a00^6*a02^2*a20^8*a22^16 + 656775680*a00^6*a02^2*a20^6*a22^18 + 
        510540544*a00^6*a02^2*a20^4*a22^20 - 41934336*a00^6*a02^2*a20^2*a22^22 + 
        142720*a00^6*a02^2*a22^24 - 1140850688*a00^5*a02^23*a20^4 - 
        738197504*a00^5*a02^23*a20^2*a22^2 - 1140850688*a00^5*a02^23*a22^4 + 
        1544552448*a00^5*a02^19*a20^8 + 14338228224*a00^5*a02^19*a20^6*a22^2 + 
        16682844160*a00^5*a02^19*a20^4*a22^4 + 14338228224*a00^5*a02^19*a20^2*a22^6 + 
        1544552448*a00^5*a02^19*a22^8 - 293863424*a00^5*a02^15*a20^12 - 
        510394368*a00^5*a02^15*a20^10*a22^2 - 95965413376*a00^5*a02^15*a20^8*a22^4 - 
        131171090432*a00^5*a02^15*a20^6*a22^6 - 95965413376*a00^5*a02^15*a20^4*a22^8 - 
        510394368*a00^5*a02^15*a20^2*a22^10 - 293863424*a00^5*a02^15*a22^12 + 
        55443456*a00^5*a02^11*a20^16 - 9130573824*a00^5*a02^11*a20^14*a22^2 + 
        59727937536*a00^5*a02^11*a20^12*a22^4 + 255528763392*a00^5*a02^11*a20^10*a22^6 + 
        434248876032*a00^5*a02^11*a20^8*a22^8 + 255528763392*a00^5*a02^11*a20^6*a22^10 + 
        59727937536*a00^5*a02^11*a20^4*a22^12 - 9130573824*a00^5*a02^11*a20^2*a22^14 + 
        55443456*a00^5*a02^11*a22^16 - 151468032*a00^5*a02^7*a20^20 + 
        376229888*a00^5*a02^7*a20^18*a22^2 - 12994910208*a00^5*a02^7*a20^16*a22^4 - 
        124461105152*a00^5*a02^7*a20^14*a22^6 - 279579602944*a00^5*a02^7*a20^12*a22^8 - 
        442252009472*a00^5*a02^7*a20^10*a22^10 - 279579602944*a00^5*a02^7*a20^8*a22^12 - 
        124461105152*a00^5*a02^7*a20^6*a22^14 - 12994910208*a00^5*a02^7*a20^4*a22^16 + 
        376229888*a00^5*a02^7*a20^2*a22^18 - 151468032*a00^5*a02^7*a22^20 - 
        719104*a00^5*a02^3*a20^24 + 153899520*a00^5*a02^3*a20^22*a22^2 - 
        415694336*a00^5*a02^3*a20^20*a22^4 + 5406829056*a00^5*a02^3*a20^18*a22^6 + 
        20128594176*a00^5*a02^3*a20^16*a22^8 + 55116039168*a00^5*a02^3*a20^14*a22^10 + 
        79740271616*a00^5*a02^3*a20^12*a22^12 + 55116039168*a00^5*a02^3*a20^10*a22^14 + 
        20128594176*a00^5*a02^3*a20^8*a22^16 + 5406829056*a00^5*a02^3*a20^6*a22^18 - 
        415694336*a00^5*a02^3*a20^4*a22^20 + 153899520*a00^5*a02^3*a20^2*a22^22 - 
        719104*a00^5*a02^3*a22^24 - 268435456*a00^4*a02^24*a20^4 - 
        100663296*a00^4*a02^24*a20^2*a22^2 - 268435456*a00^4*a02^24*a22^4 + 
        543162368*a00^4*a02^20*a20^8 + 3510632448*a00^4*a02^20*a20^6*a22^2 + 
        6077546496*a00^4*a02^20*a20^4*a22^4 + 3510632448*a00^4*a02^20*a20^2*a22^6 + 
        543162368*a00^4*a02^20*a22^8 - 276299776*a00^4*a02^16*a20^12 + 
        662700032*a00^4*a02^16*a20^10*a22^2 - 34217656320*a00^4*a02^16*a20^8*a22^4 - 
        51797557248*a00^4*a02^16*a20^6*a22^6 - 34217656320*a00^4*a02^16*a20^4*a22^8 + 
        662700032*a00^4*a02^16*a20^2*a22^10 - 276299776*a00^4*a02^16*a22^12 - 
        46166016*a00^4*a02^12*a20^16 - 4104355840*a00^4*a02^12*a20^14*a22^2 + 
        13028081664*a00^4*a02^12*a20^12*a22^4 + 114187534336*a00^4*a02^12*a20^10*a22^6 + 
        196127449088*a00^4*a02^12*a20^8*a22^8 + 114187534336*a00^4*a02^12*a20^6*a22^10 + 
        13028081664*a00^4*a02^12*a20^4*a22^12 - 4104355840*a00^4*a02^12*a20^2*a22^14 - 
        46166016*a00^4*a02^12*a22^16 + 47755264*a00^4*a02^8*a20^20 + 
        499892224*a00^4*a02^8*a20^18*a22^2 - 5250748416*a00^4*a02^8*a20^16*a22^4 - 
        53453733888*a00^4*a02^8*a20^14*a22^6 - 215837810688*a00^4*a02^8*a20^12*a22^8 - 
        249834438656*a00^4*a02^8*a20^10*a22^10 - 215837810688*a00^4*a02^8*a20^8*a22^12 - 
        53453733888*a00^4*a02^8*a20^6*a22^14 - 5250748416*a00^4*a02^8*a20^4*a22^16 + 
        499892224*a00^4*a02^8*a20^2*a22^18 + 47755264*a00^4*a02^8*a22^20 + 
        1466624*a00^4*a02^4*a20^24 - 202261504*a00^4*a02^4*a20^22*a22^2 + 
        1374230016*a00^4*a02^4*a20^20*a22^4 + 3644337152*a00^4*a02^4*a20^18*a22^6 + 
        28195471104*a00^4*a02^4*a20^16*a22^8 + 70973986816*a00^4*a02^4*a20^14*a22^10 + 
        92673250304*a00^4*a02^4*a20^12*a22^12 + 70973986816*a00^4*a02^4*a20^10*a22^14 + 
        28195471104*a00^4*a02^4*a20^8*a22^16 + 3644337152*a00^4*a02^4*a20^6*a22^18 + 
        1374230016*a00^4*a02^4*a20^4*a22^20 - 202261504*a00^4*a02^4*a20^2*a22^22 + 
        1466624*a00^4*a02^4*a22^24 + 29248*a00^4*a20^26*a22^2 + 1492224*a00^4*a20^24*a22^4 + 
        11416704*a00^4*a20^22*a22^6 + 4157696*a00^4*a20^20*a22^8 - 
        62527040*a00^4*a20^18*a22^10 - 8336896*a00^4*a20^16*a22^12 + 
        107536128*a00^4*a20^14*a22^14 - 8336896*a00^4*a20^12*a22^16 - 
        62527040*a00^4*a20^10*a22^18 + 4157696*a00^4*a20^8*a22^20 + 
        11416704*a00^4*a20^6*a22^22 + 1492224*a00^4*a20^4*a22^24 + 29248*a00^4*a20^2*a22^26 -
        33554432*a00^3*a02^25*a20^4 - 33554432*a00^3*a02^25*a22^4 + 
        92274688*a00^3*a02^21*a20^8 + 752877568*a00^3*a02^21*a20^6*a22^2 + 
        2147483648*a00^3*a02^21*a20^4*a22^4 + 752877568*a00^3*a02^21*a20^2*a22^6 + 
        92274688*a00^3*a02^21*a22^8 - 95944704*a00^3*a02^17*a20^12 + 
        66322432*a00^3*a02^17*a20^10*a22^2 - 10040115200*a00^3*a02^17*a20^8*a22^4 - 
        16482041856*a00^3*a02^17*a20^6*a22^6 - 10040115200*a00^3*a02^17*a20^4*a22^8 + 
        66322432*a00^3*a02^17*a20^2*a22^10 - 95944704*a00^3*a02^17*a22^12 + 
        44924928*a00^3*a02^13*a20^16 - 1230602240*a00^3*a02^13*a20^14*a22^2 + 
        666107904*a00^3*a02^13*a20^12*a22^4 + 36014882816*a00^3*a02^13*a20^10*a22^6 + 
        80370270208*a00^3*a02^13*a20^8*a22^8 + 36014882816*a00^3*a02^13*a20^6*a22^10 + 
        666107904*a00^3*a02^13*a20^4*a22^12 - 1230602240*a00^3*a02^13*a20^2*a22^14 + 
        44924928*a00^3*a02^13*a22^16 - 6963200*a00^3*a02^9*a20^20 + 
        230248448*a00^3*a02^9*a20^18*a22^2 + 3397672960*a00^3*a02^9*a20^16*a22^4 - 
        24178262016*a00^3*a02^9*a20^14*a22^6 - 79646695424*a00^3*a02^9*a20^12*a22^8 - 
        153524150272*a00^3*a02^9*a20^10*a22^10 - 79646695424*a00^3*a02^9*a20^8*a22^12 - 
        24178262016*a00^3*a02^9*a20^6*a22^14 + 3397672960*a00^3*a02^9*a20^4*a22^16 + 
        230248448*a00^3*a02^9*a20^2*a22^18 - 6963200*a00^3*a02^9*a22^20 - 
        719104*a00^3*a02^5*a20^24 + 153899520*a00^3*a02^5*a20^22*a22^2 - 
        415694336*a00^3*a02^5*a20^20*a22^4 + 5406829056*a00^3*a02^5*a20^18*a22^6 + 
        20128594176*a00^3*a02^5*a20^16*a22^8 + 55116039168*a00^3*a02^5*a20^14*a22^10 + 
        79740271616*a00^3*a02^5*a20^12*a22^12 + 55116039168*a00^3*a02^5*a20^10*a22^14 + 
        20128594176*a00^3*a02^5*a20^8*a22^16 + 5406829056*a00^3*a02^5*a20^6*a22^18 - 
        415694336*a00^3*a02^5*a20^4*a22^20 + 153899520*a00^3*a02^5*a20^2*a22^22 - 
        719104*a00^3*a02^5*a22^24 - 800*a00^3*a02*a20^28 - 306496*a00^3*a02*a20^26*a22^2 - 
        8384608*a00^3*a02*a20^24*a22^4 - 43614336*a00^3*a02*a20^22*a22^6 + 
        5850080*a00^3*a02*a20^20*a22^8 + 215013696*a00^3*a02*a20^18*a22^10 + 
        5812128*a00^3*a02*a20^16*a22^12 - 348739328*a00^3*a02*a20^14*a22^14 + 
        5812128*a00^3*a02*a20^12*a22^16 + 215013696*a00^3*a02*a20^10*a22^18 + 
        5850080*a00^3*a02*a20^8*a22^20 - 43614336*a00^3*a02*a20^6*a22^22 - 
        8384608*a00^3*a02*a20^4*a22^24 - 306496*a00^3*a02*a20^2*a22^26 - 800*a00^3*a02*a22^28 +
        184549376*a00^2*a02^22*a20^6*a22^2 + 608174080*a00^2*a02^22*a20^4*a22^4 + 
        184549376*a00^2*a02^22*a20^2*a22^6 - 524288*a00^2*a02^18*a20^12 - 
        305135616*a00^2*a02^18*a20^10*a22^2 - 1610088448*a00^2*a02^18*a20^8*a22^4 - 
        4829741056*a00^2*a02^18*a20^6*a22^6 - 1610088448*a00^2*a02^18*a20^4*a22^8 - 
        305135616*a00^2*a02^18*a20^2*a22^10 - 524288*a00^2*a02^18*a22^12 + 
        1064960*a00^2*a02^14*a20^16 + 87818240*a00^2*a02^14*a20^14*a22^2 - 
        1366786048*a00^2*a02^14*a20^12*a22^4 + 7572422656*a00^2*a02^14*a20^10*a22^6 + 
        28137127936*a00^2*a02^14*a20^8*a22^8 + 7572422656*a00^2*a02^14*a20^6*a22^10 - 
        1366786048*a00^2*a02^14*a20^4*a22^12 + 87818240*a00^2*a02^14*a20^2*a22^14 + 
        1064960*a00^2*a02^14*a22^16 - 688128*a00^2*a02^10*a20^20 + 
        71200768*a00^2*a02^10*a20^18*a22^2 + 1572847616*a00^2*a02^10*a20^16*a22^4 + 
        1154105344*a00^2*a02^10*a20^14*a22^6 - 35106799616*a00^2*a02^10*a20^12*a22^8 - 
        41614663680*a00^2*a02^10*a20^10*a22^10 - 35106799616*a00^2*a02^10*a20^8*a22^12 + 
        1154105344*a00^2*a02^10*a20^6*a22^14 + 1572847616*a00^2*a02^10*a20^4*a22^16 + 
        71200768*a00^2*a02^10*a20^2*a22^18 - 688128*a00^2*a02^10*a22^20 + 
        142720*a00^2*a02^6*a20^24 - 41934336*a00^2*a02^6*a20^22*a22^2 + 
        510540544*a00^2*a02^6*a20^20*a22^4 + 656775680*a00^2*a02^6*a20^18*a22^6 + 
        11233819264*a00^2*a02^6*a20^16*a22^8 + 29001401344*a00^2*a02^6*a20^14*a22^10 + 
        37537593856*a00^2*a02^6*a20^12*a22^12 + 29001401344*a00^2*a02^6*a20^10*a22^14 + 
        11233819264*a00^2*a02^6*a20^8*a22^16 + 656775680*a00^2*a02^6*a20^6*a22^18 + 
        510540544*a00^2*a02^6*a20^4*a22^20 - 41934336*a00^2*a02^6*a20^2*a22^22 + 
        142720*a00^2*a02^6*a22^24 + 2624*a00^2*a02^2*a20^28 + 613888*a00^2*a02^2*a20^26*a22^2 +
        13779648*a00^2*a02^2*a20^24*a22^4 + 63121408*a00^2*a02^2*a20^22*a22^6 - 
        16598464*a00^2*a02^2*a20^20*a22^8 - 306179584*a00^2*a02^2*a20^18*a22^10 - 
        2557760*a00^2*a02^2*a20^16*a22^12 + 495636480*a00^2*a02^2*a20^14*a22^14 - 
        2557760*a00^2*a02^2*a20^12*a22^16 - 306179584*a00^2*a02^2*a20^10*a22^18 - 
        16598464*a00^2*a02^2*a20^8*a22^20 + 63121408*a00^2*a02^2*a20^6*a22^22 + 
        13779648*a00^2*a02^2*a20^4*a22^24 + 613888*a00^2*a02^2*a20^2*a22^26 + 
        2624*a00^2*a02^2*a22^28 + 25165824*a00*a02^23*a20^6*a22^2 + 
        134217728*a00*a02^23*a20^4*a22^4 + 25165824*a00*a02^23*a20^2*a22^6 - 
        57671680*a00*a02^19*a20^10*a22^2 - 260571136*a00*a02^19*a20^8*a22^4 - 
        727711744*a00*a02^19*a20^6*a22^6 - 260571136*a00*a02^19*a20^4*a22^8 - 
        57671680*a00*a02^19*a20^2*a22^10 + 48693248*a00*a02^15*a20^14*a22^2 - 
        543227904*a00*a02^15*a20^12*a22^4 + 1006829568*a00*a02^15*a20^10*a22^6 + 
        6490554368*a00*a02^15*a20^8*a22^8 + 1006829568*a00*a02^15*a20^6*a22^10 - 
        543227904*a00*a02^15*a20^4*a22^12 + 48693248*a00*a02^15*a20^2*a22^14 - 
        2048*a00*a02^11*a20^20 - 21700608*a00*a02^11*a20^18*a22^2 + 
        794212352*a00*a02^11*a20^16*a22^4 + 98353152*a00*a02^11*a20^14*a22^6 - 
        3570184192*a00*a02^11*a20^12*a22^8 - 14062927872*a00*a02^11*a20^10*a22^10 - 
        3570184192*a00*a02^11*a20^8*a22^12 + 98353152*a00*a02^11*a20^6*a22^14 + 
        794212352*a00*a02^11*a20^4*a22^16 - 21700608*a00*a02^11*a20^2*a22^18 - 
        2048*a00*a02^11*a22^20 + 2816*a00*a02^7*a20^24 + 5797376*a00*a02^7*a20^22*a22^2 - 
        101981696*a00*a02^7*a20^20*a22^4 + 1010040320*a00*a02^7*a20^18*a22^6 + 
        2333005056*a00*a02^7*a20^16*a22^8 + 7760350208*a00*a02^7*a20^14*a22^10 + 
        12345310208*a00*a02^7*a20^12*a22^12 + 7760350208*a00*a02^7*a20^10*a22^14 + 
        2333005056*a00*a02^7*a20^8*a22^16 + 1010040320*a00*a02^7*a20^6*a22^18 - 
        101981696*a00*a02^7*a20^4*a22^20 + 5797376*a00*a02^7*a20^2*a22^22 + 
        2816*a00*a02^7*a22^24 - 800*a00*a02^3*a20^28 - 306496*a00*a02^3*a20^26*a22^2 - 
        8384608*a00*a02^3*a20^24*a22^4 - 43614336*a00*a02^3*a20^22*a22^6 + 
        5850080*a00*a02^3*a20^20*a22^8 + 215013696*a00*a02^3*a20^18*a22^10 + 
        5812128*a00*a02^3*a20^16*a22^12 - 348739328*a00*a02^3*a20^14*a22^14 + 
        5812128*a00*a02^3*a20^12*a22^16 + 215013696*a00*a02^3*a20^10*a22^18 + 
        5850080*a00*a02^3*a20^8*a22^20 - 43614336*a00*a02^3*a20^6*a22^22 - 
        8384608*a00*a02^3*a20^4*a22^24 - 306496*a00*a02^3*a20^2*a22^26 - 800*a00*a02^3*a22^28 +
        16777216*a02^24*a20^4*a22^4 + 1048576*a02^20*a20^10*a22^2 - 
        41943040*a02^20*a20^8*a22^4 - 16777216*a02^20*a20^6*a22^6 - 
        41943040*a02^20*a20^4*a22^8 + 1048576*a02^20*a20^2*a22^10 - 
        2359296*a02^16*a20^14*a22^2 + 35913728*a02^16*a20^12*a22^4 - 
        391380992*a02^16*a20^10*a22^6 + 1397293056*a02^16*a20^8*a22^8 - 
        391380992*a02^16*a20^6*a22^10 + 35913728*a02^16*a20^4*a22^12 - 
        2359296*a02^16*a20^2*a22^14 + 1744896*a02^12*a20^18*a22^2 - 
        38141952*a02^12*a20^16*a22^4 + 592822272*a02^12*a20^14*a22^6 - 
        980090880*a02^12*a20^12*a22^8 - 729726976*a02^12*a20^10*a22^10 - 
        980090880*a02^12*a20^8*a22^12 + 592822272*a02^12*a20^6*a22^14 - 
        38141952*a02^12*a20^4*a22^16 + 1744896*a02^12*a20^2*a22^18 - 
        460800*a02^8*a20^22*a22^2 + 27342336*a02^8*a20^20*a22^4 - 
        105879552*a02^8*a20^18*a22^6 + 459597824*a02^8*a20^16*a22^8 + 
        1104486400*a02^8*a20^14*a22^10 + 1324794880*a02^8*a20^12*a22^12 + 
        1104486400*a02^8*a20^10*a22^14 + 459597824*a02^8*a20^8*a22^16 - 
        105879552*a02^8*a20^6*a22^18 + 27342336*a02^8*a20^4*a22^20 - 
        460800*a02^8*a20^2*a22^22 + 29248*a02^4*a20^26*a22^2 + 1492224*a02^4*a20^24*a22^4 + 
        11416704*a02^4*a20^22*a22^6 + 4157696*a02^4*a20^20*a22^8 - 
        62527040*a02^4*a20^18*a22^10 - 8336896*a02^4*a20^16*a22^12 + 
        107536128*a02^4*a20^14*a22^14 - 8336896*a02^4*a20^12*a22^16 - 
        62527040*a02^4*a20^10*a22^18 + 4157696*a02^4*a20^8*a22^20 + 
        11416704*a02^4*a20^6*a22^22 + 1492224*a02^4*a20^4*a22^24 + 29248*a02^4*a20^2*a22^26 +
        a20^32 - 16*a20^30*a22^2 + 120*a20^28*a22^4 - 560*a20^26*a22^6 + 1820*a20^24*a22^8 - 
        4368*a20^22*a22^10 + 8008*a20^20*a22^12 - 11440*a20^18*a22^14 + 12870*a20^16*a22^16 -
        11440*a20^14*a22^18 + 8008*a20^12*a22^20 - 4368*a20^10*a22^22 + 1820*a20^8*a22^24 -
        560*a20^6*a22^26 + 120*a20^4*a22^28 - 16*a20^2*a22^30 + a22^32
        @};
end function;
