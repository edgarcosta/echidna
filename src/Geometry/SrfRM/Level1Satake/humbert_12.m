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

function SatakeHumbertPolynomial12(R)
    P<s2,s3,s5,s6> := PolynomialRing(R,4); 
    return 15217218820079907703634605566381993601951334400000000*s6^10 - 
        27396255757700350949408352280573830336872448000000000*s6^9*s3^2 - 
        9875922801978646728866721566599396227809280000000000*s6^9*s2^3 + 
        15699803708404060035078514863617019811882598400000000*s6^8*s5^2*s2 - 
        6234298508699769683979880378088602158728478720000000*s6^8*s5*s3*s2^2 + 
        21996090690067475539174932438066814802460672000000000*s6^8*s3^4 + 
        15899209523105528408336216846251566945848524800000000*s6^8*s3^2*s2^3 + 
        2881686071123012146330285610002938914144256000000000*s6^8*s2^6 - 
        27988093580667363549890200197621666744474009600000000*s6^7*s5^3*s3 - 
        7218669216276600705998763470687422235698790400000000*s6^7*s5^2*s3^2*s2 - 
        7358028198018742484669655855004235756753387520000000*s6^7*s5^2*s2^4 + 
        10242510217518579224318494825637689023182929920000000*s6^7*s5*s3^3*s2^2 + 
        2715243904444371451851673323588506907731558400000000*s6^7*s5*s3*s2^5 - 
        10386974152712360760752789233875521334411264000000000*s6^7*s3^6 - 
        12444576653482339569711177927448187059883212800000000*s6^7*s3^4*s2^3 - 
        4017338869001008798498404694001317444583424000000000*s6^7*s3^2*s2^6 - 
        497848494756135865420754268902300446831411200000000*s6^7*s2^9 - 
        2380289585936659382344515428295502479501557760000000*s6^6*s5^4*s2^2 + 
        51171749326355156409151025638593206883346022400000000*s6^6*s5^3*s3^3 + 
        13692569508205671472135575127736086345122054144000000*s6^6*s5^3*s3*s2^3 - 
        23137189178890691545287814613899134584959795200000000*s6^6*s5^2*s3^4*s2 + 
        3357085081454240068634308391321496519004127232000000*s6^6*s5^2*s3^2*s2^4 + 
        1503683843756361905355348677973254444760956928000000*s6^6*s5^2*s2^7 - 
        607252196337237841863578974691330674120458240000000*s6^6*s5*s3^5*s2^2 - 
        4719332795575778888726983491983619557330780160000000*s6^6*s5*s3^3*s2^5 - 
        507408874212591806920351520507262382343454720000000*s6^6*s5*s3*s2^8 + 
        3198404190701375509641654176186710993403904000000000*s6^6*s3^8 + 
        5307539059217961009346814931486005454805401600000000*s6^6*s3^6*s2^3 + 
        3072156408625644730048727416731999385367347200000000*s6^6*s3^4*s2^6 + 
        580707233576615066114027740520725013436825600000000*s6^6*s3^2*s2^9 + 
        56396654817925101754903763142376992079872000000000*s6^6*s2^12 + 
        4433344277243600310483939494033048483596861440000000*s6^5*s5^6 - 
        5074701276279120162653987833881491513718865920000000*s6^5*s5^5*s3*s2 + 
        6375003022204618173595436167459020781104660480000000*s6^5*s5^4*s3^2*s2^2 + 
        701496972842673731563376561131958456159557386240000*s6^5*s5^4*s2^5 - 
        37998152941083958394352616318606963053586022400000000*s6^5*s5^3*s3^5 - 
        25520083536909503120936160360527647075926540288000000*s6^5*s5^3*s3^3*s2^3 - 
        2539968718718341395717843817007988607239900364800000*s6^5*s5^3*s3*s2^6 + 
        27097141072273879757502857583227219678645452800000000*s6^5*s5^2*s3^6*s2 + 
        11772412688669027828909110784064162987472060416000000*s6^5*s5^2*s3^4*s2^4 - 
        842728269944133139785391970208401706486595584000000*s6^5*s5^2*s3^2*s2^7 - 
        174945707986039132277152408504243576928993280000000*s6^5*s5^2*s2^10 - 
        5291749031601311055279384163548003240341667840000000*s6^5*s5*s3^7*s2^2 - 
        466449327020666209335598762985311513639649280000000*s6^5*s5*s3^5*s2^5 + 
        975768042059414495313979089861092710463569920000000*s6^5*s5*s3^3*s2^8 + 
        52783886046770916368443088303768408288133120000000*s6^5*s5*s3*s2^11 - 
        671651892450040514503574483283745378507161600000000*s6^5*s3^10 - 
        1003201884211306765979256565656744932828774400000000*s6^5*s3^8*s2^3 - 
        1080885477420722553770430334445251528124006400000000*s6^5*s3^6*s2^6 - 
        436502440239923022174940074629349549146112000000000*s6^5*s3^4*s2^9 - 
        52918920636532962830689639845332340493516800000000*s6^5*s3^2*s2^12 - 
        4377232732142394787323880058946743476224000000000*s6^5*s2^15 - 
        7054569603722986123155631468852907567008972800000000*s6^4*s5^6*s3^2 - 
        2020964134642594551151967739699964237924270080000000*s6^4*s5^6*s2^3 + 
        8216259809548678958771104820913500836803379200000000*s6^4*s5^5*s3^3*s2 + 
        4093137344967746617257724808599163600042459136000000*s6^4*s5^5*s3*s2^4 - 
        2966610461991565706196785100264328586801971200000000*s6^4*s5^4*s3^4*s2^2 - 
        5309057102001861349519302200625367645333487616000000*s6^4*s5^4*s3^2*s2^5 - 
        81341044567807653378339376101760050257933107200000*s6^4*s5^4*s2^8 + 
        15029623159197829090048701283615039782125568000000000*s6^4*s5^3*s3^7 + 
        12372904855700229916645615564709765843244810240000000*s6^4*s5^3*s3^5*s2^3 + 
        7088209596438562927366884903647751360835328409600000*s6^4*s5^3*s3^3*s2^6 + 
        233223500195941895405364716810871968084734771200000*s6^4*s5^3*s3*s2^9 - 
        12807524554324905824847155176965601033715712000000000*s6^4*s5^2*s3^8*s2 - 
        8769188942967524052485246007177314795236884480000000*s6^4*s5^2*s3^6*s2^4 - 
        3033323736998833486668410457105130302191173632000000*s6^4*s5^2*s3^4*s2^7 + 
        126715662085342360872426127905299583231590400000000*s6^4*s5^2*s3^2*s2^10 + 
        12668598698572624534998424598899995605729280000000*s6^4*s5^2*s2^13 + 
        3418570902321126079306965607131156569495961600000000*s6^4*s5*s3^9*s2^2 + 
        1796526308490724627055191588986931726673510400000000*s6^4*s5*s3^7*s2^5 + 
        303183145421012110850615270366087347206881280000000*s6^4*s5*s3^5*s2^8 - 
        115486120213100478679711786901519811084288000000000*s6^4*s5*s3^3*s2^11 - 
        3306542819452124164938282747909485486407680000000*s6^4*s5*s3*s2^14 + 
        97483229678733686419553081302963407814656000000000*s6^4*s3^12 - 
        68652968194841904018738677959910787907584000000000*s6^4*s3^10*s2^3 + 
        106140699746591222101216633503335095468032000000000*s6^4*s3^8*s2^6 + 
        107132064704031010195510628081522089564569600000000*s6^4*s3^6*s2^9 + 
        39196880152994595963125108957992270132838400000000*s6^4*s3^4*s2^12 + 
        3149015943599570318470730393400758749593600000000*s6^4*s3^2*s2^15 + 
        235744036720835916023769050641841537894400000000*s6^4*s2^18 - 
        1349947921580637863625799841859519291410350080000000*s6^3*s5^8*s2 + 
        5753836937966741751363631578482260908309479424000000*s6^3*s5^7*s3*s2^2 + 
        4611804127343273237623597528315537201614028800000000*s6^3*s5^6*s3^4 - 
        9446261356620243461167951321910549331931299840000000*s6^3*s5^6*s3^2*s2^3 + 
        321238697895445886145453541103391630942346936320000*s6^3*s5^6*s2^6 - 
        7307746247783843240560209604494766707100876800000000*s6^3*s5^5*s3^5*s2 + 
        9652398284977656840860825520308966854188072960000000*s6^3*s5^5*s3^3*s2^4 - 
        789293013285512858205900632341209663325398368256000*s6^3*s5^5*s3*s2^7 + 
        3961950574099946845567559436697535357386752000000000*s6^3*s5^4*s3^6*s2^2 - 
        6302435645619164177889458597893165094142581145600000*s6^3*s5^4*s3^4*s2^5 + 
        1033353736561793561313965456834591650903165501440000*s6^3*s5^4*s3^2*s2^8 + 
        4551311725961504291242076397384789209697484800000*s6^3*s5^4*s2^11 - 
        3448393532263691119276795262451137019641856000000000*s6^3*s5^3*s3^9 - 
        4380481894729855614511385489723208871905853440000000*s6^3*s5^3*s3^7*s2^3 + 
        899276633920753932127509658093893580770980659200000*s6^3*s5^3*s3^5*s2^6 - 
        996640628686372584996402739813173073877454028800000*s6^3*s5^3*s3^3*s2^9 - 
        10992290441471673366121967640768955655336755200000*s6^3*s5^3*s3*s2^12 + 
        3237353104139438172758711543728855441421107200000000*s6^3*s5^2*s3^10*s2 + 
        3051324060529355787339151843648529893718753280000000*s6^3*s5^2*s3^8*s2^4 + 
        616260270248595929505547232683328630377414656000000*s6^3*s5^2*s3^6*s2^7 + 
        401730817418272701155141069816118775054860288000000*s6^3*s5^2*s3^4*s2^10 - 
        11301056698251900347531715127916353648066560000000*s6^3*s5^2*s3^2*s2^13 - 
        584388241633516845040172243997153414709248000000*s6^3*s5^2*s2^16 - 
        985342887415817425501000950154608884066549760000000*s6^3*s5*s3^11*s2^2 - 
        797249439637121702614926216274089618073190400000000*s6^3*s5*s3^9*s2^5 - 
        186006208083914526888430888554113990212976640000000*s6^3*s5*s3^7*s2^8 - 
        52889129800919114010474723366825311510200320000000*s6^3*s5*s3^5*s2^11 + 
        8330321119049363611948264357967045680988160000000*s6^3*s5*s3^3*s2^14 + 
        125198360395039310504051766094672910008320000000*s6^3*s5*s3*s2^17 - 
        9661648787030098544248821288044272287744000000000*s6^3*s3^14 + 
        72460532787828390094788468218955687159398400000000*s6^3*s3^12*s2^3 + 
        38897089488860916304717464882162350555136000000000*s6^3*s3^10*s2^6 - 
        5419127599685842875623654953573474143436800000000*s6^3*s3^8*s2^9 - 
        5053450843609330873865539457469349955174400000000*s6^3*s3^6*s2^12 - 
        2277827418747806111717820714596825819750400000000*s6^3*s3^4*s2^15 - 
        122044863462771401339296268283909349017600000000*s6^3*s3^2*s2^18 - 
        8699459316585567284803313640291859008000000000*s6^3*s2^21 + 
        516667323638925180853050421241927649743339520000000*s6^2*s5^9*s3 - 
        1749705356253275775817155426423258722315796480000000*s6^2*s5^8*s3^2*s2 + 
        280835759323257453443851341740222315243765760000000*s6^2*s5^8*s2^4 + 
        2792954742893002409859066585900765352072052736000000*s6^2*s5^7*s3^3*s2^2 - 
        1136058074168783717858031582691775885828035706880000*s6^2*s5^7*s3*s2^5 - 
        1278115657971994616872538559173002863103180800000000*s6^2*s5^6*s3^6 - 
        2854376837043394093627702417342421257357885440000000*s6^2*s5^6*s3^4*s2^3 + 
        1958681459090862052661028658779375554324059914240000*s6^2*s5^6*s3^2*s2^6 - 
        23796196320230445219143661954894206738016239616000*s6^2*s5^6*s2^9 + 
        2515769872112118619717171884349262097127833600000000*s6^2*s5^5*s3^7*s2 + 
        1572890314913297826990023743478647881115631616000000*s6^2*s5^5*s3^5*s2^4 - 
        1966628671628816057889620429106686637528814977024000*s6^2*s5^5*s3^3*s2^7 + 
        64732188739421945195908378889268084159509692416000*s6^2*s5^5*s3*s2^10 - 
        1895616985527922868482704955773386950390579200000000*s6^2*s5^4*s3^8*s2^2 - 
        149869581924677994474386700233909339875285401600000*s6^2*s5^4*s3^6*s2^5 + 
        1204929499020950730049500508554204389372602613760000*s6^2*s5^4*s3^4*s2^8 - 
        85195970065546414541895729394181909892971888640000*s6^2*s5^4*s3^2*s2^11 - 
        114777304752480038680412961799074069892300800000*s6^2*s5^4*s2^14 + 
        461755088302402991529315838661634641048371200000000*s6^2*s5^3*s3^11 + 
        1310677789019269516464606971913992081359503360000000*s6^2*s5^3*s3^9*s2^3 + 
        65488289749925889923272726888015210194822758400000*s6^2*s5^3*s3^7*s2^6 - 
        341955213034484855419733473248267909929631744000000*s6^2*s5^3*s3^5*s2^9 + 
        71510755098034771646240841143218841555199590400000*s6^2*s5^3*s3^3*s2^12 + 
        222521007461007528741955815063724206823833600000*s6^2*s5^3*s3*s2^15 - 
        460724851695738049323066464230437054264115200000000*s6^2*s5^2*s3^12*s2 - 
        703469138515793393591442054158050883461447680000000*s6^2*s5^2*s3^10*s2^4 - 
        152990321800584963634275480030990525391699968000000*s6^2*s5^2*s3^8*s2^7 + 
        17345519426494229884574436924037826089254912000000*s6^2*s5^2*s3^6*s2^10 - 
        27733573531997417851767927370017248862633984000000*s6^2*s5^2*s3^4*s2^13 + 
        582682172929066782506977965866505653563392000000*s6^2*s5^2*s3^2*s2^16 + 
        16758677859049277087111918302613370992640000000*s6^2*s5^2*s2^19 + 
        151007900401513012736429313565932443884584960000000*s6^2*s5*s3^13*s2^2 + 
        184928701658619046453693419860719953562828800000000*s6^2*s5*s3^11*s2^5 + 
        52223551420801055941413292874425038577336320000000*s6^2*s5*s3^9*s2^8 + 
        6601575362564612010807985487038221432913920000000*s6^2*s5*s3^7*s2^11 + 
        4098288964187780196531796344285991333232640000000*s6^2*s5*s3^5*s2^14 - 
        362433363811568459196355935989887995002880000000*s6^2*s5*s3^3*s2^17 - 
        2681847545437316291502323646928277314560000000*s6^2*s5*s3*s2^20 + 
        626101435534986239850758450497053523968000000000*s6^2*s3^16 - 
        14437203170820358557279901142670771644006400000000*s6^2*s3^14*s2^3 - 
        15006047075381749325637616806542805172224000000000*s6^2*s3^12*s2^6 - 
        3063487525122103334435095669611452797747200000000*s6^2*s3^10*s2^9 + 
        192933442907611870001870789894866861900800000000*s6^2*s3^8*s2^12 + 
        68042276162019509002475714385229980518400000000*s6^2*s3^6*s2^15 + 
        83454249104854409789332852225057939382400000000*s6^2*s3^4*s2^18 + 
        2956943039334967882782792413751990556800000000*s6^2*s3^2*s2^21 + 
        210518397503856549070200899916752272500000000*s6^2*s2^24 + 
        59850244247547568583269655817456488527429632000000*s6*s5^10*s2^2 - 
        135372672994807888590376082135693916194734080000000*s6*s5^9*s3^3 - 
        355408160770020887745692184537739590936349900800000*s6*s5^9*s3*s2^3 + 
        398872445488488348298239444227969408229703680000000*s6*s5^8*s3^4*s2 + 
        802397332392689245916032972175699083529080012800000*s6*s5^8*s3^2*s2^4 - 
        19889733333559928297174890493253343008604028928000*s6*s5^8*s2^7 - 
        724841985205591426160552915280367459743301632000000*s6*s5^7*s3^5*s2^2 - 
        998271811912703349147101359566907144180680622080000*s6*s5^7*s3^3*s2^5 + 
        76893744323560591076859838856519407699093566259200*s6*s5^7*s3*s2^8 + 
        133731423708054131652352097851592505556992000000000*s6*s5^6*s3^8 + 
        962560875859146976386237250616277806245478400000000*s6*s5^6*s3^6*s2^3 + 
        751728413435548873217573597775604250124799180800000*s6*s5^6*s3^4*s2^6 - 
        131037995875271604359972930898656789015421360537600*s6*s5^6*s3^2*s2^9 + 
        845294417255131035275886528746258999806840012800*s6*s5^6*s2^12 - 
        307617658750486509860030333969393834891673600000000*s6*s5^5*s3^9*s2 - 
        825409608443847642728563154539953552869031936000000*s6*s5^5*s3^7*s2^4 - 
        315095094485070007217770349709953539903410143232000*s6*s5^5*s3^5*s2^7 + 
        128172763289542106447466498228992229712186048512000*s6*s5^5*s3^3*s2^10 - 
        2451846685452285654702389908519621533924065280000*s6*s5^5*s3*s2^13 + 
        276259762702449430706029701317027219342622720000000*s6*s5^4*s3^10*s2^2 + 
        415050552338955726988280479071422800342705766400000*s6*s5^4*s3^8*s2^5 + 
        34890720060324442486362052413280255074191278080000*s6*s5^4*s3^6*s2^8 - 
        75829116796140742024484276118014340882636472320000*s6*s5^4*s3^4*s2^11 + 
        3237943522791383614296655876126725218718842880000*s6*s5^4*s3^2*s2^14 + 
        546248895491893275628512187515308568576000000*s6*s5^4*s2^17 - 
        33565978648238472600242666143162078907596800000000*s6*s5^3*s3^13 - 
        180633255807508213278983361363171114586472448000000*s6*s5^3*s3^11*s2^3 - 
        151106956223372873694935483230187042611868467200000*s6*s5^3*s3^9*s2^6 + 
        15463911514139513357222156430446074989851443200000*s6*s5^3*s3^7*s2^9 + 
        23722828745760501493121326088525262337966080000000*s6*s5^3*s3^5*s2^12 - 
        2527216390055279325821686681446760142477721600000*s6*s5^3*s3^3*s2^15 + 
        355716420546924336988929929000884284211200000*s6*s5^3*s3*s2^18 + 
        34917616038185406281172618288465780827750400000000*s6*s5^2*s3^14*s2 + 
        85420526066704401422363763437230921252601856000000*s6*s5^2*s3^12*s2^4 + 
        49075236644067767733474311741527943458848768000000*s6*s5^2*s3^10*s2^7 - 
        2329828716330328727080882885091181946159104000000*s6*s5^2*s3^8*s2^10 - 
        3047700181136981053348660021620451149127680000000*s6*s5^2*s3^6*s2^13 + 
        955339955947347709879332969484699030109184000000*s6*s5^2*s3^4*s2^16 - 
        16049242301778375698412347650773092771328000000*s6*s5^2*s3^2*s2^19 - 
        272945147892629251126809118203733956480000000*s6*s5^2*s2^22 - 
        12005235320320963077137267868442941739499520000000*s6*s5*s3^15*s2^2 - 
        21704470760278141899434535802044067117793280000000*s6*s5*s3^13*s2^5 - 
        10708609890668656586504952266341343475793920000000*s6*s5*s3^11*s2^8 - 
        676999630499318308748124587873224045117440000000*s6*s5*s3^9*s2^11 + 
        22991712420238158016625495726522094520320000000*s6*s5*s3^7*s2^14 - 
        149501670522395815576265747384202713118720000000*s6*s5*s3^5*s2^17 + 
        8748170583642069728589520778297934714240000000*s6*s5*s3^3*s2^20 + 
        26342866703767898949438948011328553920000000*s6*s5*s3*s2^23 - 
        23964731033812665475860786448189882368000000000*s6*s3^18 + 
        1286094015981568912781266878381452741836800000000*s6*s3^16*s2^3 + 
        1992821369135744575124748254571390015897600000000*s6*s3^14*s2^6 + 
        852341232765968198693821407680064199065600000000*s6*s3^12*s2^9 + 
        51686637709009117721076345092723205580800000000*s6*s3^10*s2^12 - 
        7054827833806622213792793561127861372800000000*s6*s3^8*s2^15 + 
        2522146442080155506691488110973074468800000000*s6*s3^6*s2^18 - 
        1756473560107579005582903547854934040400000000*s6*s3^4*s2^21 - 
        40316509230827978462576325578320974300000000*s6*s3^2*s2^24 - 
        3016687539573107601398770513971473437500000*s6*s2^27 - 
        9710897616374118284789731758030897769611264000000*s5^12 + 
        34437159744979520161597626351396684608569344000000*s5^11*s3*s2 - 
        48008320200480294384161022620300757669249024000000*s5^10*s3^2*s2^2 - 
        4279134297690268539096280650905602155545100288000*s5^10*s2^5 + 
        14219591687252551124606308085412954982318080000000*s5^9*s3^5 + 
        48458035740626886449837141561401695916366233600000*s5^9*s3^3*s2^3 + 
        23110908202036224041120205194249292228417552384000*s5^9*s3*s2^6 - 
        26625475370118520941236720422104624581836800000000*s5^8*s3^6*s2 - 
        62328568687243100416535351962119941712877977600000*s5^8*s3^4*s2^4 - 
        50133552190219478037669457078318916179410812928000*s5^8*s3^2*s2^7 + 
        475856112357013387552497162566503157180059877376*s5^8*s2^10 + 
        34577608210509188775617471967499879006076928000000*s5^7*s3^7*s2^2 + 
        90112824262994886273802417880531541696373063680000*s5^7*s3^5*s2^5 + 
        60613778599760264472922379902773257459784587673600*s5^7*s3^3*s2^8 - 
        1773427132423033659545483654251326412138626416640*s5^7*s3*s2^11 - 
        4104152771240871380831321311201959849492480000000*s5^6*s3^10 - 
        50330719108748298809045810826344982946775040000000*s5^6*s3^8*s2^3 - 
        96558338320139502487582679014347356331174789120000*s5^6*s3^6*s2^6 - 
        44757809266370910695253495229661414398295329996800*s5^6*s3^4*s2^9 + 
        2953333726754595634488148976116394845125319065600*s5^6*s3^2*s2^12 - 
        11694415788091165060835099000683578042089472000*s5^6*s2^15 + 
        11633605595638027195944963101583182596669440000000*s5^5*s3^11*s2 + 
        54544097816186718309463543808769022652055552000000*s5^5*s3^9*s2^4 + 
        66853544984619651136710547544599315059056836608000*s5^5*s3^7*s2^7 + 
        19789022384346607630887685470442483902339612672000*s5^5*s3^5*s2^10 - 
        2811060442781890948534705487632655814502121472000*s5^5*s3^3*s2^13 + 
        35460841412677390814974411794050709761359872000*s5^5*s3*s2^16 - 
        12397112488003355880610044835294003498844160000000*s5^4*s3^12*s2^2 - 
        35254903945060191697297311366699030139927265280000*s5^4*s3^10*s2^5 - 
        28517956790556239645004607978742845752693227520000*s5^4*s3^8*s2^8 - 
        4292340512482681720917226349464107397545984000000*s5^4*s3^6*s2^11 + 
        1616721630453456084778784309480329015470243840000*s5^4*s3^4*s2^14 - 
        46926967602833320045232418843721928387788800000*s5^4*s3^2*s2^17 + 
        17090717735023265070460588445075464473600000*s5^4*s2^20 + 
        1025438857828268860388343197909774027980800000000*s5^3*s3^15 + 
        8633960873271683395974757448837893126619136000000*s5^3*s3^13*s2^3 + 
        14876099723201611858076699598941695778173747200000*s5^3*s3^11*s2^6 + 
        7779277584984835673270054974211420194917580800000*s5^3*s3^9*s2^9 + 
        69522287655106375454121894325298084216832000000*s5^3*s3^7*s2^12 - 
        519076412333681529289129956168291839928729600000*s5^3*s3^5*s2^15 + 
        35062197807027194097424776326950731279360000000*s5^3*s3^3*s2^18 - 
        56072543586014929479287764015074245990400000*s5^3*s3*s2^21 - 
        1099451569609964704500144374086528244121600000000*s5^2*s3^16*s2 - 
        3995079272447268877942580659632427763761152000000*s5^2*s3^14*s2^4 - 
        4444917270739991244644334147342671233941504000000*s5^2*s3^12*s2^7 - 
        1547095968790223230608815337820229938397184000000*s5^2*s3^10*s2^10 + 
        117637511650558247574373407306541590260736000000*s5^2*s3^8*s2^13 + 
        80244681546562181202398711193936731107584000000*s5^2*s3^6*s2^16 - 
        13016197042295837628973810716789973266816000000*s5^2*s3^4*s2^19 + 
        182976980277422280303077554315286380368000000*s5^2*s3^2*s2^22 + 
        1931004421876881081898661751631338492000000*s5^2*s2^25 + 
        390856876656819249818812839179978255892480000000*s5*s3^17*s2^2 + 
        999894422436804818452598174814556032860160000000*s5*s3^15*s2^5 + 
        840900433098302995668017081265835667619840000000*s5*s3^13*s2^8 + 
        230280711167127503471760161530165915729920000000*s5*s3^11*s2^11 - 
        11736650564886627510522943489916534323200000000*s5*s3^9*s2^14 - 
        4179527747669049873543895954184667751680000000*s5*s3^7*s2^17 + 
        2102092801680585275867826830876570964000000000*s5*s3^5*s2^20 - 
        90023881866803767995917370296468913360000000*s5*s3^3*s2^23 - 
        40875522567927399522924607358850510000000*s5*s3*s2^26 + 
        411565446112426409498846165808552345600000000*s3^20 - 
        44585358266428976849036820324520506163200000000*s3^18*s2^3 - 
        95874821232118688760629829214861865779200000000*s3^16*s2^6 - 
        67694351905769176964656519817355937382400000000*s3^14*s2^9 - 
        15708268480056000492131671311362836454400000000*s3^12*s2^12 + 
        602690457401139734712569910707823657600000000*s3^10*s2^15 + 
        156832292521421986909642961975197074500000000*s3^8*s2^18 - 
        71221723197679467177678095020769737200000000*s3^6*s2^21 + 
        16204392211115378856480041230864646362500000*s3^4*s2^24 + 
        232327691529936341193890630272407262500000*s3^2*s2^27 + 
        19439199650520742256486767365558837890625*s2^30;
end function;   