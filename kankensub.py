#!/Library/Frameworks/Python.framework/Versions/3.9/bin/python3.9
# -*- coding: utf-8 -*-

import os
import sys
import urllib.request
import regex as re
import unicodedata
import json
import argparse
import socket
import pysubs2
import math

from concurrent.futures import ProcessPoolExecutor, as_completed
from collections import defaultdict
from tqdm import tqdm
from reportlab.lib.pagesizes import A4
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfbase import pdfmetrics
from kanjize import kanji2number

font_path = "NotoSansJP-VariableFont_wght.ttf"
font_name = "NotoSansJP"

try:
    pdfmetrics.registerFont(TTFont(font_name, font_path))
    print(f"フォント '{font_name}' の登録に成功しました。")
except Exception as e:
    print(f"⚠️ フォント '{font_name}' の登録中にエラーが発生しました: {e}")
    if "postscript outlines are not supported" in str(e).lower():
        print("エラー: フォントがPostScriptアウトラインを使用しているため、ReportLabではサポートされていません。")
        print("💡 解決策: フォントをTrueType (TTF) に変換するか、別のフォントを使用してください。")
    sys.exit(1)  # プログラムを終了


class KanjiUtils:
    CJK_RE = re.compile("CJK (UNIFIED|COMPATIBILITY) IDEOGRAPH")
    IS_NOT_JAPANESE_PATTERN = re.compile(r'[^\p{N}\p{Lu}○◯々-〇〻ぁ-ゖゝ-ゞァ-ヺー０-９Ａ-Ｚｦ-ﾝ\p{Radical}\p{Unified_Ideograph}]+')

    kanken_kanji_data = {
        "j1k": "乃卜叉巳勺之也丑勿云仇尤巴什壬匁廿允帀疋弗禾叶匝乎凧弘戊汀仔只乍叩卯亘亙牟托伍此艮瓜亥凪弛辻而吃吊肋亦伊夙汐曳吋匡尖夷牝丞舛圭汝戎兇旭庄佃吞牡扮苅沌李酉辿庇宏杢辰杖芹杜伽杏吾坐妓冴兎呑芥宍灼芙吻汲劫牢灸伶玖芭邑杓甫禿孜亨呆佑迄宋迂吠孟枇其侠茅祁佼尭怯斧杷欣狛姑庖朋狗杵苒怜妾坦苓姐苧竺宕於咒陀或苑奄岨岱苔苫昌茄坤忽沓肱肴杭沫昂庚昏些函卦帖兔阿侃頁柏粂荊穿荏茸姶茜叛柁哉巷珊姪剃屍栂柘狐柊廼洲殆酋矧盃祢胡柚郁祇宥盈祐歪韭荆珂洛俠耶籾竿柑姦凾恰俣柾廻虻洩姥恢垢臥亮娃粁胤俄毘衿彦毗玲咳迦按砥凌桧狼耽套迺桓峨涛悌恕桐荻哩蚤隼浬栗栖啄窄朔涌紐釘莱狸柴挺晒晋砺凋峻紗莵砧疹豹脆狽唖屑秤栴笈娩倭圃翆倦倶匪挽訊桂珪矩盌捌畠莫桔俱倖晃粍涜浩莞峩皋砿秦哨閃紘峯烏琢紬啐婁惇偓雀捺蛋掻崕埴捷埜淳淋渚庵釧娼啞渕雫掩焔痔菖惟梯蛎萊凰寅逗舵梢壷祷淘捲梼桶牽椛粕惚彪梱訣兜釦袷萄袴菩掬梧絃烹萌萠逢埠皐菅彬砦笹梓笥畦捧笠悉袈猪這梶躯梁掠晦菱甜淀掴琉畢偲匙貰揃葡靭牌硲斐厨琵椙詑筏棲溌弼斌靱焚隈遥禄裡屡脹琳湛智筑葎註椀堵菟琶焰惣敦棉葢董喋湊葱巽悶椋稀瑛湘甥閏淵渠卿喬揖欽戟堰筈葵黍蛭疏惹斯雁蛛萱韮粥蛤鈎絢堺葺菰喰壺渥覗蛙粟犀凱寓竣腔喧萩硯蒙馳碍楢爺嵩楊碓傭猷蓉蒐椴愈塙馴楕嵯逼禽鉤摸幌鈷楠跨瑚稗楳煤塘蓑椿蒔獅碇禎鼎蒜畷鳩嵳楓蒲裟罫賎蒼搔靖嘩瑞葦溢鉦蛸溯蒋碗煉蓮鼠稜楯蛾溜舜蜎詫楚遁稔牒厩蔀嘘煽蔭榊碩厭鳳閤頚箆碧漉廐廏厰摺鳶瑳蔣膏翠塵蔚斡𨻶屢頗飴賑摑駁槙蔓裳嶋僑箔窪緋輔綴綜爾熔赫嘉樺榎槍魁綾漕綬蜘鉾竪潅聡蝋鞄暢腿嘗劃銚榛箕銑槌蔦漣肇廓蓬潑篇蝿漑噓劉蝱駕蕃蝦撹鞍幡慾㵎磐撫鴇鋒鴎慧毅緬蕪誼聨僻鋪麹槻嬉駈澗諌翫誹諒蕎廟鋲遼麪鴈魯噌樋噂噛蕉潴醇蕋蕊蝶箭樟撰糎廠賤撒撚鋤蝉樗撞蕨蝕鄭歎箪糊播廚蕩諏髭鴬鴦輯橢豎鴨樫鴛薙篦醍蹄穆穐錫諫窺舘鴫諜樽薮翰餐橘憐頸穎橡叡篭錐頴錘錆縞鞘噸醐儘諺醗錨彊樵謂黛鮎噺鮒薗蕗澱鋸燕繋駿嬰嶺薯擢輿霞燭鍔燐檜繍鮪鮭鍬醤曙甑糟篠螺聯鍾鍍竃鴻檎糠瞥徽濤鮫鞠藁膿磯癌瓢薩濠壕濡禦燦檀糞嬬趨橿簞鯉藪鵜鞭鵠謬檮叢襖嚢蟬蹟鎔儲擾鎧雛瀆嚙軀鎗鎚醬麿穣鹸簾簸瀕鯖曝蘇贋繫繡顚麴禱蠅蠏蘂醱瀞顛鵬騨鯛寵蘭蟹蟻瀦麒鯵櫛藷櫓禰轍簾鵡鏑礪馨耀蠣鐙鰐纂巌灌礦鰍轟蠟鰭竈鐸龝鶯鰯纏鑓韃灘驒鰻囊聾鱈纒饗讃轡鷗鰺鷲鱒鰹攪鷺鹼麟鱗鷹讚鸚",
        "j1k1k": "戶內册收羽佛壯沒每成步免芽尙狀拔戾爭舍靑卑社兒周屆卷兩拂亞來𦤶者突卽侮勉拜彥祉恆祈臭海莊莖祖郞祝徑涉祐缺悔峽眞狹乘晉氣效姬城挾倂祕竝神悅益淚淨將陷淺專敏敕麥朗處祥條從晝梅敍帶國參產淸殺脫敎圈硏晚連巢區假壻單喝曾稅都堯盜晴猪發勞殼棧插爲畫搜惱割剩窗渚黃虛絲萬逸琢殘貳圍壹惠渴揭視著隆黑惡靖愼塚腦肅飯廉溫傳裝碎當碑搖溪經甁祿鄕勤會飮亂煮廊虜暑號與圓奧禍嘆署綠寬褐蓮塀臺福滯漢滿禎精僧飼遙賓實槇瑤榮齊圖慘奬粹稱寢僞團盡遞輕壽對舖德緖儉價澁徵樞賣練憎彈層墨醉樣穀節樓髮緣銳歐墮稻毆樂齒廣廢寫劍瘦增踐數曆器曉螢燈遼輸諭諸龜遲縣頻餘賴橫歷勳澤勵謁據擇豫龍學擔錢錄戰隨獨默險燒鄰衞劑靜辨謠濕聲總襃舊繁聰薰膽擊戲擧壓嶽穗濱檢應鍊潛餠點縱隸彌齋隱營濟禪館斷鎭醫雙壘轉歸顏禮藝藥謹雜藏蟲豐獵擴辭類關證穩癡邊瀧繩贊難贈懷獸懲瀨勸繪壞孃麵鬪蘭齡黨譯壤嚴騷譽覺爐獻犧觸寶繼釋續辯攝權驅櫻歡鷄欄屬鐵疊鑄響臟竊覽穰聽讀體鑛變驛髓驗顯纖罐巖戀靈囑觀釀讓艷灣鹽廳蠻蠶",
        "1k": "乂几匕匚于兀孑尸已幺弋丫孒屮弌丐亢仍仄仆仂卅夬夭尹弖戈扎曰毋丕丱弍仗仞仭仟冉刋匆丗卉卮叮叨叭叺圦夲孕屶戉朮艾辷价伉伜冱凩刔刎匈卍吁夸奸妁屹幵并忖戍戌扞扛扣扠扨朿朸朶汕聿犲阡艸芍芒佚估佝佗佇佞兌冏刪劬劭甸匣吽听吭吼吮吶吩吝呎囮坎圻址坏夾妝妣妍孚孛尨屁岌岑岔巫彷忻忤忸忱忰扼抉找抒抓抖抃抔抛旱杙杣杠杞杆肛肚肓汞汪沍沚沁汨沂沐泛沛糺瓧矣狄狆狃阮阯阨邨疔芫芟芬芦竍罕豕巵沪删苆皁旰呏乖亟佶侈侏侘佻佩佰侑佯侖冽凭刮刳劼咏呵咎呟呷呻咀呶咄咐咆囹坩坡坿妲姆孥岫帚帙帑帛弩徂彿忝忿怡怙怩怛怕怫怦怏怺戔拗拑抻拆拈拌拊拇抬毟杲昊昃杳旻枌枉枋枡杪杼枅虱肭肬泓泗沽沮泝泄泅沱泪泯沾牀爬軋矼瓩氛炙炒衫狎狒羌陂邯邵邱疚疝籵歿殀氓苡苳茉苜苻苣范苞苙苟苹茆苴苺迚迪廸竏秉盂罔穹祀刱幷拋卹玫矻彽卻圀俔俟俎俘俛俑俚俐俤俥兪冑剏剄剋剌勁匍厖呱呰哇咢咸咥咬哄哈咨咫哂咤囿垓垠垤奕奐奎姨姜姙姚孩屎屏峙庠弭弯徊很徇怎怱恪恟恊恍恃恤恂恬恫扁拏挌拮拱挂拯拵畋鳬斫朏昜昴昶昵昿閂缸枴柯枷柤柞柩柮柬枳柢柎柝枹枸胙胝胛胚胥胄胖曷禹禺洸洽洌洟洶洵洒洫爰癸珈珀玻玳砒砌紆紂牴酊瓰瓲瓮瓱炸炮炬炳炯衵袂衲衽狢狡狠盻眇眈眄陋陌疣疥殃殄茴茯茱荀荅茲茹茵荐茗茘茫莽迢迥竓竕秕衍罘穽矜臾舁姸姮俞竽紉挘炷烟笋倚倨倔倪倥倅俶倡倩倬俾俯們倆冓冤冢凅剞剔勍叟哥哦唏唔哽哮哭哢唳圄埃埆埒奚奘娥娟娑娜娉宦宸屓峭峪恚恁恙悁悍悃悚悄悛悖悒悧悋拿挈捐捍捏捩旃旆旁旄晟晁晏耙耘栩栞桙框桎蚓蚪蚌蚩蚣蚋栲栫胱胯胼韋浣浙涕涓浹浚涅涎笏笆笊笄珮珥珞砠紊紕紜耿鬯舫烋烝烙訖訌訐衾袗袙袢袒袍躬狷倏羔眛眩陜陝陟陞郛郢郤疳痃痂疸疽疼疱莓莚莢莪莟莎莅芻茣莨荳莠殷荼荵莉畛畚豺耆耄逅迹迴迸竚站粃秣秬秧盍赳舐罠罟皰翅窈虔祗祠祚祓祟衄豈冦弉衮捓粏虒桛桄哳凊偃偕偐偈偖偬偸做冕剪剳勗匐匏唹啀售啜啅啖啗唸圉堊堋婀婬婉娵娶婢婪孰寇崟崛崑崔崢崚崙崘帷弸彗徙徘悸惓悴悽惆悵惘戛扈掖掎掀掫捶掏掉掟捫斛旌敖毬毫晞晤晧晨晢耜閊麸桿桝桀梳蛄蚰蛉蚯蚶蚫蛆桷梭梔梵桴梟梠梺梏梛梃脣脯脛脩曼跂趺趾鹵馗淹淬淒涵涸淅淙淆淪淌淤軛笘笞笵笳笨笙欸欷琅硅釵絅紿絆紵紮紲牾犁酖聆聊瓷瓸舸舳烱焉烽訛訝訥袞袤袰袿裃裄袱袵勒猊猜猖猗猝羝羚眷眥眦眸陬陲痍疵痊痒殍菽萢菠菎菴菲萃萍菫菁菘畤覓皎貶逑逕逞逧逡逖逋逍逎竟竡盒衒翊窕舂谺寃厠勖屛晣悤埳躮萁悾梻梲偷𣶏棊筍傀傚傅剴厥啣喙喀喊喟啻啾喘喞啼喃喇喨堙堝堡奠奢媚嫂孳寔寐屠孱嵌嵒嵎嵋幄幀幇廁廂弑彭徨愕惶愀惴惺愃惻愎戞掣掾揩揀揆揣揉揶揄敞敝黹毯毳朞晰閔蛞蛬蛩蛯蛔蛟棘椏椁棗棠椈椄棕椒椚棍棹棣腋脾腓腆腑跏跖跌跚跛跋颪渙渣湲渭湮湫渾湍渺渫游溂渟湎渝湃軻軫軼馮馭筌筅筐筝赧欹琥琲琺釿鈞鈕鈑鈔絖絎絣絨絏絮犂犇酣酥聒牋焜焙詛詈訶詁詆詒瓠裙覃靫猴猩猯猥睇隋隍鄂痙痞痣粢粤粨辜甦萼葩葷萸萵葯葭葆蒂畭畴覘釉皓皖貂耋貽賁逵竢竦稈稍趁舒觝皴翔翕窖窘厦腁筓畬孶逬晳跎裎愒喑焠猋堽韵亶傴僉僂剿剽勣勦飭勠匯嗚嗇嗟嗄嗜嗤嗔塋塒壼媼媾嫋媽寞尠嵬幃幎廈徭愆惷愍慍愾愧慊愴戡搆搦搶搓搗搏搨斟旒鳰鳧黽暈暉暘暄耡閘雹蜒蜉蜀蛻蜊蜍蜈蛹蜑蜆蜃椶楹椰楸楫楮椽楾榁楔楡楝椹楞腮腴腱腥腟跟跣跪跫滉溽滄溏溥溷滔滂溘溟溲軾輅輊輌筺筥筵筧筰筬筮筱筴麁歇歃肄肆雎雉雍雋瑟瑙瑁瑕瑜瑶髢碚硼碌鉗鉉鉞鉅鉋鉈鈿絳綏絽綉絛綛綟骭酩聘艀煥煢煌煬煖煦詭詢誄詬誅誂詼矮閙裔裘褂裼裲裨褄躱獏猾頏頌睫睨睛睚睥隗隕隘鄒痿痾痰痺痼痳痲瘁粱粳粲糀飩飫辟蒭蒿蓙蒟蓖蒡蓍蓆蒹蓁蓐蒻畸皙貊貉賈貲遐遒遖遏遑逾遉稟禀稠盞觚觜衙罧罨罩舅祺豢滓蜹輀瑇榆蜋魞觥筲蜓痹搤腠榀聟僊僖僥僣僮兢匱嘔嗷嘖嗾嗽嘛塹墅夐夥嫦嫣嫗嫩嫖孵寤寥嶇嶄嶂幗幔麼廖慇愨愿愬慂慷慚慴慥慟慝慓慵截搴摶摧摎敲曄暝閨閧蜴蜿蜚蜥蜻蜩蜷槓槁槎榻寨槐榧榾榴榑榜槊榕榔槃榱膃膈膀膂膊跼跿踉韶靤颯颱滾漲滬滸漱漾滲漓滷滌輒輓箘箜箍箝箒箏箚箙歉瑯瑣瑪瑰髦髣碪碣銜銖銕銓銛鋩綺綵緇綽綢綣綸綯綮綰綫骰犒犖酲酳聚聢甄甅甃熕熄煕熏誨誡誣誦誚誑誥裹裴褌褊褓褝靼鞁靺鞅鞆睾睹鄙瘧瘋瘉粽殞蓼蔗蔔蔡蔘蔟蓴蓿蔕覡遘竭竰趙皹皸翡窩禊厮槔髥劄綦慠摏厲塿澂僵儁儂儚冪凜凛劈匳噎嘶嘸墟嫺嫻嬌嬋嶢嶝幟幢廝廛廡慳慙慫憔憚憫憮戮撓撥撕撩撈黎麾鴉鴃鴆魴麩魃魄閭霄霈霆蝨蝠蝮蝌蝴蝙蝓蝗蝟蝎蝣蝸蟒槹槲槭樊槧槿樅樛樔樒槨膣膠踝踟踞膵漿滕潸潘澎潺潭澆潯潦濆輙輟輜輦輛駟駛駑駘駝篁篌篆篋箴瑩璋瑾髫髯髴髱磑磋碾磅碼磊鋏銹銷錵錺緤緞緘緲縅緝緡醋醂甍熨熙熈熬諄諚諍諂諛鬧褞褥褫褪鞐鞋鞏獗羯頡瞎瞑瞋鄲瘟瘠瘤瘢瘡糅糂餉餃殤靠蔬蕘蕕蕁蕈蕀皚貎賚遯遨稷皺翦翩禝臧豌鴂魳魸魬踑耦蝘蝲璇噁牖璢僭儕儔冀嘴噫噤嘯噬噪嚆圜壅嬖寰嶬嶮嶼廨廩彜徼憖憊憑懌懊懈懆憺懍擒撼擅撻擂黔鴟鴒鴕鴣鴪鮃鮓鮑鮗鮖暾暹曁耨麭閻閼閹閾霓霎霑霙霏霖蟇蟆螂螟橄橙樸橇橦橈檠膩蹂踵踰踴膰靦澡澪澣澹澳濛輻輹輳駮駱駭駢赭麈歔歙霍雕篝篩篥簑璞髻髷磔磬磧磚錏錙錣錻鋺錚縡縟縊縉縋縢縒骼甌甎艘艙熹熾燉燔燗燎諤諠諢謔諞諳諷諡鬨襁褸褶躾獪羲頤頷頽瞠瞞隧瘰瘴瘻糒餔餒殫殪蕣薊蕷蕾薔薨薀薑薜薛薈薇薐薤蕭覦覩遶邁盧盥罹窶臻臈墻鴥篡麇鮇頹赬篪縕薏﨟螈螗噦噯𩶗謌襍黏儡簒燮嚀嚊嚏壑嬲嬪嬶孺嶷懃懋懦擘擱擠擡擣擯龠鼾黜黝齔斂黻鵄鴿鵁鴾鵆氈鮟鮨鮠鮴朦曚闊濶闃闍闌罅蟋螽螳蟀螯螻螫蟄蠎檣檐檄檗檬檪蹊蹉蹌蹇蹐蹈臀臂膺膾臉牆馘颶濬濘濔轅轂輾駻騁駸麋歟歛雖簔篷簍簓簇簀簗篳磽磴鍼鍮鍠縻繆縹縵縺繃縲縷醢聳艚艝燵燧燠燬謚諱謇謐謗謖謨譁褻襄襌鞜獰顆瞰隰癇癆癈癘糜餡餤餞藉薹薺藐覯覬貘賻賽賺邂邀遽盪艱翳窿虧禧豁谿繈幫鮱鮲鵇糝螾蟎檋檔壎獮嚠嚔壙彝懣懴戳擲擺擽攅鼕黠鼬旛斃鵝鵞鵑鵤鵙鯀鯊鯒鯑鯏鮹魍魎魏闖闔闕霤蟠蟯櫁檸櫃櫂檳蹙蹠蹣蹤蹕臑臍瀋濺瀁瀏瀉瀑濾轆轌騅騏麌簣簧簟瓊鬆礒礑鎰鎹鎬繧繚繖繝繦繙繞髀醪馥聶甕甓釐艟燹燿燼燻謦謾鞫謳謫鬩襠鞦鞳鞨鞣顋瞼瞿矇瞻瞽癜餮餬殯藕藜覲贄贅邇邃穢穡觴羂羃翹竅竄騈鯎鯐鮸鵥鎺蟪蠆𫒼嚥嚮壜壟嬾廬懶攀黼鵲鶉鵺鶇鵯鯣鯢鯤鯲鯡鯔鯱鯰曠霪蠍蟾蟶蟷蠖櫟檻櫚蹶蹲蹼躇臘瀚瀛瀝瀟轎騙麕麑簷簽簫籀礙鏖鏘鏈鏤鏨鏃鏝鏐繹犢醯牘艤艢艨爍譌譚譏譎譛襞襦襪覈鞴獺羹羶羸隴饂餽餾殱韲靡蘊藾蘢藺藹蘋蘆疇疆贇羆龐鰙鶍鶎鶄蹻繳蠊儳嚬歠孼孽嚶孅孀巉懺懽攘黥齣齟齠鶚鶤鶫鶩鰓鰉鰔鰕鰌鰈鰆鰒鰊鰄鰛朧曦闡罌霰蠕蠑蘗櫨櫪蘖躅躄躁鹹臙臚韜飄瀾瀲瀰轗騫驀簪籌瓏礫礬鐚鏗鐔鐃鐐鐓繽纃辮繻醵醴瓣譫譬譟襭襤矍癢糯糲饉饅蘚贍贏蘯竇壥鶪櫱躃鼯騭鰚鰘韞衊櫸霸飜儺儷囂嚼囁囃囀囈巍廱懾懼黯齦齧鶲鷁鶻鶺鷆鶸鷂鰮鰥鰤鰰曩齎魑闢闥罍霹蠢蠡欅櫺躋躊飆轜驂驃騾麝籃籔籐籖瓔鬘鐫鐶鐺纈纐纉髏醺艪爛譖譴襯癧癪癨癩饐饌饑饋饒殲贔贐籒鰧纊儼儻巓巒彎懿攤龕齬齪鷙鷓鱆鱇鰾罎霽霾蠧躓躑躔灑轢驕驍籟鬚艫襴襷顫癬糴饕蘿覿鬻贓贖羇禳攢鼴籡籙糱癭鑒攣攫黴黐鷸鷦鷯鷭鱚蠱欒躙靨轤籥籤鬟鑠鑢鑞鑚纔纓髑讌讐讎韈癰齏邏鼹驎鱛鱏鱓顬曬𬵪囓齷齲齶鷽鼇鱠鱧魘靂靆靄蠹驟鬢鑪纛讙讖讒軈韆顰癲衢羈屭鱟鱩鑵攬黌鼈靉躡臠籬鬣鑰釁顱糶纘鬭黶鱶欖躪驥驢鑷鬮顴矚鱲黷鱸驤驩鑼鑾鑽顳鸛钁鑿纜癴驪爨鸞麤"
    }

    @staticmethod
    def is_kanji(unichar):
        # 文字が漢字かどうかを判定する関数
        return bool(KanjiUtils.CJK_RE.match(unicodedata.name(unichar, "")))
    
    @staticmethod
    def load_kanken_kanji_sets():
        # 漢検漢字セットを読み込む関数
        return set(KanjiUtils.kanken_kanji_data['j1k']), set(KanjiUtils.kanken_kanji_data['j1k1k']), set(KanjiUtils.kanken_kanji_data['1k'])

    @staticmethod
    def extract_number_from_kanji(filename):
        """
        ファイル名から最初の数字を抽出し、ソートに使用できる数値を返す関数。
        漢数字の場合も対応する。
        """
        # 普通の数字を先に抽出
        normal_number = re.search(r'\d+', filename)
        if normal_number:
            return int(normal_number.group())  # 最初に見つかった数字を返す

        # 見つからない場合は漢数字を抽出
        kanji_number = re.search(r'[一二三四五六七八九十百千万億兆]+', filename)
        if kanji_number:
            return kanji2number(kanji_number.group())

        return float('inf')  #　何も見つからない場合は、ソート順を最後にするために大きな数値を返す

    @staticmethod
    def count_kanji_in_words(anki_words, kanken_j1k_set, kanken_j1k1k_set, kanken_1k_set):
        # Ankiの単語リストに含まれる漢検漢字の出現回数をカウントする
        kanji_occurrences = {kanji: 0 for kanji in kanken_j1k_set | kanken_j1k1k_set | kanken_1k_set}

        # 各単語ごとに含まれる漢字をカウント
        for word in anki_words:
            unique_kanji_in_word = set(word) & kanji_occurrences.keys()
            for kanji in unique_kanji_in_word:
                kanji_occurrences[kanji] += 1

        # 出現しなかった漢字を削除
        kanji_occurrences = {k: v for k, v in kanji_occurrences.items() if v > 0}

        return kanji_occurrences

    @staticmethod
    def clean_text(text):
        cleaned = text.replace(r'\N', ' ').strip()
        cleaned = re.sub(r'\s+', ' ', cleaned)
        return cleaned


class FileUtils():

    SETTINGS_FILE = os.path.join(os.path.dirname(__file__), 'settings.json')

    @staticmethod
    def get_files(target, extensions):
        files = []

        if os.path.isfile(target):
            if any(target.endswith(ext) for ext in extensions):
                files = [target]
        else:
            for root, _, filenames in os.walk(target):
                for filename in filenames:
                    if any(filename.endswith(ext) for ext in extensions):
                        files.append(os.path.join(root, filename))

            #　ファイルを漢数字や番号順（数字が見つからなかった場合はアルファベット順）でソート
            files.sort(key=lambda f: (KanjiUtils.extract_number_from_kanji(os.path.basename(f)), os.path.basename(f)))

        return files

    @staticmethod
    def clean_filename(filename):
        cleaned = re.sub(r'\[.*?\]', '', filename)
        cleaned = re.sub(r'\.(srt|ass|vtt)$', '', cleaned, flags=re.IGNORECASE)
        cleaned = re.sub(r'(WEBRip|BDRip|Netflix|x\d+|p|AAC|HEVC|TrueHD|x264|10bit|ja\[cc\]|v\d+|ja)', '', cleaned, flags=re.IGNORECASE)
        cleaned = re.sub(r'[._-]+', ' ', cleaned).strip()

        season_episode_match = re.search(r'(S\d+E\d+|EP\d+)', cleaned, re.IGNORECASE)
        season_episode = season_episode_match.group() if season_episode_match else ''

        main_title = re.sub(r'(S\d+E\d+|EP\d+)', '', cleaned).strip()

        if season_episode:
            return f"{main_title} {season_episode}".strip()
        else:
            return main_title

    @staticmethod
    def save_args_to_file(args):
        # Ankiデッキの情報をjsonで保存する
        data_to_save = {
            'deck': args.deck,
            'word': args.word
        }
        with open(FileUtils.SETTINGS_FILE, 'w') as f:
            json.dump(data_to_save, f, ensure_ascii=False, indent=4)


    @staticmethod
    def load_args_from_file():
        # Ankiデッキの情報を読み込む
        if os.path.exists(FileUtils.SETTINGS_FILE):
            try:
                with open(FileUtils.SETTINGS_FILE, 'r') as f:
                    return json.load(f)
            except json.JSONDecodeError:
                print(f"Warning: {FileUtils.SETTINGS_FILE} is empty or corrupted.")
                return None
        return None


class KankenSubtitleProcessor:
    def __init__(self, kanken_j1k_set, kanken_j1k1k_set, kanken_1k_set, anki_kanji_dict, export=False, batch_size=100, verbose=False):
        self.kanken_j1k_set = kanken_j1k_set
        self.kanken_j1k1k_set = kanken_j1k1k_set
        self.kanken_1k_set = kanken_1k_set
        self.total_kanken_set = kanken_j1k_set | kanken_j1k1k_set | kanken_1k_set
        self.anki_kanji_dict = anki_kanji_dict
        self.export = export
        self.verbose = verbose
        self.batch_size = batch_size
        self.kanji_timestamps = defaultdict(list)


    def _extract_text_and_timestamps(self, file):
        try:
            subs = pysubs2.load(file)
            return [(line.text, line.start, file) for line in subs]
        except Exception as e:
            if self.verbose:
                print(f"字幕ファイルの読み込みエラー ({file}): {e}")
            return []


    def _process_batch(self, files):
        local_kanji_timestamps = defaultdict(list)
        
        for file in files:
            subtitle_data = self._extract_text_and_timestamps(file)
            for text, start_time, filename in subtitle_data:
                cleaned_text = re.sub(KanjiUtils.IS_NOT_JAPANESE_PATTERN, '', text)
                for kanji in filter(KanjiUtils.is_kanji, cleaned_text):
                    local_kanji_timestamps[kanji].append((filename, start_time, text))
        
        return local_kanji_timestamps


    def process_subtitle_files(self, files, max_workers=4):
        self.kanji_timestamps.clear()
        use_progress_bar = len(files) > 100

        # Dynamic batch sizing
        min_batch_size = 4
        optimal_batches = min(32, len(files))  # Ensure we don't make too many batches
        batch_size = max(min_batch_size, math.ceil(len(files) / optimal_batches))

        batches = [files[i:i + self.batch_size] for i in range(0, len(files), self.batch_size)]

        with ProcessPoolExecutor(max_workers=max_workers) as executor:
            future_to_batch = {executor.submit(self._process_batch, batch): batch for batch in batches}
            
            file_iterator = tqdm(as_completed(future_to_batch), total=len(batches), desc="字幕処理中", unit="バッチ") if use_progress_bar else as_completed(future_to_batch)

            for future in file_iterator:
                result = future.result()
                for kanji, occurrences in result.items():
                    self.kanji_timestamps[kanji].extend(occurrences)


    def _format_kanji_info_pdf(self, kanji, occurrences):
        # 漢字情報を整形するヘルパー関数
        kanken_level = (
            "準一級" if kanji in self.kanken_j1k_set else
            "準一級／一級" if kanji in self.kanken_j1k1k_set else
            "一級"
        )

        anki_count = self.anki_kanji_dict.get(kanji, 0)
        info = f"<b><font color='purple'>{kanji}</font></b>, レベル: <font color='seagreen'>{kanken_level}</font>"
        if anki_count > 0:
            info += f", Ankiカード数: {anki_count}枚"

        occurrences_text = ""
        for file, ts, sentence in occurrences[:10]:
            cleaned_sentence = KanjiUtils.clean_text(sentence).replace(kanji, f"<font color='purple'>{kanji}</font>")
            occurrences_text += (
                f"<font color='darkgray'><br/><b>{FileUtils.clean_filename(os.path.basename(file))}</b> </font>"
                f"<font color='steelblue'>({pysubs2.time.ms_to_str(ts)})</font> - {cleaned_sentence}"
            )

        return f"{info}<br/>{occurrences_text}<br/><br/>"
    

    def _print_kanji_info_console(self, kanji, occurrences):
        purple = "\033[35m"  # 漢字
        cyan = "\033[36m"    # タイムスタンプ
        orange = "\033[38;5;208m"   # 漢検レベル
        green = "\033[97m" # 文
        reset = "\033[0m"    # 色リセット

        formatted_occurrences = "".join(
            (
                f"\n{green}{FileUtils.clean_filename(os.path.basename(file))}{reset} "
                f"({cyan}{pysubs2.time.ms_to_str(ts)}{reset}) - "
                f"{KanjiUtils.clean_text(sentence).replace(kanji, f'{purple}{kanji}{reset}')}"
            )
            for file, ts, sentence in occurrences[:10]
        )
        kanken_level = (
            f"{orange}準一級{reset}" if kanji in self.kanken_j1k_set else
            f"{orange}準一級／一級{reset}" if kanji in self.kanken_j1k1k_set else
            f"{orange}一級{reset}"
        )

        anki_count = self.anki_kanji_dict.get(kanji, 0)
        purple_kanji = f"{purple}{kanji}{reset}"
        if anki_count > 0:
            print(f"漢字: {purple_kanji}, レベル: {kanken_level}, Ankiカード数: {anki_count}枚, 出現箇所:{formatted_occurrences}\n")
        else:
            print(f"漢字: {purple_kanji}, レベル: {kanken_level}, 出現箇所:{formatted_occurrences}\n")


    def print_kanji_summary(self, nbr_of_allowed_existing_cards=1, export_path="kanji_summary.pdf"):
        # 漢字の出現要約を表示またはエクスポート
        subtitle_kanji_set = set(self.kanji_timestamps.keys())
        kk_kanji_to_print = {
            kanji for kanji in subtitle_kanji_set & self.total_kanken_set
            if self.anki_kanji_dict.get(kanji, 0) <= nbr_of_allowed_existing_cards
        }

        if self.export:
            doc = SimpleDocTemplate(export_path, pagesize=A4)
            styles = getSampleStyleSheet()
            kanji_style = ParagraphStyle("KanjiStyle", parent=styles["BodyText"], fontName="NotoSansJP", fontSize=12)
            title_style = ParagraphStyle("TitleStyle", parent=styles["Title"], fontName="NotoSansJP", fontSize=16, spaceAfter=12)
            content = [Paragraph(f"見つかった漢字: {len(kk_kanji_to_print)}字（準一級／一級 レベル）", title_style), Spacer(1, 12)]

            for kanji in sorted(kk_kanji_to_print, key=lambda k: self.kanji_timestamps[k][0][1]):
                content.append(Paragraph(self._format_kanji_info_pdf(kanji, self.kanji_timestamps[kanji]), kanji_style))
                content.append(Spacer(1, 12))

            doc.build(content)
            print(f"漢字の要約を {export_path} にエクスポートしました。")
        else:
            print(f"見つかった漢字: {len(kk_kanji_to_print)}字（準一級／一級 レベル）\n")
            for kanji in sorted(kk_kanji_to_print, key=lambda k: self.kanji_timestamps[k][0][1]):
                self._print_kanji_info_console(kanji, self.kanji_timestamps[kanji])


    def print_progress(self):
        print("\n----- 現在の進捗状況 -----")
        levels = [
            (self.kanken_j1k_set, "準一級"),
            (self.kanken_j1k1k_set, "準一級／一級"),
            (self.kanken_1k_set, "一級")
        ]

        for kanken_kanji_set, level_name in levels:
            current_kanji_in_anki = len(set(self.anki_kanji_dict.keys()) & kanken_kanji_set)
            total_kanji = len(kanken_kanji_set)

            # 字幕から追加可能な漢字
            subtitle_kanji_in_group = (set(self.kanji_timestamps.keys()) & kanken_kanji_set) - (set(self.anki_kanji_dict.keys()) & kanken_kanji_set)
            projected_progress = current_kanji_in_anki + len(subtitle_kanji_in_group)
            project_progress_percentage = (projected_progress / total_kanji) * 100 if total_kanji > 0 else 0

            current_completion_percentage = (current_kanji_in_anki / total_kanji) * 100 if total_kanji > 0 else 0

            print(f"{level_name} - 完成度: {current_kanji_in_anki} / {total_kanji} ({current_completion_percentage:.2f}%) 完了")
            if len(subtitle_kanji_in_group) == 0:
                print(f"字幕から追加可能な漢字: {len(subtitle_kanji_in_group)}\n")
            else:
                print(f"字幕から追加可能な漢字: {len(subtitle_kanji_in_group)}、 {projected_progress} / {total_kanji} ({project_progress_percentage:.2f}%) 完了予定\n")


# 妹ジャックから貰ったコード
class AnkiHandler():

    def __init__(self, url='http://127.0.0.1:8765'):
        self.url = url

    def _request(self, action, **params):
        return { 'action': action, 'params': params, 'version': 6 }

    def _invoke(self, action, **params):
        try:
            request_json = json.dumps(self._request(action, **params)).encode('utf-8')

            with urllib.request.urlopen(urllib.request.Request(self.url, request_json)) as url:
                response = json.load(url)

            if len(response) != 2:
                raise Exception('The response has an unexpected number of fields.')
            if 'error' not in response:
                raise Exception('The response is missing a required error field.')
            if 'result' not in response:
                raise Exception('The response is missing a required result field.')
            if response['error'] is not None:
                raise Exception(response['error'])

            return response['result']

        except socket.error:
            print("Ankiが実行されていないようです。Ankiを起動して再試行してください。")
            sys.exit()
            return None
        except Exception as e:
            print(f"エラーが発生しました: {e}")
            sys.exit()
            return None

    def get_words_in_deck(self, deck, word_field, ignore_existing_cards_without_audio=False):
        if ignore_existing_cards_without_audio:
            search_query = f'"deck:{deck}" KankenAudio:_*'
        else:
            search_query = f'deck:"{deck}"'

        note_ids = self._invoke('findNotes', query=search_query)
        if not note_ids:
            print(f'デッキ「{deck}」にはカードが見つかりませんでした。')
            return []

        notes = self._invoke('notesInfo', notes=note_ids)
        if notes and word_field not in notes[0]['fields']:
            print(f'⚠️ フィールド「{word_field}」が見つかりません。')
            return []

        words = [note['fields'][word_field]['value'] + '\n' for note in notes]
        
        print(f'デッキ「{deck}」から {len(words)}個の単語を取得しました。')
        return words


def main():
    # 字幕ファイルを処理してユニークな漢字を抽出する
    parser = argparse.ArgumentParser(description="字幕ファイルから漢検準一級／一級の漢字を抽出します")
    parser.add_argument("target", type=str, help="処理する対象ディレクトリまたはファイル")

    saved_args = FileUtils.load_args_from_file()
    deck_required = True
    word_required = True

    if saved_args:
        parser.set_defaults(**saved_args)
        deck_required = False
        word_required = False

    parser.add_argument('--deck', type=str, required=deck_required, help='Ankiデッキの名')
    parser.add_argument('--word', type=str, required=word_required, help='単語を含むフィールド名')
    parser.add_argument("-ia", action='store_true', help='Ankiカードが既に存在していても、音声がない場合は、字幕に出現する漢字を表示します')
    parser.add_argument("-e", action='store_true')
    args = parser.parse_args()

    kanken_kanken_j1k_set, kanken_kanken_j1k1k_set, kanken_1k_set = KanjiUtils.load_kanken_kanji_sets()

    anki_handler = AnkiHandler()
    words = anki_handler.get_words_in_deck(args.deck, args.word, ignore_existing_cards_without_audio=args.ia)
    anki_kanji_occurrences = KanjiUtils.count_kanji_in_words(words, kanken_kanken_j1k_set, kanken_kanken_j1k1k_set, kanken_1k_set)

    kanken_sub_handler = KankenSubtitleProcessor(kanken_kanken_j1k_set, kanken_kanken_j1k1k_set, kanken_1k_set, anki_kanji_occurrences, export=args.e)

    files = FileUtils.get_files(args.target, ['.srt', '.ass'])
    if not files:
        print(f"フォルダ '{args.target}' には字幕ファイルが見つかりませんでした")
        return
    print(f"見つかったファイル: {len(files)}")

    kanken_sub_handler.process_subtitle_files(files)
    kanken_sub_handler.print_kanji_summary(nbr_of_allowed_existing_cards=0)
    kanken_sub_handler.print_progress()

    if not words:
        print("\n" + "=" * 50)
        print("⚠️  単語が見つかりませんでした！ ⚠️")
        print("指定したデッキや単語フィールドが正しいか確認してください。")
        print("=" * 50 + "\n")

    FileUtils.save_args_to_file(args)


if __name__ == "__main__":
    main()