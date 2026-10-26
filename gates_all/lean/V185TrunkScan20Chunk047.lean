import V185TrunkScan20Chunk046

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_286417 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_286417 : Nat := 118140960795 + 286417 * 2 ^ 59
def prefixEnd_286417 : Nat := 4983230072969 + 3 ^ 40 * 286417 * 2
def baseEnd_286417 : Nat := 130728523216809889662487

theorem tailTrace_286417 : CollatzResearch.WordTrace tailWord_286417 prefixEnd_286417 130728523216809889662487 := by
  unfold tailWord_286417
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446486203367599974297505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6964324135578399982865003 10446486203367599974297505)
  ·
    refine ⟨7834864652525699980723129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10446486203367599974297505 7834864652525699980723129)
    ·
      refine ⟨5876148489394274985542347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7834864652525699980723129 5876148489394274985542347)
      ·
        refine ⟨8814222734091412478313521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5876148489394274985542347 8814222734091412478313521)
        ·
          refine ⟨6610667050568559358735141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8814222734091412478313521 6610667050568559358735141)
          ·
            refine ⟨1239500071981604879762839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6610667050568559358735141 1239500071981604879762839)
            ·
              refine ⟨1859250107972407319644259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239500071981604879762839 1859250107972407319644259)
              ·
                refine ⟨2788875161958610979466389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859250107972407319644259 2788875161958610979466389)
                ·
                  refine ⟨130728523216809889662487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2788875161958610979466389 130728523216809889662487)
                  ·
                    rfl

theorem cell20_286417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_286417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286417 prefixEnd_286417 := by exact prefixLift 286417
  have htrace : WordTrace (prefixWord ++ tailWord_286417) baseStart_286417 baseEnd_286417 := by
    simpa [prefixWord, tailWord_286417, baseEnd_286417] using wordTrace_append hprefix tailTrace_286417
  have hstable : (prefixWord ++ tailWord_286417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286417).length < 2 ^ (prefixWord ++ tailWord_286417).sum := by decide
  have hdescent : baseEnd_286417 < baseStart_286417 := by decide
  rcases family_descends (prefixWord ++ tailWord_286417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286448 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_286448 : Nat := 118140960795 + 286448 * 2 ^ 59
def prefixEnd_286448 : Nat := 4983230072969 + 3 ^ 40 * 286448 * 2
def baseEnd_286448 : Nat := 130742672461511559629027

theorem tailTrace_286448 : CollatzResearch.WordTrace tailWord_286448 prefixEnd_286448 130742672461511559629027 := by
  unfold tailWord_286448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5223808433127646134337999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6965077910836861512450665 5223808433127646134337999)
  ·
    refine ⟨7835712649691469201506999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5223808433127646134337999 7835712649691469201506999)
    ·
      refine ⟨11753568974537203802260499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7835712649691469201506999 11753568974537203802260499)
      ·
        refine ⟨17630353461805805703390749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11753568974537203802260499 17630353461805805703390749)
        ·
          refine ⟨6611382548177177138771531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17630353461805805703390749 6611382548177177138771531)
          ·
            refine ⟨9917073822265765708157297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6611382548177177138771531 9917073822265765708157297)
            ·
              refine ⟨7437805366699324281117973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9917073822265765708157297 7437805366699324281117973)
              ·
                refine ⟨348647126564030825677405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7437805366699324281117973 348647126564030825677405)
                ·
                  refine ⟨130742672461511559629027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348647126564030825677405 130742672461511559629027)
                  ·
                    rfl

theorem cell20_286448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_286448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286448 prefixEnd_286448 := by exact prefixLift 286448
  have htrace : WordTrace (prefixWord ++ tailWord_286448) baseStart_286448 baseEnd_286448 := by
    simpa [prefixWord, tailWord_286448, baseEnd_286448] using wordTrace_append hprefix tailTrace_286448
  have hstable : (prefixWord ++ tailWord_286448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286448).length < 2 ^ (prefixWord ++ tailWord_286448).sum := by decide
  have hdescent : baseEnd_286448 < baseStart_286448 := by decide
  rcases family_descends (prefixWord ++ tailWord_286448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286455 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_286455 : Nat := 118140960795 + 286455 * 2 ^ 59
def prefixEnd_286455 : Nat := 4983230072969 + 3 ^ 40 * 286455 * 2
def baseEnd_286455 : Nat := 130745867452250646395665

theorem tailTrace_286455 : CollatzResearch.WordTrace tailWord_286455 prefixEnd_286455 130745867452250646395665 := by
  unfold tailWord_286455
  simp only [CollatzResearch.WordTrace]
  refine ⟨10447872177229932464180819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6965248118153288309453879 10447872177229932464180819)
  ·
    refine ⟨15671808265844898696271229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10447872177229932464180819 15671808265844898696271229)
    ·
      refine ⟨5876928099691837011101711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15671808265844898696271229 5876928099691837011101711)
      ·
        refine ⟨8815392149537755516652567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5876928099691837011101711 8815392149537755516652567)
        ·
          refine ⟨13223088224306633274978851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8815392149537755516652567 13223088224306633274978851)
          ·
            refine ⟨19834632336459949912468277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13223088224306633274978851 19834632336459949912468277)
            ·
              refine ⟨1859496781543120304293901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19834632336459949912468277 1859496781543120304293901)
              ·
                refine ⟨697311293078670114110213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1859496781543120304293901 697311293078670114110213)
                ·
                  refine ⟨130745867452250646395665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697311293078670114110213 130745867452250646395665)
                  ·
                    rfl

theorem cell20_286455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_286455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286455 prefixEnd_286455 := by exact prefixLift 286455
  have htrace : WordTrace (prefixWord ++ tailWord_286455) baseStart_286455 baseEnd_286455 := by
    simpa [prefixWord, tailWord_286455, baseEnd_286455] using wordTrace_append hprefix tailTrace_286455
  have hstable : (prefixWord ++ tailWord_286455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286455).length < 2 ^ (prefixWord ++ tailWord_286455).sum := by decide
  have hdescent : baseEnd_286455 < baseStart_286455 := by decide
  rcases family_descends (prefixWord ++ tailWord_286455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286507 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_286507 : Nat := 118140960795 + 286507 * 2 ^ 59
def prefixEnd_286507 : Nat := 4983230072969 + 3 ^ 40 * 286507 * 2
def baseEnd_286507 : Nat := 130769601669169576662119

theorem tailTrace_286507 : CollatzResearch.WordTrace tailWord_286507 prefixEnd_286507 130769601669169576662119 := by
  unfold tailWord_286507
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449768773041545345073775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6966512515361030230049183 10449768773041545345073775)
  ·
    refine ⟨15674653159562318017610663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449768773041545345073775 15674653159562318017610663)
    ·
      refine ⟨23511979739343477026415995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15674653159562318017610663 23511979739343477026415995)
      ·
        refine ⟨35267969609015215539623993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23511979739343477026415995 35267969609015215539623993)
        ·
          refine ⟨26450977206761411654717995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35267969609015215539623993 26450977206761411654717995)
          ·
            refine ⟨39676465810142117482076993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26450977206761411654717995 39676465810142117482076993)
            ·
              refine ⟨29757349357606588111557745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39676465810142117482076993 29757349357606588111557745)
              ·
                refine ⟨22318012018204941083668309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29757349357606588111557745 22318012018204941083668309)
                ·
                  refine ⟨130769601669169576662119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22318012018204941083668309 130769601669169576662119)
                  ·
                    rfl

theorem cell20_286507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_286507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286507 prefixEnd_286507 := by exact prefixLift 286507
  have htrace : WordTrace (prefixWord ++ tailWord_286507) baseStart_286507 baseEnd_286507 := by
    simpa [prefixWord, tailWord_286507, baseEnd_286507] using wordTrace_append hprefix tailTrace_286507
  have hstable : (prefixWord ++ tailWord_286507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286507).length < 2 ^ (prefixWord ++ tailWord_286507).sum := by decide
  have hdescent : baseEnd_286507 < baseStart_286507 := by decide
  rcases family_descends (prefixWord ++ tailWord_286507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286520 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_286520 : Nat := 118140960795 + 286520 * 2 ^ 59
def prefixEnd_286520 : Nat := 4983230072969 + 3 ^ 40 * 286520 * 2
def baseEnd_286520 : Nat := 130775535223399309228733

theorem tailTrace_286520 : CollatzResearch.WordTrace tailWord_286520 prefixEnd_286520 130775535223399309228733 := by
  unfold tailWord_286520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225121460997224282648507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6966828614662965710198009 5225121460997224282648507)
  ·
    refine ⟨7837682191495836423972761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5225121460997224282648507 7837682191495836423972761)
    ·
      refine ⟨5878261643621877317979571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7837682191495836423972761 5878261643621877317979571)
      ·
        refine ⟨8817392465432815976969357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5878261643621877317979571 8817392465432815976969357)
        ·
          refine ⟨3306522174537305991363509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8817392465432815976969357 3306522174537305991363509)
          ·
            refine ⟨309986453862872436690329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3306522174537305991363509 309986453862872436690329)
            ·
              refine ⟨232489840397154327517747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309986453862872436690329 232489840397154327517747)
              ·
                refine ⟨348734760595731491276621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232489840397154327517747 348734760595731491276621)
                ·
                  refine ⟨130775535223399309228733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348734760595731491276621 130775535223399309228733)
                  ·
                    rfl

theorem cell20_286520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_286520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286520 prefixEnd_286520 := by exact prefixLift 286520
  have htrace : WordTrace (prefixWord ++ tailWord_286520) baseStart_286520 baseEnd_286520 := by
    simpa [prefixWord, tailWord_286520, baseEnd_286520] using wordTrace_append hprefix tailTrace_286520
  have hstable : (prefixWord ++ tailWord_286520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286520).length < 2 ^ (prefixWord ++ tailWord_286520).sum := by decide
  have hdescent : baseEnd_286520 < baseStart_286520 := by decide
  rcases family_descends (prefixWord ++ tailWord_286520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286538 : List Nat := [3, 1, 2, 1, 1, 1, 3, 8]
def baseStart_286538 : Nat := 118140960795 + 286538 * 2 ^ 59
def prefixEnd_286538 : Nat := 4983230072969 + 3 ^ 40 * 286538 * 2
def baseEnd_286538 : Nat := 43594583637957082209553

theorem tailTrace_286538 : CollatzResearch.WordTrace tailWord_286538 prefixEnd_286538 43594583637957082209553 := by
  unfold tailWord_286538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612724858982309409863067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6967266290619491759634845 2612724858982309409863067)
  ·
    refine ⟨3919087288473464114794601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2612724858982309409863067 3919087288473464114794601)
    ·
      refine ⟨2939315466355098086095951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3919087288473464114794601 2939315466355098086095951)
      ·
        refine ⟨4408973199532647129143927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2939315466355098086095951 4408973199532647129143927)
        ·
          refine ⟨6613459799298970693715891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4408973199532647129143927 6613459799298970693715891)
          ·
            refine ⟨9920189698948456040573837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613459799298970693715891 9920189698948456040573837)
            ·
              refine ⟨3720071137105671015215189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9920189698948456040573837 3720071137105671015215189)
              ·
                refine ⟨43594583637957082209553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3720071137105671015215189 43594583637957082209553)
                ·
                  rfl

theorem cell20_286538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_286538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286538 prefixEnd_286538 := by exact prefixLift 286538
  have htrace : WordTrace (prefixWord ++ tailWord_286538) baseStart_286538 baseEnd_286538 := by
    simpa [prefixWord, tailWord_286538, baseEnd_286538] using wordTrace_append hprefix tailTrace_286538
  have hstable : (prefixWord ++ tailWord_286538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286538).length < 2 ^ (prefixWord ++ tailWord_286538).sum := by decide
  have hdescent : baseEnd_286538 < baseStart_286538 := by decide
  rcases family_descends (prefixWord ++ tailWord_286538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286583 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_286583 : Nat := 118140960795 + 286583 * 2 ^ 59
def prefixEnd_286583 : Nat := 4983230072969 + 3 ^ 40 * 286583 * 2
def baseEnd_286583 : Nat := 130804290140051090128475

theorem tailTrace_286583 : CollatzResearch.WordTrace tailWord_286583 prefixEnd_286583 130804290140051090128475 := by
  unfold tailWord_286583
  simp only [CollatzResearch.WordTrace]
  refine ⟨10452540720766210324840403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6968360480510806883226935 10452540720766210324840403)
  ·
    refine ⟨15678811081149315487260605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10452540720766210324840403 15678811081149315487260605)
    ·
      refine ⟨5879554155430993307722727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15678811081149315487260605 5879554155430993307722727)
      ·
        refine ⟨8819331233146489961584091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5879554155430993307722727 8819331233146489961584091)
        ·
          refine ⟨13228996849719734942376137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8819331233146489961584091 13228996849719734942376137)
          ·
            refine ⟨9921747637289801206782103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13228996849719734942376137 9921747637289801206782103)
            ·
              refine ⟨14882621455934701810173155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9921747637289801206782103 14882621455934701810173155)
              ·
                refine ⟨22323932183902052715259733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14882621455934701810173155 22323932183902052715259733)
                ·
                  refine ⟨130804290140051090128475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22323932183902052715259733 130804290140051090128475)
                  ·
                    rfl

theorem cell20_286583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_286583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286583 prefixEnd_286583 := by exact prefixLift 286583
  have htrace : WordTrace (prefixWord ++ tailWord_286583) baseStart_286583 baseEnd_286583 := by
    simpa [prefixWord, tailWord_286583, baseEnd_286583] using wordTrace_append hprefix tailTrace_286583
  have hstable : (prefixWord ++ tailWord_286583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286583).length < 2 ^ (prefixWord ++ tailWord_286583).sum := by decide
  have hdescent : baseEnd_286583 < baseStart_286583 := by decide
  rcases family_descends (prefixWord ++ tailWord_286583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286644 : List Nat := [2, 5, 2, 1, 2, 2, 2, 4]
def baseStart_286644 : Nat := 118140960795 + 286644 * 2 ^ 59
def prefixEnd_286644 : Nat := 4983230072969 + 3 ^ 40 * 286644 * 2
def baseEnd_286644 : Nat := 43610710734068663031631

theorem tailTrace_286644 : CollatzResearch.WordTrace tailWord_286644 prefixEnd_286644 43610710734068663031631 := by
  unfold tailWord_286644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227382786772608871405493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6969843715696811828540657 5227382786772608871405493)
  ·
    refine ⟨490067136259932081694265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5227382786772608871405493 490067136259932081694265)
    ·
      refine ⟨367550352194949061270699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 490067136259932081694265 367550352194949061270699)
      ·
        refine ⟨551325528292423591906049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367550352194949061270699 551325528292423591906049)
        ·
          refine ⟨413494146219317693929537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551325528292423591906049 413494146219317693929537)
          ·
            refine ⟨310120609664488270447153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413494146219317693929537 310120609664488270447153)
            ·
              refine ⟨232590457248366202835365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310120609664488270447153 232590457248366202835365)
              ·
                refine ⟨43610710734068663031631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232590457248366202835365 43610710734068663031631)
                ·
                  rfl

theorem cell20_286644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_286644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286644 prefixEnd_286644 := by exact prefixLift 286644
  have htrace : WordTrace (prefixWord ++ tailWord_286644) baseStart_286644 baseEnd_286644 := by
    simpa [prefixWord, tailWord_286644, baseEnd_286644] using wordTrace_append hprefix tailTrace_286644
  have hstable : (prefixWord ++ tailWord_286644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286644).length < 2 ^ (prefixWord ++ tailWord_286644).sum := by decide
  have hdescent : baseEnd_286644 < baseStart_286644 := by decide
  rcases family_descends (prefixWord ++ tailWord_286644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286676 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_286676 : Nat := 118140960795 + 286676 * 2 ^ 59
def prefixEnd_286676 : Nat := 4983230072969 + 3 ^ 40 * 286676 * 2
def baseEnd_286676 : Nat := 130846737874156100028095

theorem tailTrace_286676 : CollatzResearch.WordTrace tailWord_286676 prefixEnd_286676 130846737874156100028095 := by
  unfold tailWord_286676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227966354714643603987941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6970621806286191471983921 5227966354714643603987941)
  ·
    refine ⟨980243691508995675747739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5227966354714643603987941 980243691508995675747739)
    ·
      refine ⟨1470365537263493513621609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980243691508995675747739 1470365537263493513621609)
      ·
        refine ⟨1102774152947620135216207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1470365537263493513621609 1102774152947620135216207)
        ·
          refine ⟨1654161229421430202824311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102774152947620135216207 1654161229421430202824311)
          ·
            refine ⟨2481241844132145304236467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654161229421430202824311 2481241844132145304236467)
            ·
              refine ⟨3721862766198217956354701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481241844132145304236467 3721862766198217956354701)
              ·
                refine ⟨1395698537324331733633013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3721862766198217956354701 1395698537324331733633013)
                ·
                  refine ⟨130846737874156100028095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1395698537324331733633013 130846737874156100028095)
                  ·
                    rfl

theorem cell20_286676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_286676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286676 prefixEnd_286676 := by exact prefixLift 286676
  have htrace : WordTrace (prefixWord ++ tailWord_286676) baseStart_286676 baseEnd_286676 := by
    simpa [prefixWord, tailWord_286676, baseEnd_286676] using wordTrace_append hprefix tailTrace_286676
  have hstable : (prefixWord ++ tailWord_286676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286676).length < 2 ^ (prefixWord ++ tailWord_286676).sum := by decide
  have hdescent : baseEnd_286676 < baseStart_286676 := by decide
  rcases family_descends (prefixWord ++ tailWord_286676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286679 : List Nat := [1, 1, 3, 2, 1, 1, 7, 2, 2]
def baseStart_286679 : Nat := 118140960795 + 286679 * 2 ^ 59
def prefixEnd_286679 : Nat := 4983230072969 + 3 ^ 40 * 286679 * 2
def baseEnd_286679 : Nat := 130848107155901422928083

theorem tailTrace_286679 : CollatzResearch.WordTrace tailWord_286679 prefixEnd_286679 130848107155901422928083 := by
  unfold tailWord_286679
  simp only [CollatzResearch.WordTrace]
  refine ⟨10456042128418418720335091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6970694752278945813556727 10456042128418418720335091)
  ·
    refine ⟨15684063192627628080502637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10456042128418418720335091 15684063192627628080502637)
    ·
      refine ⟨5881523697235360530188489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15684063192627628080502637 5881523697235360530188489)
      ·
        refine ⟨4411142772926520397641367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5881523697235360530188489 4411142772926520397641367)
        ·
          refine ⟨6616714159389780596462051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4411142772926520397641367 6616714159389780596462051)
          ·
            refine ⟨9925071239084670894693077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6616714159389780596462051 9925071239084670894693077)
            ·
              refine ⟨232618857166046974094369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9925071239084670894693077 232618857166046974094369)
              ·
                refine ⟨174464142874535230570777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232618857166046974094369 174464142874535230570777)
                ·
                  refine ⟨130848107155901422928083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174464142874535230570777 130848107155901422928083)
                  ·
                    rfl

theorem cell20_286679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 2].length) (baseStart_286679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286679 prefixEnd_286679 := by exact prefixLift 286679
  have htrace : WordTrace (prefixWord ++ tailWord_286679) baseStart_286679 baseEnd_286679 := by
    simpa [prefixWord, tailWord_286679, baseEnd_286679] using wordTrace_append hprefix tailTrace_286679
  have hstable : (prefixWord ++ tailWord_286679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286679).length < 2 ^ (prefixWord ++ tailWord_286679).sum := by decide
  have hdescent : baseEnd_286679 < baseStart_286679 := by decide
  rcases family_descends (prefixWord ++ tailWord_286679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286724 : List Nat := [2, 3, 2, 4, 2, 7]
def baseStart_286724 : Nat := 118140960795 + 286724 * 2 ^ 59
def prefixEnd_286724 : Nat := 4983230072969 + 3 ^ 40 * 286724 * 2
def baseEnd_286724 : Nat := 4846986903040046904737

theorem tailTrace_286724 : CollatzResearch.WordTrace tailWord_286724 prefixEnd_286724 4846986903040046904737 := by
  unfold tailWord_286724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228841706627695702861613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6971788942170260937148817 5228841706627695702861613)
  ·
    refine ⟨1960815639985385888573105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5228841706627695702861613 1960815639985385888573105)
    ·
      refine ⟨1470611729989039416429829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1960815639985385888573105 1470611729989039416429829)
      ·
        refine ⟨275739699372944890580593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1470611729989039416429829 275739699372944890580593)
        ·
          refine ⟨206804774529708667935445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275739699372944890580593 206804774529708667935445)
          ·
            refine ⟨4846986903040046904737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 206804774529708667935445 4846986903040046904737)
            ·
              rfl

theorem cell20_286724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 7].length) (baseStart_286724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286724 prefixEnd_286724 := by exact prefixLift 286724
  have htrace : WordTrace (prefixWord ++ tailWord_286724) baseStart_286724 baseEnd_286724 := by
    simpa [prefixWord, tailWord_286724, baseEnd_286724] using wordTrace_append hprefix tailTrace_286724
  have hstable : (prefixWord ++ tailWord_286724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286724).length < 2 ^ (prefixWord ++ tailWord_286724).sum := by decide
  have hdescent : baseEnd_286724 < baseStart_286724 := by decide
  rcases family_descends (prefixWord ++ tailWord_286724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286726 : List Nat := [6, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_286726 : Nat := 118140960795 + 286726 * 2 ^ 59
def prefixEnd_286726 : Nat := 4983230072969 + 3 ^ 40 * 286726 * 2
def baseEnd_286726 : Nat := 130869559236578148361225

theorem tailTrace_286726 : CollatzResearch.WordTrace tailWord_286726 prefixEnd_286726 130869559236578148361225 := by
  unfold tailWord_286726
  simp only [CollatzResearch.WordTrace]
  refine ⟨326804886226504554603001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6971837572832097164864021 326804886226504554603001)
  ·
    refine ⟨245103664669878415952251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 326804886226504554603001 245103664669878415952251)
    ·
      refine ⟨367655497004817623928377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245103664669878415952251 367655497004817623928377)
      ·
        refine ⟨275741622753613217946283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367655497004817623928377 275741622753613217946283)
        ·
          refine ⟨413612434130419826919425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275741622753613217946283 413612434130419826919425)
          ·
            refine ⟨310209325597814870189569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413612434130419826919425 310209325597814870189569)
            ·
              refine ⟨232656994198361152642177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310209325597814870189569 232656994198361152642177)
              ·
                refine ⟨174492745648770864481633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232656994198361152642177 174492745648770864481633)
                ·
                  refine ⟨130869559236578148361225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174492745648770864481633 130869559236578148361225)
                  ·
                    rfl

theorem cell20_286726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_286726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286726 prefixEnd_286726 := by exact prefixLift 286726
  have htrace : WordTrace (prefixWord ++ tailWord_286726) baseStart_286726 baseEnd_286726 := by
    simpa [prefixWord, tailWord_286726, baseEnd_286726] using wordTrace_append hprefix tailTrace_286726
  have hstable : (prefixWord ++ tailWord_286726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286726).length < 2 ^ (prefixWord ++ tailWord_286726).sum := by decide
  have hdescent : baseEnd_286726 < baseStart_286726 := by decide
  rcases family_descends (prefixWord ++ tailWord_286726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286762 : List Nat := [3, 1, 4, 1, 2, 2, 3, 4]
def baseStart_286762 : Nat := 118140960795 + 286762 * 2 ^ 59
def prefixEnd_286762 : Nat := 4983230072969 + 3 ^ 40 * 286762 * 2
def baseEnd_286762 : Nat := 43628663539174007720359

theorem tailTrace_286762 : CollatzResearch.WordTrace tailWord_286762 prefixEnd_286762 43628663539174007720359 := by
  unfold tailWord_286762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614767346779430973901635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6972712924745149263737693 2614767346779430973901635)
  ·
    refine ⟨3922151020169146460852453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2614767346779430973901635 3922151020169146460852453)
    ·
      refine ⟨735403316281714961409835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3922151020169146460852453 735403316281714961409835)
      ·
        refine ⟨1103104974422572442114753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735403316281714961409835 1103104974422572442114753)
        ·
          refine ⟨827328730816929331586065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103104974422572442114753 827328730816929331586065)
          ·
            refine ⟨620496548112696998689549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827328730816929331586065 620496548112696998689549)
            ·
              refine ⟨232686205542261374508581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620496548112696998689549 232686205542261374508581)
              ·
                refine ⟨43628663539174007720359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232686205542261374508581 43628663539174007720359)
                ·
                  rfl

theorem cell20_286762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_286762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286762 prefixEnd_286762 := by exact prefixLift 286762
  have htrace : WordTrace (prefixWord ++ tailWord_286762) baseStart_286762 baseEnd_286762 := by
    simpa [prefixWord, tailWord_286762, baseEnd_286762] using wordTrace_append hprefix tailTrace_286762
  have hstable : (prefixWord ++ tailWord_286762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286762).length < 2 ^ (prefixWord ++ tailWord_286762).sum := by decide
  have hdescent : baseEnd_286762 < baseStart_286762 := by decide
  rcases family_descends (prefixWord ++ tailWord_286762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286804 : List Nat := [2, 4, 1, 1, 1, 1, 1, 9]
def baseStart_286804 : Nat := 118140960795 + 286804 * 2 ^ 59
def prefixEnd_286804 : Nat := 4983230072969 + 3 ^ 40 * 286804 * 2
def baseEnd_286804 : Nat := 43635053520652181253635

theorem tailTrace_286804 : CollatzResearch.WordTrace tailWord_286804 prefixEnd_286804 43635053520652181253635 := by
  unfold tailWord_286804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230300626482782534317733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6973734168643710045756977 5230300626482782534317733)
  ·
    refine ⟨980681367465521725184575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5230300626482782534317733 980681367465521725184575)
    ·
      refine ⟨1471022051198282587776863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980681367465521725184575 1471022051198282587776863)
      ·
        refine ⟨2206533076797423881665295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471022051198282587776863 2206533076797423881665295)
        ·
          refine ⟨3309799615196135822497943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206533076797423881665295 3309799615196135822497943)
          ·
            refine ⟨4964699422794203733746915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3309799615196135822497943 4964699422794203733746915)
            ·
              refine ⟨7447049134191305600620373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964699422794203733746915 7447049134191305600620373)
              ·
                refine ⟨43635053520652181253635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7447049134191305600620373 43635053520652181253635)
                ·
                  rfl

theorem cell20_286804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_286804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286804 prefixEnd_286804 := by exact prefixLift 286804
  have htrace : WordTrace (prefixWord ++ tailWord_286804) baseStart_286804 baseEnd_286804 := by
    simpa [prefixWord, tailWord_286804, baseEnd_286804] using wordTrace_append hprefix tailTrace_286804
  have hstable : (prefixWord ++ tailWord_286804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286804).length < 2 ^ (prefixWord ++ tailWord_286804).sum := by decide
  have hdescent : baseEnd_286804 < baseStart_286804 := by decide
  rcases family_descends (prefixWord ++ tailWord_286804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286821 : List Nat := [1, 3, 1, 3, 2, 2, 4, 4]
def baseStart_286821 : Nat := 118140960795 + 286821 * 2 ^ 59
def prefixEnd_286821 : Nat := 4983230072969 + 3 ^ 40 * 286821 * 2
def baseEnd_286821 : Nat := 43637639941726680064723

theorem tailTrace_286821 : CollatzResearch.WordTrace tailWord_286821 prefixEnd_286821 43637639941726680064723 := by
  unfold tailWord_286821
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461221293903976972004317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6974147529269317981336211 10461221293903976972004317)
  ·
    refine ⟨3922957985213991364501619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10461221293903976972004317 3922957985213991364501619)
    ·
      refine ⟨5884436977820987046752429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3922957985213991364501619 5884436977820987046752429)
      ·
        refine ⟨2206663866682870142532161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5884436977820987046752429 2206663866682870142532161)
        ·
          refine ⟨1654997900012152606899121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2206663866682870142532161 1654997900012152606899121)
          ·
            refine ⟨1241248425009114455174341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1654997900012152606899121 1241248425009114455174341)
            ·
              refine ⟨232734079689208960345189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1241248425009114455174341 232734079689208960345189)
              ·
                refine ⟨43637639941726680064723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232734079689208960345189 43637639941726680064723)
                ·
                  rfl

theorem cell20_286821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_286821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286821 prefixEnd_286821 := by exact prefixLift 286821
  have htrace : WordTrace (prefixWord ++ tailWord_286821) baseStart_286821 baseEnd_286821 := by
    simpa [prefixWord, tailWord_286821, baseEnd_286821] using wordTrace_append hprefix tailTrace_286821
  have hstable : (prefixWord ++ tailWord_286821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286821).length < 2 ^ (prefixWord ++ tailWord_286821).sum := by decide
  have hdescent : baseEnd_286821 < baseStart_286821 := by decide
  rcases family_descends (prefixWord ++ tailWord_286821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286831 : List Nat := [1, 1, 2, 1, 3, 6, 1, 3, 2]
def baseStart_286831 : Nat := 118140960795 + 286831 * 2 ^ 59
def prefixEnd_286831 : Nat := 4983230072969 + 3 ^ 40 * 286831 * 2
def baseEnd_286831 : Nat := 130917484097664449860795

theorem tailTrace_286831 : CollatzResearch.WordTrace tailWord_286831 prefixEnd_286831 130917484097664449860795 := by
  unfold tailWord_286831
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461586023867748679868347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6974390682578499119912231 10461586023867748679868347)
  ·
    refine ⟨15692379035801623019802521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10461586023867748679868347 15692379035801623019802521)
    ·
      refine ⟨11769284276851217264851891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15692379035801623019802521 11769284276851217264851891)
      ·
        refine ⟨17653926415276825897277837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11769284276851217264851891 17653926415276825897277837)
        ·
          refine ⟨6620222405728809711479189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17653926415276825897277837 6620222405728809711479189)
          ·
            refine ⟨310322925268537955225587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6620222405728809711479189 310322925268537955225587)
            ·
              refine ⟨465484387902806932838381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310322925268537955225587 465484387902806932838381)
              ·
                refine ⟨174556645463552599814393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 465484387902806932838381 174556645463552599814393)
                ·
                  refine ⟨130917484097664449860795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174556645463552599814393 130917484097664449860795)
                  ·
                    rfl

theorem cell20_286831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 2].length) (baseStart_286831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286831 prefixEnd_286831 := by exact prefixLift 286831
  have htrace : WordTrace (prefixWord ++ tailWord_286831) baseStart_286831 baseEnd_286831 := by
    simpa [prefixWord, tailWord_286831, baseEnd_286831] using wordTrace_append hprefix tailTrace_286831
  have hstable : (prefixWord ++ tailWord_286831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286831).length < 2 ^ (prefixWord ++ tailWord_286831).sum := by decide
  have hdescent : baseEnd_286831 < baseStart_286831 := by decide
  rcases family_descends (prefixWord ++ tailWord_286831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286880 : List Nat := [2, 1, 1, 4, 2, 2, 2, 6]
def baseStart_286880 : Nat := 118140960795 + 286880 * 2 ^ 59
def prefixEnd_286880 : Nat := 4983230072969 + 3 ^ 40 * 286880 * 2
def baseEnd_286880 : Nat := 43646616344279352409087

theorem tailTrace_286880 : CollatzResearch.WordTrace tailWord_286880 prefixEnd_286880 43646616344279352409087 := by
  unfold tailWord_286880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5231686600345115024201047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6975582133793486698934729 5231686600345115024201047)
  ·
    refine ⟨7847529900517672536301571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5231686600345115024201047 7847529900517672536301571)
    ·
      refine ⟨11771294850776508804452357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7847529900517672536301571 11771294850776508804452357)
      ·
        refine ⟨2207117784520595400834817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11771294850776508804452357 2207117784520595400834817)
        ·
          refine ⟨1655338338390446550626113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2207117784520595400834817 1655338338390446550626113)
          ·
            refine ⟨1241503753792834912969585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1655338338390446550626113 1241503753792834912969585)
            ·
              refine ⟨931127815344626184727189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241503753792834912969585 931127815344626184727189)
              ·
                refine ⟨43646616344279352409087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 931127815344626184727189 43646616344279352409087)
                ·
                  rfl

theorem cell20_286880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_286880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286880 prefixEnd_286880 := by exact prefixLift 286880
  have htrace : WordTrace (prefixWord ++ tailWord_286880) baseStart_286880 baseEnd_286880 := by
    simpa [prefixWord, tailWord_286880, baseEnd_286880] using wordTrace_append hprefix tailTrace_286880
  have hstable : (prefixWord ++ tailWord_286880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286880).length < 2 ^ (prefixWord ++ tailWord_286880).sum := by decide
  have hdescent : baseEnd_286880 < baseStart_286880 := by decide
  rcases family_descends (prefixWord ++ tailWord_286880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286897 : List Nat := [1, 2, 2, 5, 3, 7]
def baseStart_286897 : Nat := 118140960795 + 286897 * 2 ^ 59
def prefixEnd_286897 : Nat := 4983230072969 + 3 ^ 40 * 286897 * 2
def baseEnd_286897 : Nat := 4849911418372650135575

theorem tailTrace_286897 : CollatzResearch.WordTrace tailWord_286897 prefixEnd_286897 4849911418372650135575 := by
  unfold tailWord_286897
  simp only [CollatzResearch.WordTrace]
  refine ⟨10463993241628641951770945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6975995494419094634513963 10463993241628641951770945)
  ·
    refine ⟨7847994931221481463828209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10463993241628641951770945 7847994931221481463828209)
    ·
      refine ⟨5885996198416111097871157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7847994931221481463828209 5885996198416111097871157)
      ·
        refine ⟨551812143601510415425421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5885996198416111097871157 551812143601510415425421)
        ·
          refine ⟨206929553850566405784533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 551812143601510415425421 206929553850566405784533)
          ·
            refine ⟨4849911418372650135575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 206929553850566405784533 4849911418372650135575)
            ·
              rfl

theorem cell20_286897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 7].length) (baseStart_286897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286897 prefixEnd_286897 := by exact prefixLift 286897
  have htrace : WordTrace (prefixWord ++ tailWord_286897) baseStart_286897 baseEnd_286897 := by
    simpa [prefixWord, tailWord_286897, baseEnd_286897] using wordTrace_append hprefix tailTrace_286897
  have hstable : (prefixWord ++ tailWord_286897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286897).length < 2 ^ (prefixWord ++ tailWord_286897).sum := by decide
  have hdescent : baseEnd_286897 < baseStart_286897 := by decide
  rcases family_descends (prefixWord ++ tailWord_286897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286904 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_286904 : Nat := 118140960795 + 286904 * 2 ^ 59
def prefixEnd_286904 : Nat := 4983230072969 + 3 ^ 40 * 286904 * 2
def baseEnd_286904 : Nat := 130950803286800640427163

theorem tailTrace_286904 : CollatzResearch.WordTrace tailWord_286904 prefixEnd_286904 130950803286800640427163 := by
  unfold tailWord_286904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232124276301641073637883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6976165701735521431517177 5232124276301641073637883)
  ·
    refine ⟨7848186414452461610456825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5232124276301641073637883 7848186414452461610456825)
    ·
      refine ⟨5886139810839346207842619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7848186414452461610456825 5886139810839346207842619)
      ·
        refine ⟨8829209716259019311763929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5886139810839346207842619 8829209716259019311763929)
        ·
          refine ⟨6621907287194264483822947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8829209716259019311763929 6621907287194264483822947)
          ·
            refine ⟨9932860930791396725734421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621907287194264483822947 9932860930791396725734421)
            ·
              refine ⟨465602856130846721518801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9932860930791396725734421 465602856130846721518801)
              ·
                refine ⟨349202142098135041139101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465602856130846721518801 349202142098135041139101)
                ·
                  refine ⟨130950803286800640427163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349202142098135041139101 130950803286800640427163)
                  ·
                    rfl

theorem cell20_286904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_286904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286904 prefixEnd_286904 := by exact prefixLift 286904
  have htrace : WordTrace (prefixWord ++ tailWord_286904) baseStart_286904 baseEnd_286904 := by
    simpa [prefixWord, tailWord_286904, baseEnd_286904] using wordTrace_append hprefix tailTrace_286904
  have hstable : (prefixWord ++ tailWord_286904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286904).length < 2 ^ (prefixWord ++ tailWord_286904).sum := by decide
  have hdescent : baseEnd_286904 < baseStart_286904 := by decide
  rcases family_descends (prefixWord ++ tailWord_286904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286959 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 3]
def baseStart_286959 : Nat := 118140960795 + 286959 * 2 ^ 59
def prefixEnd_286959 : Nat := 4983230072969 + 3 ^ 40 * 286959 * 2
def baseEnd_286959 : Nat := 130975906785464893593605

theorem tailTrace_286959 : CollatzResearch.WordTrace tailWord_286959 prefixEnd_286959 130975906785464893593605 := by
  unfold tailWord_286959
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466254567404026540527931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6977503044936017693685287 10466254567404026540527931)
  ·
    refine ⟨15699381851106039810791897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10466254567404026540527931 15699381851106039810791897)
    ·
      refine ⟨11774536388329529858093923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15699381851106039810791897 11774536388329529858093923)
      ·
        refine ⟨17661804582494294787140885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11774536388329529858093923 17661804582494294787140885)
        ·
          refine ⟨827897089804420068147229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17661804582494294787140885 827897089804420068147229)
          ·
            refine ⟨310461408676657525555211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 827897089804420068147229 310461408676657525555211)
            ·
              refine ⟨465692113014986288332817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310461408676657525555211 465692113014986288332817)
              ·
                refine ⟨349269084761239716249613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465692113014986288332817 349269084761239716249613)
                ·
                  refine ⟨130975906785464893593605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349269084761239716249613 130975906785464893593605)
                  ·
                    rfl

theorem cell20_286959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_286959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286959 prefixEnd_286959 := by exact prefixLift 286959
  have htrace : WordTrace (prefixWord ++ tailWord_286959) baseStart_286959 baseEnd_286959 := by
    simpa [prefixWord, tailWord_286959, baseEnd_286959] using wordTrace_append hprefix tailTrace_286959
  have hstable : (prefixWord ++ tailWord_286959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286959).length < 2 ^ (prefixWord ++ tailWord_286959).sum := by decide
  have hdescent : baseEnd_286959 < baseStart_286959 := by decide
  rcases family_descends (prefixWord ++ tailWord_286959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286963 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_286963 : Nat := 118140960795 + 286963 * 2 ^ 59
def prefixEnd_286963 : Nat := 4983230072969 + 3 ^ 40 * 286963 * 2
def baseEnd_286963 : Nat := 130977732494458657460255

theorem tailTrace_286963 : CollatzResearch.WordTrace tailWord_286963 prefixEnd_286963 130977732494458657460255 := by
  unfold tailWord_286963
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466400459389535223673543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6977600306259690149115695 10466400459389535223673543)
  ·
    refine ⟨15699600689084302835510315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10466400459389535223673543 15699600689084302835510315)
    ·
      refine ⟨23549401033626454253265473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15699600689084302835510315 23549401033626454253265473)
      ·
        refine ⟨17662050775219840689949105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23549401033626454253265473 17662050775219840689949105)
        ·
          refine ⟨13246538081414880517461829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17662050775219840689949105 13246538081414880517461829)
          ·
            refine ⟨2483725890265290097024093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13246538081414880517461829 2483725890265290097024093)
            ·
              refine ⟨931397208849483786384035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2483725890265290097024093 931397208849483786384035)
              ·
                refine ⟨1397095813274225679576053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931397208849483786384035 1397095813274225679576053)
                ·
                  refine ⟨130977732494458657460255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1397095813274225679576053 130977732494458657460255)
                  ·
                    rfl

theorem cell20_286963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_286963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286963 prefixEnd_286963 := by exact prefixLift 286963
  have htrace : WordTrace (prefixWord ++ tailWord_286963) baseStart_286963 baseEnd_286963 := by
    simpa [prefixWord, tailWord_286963, baseEnd_286963] using wordTrace_append hprefix tailTrace_286963
  have hstable : (prefixWord ++ tailWord_286963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286963).length < 2 ^ (prefixWord ++ tailWord_286963).sum := by decide
  have hdescent : baseEnd_286963 < baseStart_286963 := by decide
  rcases family_descends (prefixWord ++ tailWord_286963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287101 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_287101 : Nat := 118140960795 + 287101 * 2 ^ 59
def prefixEnd_287101 : Nat := 4983230072969 + 3 ^ 40 * 287101 * 2
def baseEnd_287101 : Nat := 131040719454743510859691

theorem tailTrace_287101 : CollatzResearch.WordTrace tailWord_287101 prefixEnd_287101 131040719454743510859691 := by
  unfold tailWord_287101
  simp only [CollatzResearch.WordTrace]
  refine ⟨10471433732889584792197157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6980955821926389861464771 10471433732889584792197157)
  ·
    refine ⟨1963393824916797148536967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10471433732889584792197157 1963393824916797148536967)
    ·
      refine ⟨2945090737375195722805451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963393824916797148536967 2945090737375195722805451)
      ·
        refine ⟨4417636106062793584208177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945090737375195722805451 4417636106062793584208177)
        ·
          refine ⟨3313227079547095188156133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4417636106062793584208177 3313227079547095188156133)
          ·
            refine ⟨621230077415080347779275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3313227079547095188156133 621230077415080347779275)
            ·
              refine ⟨931845116122620521668913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621230077415080347779275 931845116122620521668913)
              ·
                refine ⟨698883837091965391251685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931845116122620521668913 698883837091965391251685)
                ·
                  refine ⟨131040719454743510859691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698883837091965391251685 131040719454743510859691)
                  ·
                    rfl

theorem cell20_287101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_287101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287101 prefixEnd_287101 := by exact prefixLift 287101
  have htrace : WordTrace (prefixWord ++ tailWord_287101) baseStart_287101 baseEnd_287101 := by
    simpa [prefixWord, tailWord_287101, baseEnd_287101] using wordTrace_append hprefix tailTrace_287101
  have hstable : (prefixWord ++ tailWord_287101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287101).length < 2 ^ (prefixWord ++ tailWord_287101).sum := by decide
  have hdescent : baseEnd_287101 < baseStart_287101 := by decide
  rcases family_descends (prefixWord ++ tailWord_287101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287114 : List Nat := [3, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_287114 : Nat := 118140960795 + 287114 * 2 ^ 59
def prefixEnd_287114 : Nat := 4983230072969 + 3 ^ 40 * 287114 * 2
def baseEnd_287114 : Nat := 131046653008973243426305

theorem tailTrace_287114 : CollatzResearch.WordTrace tailWord_287114 prefixEnd_287114 131046653008973243426305 := by
  unfold tailWord_287114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617976970460622003105099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6981271921228325341613597 2617976970460622003105099)
  ·
    refine ⟨3926965455690933004657649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2617976970460622003105099 3926965455690933004657649)
    ·
      refine ⟨2945224091768199753493237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3926965455690933004657649 2945224091768199753493237)
      ·
        refine ⟨276114758603268726889991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2945224091768199753493237 276114758603268726889991)
        ·
          refine ⟨414172137904903090334987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276114758603268726889991 414172137904903090334987)
          ·
            refine ⟨621258206857354635502481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414172137904903090334987 621258206857354635502481)
            ·
              refine ⟨465943655143015976626861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621258206857354635502481 465943655143015976626861)
              ·
                refine ⟨174728870678630991235073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 465943655143015976626861 174728870678630991235073)
                ·
                  refine ⟨131046653008973243426305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174728870678630991235073 131046653008973243426305)
                  ·
                    rfl

theorem cell20_287114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_287114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287114 prefixEnd_287114 := by exact prefixLift 287114
  have htrace : WordTrace (prefixWord ++ tailWord_287114) baseStart_287114 baseEnd_287114 := by
    simpa [prefixWord, tailWord_287114, baseEnd_287114] using wordTrace_append hprefix tailTrace_287114
  have hstable : (prefixWord ++ tailWord_287114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287114).length < 2 ^ (prefixWord ++ tailWord_287114).sum := by decide
  have hdescent : baseEnd_287114 < baseStart_287114 := by decide
  rcases family_descends (prefixWord ++ tailWord_287114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287129 : List Nat := [1, 2, 1, 2, 1, 4, 9]
def baseStart_287129 : Nat := 118140960795 + 287129 * 2 ^ 59
def prefixEnd_287129 : Nat := 4983230072969 + 3 ^ 40 * 287129 * 2
def baseEnd_287129 : Nat := 14561499935299984214027

theorem tailTrace_287129 : CollatzResearch.WordTrace tailWord_287129 prefixEnd_287129 14561499935299984214027 := by
  unfold tailWord_287129
  simp only [CollatzResearch.WordTrace]
  refine ⟨10472454976788145574216441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6981636651192097049477627 10472454976788145574216441)
  ·
    refine ⟨7854341232591109180662331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10472454976788145574216441 7854341232591109180662331)
    ·
      refine ⟨11781511848886663770993497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7854341232591109180662331 11781511848886663770993497)
      ·
        refine ⟨8836133886664997828245123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11781511848886663770993497 8836133886664997828245123)
        ·
          refine ⟨13254200829997496742367685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8836133886664997828245123 13254200829997496742367685)
          ·
            refine ⟨2485162655624530639193941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13254200829997496742367685 2485162655624530639193941)
            ·
              refine ⟨14561499935299984214027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2485162655624530639193941 14561499935299984214027)
              ·
                rfl

theorem cell20_287129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_287129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287129 prefixEnd_287129 := by exact prefixLift 287129
  have htrace : WordTrace (prefixWord ++ tailWord_287129) baseStart_287129 baseEnd_287129 := by
    simpa [prefixWord, tailWord_287129, baseEnd_287129] using wordTrace_append hprefix tailTrace_287129
  have hstable : (prefixWord ++ tailWord_287129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287129).length < 2 ^ (prefixWord ++ tailWord_287129).sum := by decide
  have hdescent : baseEnd_287129 < baseStart_287129 := by decide
  rcases family_descends (prefixWord ++ tailWord_287129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287139 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_287139 : Nat := 118140960795 + 287139 * 2 ^ 59
def prefixEnd_287139 : Nat := 4983230072969 + 3 ^ 40 * 287139 * 2
def baseEnd_287139 : Nat := 131058063690184267592869

theorem tailTrace_287139 : CollatzResearch.WordTrace tailWord_287139 prefixEnd_287139 131058063690184267592869 := by
  unfold tailWord_287139
  simp only [CollatzResearch.WordTrace]
  refine ⟨10472819706751917282080471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6981879804501278188053647 10472819706751917282080471)
  ·
    refine ⟨15709229560127875923120707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10472819706751917282080471 15709229560127875923120707)
    ·
      refine ⟨23563844340191813884681061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15709229560127875923120707 23563844340191813884681061)
      ·
        refine ⟨4418220813785965103377699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23563844340191813884681061 4418220813785965103377699)
        ·
          refine ⟨6627331220678947655066549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4418220813785965103377699 6627331220678947655066549)
          ·
            refine ⟨621312301938651342662489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6627331220678947655066549 621312301938651342662489)
            ·
              refine ⟨465984226453988506996867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621312301938651342662489 465984226453988506996867)
              ·
                refine ⟨698976339680982760495301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465984226453988506996867 698976339680982760495301)
                ·
                  refine ⟨131058063690184267592869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698976339680982760495301 131058063690184267592869)
                  ·
                    rfl

theorem cell20_287139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_287139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287139 prefixEnd_287139 := by exact prefixLift 287139
  have htrace : WordTrace (prefixWord ++ tailWord_287139) baseStart_287139 baseEnd_287139 := by
    simpa [prefixWord, tailWord_287139, baseEnd_287139] using wordTrace_append hprefix tailTrace_287139
  have hstable : (prefixWord ++ tailWord_287139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287139).length < 2 ^ (prefixWord ++ tailWord_287139).sum := by decide
  have hdescent : baseEnd_287139 < baseStart_287139 := by decide
  rcases family_descends (prefixWord ++ tailWord_287139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287190 : List Nat := [5, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_287190 : Nat := 118140960795 + 287190 * 2 ^ 59
def prefixEnd_287190 : Nat := 4983230072969 + 3 ^ 40 * 287190 * 2
def baseEnd_287190 : Nat := 131081341479854756892661

theorem tailTrace_287190 : CollatzResearch.WordTrace tailWord_287190 prefixEnd_287190 131081341479854756892661 := by
  unfold tailWord_287190
  simp only [CollatzResearch.WordTrace]
  refine ⟨654667489347947062011689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6983119886378101994791349 654667489347947062011689)
  ·
    refine ⟨491000617010960296508767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 654667489347947062011689 491000617010960296508767)
    ·
      refine ⟨736500925516440444763151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491000617010960296508767 736500925516440444763151)
      ·
        refine ⟨1104751388274660667144727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736500925516440444763151 1104751388274660667144727)
        ·
          refine ⟨1657127082411991000717091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104751388274660667144727 1657127082411991000717091)
          ·
            refine ⟨2485690623617986501075637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657127082411991000717091 2485690623617986501075637)
            ·
              refine ⟨233033495964186234475841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2485690623617986501075637 233033495964186234475841)
              ·
                refine ⟨174775121973139675856881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233033495964186234475841 174775121973139675856881)
                ·
                  refine ⟨131081341479854756892661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174775121973139675856881 131081341479854756892661)
                  ·
                    rfl

theorem cell20_287190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_287190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287190 prefixEnd_287190 := by exact prefixLift 287190
  have htrace : WordTrace (prefixWord ++ tailWord_287190) baseStart_287190 baseEnd_287190 := by
    simpa [prefixWord, tailWord_287190, baseEnd_287190] using wordTrace_append hprefix tailTrace_287190
  have hstable : (prefixWord ++ tailWord_287190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287190).length < 2 ^ (prefixWord ++ tailWord_287190).sum := by decide
  have hdescent : baseEnd_287190 < baseStart_287190 := by decide
  rcases family_descends (prefixWord ++ tailWord_287190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287208 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_287208 : Nat := 118140960795 + 287208 * 2 ^ 59
def prefixEnd_287208 : Nat := 4983230072969 + 3 ^ 40 * 287208 * 2
def baseEnd_287208 : Nat := 131089557170326694292587

theorem tailTrace_287208 : CollatzResearch.WordTrace tailWord_287208 prefixEnd_287208 131089557170326694292587 := by
  unfold tailWord_287208
  simp only [CollatzResearch.WordTrace]
  refine ⟨5237668171750971033171139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6983557562334628044228185 5237668171750971033171139)
  ·
    refine ⟨7856502257626456549756709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5237668171750971033171139 7856502257626456549756709)
    ·
      refine ⟨1473094173304960603079383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7856502257626456549756709 1473094173304960603079383)
      ·
        refine ⟨2209641259957440904619075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473094173304960603079383 2209641259957440904619075)
        ·
          refine ⟨3314461889936161356928613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209641259957440904619075 3314461889936161356928613)
          ·
            refine ⟨621461604363030254424115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3314461889936161356928613 621461604363030254424115)
            ·
              refine ⟨932192406544545381636173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621461604363030254424115 932192406544545381636173)
              ·
                refine ⟨349572152454204518113565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 932192406544545381636173 349572152454204518113565)
                ·
                  refine ⟨131089557170326694292587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349572152454204518113565 131089557170326694292587)
                  ·
                    rfl

theorem cell20_287208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_287208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287208 prefixEnd_287208 := by exact prefixLift 287208
  have htrace : WordTrace (prefixWord ++ tailWord_287208) baseStart_287208 baseEnd_287208 := by
    simpa [prefixWord, tailWord_287208, baseEnd_287208] using wordTrace_append hprefix tailTrace_287208
  have hstable : (prefixWord ++ tailWord_287208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287208).length < 2 ^ (prefixWord ++ tailWord_287208).sum := by decide
  have hdescent : baseEnd_287208 < baseStart_287208 := by decide
  rcases family_descends (prefixWord ++ tailWord_287208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287222 : List Nat := [5, 1, 1, 1, 2, 1, 1, 8]
def baseStart_287222 : Nat := 118140960795 + 287222 * 2 ^ 59
def prefixEnd_287222 : Nat := 4983230072969 + 3 ^ 40 * 287222 * 2
def baseEnd_287222 : Nat := 43698649050601622608621

theorem tailTrace_287222 : CollatzResearch.WordTrace tailWord_287222 prefixEnd_287222 43698649050601622608621 := by
  unfold tailWord_287222
  simp only [CollatzResearch.WordTrace]
  refine ⟨654740435340701403584495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6983897976967481638234613 654740435340701403584495)
  ·
    refine ⟨982110653011052105376743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 654740435340701403584495 982110653011052105376743)
    ·
      refine ⟨1473165979516578158065115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982110653011052105376743 1473165979516578158065115)
      ·
        refine ⟨2209748969274867237097673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473165979516578158065115 2209748969274867237097673)
        ·
          refine ⟨1657311726956150427823255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2209748969274867237097673 1657311726956150427823255)
          ·
            refine ⟨2485967590434225641734883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657311726956150427823255 2485967590434225641734883)
            ·
              refine ⟨3728951385651338462602325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485967590434225641734883 3728951385651338462602325)
              ·
                refine ⟨43698649050601622608621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3728951385651338462602325 43698649050601622608621)
                ·
                  rfl

theorem cell20_287222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_287222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287222 prefixEnd_287222 := by exact prefixLift 287222
  have htrace : WordTrace (prefixWord ++ tailWord_287222) baseStart_287222 baseEnd_287222 := by
    simpa [prefixWord, tailWord_287222, baseEnd_287222] using wordTrace_append hprefix tailTrace_287222
  have hstable : (prefixWord ++ tailWord_287222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287222).length < 2 ^ (prefixWord ++ tailWord_287222).sum := by decide
  have hdescent : baseEnd_287222 < baseStart_287222 := by decide
  rcases family_descends (prefixWord ++ tailWord_287222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287243 : List Nat := [1, 1, 1, 1, 7, 9]
def baseStart_287243 : Nat := 118140960795 + 287243 * 2 ^ 59
def prefixEnd_287243 : Nat := 4983230072969 + 3 ^ 40 * 287243 * 2
def baseEnd_287243 : Nat := 4855760449037856597251

theorem tailTrace_287243 : CollatzResearch.WordTrace tailWord_287243 prefixEnd_287243 4855760449037856597251 := by
  unfold tailWord_287243
  simp only [CollatzResearch.WordTrace]
  refine ⟨10476612898375143043866383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6984408598916762029244255 10476612898375143043866383)
  ·
    refine ⟨15714919347562714565799575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10476612898375143043866383 15714919347562714565799575)
    ·
      refine ⟨23572379021344071848699363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15714919347562714565799575 23572379021344071848699363)
      ·
        refine ⟨35358568532016107773049045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23572379021344071848699363 35358568532016107773049045)
        ·
          refine ⟨828716449969127525930837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35358568532016107773049045 828716449969127525930837)
          ·
            refine ⟨4855760449037856597251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 828716449969127525930837 4855760449037856597251)
            ·
              rfl

theorem cell20_287243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 9].length) (baseStart_287243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287243 prefixEnd_287243 := by exact prefixLift 287243
  have htrace : WordTrace (prefixWord ++ tailWord_287243) baseStart_287243 baseEnd_287243 := by
    simpa [prefixWord, tailWord_287243, baseEnd_287243] using wordTrace_append hprefix tailTrace_287243
  have hstable : (prefixWord ++ tailWord_287243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287243).length < 2 ^ (prefixWord ++ tailWord_287243).sum := by decide
  have hdescent : baseEnd_287243 < baseStart_287243 := by decide
  rcases family_descends (prefixWord ++ tailWord_287243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287245 : List Nat := [1, 7, 1, 1, 1, 1, 4, 2, 2]
def baseStart_287245 : Nat := 118140960795 + 287245 * 2 ^ 59
def prefixEnd_287245 : Nat := 4983230072969 + 3 ^ 40 * 287245 * 2
def baseEnd_287245 : Nat := 131106444978519010059103

theorem tailTrace_287245 : CollatzResearch.WordTrace tailWord_287245 prefixEnd_287245 131106444978519010059103 := by
  unfold tailWord_287245
  simp only [CollatzResearch.WordTrace]
  refine ⟨10476685844367897385439189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6984457229578598256959459 10476685844367897385439189)
  ·
    refine ⟨245547324477372594971231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10476685844367897385439189 245547324477372594971231)
    ·
      refine ⟨368320986716058892456847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245547324477372594971231 368320986716058892456847)
      ·
        refine ⟨552481480074088338685271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368320986716058892456847 552481480074088338685271)
        ·
          refine ⟨828722220111132508027907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552481480074088338685271 828722220111132508027907)
          ·
            refine ⟨1243083330166698762041861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828722220111132508027907 1243083330166698762041861)
            ·
              refine ⟨233078124406256017882849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1243083330166698762041861 233078124406256017882849)
              ·
                refine ⟨174808593304692013412137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233078124406256017882849 174808593304692013412137)
                ·
                  refine ⟨131106444978519010059103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174808593304692013412137 131106444978519010059103)
                  ·
                    rfl

theorem cell20_287245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_287245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287245 prefixEnd_287245 := by exact prefixLift 287245
  have htrace : WordTrace (prefixWord ++ tailWord_287245) baseStart_287245 baseEnd_287245 := by
    simpa [prefixWord, tailWord_287245, baseEnd_287245] using wordTrace_append hprefix tailTrace_287245
  have hstable : (prefixWord ++ tailWord_287245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287245).length < 2 ^ (prefixWord ++ tailWord_287245).sum := by decide
  have hdescent : baseEnd_287245 < baseStart_287245 := by decide
  rcases family_descends (prefixWord ++ tailWord_287245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287246 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_287246 : Nat := 118140960795 + 287246 * 2 ^ 59
def prefixEnd_287246 : Nat := 4983230072969 + 3 ^ 40 * 287246 * 2
def baseEnd_287246 : Nat := 131106901405767451025765

theorem tailTrace_287246 : CollatzResearch.WordTrace tailWord_287246 prefixEnd_287246 131106901405767451025765 := by
  unfold tailWord_287246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309590289670534319528199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6984481544909516370817061 1309590289670534319528199)
  ·
    refine ⟨1964385434505801479292299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1309590289670534319528199 1964385434505801479292299)
    ·
      refine ⟨2946578151758702218938449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1964385434505801479292299 2946578151758702218938449)
      ·
        refine ⟨2209933613819026664203837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2946578151758702218938449 2209933613819026664203837)
        ·
          refine ⟨828725105182134999076439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2209933613819026664203837 828725105182134999076439)
          ·
            refine ⟨1243087657773202498614659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828725105182134999076439 1243087657773202498614659)
            ·
              refine ⟨1864631486659803747921989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243087657773202498614659 1864631486659803747921989)
              ·
                refine ⟨349618403748713202735373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1864631486659803747921989 349618403748713202735373)
                ·
                  refine ⟨131106901405767451025765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349618403748713202735373 131106901405767451025765)
                  ·
                    rfl

theorem cell20_287246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_287246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287246 prefixEnd_287246 := by exact prefixLift 287246
  have htrace : WordTrace (prefixWord ++ tailWord_287246) baseStart_287246 baseEnd_287246 := by
    simpa [prefixWord, tailWord_287246, baseEnd_287246] using wordTrace_append hprefix tailTrace_287246
  have hstable : (prefixWord ++ tailWord_287246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287246).length < 2 ^ (prefixWord ++ tailWord_287246).sum := by decide
  have hdescent : baseEnd_287246 < baseStart_287246 := by decide
  rcases family_descends (prefixWord ++ tailWord_287246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287260 : List Nat := [2, 2, 3, 1, 2, 2, 3, 5]
def baseStart_287260 : Nat := 118140960795 + 287260 * 2 ^ 59
def prefixEnd_287260 : Nat := 4983230072969 + 3 ^ 40 * 287260 * 2
def baseEnd_287260 : Nat := 43704430462415208186347

theorem tailTrace_287260 : CollatzResearch.WordTrace tailWord_287260 prefixEnd_287260 43704430462415208186347 := by
  unfold tailWord_287260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5238616469656777473617617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6984821959542369964823489 5238616469656777473617617)
  ·
    refine ⟨3928962352242583105213213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5238616469656777473617617 3928962352242583105213213)
    ·
      refine ⟨1473360882090968664454955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3928962352242583105213213 1473360882090968664454955)
      ·
        refine ⟨2210041323136452996682433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473360882090968664454955 2210041323136452996682433)
        ·
          refine ⟨1657530992352339747511825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210041323136452996682433 1657530992352339747511825)
          ·
            refine ⟨1243148244264254810633869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657530992352339747511825 1243148244264254810633869)
            ·
              refine ⟨466180591599095553987701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243148244264254810633869 466180591599095553987701)
              ·
                refine ⟨43704430462415208186347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466180591599095553987701 43704430462415208186347)
                ·
                  rfl

theorem cell20_287260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_287260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287260 prefixEnd_287260 := by exact prefixLift 287260
  have htrace : WordTrace (prefixWord ++ tailWord_287260) baseStart_287260 baseEnd_287260 := by
    simpa [prefixWord, tailWord_287260, baseEnd_287260] using wordTrace_append hprefix tailTrace_287260
  have hstable : (prefixWord ++ tailWord_287260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287260).length < 2 ^ (prefixWord ++ tailWord_287260).sum := by decide
  have hdescent : baseEnd_287260 < baseStart_287260 := by decide
  rcases family_descends (prefixWord ++ tailWord_287260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287281 : List Nat := [1, 2, 2, 3, 1, 1, 2, 8]
def baseStart_287281 : Nat := 118140960795 + 287281 * 2 ^ 59
def prefixEnd_287281 : Nat := 4983230072969 + 3 ^ 40 * 287281 * 2
def baseEnd_287281 : Nat := 43707625453154294952985

theorem tailTrace_287281 : CollatzResearch.WordTrace tailWord_287281 prefixEnd_287281 43707625453154294952985 := by
  unfold tailWord_287281
  simp only [CollatzResearch.WordTrace]
  refine ⟨10477998872237475533749697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6985332581491650355833131 10477998872237475533749697)
  ·
    refine ⟨7858499154178106650312273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10477998872237475533749697 7858499154178106650312273)
    ·
      refine ⟨5893874365633579987734205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7858499154178106650312273 5893874365633579987734205)
      ·
        refine ⟨2210202887112592495400327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5893874365633579987734205 2210202887112592495400327)
        ·
          refine ⟨3315304330668888743100491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210202887112592495400327 3315304330668888743100491)
          ·
            refine ⟨4972956496003333114650737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315304330668888743100491 4972956496003333114650737)
            ·
              refine ⟨3729717372002499835988053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4972956496003333114650737 3729717372002499835988053)
              ·
                refine ⟨43707625453154294952985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3729717372002499835988053 43707625453154294952985)
                ·
                  rfl

theorem cell20_287281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_287281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287281 prefixEnd_287281 := by exact prefixLift 287281
  have htrace : WordTrace (prefixWord ++ tailWord_287281) baseStart_287281 baseEnd_287281 := by
    simpa [prefixWord, tailWord_287281, baseEnd_287281] using wordTrace_append hprefix tailTrace_287281
  have hstable : (prefixWord ++ tailWord_287281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287281).length < 2 ^ (prefixWord ++ tailWord_287281).sum := by decide
  have hdescent : baseEnd_287281 < baseStart_287281 := by decide
  rcases family_descends (prefixWord ++ tailWord_287281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287319 : List Nat := [1, 1, 3, 2, 2, 2, 2, 7]
def baseStart_287319 : Nat := 118140960795 + 287319 * 2 ^ 59
def prefixEnd_287319 : Nat := 4983230072969 + 3 ^ 40 * 287319 * 2
def baseEnd_287319 : Nat := 43713406864967880530711

theorem tailTrace_287319 : CollatzResearch.WordTrace tailWord_287319 prefixEnd_287319 43713406864967880530711 := by
  unfold tailWord_287319
  simp only [CollatzResearch.WordTrace]
  refine ⟨10479384846099808023633011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6986256564066538682422007 10479384846099808023633011)
  ·
    refine ⟨15719077269149712035449517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10479384846099808023633011 15719077269149712035449517)
    ·
      refine ⟨5894653975931142013293569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15719077269149712035449517 5894653975931142013293569)
      ·
        refine ⟨4420990481948356509970177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5894653975931142013293569 4420990481948356509970177)
        ·
          refine ⟨3315742861461267382477633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4420990481948356509970177 3315742861461267382477633)
          ·
            refine ⟨2486807146095950536858225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315742861461267382477633 2486807146095950536858225)
            ·
              refine ⟨1865105359571962902643669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486807146095950536858225 1865105359571962902643669)
              ·
                refine ⟨43713406864967880530711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1865105359571962902643669 43713406864967880530711)
                ·
                  rfl

theorem cell20_287319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_287319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287319 prefixEnd_287319 := by exact prefixLift 287319
  have htrace : WordTrace (prefixWord ++ tailWord_287319) baseStart_287319 baseEnd_287319 := by
    simpa [prefixWord, tailWord_287319, baseEnd_287319] using wordTrace_append hprefix tailTrace_287319
  have hstable : (prefixWord ++ tailWord_287319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287319).length < 2 ^ (prefixWord ++ tailWord_287319).sum := by decide
  have hdescent : baseEnd_287319 < baseStart_287319 := by decide
  rcases family_descends (prefixWord ++ tailWord_287319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287374 : List Nat := [4, 1, 1, 3, 1, 1, 4, 5]
def baseStart_287374 : Nat := 118140960795 + 287374 * 2 ^ 59
def prefixEnd_287374 : Nat := 4983230072969 + 3 ^ 40 * 287374 * 2
def baseEnd_287374 : Nat := 43721774697855964919525

theorem tailTrace_287374 : CollatzResearch.WordTrace tailWord_287374 prefixEnd_287374 43721774697855964919525 := by
  unfold tailWord_287374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310173857612569052110647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6987593907267034944590117 1310173857612569052110647)
  ·
    refine ⟨1965260786418853578165971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1310173857612569052110647 1965260786418853578165971)
    ·
      refine ⟨2947891179628280367248957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965260786418853578165971 2947891179628280367248957)
      ·
        refine ⟨1105459192360605137718359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2947891179628280367248957 1105459192360605137718359)
        ·
          refine ⟨1658188788540907706577539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105459192360605137718359 1658188788540907706577539)
          ·
            refine ⟨2487283182811361559866309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658188788540907706577539 2487283182811361559866309)
            ·
              refine ⟨466365596777130292474933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2487283182811361559866309 466365596777130292474933)
              ·
                refine ⟨43721774697855964919525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466365596777130292474933 43721774697855964919525)
                ·
                  rfl

theorem cell20_287374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_287374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287374 prefixEnd_287374 := by exact prefixLift 287374
  have htrace : WordTrace (prefixWord ++ tailWord_287374) baseStart_287374 baseEnd_287374 := by
    simpa [prefixWord, tailWord_287374, baseEnd_287374] using wordTrace_append hprefix tailTrace_287374
  have hstable : (prefixWord ++ tailWord_287374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287374).length < 2 ^ (prefixWord ++ tailWord_287374).sum := by decide
  have hdescent : baseEnd_287374 < baseStart_287374 := by decide
  rcases family_descends (prefixWord ++ tailWord_287374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287414 : List Nat := [5, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_287414 : Nat := 118140960795 + 287414 * 2 ^ 59
def prefixEnd_287414 : Nat := 4983230072969 + 3 ^ 40 * 287414 * 2
def baseEnd_287414 : Nat := 131183581183505533425079

theorem tailTrace_287414 : CollatzResearch.WordTrace tailWord_287414 prefixEnd_287414 131183581183505533425079 := by
  unfold tailWord_287414
  simp only [CollatzResearch.WordTrace]
  refine ⟨655178111297227453021331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6988566520503759498894197 655178111297227453021331)
  ·
    refine ⟨982767166945841179531997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655178111297227453021331 982767166945841179531997)
    ·
      refine ⟨368537687604690442324499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 982767166945841179531997 368537687604690442324499)
      ·
        refine ⟨552806531407035663486749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368537687604690442324499 552806531407035663486749)
        ·
          refine ⟨207302449277638373807531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 552806531407035663486749 207302449277638373807531)
          ·
            refine ⟨310953673916457560711297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207302449277638373807531 310953673916457560711297)
            ·
              refine ⟨233215255437343170533473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310953673916457560711297 233215255437343170533473)
              ·
                refine ⟨174911441578007377900105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233215255437343170533473 174911441578007377900105)
                ·
                  refine ⟨131183581183505533425079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174911441578007377900105 131183581183505533425079)
                  ·
                    rfl

theorem cell20_287414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_287414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287414 prefixEnd_287414 := by exact prefixLift 287414
  have htrace : WordTrace (prefixWord ++ tailWord_287414) baseStart_287414 baseEnd_287414 := by
    simpa [prefixWord, tailWord_287414, baseEnd_287414] using wordTrace_append hprefix tailTrace_287414
  have hstable : (prefixWord ++ tailWord_287414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287414).length < 2 ^ (prefixWord ++ tailWord_287414).sum := by decide
  have hdescent : baseEnd_287414 < baseStart_287414 := by decide
  rcases family_descends (prefixWord ++ tailWord_287414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287422 : List Nat := [4, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_287422 : Nat := 118140960795 + 287422 * 2 ^ 59
def prefixEnd_287422 : Nat := 4983230072969 + 3 ^ 40 * 287422 * 2
def baseEnd_287422 : Nat := 131187232601493061158379

theorem tailTrace_287422 : CollatzResearch.WordTrace tailWord_287422 prefixEnd_287422 131187232601493061158379 := by
  unfold tailWord_287422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310392695590832076829065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6988761043151104409755013 1310392695590832076829065)
  ·
    refine ⟨982794521693124057621799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1310392695590832076829065 982794521693124057621799)
    ·
      refine ⟨1474191782539686086432699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982794521693124057621799 1474191782539686086432699)
      ·
        refine ⟨2211287673809529129649049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474191782539686086432699 2211287673809529129649049)
        ·
          refine ⟨1658465755357146847236787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211287673809529129649049 1658465755357146847236787)
          ·
            refine ⟨2487698633035720270855181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658465755357146847236787 2487698633035720270855181)
            ·
              refine ⟨932886987388395101570693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2487698633035720270855181 932886987388395101570693)
              ·
                refine ⟨174916310135324081544505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 932886987388395101570693 174916310135324081544505)
                ·
                  refine ⟨131187232601493061158379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174916310135324081544505 131187232601493061158379)
                  ·
                    rfl

theorem cell20_287422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_287422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287422 prefixEnd_287422 := by exact prefixLift 287422
  have htrace : WordTrace (prefixWord ++ tailWord_287422) baseStart_287422 baseEnd_287422 := by
    simpa [prefixWord, tailWord_287422, baseEnd_287422] using wordTrace_append hprefix tailTrace_287422
  have hstable : (prefixWord ++ tailWord_287422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287422).length < 2 ^ (prefixWord ++ tailWord_287422).sum := by decide
  have hdescent : baseEnd_287422 < baseStart_287422 := by decide
  rcases family_descends (prefixWord ++ tailWord_287422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287425 : List Nat := [1, 2, 6, 2, 2, 1, 1, 5]
def baseStart_287425 : Nat := 118140960795 + 287425 * 2 ^ 59
def prefixEnd_287425 : Nat := 4983230072969 + 3 ^ 40 * 287425 * 2
def baseEnd_287425 : Nat := 43729533961079461352789

theorem tailTrace_287425 : CollatzResearch.WordTrace tailWord_287425 prefixEnd_287425 43729533961079461352789 := by
  unfold tailWord_287425
  simp only [CollatzResearch.WordTrace]
  refine ⟨10483250983715788126991729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6988833989143858751327819 10483250983715788126991729)
  ·
    refine ⟨7862438237786841095243797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10483250983715788126991729 7862438237786841095243797)
    ·
      refine ⟨368551792396258176339553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7862438237786841095243797 368551792396258176339553)
      ·
        refine ⟨276413844297193632254665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368551792396258176339553 276413844297193632254665)
        ·
          refine ⟨207310383222895224190999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276413844297193632254665 207310383222895224190999)
          ·
            refine ⟨310965574834342836286499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207310383222895224190999 310965574834342836286499)
            ·
              refine ⟨466448362251514254429749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310965574834342836286499 466448362251514254429749)
              ·
                refine ⟨43729533961079461352789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466448362251514254429749 43729533961079461352789)
                ·
                  rfl

theorem cell20_287425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5].length) (baseStart_287425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287425 prefixEnd_287425 := by exact prefixLift 287425
  have htrace : WordTrace (prefixWord ++ tailWord_287425) baseStart_287425 baseEnd_287425 := by
    simpa [prefixWord, tailWord_287425, baseEnd_287425] using wordTrace_append hprefix tailTrace_287425
  have hstable : (prefixWord ++ tailWord_287425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287425).length < 2 ^ (prefixWord ++ tailWord_287425).sum := by decide
  have hdescent : baseEnd_287425 < baseStart_287425 := by decide
  rcases family_descends (prefixWord ++ tailWord_287425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287436 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_287436 : Nat := 118140960795 + 287436 * 2 ^ 59
def prefixEnd_287436 : Nat := 4983230072969 + 3 ^ 40 * 287436 * 2
def baseEnd_287436 : Nat := 131193622582971234691655

theorem tailTrace_287436 : CollatzResearch.WordTrace tailWord_287436 prefixEnd_287436 131193622582971234691655 := by
  unfold tailWord_287436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5241826093337968502821081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6989101457783958003761441 5241826093337968502821081)
  ·
    refine ⟨3931369570003476377115811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5241826093337968502821081 3931369570003476377115811)
    ·
      refine ⟨5897054355005214565673717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931369570003476377115811 5897054355005214565673717)
      ·
        refine ⟨552848845781738865531911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5897054355005214565673717 552848845781738865531911)
        ·
          refine ⟨829273268672608298297867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552848845781738865531911 829273268672608298297867)
          ·
            refine ⟨1243909903008912447446801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829273268672608298297867 1243909903008912447446801)
            ·
              refine ⟨932932427256684335585101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1243909903008912447446801 932932427256684335585101)
              ·
                refine ⟨349849660221256625844413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 932932427256684335585101 349849660221256625844413)
                ·
                  refine ⟨131193622582971234691655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349849660221256625844413 131193622582971234691655)
                  ·
                    rfl

theorem cell20_287436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_287436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287436 prefixEnd_287436 := by exact prefixLift 287436
  have htrace : WordTrace (prefixWord ++ tailWord_287436) baseStart_287436 baseEnd_287436 := by
    simpa [prefixWord, tailWord_287436, baseEnd_287436] using wordTrace_append hprefix tailTrace_287436
  have hstable : (prefixWord ++ tailWord_287436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287436).length < 2 ^ (prefixWord ++ tailWord_287436).sum := by decide
  have hdescent : baseEnd_287436 < baseStart_287436 := by decide
  rcases family_descends (prefixWord ++ tailWord_287436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287450 : List Nat := [3, 1, 1, 2, 2, 2, 5, 4]
def baseStart_287450 : Nat := 118140960795 + 287450 * 2 ^ 59
def prefixEnd_287450 : Nat := 4983230072969 + 3 ^ 40 * 287450 * 2
def baseEnd_287450 : Nat := 43733337521483136074977

theorem tailTrace_287450 : CollatzResearch.WordTrace tailWord_287450 prefixEnd_287450 43733337521483136074977 := by
  unfold tailWord_287450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621040702156304349162951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6989441872416811597767869 2621040702156304349162951)
  ·
    refine ⟨3931561053234456523744427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2621040702156304349162951 3931561053234456523744427)
    ·
      refine ⟨5897341579851684785616641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931561053234456523744427 5897341579851684785616641)
      ·
        refine ⟨4423006184888763589212481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5897341579851684785616641 4423006184888763589212481)
        ·
          refine ⟨3317254638666572691909361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4423006184888763589212481 3317254638666572691909361)
          ·
            refine ⟨2487940978999929518932021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3317254638666572691909361 2487940978999929518932021)
            ·
              refine ⟨233244466781243392399877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2487940978999929518932021 233244466781243392399877)
              ·
                refine ⟨43733337521483136074977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233244466781243392399877 43733337521483136074977)
                ·
                  rfl

theorem cell20_287450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_287450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287450 prefixEnd_287450 := by exact prefixLift 287450
  have htrace : WordTrace (prefixWord ++ tailWord_287450) baseStart_287450 baseEnd_287450 := by
    simpa [prefixWord, tailWord_287450, baseEnd_287450] using wordTrace_append hprefix tailTrace_287450
  have hstable : (prefixWord ++ tailWord_287450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287450).length < 2 ^ (prefixWord ++ tailWord_287450).sum := by decide
  have hdescent : baseEnd_287450 < baseStart_287450 := by decide
  rcases family_descends (prefixWord ++ tailWord_287450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287460 : List Nat := [2, 3, 1, 1, 1, 5, 2, 3, 2]
def baseStart_287460 : Nat := 118140960795 + 287460 * 2 ^ 59
def prefixEnd_287460 : Nat := 4983230072969 + 3 ^ 40 * 287460 * 2
def baseEnd_287460 : Nat := 131204576836933817891557

theorem tailTrace_287460 : CollatzResearch.WordTrace tailWord_287460 prefixEnd_287460 131204576836933817891557 := by
  unfold tailWord_287460
  simp only [CollatzResearch.WordTrace]
  refine ⟨5242263769294494552257917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6989685025725992736343889 5242263769294494552257917)
  ·
    refine ⟨1965848913485435457096719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5242263769294494552257917 1965848913485435457096719)
    ·
      refine ⟨2948773370228153185645079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965848913485435457096719 2948773370228153185645079)
      ·
        refine ⟨4423160055342229778467619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948773370228153185645079 4423160055342229778467619)
        ·
          refine ⟨6634740083013344667701429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4423160055342229778467619 6634740083013344667701429)
          ·
            refine ⟨622006882782501062597009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6634740083013344667701429 622006882782501062597009)
            ·
              refine ⟨466505162086875796947757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622006882782501062597009 466505162086875796947757)
              ·
                refine ⟨174939435782578423855409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466505162086875796947757 174939435782578423855409)
                ·
                  refine ⟨131204576836933817891557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174939435782578423855409 131204576836933817891557)
                  ·
                    rfl

theorem cell20_287460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_287460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287460 prefixEnd_287460 := by exact prefixLift 287460
  have htrace : WordTrace (prefixWord ++ tailWord_287460) baseStart_287460 baseEnd_287460 := by
    simpa [prefixWord, tailWord_287460, baseEnd_287460] using wordTrace_append hprefix tailTrace_287460
  have hstable : (prefixWord ++ tailWord_287460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287460).length < 2 ^ (prefixWord ++ tailWord_287460).sum := by decide
  have hdescent : baseEnd_287460 < baseStart_287460 := by decide
  rcases family_descends (prefixWord ++ tailWord_287460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287471 : List Nat := [1, 1, 2, 1, 5, 3, 7]
def baseStart_287471 : Nat := 118140960795 + 287471 * 2 ^ 59
def prefixEnd_287471 : Nat := 4983230072969 + 3 ^ 40 * 287471 * 2
def baseEnd_287471 : Nat := 14578844170740740947205

theorem tailTrace_287471 : CollatzResearch.WordTrace tailWord_287471 prefixEnd_287471 14578844170740740947205 := by
  unfold tailWord_287471
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484928741549137983166267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6989952494366091988777511 10484928741549137983166267)
  ·
    refine ⟨15727393112323706974749401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10484928741549137983166267 15727393112323706974749401)
    ·
      refine ⟨11795544834242780231062051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15727393112323706974749401 11795544834242780231062051)
      ·
        refine ⟨17693317251364170346593077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11795544834242780231062051 17693317251364170346593077)
        ·
          refine ⟨1658748492315390969993101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17693317251364170346593077 1658748492315390969993101)
          ·
            refine ⟨622030684618271613747413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1658748492315390969993101 622030684618271613747413)
            ·
              refine ⟨14578844170740740947205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 622030684618271613747413 14578844170740740947205)
              ·
                rfl

theorem cell20_287471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_287471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287471 prefixEnd_287471 := by exact prefixLift 287471
  have htrace : WordTrace (prefixWord ++ tailWord_287471) baseStart_287471 baseEnd_287471 := by
    simpa [prefixWord, tailWord_287471, baseEnd_287471] using wordTrace_append hprefix tailTrace_287471
  have hstable : (prefixWord ++ tailWord_287471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287471).length < 2 ^ (prefixWord ++ tailWord_287471).sum := by decide
  have hdescent : baseEnd_287471 < baseStart_287471 := by decide
  rcases family_descends (prefixWord ++ tailWord_287471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287474 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_287474 : Nat := 118140960795 + 287474 * 2 ^ 59
def prefixEnd_287474 : Nat := 4983230072969 + 3 ^ 40 * 287474 * 2
def baseEnd_287474 : Nat := 131210966818411991424833

theorem tailTrace_287474 : CollatzResearch.WordTrace tailWord_287474 prefixEnd_287474 131210966818411991424833 := by
  unfold tailWord_287474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621259540134567373881369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6990025440358846330350317 2621259540134567373881369)
  ·
    refine ⟨1965944655100925530411027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2621259540134567373881369 1965944655100925530411027)
    ·
      refine ⟨2948916982651388295616541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965944655100925530411027 2948916982651388295616541)
      ·
        refine ⟨1105843868494270610856203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2948916982651388295616541 1105843868494270610856203)
        ·
          refine ⟨1658765802741405916284305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105843868494270610856203 1658765802741405916284305)
          ·
            refine ⟨1244074352056054437213229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1658765802741405916284305 1244074352056054437213229)
            ·
              refine ⟨466527882021020413954961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1244074352056054437213229 466527882021020413954961)
              ·
                refine ⟨349895911515765310466221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466527882021020413954961 349895911515765310466221)
                ·
                  refine ⟨131210966818411991424833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349895911515765310466221 131210966818411991424833)
                  ·
                    rfl

theorem cell20_287474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_287474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287474 prefixEnd_287474 := by exact prefixLift 287474
  have htrace : WordTrace (prefixWord ++ tailWord_287474) baseStart_287474 baseEnd_287474 := by
    simpa [prefixWord, tailWord_287474, baseEnd_287474] using wordTrace_append hprefix tailTrace_287474
  have hstable : (prefixWord ++ tailWord_287474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287474).length < 2 ^ (prefixWord ++ tailWord_287474).sum := by decide
  have hdescent : baseEnd_287474 < baseStart_287474 := by decide
  rcases family_descends (prefixWord ++ tailWord_287474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287509 : List Nat := [1, 3, 2, 1, 2, 2, 3, 6]
def baseStart_287509 : Nat := 118140960795 + 287509 * 2 ^ 59
def prefixEnd_287509 : Nat := 4983230072969 + 3 ^ 40 * 287509 * 2
def baseEnd_287509 : Nat := 43742313924035808419341

theorem tailTrace_287509 : CollatzResearch.WordTrace tailWord_287509 prefixEnd_287509 43742313924035808419341 := by
  unfold tailWord_287509
  simp only [CollatzResearch.WordTrace]
  refine ⟨10486314715411470473049581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6990876476940980315366387 10486314715411470473049581)
  ·
    refine ⟨3932368018279301427393593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10486314715411470473049581 3932368018279301427393593)
    ·
      refine ⟨2949276013709476070545195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3932368018279301427393593 2949276013709476070545195)
      ·
        refine ⟨4423914020564214105817793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2949276013709476070545195 4423914020564214105817793)
        ·
          refine ⟨3317935515423160579363345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4423914020564214105817793 3317935515423160579363345)
          ·
            refine ⟨2488451636567370434522509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3317935515423160579363345 2488451636567370434522509)
            ·
              refine ⟨933169363712763912945941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2488451636567370434522509 933169363712763912945941)
              ·
                refine ⟨43742313924035808419341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 933169363712763912945941 43742313924035808419341)
                ·
                  rfl

theorem cell20_287509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_287509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287509 prefixEnd_287509 := by exact prefixLift 287509
  have htrace : WordTrace (prefixWord ++ tailWord_287509) baseStart_287509 baseEnd_287509 := by
    simpa [prefixWord, tailWord_287509, baseEnd_287509] using wordTrace_append hprefix tailTrace_287509
  have hstable : (prefixWord ++ tailWord_287509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287509).length < 2 ^ (prefixWord ++ tailWord_287509).sum := by decide
  have hdescent : baseEnd_287509 < baseStart_287509 := by decide
  rcases family_descends (prefixWord ++ tailWord_287509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287546 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_287546 : Nat := 118140960795 + 287546 * 2 ^ 59
def prefixEnd_287546 : Nat := 4983230072969 + 3 ^ 40 * 287546 * 2
def baseEnd_287546 : Nat := 131243829580299741024539

theorem tailTrace_287546 : CollatzResearch.WordTrace tailWord_287546 prefixEnd_287546 131243829580299741024539 := by
  unfold tailWord_287546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621916054069356448036623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6991776144184950528097661 2621916054069356448036623)
  ·
    refine ⟨3932874081104034672054935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2621916054069356448036623 3932874081104034672054935)
    ·
      refine ⟨5899311121656052008082403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3932874081104034672054935 5899311121656052008082403)
      ·
        refine ⟨8848966682484078012123605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5899311121656052008082403 8848966682484078012123605)
        ·
          refine ⟨207397656620720578409147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8848966682484078012123605 207397656620720578409147)
          ·
            refine ⟨311096484931080867613721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207397656620720578409147 311096484931080867613721)
            ·
              refine ⟨233322363698310650710291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311096484931080867613721 233322363698310650710291)
              ·
                refine ⟨349983545547465976065437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233322363698310650710291 349983545547465976065437)
                ·
                  refine ⟨131243829580299741024539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349983545547465976065437 131243829580299741024539)
                  ·
                    rfl

theorem cell20_287546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_287546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287546 prefixEnd_287546 := by exact prefixLift 287546
  have htrace : WordTrace (prefixWord ++ tailWord_287546) baseStart_287546 baseEnd_287546 := by
    simpa [prefixWord, tailWord_287546, baseEnd_287546] using wordTrace_append hprefix tailTrace_287546
  have hstable : (prefixWord ++ tailWord_287546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287546).length < 2 ^ (prefixWord ++ tailWord_287546).sum := by decide
  have hdescent : baseEnd_287546 < baseStart_287546 := by decide
  rcases family_descends (prefixWord ++ tailWord_287546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287588 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_287588 : Nat := 118140960795 + 287588 * 2 ^ 59
def prefixEnd_287588 : Nat := 4983230072969 + 3 ^ 40 * 287588 * 2
def baseEnd_287588 : Nat := 131262999524734261624367

theorem tailTrace_287588 : CollatzResearch.WordTrace tailWord_287588 prefixEnd_287588 131262999524734261624367 := by
  unfold tailWord_287588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244598041062633482587709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6992797388083511310116945 5244598041062633482587709)
  ·
    refine ⟨1966724265398487555970391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5244598041062633482587709 1966724265398487555970391)
    ·
      refine ⟨2950086398097731333955587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1966724265398487555970391 2950086398097731333955587)
      ·
        refine ⟨4425129597146597000933381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2950086398097731333955587 4425129597146597000933381)
        ·
          refine ⟨829711799464986937675009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4425129597146597000933381 829711799464986937675009)
          ·
            refine ⟨622283849598740203256257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829711799464986937675009 622283849598740203256257)
            ·
              refine ⟨466712887199055152442193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622283849598740203256257 466712887199055152442193)
              ·
                refine ⟨350034665399291364331645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466712887199055152442193 350034665399291364331645)
                ·
                  refine ⟨131262999524734261624367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350034665399291364331645 131262999524734261624367)
                  ·
                    rfl

theorem cell20_287588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_287588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287588 prefixEnd_287588 := by exact prefixLift 287588
  have htrace : WordTrace (prefixWord ++ tailWord_287588) baseStart_287588 baseEnd_287588 := by
    simpa [prefixWord, tailWord_287588, baseEnd_287588] using wordTrace_append hprefix tailTrace_287588
  have hstable : (prefixWord ++ tailWord_287588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287588).length < 2 ^ (prefixWord ++ tailWord_287588).sum := by decide
  have hdescent : baseEnd_287588 < baseStart_287588 := by decide
  rcases family_descends (prefixWord ++ tailWord_287588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287591 : List Nat := [1, 1, 5, 1, 2, 4, 2, 2, 2]
def baseStart_287591 : Nat := 118140960795 + 287591 * 2 ^ 59
def prefixEnd_287591 : Nat := 4983230072969 + 3 ^ 40 * 287591 * 2
def baseEnd_287591 : Nat := 131264368806479584524355

theorem tailTrace_287591 : CollatzResearch.WordTrace tailWord_287591 prefixEnd_287591 131264368806479584524355 := by
  unfold tailWord_287591
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489305501114398477534627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6992870334076265651689751 10489305501114398477534627)
  ·
    refine ⟨15733958251671597716301941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10489305501114398477534627 15733958251671597716301941)
    ·
      refine ⟨1475058586094212285903307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15733958251671597716301941 1475058586094212285903307)
      ·
        refine ⟨2212587879141318428854961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475058586094212285903307 2212587879141318428854961)
        ·
          refine ⟨1659440909355988821641221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2212587879141318428854961 1659440909355988821641221)
          ·
            refine ⟨311145170504247904057729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1659440909355988821641221 311145170504247904057729)
            ·
              refine ⟨233358877878185928043297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311145170504247904057729 233358877878185928043297)
              ·
                refine ⟨175019158408639446032473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233358877878185928043297 175019158408639446032473)
                ·
                  refine ⟨131264368806479584524355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175019158408639446032473 131264368806479584524355)
                  ·
                    rfl

theorem cell20_287591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 2].length) (baseStart_287591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287591 prefixEnd_287591 := by exact prefixLift 287591
  have htrace : WordTrace (prefixWord ++ tailWord_287591) baseStart_287591 baseEnd_287591 := by
    simpa [prefixWord, tailWord_287591, baseEnd_287591] using wordTrace_append hprefix tailTrace_287591
  have hstable : (prefixWord ++ tailWord_287591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287591).length < 2 ^ (prefixWord ++ tailWord_287591).sum := by decide
  have hdescent : baseEnd_287591 < baseStart_287591 := by decide
  rcases family_descends (prefixWord ++ tailWord_287591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287598 : List Nat := [4, 1, 2, 3, 3, 1, 1, 5]
def baseStart_287598 : Nat := 118140960795 + 287598 * 2 ^ 59
def prefixEnd_287598 : Nat := 4983230072969 + 3 ^ 40 * 287598 * 2
def baseEnd_287598 : Nat := 43755854599072890430331

theorem tailTrace_287598 : CollatzResearch.WordTrace tailWord_287598 prefixEnd_287598 43755854599072890430331 := by
  unfold tailWord_287598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311195101511129834129931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6993040541392692448692965 1311195101511129834129931)
  ·
    refine ⟨1966792652266694751194897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1311195101511129834129931 1966792652266694751194897)
    ·
      refine ⟨1475094489200021063396173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1966792652266694751194897 1475094489200021063396173)
      ·
        refine ⟨553160433450007898773565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1475094489200021063396173 553160433450007898773565)
        ·
          refine ⟨207435162543752962040087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 553160433450007898773565 207435162543752962040087)
          ·
            refine ⟨311152743815629443060131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207435162543752962040087 311152743815629443060131)
            ·
              refine ⟨466729115723444164590197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311152743815629443060131 466729115723444164590197)
              ·
                refine ⟨43755854599072890430331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466729115723444164590197 43755854599072890430331)
                ·
                  rfl

theorem cell20_287598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_287598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287598 prefixEnd_287598 := by exact prefixLift 287598
  have htrace : WordTrace (prefixWord ++ tailWord_287598) baseStart_287598 baseEnd_287598 := by
    simpa [prefixWord, tailWord_287598, baseEnd_287598] using wordTrace_append hprefix tailTrace_287598
  have hstable : (prefixWord ++ tailWord_287598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287598).length < 2 ^ (prefixWord ++ tailWord_287598).sum := by decide
  have hdescent : baseEnd_287598 < baseStart_287598 := by decide
  rcases family_descends (prefixWord ++ tailWord_287598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287599 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_287599 : Nat := 118140960795 + 287599 * 2 ^ 59
def prefixEnd_287599 : Nat := 4983230072969 + 3 ^ 40 * 287599 * 2
def baseEnd_287599 : Nat := 131268020224467112257655

theorem tailTrace_287599 : CollatzResearch.WordTrace tailWord_287599 prefixEnd_287599 131268020224467112257655 := by
  unfold tailWord_287599
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489597285085415843825851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6993064856723610562550567 10489597285085415843825851)
  ·
    refine ⟨15734395927628123765738777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10489597285085415843825851 15734395927628123765738777)
    ·
      refine ⟨11800796945721092824304083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15734395927628123765738777 11800796945721092824304083)
      ·
        refine ⟨17701195418581639236456125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11800796945721092824304083 17701195418581639236456125)
        ·
          refine ⟨6637948281968114713671047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17701195418581639236456125 6637948281968114713671047)
          ·
            refine ⟨9956922422952172070506571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6637948281968114713671047 9956922422952172070506571)
            ·
              refine ⟨14935383634428258105759857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9956922422952172070506571 14935383634428258105759857)
              ·
                refine ⟨11201537725821193579319893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14935383634428258105759857 11201537725821193579319893)
                ·
                  refine ⟨131268020224467112257655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11201537725821193579319893 131268020224467112257655)
                  ·
                    rfl

theorem cell20_287599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_287599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287599 prefixEnd_287599 := by exact prefixLift 287599
  have htrace : WordTrace (prefixWord ++ tailWord_287599) baseStart_287599 baseEnd_287599 := by
    simpa [prefixWord, tailWord_287599, baseEnd_287599] using wordTrace_append hprefix tailTrace_287599
  have hstable : (prefixWord ++ tailWord_287599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287599).length < 2 ^ (prefixWord ++ tailWord_287599).sum := by decide
  have hdescent : baseEnd_287599 < baseStart_287599 := by decide
  rcases family_descends (prefixWord ++ tailWord_287599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287609 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 3]
def baseStart_287609 : Nat := 118140960795 + 287609 * 2 ^ 59
def prefixEnd_287609 : Nat := 4983230072969 + 3 ^ 40 * 287609 * 2
def baseEnd_287609 : Nat := 131272584496951521924281

theorem tailTrace_287609 : CollatzResearch.WordTrace tailWord_287609 prefixEnd_287609 131272584496951521924281 := by
  unfold tailWord_287609
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489962015049187551689881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6993308010032791701126587 10489962015049187551689881)
  ·
    refine ⟨7867471511286890663767411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10489962015049187551689881 7867471511286890663767411)
    ·
      refine ⟨11801207266930335995651117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7867471511286890663767411 11801207266930335995651117)
      ·
        refine ⟨4425452725098875998369169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11801207266930335995651117 4425452725098875998369169)
        ·
          refine ⟨3319089543824156998776877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4425452725098875998369169 3319089543824156998776877)
          ·
            refine ⟨1244658578934058874541329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3319089543824156998776877 1244658578934058874541329)
            ·
              refine ⟨933493934200544155905997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244658578934058874541329 933493934200544155905997)
              ·
                refine ⟨350060225325204058464749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933493934200544155905997 350060225325204058464749)
                ·
                  refine ⟨131272584496951521924281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350060225325204058464749 131272584496951521924281)
                  ·
                    rfl

theorem cell20_287609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_287609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287609 prefixEnd_287609 := by exact prefixLift 287609
  have htrace : WordTrace (prefixWord ++ tailWord_287609) baseStart_287609 baseEnd_287609 := by
    simpa [prefixWord, tailWord_287609, baseEnd_287609] using wordTrace_append hprefix tailTrace_287609
  have hstable : (prefixWord ++ tailWord_287609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287609).length < 2 ^ (prefixWord ++ tailWord_287609).sum := by decide
  have hdescent : baseEnd_287609 < baseStart_287609 := by decide
  rcases family_descends (prefixWord ++ tailWord_287609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287647 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_287647 : Nat := 118140960795 + 287647 * 2 ^ 59
def prefixEnd_287647 : Nat := 4983230072969 + 3 ^ 40 * 287647 * 2
def baseEnd_287647 : Nat := 131289928732392278657459

theorem tailTrace_287647 : CollatzResearch.WordTrace tailWord_287647 prefixEnd_287647 131289928732392278657459 := by
  unfold tailWord_287647
  simp only [CollatzResearch.WordTrace]
  refine ⟨10491347988911520041573195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6994231992607680027715463 10491347988911520041573195)
  ·
    refine ⟨15737021983367280062359793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10491347988911520041573195 15737021983367280062359793)
    ·
      refine ⟨11802766487525460046769845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15737021983367280062359793 11802766487525460046769845)
      ·
        refine ⟨1106509358205511879384673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11802766487525460046769845 1106509358205511879384673)
        ·
          refine ⟨829882018654133909538505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1106509358205511879384673 829882018654133909538505)
          ·
            refine ⟨622411513990600432153879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829882018654133909538505 622411513990600432153879)
            ·
              refine ⟨933617270985900648230819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622411513990600432153879 933617270985900648230819)
              ·
                refine ⟨1400425906478850972346229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933617270985900648230819 1400425906478850972346229)
                ·
                  refine ⟨131289928732392278657459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1400425906478850972346229 131289928732392278657459)
                  ·
                    rfl

theorem cell20_287647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_287647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287647 prefixEnd_287647 := by exact prefixLift 287647
  have htrace : WordTrace (prefixWord ++ tailWord_287647) baseStart_287647 baseEnd_287647 := by
    simpa [prefixWord, tailWord_287647, baseEnd_287647] using wordTrace_append hprefix tailTrace_287647
  have hstable : (prefixWord ++ tailWord_287647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287647).length < 2 ^ (prefixWord ++ tailWord_287647).sum := by decide
  have hdescent : baseEnd_287647 < baseStart_287647 := by decide
  rcases family_descends (prefixWord ++ tailWord_287647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287650 : List Nat := [3, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_287650 : Nat := 118140960795 + 287650 * 2 ^ 59
def prefixEnd_287650 : Nat := 4983230072969 + 3 ^ 40 * 287650 * 2
def baseEnd_287650 : Nat := 131291298014137601557447

theorem tailTrace_287650 : CollatzResearch.WordTrace tailWord_287650 prefixEnd_287650 131291298014137601557447 := by
  unfold tailWord_287650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622864351975162888483101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6994304938600434369288269 2622864351975162888483101)
  ·
    refine ⟨983574131990686083181163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2622864351975162888483101 983574131990686083181163)
    ·
      refine ⟨1475361197986029124771745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983574131990686083181163 1475361197986029124771745)
      ·
        refine ⟨1106520898489521843578809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1475361197986029124771745 1106520898489521843578809)
        ·
          refine ⟨829890673867141382684107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1106520898489521843578809 829890673867141382684107)
          ·
            refine ⟨1244836010800712074026161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829890673867141382684107 1244836010800712074026161)
            ·
              refine ⟨933627008100534055519621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244836010800712074026161 933627008100534055519621)
              ·
                refine ⟨175055064018850135409929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 933627008100534055519621 175055064018850135409929)
                ·
                  refine ⟨131291298014137601557447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175055064018850135409929 131291298014137601557447)
                  ·
                    rfl

theorem cell20_287650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_287650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287650 prefixEnd_287650 := by exact prefixLift 287650
  have htrace : WordTrace (prefixWord ++ tailWord_287650) baseStart_287650 baseEnd_287650 := by
    simpa [prefixWord, tailWord_287650, baseEnd_287650] using wordTrace_append hprefix tailTrace_287650
  have hstable : (prefixWord ++ tailWord_287650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287650).length < 2 ^ (prefixWord ++ tailWord_287650).sum := by decide
  have hdescent : baseEnd_287650 < baseStart_287650 := by decide
  rcases family_descends (prefixWord ++ tailWord_287650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287670 : List Nat := [5, 1, 4, 1, 1, 2, 2, 4]
def baseStart_287670 : Nat := 118140960795 + 287670 * 2 ^ 59
def prefixEnd_287670 : Nat := 4983230072969 + 3 ^ 40 * 287670 * 2
def baseEnd_287670 : Nat := 43766808853035473630233

theorem tailTrace_287670 : CollatzResearch.WordTrace tailWord_287670 prefixEnd_287670 43766808853035473630233 := by
  unfold tailWord_287670
  simp only [CollatzResearch.WordTrace]
  refine ⟨655761679239262185603779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6994791245218796646440309 655761679239262185603779)
  ·
    refine ⟨983642518858893278405669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655761679239262185603779 983642518858893278405669)
    ·
      refine ⟨184432972286042489701063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 983642518858893278405669 184432972286042489701063)
      ·
        refine ⟨276649458429063734551595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184432972286042489701063 276649458429063734551595)
        ·
          refine ⟨414974187643595601827393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276649458429063734551595 414974187643595601827393)
          ·
            refine ⟨311230640732696701370545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414974187643595601827393 311230640732696701370545)
            ·
              refine ⟨233422980549522526027909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311230640732696701370545 233422980549522526027909)
              ·
                refine ⟨43766808853035473630233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233422980549522526027909 43766808853035473630233)
                ·
                  rfl

theorem cell20_287670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_287670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287670 prefixEnd_287670 := by exact prefixLift 287670
  have htrace : WordTrace (prefixWord ++ tailWord_287670) baseStart_287670 baseEnd_287670 := by
    simpa [prefixWord, tailWord_287670, baseEnd_287670] using wordTrace_append hprefix tailTrace_287670
  have hstable : (prefixWord ++ tailWord_287670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287670).length < 2 ^ (prefixWord ++ tailWord_287670).sum := by decide
  have hdescent : baseEnd_287670 < baseStart_287670 := by decide
  rcases family_descends (prefixWord ++ tailWord_287670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287684 : List Nat := [2, 3, 3, 3, 1, 2, 1, 3, 2]
def baseStart_287684 : Nat := 118140960795 + 287684 * 2 ^ 59
def prefixEnd_287684 : Nat := 4983230072969 + 3 ^ 40 * 287684 * 2
def baseEnd_287684 : Nat := 131306816540584594423975

theorem tailTrace_287684 : CollatzResearch.WordTrace tailWord_287684 prefixEnd_287684 131306816540584594423975 := by
  unfold tailWord_287684
  simp only [CollatzResearch.WordTrace]
  refine ⟨5246348744888737680335053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6995131659851650240446737 5246348744888737680335053)
  ·
    refine ⟨1967380779333276630125645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5246348744888737680335053 1967380779333276630125645)
    ·
      refine ⟨737767792249978736297117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1967380779333276630125645 737767792249978736297117)
      ·
        refine ⟨276662922093742026111419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 737767792249978736297117 276662922093742026111419)
        ·
          refine ⟨414994383140613039167129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276662922093742026111419 414994383140613039167129)
          ·
            refine ⟨311245787355459779375347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414994383140613039167129 311245787355459779375347)
            ·
              refine ⟨466868681033189669063021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311245787355459779375347 466868681033189669063021)
              ·
                refine ⟨175075755387446125898633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466868681033189669063021 175075755387446125898633)
                ·
                  refine ⟨131306816540584594423975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175075755387446125898633 131306816540584594423975)
                  ·
                    rfl

theorem cell20_287684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_287684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287684 prefixEnd_287684 := by exact prefixLift 287684
  have htrace : WordTrace (prefixWord ++ tailWord_287684) baseStart_287684 baseEnd_287684 := by
    simpa [prefixWord, tailWord_287684, baseEnd_287684] using wordTrace_append hprefix tailTrace_287684
  have hstable : (prefixWord ++ tailWord_287684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287684).length < 2 ^ (prefixWord ++ tailWord_287684).sum := by decide
  have hdescent : baseEnd_287684 < baseStart_287684 := by decide
  rcases family_descends (prefixWord ++ tailWord_287684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287702 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_287702 : Nat := 118140960795 + 287702 * 2 ^ 59
def prefixEnd_287702 : Nat := 4983230072969 + 3 ^ 40 * 287702 * 2
def baseEnd_287702 : Nat := 131315032231056531823901

theorem tailTrace_287702 : CollatzResearch.WordTrace tailWord_287702 prefixEnd_287702 131315032231056531823901 := by
  unfold tailWord_287702
  simp only [CollatzResearch.WordTrace]
  refine ⟨655834625232016527176585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6995569335808176289883573 655834625232016527176585)
  ·
    refine ⟨491875968924012395382439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 655834625232016527176585 491875968924012395382439)
    ·
      refine ⟨737813953386018593073659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491875968924012395382439 737813953386018593073659)
      ·
        refine ⟨1106720930079027889610489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737813953386018593073659 1106720930079027889610489)
        ·
          refine ⟨830040697559270917207867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1106720930079027889610489 830040697559270917207867)
          ·
            refine ⟨1245061046338906375811801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830040697559270917207867 1245061046338906375811801)
            ·
              refine ⟨933795784754179781858851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245061046338906375811801 933795784754179781858851)
              ·
                refine ⟨1400693677131269672788277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933795784754179781858851 1400693677131269672788277)
                ·
                  refine ⟨131315032231056531823901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1400693677131269672788277 131315032231056531823901)
                  ·
                    rfl

theorem cell20_287702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_287702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287702 prefixEnd_287702 := by exact prefixLift 287702
  have htrace : WordTrace (prefixWord ++ tailWord_287702) baseStart_287702 baseEnd_287702 := by
    simpa [prefixWord, tailWord_287702, baseEnd_287702] using wordTrace_append hprefix tailTrace_287702
  have hstable : (prefixWord ++ tailWord_287702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287702).length < 2 ^ (prefixWord ++ tailWord_287702).sum := by decide
  have hdescent : baseEnd_287702 < baseStart_287702 := by decide
  rcases family_descends (prefixWord ++ tailWord_287702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287709 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_287709 : Nat := 118140960795 + 287709 * 2 ^ 59
def prefixEnd_287709 : Nat := 4983230072969 + 3 ^ 40 * 287709 * 2
def baseEnd_287709 : Nat := 131318227221795618590539

theorem tailTrace_287709 : CollatzResearch.WordTrace tailWord_287709 prefixEnd_287709 131318227221795618590539 := by
  unfold tailWord_287709
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493609314686904630330181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6995739543124603086886787 10493609314686904630330181)
  ·
    refine ⟨1967551746503794618186909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10493609314686904630330181 1967551746503794618186909)
    ·
      refine ⟨737831904938922981820091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1967551746503794618186909 737831904938922981820091)
      ·
        refine ⟨1106747857408384472730137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737831904938922981820091 1106747857408384472730137)
        ·
          refine ⟨830060893056288354547603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1106747857408384472730137 830060893056288354547603)
          ·
            refine ⟨1245091339584432531821405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830060893056288354547603 1245091339584432531821405)
            ·
              refine ⟨466909252344162199433027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1245091339584432531821405 466909252344162199433027)
              ·
                refine ⟨700363878516243299149541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466909252344162199433027 700363878516243299149541)
                ·
                  refine ⟨131318227221795618590539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700363878516243299149541 131318227221795618590539)
                  ·
                    rfl

theorem cell20_287709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_287709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287709 prefixEnd_287709 := by exact prefixLift 287709
  have htrace : WordTrace (prefixWord ++ tailWord_287709) baseStart_287709 baseEnd_287709 := by
    simpa [prefixWord, tailWord_287709, baseEnd_287709] using wordTrace_append hprefix tailTrace_287709
  have hstable : (prefixWord ++ tailWord_287709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287709).length < 2 ^ (prefixWord ++ tailWord_287709).sum := by decide
  have hdescent : baseEnd_287709 < baseStart_287709 := by decide
  rcases family_descends (prefixWord ++ tailWord_287709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287719 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 3]
def baseStart_287719 : Nat := 118140960795 + 287719 * 2 ^ 59
def prefixEnd_287719 : Nat := 4983230072969 + 3 ^ 40 * 287719 * 2
def baseEnd_287719 : Nat := 131322791494280028257165

theorem tailTrace_287719 : CollatzResearch.WordTrace tailWord_287719 prefixEnd_287719 131322791494280028257165 := by
  unfold tailWord_287719
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493974044650676338194211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6995982696433784225462807 10493974044650676338194211)
  ·
    refine ⟨15740961066976014507291317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10493974044650676338194211 15740961066976014507291317)
    ·
      refine ⟨1475715100029001360058561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15740961066976014507291317 1475715100029001360058561)
      ·
        refine ⟨1106786325021751020043921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1475715100029001360058561 1106786325021751020043921)
        ·
          refine ⟨830089743766313265032941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1106786325021751020043921 830089743766313265032941)
          ·
            refine ⟨311283653912367474387353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 830089743766313265032941 311283653912367474387353)
            ·
              refine ⟨233462740434275605790515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311283653912367474387353 233462740434275605790515)
              ·
                refine ⟨350194110651413408685773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233462740434275605790515 350194110651413408685773)
                ·
                  refine ⟨131322791494280028257165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350194110651413408685773 131322791494280028257165)
                  ·
                    rfl

theorem cell20_287719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 3].length) (baseStart_287719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287719 prefixEnd_287719 := by exact prefixLift 287719
  have htrace : WordTrace (prefixWord ++ tailWord_287719) baseStart_287719 baseEnd_287719 := by
    simpa [prefixWord, tailWord_287719, baseEnd_287719] using wordTrace_append hprefix tailTrace_287719
  have hstable : (prefixWord ++ tailWord_287719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287719).length < 2 ^ (prefixWord ++ tailWord_287719).sum := by decide
  have hdescent : baseEnd_287719 < baseStart_287719 := by decide
  rcases family_descends (prefixWord ++ tailWord_287719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287775 : List Nat := [1, 1, 2, 4, 1, 3, 3, 5]
def baseStart_287775 : Nat := 118140960795 + 287775 * 2 ^ 59
def prefixEnd_287775 : Nat := 4983230072969 + 3 ^ 40 * 287775 * 2
def baseEnd_287775 : Nat := 43782783806730907463423

theorem tailTrace_287775 : CollatzResearch.WordTrace tailWord_287775 prefixEnd_287775 43782783806730907463423 := by
  unfold tailWord_287775
  simp only [CollatzResearch.WordTrace]
  refine ⟨10496016532447797902232779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6997344354965198601488519 10496016532447797902232779)
  ·
    refine ⟨15744024798671696853349169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10496016532447797902232779 15744024798671696853349169)
    ·
      refine ⟨11808018599003772640011877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15744024798671696853349169 11808018599003772640011877)
      ·
        refine ⟨2214003487313207370002227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11808018599003772640011877 2214003487313207370002227)
        ·
          refine ⟨3321005230969811055003341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214003487313207370002227 3321005230969811055003341)
          ·
            refine ⟨1245376961613679145626253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3321005230969811055003341 1245376961613679145626253)
            ·
              refine ⟨467016360605129679609845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1245376961613679145626253 467016360605129679609845)
              ·
                refine ⟨43782783806730907463423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 467016360605129679609845 43782783806730907463423)
                ·
                  rfl

theorem cell20_287775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_287775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287775 prefixEnd_287775 := by exact prefixLift 287775
  have htrace : WordTrace (prefixWord ++ tailWord_287775) baseStart_287775 baseEnd_287775 := by
    simpa [prefixWord, tailWord_287775, baseEnd_287775] using wordTrace_append hprefix tailTrace_287775
  have hstable : (prefixWord ++ tailWord_287775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287775).length < 2 ^ (prefixWord ++ tailWord_287775).sum := by decide
  have hdescent : baseEnd_287775 < baseStart_287775 := by decide
  rcases family_descends (prefixWord ++ tailWord_287775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287827 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_287827 : Nat := 118140960795 + 287827 * 2 ^ 59
def prefixEnd_287827 : Nat := 4983230072969 + 3 ^ 40 * 287827 * 2
def baseEnd_287827 : Nat := 131372085637111652656723

theorem tailTrace_287827 : CollatzResearch.WordTrace tailWord_287827 prefixEnd_287827 131372085637111652656723 := by
  unfold tailWord_287827
  simp only [CollatzResearch.WordTrace]
  refine ⟨10497913128259410783125735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6998608752172940522083823 10497913128259410783125735)
  ·
    refine ⟨15746869692389116174688603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10497913128259410783125735 15746869692389116174688603)
    ·
      refine ⟨23620304538583674262032905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15746869692389116174688603 23620304538583674262032905)
      ·
        refine ⟨17715228403937755696524679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23620304538583674262032905 17715228403937755696524679)
        ·
          refine ⟨26572842605906633544787019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17715228403937755696524679 26572842605906633544787019)
          ·
            refine ⟨39859263908859950317180529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26572842605906633544787019 39859263908859950317180529)
            ·
              refine ⟨29894447931644962737885397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39859263908859950317180529 29894447931644962737885397)
              ·
                refine ⟨700651123397928814169189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29894447931644962737885397 700651123397928814169189)
                ·
                  refine ⟨131372085637111652656723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700651123397928814169189 131372085637111652656723)
                  ·
                    rfl

theorem cell20_287827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_287827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287827 prefixEnd_287827 := by exact prefixLift 287827
  have htrace : WordTrace (prefixWord ++ tailWord_287827) baseStart_287827 baseEnd_287827 := by
    simpa [prefixWord, tailWord_287827, baseEnd_287827] using wordTrace_append hprefix tailTrace_287827
  have hstable : (prefixWord ++ tailWord_287827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287827).length < 2 ^ (prefixWord ++ tailWord_287827).sum := by decide
  have hdescent : baseEnd_287827 < baseStart_287827 := by decide
  rcases family_descends (prefixWord ++ tailWord_287827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287858 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_287858 : Nat := 118140960795 + 287858 * 2 ^ 59
def prefixEnd_287858 : Nat := 4983230072969 + 3 ^ 40 * 287858 * 2
def baseEnd_287858 : Nat := 131386234881813322623263

theorem tailTrace_287858 : CollatzResearch.WordTrace tailWord_287858 prefixEnd_287858 131386234881813322623263 := by
  unfold tailWord_287858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624760947786775769376057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6999362527431402051669485 2624760947786775769376057)
  ·
    refine ⟨1968570710840081827032043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2624760947786775769376057 1968570710840081827032043)
    ·
      refine ⟨2952856066260122740548065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1968570710840081827032043 2952856066260122740548065)
      ·
        refine ⟨2214642049695092055411049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2952856066260122740548065 2214642049695092055411049)
        ·
          refine ⟨1660981537271319041558287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2214642049695092055411049 1660981537271319041558287)
          ·
            refine ⟨2491472305906978562337431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660981537271319041558287 2491472305906978562337431)
            ·
              refine ⟨3737208458860467843506147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491472305906978562337431 3737208458860467843506147)
              ·
                refine ⟨5605812688290701765259221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737208458860467843506147 5605812688290701765259221)
                ·
                  refine ⟨131386234881813322623263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5605812688290701765259221 131386234881813322623263)
                  ·
                    rfl

theorem cell20_287858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_287858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287858 prefixEnd_287858 := by exact prefixLift 287858
  have htrace : WordTrace (prefixWord ++ tailWord_287858) baseStart_287858 baseEnd_287858 := by
    simpa [prefixWord, tailWord_287858, baseEnd_287858] using wordTrace_append hprefix tailTrace_287858
  have hstable : (prefixWord ++ tailWord_287858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287858).length < 2 ^ (prefixWord ++ tailWord_287858).sum := by decide
  have hdescent : baseEnd_287858 < baseStart_287858 := by decide
  rcases family_descends (prefixWord ++ tailWord_287858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287872 : List Nat := [2, 1, 1, 2, 1, 3, 10]
def baseStart_287872 : Nat := 118140960795 + 287872 * 2 ^ 59
def prefixEnd_287872 : Nat := 4983230072969 + 3 ^ 40 * 287872 * 2
def baseEnd_287872 : Nat := 14599180540365721795171

theorem tailTrace_287872 : CollatzResearch.WordTrace tailWord_287872 prefixEnd_287872 14599180540365721795171 := by
  unfold tailWord_287872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5249777206548191734256935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6999702942064255645675913 5249777206548191734256935)
  ·
    refine ⟨7874665809822287601385403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5249777206548191734256935 7874665809822287601385403)
    ·
      refine ⟨11811998714733431402078105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7874665809822287601385403 11811998714733431402078105)
      ·
        refine ⟨8858999036050073551558579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11811998714733431402078105 8858999036050073551558579)
        ·
          refine ⟨13288498554075110327337869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8858999036050073551558579 13288498554075110327337869)
          ·
            refine ⟨4983186957778166372751701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13288498554075110327337869 4983186957778166372751701)
            ·
              refine ⟨14599180540365721795171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4983186957778166372751701 14599180540365721795171)
              ·
                rfl

theorem cell20_287872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 10].length) (baseStart_287872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287872 prefixEnd_287872 := by exact prefixLift 287872
  have htrace : WordTrace (prefixWord ++ tailWord_287872) baseStart_287872 baseEnd_287872 := by
    simpa [prefixWord, tailWord_287872, baseEnd_287872] using wordTrace_append hprefix tailTrace_287872
  have hstable : (prefixWord ++ tailWord_287872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287872).length < 2 ^ (prefixWord ++ tailWord_287872).sum := by decide
  have hdescent : baseEnd_287872 < baseStart_287872 := by decide
  rcases family_descends (prefixWord ++ tailWord_287872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287926 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_287926 : Nat := 118140960795 + 287926 * 2 ^ 59
def prefixEnd_287926 : Nat := 4983230072969 + 3 ^ 40 * 287926 * 2
def baseEnd_287926 : Nat := 131417271934707308356319

theorem tailTrace_287926 : CollatzResearch.WordTrace tailWord_287926 prefixEnd_287926 131417271934707308356319 := by
  unfold tailWord_287926
  simp only [CollatzResearch.WordTrace]
  refine ⟨656345247181296918186227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7001015969933833793986421 656345247181296918186227)
  ·
    refine ⟨984517870771945377279341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 656345247181296918186227 984517870771945377279341)
    ·
      refine ⟨369194201539479516479753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 984517870771945377279341 369194201539479516479753)
      ·
        refine ⟨276895651154609637359815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369194201539479516479753 276895651154609637359815)
        ·
          refine ⟨415343476731914456039723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276895651154609637359815 415343476731914456039723)
          ·
            refine ⟨623015215097871684059585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415343476731914456039723 623015215097871684059585)
            ·
              refine ⟨467261411323403763044689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623015215097871684059585 467261411323403763044689)
              ·
                refine ⟨350446058492552822283517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467261411323403763044689 350446058492552822283517)
                ·
                  refine ⟨131417271934707308356319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350446058492552822283517 131417271934707308356319)
                  ·
                    rfl

theorem cell20_287926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_287926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287926 prefixEnd_287926 := by exact prefixLift 287926
  have htrace : WordTrace (prefixWord ++ tailWord_287926) baseStart_287926 baseEnd_287926 := by
    simpa [prefixWord, tailWord_287926, baseEnd_287926] using wordTrace_append hprefix tailTrace_287926
  have hstable : (prefixWord ++ tailWord_287926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287926).length < 2 ^ (prefixWord ++ tailWord_287926).sum := by decide
  have hdescent : baseEnd_287926 < baseStart_287926 := by decide
  rcases family_descends (prefixWord ++ tailWord_287926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_287941 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_287941 : Nat := 118140960795 + 287941 * 2 ^ 59
def prefixEnd_287941 : Nat := 4983230072969 + 3 ^ 40 * 287941 * 2
def baseEnd_287941 : Nat := 131424118343433922856257

theorem tailTrace_287941 : CollatzResearch.WordTrace tailWord_287941 prefixEnd_287941 131424118343433922856257 := by
  unfold tailWord_287941
  simp only [CollatzResearch.WordTrace]
  refine ⟨10502071049846408252775677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7001380699897605501850451 10502071049846408252775677)
  ·
    refine ⟨3938276643692403094790879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10502071049846408252775677 3938276643692403094790879)
    ·
      refine ⟨5907414965538604642186319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3938276643692403094790879 5907414965538604642186319)
      ·
        refine ⟨8861122448307906963279479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5907414965538604642186319 8861122448307906963279479)
        ·
          refine ⟨13291683672461860444919219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8861122448307906963279479 13291683672461860444919219)
          ·
            refine ⟨19937525508692790667378829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13291683672461860444919219 19937525508692790667378829)
            ·
              refine ⟨7476572065759796500267061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19937525508692790667378829 7476572065759796500267061)
              ·
                refine ⟨700928631164980921900037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7476572065759796500267061 700928631164980921900037)
                ·
                  refine ⟨131424118343433922856257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700928631164980921900037 131424118343433922856257)
                  ·
                    rfl

theorem cell20_287941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_287941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_287941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_287941 prefixEnd_287941 := by exact prefixLift 287941
  have htrace : WordTrace (prefixWord ++ tailWord_287941) baseStart_287941 baseEnd_287941 := by
    simpa [prefixWord, tailWord_287941, baseEnd_287941] using wordTrace_append hprefix tailTrace_287941
  have hstable : (prefixWord ++ tailWord_287941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_287941).length < 2 ^ (prefixWord ++ tailWord_287941).sum := by decide
  have hdescent : baseEnd_287941 < baseStart_287941 := by decide
  rcases family_descends (prefixWord ++ tailWord_287941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288017 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_288017 : Nat := 118140960795 + 288017 * 2 ^ 59
def prefixEnd_288017 : Nat := 4983230072969 + 3 ^ 40 * 288017 * 2
def baseEnd_288017 : Nat := 131458806814315436322613

theorem tailTrace_288017 : CollatzResearch.WordTrace tailWord_288017 prefixEnd_288017 131458806814315436322613 := by
  unfold tailWord_288017
  simp only [CollatzResearch.WordTrace]
  refine ⟨10504842997571073232542305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7003228665047382155028203 10504842997571073232542305)
  ·
    refine ⟨7878632248178304924406729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10504842997571073232542305 7878632248178304924406729)
    ·
      refine ⟨5908974186133728693305047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7878632248178304924406729 5908974186133728693305047)
      ·
        refine ⟨8863461279200593039957571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908974186133728693305047 8863461279200593039957571)
        ·
          refine ⟨13295191918800889559936357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8863461279200593039957571 13295191918800889559936357)
          ·
            refine ⟨2492848484775166792488067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13295191918800889559936357 2492848484775166792488067)
            ·
              refine ⟨3739272727162750188732101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492848484775166792488067 3739272727162750188732101)
              ·
                refine ⟨701113636343015660387269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3739272727162750188732101 701113636343015660387269)
                ·
                  refine ⟨131458806814315436322613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701113636343015660387269 131458806814315436322613)
                  ·
                    rfl

theorem cell20_288017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_288017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288017 prefixEnd_288017 := by exact prefixLift 288017
  have htrace : WordTrace (prefixWord ++ tailWord_288017) baseStart_288017 baseEnd_288017 := by
    simpa [prefixWord, tailWord_288017, baseEnd_288017] using wordTrace_append hprefix tailTrace_288017
  have hstable : (prefixWord ++ tailWord_288017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288017).length < 2 ^ (prefixWord ++ tailWord_288017).sum := by decide
  have hdescent : baseEnd_288017 < baseStart_288017 := by decide
  rcases family_descends (prefixWord ++ tailWord_288017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288048 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_288048 : Nat := 118140960795 + 288048 * 2 ^ 59
def prefixEnd_288048 : Nat := 4983230072969 + 3 ^ 40 * 288048 * 2
def baseEnd_288048 : Nat := 131472956059017106289153

theorem tailTrace_288048 : CollatzResearch.WordTrace tailWord_288048 prefixEnd_288048 131472956059017106289153 := by
  unfold tailWord_288048
  simp only [CollatzResearch.WordTrace]
  refine ⟨5252986830229382763460399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7003982440305843684613865 5252986830229382763460399)
  ·
    refine ⟨7879480245344074145190599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5252986830229382763460399 7879480245344074145190599)
    ·
      refine ⟨11819220368016111217785899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7879480245344074145190599 11819220368016111217785899)
      ·
        refine ⟨17728830552024166826678849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11819220368016111217785899 17728830552024166826678849)
        ·
          refine ⟨13296622914018125120009137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17728830552024166826678849 13296622914018125120009137)
          ·
            refine ⟨9972467185513593840006853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13296622914018125120009137 9972467185513593840006853)
            ·
              refine ⟨1869837597283798845001285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9972467185513593840006853 1869837597283798845001285)
              ·
                refine ⟨350594549490712283437741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1869837597283798845001285 350594549490712283437741)
                ·
                  refine ⟨131472956059017106289153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350594549490712283437741 131472956059017106289153)
                  ·
                    rfl

theorem cell20_288048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_288048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288048 prefixEnd_288048 := by exact prefixLift 288048
  have htrace : WordTrace (prefixWord ++ tailWord_288048) baseStart_288048 baseEnd_288048 := by
    simpa [prefixWord, tailWord_288048, baseEnd_288048] using wordTrace_append hprefix tailTrace_288048
  have hstable : (prefixWord ++ tailWord_288048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288048).length < 2 ^ (prefixWord ++ tailWord_288048).sum := by decide
  have hdescent : baseEnd_288048 < baseStart_288048 := by decide
  rcases family_descends (prefixWord ++ tailWord_288048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288100 : List Nat := [2, 3, 1, 1, 3, 10]
def baseStart_288100 : Nat := 118140960795 + 288100 * 2 ^ 59
def prefixEnd_288100 : Nat := 4983230072969 + 3 ^ 40 * 288100 * 2
def baseEnd_288100 : Nat := 4870247787997630983541

theorem tailTrace_288100 : CollatzResearch.WordTrace tailWord_288100 prefixEnd_288100 4870247787997630983541 := by
  unfold tailWord_288100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253935128135189203906877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7005246837513585605209169 5253935128135189203906877)
  ·
    refine ⟨1970225673050695951465079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5253935128135189203906877 1970225673050695951465079)
    ·
      refine ⟨2955338509576043927197619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1970225673050695951465079 2955338509576043927197619)
      ·
        refine ⟨4433007764364065890796429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955338509576043927197619 4433007764364065890796429)
        ·
          refine ⟨1662377911636524709048661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4433007764364065890796429 1662377911636524709048661)
          ·
            refine ⟨4870247787997630983541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1662377911636524709048661 4870247787997630983541)
            ·
              rfl

theorem cell20_288100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 10].length) (baseStart_288100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288100 prefixEnd_288100 := by exact prefixLift 288100
  have htrace : WordTrace (prefixWord ++ tailWord_288100) baseStart_288100 baseEnd_288100 := by
    simpa [prefixWord, tailWord_288100, baseEnd_288100] using wordTrace_append hprefix tailTrace_288100
  have hstable : (prefixWord ++ tailWord_288100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288100).length < 2 ^ (prefixWord ++ tailWord_288100).sum := by decide
  have hdescent : baseEnd_288100 < baseStart_288100 := by decide
  rcases family_descends (prefixWord ++ tailWord_288100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288106 : List Nat := [3, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_288106 : Nat := 118140960795 + 288106 * 2 ^ 59
def prefixEnd_288106 : Nat := 4983230072969 + 3 ^ 40 * 288106 * 2
def baseEnd_288106 : Nat := 131499428839426682355583

theorem tailTrace_288106 : CollatzResearch.WordTrace tailWord_288106 prefixEnd_288106 131499428839426682355583 := by
  unfold tailWord_288106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627022273562160358133043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7005392729499094288354781 2627022273562160358133043)
  ·
    refine ⟨3940533410343240537199565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2627022273562160358133043 3940533410343240537199565)
    ·
      refine ⟨1477700028878715201449837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3940533410343240537199565 1477700028878715201449837)
      ·
        refine ⟨554137510829518200543689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1477700028878715201449837 554137510829518200543689)
        ·
          refine ⟨415603133122138650407767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 554137510829518200543689 415603133122138650407767)
          ·
            refine ⟨623404699683207975611651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415603133122138650407767 623404699683207975611651)
            ·
              refine ⟨935107049524811963417477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623404699683207975611651 935107049524811963417477)
              ·
                refine ⟨175332571785902243140777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 935107049524811963417477 175332571785902243140777)
                ·
                  refine ⟨131499428839426682355583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175332571785902243140777 131499428839426682355583)
                  ·
                    rfl

theorem cell20_288106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_288106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288106 prefixEnd_288106 := by exact prefixLift 288106
  have htrace : WordTrace (prefixWord ++ tailWord_288106) baseStart_288106 baseEnd_288106 := by
    simpa [prefixWord, tailWord_288106, baseEnd_288106] using wordTrace_append hprefix tailTrace_288106
  have hstable : (prefixWord ++ tailWord_288106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288106).length < 2 ^ (prefixWord ++ tailWord_288106).sum := by decide
  have hdescent : baseEnd_288106 < baseStart_288106 := by decide
  rcases family_descends (prefixWord ++ tailWord_288106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288124 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_288124 : Nat := 118140960795 + 288124 * 2 ^ 59
def prefixEnd_288124 : Nat := 4983230072969 + 3 ^ 40 * 288124 * 2
def baseEnd_288124 : Nat := 131507644529898619755509

theorem tailTrace_288124 : CollatzResearch.WordTrace tailWord_288124 prefixEnd_288124 131507644529898619755509 := by
  unfold tailWord_288124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254372804091715253343713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7005830405455620337791617 5254372804091715253343713)
  ·
    refine ⟨3940779603068786440007785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5254372804091715253343713 3940779603068786440007785)
    ·
      refine ⟨2955584702301589830005839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3940779603068786440007785 2955584702301589830005839)
      ·
        refine ⟨4433377053452384745008759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955584702301589830005839 4433377053452384745008759)
        ·
          refine ⟨6650065580178577117513139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4433377053452384745008759 6650065580178577117513139)
          ·
            refine ⟨9975098370267865676269709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6650065580178577117513139 9975098370267865676269709)
            ·
              refine ⟨3740661888850449628601141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9975098370267865676269709 3740661888850449628601141)
              ·
                refine ⟨350687052079729652681357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3740661888850449628601141 350687052079729652681357)
                ·
                  refine ⟨131507644529898619755509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350687052079729652681357 131507644529898619755509)
                  ·
                    rfl

theorem cell20_288124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_288124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288124 prefixEnd_288124 := by exact prefixLift 288124
  have htrace : WordTrace (prefixWord ++ tailWord_288124) baseStart_288124 baseEnd_288124 := by
    simpa [prefixWord, tailWord_288124, baseEnd_288124] using wordTrace_append hprefix tailTrace_288124
  have hstable : (prefixWord ++ tailWord_288124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288124).length < 2 ^ (prefixWord ++ tailWord_288124).sum := by decide
  have hdescent : baseEnd_288124 < baseStart_288124 := by decide
  rcases family_descends (prefixWord ++ tailWord_288124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288131 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_288131 : Nat := 118140960795 + 288131 * 2 ^ 59
def prefixEnd_288131 : Nat := 4983230072969 + 3 ^ 40 * 288131 * 2
def baseEnd_288131 : Nat := 131510839520637706522147

theorem tailTrace_288131 : CollatzResearch.WordTrace tailWord_288131 prefixEnd_288131 131510839520637706522147 := by
  unfold tailWord_288131
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509000919158070702192247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7006000612772047134794831 10509000919158070702192247)
  ·
    refine ⟨15763501378737106053288371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10509000919158070702192247 15763501378737106053288371)
    ·
      refine ⟨23645252068105659079932557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15763501378737106053288371 23645252068105659079932557)
      ·
        refine ⟨8866969525539622154974709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23645252068105659079932557 8866969525539622154974709)
        ·
          refine ⟨831278393019339577028879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8866969525539622154974709 831278393019339577028879)
          ·
            refine ⟨1246917589529009365543319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831278393019339577028879 1246917589529009365543319)
            ·
              refine ⟨1870376384293514048314979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246917589529009365543319 1870376384293514048314979)
              ·
                refine ⟨2805564576440271072472469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870376384293514048314979 2805564576440271072472469)
                ·
                  refine ⟨131510839520637706522147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2805564576440271072472469 131510839520637706522147)
                  ·
                    rfl

theorem cell20_288131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_288131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288131 prefixEnd_288131 := by exact prefixLift 288131
  have htrace : WordTrace (prefixWord ++ tailWord_288131) baseStart_288131 baseEnd_288131 := by
    simpa [prefixWord, tailWord_288131, baseEnd_288131] using wordTrace_append hprefix tailTrace_288131
  have hstable : (prefixWord ++ tailWord_288131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288131).length < 2 ^ (prefixWord ++ tailWord_288131).sum := by decide
  have hdescent : baseEnd_288131 < baseStart_288131 := by decide
  rcases family_descends (prefixWord ++ tailWord_288131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288145 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_288145 : Nat := 118140960795 + 288145 * 2 ^ 59
def prefixEnd_288145 : Nat := 4983230072969 + 3 ^ 40 * 288145 * 2
def baseEnd_288145 : Nat := 131517229502115880055423

theorem tailTrace_288145 : CollatzResearch.WordTrace tailWord_288145 prefixEnd_288145 131517229502115880055423 := by
  unfold tailWord_288145
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509511541107351093201889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7006341027404900728801259 10509511541107351093201889)
  ·
    refine ⟨7882133655830513319901417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10509511541107351093201889 7882133655830513319901417)
    ·
      refine ⟨5911600241872884989926063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7882133655830513319901417 5911600241872884989926063)
      ·
        refine ⟨8867400362809327484889095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5911600241872884989926063 8867400362809327484889095)
        ·
          refine ⟨13301100544213991227333643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8867400362809327484889095 13301100544213991227333643)
          ·
            refine ⟨19951650816320986841000465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13301100544213991227333643 19951650816320986841000465)
            ·
              refine ⟨14963738112240740130750349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19951650816320986841000465 14963738112240740130750349)
              ·
                refine ⟨5611401792090277549031381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14963738112240740130750349 5611401792090277549031381)
                ·
                  refine ⟨131517229502115880055423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5611401792090277549031381 131517229502115880055423)
                  ·
                    rfl

theorem cell20_288145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_288145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288145 prefixEnd_288145 := by exact prefixLift 288145
  have htrace : WordTrace (prefixWord ++ tailWord_288145) baseStart_288145 baseEnd_288145 := by
    simpa [prefixWord, tailWord_288145, baseEnd_288145] using wordTrace_append hprefix tailTrace_288145
  have hstable : (prefixWord ++ tailWord_288145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288145).length < 2 ^ (prefixWord ++ tailWord_288145).sum := by decide
  have hdescent : baseEnd_288145 < baseStart_288145 := by decide
  rcases family_descends (prefixWord ++ tailWord_288145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288158 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_288158 : Nat := 118140960795 + 288158 * 2 ^ 59
def prefixEnd_288158 : Nat := 4983230072969 + 3 ^ 40 * 288158 * 2
def baseEnd_288158 : Nat := 131523163056345612622037

theorem tailTrace_288158 : CollatzResearch.WordTrace tailWord_288158 prefixEnd_288158 131523163056345612622037 := by
  unfold tailWord_288158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313748211257531789178141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7006657126706836208950085 1313748211257531789178141)
  ·
    refine ⟨492655579221574420941803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1313748211257531789178141 492655579221574420941803)
    ·
      refine ⟨738983368832361631412705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492655579221574420941803 738983368832361631412705)
      ·
        refine ⟨554237526624271223559529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738983368832361631412705 554237526624271223559529)
        ·
          refine ⟨415678144968203417669647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 554237526624271223559529 415678144968203417669647)
          ·
            refine ⟨623517217452305126504471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415678144968203417669647 623517217452305126504471)
            ·
              refine ⟨935275826178457689756707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623517217452305126504471 935275826178457689756707)
              ·
                refine ⟨1402913739267686534635061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935275826178457689756707 1402913739267686534635061)
                ·
                  refine ⟨131523163056345612622037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1402913739267686534635061 131523163056345612622037)
                  ·
                    rfl

theorem cell20_288158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_288158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288158 prefixEnd_288158 := by exact prefixLift 288158
  have htrace : WordTrace (prefixWord ++ tailWord_288158) baseStart_288158 baseEnd_288158 := by
    simpa [prefixWord, tailWord_288158, baseEnd_288158] using wordTrace_append hprefix tailTrace_288158
  have hstable : (prefixWord ++ tailWord_288158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288158).length < 2 ^ (prefixWord ++ tailWord_288158).sum := by decide
  have hdescent : baseEnd_288158 < baseStart_288158 := by decide
  rcases family_descends (prefixWord ++ tailWord_288158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288231 : List Nat := [1, 1, 5, 2, 1, 3, 2, 5]
def baseStart_288231 : Nat := 118140960795 + 288231 * 2 ^ 59
def prefixEnd_288231 : Nat := 4983230072969 + 3 ^ 40 * 288231 * 2
def baseEnd_288231 : Nat := 43852160748493934396135

theorem tailTrace_288231 : CollatzResearch.WordTrace tailWord_288231 prefixEnd_288231 43852160748493934396135 := by
  unfold tailWord_288231
  simp only [CollatzResearch.WordTrace]
  refine ⟨10512648218795787780832547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7008432145863858520555031 10512648218795787780832547)
  ·
    refine ⟨15768972328193681671248821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10512648218795787780832547 15768972328193681671248821)
    ·
      refine ⟨1478341155768157656679577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15768972328193681671248821 1478341155768157656679577)
      ·
        refine ⟨1108755866826118242509683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1478341155768157656679577 1108755866826118242509683)
        ·
          refine ⟨1663133800239177363764525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108755866826118242509683 1663133800239177363764525)
          ·
            refine ⟨623675175089691511411697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1663133800239177363764525 623675175089691511411697)
            ·
              refine ⟨467756381317268633558773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623675175089691511411697 467756381317268633558773)
              ·
                refine ⟨43852160748493934396135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 467756381317268633558773 43852160748493934396135)
                ·
                  rfl

theorem cell20_288231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_288231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288231 prefixEnd_288231 := by exact prefixLift 288231
  have htrace : WordTrace (prefixWord ++ tailWord_288231) baseStart_288231 baseEnd_288231 := by
    simpa [prefixWord, tailWord_288231, baseEnd_288231] using wordTrace_append hprefix tailTrace_288231
  have hstable : (prefixWord ++ tailWord_288231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288231).length < 2 ^ (prefixWord ++ tailWord_288231).sum := by decide
  have hdescent : baseEnd_288231 < baseStart_288231 := by decide
  rcases family_descends (prefixWord ++ tailWord_288231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288252 : List Nat := [2, 2, 2, 1, 2, 1, 4, 6]
def baseStart_288252 : Nat := 118140960795 + 288252 * 2 ^ 59
def prefixEnd_288252 : Nat := 4983230072969 + 3 ^ 40 * 288252 * 2
def baseEnd_288252 : Nat := 43855355739233021162773

theorem tailTrace_288252 : CollatzResearch.WordTrace tailWord_288252 prefixEnd_288252 43855355739233021162773 := by
  unfold tailWord_288252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5256707075859854183673505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7008942767813138911564673 5256707075859854183673505)
  ·
    refine ⟨3942530306894890637755129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5256707075859854183673505 3942530306894890637755129)
    ·
      refine ⟨2956897730171167978316347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3942530306894890637755129 2956897730171167978316347)
      ·
        refine ⟨4435346595256751967474521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2956897730171167978316347 4435346595256751967474521)
        ·
          refine ⟨3326509946442563975605891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435346595256751967474521 3326509946442563975605891)
          ·
            refine ⟨4989764919663845963408837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326509946442563975605891 4989764919663845963408837)
            ·
              refine ⟨935580922436971118139157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4989764919663845963408837 935580922436971118139157)
              ·
                refine ⟨43855355739233021162773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 935580922436971118139157 43855355739233021162773)
                ·
                  rfl

theorem cell20_288252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_288252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288252 prefixEnd_288252 := by exact prefixLift 288252
  have htrace : WordTrace (prefixWord ++ tailWord_288252) baseStart_288252 baseEnd_288252 := by
    simpa [prefixWord, tailWord_288252, baseEnd_288252] using wordTrace_append hprefix tailTrace_288252
  have hstable : (prefixWord ++ tailWord_288252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288252).length < 2 ^ (prefixWord ++ tailWord_288252).sum := by decide
  have hdescent : baseEnd_288252 < baseStart_288252 := by decide
  rcases family_descends (prefixWord ++ tailWord_288252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288259 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_288259 : Nat := 118140960795 + 288259 * 2 ^ 59
def prefixEnd_288259 : Nat := 4983230072969 + 3 ^ 40 * 288259 * 2
def baseEnd_288259 : Nat := 131569262208438150254957

theorem tailTrace_288259 : CollatzResearch.WordTrace tailWord_288259 prefixEnd_288259 131569262208438150254957 := by
  unfold tailWord_288259
  simp only [CollatzResearch.WordTrace]
  refine ⟨10513669462694348562851831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7009112975129565708567887 10513669462694348562851831)
  ·
    refine ⟨15770504194041522844277747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10513669462694348562851831 15770504194041522844277747)
    ·
      refine ⟨23655756291062284266416621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15770504194041522844277747 23655756291062284266416621)
      ·
        refine ⟨8870908609148356599906233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23655756291062284266416621 8870908609148356599906233)
        ·
          refine ⟨6653181456861267449929675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8870908609148356599906233 6653181456861267449929675)
          ·
            refine ⟨9979772185291901174894513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653181456861267449929675 9979772185291901174894513)
            ·
              refine ⟨7484829138968925881170885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9979772185291901174894513 7484829138968925881170885)
              ·
                refine ⟨1403405463556673602719541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7484829138968925881170885 1403405463556673602719541)
                ·
                  refine ⟨131569262208438150254957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403405463556673602719541 131569262208438150254957)
                  ·
                    rfl

theorem cell20_288259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_288259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288259 prefixEnd_288259 := by exact prefixLift 288259
  have htrace : WordTrace (prefixWord ++ tailWord_288259) baseStart_288259 baseEnd_288259 := by
    simpa [prefixWord, tailWord_288259, baseEnd_288259] using wordTrace_append hprefix tailTrace_288259
  have hstable : (prefixWord ++ tailWord_288259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288259).length < 2 ^ (prefixWord ++ tailWord_288259).sum := by decide
  have hdescent : baseEnd_288259 < baseStart_288259 := by decide
  rcases family_descends (prefixWord ++ tailWord_288259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288307 : List Nat := [1, 1, 1, 2, 4, 4, 3, 4]
def baseStart_288307 : Nat := 118140960795 + 288307 * 2 ^ 59
def prefixEnd_288307 : Nat := 4983230072969 + 3 ^ 40 * 288307 * 2
def baseEnd_288307 : Nat := 43863723572121105551587

theorem tailTrace_288307 : CollatzResearch.WordTrace tailWord_288307 prefixEnd_288307 43863723572121105551587 := by
  unfold tailWord_288307
  simp only [CollatzResearch.WordTrace]
  refine ⟨10515420166520452760599175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7010280111013635173732783 10515420166520452760599175)
  ·
    refine ⟨15773130249780679140898763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10515420166520452760599175 15773130249780679140898763)
    ·
      refine ⟨23659695374671018711348145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15773130249780679140898763 23659695374671018711348145)
      ·
        refine ⟨17744771531003264033511109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23659695374671018711348145 17744771531003264033511109)
        ·
          refine ⟨3327144662063112006283333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17744771531003264033511109 3327144662063112006283333)
          ·
            refine ⟨623839624136833501178125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3327144662063112006283333 623839624136833501178125)
            ·
              refine ⟨233939859051312562941797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623839624136833501178125 233939859051312562941797)
              ·
                refine ⟨43863723572121105551587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233939859051312562941797 43863723572121105551587)
                ·
                  rfl

theorem cell20_288307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_288307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288307 prefixEnd_288307 := by exact prefixLift 288307
  have htrace : WordTrace (prefixWord ++ tailWord_288307) baseStart_288307 baseEnd_288307 := by
    simpa [prefixWord, tailWord_288307, baseEnd_288307] using wordTrace_append hprefix tailTrace_288307
  have hstable : (prefixWord ++ tailWord_288307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288307).length < 2 ^ (prefixWord ++ tailWord_288307).sum := by decide
  have hdescent : baseEnd_288307 < baseStart_288307 := by decide
  rcases family_descends (prefixWord ++ tailWord_288307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288321 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_288321 : Nat := 118140960795 + 288321 * 2 ^ 59
def prefixEnd_288321 : Nat := 4983230072969 + 3 ^ 40 * 288321 * 2
def baseEnd_288321 : Nat := 131597560697841490188037

theorem tailTrace_288321 : CollatzResearch.WordTrace tailWord_288321 prefixEnd_288321 131597560697841490188037 := by
  unfold tailWord_288321
  simp only [CollatzResearch.WordTrace]
  refine ⟨10515930788469733151608817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7010620525646488767739211 10515930788469733151608817)
  ·
    refine ⟨7886948091352299863706613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10515930788469733151608817 7886948091352299863706613)
    ·
      refine ⟨739401383564278112222495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7886948091352299863706613 739401383564278112222495)
      ·
        refine ⟨1109102075346417168333743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739401383564278112222495 1109102075346417168333743)
        ·
          refine ⟨1663653113019625752500615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109102075346417168333743 1663653113019625752500615)
          ·
            refine ⟨2495479669529438628750923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663653113019625752500615 2495479669529438628750923)
            ·
              refine ⟨3743219504294157943126385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495479669529438628750923 3743219504294157943126385)
              ·
                refine ⟨2807414628220618457344789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3743219504294157943126385 2807414628220618457344789)
                ·
                  refine ⟨131597560697841490188037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2807414628220618457344789 131597560697841490188037)
                  ·
                    rfl

theorem cell20_288321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_288321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288321 prefixEnd_288321 := by exact prefixLift 288321
  have htrace : WordTrace (prefixWord ++ tailWord_288321) baseStart_288321 baseEnd_288321 := by
    simpa [prefixWord, tailWord_288321, baseEnd_288321] using wordTrace_append hprefix tailTrace_288321
  have hstable : (prefixWord ++ tailWord_288321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288321).length < 2 ^ (prefixWord ++ tailWord_288321).sum := by decide
  have hdescent : baseEnd_288321 < baseStart_288321 := by decide
  rcases family_descends (prefixWord ++ tailWord_288321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288338 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_288338 : Nat := 118140960795 + 288338 * 2 ^ 59
def prefixEnd_288338 : Nat := 4983230072969 + 3 ^ 40 * 288338 * 2
def baseEnd_288338 : Nat := 131605319961064986621301

theorem tailTrace_288338 : CollatzResearch.WordTrace tailWord_288338 prefixEnd_288338 131605319961064986621301 := by
  unfold tailWord_288338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629137707352036263744417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7011033886272096703318445 2629137707352036263744417)
  ·
    refine ⟨1971853280514027197808313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2629137707352036263744417 1971853280514027197808313)
    ·
      refine ⟨1478889960385520398356235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1971853280514027197808313 1478889960385520398356235)
      ·
        refine ⟨2218334940578280597534353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478889960385520398356235 2218334940578280597534353)
        ·
          refine ⟨1663751205433710448150765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2218334940578280597534353 1663751205433710448150765)
          ·
            refine ⟨623906702037641418056537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1663751205433710448150765 623906702037641418056537)
            ·
              refine ⟨467930026528231063542403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623906702037641418056537 467930026528231063542403)
              ·
                refine ⟨701895039792346595313605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467930026528231063542403 701895039792346595313605)
                ·
                  refine ⟨131605319961064986621301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701895039792346595313605 131605319961064986621301)
                  ·
                    rfl

theorem cell20_288338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_288338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288338 prefixEnd_288338 := by exact prefixLift 288338
  have htrace : WordTrace (prefixWord ++ tailWord_288338) baseStart_288338 baseEnd_288338 := by
    simpa [prefixWord, tailWord_288338, baseEnd_288338] using wordTrace_append hprefix tailTrace_288338
  have hstable : (prefixWord ++ tailWord_288338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288338).length < 2 ^ (prefixWord ++ tailWord_288338).sum := by decide
  have hdescent : baseEnd_288338 < baseStart_288338 := by decide
  rcases family_descends (prefixWord ++ tailWord_288338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288348 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_288348 : Nat := 118140960795 + 288348 * 2 ^ 59
def prefixEnd_288348 : Nat := 4983230072969 + 3 ^ 40 * 288348 * 2
def baseEnd_288348 : Nat := 131609884233549396287927

theorem tailTrace_288348 : CollatzResearch.WordTrace tailWord_288348 prefixEnd_288348 131609884233549396287927 := by
  unfold tailWord_288348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258457779685958381420849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7011277039581277841894465 5258457779685958381420849)
  ·
    refine ⟨3943843334764468786065637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5258457779685958381420849 3943843334764468786065637)
    ·
      refine ⟨739470625268337897387307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3943843334764468786065637 739470625268337897387307)
      ·
        refine ⟨1109205937902506846080961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739470625268337897387307 1109205937902506846080961)
        ·
          refine ⟨831904453426880134560721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109205937902506846080961 831904453426880134560721)
          ·
            refine ⟨623928340070160100920541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831904453426880134560721 623928340070160100920541)
            ·
              refine ⟨233973127526310037845203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623928340070160100920541 233973127526310037845203)
              ·
                refine ⟨350959691289465056767805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233973127526310037845203 350959691289465056767805)
                ·
                  refine ⟨131609884233549396287927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350959691289465056767805 131609884233549396287927)
                  ·
                    rfl

theorem cell20_288348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_288348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288348 prefixEnd_288348 := by exact prefixLift 288348
  have htrace : WordTrace (prefixWord ++ tailWord_288348) baseStart_288348 baseEnd_288348 := by
    simpa [prefixWord, tailWord_288348, baseEnd_288348] using wordTrace_append hprefix tailTrace_288348
  have hstable : (prefixWord ++ tailWord_288348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288348).length < 2 ^ (prefixWord ++ tailWord_288348).sum := by decide
  have hdescent : baseEnd_288348 < baseStart_288348 := by decide
  rcases family_descends (prefixWord ++ tailWord_288348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288359 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_288359 : Nat := 118140960795 + 288359 * 2 ^ 59
def prefixEnd_288359 : Nat := 4983230072969 + 3 ^ 40 * 288359 * 2
def baseEnd_288359 : Nat := 131614904933282246921215

theorem tailTrace_288359 : CollatzResearch.WordTrace tailWord_288359 prefixEnd_288359 131614904933282246921215 := by
  unfold tailWord_288359
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517316762332065641492131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7011544508221377094328087 10517316762332065641492131)
  ·
    refine ⟨15775975143498098462238197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10517316762332065641492131 15775975143498098462238197)
    ·
      refine ⟨1478997669702946730834831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15775975143498098462238197 1478997669702946730834831)
      ·
        refine ⟨2218496504554420096252247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478997669702946730834831 2218496504554420096252247)
        ·
          refine ⟨3327744756831630144378371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218496504554420096252247 3327744756831630144378371)
          ·
            refine ⟨4991617135247445216567557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327744756831630144378371 4991617135247445216567557)
            ·
              refine ⟨935928212858895978106417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4991617135247445216567557 935928212858895978106417)
              ·
                refine ⟨701946159644171983579813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935928212858895978106417 701946159644171983579813)
                ·
                  refine ⟨131614904933282246921215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701946159644171983579813 131614904933282246921215)
                  ·
                    rfl

theorem cell20_288359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_288359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288359 prefixEnd_288359 := by exact prefixLift 288359
  have htrace : WordTrace (prefixWord ++ tailWord_288359) baseStart_288359 baseEnd_288359 := by
    simpa [prefixWord, tailWord_288359, baseEnd_288359] using wordTrace_append hprefix tailTrace_288359
  have hstable : (prefixWord ++ tailWord_288359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288359).length < 2 ^ (prefixWord ++ tailWord_288359).sum := by decide
  have hdescent : baseEnd_288359 < baseStart_288359 := by decide
  rcases family_descends (prefixWord ++ tailWord_288359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288362 : List Nat := [3, 1, 3, 2, 1, 4, 2, 4]
def baseStart_288362 : Nat := 118140960795 + 288362 * 2 ^ 59
def prefixEnd_288362 : Nat := 4983230072969 + 3 ^ 40 * 288362 * 2
def baseEnd_288362 : Nat := 43872091405009189940401

theorem tailTrace_288362 : CollatzResearch.WordTrace tailWord_288362 prefixEnd_288362 43872091405009189940401 := by
  unfold tailWord_288362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629356545330299288462835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7011617454214131435900893 2629356545330299288462835)
  ·
    refine ⟨3944034817995448932694253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629356545330299288462835 3944034817995448932694253)
    ·
      refine ⟨1479013056748293349760345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3944034817995448932694253 1479013056748293349760345)
      ·
        refine ⟨1109259792561220012320259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479013056748293349760345 1109259792561220012320259)
        ·
          refine ⟨1663889688841830018480389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109259792561220012320259 1663889688841830018480389)
          ·
            refine ⟨311979316657843128465073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1663889688841830018480389 311979316657843128465073)
            ·
              refine ⟨233984487493382346348805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311979316657843128465073 233984487493382346348805)
              ·
                refine ⟨43872091405009189940401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233984487493382346348805 43872091405009189940401)
                ·
                  rfl

theorem cell20_288362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_288362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288362 prefixEnd_288362 := by exact prefixLift 288362
  have htrace : WordTrace (prefixWord ++ tailWord_288362) baseStart_288362 baseEnd_288362 := by
    simpa [prefixWord, tailWord_288362, baseEnd_288362] using wordTrace_append hprefix tailTrace_288362
  have hstable : (prefixWord ++ tailWord_288362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288362).length < 2 ^ (prefixWord ++ tailWord_288362).sum := by decide
  have hdescent : baseEnd_288362 < baseStart_288362 := by decide
  rcases family_descends (prefixWord ++ tailWord_288362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288407 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 3]
def baseStart_288407 : Nat := 118140960795 + 288407 * 2 ^ 59
def prefixEnd_288407 : Nat := 4983230072969 + 3 ^ 40 * 288407 * 2
def baseEnd_288407 : Nat := 131636813441207413321019

theorem tailTrace_288407 : CollatzResearch.WordTrace tailWord_288407 prefixEnd_288407 131636813441207413321019 := by
  unfold tailWord_288407
  simp only [CollatzResearch.WordTrace]
  refine ⟨10519067466158169839239475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7012711644105446559492983 10519067466158169839239475)
  ·
    refine ⟨15778601199237254758859213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10519067466158169839239475 15778601199237254758859213)
    ·
      refine ⟨5916975449713970534572205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15778601199237254758859213 5916975449713970534572205)
      ·
        refine ⟨2218865793642738950464577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5916975449713970534572205 2218865793642738950464577)
        ·
          refine ⟨1664149345232054212848433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2218865793642738950464577 1664149345232054212848433)
          ·
            refine ⟨1248112008924040659636325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664149345232054212848433 1248112008924040659636325)
            ·
              refine ⟨234021001673257623681811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1248112008924040659636325 234021001673257623681811)
              ·
                refine ⟨351031502509886435522717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234021001673257623681811 351031502509886435522717)
                ·
                  refine ⟨131636813441207413321019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351031502509886435522717 131636813441207413321019)
                  ·
                    rfl

theorem cell20_288407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 3].length) (baseStart_288407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288407 prefixEnd_288407 := by exact prefixLift 288407
  have htrace : WordTrace (prefixWord ++ tailWord_288407) baseStart_288407 baseEnd_288407 := by
    simpa [prefixWord, tailWord_288407, baseEnd_288407] using wordTrace_append hprefix tailTrace_288407
  have hstable : (prefixWord ++ tailWord_288407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288407).length < 2 ^ (prefixWord ++ tailWord_288407).sum := by decide
  have hdescent : baseEnd_288407 < baseStart_288407 := by decide
  rcases family_descends (prefixWord ++ tailWord_288407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288473 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_288473 : Nat := 118140960795 + 288473 * 2 ^ 59
def prefixEnd_288473 : Nat := 4983230072969 + 3 ^ 40 * 288473 * 2
def baseEnd_288473 : Nat := 131666937639604517120749

theorem tailTrace_288473 : CollatzResearch.WordTrace tailWord_288473 prefixEnd_288473 131666937639604517120749 := by
  unfold tailWord_288473
  simp only [CollatzResearch.WordTrace]
  refine ⟨10521474683919063111142073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7014316455946042074094715 10521474683919063111142073)
  ·
    refine ⟨7891106012939297333356555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10521474683919063111142073 7891106012939297333356555)
    ·
      refine ⟨11836659019408946000034833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7891106012939297333356555 11836659019408946000034833)
      ·
        refine ⟨8877494264556709500026125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11836659019408946000034833 8877494264556709500026125)
        ·
          refine ⟨3329060349208766062509797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8877494264556709500026125 3329060349208766062509797)
          ·
            refine ⟨624198815476643636720587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3329060349208766062509797 624198815476643636720587)
            ·
              refine ⟨936298223214965455080881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624198815476643636720587 936298223214965455080881)
              ·
                refine ⟨702223667411224091310661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936298223214965455080881 702223667411224091310661)
                ·
                  refine ⟨131666937639604517120749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702223667411224091310661 131666937639604517120749)
                  ·
                    rfl

theorem cell20_288473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_288473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288473 prefixEnd_288473 := by exact prefixLift 288473
  have htrace : WordTrace (prefixWord ++ tailWord_288473) baseStart_288473 baseEnd_288473 := by
    simpa [prefixWord, tailWord_288473, baseEnd_288473] using wordTrace_append hprefix tailTrace_288473
  have hstable : (prefixWord ++ tailWord_288473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288473).length < 2 ^ (prefixWord ++ tailWord_288473).sum := by decide
  have hdescent : baseEnd_288473 < baseStart_288473 := by decide
  rcases family_descends (prefixWord ++ tailWord_288473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288490 : List Nat := [3, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_288490 : Nat := 118140960795 + 288490 * 2 ^ 59
def prefixEnd_288490 : Nat := 4983230072969 + 3 ^ 40 * 288490 * 2
def baseEnd_288490 : Nat := 131674696902828013554013

theorem tailTrace_288490 : CollatzResearch.WordTrace tailWord_288490 prefixEnd_288490 131674696902828013554013 := by
  unfold tailWord_288490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2630523681214368753627731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7014729816571650009673949 2630523681214368753627731)
  ·
    refine ⟨3945785521821553130441597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2630523681214368753627731 3945785521821553130441597)
    ·
      refine ⟨1479669570683082423915599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3945785521821553130441597 1479669570683082423915599)
      ·
        refine ⟨2219504356024623635873399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479669570683082423915599 2219504356024623635873399)
        ·
          refine ⟨3329256534036935453810099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219504356024623635873399 3329256534036935453810099)
          ·
            refine ⟨4993884801055403180715149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329256534036935453810099 4993884801055403180715149)
            ·
              refine ⟨1872706800395776192768181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4993884801055403180715149 1872706800395776192768181)
              ·
                refine ⟨175566262537104018072017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1872706800395776192768181 175566262537104018072017)
                ·
                  refine ⟨131674696902828013554013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175566262537104018072017 131674696902828013554013)
                  ·
                    rfl

theorem cell20_288490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_288490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288490 prefixEnd_288490 := by exact prefixLift 288490
  have htrace : WordTrace (prefixWord ++ tailWord_288490) baseStart_288490 baseEnd_288490 := by
    simpa [prefixWord, tailWord_288490, baseEnd_288490] using wordTrace_append hprefix tailTrace_288490
  have hstable : (prefixWord ++ tailWord_288490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288490).length < 2 ^ (prefixWord ++ tailWord_288490).sum := by decide
  have hdescent : baseEnd_288490 < baseStart_288490 := by decide
  rcases family_descends (prefixWord ++ tailWord_288490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288500 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_288500 : Nat := 118140960795 + 288500 * 2 ^ 59
def prefixEnd_288500 : Nat := 4983230072969 + 3 ^ 40 * 288500 * 2
def baseEnd_288500 : Nat := 131679261175312423220639

theorem tailTrace_288500 : CollatzResearch.WordTrace tailWord_288500 prefixEnd_288500 131679261175312423220639 := by
  unfold tailWord_288500
  simp only [CollatzResearch.WordTrace]
  refine ⟨5261229727410623361187477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7014972969880831148249969 5261229727410623361187477)
  ·
    refine ⟨246620143472372970055663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5261229727410623361187477 246620143472372970055663)
    ·
      refine ⟨369930215208559455083495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246620143472372970055663 369930215208559455083495)
      ·
        refine ⟨554895322812839182625243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369930215208559455083495 554895322812839182625243)
        ·
          refine ⟨832342984219258773937865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554895322812839182625243 832342984219258773937865)
          ·
            refine ⟨624257238164444080453399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832342984219258773937865 624257238164444080453399)
            ·
              refine ⟨936385857246666120680099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624257238164444080453399 936385857246666120680099)
              ·
                refine ⟨1404578785869999181020149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936385857246666120680099 1404578785869999181020149)
                ·
                  refine ⟨131679261175312423220639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1404578785869999181020149 131679261175312423220639)
                  ·
                    rfl

theorem cell20_288500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_288500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288500 prefixEnd_288500 := by exact prefixLift 288500
  have htrace : WordTrace (prefixWord ++ tailWord_288500) baseStart_288500 baseEnd_288500 := by
    simpa [prefixWord, tailWord_288500, baseEnd_288500] using wordTrace_append hprefix tailTrace_288500
  have hstable : (prefixWord ++ tailWord_288500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288500).length < 2 ^ (prefixWord ++ tailWord_288500).sum := by decide
  have hdescent : baseEnd_288500 < baseStart_288500 := by decide
  rcases family_descends (prefixWord ++ tailWord_288500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288535 : List Nat := [1, 1, 3, 4, 2, 1, 4, 4]
def baseStart_288535 : Nat := 118140960795 + 288535 * 2 ^ 59
def prefixEnd_288535 : Nat := 4983230072969 + 3 ^ 40 * 288535 * 2
def baseEnd_288535 : Nat := 43898412043002619017943

theorem tailTrace_288535 : CollatzResearch.WordTrace tailWord_288535 prefixEnd_288535 43898412043002619017943 := by
  unfold tailWord_288535
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523736009694447699899059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7015824006462965133266039 10523736009694447699899059)
  ·
    refine ⟨15785604014541671549848589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10523736009694447699899059 15785604014541671549848589)
    ·
      refine ⟨5919601505453126831193221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15785604014541671549848589 5919601505453126831193221)
      ·
        refine ⟨1109925282272461280848729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5919601505453126831193221 1109925282272461280848729)
        ·
          refine ⟨832443961704345960636547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109925282272461280848729 832443961704345960636547)
          ·
            refine ⟨1248665942556518940954821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832443961704345960636547 1248665942556518940954821)
            ·
              refine ⟨234124864229347301429029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1248665942556518940954821 234124864229347301429029)
              ·
                refine ⟨43898412043002619017943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234124864229347301429029 43898412043002619017943)
                ·
                  rfl

theorem cell20_288535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_288535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288535 prefixEnd_288535 := by exact prefixLift 288535
  have htrace : WordTrace (prefixWord ++ tailWord_288535) baseStart_288535 baseEnd_288535 := by
    simpa [prefixWord, tailWord_288535, baseEnd_288535] using wordTrace_append hprefix tailTrace_288535
  have hstable : (prefixWord ++ tailWord_288535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288535).length < 2 ^ (prefixWord ++ tailWord_288535).sum := by decide
  have hdescent : baseEnd_288535 < baseStart_288535 := by decide
  rcases family_descends (prefixWord ++ tailWord_288535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288539 : List Nat := [1, 1, 1, 1, 1, 1, 4, 10]
def baseStart_288539 : Nat := 118140960795 + 288539 * 2 ^ 59
def prefixEnd_288539 : Nat := 4983230072969 + 3 ^ 40 * 288539 * 2
def baseEnd_288539 : Nat := 43899020612667206973493

theorem tailTrace_288539 : CollatzResearch.WordTrace tailWord_288539 prefixEnd_288539 43899020612667206973493 := by
  unfold tailWord_288539
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523881901679956383044671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7015921267786637588696447 10523881901679956383044671)
  ·
    refine ⟨15785822852519934574567007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10523881901679956383044671 15785822852519934574567007)
    ·
      refine ⟨23678734278779901861850511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15785822852519934574567007 23678734278779901861850511)
      ·
        refine ⟨35518101418169852792775767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23678734278779901861850511 35518101418169852792775767)
        ·
          refine ⟨53277152127254779189163651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35518101418169852792775767 53277152127254779189163651)
          ·
            refine ⟨79915728190882168783745477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53277152127254779189163651 79915728190882168783745477)
            ·
              refine ⟨14984199035790406646952277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79915728190882168783745477 14984199035790406646952277)
              ·
                refine ⟨43899020612667206973493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14984199035790406646952277 43899020612667206973493)
                ·
                  rfl

theorem cell20_288539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_288539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288539 prefixEnd_288539 := by exact prefixLift 288539
  have htrace : WordTrace (prefixWord ++ tailWord_288539) baseStart_288539 baseEnd_288539 := by
    simpa [prefixWord, tailWord_288539, baseEnd_288539] using wordTrace_append hprefix tailTrace_288539
  have hstable : (prefixWord ++ tailWord_288539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288539).length < 2 ^ (prefixWord ++ tailWord_288539).sum := by decide
  have hdescent : baseEnd_288539 < baseStart_288539 := by decide
  rcases family_descends (prefixWord ++ tailWord_288539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288545 : List Nat := [1, 2, 3, 2, 1, 5, 1, 3, 2]
def baseStart_288545 : Nat := 118140960795 + 288545 * 2 ^ 59
def prefixEnd_288545 : Nat := 4983230072969 + 3 ^ 40 * 288545 * 2
def baseEnd_288545 : Nat := 131699800401492266720455

theorem tailTrace_288545 : CollatzResearch.WordTrace tailWord_288545 prefixEnd_288545 131699800401492266720455 := by
  unfold tailWord_288545
  simp only [CollatzResearch.WordTrace]
  refine ⟨10524100739658219407763089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7016067159772146271842059 10524100739658219407763089)
  ·
    refine ⟨7893075554743664555822317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10524100739658219407763089 7893075554743664555822317)
    ·
      refine ⟨2959903333028874208433369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7893075554743664555822317 2959903333028874208433369)
      ·
        refine ⟨2219927499771655656325027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2959903333028874208433369 2219927499771655656325027)
        ·
          refine ⟨3329891249657483484487541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219927499771655656325027 3329891249657483484487541)
          ·
            refine ⟨312177304655389076670707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3329891249657483484487541 312177304655389076670707)
            ·
              refine ⟨468265956983083615006061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312177304655389076670707 468265956983083615006061)
              ·
                refine ⟨175599733868656355627273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468265956983083615006061 175599733868656355627273)
                ·
                  refine ⟨131699800401492266720455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175599733868656355627273 131699800401492266720455)
                  ·
                    rfl

theorem cell20_288545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_288545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288545 prefixEnd_288545 := by exact prefixLift 288545
  have htrace : WordTrace (prefixWord ++ tailWord_288545) baseStart_288545 baseEnd_288545 := by
    simpa [prefixWord, tailWord_288545, baseEnd_288545] using wordTrace_append hprefix tailTrace_288545
  have hstable : (prefixWord ++ tailWord_288545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288545).length < 2 ^ (prefixWord ++ tailWord_288545).sum := by decide
  have hdescent : baseEnd_288545 < baseStart_288545 := by decide
  rcases family_descends (prefixWord ++ tailWord_288545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288556 : List Nat := [2, 2, 1, 1, 1, 7, 6]
def baseStart_288556 : Nat := 118140960795 + 288556 * 2 ^ 59
def prefixEnd_288556 : Nat := 4983230072969 + 3 ^ 40 * 288556 * 2
def baseEnd_288556 : Nat := 14633869011247235261527

theorem tailTrace_288556 : CollatzResearch.WordTrace tailWord_288556 prefixEnd_288556 14633869011247235261527 := by
  unfold tailWord_288556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262250971309184143206761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7016334628412245524275681 5262250971309184143206761)
  ·
    refine ⟨3946688228481888107405071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5262250971309184143206761 3946688228481888107405071)
    ·
      refine ⟨5920032342722832161107607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3946688228481888107405071 5920032342722832161107607)
      ·
        refine ⟨8880048514084248241661411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5920032342722832161107607 8880048514084248241661411)
        ·
          refine ⟨13320072771126372362492117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8880048514084248241661411 13320072771126372362492117)
          ·
            refine ⟨312189205573274352245909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 13320072771126372362492117 312189205573274352245909)
            ·
              refine ⟨14633869011247235261527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 312189205573274352245909 14633869011247235261527)
              ·
                rfl

theorem cell20_288556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 6].length) (baseStart_288556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288556 prefixEnd_288556 := by exact prefixLift 288556
  have htrace : WordTrace (prefixWord ++ tailWord_288556) baseStart_288556 baseEnd_288556 := by
    simpa [prefixWord, tailWord_288556, baseEnd_288556] using wordTrace_append hprefix tailTrace_288556
  have hstable : (prefixWord ++ tailWord_288556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288556).length < 2 ^ (prefixWord ++ tailWord_288556).sum := by decide
  have hdescent : baseEnd_288556 < baseStart_288556 := by decide
  rcases family_descends (prefixWord ++ tailWord_288556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288573 : List Nat := [1, 4, 1, 4, 1, 2, 2, 5]
def baseStart_288573 : Nat := 118140960795 + 288573 * 2 ^ 59
def prefixEnd_288573 : Nat := 4983230072969 + 3 ^ 40 * 288573 * 2
def baseEnd_288573 : Nat := 43904193454816204595669

theorem tailTrace_288573 : CollatzResearch.WordTrace tailWord_288573 prefixEnd_288573 43904193454816204595669 := by
  unfold tailWord_288573
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525121983556780189782373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7016747989037853459854915 10525121983556780189782373)
  ·
    refine ⟨1973460371916896285584195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10525121983556780189782373 1973460371916896285584195)
    ·
      refine ⟨2960190557875344428376293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973460371916896285584195 2960190557875344428376293)
      ·
        refine ⟨555035729601627080320555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2960190557875344428376293 555035729601627080320555)
        ·
          refine ⟨832553594402440620480833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555035729601627080320555 832553594402440620480833)
          ·
            refine ⟨624415195801830465360625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832553594402440620480833 624415195801830465360625)
            ·
              refine ⟨468311396851372849020469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624415195801830465360625 468311396851372849020469)
              ·
                refine ⟨43904193454816204595669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 468311396851372849020469 43904193454816204595669)
                ·
                  rfl

theorem cell20_288573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_288573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288573 prefixEnd_288573 := by exact prefixLift 288573
  have htrace : WordTrace (prefixWord ++ tailWord_288573) baseStart_288573 baseEnd_288573 := by
    simpa [prefixWord, tailWord_288573, baseEnd_288573] using wordTrace_append hprefix tailTrace_288573
  have hstable : (prefixWord ++ tailWord_288573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288573).length < 2 ^ (prefixWord ++ tailWord_288573).sum := by decide
  have hdescent : baseEnd_288573 < baseStart_288573 := by decide
  rcases family_descends (prefixWord ++ tailWord_288573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288594 : List Nat := [3, 2, 2, 1, 1, 3, 2, 6]
def baseStart_288594 : Nat := 118140960795 + 288594 * 2 ^ 59
def prefixEnd_288594 : Nat := 4983230072969 + 3 ^ 40 * 288594 * 2
def baseEnd_288594 : Nat := 43907388445555291362307

theorem tailTrace_288594 : CollatzResearch.WordTrace tailWord_288594 prefixEnd_288594 43907388445555291362307 := by
  unfold tailWord_288594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631471979120175194074209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7017258610987133850864557 2631471979120175194074209)
  ·
    refine ⟨1973603984340131395555657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2631471979120175194074209 1973603984340131395555657)
    ·
      refine ⟨1480202988255098546666743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1973603984340131395555657 1480202988255098546666743)
      ·
        refine ⟨2220304482382647820000115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480202988255098546666743 2220304482382647820000115)
        ·
          refine ⟨3330456723573971730000173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220304482382647820000115 3330456723573971730000173)
          ·
            refine ⟨1248921271340239398750065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3330456723573971730000173 1248921271340239398750065)
            ·
              refine ⟨936690953505179549062549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248921271340239398750065 936690953505179549062549)
              ·
                refine ⟨43907388445555291362307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 936690953505179549062549 43907388445555291362307)
                ·
                  rfl

theorem cell20_288594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_288594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288594 prefixEnd_288594 := by exact prefixLift 288594
  have htrace : WordTrace (prefixWord ++ tailWord_288594) baseStart_288594 baseEnd_288594 := by
    simpa [prefixWord, tailWord_288594, baseEnd_288594] using wordTrace_append hprefix tailTrace_288594
  have hstable : (prefixWord ++ tailWord_288594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288594).length < 2 ^ (prefixWord ++ tailWord_288594).sum := by decide
  have hdescent : baseEnd_288594 < baseStart_288594 := by decide
  rcases family_descends (prefixWord ++ tailWord_288594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288621 : List Nat := [1, 5, 1, 1, 1, 1, 6, 2, 2]
def baseStart_288621 : Nat := 118140960795 + 288621 * 2 ^ 59
def prefixEnd_288621 : Nat := 4983230072969 + 3 ^ 40 * 288621 * 2
def baseEnd_288621 : Nat := 131734488872373780186811

theorem tailTrace_288621 : CollatzResearch.WordTrace tailWord_288621 prefixEnd_288621 131734488872373780186811 := by
  unfold tailWord_288621
  simp only [CollatzResearch.WordTrace]
  refine ⟨10526872687382884387529717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7017915124921922925019811 10526872687382884387529717)
  ·
    refine ⟨986894314442145411330911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10526872687382884387529717 986894314442145411330911)
    ·
      refine ⟨1480341471663218116996367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986894314442145411330911 1480341471663218116996367)
      ·
        refine ⟨2220512207494827175494551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480341471663218116996367 2220512207494827175494551)
        ·
          refine ⟨3330768311242240763241827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220512207494827175494551 3330768311242240763241827)
          ·
            refine ⟨4996152466863361144862741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330768311242240763241827 4996152466863361144862741)
            ·
              refine ⟨234194646884220053665441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4996152466863361144862741 234194646884220053665441)
              ·
                refine ⟨175645985163165040249081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234194646884220053665441 175645985163165040249081)
                ·
                  refine ⟨131734488872373780186811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175645985163165040249081 131734488872373780186811)
                  ·
                    rfl

theorem cell20_288621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_288621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288621 prefixEnd_288621 := by exact prefixLift 288621
  have htrace : WordTrace (prefixWord ++ tailWord_288621) baseStart_288621 baseEnd_288621 := by
    simpa [prefixWord, tailWord_288621, baseEnd_288621] using wordTrace_append hprefix tailTrace_288621
  have hstable : (prefixWord ++ tailWord_288621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288621).length < 2 ^ (prefixWord ++ tailWord_288621).sum := by decide
  have hdescent : baseEnd_288621 < baseStart_288621 := by decide
  rcases family_descends (prefixWord ++ tailWord_288621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288686 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_288686 : Nat := 118140960795 + 288686 * 2 ^ 59
def prefixEnd_288686 : Nat := 4983230072969 + 3 ^ 40 * 288686 * 2
def baseEnd_288686 : Nat := 131764156643522443019879

theorem tailTrace_288686 : CollatzResearch.WordTrace tailWord_288686 prefixEnd_288686 131764156643522443019879 := by
  unfold tailWord_288686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316155429018425061080739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7019495621431600325763941 1316155429018425061080739)
  ·
    refine ⟨1974233143527637591621109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316155429018425061080739 1974233143527637591621109)
    ·
      refine ⟨185084357205716024214479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1974233143527637591621109 185084357205716024214479)
      ·
        refine ⟨277626535808574036321719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185084357205716024214479 277626535808574036321719)
        ·
          refine ⟨416439803712861054482579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277626535808574036321719 416439803712861054482579)
          ·
            refine ⟨624659705569291581723869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416439803712861054482579 624659705569291581723869)
            ·
              refine ⟨234247389588484343146451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 624659705569291581723869 234247389588484343146451)
              ·
                refine ⟨351371084382726514719677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234247389588484343146451 351371084382726514719677)
                ·
                  refine ⟨131764156643522443019879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351371084382726514719677 131764156643522443019879)
                  ·
                    rfl

theorem cell20_288686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_288686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288686 prefixEnd_288686 := by exact prefixLift 288686
  have htrace : WordTrace (prefixWord ++ tailWord_288686) baseStart_288686 baseEnd_288686 := by
    simpa [prefixWord, tailWord_288686, baseEnd_288686] using wordTrace_append hprefix tailTrace_288686
  have hstable : (prefixWord ++ tailWord_288686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288686).length < 2 ^ (prefixWord ++ tailWord_288686).sum := by decide
  have hdescent : baseEnd_288686 < baseStart_288686 := by decide
  rcases family_descends (prefixWord ++ tailWord_288686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288691 : List Nat := [1, 1, 1, 2, 3, 1, 4, 7]
def baseStart_288691 : Nat := 118140960795 + 288691 * 2 ^ 59
def prefixEnd_288691 : Nat := 4983230072969 + 3 ^ 40 * 288691 * 2
def baseEnd_288691 : Nat := 43922146259921549284397

theorem tailTrace_288691 : CollatzResearch.WordTrace tailWord_288691 prefixEnd_288691 43922146259921549284397 := by
  unfold tailWord_288691
  simp only [CollatzResearch.WordTrace]
  refine ⟨10529425797129286342577927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7019617198086190895051951 10529425797129286342577927)
  ·
    refine ⟨15794138695693929513866891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10529425797129286342577927 15794138695693929513866891)
    ·
      refine ⟨23691208043540894270800337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15794138695693929513866891 23691208043540894270800337)
      ·
        refine ⟨17768406032655670703100253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23691208043540894270800337 17768406032655670703100253)
        ·
          refine ⟨6663152262245876513662595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17768406032655670703100253 6663152262245876513662595)
          ·
            refine ⟨9994728393368814770493893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663152262245876513662595 9994728393368814770493893)
            ·
              refine ⟨1874011573756652769467605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9994728393368814770493893 1874011573756652769467605)
              ·
                refine ⟨43922146259921549284397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1874011573756652769467605 43922146259921549284397)
                ·
                  rfl

theorem cell20_288691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_288691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288691 prefixEnd_288691 := by exact prefixLift 288691
  have htrace : WordTrace (prefixWord ++ tailWord_288691) baseStart_288691 baseEnd_288691 := by
    simpa [prefixWord, tailWord_288691, baseEnd_288691] using wordTrace_append hprefix tailTrace_288691
  have hstable : (prefixWord ++ tailWord_288691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288691).length < 2 ^ (prefixWord ++ tailWord_288691).sum := by decide
  have hdescent : baseEnd_288691 < baseStart_288691 := by decide
  rcases family_descends (prefixWord ++ tailWord_288691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288701 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_288701 : Nat := 118140960795 + 288701 * 2 ^ 59
def prefixEnd_288701 : Nat := 4983230072969 + 3 ^ 40 * 288701 * 2
def baseEnd_288701 : Nat := 131771003052249057519817

theorem tailTrace_288701 : CollatzResearch.WordTrace tailWord_288701 prefixEnd_288701 131771003052249057519817 := by
  unfold tailWord_288701
  simp only [CollatzResearch.WordTrace]
  refine ⟨10529790527093058050441957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7019860351395372033627971 10529790527093058050441957)
  ·
    refine ⟨1974335723829948384457867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10529790527093058050441957 1974335723829948384457867)
    ·
      refine ⟨2961503585744922576686801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974335723829948384457867 2961503585744922576686801)
      ·
        refine ⟨2221127689308691932515101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2961503585744922576686801 2221127689308691932515101)
        ·
          refine ⟨832922883490759474693163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2221127689308691932515101 832922883490759474693163)
          ·
            refine ⟨1249384325236139212039745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832922883490759474693163 1249384325236139212039745)
            ·
              refine ⟨937038243927104409029809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249384325236139212039745 937038243927104409029809)
              ·
                refine ⟨702778682945328306772357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937038243927104409029809 702778682945328306772357)
                ·
                  refine ⟨131771003052249057519817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702778682945328306772357 131771003052249057519817)
                  ·
                    rfl

theorem cell20_288701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_288701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288701 prefixEnd_288701 := by exact prefixLift 288701
  have htrace : WordTrace (prefixWord ++ tailWord_288701) baseStart_288701 baseEnd_288701 := by
    simpa [prefixWord, tailWord_288701, baseEnd_288701] using wordTrace_append hprefix tailTrace_288701
  have hstable : (prefixWord ++ tailWord_288701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288701).length < 2 ^ (prefixWord ++ tailWord_288701).sum := by decide
  have hdescent : baseEnd_288701 < baseStart_288701 := by decide
  rcases family_descends (prefixWord ++ tailWord_288701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288735 : List Nat := [1, 1, 2, 3, 4, 2, 3, 2, 2]
def baseStart_288735 : Nat := 118140960795 + 288735 * 2 ^ 59
def prefixEnd_288735 : Nat := 4983230072969 + 3 ^ 40 * 288735 * 2
def baseEnd_288735 : Nat := 131786521578696050386345

theorem tailTrace_288735 : CollatzResearch.WordTrace tailWord_288735 prefixEnd_288735 131786521578696050386345 := by
  unfold tailWord_288735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10531030608969881857179659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7020687072646587904786439 10531030608969881857179659)
  ·
    refine ⟨15796545913454822785769489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10531030608969881857179659 15796545913454822785769489)
    ·
      refine ⟨11847409435091117089327117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15796545913454822785769489 11847409435091117089327117)
      ·
        refine ⟨4442778538159168908497669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11847409435091117089327117 4442778538159168908497669)
        ·
          refine ⟨833020975904844170343313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4442778538159168908497669 833020975904844170343313)
          ·
            refine ⟨624765731928633127757485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833020975904844170343313 624765731928633127757485)
            ·
              refine ⟨234287149473237422909057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 624765731928633127757485 234287149473237422909057)
              ·
                refine ⟨175715362104928067181793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234287149473237422909057 175715362104928067181793)
                ·
                  refine ⟨131786521578696050386345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175715362104928067181793 131786521578696050386345)
                  ·
                    rfl

theorem cell20_288735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 2].length) (baseStart_288735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288735 prefixEnd_288735 := by exact prefixLift 288735
  have htrace : WordTrace (prefixWord ++ tailWord_288735) baseStart_288735 baseEnd_288735 := by
    simpa [prefixWord, tailWord_288735, baseEnd_288735] using wordTrace_append hprefix tailTrace_288735
  have hstable : (prefixWord ++ tailWord_288735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288735).length < 2 ^ (prefixWord ++ tailWord_288735).sum := by decide
  have hdescent : baseEnd_288735 < baseStart_288735 := by decide
  rcases family_descends (prefixWord ++ tailWord_288735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288739 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_288739 : Nat := 118140960795 + 288739 * 2 ^ 59
def prefixEnd_288739 : Nat := 4983230072969 + 3 ^ 40 * 288739 * 2
def baseEnd_288739 : Nat := 131788347287689814252995

theorem tailTrace_288739 : CollatzResearch.WordTrace tailWord_288739 prefixEnd_288739 131788347287689814252995 := by
  unfold tailWord_288739
  simp only [CollatzResearch.WordTrace]
  refine ⟨10531176500955390540325271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7020784333970260360216847 10531176500955390540325271)
  ·
    refine ⟨15796764751433085810487907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10531176500955390540325271 15796764751433085810487907)
    ·
      refine ⟨23695147127149628715731861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15796764751433085810487907 23695147127149628715731861)
      ·
        refine ⟨1110710021585138846049931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23695147127149628715731861 1110710021585138846049931)
        ·
          refine ⟨1666065032377708269074897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110710021585138846049931 1666065032377708269074897)
          ·
            refine ⟨1249548774283281201806173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666065032377708269074897 1249548774283281201806173)
            ·
              refine ⟨468580790356230450677315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1249548774283281201806173 468580790356230450677315)
              ·
                refine ⟨702871185534345676015973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468580790356230450677315 702871185534345676015973)
                ·
                  refine ⟨131788347287689814252995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702871185534345676015973 131788347287689814252995)
                  ·
                    rfl

theorem cell20_288739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_288739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288739 prefixEnd_288739 := by exact prefixLift 288739
  have htrace : WordTrace (prefixWord ++ tailWord_288739) baseStart_288739 baseEnd_288739 := by
    simpa [prefixWord, tailWord_288739, baseEnd_288739] using wordTrace_append hprefix tailTrace_288739
  have hstable : (prefixWord ++ tailWord_288739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288739).length < 2 ^ (prefixWord ++ tailWord_288739).sum := by decide
  have hdescent : baseEnd_288739 < baseStart_288739 := by decide
  rcases family_descends (prefixWord ++ tailWord_288739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288746 : List Nat := [3, 1, 3, 1, 2, 1, 4, 5]
def baseStart_288746 : Nat := 118140960795 + 288746 * 2 ^ 59
def prefixEnd_288746 : Nat := 4983230072969 + 3 ^ 40 * 288746 * 2
def baseEnd_288746 : Nat := 43930514092809633673211

theorem tailTrace_288746 : CollatzResearch.WordTrace tailWord_288746 prefixEnd_288746 43930514092809633673211 := by
  unfold tailWord_288746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632857952982507683957523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7020954541286687157220061 2632857952982507683957523)
  ·
    refine ⟨3949286929473761525936285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2632857952982507683957523 3949286929473761525936285)
    ·
      refine ⟨1480982598552660572226107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3949286929473761525936285 1480982598552660572226107)
      ·
        refine ⟨2221473897828990858339161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480982598552660572226107 2221473897828990858339161)
        ·
          refine ⟨1666105423371743143754371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221473897828990858339161 1666105423371743143754371)
          ·
            refine ⟨2499158135057614715631557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666105423371743143754371 2499158135057614715631557)
            ·
              refine ⟨468592150323302759180917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2499158135057614715631557 468592150323302759180917)
              ·
                refine ⟨43930514092809633673211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 468592150323302759180917 43930514092809633673211)
                ·
                  rfl

theorem cell20_288746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_288746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288746 prefixEnd_288746 := by exact prefixLift 288746
  have htrace : WordTrace (prefixWord ++ tailWord_288746) baseStart_288746 baseEnd_288746 := by
    simpa [prefixWord, tailWord_288746, baseEnd_288746] using wordTrace_append hprefix tailTrace_288746
  have hstable : (prefixWord ++ tailWord_288746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288746).length < 2 ^ (prefixWord ++ tailWord_288746).sum := by decide
  have hdescent : baseEnd_288746 < baseStart_288746 := by decide
  rcases family_descends (prefixWord ++ tailWord_288746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288760 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_288760 : Nat := 118140960795 + 288760 * 2 ^ 59
def prefixEnd_288760 : Nat := 4983230072969 + 3 ^ 40 * 288760 * 2
def baseEnd_288760 : Nat := 131797932259907074552909

theorem tailTrace_288760 : CollatzResearch.WordTrace tailWord_288760 prefixEnd_288760 131797932259907074552909 := by
  unfold tailWord_288760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265971216939655563419867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7021294955919540751226489 5265971216939655563419867)
  ·
    refine ⟨7898956825409483345129801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5265971216939655563419867 7898956825409483345129801)
    ·
      refine ⟨5924217619057112508847351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7898956825409483345129801 5924217619057112508847351)
      ·
        refine ⟨8886326428585668763271027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5924217619057112508847351 8886326428585668763271027)
        ·
          refine ⟨13329489642878503144906541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8886326428585668763271027 13329489642878503144906541)
          ·
            refine ⟨4998558616079438679339953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13329489642878503144906541 4998558616079438679339953)
            ·
              refine ⟨3748918962059579009504965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4998558616079438679339953 3748918962059579009504965)
              ·
                refine ⟨702922305386171064282181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3748918962059579009504965 702922305386171064282181)
                ·
                  refine ⟨131797932259907074552909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702922305386171064282181 131797932259907074552909)
                  ·
                    rfl

theorem cell20_288760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_288760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288760 prefixEnd_288760 := by exact prefixLift 288760
  have htrace : WordTrace (prefixWord ++ tailWord_288760) baseStart_288760 baseEnd_288760 := by
    simpa [prefixWord, tailWord_288760, baseEnd_288760] using wordTrace_append hprefix tailTrace_288760
  have hstable : (prefixWord ++ tailWord_288760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288760).length < 2 ^ (prefixWord ++ tailWord_288760).sum := by decide
  have hdescent : baseEnd_288760 < baseStart_288760 := by decide
  rcases family_descends (prefixWord ++ tailWord_288760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288794 : List Nat := [3, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_288794 : Nat := 118140960795 + 288794 * 2 ^ 59
def prefixEnd_288794 : Nat := 4983230072969 + 3 ^ 40 * 288794 * 2
def baseEnd_288794 : Nat := 131813450786354067419437

theorem tailTrace_288794 : CollatzResearch.WordTrace tailWord_288794 prefixEnd_288794 131813450786354067419437 := by
  unfold tailWord_288794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633295628939033733394359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7022121677170756622384957 2633295628939033733394359)
  ·
    refine ⟨3949943443408550600091539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2633295628939033733394359 3949943443408550600091539)
    ·
      refine ⟨5924915165112825900137309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3949943443408550600091539 5924915165112825900137309)
      ·
        refine ⟨2221843186917309712551491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5924915165112825900137309 2221843186917309712551491)
        ·
          refine ⟨3332764780375964568827237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221843186917309712551491 3332764780375964568827237)
          ·
            refine ⟨624893396320493356655107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3332764780375964568827237 624893396320493356655107)
            ·
              refine ⟨937340094480740034982661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624893396320493356655107 937340094480740034982661)
              ·
                refine ⟨175751267715138756559249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 937340094480740034982661 175751267715138756559249)
                ·
                  refine ⟨131813450786354067419437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175751267715138756559249 131813450786354067419437)
                  ·
                    rfl

theorem cell20_288794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_288794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288794 prefixEnd_288794 := by exact prefixLift 288794
  have htrace : WordTrace (prefixWord ++ tailWord_288794) baseStart_288794 baseEnd_288794 := by
    simpa [prefixWord, tailWord_288794, baseEnd_288794] using wordTrace_append hprefix tailTrace_288794
  have hstable : (prefixWord ++ tailWord_288794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288794).length < 2 ^ (prefixWord ++ tailWord_288794).sum := by decide
  have hdescent : baseEnd_288794 < baseStart_288794 := by decide
  rcases family_descends (prefixWord ++ tailWord_288794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288801 : List Nat := [1, 2, 3, 2, 4, 2, 1, 5]
def baseStart_288801 : Nat := 118140960795 + 288801 * 2 ^ 59
def prefixEnd_288801 : Nat := 4983230072969 + 3 ^ 40 * 288801 * 2
def baseEnd_288801 : Nat := 43938881925697718062025

theorem tailTrace_288801 : CollatzResearch.WordTrace tailWord_288801 prefixEnd_288801 43938881925697718062025 := by
  unfold tailWord_288801
  simp only [CollatzResearch.WordTrace]
  refine ⟨10533437826730775129082257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7022291884487183419388171 10533437826730775129082257)
  ·
    refine ⟨7900078370048081346811693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10533437826730775129082257 7900078370048081346811693)
    ·
      refine ⟨2962529388768030505054385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7900078370048081346811693 2962529388768030505054385)
      ·
        refine ⟨2221897041576022878790789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2962529388768030505054385 2221897041576022878790789)
        ·
          refine ⟨416605695295504289773273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2221897041576022878790789 416605695295504289773273)
          ·
            refine ⟨312454271471628217329955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416605695295504289773273 312454271471628217329955)
            ·
              refine ⟨468681407207442325994933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312454271471628217329955 468681407207442325994933)
              ·
                refine ⟨43938881925697718062025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 468681407207442325994933 43938881925697718062025)
                ·
                  rfl

theorem cell20_288801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_288801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288801 prefixEnd_288801 := by exact prefixLift 288801
  have htrace : WordTrace (prefixWord ++ tailWord_288801) baseStart_288801 baseEnd_288801 := by
    simpa [prefixWord, tailWord_288801, baseEnd_288801] using wordTrace_append hprefix tailTrace_288801
  have hstable : (prefixWord ++ tailWord_288801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288801).length < 2 ^ (prefixWord ++ tailWord_288801).sum := by decide
  have hdescent : baseEnd_288801 < baseStart_288801 := by decide
  rcases family_descends (prefixWord ++ tailWord_288801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288829 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_288829 : Nat := 118140960795 + 288829 * 2 ^ 59
def prefixEnd_288829 : Nat := 4983230072969 + 3 ^ 40 * 288829 * 2
def baseEnd_288829 : Nat := 131829425740049501252627

theorem tailTrace_288829 : CollatzResearch.WordTrace tailWord_288829 prefixEnd_288829 131829425740049501252627 := by
  unfold tailWord_288829
  simp only [CollatzResearch.WordTrace]
  refine ⟨10534459070629335911101541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7022972713752890607401027 10534459070629335911101541)
  ·
    refine ⟨1975211075743000483331539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10534459070629335911101541 1975211075743000483331539)
    ·
      refine ⟨2962816613614500724997309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975211075743000483331539 2962816613614500724997309)
      ·
        refine ⟨1111056230105437771873991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2962816613614500724997309 1111056230105437771873991)
        ·
          refine ⟨1666584345158156657810987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111056230105437771873991 1666584345158156657810987)
          ·
            refine ⟨2499876517737234986716481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666584345158156657810987 2499876517737234986716481)
            ·
              refine ⟨1874907388302926240037361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2499876517737234986716481 1874907388302926240037361)
              ·
                refine ⟨1406180541227194680028021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874907388302926240037361 1406180541227194680028021)
                ·
                  refine ⟨131829425740049501252627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1406180541227194680028021 131829425740049501252627)
                  ·
                    rfl

theorem cell20_288829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_288829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288829 prefixEnd_288829 := by exact prefixLift 288829
  have htrace : WordTrace (prefixWord ++ tailWord_288829) baseStart_288829 baseEnd_288829 := by
    simpa [prefixWord, tailWord_288829, baseEnd_288829] using wordTrace_append hprefix tailTrace_288829
  have hstable : (prefixWord ++ tailWord_288829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288829).length < 2 ^ (prefixWord ++ tailWord_288829).sum := by decide
  have hdescent : baseEnd_288829 < baseStart_288829 := by decide
  rcases family_descends (prefixWord ++ tailWord_288829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288832 : List Nat := [2, 1, 1, 2, 2, 5, 2, 3, 2]
def baseStart_288832 : Nat := 118140960795 + 288832 * 2 ^ 59
def prefixEnd_288832 : Nat := 4983230072969 + 3 ^ 40 * 288832 * 2
def baseEnd_288832 : Nat := 131830795021794824152615

theorem tailTrace_288832 : CollatzResearch.WordTrace tailWord_288832 prefixEnd_288832 131830795021794824152615 := by
  unfold tailWord_288832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267284244809233711730375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7023045659745644948973833 5267284244809233711730375)
  ·
    refine ⟨7900926367213850567595563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5267284244809233711730375 7900926367213850567595563)
    ·
      refine ⟨11851389550820775851393345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7900926367213850567595563 11851389550820775851393345)
      ·
        refine ⟨8888542163115581888545009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11851389550820775851393345 8888542163115581888545009)
        ·
          refine ⟨6666406622336686416408757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8888542163115581888545009 6666406622336686416408757)
          ·
            refine ⟨624975620844064351538321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6666406622336686416408757 624975620844064351538321)
            ·
              refine ⟨468731715633048263653741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624975620844064351538321 468731715633048263653741)
              ·
                refine ⟨175774393362393098870153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468731715633048263653741 175774393362393098870153)
                ·
                  refine ⟨131830795021794824152615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175774393362393098870153 131830795021794824152615)
                  ·
                    rfl

theorem cell20_288832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_288832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288832 prefixEnd_288832 := by exact prefixLift 288832
  have htrace : WordTrace (prefixWord ++ tailWord_288832) baseStart_288832 baseEnd_288832 := by
    simpa [prefixWord, tailWord_288832, baseEnd_288832] using wordTrace_append hprefix tailTrace_288832
  have hstable : (prefixWord ++ tailWord_288832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288832).length < 2 ^ (prefixWord ++ tailWord_288832).sum := by decide
  have hdescent : baseEnd_288832 < baseStart_288832 := by decide
  rcases family_descends (prefixWord ++ tailWord_288832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288846 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_288846 : Nat := 118140960795 + 288846 * 2 ^ 59
def prefixEnd_288846 : Nat := 4983230072969 + 3 ^ 40 * 288846 * 2
def baseEnd_288846 : Nat := 131837185003272997685891

theorem tailTrace_288846 : CollatzResearch.WordTrace tailWord_288846 prefixEnd_288846 131837185003272997685891 := by
  unfold tailWord_288846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316884888945968476808799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7023386074378498542980261 1316884888945968476808799)
  ·
    refine ⟨1975327333418952715213199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316884888945968476808799 1975327333418952715213199)
    ·
      refine ⟨2962991000128429072819799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975327333418952715213199 2962991000128429072819799)
      ·
        refine ⟨4444486500192643609229699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962991000128429072819799 4444486500192643609229699)
        ·
          refine ⟨6666729750288965413844549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4444486500192643609229699 6666729750288965413844549)
          ·
            refine ⟨1250011828179181015095853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6666729750288965413844549 1250011828179181015095853)
            ·
              refine ⟨468754435567192880660945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250011828179181015095853 468754435567192880660945)
              ·
                refine ⟨351565826675394660495709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468754435567192880660945 351565826675394660495709)
                ·
                  refine ⟨131837185003272997685891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351565826675394660495709 131837185003272997685891)
                  ·
                    rfl

theorem cell20_288846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_288846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288846 prefixEnd_288846 := by exact prefixLift 288846
  have htrace : WordTrace (prefixWord ++ tailWord_288846) baseStart_288846 baseEnd_288846 := by
    simpa [prefixWord, tailWord_288846, baseEnd_288846] using wordTrace_append hprefix tailTrace_288846
  have hstable : (prefixWord ++ tailWord_288846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288846).length < 2 ^ (prefixWord ++ tailWord_288846).sum := by decide
  have hdescent : baseEnd_288846 < baseStart_288846 := by decide
  rcases family_descends (prefixWord ++ tailWord_288846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288853 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_288853 : Nat := 118140960795 + 288853 * 2 ^ 59
def prefixEnd_288853 : Nat := 4983230072969 + 3 ^ 40 * 288853 * 2
def baseEnd_288853 : Nat := 131840379994012084452529

theorem tailTrace_288853 : CollatzResearch.WordTrace tailWord_288853 prefixEnd_288853 131840379994012084452529 := by
  unfold tailWord_288853
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535334422542388009975213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7023556281694925339983475 10535334422542388009975213)
  ·
    refine ⟨3950750408453395503740705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10535334422542388009975213 3950750408453395503740705)
    ·
      refine ⟨2963062806340046627805529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3950750408453395503740705 2963062806340046627805529)
      ·
        refine ⟨2222297104755034970854147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2963062806340046627805529 2222297104755034970854147)
        ·
          refine ⟨3333445657132552456281221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222297104755034970854147 3333445657132552456281221)
          ·
            refine ⟨625021060712353585552729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3333445657132552456281221 625021060712353585552729)
            ·
              refine ⟨468765795534265189164547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625021060712353585552729 468765795534265189164547)
              ·
                refine ⟨703148693301397783746821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468765795534265189164547 703148693301397783746821)
                ·
                  refine ⟨131840379994012084452529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 703148693301397783746821 131840379994012084452529)
                  ·
                    rfl

theorem cell20_288853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_288853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288853 prefixEnd_288853 := by exact prefixLift 288853
  have htrace : WordTrace (prefixWord ++ tailWord_288853) baseStart_288853 baseEnd_288853 := by
    simpa [prefixWord, tailWord_288853, baseEnd_288853] using wordTrace_append hprefix tailTrace_288853
  have hstable : (prefixWord ++ tailWord_288853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288853).length < 2 ^ (prefixWord ++ tailWord_288853).sum := by decide
  have hdescent : baseEnd_288853 < baseStart_288853 := by decide
  rcases family_descends (prefixWord ++ tailWord_288853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288867 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_288867 : Nat := 118140960795 + 288867 * 2 ^ 59
def prefixEnd_288867 : Nat := 4983230072969 + 3 ^ 40 * 288867 * 2
def baseEnd_288867 : Nat := 131846769975490257985805

theorem tailTrace_288867 : CollatzResearch.WordTrace tailWord_288867 prefixEnd_288867 131846769975490257985805 := by
  unfold tailWord_288867
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535845044491668400984855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7023896696327778933989903 10535845044491668400984855)
  ·
    refine ⟨15803767566737502601477283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10535845044491668400984855 15803767566737502601477283)
    ·
      refine ⟨23705651350106253902215925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15803767566737502601477283 23705651350106253902215925)
      ·
        refine ⟨2222404814072461303332743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23705651350106253902215925 2222404814072461303332743)
        ·
          refine ⟨3333607221108691954999115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222404814072461303332743 3333607221108691954999115)
          ·
            refine ⟨5000410831663037932498673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333607221108691954999115 5000410831663037932498673)
            ·
              refine ⟨3750308123747278449374005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5000410831663037932498673 3750308123747278449374005)
              ·
                refine ⟨351591386601307354628813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3750308123747278449374005 351591386601307354628813)
                ·
                  refine ⟨131846769975490257985805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351591386601307354628813 131846769975490257985805)
                  ·
                    rfl

theorem cell20_288867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_288867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288867 prefixEnd_288867 := by exact prefixLift 288867
  have htrace : WordTrace (prefixWord ++ tailWord_288867) baseStart_288867 baseEnd_288867 := by
    simpa [prefixWord, tailWord_288867, baseEnd_288867] using wordTrace_append hprefix tailTrace_288867
  have hstable : (prefixWord ++ tailWord_288867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288867).length < 2 ^ (prefixWord ++ tailWord_288867).sum := by decide
  have hdescent : baseEnd_288867 < baseStart_288867 := by decide
  rcases family_descends (prefixWord ++ tailWord_288867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288881 : List Nat := [1, 2, 2, 2, 1, 1, 5, 6]
def baseStart_288881 : Nat := 118140960795 + 288881 * 2 ^ 59
def prefixEnd_288881 : Nat := 4983230072969 + 3 ^ 40 * 288881 * 2
def baseEnd_288881 : Nat := 43951053318989477173027

theorem tailTrace_288881 : CollatzResearch.WordTrace tailWord_288881 prefixEnd_288881 43951053318989477173027 := by
  unfold tailWord_288881
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536355666440948791994497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7024237110960632527996331 10536355666440948791994497)
  ·
    refine ⟨7902266749830711593995873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10536355666440948791994497 7902266749830711593995873)
    ·
      refine ⟨5926700062373033695496905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7902266749830711593995873 5926700062373033695496905)
      ·
        refine ⟨4445025046779775271622679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5926700062373033695496905 4445025046779775271622679)
        ·
          refine ⟨6667537570169662907434019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445025046779775271622679 6667537570169662907434019)
          ·
            refine ⟨10001306355254494361151029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667537570169662907434019 10001306355254494361151029)
            ·
              refine ⟨937622470805108846357909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10001306355254494361151029 937622470805108846357909)
              ·
                refine ⟨43951053318989477173027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 937622470805108846357909 43951053318989477173027)
                ·
                  rfl

theorem cell20_288881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_288881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288881 prefixEnd_288881 := by exact prefixLift 288881
  have htrace : WordTrace (prefixWord ++ tailWord_288881) baseStart_288881 baseEnd_288881 := by
    simpa [prefixWord, tailWord_288881, baseEnd_288881] using wordTrace_append hprefix tailTrace_288881
  have hstable : (prefixWord ++ tailWord_288881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288881).length < 2 ^ (prefixWord ++ tailWord_288881).sum := by decide
  have hdescent : baseEnd_288881 < baseStart_288881 := by decide
  rcases family_descends (prefixWord ++ tailWord_288881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288905 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_288905 : Nat := 118140960795 + 288905 * 2 ^ 59
def prefixEnd_288905 : Nat := 4983230072969 + 3 ^ 40 * 288905 * 2
def baseEnd_288905 : Nat := 131864114210931014718983

theorem tailTrace_288905 : CollatzResearch.WordTrace tailWord_288905 prefixEnd_288905 131864114210931014718983 := by
  unfold tailWord_288905
  simp only [CollatzResearch.WordTrace]
  refine ⟨10537231018354000890868169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7024820678902667260578779 10537231018354000890868169)
  ·
    refine ⟨7902923263765500668151127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10537231018354000890868169 7902923263765500668151127)
    ·
      refine ⟨11854384895648251002226691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902923263765500668151127 11854384895648251002226691)
      ·
        refine ⟨17781577343472376503340037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11854384895648251002226691 17781577343472376503340037)
        ·
          refine ⟨3334045751901070594376257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17781577343472376503340037 3334045751901070594376257)
          ·
            refine ⟨2500534313925802945782193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3334045751901070594376257 2500534313925802945782193)
            ·
              refine ⟨1875400735444352209336645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2500534313925802945782193 1875400735444352209336645)
              ·
                refine ⟨351637637895816039250621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1875400735444352209336645 351637637895816039250621)
                ·
                  refine ⟨131864114210931014718983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351637637895816039250621 131864114210931014718983)
                  ·
                    rfl

theorem cell20_288905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_288905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288905 prefixEnd_288905 := by exact prefixLift 288905
  have htrace : WordTrace (prefixWord ++ tailWord_288905) baseStart_288905 baseEnd_288905 := by
    simpa [prefixWord, tailWord_288905, baseEnd_288905] using wordTrace_append hprefix tailTrace_288905
  have hstable : (prefixWord ++ tailWord_288905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288905).length < 2 ^ (prefixWord ++ tailWord_288905).sum := by decide
  have hdescent : baseEnd_288905 < baseStart_288905 := by decide
  rcases family_descends (prefixWord ++ tailWord_288905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288960 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_288960 : Nat := 118140960795 + 288960 * 2 ^ 59
def prefixEnd_288960 : Nat := 4983230072969 + 3 ^ 40 * 288960 * 2
def baseEnd_288960 : Nat := 131889217709595267885425

theorem tailTrace_288960 : CollatzResearch.WordTrace tailWord_288960 prefixEnd_288960 131889217709595267885425 := by
  unfold tailWord_288960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5269618516577372642060167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7026158022103163522746889 5269618516577372642060167)
  ·
    refine ⟨7904427774866058963090251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5269618516577372642060167 7904427774866058963090251)
    ·
      refine ⟨11856641662299088444635377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7904427774866058963090251 11856641662299088444635377)
      ·
        refine ⟨8892481246724316333476533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11856641662299088444635377 8892481246724316333476533)
        ·
          refine ⟨833670116880404656263425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8892481246724316333476533 833670116880404656263425)
          ·
            refine ⟨625252587660303492197569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833670116880404656263425 625252587660303492197569)
            ·
              refine ⟨468939440745227619148177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625252587660303492197569 468939440745227619148177)
              ·
                refine ⟨351704580558920714361133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468939440745227619148177 351704580558920714361133)
                ·
                  refine ⟨131889217709595267885425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351704580558920714361133 131889217709595267885425)
                  ·
                    rfl

theorem cell20_288960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_288960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288960 prefixEnd_288960 := by exact prefixLift 288960
  have htrace : WordTrace (prefixWord ++ tailWord_288960) baseStart_288960 baseEnd_288960 := by
    simpa [prefixWord, tailWord_288960, baseEnd_288960] using wordTrace_append hprefix tailTrace_288960
  have hstable : (prefixWord ++ tailWord_288960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288960).length < 2 ^ (prefixWord ++ tailWord_288960).sum := by decide
  have hdescent : baseEnd_288960 < baseStart_288960 := by decide
  rcases family_descends (prefixWord ++ tailWord_288960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_288974 : List Nat := [4, 1, 1, 1, 4, 1, 3, 5]
def baseStart_288974 : Nat := 118140960795 + 288974 * 2 ^ 59
def prefixEnd_288974 : Nat := 4983230072969 + 3 ^ 40 * 288974 * 2
def baseEnd_288974 : Nat := 43965202563691147139567

theorem tailTrace_288974 : CollatzResearch.WordTrace tailWord_288974 prefixEnd_288974 43965202563691147139567 := by
  unfold tailWord_288974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317468456888003209391247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7026498436736017116753317 1317468456888003209391247)
  ·
    refine ⟨1976202685332004814086871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1317468456888003209391247 1976202685332004814086871)
    ·
      refine ⟨2964304027998007221130307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976202685332004814086871 2964304027998007221130307)
      ·
        refine ⟨4446456041997010831695461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964304027998007221130307 4446456041997010831695461)
        ·
          refine ⟨833710507874439530942899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4446456041997010831695461 833710507874439530942899)
          ·
            refine ⟨1250565761811659296414349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833710507874439530942899 1250565761811659296414349)
            ·
              refine ⟨468962160679372236155381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250565761811659296414349 468962160679372236155381)
              ·
                refine ⟨43965202563691147139567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 468962160679372236155381 43965202563691147139567)
                ·
                  rfl

theorem cell20_288974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_288974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_288974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_288974 prefixEnd_288974 := by exact prefixLift 288974
  have htrace : WordTrace (prefixWord ++ tailWord_288974) baseStart_288974 baseEnd_288974 := by
    simpa [prefixWord, tailWord_288974, baseEnd_288974] using wordTrace_append hprefix tailTrace_288974
  have hstable : (prefixWord ++ tailWord_288974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_288974).length < 2 ^ (prefixWord ++ tailWord_288974).sum := by decide
  have hdescent : baseEnd_288974 < baseStart_288974 := by decide
  rcases family_descends (prefixWord ++ tailWord_288974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289022 : List Nat := [4, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_289022 : Nat := 118140960795 + 289022 * 2 ^ 59
def prefixEnd_289022 : Nat := 4983230072969 + 3 ^ 40 * 289022 * 2
def baseEnd_289022 : Nat := 131917516198998607818505

theorem tailTrace_289022 : CollatzResearch.WordTrace tailWord_289022 prefixEnd_289022 131917516198998607818505 := by
  unfold tailWord_289022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317687294866266234109665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7027665572620086581918213 1317687294866266234109665)
  ·
    refine ⟨988265471149699675582249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1317687294866266234109665 988265471149699675582249)
    ·
      refine ⟨741199103362274756686687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 988265471149699675582249 741199103362274756686687)
      ·
        refine ⟨1111798655043412135030031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741199103362274756686687 1111798655043412135030031)
        ·
          refine ⟨1667697982565118202545047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111798655043412135030031 1667697982565118202545047)
          ·
            refine ⟨2501546973847677303817571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667697982565118202545047 2501546973847677303817571)
            ·
              refine ⟨3752320460771515955726357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501546973847677303817571 3752320460771515955726357)
              ·
                refine ⟨175890021598664810424673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3752320460771515955726357 175890021598664810424673)
                ·
                  refine ⟨131917516198998607818505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175890021598664810424673 131917516198998607818505)
                  ·
                    rfl

theorem cell20_289022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_289022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289022 prefixEnd_289022 := by exact prefixLift 289022
  have htrace : WordTrace (prefixWord ++ tailWord_289022) baseStart_289022 baseEnd_289022 := by
    simpa [prefixWord, tailWord_289022, baseEnd_289022] using wordTrace_append hprefix tailTrace_289022
  have hstable : (prefixWord ++ tailWord_289022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289022).length < 2 ^ (prefixWord ++ tailWord_289022).sum := by decide
  have hdescent : baseEnd_289022 < baseStart_289022 := by decide
  rcases family_descends (prefixWord ++ tailWord_289022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289036 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_289036 : Nat := 118140960795 + 289036 * 2 ^ 59
def prefixEnd_289036 : Nat := 4983230072969 + 3 ^ 40 * 289036 * 2
def baseEnd_289036 : Nat := 131923906180476781351781

theorem tailTrace_289036 : CollatzResearch.WordTrace tailWord_289036 prefixEnd_289036 131923906180476781351781 := by
  unfold tailWord_289036
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271004490439705131943481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7028005987252940175924641 5271004490439705131943481)
  ·
    refine ⟨3953253367829778848957611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5271004490439705131943481 3953253367829778848957611)
    ·
      refine ⟨5929880051744668273436417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3953253367829778848957611 5929880051744668273436417)
      ·
        refine ⟨4447410038808501205077313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5929880051744668273436417 4447410038808501205077313)
        ·
          refine ⟨3335557529106375903807985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4447410038808501205077313 3335557529106375903807985)
          ·
            refine ⟨2501668146829781927855989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3335557529106375903807985 2501668146829781927855989)
            ·
              refine ⟨234531388765292055736499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2501668146829781927855989 234531388765292055736499)
              ·
                refine ⟨351797083147938083604749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234531388765292055736499 351797083147938083604749)
                ·
                  refine ⟨131923906180476781351781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351797083147938083604749 131923906180476781351781)
                  ·
                    rfl

theorem cell20_289036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_289036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289036 prefixEnd_289036 := by exact prefixLift 289036
  have htrace : WordTrace (prefixWord ++ tailWord_289036) baseStart_289036 baseEnd_289036 := by
    simpa [prefixWord, tailWord_289036, baseEnd_289036] using wordTrace_append hprefix tailTrace_289036
  have hstable : (prefixWord ++ tailWord_289036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289036).length < 2 ^ (prefixWord ++ tailWord_289036).sum := by decide
  have hdescent : baseEnd_289036 < baseStart_289036 := by decide
  rcases family_descends (prefixWord ++ tailWord_289036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289050 : List Nat := [3, 1, 1, 3, 4, 1, 1, 6]
def baseStart_289050 : Nat := 118140960795 + 289050 * 2 ^ 59
def prefixEnd_289050 : Nat := 4983230072969 + 3 ^ 40 * 289050 * 2
def baseEnd_289050 : Nat := 43976765387318318295019

theorem tailTrace_289050 : CollatzResearch.WordTrace tailWord_289050 prefixEnd_289050 43976765387318318295019 := by
  unfold tailWord_289050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635629900707172663724151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7028346401885793769931069 2635629900707172663724151)
  ·
    refine ⟨3953444851060758995586227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635629900707172663724151 3953444851060758995586227)
    ·
      refine ⟨5930167276591138493379341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3953444851060758995586227 5930167276591138493379341)
      ·
        refine ⟨2223812728721676935017253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5930167276591138493379341 2223812728721676935017253)
        ·
          refine ⟨416964886635314425315735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2223812728721676935017253 416964886635314425315735)
          ·
            refine ⟨625447329952971637973603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416964886635314425315735 625447329952971637973603)
            ·
              refine ⟨938170994929457456960405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625447329952971637973603 938170994929457456960405)
              ·
                refine ⟨43976765387318318295019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 938170994929457456960405 43976765387318318295019)
                ·
                  rfl

theorem cell20_289050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_289050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289050 prefixEnd_289050 := by exact prefixLift 289050
  have htrace : WordTrace (prefixWord ++ tailWord_289050) baseStart_289050 baseEnd_289050 := by
    simpa [prefixWord, tailWord_289050, baseEnd_289050] using wordTrace_append hprefix tailTrace_289050
  have hstable : (prefixWord ++ tailWord_289050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289050).length < 2 ^ (prefixWord ++ tailWord_289050).sum := by decide
  have hdescent : baseEnd_289050 < baseStart_289050 := by decide
  rcases family_descends (prefixWord ++ tailWord_289050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289060 : List Nat := [2, 3, 1, 3, 1, 2, 3, 3, 2]
def baseStart_289060 : Nat := 118140960795 + 289060 * 2 ^ 59
def prefixEnd_289060 : Nat := 4983230072969 + 3 ^ 40 * 289060 * 2
def baseEnd_289060 : Nat := 131934860434439364551683

theorem tailTrace_289060 : CollatzResearch.WordTrace tailWord_289060 prefixEnd_289060 131934860434439364551683 := by
  unfold tailWord_289060
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271442166396231181380317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7028589555194974908507089 5271442166396231181380317)
  ·
    refine ⟨1976790812398586693017619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5271442166396231181380317 1976790812398586693017619)
    ·
      refine ⟨2965186218597880039526429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976790812398586693017619 2965186218597880039526429)
      ·
        refine ⟨1111944831974205014822411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2965186218597880039526429 1111944831974205014822411)
        ·
          refine ⟨1667917247961307522233617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111944831974205014822411 1667917247961307522233617)
          ·
            refine ⟨1250937935970980641675213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667917247961307522233617 1250937935970980641675213)
            ·
              refine ⟨469101725989117740628205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250937935970980641675213 469101725989117740628205)
              ·
                refine ⟨175913147245919152735577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469101725989117740628205 175913147245919152735577)
                ·
                  refine ⟨131934860434439364551683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175913147245919152735577 131934860434439364551683)
                  ·
                    rfl

theorem cell20_289060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_289060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289060 prefixEnd_289060 := by exact prefixLift 289060
  have htrace : WordTrace (prefixWord ++ tailWord_289060) baseStart_289060 baseEnd_289060 := by
    simpa [prefixWord, tailWord_289060, baseEnd_289060] using wordTrace_append hprefix tailTrace_289060
  have hstable : (prefixWord ++ tailWord_289060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289060).length < 2 ^ (prefixWord ++ tailWord_289060).sum := by decide
  have hdescent : baseEnd_289060 < baseStart_289060 := by decide
  rcases family_descends (prefixWord ++ tailWord_289060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289063 : List Nat := [1, 1, 8, 1, 2, 1, 6]
def baseStart_289063 : Nat := 118140960795 + 289063 * 2 ^ 59
def prefixEnd_289063 : Nat := 4983230072969 + 3 ^ 40 * 289063 * 2
def baseEnd_289063 : Nat := 14659581079576076383519

theorem tailTrace_289063 : CollatzResearch.WordTrace tailWord_289063 prefixEnd_289063 14659581079576076383519 := by
  unfold tailWord_289063
  simp only [CollatzResearch.WordTrace]
  refine ⟨10542993751781593875119843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7028662501187729250079895 10542993751781593875119843)
  ·
    refine ⟨15814490627672390812679765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10542993751781593875119843 15814490627672390812679765)
    ·
      refine ⟨185326062043035829836091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 15814490627672390812679765 185326062043035829836091)
      ·
        refine ⟨277989093064553744754137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185326062043035829836091 277989093064553744754137)
        ·
          refine ⟨208491819798415308565603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277989093064553744754137 208491819798415308565603)
          ·
            refine ⟨312737729697622962848405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208491819798415308565603 312737729697622962848405)
            ·
              refine ⟨14659581079576076383519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 312737729697622962848405 14659581079576076383519)
              ·
                rfl

theorem cell20_289063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 6].length) (baseStart_289063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289063 prefixEnd_289063 := by exact prefixLift 289063
  have htrace : WordTrace (prefixWord ++ tailWord_289063) baseStart_289063 baseEnd_289063 := by
    simpa [prefixWord, tailWord_289063, baseEnd_289063] using wordTrace_append hprefix tailTrace_289063
  have hstable : (prefixWord ++ tailWord_289063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289063).length < 2 ^ (prefixWord ++ tailWord_289063).sum := by decide
  have hdescent : baseEnd_289063 < baseStart_289063 := by decide
  rcases family_descends (prefixWord ++ tailWord_289063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289081 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_289081 : Nat := 118140960795 + 289081 * 2 ^ 59
def prefixEnd_289081 : Nat := 4983230072969 + 3 ^ 40 * 289081 * 2
def baseEnd_289081 : Nat := 131944445406656624851597

theorem tailTrace_289081 : CollatzResearch.WordTrace tailWord_289081 prefixEnd_289081 131944445406656624851597 := by
  unfold tailWord_289081
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543650265716382949275097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7029100177144255299516731 10543650265716382949275097)
  ·
    refine ⟨7907737699287287211956323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10543650265716382949275097 7907737699287287211956323)
    ·
      refine ⟨11861606548930930817934485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7907737699287287211956323 11861606548930930817934485)
      ·
        refine ⟨556012806981137382090679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11861606548930930817934485 556012806981137382090679)
        ·
          refine ⟨834019210471706073136019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556012806981137382090679 834019210471706073136019)
          ·
            refine ⟨1251028815707559109704029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834019210471706073136019 1251028815707559109704029)
            ·
              refine ⟨469135805890334666139011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251028815707559109704029 469135805890334666139011)
              ·
                refine ⟨703703708835501999208517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469135805890334666139011 703703708835501999208517)
                ·
                  refine ⟨131944445406656624851597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 703703708835501999208517 131944445406656624851597)
                  ·
                    rfl

theorem cell20_289081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_289081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289081 prefixEnd_289081 := by exact prefixLift 289081
  have htrace : WordTrace (prefixWord ++ tailWord_289081) baseStart_289081 baseEnd_289081 := by
    simpa [prefixWord, tailWord_289081, baseEnd_289081] using wordTrace_append hprefix tailTrace_289081
  have hstable : (prefixWord ++ tailWord_289081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289081).length < 2 ^ (prefixWord ++ tailWord_289081).sum := by decide
  have hdescent : baseEnd_289081 < baseStart_289081 := by decide
  rcases family_descends (prefixWord ++ tailWord_289081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289095 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_289095 : Nat := 118140960795 + 289095 * 2 ^ 59
def prefixEnd_289095 : Nat := 4983230072969 + 3 ^ 40 * 289095 * 2
def baseEnd_289095 : Nat := 131950835388134798384873

theorem tailTrace_289095 : CollatzResearch.WordTrace tailWord_289095 prefixEnd_289095 131950835388134798384873 := by
  unfold tailWord_289095
  simp only [CollatzResearch.WordTrace]
  refine ⟨10544160887665663340284739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7029440591777108893523159 10544160887665663340284739)
  ·
    refine ⟨15816241331498495010427109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10544160887665663340284739 15816241331498495010427109)
    ·
      refine ⟨2965545249655967814455083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15816241331498495010427109 2965545249655967814455083)
      ·
        refine ⟨4448317874483951721682625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2965545249655967814455083 4448317874483951721682625)
        ·
          refine ⟨3336238405862963791261969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4448317874483951721682625 3336238405862963791261969)
          ·
            refine ⟨2502178804397222843446477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3336238405862963791261969 2502178804397222843446477)
            ·
              refine ⟨938317051648958566292429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2502178804397222843446477 938317051648958566292429)
              ·
                refine ⟨351868894368359462359661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938317051648958566292429 351868894368359462359661)
                ·
                  refine ⟨131950835388134798384873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351868894368359462359661 131950835388134798384873)
                  ·
                    rfl

theorem cell20_289095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_289095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289095 prefixEnd_289095 := by exact prefixLift 289095
  have htrace : WordTrace (prefixWord ++ tailWord_289095) baseStart_289095 baseEnd_289095 := by
    simpa [prefixWord, tailWord_289095, baseEnd_289095] using wordTrace_append hprefix tailTrace_289095
  have hstable : (prefixWord ++ tailWord_289095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289095).length < 2 ^ (prefixWord ++ tailWord_289095).sum := by decide
  have hdescent : baseEnd_289095 < baseStart_289095 := by decide
  rcases family_descends (prefixWord ++ tailWord_289095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289132 : List Nat := [2, 2, 1, 1, 7, 1, 2, 2, 2]
def baseStart_289132 : Nat := 118140960795 + 289132 * 2 ^ 59
def prefixEnd_289132 : Nat := 4983230072969 + 3 ^ 40 * 289132 * 2
def baseEnd_289132 : Nat := 131967723196327114151389

theorem tailTrace_289132 : CollatzResearch.WordTrace tailWord_289132 prefixEnd_289132 131967723196327114151389 := by
  unfold tailWord_289132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272755194265809329690825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7030340259021079106254433 5272755194265809329690825)
  ·
    refine ⟨3954566395699356997268119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5272755194265809329690825 3954566395699356997268119)
    ·
      refine ⟨5931849593549035495902179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3954566395699356997268119 5931849593549035495902179)
      ·
        refine ⟨8897774390323553243853269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5931849593549035495902179 8897774390323553243853269)
        ·
          refine ⟨208541587273208279152811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8897774390323553243853269 208541587273208279152811)
          ·
            refine ⟨312812380909812418729217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208541587273208279152811 312812380909812418729217)
            ·
              refine ⟨234609285682359314046913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312812380909812418729217 234609285682359314046913)
              ·
                refine ⟨175956964261769485535185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234609285682359314046913 175956964261769485535185)
                ·
                  refine ⟨131967723196327114151389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175956964261769485535185 131967723196327114151389)
                  ·
                    rfl

theorem cell20_289132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_289132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289132 prefixEnd_289132 := by exact prefixLift 289132
  have htrace : WordTrace (prefixWord ++ tailWord_289132) baseStart_289132 baseEnd_289132 := by
    simpa [prefixWord, tailWord_289132, baseEnd_289132] using wordTrace_append hprefix tailTrace_289132
  have hstable : (prefixWord ++ tailWord_289132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289132).length < 2 ^ (prefixWord ++ tailWord_289132).sum := by decide
  have hdescent : baseEnd_289132 < baseStart_289132 := by decide
  rcases family_descends (prefixWord ++ tailWord_289132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289136 : List Nat := [2, 1, 1, 1, 4, 3, 4, 2, 2]
def baseStart_289136 : Nat := 118140960795 + 289136 * 2 ^ 59
def prefixEnd_289136 : Nat := 4983230072969 + 3 ^ 40 * 289136 * 2
def baseEnd_289136 : Nat := 131969548905320878018039

theorem tailTrace_289136 : CollatzResearch.WordTrace tailWord_289136 prefixEnd_289136 131969548905320878018039 := by
  unfold tailWord_289136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272828140258563671263631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7030437520344751561684841 5272828140258563671263631)
  ·
    refine ⟨7909242210387845506895447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5272828140258563671263631 7909242210387845506895447)
    ·
      refine ⟨11863863315581768260343171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7909242210387845506895447 11863863315581768260343171)
      ·
        refine ⟨17795794973372652390514757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11863863315581768260343171 17795794973372652390514757)
        ·
          refine ⟨3336711557507372323221517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17795794973372652390514757 3336711557507372323221517)
          ·
            refine ⟨1251266834065264621208069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3336711557507372323221517 1251266834065264621208069)
            ·
              refine ⟨234612531387237116476513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1251266834065264621208069 234612531387237116476513)
              ·
                refine ⟨175959398540427837357385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234612531387237116476513 175959398540427837357385)
                ·
                  refine ⟨131969548905320878018039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175959398540427837357385 131969548905320878018039)
                  ·
                    rfl

theorem cell20_289136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_289136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289136 prefixEnd_289136 := by exact prefixLift 289136
  have htrace : WordTrace (prefixWord ++ tailWord_289136) baseStart_289136 baseEnd_289136 := by
    simpa [prefixWord, tailWord_289136, baseEnd_289136] using wordTrace_append hprefix tailTrace_289136
  have hstable : (prefixWord ++ tailWord_289136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289136).length < 2 ^ (prefixWord ++ tailWord_289136).sum := by decide
  have hdescent : baseEnd_289136 < baseStart_289136 := by decide
  rcases family_descends (prefixWord ++ tailWord_289136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289147 : List Nat := [1, 1, 1, 1, 1, 7, 3, 5]
def baseStart_289147 : Nat := 118140960795 + 289147 * 2 ^ 59
def prefixEnd_289147 : Nat := 4983230072969 + 3 ^ 40 * 289147 * 2
def baseEnd_289147 : Nat := 43991523201684576217109

theorem tailTrace_289147 : CollatzResearch.WordTrace tailWord_289147 prefixEnd_289147 43991523201684576217109 := by
  unfold tailWord_289147
  simp only [CollatzResearch.WordTrace]
  refine ⟨10546057483477276221177695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7030704988984850814118463 10546057483477276221177695)
  ·
    refine ⟨15819086225215914331766543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10546057483477276221177695 15819086225215914331766543)
    ·
      refine ⟨23728629337823871497649815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15819086225215914331766543 23728629337823871497649815)
      ·
        refine ⟨35592944006735807246474723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23728629337823871497649815 35592944006735807246474723)
        ·
          refine ⟨53389416010103710869712085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35592944006735807246474723 53389416010103710869712085)
          ·
            refine ⟨1251314437736805723508877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53389416010103710869712085 1251314437736805723508877)
            ·
              refine ⟨469242914151302146315829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251314437736805723508877 469242914151302146315829)
              ·
                refine ⟨43991523201684576217109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 469242914151302146315829 43991523201684576217109)
                ·
                  rfl

theorem cell20_289147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_289147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289147 prefixEnd_289147 := by exact prefixLift 289147
  have htrace : WordTrace (prefixWord ++ tailWord_289147) baseStart_289147 baseEnd_289147 := by
    simpa [prefixWord, tailWord_289147, baseEnd_289147] using wordTrace_append hprefix tailTrace_289147
  have hstable : (prefixWord ++ tailWord_289147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289147).length < 2 ^ (prefixWord ++ tailWord_289147).sum := by decide
  have hdescent : baseEnd_289147 < baseStart_289147 := by decide
  rcases family_descends (prefixWord ++ tailWord_289147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289164 : List Nat := [2, 2, 1, 2, 1, 5, 3, 4]
def baseStart_289164 : Nat := 118140960795 + 289164 * 2 ^ 59
def prefixEnd_289164 : Nat := 4983230072969 + 3 ^ 40 * 289164 * 2
def baseEnd_289164 : Nat := 43994109622759075028197

theorem tailTrace_289164 : CollatzResearch.WordTrace tailWord_289164 prefixEnd_289164 43994109622759075028197 := by
  unfold tailWord_289164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5273338762207844062273273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7031118349610458749697697 5273338762207844062273273)
  ·
    refine ⟨3955004071655883046704955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5273338762207844062273273 3955004071655883046704955)
    ·
      refine ⟨5932506107483824570057433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3955004071655883046704955 5932506107483824570057433)
      ·
        refine ⟨4449379580612868427543075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5932506107483824570057433 4449379580612868427543075)
        ·
          refine ⟨6674069370919302641314613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4449379580612868427543075 6674069370919302641314613)
          ·
            refine ⟨625694003523684622623245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6674069370919302641314613 625694003523684622623245)
            ·
              refine ⟨234635251321381733483717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625694003523684622623245 234635251321381733483717)
              ·
                refine ⟨43994109622759075028197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234635251321381733483717 43994109622759075028197)
                ·
                  rfl

theorem cell20_289164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_289164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289164 prefixEnd_289164 := by exact prefixLift 289164
  have htrace : WordTrace (prefixWord ++ tailWord_289164) baseStart_289164 baseEnd_289164 := by
    simpa [prefixWord, tailWord_289164, baseEnd_289164] using wordTrace_append hprefix tailTrace_289164
  have hstable : (prefixWord ++ tailWord_289164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289164).length < 2 ^ (prefixWord ++ tailWord_289164).sum := by decide
  have hdescent : baseEnd_289164 < baseStart_289164 := by decide
  rcases family_descends (prefixWord ++ tailWord_289164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289205 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 3]
def baseStart_289205 : Nat := 118140960795 + 289205 * 2 ^ 59
def prefixEnd_289205 : Nat := 4983230072969 + 3 ^ 40 * 289205 * 2
def baseEnd_289205 : Nat := 132001042385463304717757

theorem tailTrace_289205 : CollatzResearch.WordTrace tailWord_289205 prefixEnd_289205 132001042385463304717757 := by
  unfold tailWord_289205
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548172917267152126789069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7032115278178101417859379 10548172917267152126789069)
  ·
    refine ⟨3955564843975182047545901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10548172917267152126789069 3955564843975182047545901)
    ·
      refine ⟨1483336816490693267829713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3955564843975182047545901 1483336816490693267829713)
      ·
        refine ⟨1112502612368019950872285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1483336816490693267829713 1112502612368019950872285)
        ·
          refine ⟨417188479638007481577107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1112502612368019950872285 417188479638007481577107)
          ·
            refine ⟨625782719457011222365661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417188479638007481577107 625782719457011222365661)
            ·
              refine ⟨234668519796379208387123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625782719457011222365661 234668519796379208387123)
              ·
                refine ⟨352002779694568812580685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234668519796379208387123 352002779694568812580685)
                ·
                  refine ⟨132001042385463304717757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352002779694568812580685 132001042385463304717757)
                  ·
                    rfl

theorem cell20_289205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_289205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289205 prefixEnd_289205 := by exact prefixLift 289205
  have htrace : WordTrace (prefixWord ++ tailWord_289205) baseStart_289205 baseEnd_289205 := by
    simpa [prefixWord, tailWord_289205, baseEnd_289205] using wordTrace_append hprefix tailTrace_289205
  have hstable : (prefixWord ++ tailWord_289205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289205).length < 2 ^ (prefixWord ++ tailWord_289205).sum := by decide
  have hdescent : baseEnd_289205 < baseStart_289205 := by decide
  rcases family_descends (prefixWord ++ tailWord_289205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289223 : List Nat := [1, 1, 4, 1, 1, 5, 1, 6]
def baseStart_289223 : Nat := 118140960795 + 289223 * 2 ^ 59
def prefixEnd_289223 : Nat := 4983230072969 + 3 ^ 40 * 289223 * 2
def baseEnd_289223 : Nat := 44003086025311747372561

theorem tailTrace_289223 : CollatzResearch.WordTrace tailWord_289223 prefixEnd_289223 44003086025311747372561 := by
  unfold tailWord_289223
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548829431201941200944323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7032552954134627467296215 10548829431201941200944323)
  ·
    refine ⟨15823244146802911801416485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10548829431201941200944323 15823244146802911801416485)
    ·
      refine ⟨2966858277525545962765591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15823244146802911801416485 2966858277525545962765591)
      ·
        refine ⟨4450287416288318944148387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2966858277525545962765591 4450287416288318944148387)
        ·
          refine ⟨6675431124432478416222581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4450287416288318944148387 6675431124432478416222581)
          ·
            refine ⟨625821667915544851520867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6675431124432478416222581 625821667915544851520867)
            ·
              refine ⟨938732501873317277281301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625821667915544851520867 938732501873317277281301)
              ·
                refine ⟨44003086025311747372561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 938732501873317277281301 44003086025311747372561)
                ·
                  rfl

theorem cell20_289223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_289223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289223 prefixEnd_289223 := by exact prefixLift 289223
  have htrace : WordTrace (prefixWord ++ tailWord_289223) baseStart_289223 baseEnd_289223 := by
    simpa [prefixWord, tailWord_289223, baseEnd_289223] using wordTrace_append hprefix tailTrace_289223
  have hstable : (prefixWord ++ tailWord_289223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289223).length < 2 ^ (prefixWord ++ tailWord_289223).sum := by decide
  have hdescent : baseEnd_289223 < baseStart_289223 := by decide
  rcases family_descends (prefixWord ++ tailWord_289223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289306 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_289306 : Nat := 118140960795 + 289306 * 2 ^ 59
def prefixEnd_289306 : Nat := 4983230072969 + 3 ^ 40 * 289306 * 2
def baseEnd_289306 : Nat := 132047141537555842350677

theorem tailTrace_289306 : CollatzResearch.WordTrace tailWord_289306 prefixEnd_289306 132047141537555842350677 := by
  unfold tailWord_289306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2637964172475311594053943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7034571126600830917477181 2637964172475311594053943)
  ·
    refine ⟨3956946258712967391080915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2637964172475311594053943 3956946258712967391080915)
    ·
      refine ⟨5935419388069451086621373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3956946258712967391080915 5935419388069451086621373)
      ·
        refine ⟨2225782270526044157483015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5935419388069451086621373 2225782270526044157483015)
        ·
          refine ⟨3338673405789066236224523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225782270526044157483015 3338673405789066236224523)
          ·
            refine ⟨5008010108683599354336785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338673405789066236224523 5008010108683599354336785)
            ·
              refine ⟨3756007581512699515752589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5008010108683599354336785 3756007581512699515752589)
              ·
                refine ⟨1408502843067262318407221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3756007581512699515752589 1408502843067262318407221)
                ·
                  refine ⟨132047141537555842350677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1408502843067262318407221 132047141537555842350677)
                  ·
                    rfl

theorem cell20_289306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_289306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289306 prefixEnd_289306 := by exact prefixLift 289306
  have htrace : WordTrace (prefixWord ++ tailWord_289306) baseStart_289306 baseEnd_289306 := by
    simpa [prefixWord, tailWord_289306, baseEnd_289306] using wordTrace_append hprefix tailTrace_289306
  have hstable : (prefixWord ++ tailWord_289306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289306).length < 2 ^ (prefixWord ++ tailWord_289306).sum := by decide
  have hdescent : baseEnd_289306 < baseStart_289306 := by decide
  rcases family_descends (prefixWord ++ tailWord_289306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289357 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 3]
def baseStart_289357 : Nat := 118140960795 + 289357 * 2 ^ 59
def prefixEnd_289357 : Nat := 4983230072969 + 3 ^ 40 * 289357 * 2
def baseEnd_289357 : Nat := 132070419327226331650469

theorem tailTrace_289357 : CollatzResearch.WordTrace tailWord_289357 prefixEnd_289357 132070419327226331650469 := by
  unfold tailWord_289357
  simp only [CollatzResearch.WordTrace]
  refine ⟨10553716812716482086322325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7035811208477654724214883 10553716812716482086322325)
  ·
    refine ⟨494705475596085097796359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10553716812716482086322325 494705475596085097796359)
    ·
      refine ⟨742058213394127646694539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494705475596085097796359 742058213394127646694539)
      ·
        refine ⟨1113087320091191470041809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742058213394127646694539 1113087320091191470041809)
        ·
          refine ⟨834815490068393602531357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1113087320091191470041809 834815490068393602531357)
          ·
            refine ⟨313055808775647600949259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 834815490068393602531357 313055808775647600949259)
            ·
              refine ⟨469583713163471401423889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313055808775647600949259 469583713163471401423889)
              ·
                refine ⟨352187784872603551067917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469583713163471401423889 352187784872603551067917)
                ·
                  refine ⟨132070419327226331650469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352187784872603551067917 132070419327226331650469)
                  ·
                    rfl

theorem cell20_289357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_289357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289357 prefixEnd_289357 := by exact prefixLift 289357
  have htrace : WordTrace (prefixWord ++ tailWord_289357) baseStart_289357 baseEnd_289357 := by
    simpa [prefixWord, tailWord_289357, baseEnd_289357] using wordTrace_append hprefix tailTrace_289357
  have hstable : (prefixWord ++ tailWord_289357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289357).length < 2 ^ (prefixWord ++ tailWord_289357).sum := by decide
  have hdescent : baseEnd_289357 < baseStart_289357 := by decide
  rcases family_descends (prefixWord ++ tailWord_289357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289361 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 3]
def baseStart_289361 : Nat := 118140960795 + 289361 * 2 ^ 59
def prefixEnd_289361 : Nat := 4983230072969 + 3 ^ 40 * 289361 * 2
def baseEnd_289361 : Nat := 132072245036220095517119

theorem tailTrace_289361 : CollatzResearch.WordTrace tailWord_289361 prefixEnd_289361 132072245036220095517119 := by
  unfold tailWord_289361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10553862704701990769467937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7035908469801327179645291 10553862704701990769467937)
  ·
    refine ⟨7915397028526493077100953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10553862704701990769467937 7915397028526493077100953)
    ·
      refine ⟨5936547771394869807825715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7915397028526493077100953 5936547771394869807825715)
      ·
        refine ⟨8904821657092304711738573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5936547771394869807825715 8904821657092304711738573)
        ·
          refine ⟨3339308121409614266901965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8904821657092304711738573 3339308121409614266901965)
          ·
            refine ⟨1252240545528605350088237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3339308121409614266901965 1252240545528605350088237)
            ·
              refine ⟨469590204573227006283089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1252240545528605350088237 469590204573227006283089)
              ·
                refine ⟨352192653429920254712317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469590204573227006283089 352192653429920254712317)
                ·
                  refine ⟨132072245036220095517119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352192653429920254712317 132072245036220095517119)
                  ·
                    rfl

theorem cell20_289361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_289361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289361 prefixEnd_289361 := by exact prefixLift 289361
  have htrace : WordTrace (prefixWord ++ tailWord_289361) baseStart_289361 baseEnd_289361 := by
    simpa [prefixWord, tailWord_289361, baseEnd_289361] using wordTrace_append hprefix tailTrace_289361
  have hstable : (prefixWord ++ tailWord_289361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289361).length < 2 ^ (prefixWord ++ tailWord_289361).sum := by decide
  have hdescent : baseEnd_289361 < baseStart_289361 := by decide
  rcases family_descends (prefixWord ++ tailWord_289361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289398 : List Nat := [5, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_289398 : Nat := 118140960795 + 289398 * 2 ^ 59
def prefixEnd_289398 : Nat := 4983230072969 + 3 ^ 40 * 289398 * 2
def baseEnd_289398 : Nat := 132089132844412411283635

theorem tailTrace_289398 : CollatzResearch.WordTrace tailWord_289398 prefixEnd_289398 132089132844412411283635 := by
  unfold tailWord_289398
  simp only [CollatzResearch.WordTrace]
  refine ⟨659700762847996630535303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7036808137045297392376565 659700762847996630535303)
  ·
    refine ⟨989551144271994945802955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659700762847996630535303 989551144271994945802955)
    ·
      refine ⟨1484326716407992418704433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989551144271994945802955 1484326716407992418704433)
      ·
        refine ⟨1113245037305994314028325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1484326716407992418704433 1113245037305994314028325)
        ·
          refine ⟨208733444494873933880311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1113245037305994314028325 208733444494873933880311)
          ·
            refine ⟨313100166742310900820467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208733444494873933880311 313100166742310900820467)
            ·
              refine ⟨469650250113466351230701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313100166742310900820467 469650250113466351230701)
              ·
                refine ⟨176118843792549881711513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469650250113466351230701 176118843792549881711513)
                ·
                  refine ⟨132089132844412411283635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176118843792549881711513 132089132844412411283635)
                  ·
                    rfl

theorem cell20_289398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_289398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289398 prefixEnd_289398 := by exact prefixLift 289398
  have htrace : WordTrace (prefixWord ++ tailWord_289398) baseStart_289398 baseEnd_289398 := by
    simpa [prefixWord, tailWord_289398, baseEnd_289398] using wordTrace_append hprefix tailTrace_289398
  have hstable : (prefixWord ++ tailWord_289398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289398).length < 2 ^ (prefixWord ++ tailWord_289398).sum := by decide
  have hdescent : baseEnd_289398 < baseStart_289398 := by decide
  rcases family_descends (prefixWord ++ tailWord_289398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289413 : List Nat := [1, 3, 1, 1, 4, 4, 6]
def baseStart_289413 : Nat := 118140960795 + 289413 * 2 ^ 59
def prefixEnd_289413 : Nat := 4983230072969 + 3 ^ 40 * 289413 * 2
def baseEnd_289413 : Nat := 14677331028126558420397

theorem tailTrace_289413 : CollatzResearch.WordTrace tailWord_289413 prefixEnd_289413 14677331028126558420397 := by
  unfold tailWord_289413
  simp only [CollatzResearch.WordTrace]
  refine ⟨10555759300513603650360893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7037172867009069100240595 10555759300513603650360893)
  ·
    refine ⟨3958409737692601368885335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10555759300513603650360893 3958409737692601368885335)
    ·
      refine ⟨5937614606538902053328003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3958409737692601368885335 5937614606538902053328003)
      ·
        refine ⟨8906421909808353079992005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937614606538902053328003 8906421909808353079992005)
        ·
          refine ⟨1669954108089066202498501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8906421909808353079992005 1669954108089066202498501)
          ·
            refine ⟨313116395266699912968469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1669954108089066202498501 313116395266699912968469)
            ·
              refine ⟨14677331028126558420397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 313116395266699912968469 14677331028126558420397)
              ·
                rfl

theorem cell20_289413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 6].length) (baseStart_289413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289413 prefixEnd_289413 := by exact prefixLift 289413
  have htrace : WordTrace (prefixWord ++ tailWord_289413) baseStart_289413 baseEnd_289413 := by
    simpa [prefixWord, tailWord_289413, baseEnd_289413] using wordTrace_append hprefix tailTrace_289413
  have hstable : (prefixWord ++ tailWord_289413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289413).length < 2 ^ (prefixWord ++ tailWord_289413).sum := by decide
  have hdescent : baseEnd_289413 < baseStart_289413 := by decide
  rcases family_descends (prefixWord ++ tailWord_289413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289472 : List Nat := [2, 1, 1, 2, 4, 10]
def baseStart_289472 : Nat := 118140960795 + 289472 * 2 ^ 59
def prefixEnd_289472 : Nat := 4983230072969 + 3 ^ 40 * 289472 * 2
def baseEnd_289472 : Nat := 4893441054103594178395

theorem tailTrace_289472 : CollatzResearch.WordTrace tailWord_289472 prefixEnd_289472 4893441054103594178395 := by
  unfold tailWord_289472
  simp only [CollatzResearch.WordTrace]
  refine ⟨5278955603649928363379335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7038607471533237817839113 5278955603649928363379335)
  ·
    refine ⟨7918433405474892545069003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5278955603649928363379335 7918433405474892545069003)
    ·
      refine ⟨11877650108212338817603505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7918433405474892545069003 11877650108212338817603505)
      ·
        refine ⟨8908237581159254113202629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11877650108212338817603505 8908237581159254113202629)
        ·
          refine ⟨1670294546467360146225493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8908237581159254113202629 1670294546467360146225493)
          ·
            refine ⟨4893441054103594178395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1670294546467360146225493 4893441054103594178395)
            ·
              rfl

theorem cell20_289472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 10].length) (baseStart_289472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289472 prefixEnd_289472 := by exact prefixLift 289472
  have htrace : WordTrace (prefixWord ++ tailWord_289472) baseStart_289472 baseEnd_289472 := by
    simpa [prefixWord, tailWord_289472, baseEnd_289472] using wordTrace_append hprefix tailTrace_289472
  have hstable : (prefixWord ++ tailWord_289472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289472).length < 2 ^ (prefixWord ++ tailWord_289472).sum := by decide
  have hdescent : baseEnd_289472 < baseStart_289472 := by decide
  rcases family_descends (prefixWord ++ tailWord_289472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289503 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_289503 : Nat := 118140960795 + 289503 * 2 ^ 59
def prefixEnd_289503 : Nat := 4983230072969 + 3 ^ 40 * 289503 * 2
def baseEnd_289503 : Nat := 132137057705498712783205

theorem tailTrace_289503 : CollatzResearch.WordTrace tailWord_289503 prefixEnd_289503 132137057705498712783205 := by
  unfold tailWord_289503
  simp only [CollatzResearch.WordTrace]
  refine ⟨10559041870187549021137163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7039361246791699347424775 10559041870187549021137163)
  ·
    refine ⟨15838562805281323531705745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10559041870187549021137163 15838562805281323531705745)
    ·
      refine ⟨11878922103960992648779309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15838562805281323531705745 11878922103960992648779309)
      ·
        refine ⟨4454595788985372243292241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11878922103960992648779309 4454595788985372243292241)
        ·
          refine ⟨3340946841739029182469181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4454595788985372243292241 3340946841739029182469181)
          ·
            refine ⟨1252855065652135943425943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3340946841739029182469181 1252855065652135943425943)
            ·
              refine ⟨1879282598478203915138915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252855065652135943425943 1879282598478203915138915)
              ·
                refine ⟨2818923897717305872708373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879282598478203915138915 2818923897717305872708373)
                ·
                  refine ⟨132137057705498712783205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2818923897717305872708373 132137057705498712783205)
                  ·
                    rfl

theorem cell20_289503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_289503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289503 prefixEnd_289503 := by exact prefixLift 289503
  have htrace : WordTrace (prefixWord ++ tailWord_289503) baseStart_289503 baseEnd_289503 := by
    simpa [prefixWord, tailWord_289503, baseEnd_289503] using wordTrace_append hprefix tailTrace_289503
  have hstable : (prefixWord ++ tailWord_289503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289503).length < 2 ^ (prefixWord ++ tailWord_289503).sum := by decide
  have hdescent : baseEnd_289503 < baseStart_289503 := by decide
  rcases family_descends (prefixWord ++ tailWord_289503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289548 : List Nat := [2, 2, 1, 2, 2, 1, 1, 9]
def baseStart_289548 : Nat := 118140960795 + 289548 * 2 ^ 59
def prefixEnd_289548 : Nat := 4983230072969 + 3 ^ 40 * 289548 * 2
def baseEnd_289548 : Nat := 44052532310559518761007

theorem tailTrace_289548 : CollatzResearch.WordTrace tailWord_289548 prefixEnd_289548 44052532310559518761007 := by
  unfold tailWord_289548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280341577512260853262649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7040455436683014471016865 5280341577512260853262649)
  ·
    refine ⟨3960256183134195639946987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5280341577512260853262649 3960256183134195639946987)
    ·
      refine ⟨5940384274701293459920481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3960256183134195639946987 5940384274701293459920481)
      ·
        refine ⟨4455288206025970094940361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5940384274701293459920481 4455288206025970094940361)
        ·
          refine ⟨3341466154519477571205271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4455288206025970094940361 3341466154519477571205271)
          ·
            refine ⟨5012199231779216356807907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341466154519477571205271 5012199231779216356807907)
            ·
              refine ⟨7518298847668824535211861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012199231779216356807907 7518298847668824535211861)
              ·
                refine ⟨44052532310559518761007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7518298847668824535211861 44052532310559518761007)
                ·
                  rfl

theorem cell20_289548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_289548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289548 prefixEnd_289548 := by exact prefixLift 289548
  have htrace : WordTrace (prefixWord ++ tailWord_289548) baseStart_289548 baseEnd_289548 := by
    simpa [prefixWord, tailWord_289548, baseEnd_289548] using wordTrace_append hprefix tailTrace_289548
  have hstable : (prefixWord ++ tailWord_289548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289548).length < 2 ^ (prefixWord ++ tailWord_289548).sum := by decide
  have hdescent : baseEnd_289548 < baseStart_289548 := by decide
  rcases family_descends (prefixWord ++ tailWord_289548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289551 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 3]
def baseStart_289551 : Nat := 118140960795 + 289551 * 2 ^ 59
def prefixEnd_289551 : Nat := 4983230072969 + 3 ^ 40 * 289551 * 2
def baseEnd_289551 : Nat := 132158966213423879183009

theorem tailTrace_289551 : CollatzResearch.WordTrace tailWord_289551 prefixEnd_289551 132158966213423879183009 := by
  unfold tailWord_289551
  simp only [CollatzResearch.WordTrace]
  refine ⟨10560792574013653218884507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7040528382675768812589671 10560792574013653218884507)
  ·
    refine ⟨15841188861020479828326761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10560792574013653218884507 15841188861020479828326761)
    ·
      refine ⟨11880891645765359871245071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15841188861020479828326761 11880891645765359871245071)
      ·
        refine ⟨17821337468648039806867607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11880891645765359871245071 17821337468648039806867607)
        ·
          refine ⟨26732006202972059710301411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17821337468648039806867607 26732006202972059710301411)
          ·
            refine ⟨40098009304458089565452117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26732006202972059710301411 40098009304458089565452117)
            ·
              refine ⟨234949273268309118547571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 40098009304458089565452117 234949273268309118547571)
              ·
                refine ⟨352423909902463677821357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234949273268309118547571 352423909902463677821357)
                ·
                  refine ⟨132158966213423879183009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352423909902463677821357 132158966213423879183009)
                  ·
                    rfl

theorem cell20_289551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 3].length) (baseStart_289551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289551 prefixEnd_289551 := by exact prefixLift 289551
  have htrace : WordTrace (prefixWord ++ tailWord_289551) baseStart_289551 baseEnd_289551 := by
    simpa [prefixWord, tailWord_289551, baseEnd_289551] using wordTrace_append hprefix tailTrace_289551
  have hstable : (prefixWord ++ tailWord_289551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289551).length < 2 ^ (prefixWord ++ tailWord_289551).sum := by decide
  have hdescent : baseEnd_289551 < baseStart_289551 := by decide
  rcases family_descends (prefixWord ++ tailWord_289551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289582 : List Nat := [4, 1, 3, 2, 1, 3, 6]
def baseStart_289582 : Nat := 118140960795 + 289582 * 2 ^ 59
def prefixEnd_289582 : Nat := 4983230072969 + 3 ^ 40 * 289582 * 2
def baseEnd_289582 : Nat := 14685901717569505461061

theorem tailTrace_289582 : CollatzResearch.WordTrace tailWord_289582 prefixEnd_289582 14685901717569505461061 := by
  unfold tailWord_289582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320240404612668189157875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7041282157934230342175333 1320240404612668189157875)
  ·
    refine ⟨1980360606919002283736813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1320240404612668189157875 1980360606919002283736813)
    ·
      refine ⟨742635227594625856401305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1980360606919002283736813 742635227594625856401305)
      ·
        refine ⟨556976420695969392300979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 742635227594625856401305 556976420695969392300979)
        ·
          refine ⟨835464631043954088451469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556976420695969392300979 835464631043954088451469)
          ·
            refine ⟨313299236641482783169301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 835464631043954088451469 313299236641482783169301)
            ·
              refine ⟨14685901717569505461061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 313299236641482783169301 14685901717569505461061)
              ·
                rfl

theorem cell20_289582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 6].length) (baseStart_289582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289582 prefixEnd_289582 := by exact prefixLift 289582
  have htrace : WordTrace (prefixWord ++ tailWord_289582) baseStart_289582 baseEnd_289582 := by
    simpa [prefixWord, tailWord_289582, baseEnd_289582] using wordTrace_append hprefix tailTrace_289582
  have hstable : (prefixWord ++ tailWord_289582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289582).length < 2 ^ (prefixWord ++ tailWord_289582).sum := by decide
  have hdescent : baseEnd_289582 < baseStart_289582 := by decide
  rcases family_descends (prefixWord ++ tailWord_289582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289648 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_289648 : Nat := 118140960795 + 289648 * 2 ^ 59
def prefixEnd_289648 : Nat := 4983230072969 + 3 ^ 40 * 289648 * 2
def baseEnd_289648 : Nat := 132203239656522652949279

theorem tailTrace_289648 : CollatzResearch.WordTrace tailWord_289648 prefixEnd_289648 132203239656522652949279 := by
  unfold tailWord_289648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282165227331119392582799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7042886969774825856777065 5282165227331119392582799)
  ·
    refine ⟨7923247840996679088874199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5282165227331119392582799 7923247840996679088874199)
    ·
      refine ⟨11884871761495018633311299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7923247840996679088874199 11884871761495018633311299)
      ·
        refine ⟨17827307642242527949966949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11884871761495018633311299 17827307642242527949966949)
        ·
          refine ⟨3342620182920473990618803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17827307642242527949966949 3342620182920473990618803)
          ·
            refine ⟨5013930274380710985928205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3342620182920473990618803 5013930274380710985928205)
            ·
              refine ⟨1880223852892766619723077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5013930274380710985928205 1880223852892766619723077)
              ·
                refine ⟨352541972417393741198077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1880223852892766619723077 352541972417393741198077)
                ·
                  refine ⟨132203239656522652949279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352541972417393741198077 132203239656522652949279)
                  ·
                    rfl

theorem cell20_289648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_289648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289648 prefixEnd_289648 := by exact prefixLift 289648
  have htrace : WordTrace (prefixWord ++ tailWord_289648) baseStart_289648 baseEnd_289648 := by
    simpa [prefixWord, tailWord_289648, baseEnd_289648] using wordTrace_append hprefix tailTrace_289648
  have hstable : (prefixWord ++ tailWord_289648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289648).length < 2 ^ (prefixWord ++ tailWord_289648).sum := by decide
  have hdescent : baseEnd_289648 < baseStart_289648 := by decide
  rcases family_descends (prefixWord ++ tailWord_289648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289651 : List Nat := [1, 1, 1, 2, 2, 1, 8, 2, 2]
def baseStart_289651 : Nat := 118140960795 + 289651 * 2 ^ 59
def prefixEnd_289651 : Nat := 4983230072969 + 3 ^ 40 * 289651 * 2
def baseEnd_289651 : Nat := 132204608938267975849267

theorem tailTrace_289651 : CollatzResearch.WordTrace tailWord_289651 prefixEnd_289651 132204608938267975849267 := by
  unfold tailWord_289651
  simp only [CollatzResearch.WordTrace]
  refine ⟨10564439873651370297524807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7042959915767580198349871 10564439873651370297524807)
  ·
    refine ⟨15846659810477055446287211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10564439873651370297524807 15846659810477055446287211)
    ·
      refine ⟨23769989715715583169430817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15846659810477055446287211 23769989715715583169430817)
      ·
        refine ⟨17827492286786687377073113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23769989715715583169430817 17827492286786687377073113)
        ·
          refine ⟨13370619215090015532804835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17827492286786687377073113 13370619215090015532804835)
          ·
            refine ⟨20055928822635023299207253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13370619215090015532804835 20055928822635023299207253)
            ·
              refine ⟨235030415890254179287585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 20055928822635023299207253 235030415890254179287585)
              ·
                refine ⟨176272811917690634465689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235030415890254179287585 176272811917690634465689)
                ·
                  refine ⟨132204608938267975849267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176272811917690634465689 132204608938267975849267)
                  ·
                    rfl

theorem cell20_289651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 2].length) (baseStart_289651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289651 prefixEnd_289651 := by exact prefixLift 289651
  have htrace : WordTrace (prefixWord ++ tailWord_289651) baseStart_289651 baseEnd_289651 := by
    simpa [prefixWord, tailWord_289651, baseEnd_289651] using wordTrace_append hprefix tailTrace_289651
  have hstable : (prefixWord ++ tailWord_289651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289651).length < 2 ^ (prefixWord ++ tailWord_289651).sum := by decide
  have hdescent : baseEnd_289651 < baseStart_289651 := by decide
  rcases family_descends (prefixWord ++ tailWord_289651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289672 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_289672 : Nat := 118140960795 + 289672 * 2 ^ 59
def prefixEnd_289672 : Nat := 4983230072969 + 3 ^ 40 * 289672 * 2
def baseEnd_289672 : Nat := 132214193910485236149181

theorem tailTrace_289672 : CollatzResearch.WordTrace tailWord_289672 prefixEnd_289672 132214193910485236149181 := by
  unfold tailWord_289672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282602903287645442019635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7043470537716860589359513 5282602903287645442019635)
  ·
    refine ⟨7923904354931468163029453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5282602903287645442019635 7923904354931468163029453)
    ·
      refine ⟨2971464133099300561136045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7923904354931468163029453 2971464133099300561136045)
      ·
        refine ⟨1114299049912237710426017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2971464133099300561136045 1114299049912237710426017)
        ·
          refine ⟨835724287434178282819513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114299049912237710426017 835724287434178282819513)
          ·
            refine ⟨626793215575633712114635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835724287434178282819513 626793215575633712114635)
            ·
              refine ⟨940189823363450568171953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626793215575633712114635 940189823363450568171953)
              ·
                refine ⟨705142367522587926128965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940189823363450568171953 705142367522587926128965)
                ·
                  refine ⟨132214193910485236149181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705142367522587926128965 132214193910485236149181)
                  ·
                    rfl

theorem cell20_289672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_289672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289672 prefixEnd_289672 := by exact prefixLift 289672
  have htrace : WordTrace (prefixWord ++ tailWord_289672) baseStart_289672 baseEnd_289672 := by
    simpa [prefixWord, tailWord_289672, baseEnd_289672] using wordTrace_append hprefix tailTrace_289672
  have hstable : (prefixWord ++ tailWord_289672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289672).length < 2 ^ (prefixWord ++ tailWord_289672).sum := by decide
  have hdescent : baseEnd_289672 < baseStart_289672 := by decide
  rcases family_descends (prefixWord ++ tailWord_289672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289693 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_289693 : Nat := 118140960795 + 289693 * 2 ^ 59
def prefixEnd_289693 : Nat := 4983230072969 + 3 ^ 40 * 289693 * 2
def baseEnd_289693 : Nat := 132223778882702496449095

theorem tailTrace_289693 : CollatzResearch.WordTrace tailWord_289693 prefixEnd_289693 132223778882702496449095 := by
  unfold tailWord_289693
  simp only [CollatzResearch.WordTrace]
  refine ⟨10565971739499211470553733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7043981159666140980369155 10565971739499211470553733)
  ·
    refine ⟨1981119701156102150728825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10565971739499211470553733 1981119701156102150728825)
    ·
      refine ⟨1485839775867076613046619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1981119701156102150728825 1485839775867076613046619)
      ·
        refine ⟨2228759663800614919569929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485839775867076613046619 2228759663800614919569929)
        ·
          refine ⟨1671569747850461189677447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2228759663800614919569929 1671569747850461189677447)
          ·
            refine ⟨2507354621775691784516171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671569747850461189677447 2507354621775691784516171)
            ·
              refine ⟨3761031932663537676774257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507354621775691784516171 3761031932663537676774257)
              ·
                refine ⟨2820773949497653257580693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761031932663537676774257 2820773949497653257580693)
                ·
                  refine ⟨132223778882702496449095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2820773949497653257580693 132223778882702496449095)
                  ·
                    rfl

theorem cell20_289693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_289693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289693 prefixEnd_289693 := by exact prefixLift 289693
  have htrace : WordTrace (prefixWord ++ tailWord_289693) baseStart_289693 baseEnd_289693 := by
    simpa [prefixWord, tailWord_289693, baseEnd_289693] using wordTrace_append hprefix tailTrace_289693
  have hstable : (prefixWord ++ tailWord_289693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289693).length < 2 ^ (prefixWord ++ tailWord_289693).sum := by decide
  have hdescent : baseEnd_289693 < baseStart_289693 := by decide
  rcases family_descends (prefixWord ++ tailWord_289693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289700 : List Nat := [2, 3, 1, 2, 1, 2, 9]
def baseStart_289700 : Nat := 118140960795 + 289700 * 2 ^ 59
def prefixEnd_289700 : Nat := 4983230072969 + 3 ^ 40 * 289700 * 2
def baseEnd_289700 : Nat := 14691885985937953690637

theorem tailTrace_289700 : CollatzResearch.WordTrace tailWord_289700 prefixEnd_289700 14691885985937953690637 := by
  unfold tailWord_289700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283113525236925833029277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7044151366982567777372369 5283113525236925833029277)
  ·
    refine ⟨1981167571963847187385979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5283113525236925833029277 1981167571963847187385979)
    ·
      refine ⟨2971751357945770781078969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981167571963847187385979 2971751357945770781078969)
      ·
        refine ⟨2228813518459328085809227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2971751357945770781078969 2228813518459328085809227)
        ·
          refine ⟨3343220277688992128713841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228813518459328085809227 3343220277688992128713841)
          ·
            refine ⟨2507415208266744096535381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3343220277688992128713841 2507415208266744096535381)
            ·
              refine ⟨14691885985937953690637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2507415208266744096535381 14691885985937953690637)
              ·
                rfl

theorem cell20_289700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 9].length) (baseStart_289700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289700 prefixEnd_289700 := by exact prefixLift 289700
  have htrace : WordTrace (prefixWord ++ tailWord_289700) baseStart_289700 baseEnd_289700 := by
    simpa [prefixWord, tailWord_289700, baseEnd_289700] using wordTrace_append hprefix tailTrace_289700
  have hstable : (prefixWord ++ tailWord_289700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289700).length < 2 ^ (prefixWord ++ tailWord_289700).sum := by decide
  have hdescent : baseEnd_289700 < baseStart_289700 := by decide
  rcases family_descends (prefixWord ++ tailWord_289700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289703 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 5]
def baseStart_289703 : Nat := 118140960795 + 289703 * 2 ^ 59
def prefixEnd_289703 : Nat := 4983230072969 + 3 ^ 40 * 289703 * 2
def baseEnd_289703 : Nat := 132228343155186906115721

theorem tailTrace_289703 : CollatzResearch.WordTrace tailWord_289703 prefixEnd_289703 132228343155186906115721 := by
  unfold tailWord_289703
  simp only [CollatzResearch.WordTrace]
  refine ⟨10566336469462983178417763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7044224312975322118945175 10566336469462983178417763)
  ·
    refine ⟨15849504704194474767626645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10566336469462983178417763 15849504704194474767626645)
    ·
      refine ⟨742945533009116004732499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15849504704194474767626645 742945533009116004732499)
      ·
        refine ⟨1114418299513674007098749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742945533009116004732499 1114418299513674007098749)
        ·
          refine ⟨417906862317627752662031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1114418299513674007098749 417906862317627752662031)
          ·
            refine ⟨626860293476441628993047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417906862317627752662031 626860293476441628993047)
            ·
              refine ⟨940290440214662443489571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626860293476441628993047 940290440214662443489571)
              ·
                refine ⟨1410435660321993665234357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940290440214662443489571 1410435660321993665234357)
                ·
                  refine ⟨132228343155186906115721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1410435660321993665234357 132228343155186906115721)
                  ·
                    rfl

theorem cell20_289703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_289703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289703 prefixEnd_289703 := by exact prefixLift 289703
  have htrace : WordTrace (prefixWord ++ tailWord_289703) baseStart_289703 baseEnd_289703 := by
    simpa [prefixWord, tailWord_289703, baseEnd_289703] using wordTrace_append hprefix tailTrace_289703
  have hstable : (prefixWord ++ tailWord_289703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289703).length < 2 ^ (prefixWord ++ tailWord_289703).sum := by decide
  have hdescent : baseEnd_289703 < baseStart_289703 := by decide
  rcases family_descends (prefixWord ++ tailWord_289703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289707 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_289707 : Nat := 118140960795 + 289707 * 2 ^ 59
def prefixEnd_289707 : Nat := 4983230072969 + 3 ^ 40 * 289707 * 2
def baseEnd_289707 : Nat := 132230168864180669982371

theorem tailTrace_289707 : CollatzResearch.WordTrace tailWord_289707 prefixEnd_289707 132230168864180669982371 := by
  unfold tailWord_289707
  simp only [CollatzResearch.WordTrace]
  refine ⟨10566482361448491861563375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7044321574298994574375583 10566482361448491861563375)
  ·
    refine ⟨15849723542172737792345063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10566482361448491861563375 15849723542172737792345063)
    ·
      refine ⟨23774585313259106688517595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15849723542172737792345063 23774585313259106688517595)
      ·
        refine ⟨35661877969888660032776393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23774585313259106688517595 35661877969888660032776393)
        ·
          refine ⟨26746408477416495024582295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35661877969888660032776393 26746408477416495024582295)
          ·
            refine ⟨40119612716124742536873443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26746408477416495024582295 40119612716124742536873443)
            ·
              refine ⟨60179419074187113805310165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40119612716124742536873443 60179419074187113805310165)
              ·
                refine ⟨1410455134551260479811957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60179419074187113805310165 1410455134551260479811957)
                ·
                  refine ⟨132230168864180669982371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1410455134551260479811957 132230168864180669982371)
                  ·
                    rfl

theorem cell20_289707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_289707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289707 prefixEnd_289707 := by exact prefixLift 289707
  have htrace : WordTrace (prefixWord ++ tailWord_289707) baseStart_289707 baseEnd_289707 := by
    simpa [prefixWord, tailWord_289707, baseEnd_289707] using wordTrace_append hprefix tailTrace_289707
  have hstable : (prefixWord ++ tailWord_289707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289707).length < 2 ^ (prefixWord ++ tailWord_289707).sum := by decide
  have hdescent : baseEnd_289707 < baseStart_289707 := by decide
  rcases family_descends (prefixWord ++ tailWord_289707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289745 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_289745 : Nat := 118140960795 + 289745 * 2 ^ 59
def prefixEnd_289745 : Nat := 4983230072969 + 3 ^ 40 * 289745 * 2
def baseEnd_289745 : Nat := 132247513099621426715549

theorem tailTrace_289745 : CollatzResearch.WordTrace tailWord_289745 prefixEnd_289745 132247513099621426715549 := by
  unfold tailWord_289745
  simp only [CollatzResearch.WordTrace]
  refine ⟨10567868335310824351446689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7045245556873882900964459 10567868335310824351446689)
  ·
    refine ⟨7925901251483118263585017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10567868335310824351446689 7925901251483118263585017)
    ·
      refine ⟨5944425938612338697688763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7925901251483118263585017 5944425938612338697688763)
      ·
        refine ⟨8916638907918508046533145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5944425938612338697688763 8916638907918508046533145)
        ·
          refine ⟨6687479180938881034899859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8916638907918508046533145 6687479180938881034899859)
          ·
            refine ⟨10031218771408321552349789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6687479180938881034899859 10031218771408321552349789)
            ·
              refine ⟨3761707039278120582131171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10031218771408321552349789 3761707039278120582131171)
              ·
                refine ⟨5642560558917180873196757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761707039278120582131171 5642560558917180873196757)
                ·
                  refine ⟨132247513099621426715549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5642560558917180873196757 132247513099621426715549)
                  ·
                    rfl

theorem cell20_289745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_289745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289745 prefixEnd_289745 := by exact prefixLift 289745
  have htrace : WordTrace (prefixWord ++ tailWord_289745) baseStart_289745 baseEnd_289745 := by
    simpa [prefixWord, tailWord_289745, baseEnd_289745] using wordTrace_append hprefix tailTrace_289745
  have hstable : (prefixWord ++ tailWord_289745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289745).length < 2 ^ (prefixWord ++ tailWord_289745).sum := by decide
  have hdescent : baseEnd_289745 < baseStart_289745 := by decide
  rcases family_descends (prefixWord ++ tailWord_289745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289810 : List Nat := [3, 2, 5, 1, 9]
def baseStart_289810 : Nat := 118140960795 + 289810 * 2 ^ 59
def prefixEnd_289810 : Nat := 4983230072969 + 3 ^ 40 * 289810 * 2
def baseEnd_289810 : Nat := 1633051615688519624057

theorem tailTrace_289810 : CollatzResearch.WordTrace tailWord_289810 prefixEnd_289810 1633051615688519624057 := by
  unfold tailWord_289810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642559770018835113140721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7046826053383560301708589 2642559770018835113140721)
  ·
    refine ⟨1981919827514126334855541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2642559770018835113140721 1981919827514126334855541)
    ·
      refine ⟨185804983829449343892707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1981919827514126334855541 185804983829449343892707)
      ·
        refine ⟨278707475744174015839061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185804983829449343892707 278707475744174015839061)
        ·
          refine ⟨1633051615688519624057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 278707475744174015839061 1633051615688519624057)
          ·
            rfl

theorem cell20_289810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 9].length) (baseStart_289810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289810 prefixEnd_289810 := by exact prefixLift 289810
  have htrace : WordTrace (prefixWord ++ tailWord_289810) baseStart_289810 baseEnd_289810 := by
    simpa [prefixWord, tailWord_289810, baseEnd_289810] using wordTrace_append hprefix tailTrace_289810
  have hstable : (prefixWord ++ tailWord_289810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289810).length < 2 ^ (prefixWord ++ tailWord_289810).sum := by decide
  have hdescent : baseEnd_289810 < baseStart_289810 := by decide
  rcases family_descends (prefixWord ++ tailWord_289810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289859 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_289859 : Nat := 118140960795 + 289859 * 2 ^ 59
def prefixEnd_289859 : Nat := 4983230072969 + 3 ^ 40 * 289859 * 2
def baseEnd_289859 : Nat := 132299545805943696915083

theorem tailTrace_289859 : CollatzResearch.WordTrace tailWord_289859 prefixEnd_289859 132299545805943696915083 := by
  unfold tailWord_289859
  simp only [CollatzResearch.WordTrace]
  refine ⟨10572026256897821821096631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7048017504598547880731087 10572026256897821821096631)
  ·
    refine ⟨15858039385346732731644947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10572026256897821821096631 15858039385346732731644947)
    ·
      refine ⟨23787059078020099097467421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15858039385346732731644947 23787059078020099097467421)
      ·
        refine ⟨8920147154257537161550283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23787059078020099097467421 8920147154257537161550283)
        ·
          refine ⟨13380220731386305742325425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8920147154257537161550283 13380220731386305742325425)
          ·
            refine ⟨10035165548539729306744069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13380220731386305742325425 10035165548539729306744069)
            ·
              refine ⟨1881593540351199245014513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10035165548539729306744069 1881593540351199245014513)
              ·
                refine ⟨1411195155263399433760885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881593540351199245014513 1411195155263399433760885)
                ·
                  refine ⟨132299545805943696915083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411195155263399433760885 132299545805943696915083)
                  ·
                    rfl

theorem cell20_289859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_289859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289859 prefixEnd_289859 := by exact prefixLift 289859
  have htrace : WordTrace (prefixWord ++ tailWord_289859) baseStart_289859 baseEnd_289859 := by
    simpa [prefixWord, tailWord_289859, baseEnd_289859] using wordTrace_append hprefix tailTrace_289859
  have hstable : (prefixWord ++ tailWord_289859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289859).length < 2 ^ (prefixWord ++ tailWord_289859).sum := by decide
  have hdescent : baseEnd_289859 < baseStart_289859 := by decide
  rcases family_descends (prefixWord ++ tailWord_289859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289869 : List Nat := [1, 6, 1, 1, 1, 3, 7]
def baseStart_289869 : Nat := 118140960795 + 289869 * 2 ^ 59
def prefixEnd_289869 : Nat := 4983230072969 + 3 ^ 40 * 289869 * 2
def baseEnd_289869 : Nat := 14700456675380900731301

theorem tailTrace_289869 : CollatzResearch.WordTrace tailWord_289869 prefixEnd_289869 14700456675380900731301 := by
  unfold tailWord_289869
  simp only [CollatzResearch.WordTrace]
  refine ⟨10572390986861593528960661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7048260657907729019307107 10572390986861593528960661)
  ·
    refine ⟨495580827509137196670031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10572390986861593528960661 495580827509137196670031)
    ·
      refine ⟨743371241263705795005047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495580827509137196670031 743371241263705795005047)
      ·
        refine ⟨1115056861895558692507571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743371241263705795005047 1115056861895558692507571)
        ·
          refine ⟨1672585292843338038761357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115056861895558692507571 1672585292843338038761357)
          ·
            refine ⟨627219484816251764535509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1672585292843338038761357 627219484816251764535509)
            ·
              refine ⟨14700456675380900731301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 627219484816251764535509 14700456675380900731301)
              ·
                rfl

theorem cell20_289869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_289869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289869 prefixEnd_289869 := by exact prefixLift 289869
  have htrace : WordTrace (prefixWord ++ tailWord_289869) baseStart_289869 baseEnd_289869 := by
    simpa [prefixWord, tailWord_289869, baseEnd_289869] using wordTrace_append hprefix tailTrace_289869
  have hstable : (prefixWord ++ tailWord_289869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289869).length < 2 ^ (prefixWord ++ tailWord_289869).sum := by decide
  have hdescent : baseEnd_289869 < baseStart_289869 := by decide
  rcases family_descends (prefixWord ++ tailWord_289869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289893 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 3]
def baseStart_289893 : Nat := 118140960795 + 289893 * 2 ^ 59
def prefixEnd_289893 : Nat := 4983230072969 + 3 ^ 40 * 289893 * 2
def baseEnd_289893 : Nat := 132315064332390689781611

theorem tailTrace_289893 : CollatzResearch.WordTrace tailWord_289893 prefixEnd_289893 132315064332390689781611 := by
  unfold tailWord_289893
  simp only [CollatzResearch.WordTrace]
  refine ⟨10573266338774645627834333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7048844225849763751889555 10573266338774645627834333)
  ·
    refine ⟨3964974877040492110437875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10573266338774645627834333 3964974877040492110437875)
    ·
      refine ⟨5947462315560738165656813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964974877040492110437875 5947462315560738165656813)
      ·
        refine ⟨2230298368335276812121305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5947462315560738165656813 2230298368335276812121305)
        ·
          refine ⟨1672723776251457609090979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2230298368335276812121305 1672723776251457609090979)
          ·
            refine ⟨2509085664377186413636469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672723776251457609090979 2509085664377186413636469)
            ·
              refine ⟨235226781035361226278419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2509085664377186413636469 235226781035361226278419)
              ·
                refine ⟨352840171553041839417629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235226781035361226278419 352840171553041839417629)
                ·
                  refine ⟨132315064332390689781611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352840171553041839417629 132315064332390689781611)
                  ·
                    rfl

theorem cell20_289893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_289893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289893 prefixEnd_289893 := by exact prefixLift 289893
  have htrace : WordTrace (prefixWord ++ tailWord_289893) baseStart_289893 baseEnd_289893 := by
    simpa [prefixWord, tailWord_289893, baseEnd_289893] using wordTrace_append hprefix tailTrace_289893
  have hstable : (prefixWord ++ tailWord_289893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289893).length < 2 ^ (prefixWord ++ tailWord_289893).sum := by decide
  have hdescent : baseEnd_289893 < baseStart_289893 := by decide
  rcases family_descends (prefixWord ++ tailWord_289893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289934 : List Nat := [4, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_289934 : Nat := 118140960795 + 289934 * 2 ^ 59
def prefixEnd_289934 : Nat := 4983230072969 + 3 ^ 40 * 289934 * 2
def baseEnd_289934 : Nat := 132333777849576769414777

theorem tailTrace_289934 : CollatzResearch.WordTrace tailWord_289934 prefixEnd_289934 132333777849576769414777 := by
  unfold tailWord_289934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321845216453263703759607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7049841154417406420051237 1321845216453263703759607)
  ·
    refine ⟨1982767824679895555639411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1321845216453263703759607 1982767824679895555639411)
    ·
      refine ⟨2974151737019843333459117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982767824679895555639411 2974151737019843333459117)
      ·
        refine ⟨1115306901382441250047169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2974151737019843333459117 1115306901382441250047169)
        ·
          refine ⟨836480176036830937535377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1115306901382441250047169 836480176036830937535377)
          ·
            refine ⟨627360132027623203151533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836480176036830937535377 627360132027623203151533)
            ·
              refine ⟨235260049510358701181825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 627360132027623203151533 235260049510358701181825)
              ·
                refine ⟨176445037132769025886369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235260049510358701181825 176445037132769025886369)
                ·
                  refine ⟨132333777849576769414777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176445037132769025886369 132333777849576769414777)
                  ·
                    rfl

theorem cell20_289934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_289934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289934 prefixEnd_289934 := by exact prefixLift 289934
  have htrace : WordTrace (prefixWord ++ tailWord_289934) baseStart_289934 baseEnd_289934 := by
    simpa [prefixWord, tailWord_289934, baseEnd_289934] using wordTrace_append hprefix tailTrace_289934
  have hstable : (prefixWord ++ tailWord_289934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289934).length < 2 ^ (prefixWord ++ tailWord_289934).sum := by decide
  have hdescent : baseEnd_289934 < baseStart_289934 := by decide
  rcases family_descends (prefixWord ++ tailWord_289934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289938 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_289938 : Nat := 118140960795 + 289938 * 2 ^ 59
def prefixEnd_289938 : Nat := 4983230072969 + 3 ^ 40 * 289938 * 2
def baseEnd_289938 : Nat := 132335603558570533281427

theorem tailTrace_289938 : CollatzResearch.WordTrace tailWord_289938 prefixEnd_289938 132335603558570533281427 := by
  unfold tailWord_289938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643726905902904578305617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7049938415741078875481645 2643726905902904578305617)
  ·
    refine ⟨1982795179427178433729213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2643726905902904578305617 1982795179427178433729213)
    ·
      refine ⟨743548192285191912648455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1982795179427178433729213 743548192285191912648455)
      ·
        refine ⟨1115322288427787868972683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743548192285191912648455 1115322288427787868972683)
        ·
          refine ⟨1672983432641681803459025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115322288427787868972683 1672983432641681803459025)
          ·
            refine ⟨1254737574481261352594269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672983432641681803459025 1254737574481261352594269)
            ·
              refine ⟨470526590430473007222851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1254737574481261352594269 470526590430473007222851)
              ·
                refine ⟨705789885645709510834277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470526590430473007222851 705789885645709510834277)
                ·
                  refine ⟨132335603558570533281427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705789885645709510834277 132335603558570533281427)
                  ·
                    rfl

theorem cell20_289938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_289938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289938 prefixEnd_289938 := by exact prefixLift 289938
  have htrace : WordTrace (prefixWord ++ tailWord_289938) baseStart_289938 baseEnd_289938 := by
    simpa [prefixWord, tailWord_289938, baseEnd_289938] using wordTrace_append hprefix tailTrace_289938
  have hstable : (prefixWord ++ tailWord_289938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289938).length < 2 ^ (prefixWord ++ tailWord_289938).sum := by decide
  have hdescent : baseEnd_289938 < baseStart_289938 := by decide
  rcases family_descends (prefixWord ++ tailWord_289938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289948 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_289948 : Nat := 118140960795 + 289948 * 2 ^ 59
def prefixEnd_289948 : Nat := 4983230072969 + 3 ^ 40 * 289948 * 2
def baseEnd_289948 : Nat := 132340167831054942948053

theorem tailTrace_289948 : CollatzResearch.WordTrace tailWord_289948 prefixEnd_289948 132340167831054942948053 := by
  unfold tailWord_289948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287636176787695010543249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7050181569050260014057665 5287636176787695010543249)
  ·
    refine ⟨3965727132590771257907437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5287636176787695010543249 3965727132590771257907437)
    ·
      refine ⟨1487147674721539221715289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3965727132590771257907437 1487147674721539221715289)
      ·
        refine ⟨1115360756041154416286467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1487147674721539221715289 1115360756041154416286467)
        ·
          refine ⟨1673041134061731624429701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115360756041154416286467 1673041134061731624429701)
          ·
            refine ⟨313695212636574679580569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1673041134061731624429701 313695212636574679580569)
            ·
              refine ⟨235271409477431009685427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313695212636574679580569 235271409477431009685427)
              ·
                refine ⟨352907114216146514528141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235271409477431009685427 352907114216146514528141)
                ·
                  refine ⟨132340167831054942948053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352907114216146514528141 132340167831054942948053)
                  ·
                    rfl

theorem cell20_289948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_289948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289948 prefixEnd_289948 := by exact prefixLift 289948
  have htrace : WordTrace (prefixWord ++ tailWord_289948) baseStart_289948 baseEnd_289948 := by
    simpa [prefixWord, tailWord_289948, baseEnd_289948] using wordTrace_append hprefix tailTrace_289948
  have hstable : (prefixWord ++ tailWord_289948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289948).length < 2 ^ (prefixWord ++ tailWord_289948).sum := by decide
  have hdescent : baseEnd_289948 < baseStart_289948 := by decide
  rcases family_descends (prefixWord ++ tailWord_289948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_289952 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_289952 : Nat := 118140960795 + 289952 * 2 ^ 59
def prefixEnd_289952 : Nat := 4983230072969 + 3 ^ 40 * 289952 * 2
def baseEnd_289952 : Nat := 132341993540048706814703

theorem tailTrace_289952 : CollatzResearch.WordTrace tailWord_289952 prefixEnd_289952 132341993540048706814703 := by
  unfold tailWord_289952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287709122780449352116055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7050278830373932469488073 5287709122780449352116055)
  ·
    refine ⟨7931563684170674028174083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5287709122780449352116055 7931563684170674028174083)
    ·
      refine ⟨11897345526256011042261125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7931563684170674028174083 11897345526256011042261125)
      ·
        refine ⟨2230752286173002070423961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11897345526256011042261125 2230752286173002070423961)
        ·
          refine ⟨1673064214629751552817971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2230752286173002070423961 1673064214629751552817971)
          ·
            refine ⟨2509596321944627329226957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673064214629751552817971 2509596321944627329226957)
            ·
              refine ⟨941098620729235248460109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2509596321944627329226957 941098620729235248460109)
              ·
                refine ⟨352911982773463218172541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 941098620729235248460109 352911982773463218172541)
                ·
                  refine ⟨132341993540048706814703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352911982773463218172541 132341993540048706814703)
                  ·
                    rfl

theorem cell20_289952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_289952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_289952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_289952 prefixEnd_289952 := by exact prefixLift 289952
  have htrace : WordTrace (prefixWord ++ tailWord_289952) baseStart_289952 baseEnd_289952 := by
    simpa [prefixWord, tailWord_289952, baseEnd_289952] using wordTrace_append hprefix tailTrace_289952
  have hstable : (prefixWord ++ tailWord_289952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_289952).length < 2 ^ (prefixWord ++ tailWord_289952).sum := by decide
  have hdescent : baseEnd_289952 < baseStart_289952 := by decide
  rcases family_descends (prefixWord ++ tailWord_289952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290031 : List Nat := [1, 1, 2, 1, 7, 1, 2, 3, 2]
def baseStart_290031 : Nat := 118140960795 + 290031 * 2 ^ 59
def prefixEnd_290031 : Nat := 4983230072969 + 3 ^ 40 * 290031 * 2
def baseEnd_290031 : Nat := 132378051292675543181047

theorem tailTrace_290031 : CollatzResearch.WordTrace tailWord_290031 prefixEnd_290031 132378051292675543181047 := by
  unfold tailWord_290031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10578299612274695196357947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7052199741516463464238631 10578299612274695196357947)
  ·
    refine ⟨15867449418412042794536921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10578299612274695196357947 15867449418412042794536921)
    ·
      refine ⟨11900587063809032095902691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15867449418412042794536921 11900587063809032095902691)
      ·
        refine ⟨17850880595713548143854037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11900587063809032095902691 17850880595713548143854037)
        ·
          refine ⟨418380013962036284621579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17850880595713548143854037 418380013962036284621579)
          ·
            refine ⟨627570020943054426932369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418380013962036284621579 627570020943054426932369)
            ·
              refine ⟨470677515707290820199277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627570020943054426932369 470677515707290820199277)
              ·
                refine ⟨176504068390234057574729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 470677515707290820199277 176504068390234057574729)
                ·
                  refine ⟨132378051292675543181047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176504068390234057574729 132378051292675543181047)
                  ·
                    rfl

theorem cell20_290031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 2].length) (baseStart_290031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290031 prefixEnd_290031 := by exact prefixLift 290031
  have htrace : WordTrace (prefixWord ++ tailWord_290031) baseStart_290031 baseEnd_290031 := by
    simpa [prefixWord, tailWord_290031, baseEnd_290031] using wordTrace_append hprefix tailTrace_290031
  have hstable : (prefixWord ++ tailWord_290031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290031).length < 2 ^ (prefixWord ++ tailWord_290031).sum := by decide
  have hdescent : baseEnd_290031 < baseStart_290031 := by decide
  rcases family_descends (prefixWord ++ tailWord_290031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290052 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_290052 : Nat := 118140960795 + 290052 * 2 ^ 59
def prefixEnd_290052 : Nat := 4983230072969 + 3 ^ 40 * 290052 * 2
def baseEnd_290052 : Nat := 132387636264892803480961

theorem tailTrace_290052 : CollatzResearch.WordTrace tailWord_290052 prefixEnd_290052 132387636264892803480961 := by
  unfold tailWord_290052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289532772599307891436205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7052710363465743855248273 5289532772599307891436205)
  ·
    refine ⟨1983574789724740459288577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5289532772599307891436205 1983574789724740459288577)
    ·
      refine ⟨1487681092293555344466433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1983574789724740459288577 1487681092293555344466433)
      ·
        refine ⟨1115760819220166508349825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1487681092293555344466433 1115760819220166508349825)
        ·
          refine ⟨836820614415124881262369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1115760819220166508349825 836820614415124881262369)
          ·
            refine ⟨627615460811343660946777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836820614415124881262369 627615460811343660946777)
            ·
              refine ⟨470711595608507745710083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627615460811343660946777 470711595608507745710083)
              ·
                refine ⟨706067393412761618565125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470711595608507745710083 706067393412761618565125)
                ·
                  refine ⟨132387636264892803480961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706067393412761618565125 132387636264892803480961)
                  ·
                    rfl

theorem cell20_290052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_290052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290052 prefixEnd_290052 := by exact prefixLift 290052
  have htrace : WordTrace (prefixWord ++ tailWord_290052) baseStart_290052 baseEnd_290052 := by
    simpa [prefixWord, tailWord_290052, baseEnd_290052] using wordTrace_append hprefix tailTrace_290052
  have hstable : (prefixWord ++ tailWord_290052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290052).length < 2 ^ (prefixWord ++ tailWord_290052).sum := by decide
  have hdescent : baseEnd_290052 < baseStart_290052 := by decide
  rcases family_descends (prefixWord ++ tailWord_290052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290111 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_290111 : Nat := 118140960795 + 290111 * 2 ^ 59
def prefixEnd_290111 : Nat := 4983230072969 + 3 ^ 40 * 290111 * 2
def baseEnd_290111 : Nat := 132414565472550820514053

theorem tailTrace_290111 : CollatzResearch.WordTrace tailWord_290111 prefixEnd_290111 132414565472550820514053 := by
  unfold tailWord_290111
  simp only [CollatzResearch.WordTrace]
  refine ⟨10581217451984868859270187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7054144967989912572846791 10581217451984868859270187)
  ·
    refine ⟨15871826177977303288905281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10581217451984868859270187 15871826177977303288905281)
    ·
      refine ⟨11903869633482977466678961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15871826177977303288905281 11903869633482977466678961)
      ·
        refine ⟨8927902225112233100009221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11903869633482977466678961 8927902225112233100009221)
        ·
          refine ⟨1673981667208543706251729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8927902225112233100009221 1673981667208543706251729)
          ·
            refine ⟨1255486250406407779688797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1673981667208543706251729 1255486250406407779688797)
            ·
              refine ⟨470807343902402917383299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1255486250406407779688797 470807343902402917383299)
              ·
                refine ⟨706211015853604376074949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470807343902402917383299 706211015853604376074949)
                ·
                  refine ⟨132414565472550820514053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706211015853604376074949 132414565472550820514053)
                  ·
                    rfl

theorem cell20_290111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_290111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290111 prefixEnd_290111 := by exact prefixLift 290111
  have htrace : WordTrace (prefixWord ++ tailWord_290111) baseStart_290111 baseEnd_290111 := by
    simpa [prefixWord, tailWord_290111, baseEnd_290111] using wordTrace_append hprefix tailTrace_290111
  have hstable : (prefixWord ++ tailWord_290111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290111).length < 2 ^ (prefixWord ++ tailWord_290111).sum := by decide
  have hdescent : baseEnd_290111 < baseStart_290111 := by decide
  rcases family_descends (prefixWord ++ tailWord_290111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290158 : List Nat := [4, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_290158 : Nat := 118140960795 + 290158 * 2 ^ 59
def prefixEnd_290158 : Nat := 4983230072969 + 3 ^ 40 * 290158 * 2
def baseEnd_290158 : Nat := 132436017553227545947195

theorem tailTrace_290158 : CollatzResearch.WordTrace tailWord_290158 prefixEnd_290158 132436017553227545947195 := by
  unfold tailWord_290158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322866460351824485778891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7055287788543063924154085 1322866460351824485778891)
  ·
    refine ⟨1984299690527736728668337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322866460351824485778891 1984299690527736728668337)
    ·
      refine ⟨1488224767895802546501253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1984299690527736728668337 1488224767895802546501253)
      ·
        refine ⟨279042143980462977468985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1488224767895802546501253 279042143980462977468985)
        ·
          refine ⟨209281607985347233101739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279042143980462977468985 209281607985347233101739)
          ·
            refine ⟨313922411978020849652609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209281607985347233101739 313922411978020849652609)
            ·
              refine ⟨235441808983515637239457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313922411978020849652609 235441808983515637239457)
              ·
                refine ⟨176581356737636727929593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235441808983515637239457 176581356737636727929593)
                ·
                  refine ⟨132436017553227545947195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176581356737636727929593 132436017553227545947195)
                  ·
                    rfl

theorem cell20_290158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_290158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290158 prefixEnd_290158 := by exact prefixLift 290158
  have htrace : WordTrace (prefixWord ++ tailWord_290158) baseStart_290158 baseEnd_290158 := by
    simpa [prefixWord, tailWord_290158, baseEnd_290158] using wordTrace_append hprefix tailTrace_290158
  have hstable : (prefixWord ++ tailWord_290158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290158).length < 2 ^ (prefixWord ++ tailWord_290158).sum := by decide
  have hdescent : baseEnd_290158 < baseStart_290158 := by decide
  rcases family_descends (prefixWord ++ tailWord_290158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290180 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_290180 : Nat := 118140960795 + 290180 * 2 ^ 59
def prefixEnd_290180 : Nat := 4983230072969 + 3 ^ 40 * 290180 * 2
def baseEnd_290180 : Nat := 132446058952693247213771

theorem tailTrace_290180 : CollatzResearch.WordTrace tailWord_290180 prefixEnd_290180 132446058952693247213771 := by
  unfold tailWord_290180
  simp only [CollatzResearch.WordTrace]
  refine ⟨5291867044367446821765997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7055822725823262429021329 5291867044367446821765997)
  ·
    refine ⟨1984450141637792558162249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5291867044367446821765997 1984450141637792558162249)
    ·
      refine ⟨1488337606228344418621687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1984450141637792558162249 1488337606228344418621687)
      ·
        refine ⟨2232506409342516627932531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488337606228344418621687 2232506409342516627932531)
        ·
          refine ⟨3348759614013774941898797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232506409342516627932531 3348759614013774941898797)
          ·
            refine ⟨1255784855255165603212049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3348759614013774941898797 1255784855255165603212049)
            ·
              refine ⟨941838641441374202409037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255784855255165603212049 941838641441374202409037)
              ·
                refine ⟨353189490540515325903389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 941838641441374202409037 353189490540515325903389)
                ·
                  refine ⟨132446058952693247213771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353189490540515325903389 132446058952693247213771)
                  ·
                    rfl

theorem cell20_290180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_290180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290180 prefixEnd_290180 := by exact prefixLift 290180
  have htrace : WordTrace (prefixWord ++ tailWord_290180) baseStart_290180 baseEnd_290180 := by
    simpa [prefixWord, tailWord_290180, baseEnd_290180] using wordTrace_append hprefix tailTrace_290180
  have hstable : (prefixWord ++ tailWord_290180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290180).length < 2 ^ (prefixWord ++ tailWord_290180).sum := by decide
  have hdescent : baseEnd_290180 < baseStart_290180 := by decide
  rcases family_descends (prefixWord ++ tailWord_290180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290190 : List Nat := [4, 1, 1, 4, 2, 1, 3, 4]
def baseStart_290190 : Nat := 118140960795 + 290190 * 2 ^ 59
def prefixEnd_290190 : Nat := 4983230072969 + 3 ^ 40 * 290190 * 2
def baseEnd_290190 : Nat := 44150207741725885626799

theorem tailTrace_290190 : CollatzResearch.WordTrace tailWord_290190 prefixEnd_290190 44150207741725885626799 := by
  unfold tailWord_290190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323012352337333168924503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7056065879132443567597349 1323012352337333168924503)
  ·
    refine ⟨1984518528505999753386755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323012352337333168924503 1984518528505999753386755)
    ·
      refine ⟨2976777792758999630080133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984518528505999753386755 2976777792758999630080133)
      ·
        refine ⟨558145836142312430640025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2976777792758999630080133 558145836142312430640025)
        ·
          refine ⟨418609377106734322980019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558145836142312430640025 418609377106734322980019)
          ·
            refine ⟨627914065660101484470029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418609377106734322980019 627914065660101484470029)
            ·
              refine ⟨235467774622538056676261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 627914065660101484470029 235467774622538056676261)
              ·
                refine ⟨44150207741725885626799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235467774622538056676261 44150207741725885626799)
                ·
                  rfl

theorem cell20_290190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_290190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290190 prefixEnd_290190 := by exact prefixLift 290190
  have htrace : WordTrace (prefixWord ++ tailWord_290190) baseStart_290190 baseEnd_290190 := by
    simpa [prefixWord, tailWord_290190, baseEnd_290190] using wordTrace_append hprefix tailTrace_290190
  have hstable : (prefixWord ++ tailWord_290190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290190).length < 2 ^ (prefixWord ++ tailWord_290190).sum := by decide
  have hdescent : baseEnd_290190 < baseStart_290190 := by decide
  rcases family_descends (prefixWord ++ tailWord_290190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290208 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_290208 : Nat := 118140960795 + 290208 * 2 ^ 59
def prefixEnd_290208 : Nat := 4983230072969 + 3 ^ 40 * 290208 * 2
def baseEnd_290208 : Nat := 132458838915649594280323

theorem tailTrace_290208 : CollatzResearch.WordTrace tailWord_290208 prefixEnd_290208 132458838915649594280323 := by
  unfold tailWord_290208
  simp only [CollatzResearch.WordTrace]
  refine ⟨5292377666316727212775639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7056503555088969617034185 5292377666316727212775639)
  ·
    refine ⟨7938566499475090819163459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5292377666316727212775639 7938566499475090819163459)
    ·
      refine ⟨11907849749212636228745189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7938566499475090819163459 11907849749212636228745189)
      ·
        refine ⟨2232721827977369292889723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11907849749212636228745189 2232721827977369292889723)
        ·
          refine ⟨3349082741966053939334585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232721827977369292889723 3349082741966053939334585)
          ·
            refine ⟨2511812056474540454500939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3349082741966053939334585 2511812056474540454500939)
            ·
              refine ⟨3767718084711810681751409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511812056474540454500939 3767718084711810681751409)
              ·
                refine ⟨2825788563533858011313557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3767718084711810681751409 2825788563533858011313557)
                ·
                  refine ⟨132458838915649594280323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2825788563533858011313557 132458838915649594280323)
                  ·
                    rfl

theorem cell20_290208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_290208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290208 prefixEnd_290208 := by exact prefixLift 290208
  have htrace : WordTrace (prefixWord ++ tailWord_290208) baseStart_290208 baseEnd_290208 := by
    simpa [prefixWord, tailWord_290208, baseEnd_290208] using wordTrace_append hprefix tailTrace_290208
  have hstable : (prefixWord ++ tailWord_290208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290208).length < 2 ^ (prefixWord ++ tailWord_290208).sum := by decide
  have hdescent : baseEnd_290208 < baseStart_290208 := by decide
  rcases family_descends (prefixWord ++ tailWord_290208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290221 : List Nat := [1, 5, 2, 2, 1, 1, 2, 4, 2]
def baseStart_290221 : Nat := 118140960795 + 290221 * 2 ^ 59
def prefixEnd_290221 : Nat := 4983230072969 + 3 ^ 40 * 290221 * 2
def baseEnd_290221 : Nat := 132464772469879326846937

theorem tailTrace_290221 : CollatzResearch.WordTrace tailWord_290221 prefixEnd_290221 132464772469879326846937 := by
  unfold tailWord_290221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585229481586357645774517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7056819654390905097183011 10585229481586357645774517)
  ·
    refine ⟨992365263898721029291361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10585229481586357645774517 992365263898721029291361)
    ·
      refine ⟨744273947924040771968521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 992365263898721029291361 744273947924040771968521)
      ·
        refine ⟨558205460943030578976391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 744273947924040771968521 558205460943030578976391)
        ·
          refine ⟨837308191414545868464587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558205460943030578976391 837308191414545868464587)
          ·
            refine ⟨1255962287121818802696881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837308191414545868464587 1255962287121818802696881)
            ·
              refine ⟨941971715341364102022661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255962287121818802696881 941971715341364102022661)
              ·
                refine ⟨176619696626505769129249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 941971715341364102022661 176619696626505769129249)
                ·
                  refine ⟨132464772469879326846937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176619696626505769129249 132464772469879326846937)
                  ·
                    rfl

theorem cell20_290221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_290221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290221 prefixEnd_290221 := by exact prefixLift 290221
  have htrace : WordTrace (prefixWord ++ tailWord_290221) baseStart_290221 baseEnd_290221 := by
    simpa [prefixWord, tailWord_290221, baseEnd_290221] using wordTrace_append hprefix tailTrace_290221
  have hstable : (prefixWord ++ tailWord_290221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290221).length < 2 ^ (prefixWord ++ tailWord_290221).sum := by decide
  have hdescent : baseEnd_290221 < baseStart_290221 := by decide
  rcases family_descends (prefixWord ++ tailWord_290221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290225 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_290225 : Nat := 118140960795 + 290225 * 2 ^ 59
def prefixEnd_290225 : Nat := 4983230072969 + 3 ^ 40 * 290225 * 2
def baseEnd_290225 : Nat := 132466598178873090713587

theorem tailTrace_290225 : CollatzResearch.WordTrace tailWord_290225 prefixEnd_290225 132466598178873090713587 := by
  unfold tailWord_290225
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585375373571866328920129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7056916915714577552613419 10585375373571866328920129)
  ·
    refine ⟨7939031530178899746690097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10585375373571866328920129 7939031530178899746690097)
    ·
      refine ⟨5954273647634174810017573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7939031530178899746690097 5954273647634174810017573)
      ·
        refine ⟨1116426308931407776878295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5954273647634174810017573 1116426308931407776878295)
        ·
          refine ⟨1674639463397111665317443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116426308931407776878295 1674639463397111665317443)
          ·
            refine ⟨2511959195095667497976165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674639463397111665317443 2511959195095667497976165)
            ·
              refine ⟨470992349080437655870531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2511959195095667497976165 470992349080437655870531)
              ·
                refine ⟨706488523620656483805797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470992349080437655870531 706488523620656483805797)
                ·
                  refine ⟨132466598178873090713587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706488523620656483805797 132466598178873090713587)
                  ·
                    rfl

theorem cell20_290225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_290225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290225 prefixEnd_290225 := by exact prefixLift 290225
  have htrace : WordTrace (prefixWord ++ tailWord_290225) baseStart_290225 baseEnd_290225 := by
    simpa [prefixWord, tailWord_290225, baseEnd_290225] using wordTrace_append hprefix tailTrace_290225
  have hstable : (prefixWord ++ tailWord_290225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290225).length < 2 ^ (prefixWord ++ tailWord_290225).sum := by decide
  have hdescent : baseEnd_290225 < baseStart_290225 := by decide
  rcases family_descends (prefixWord ++ tailWord_290225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290239 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 3]
def baseStart_290239 : Nat := 118140960795 + 290239 * 2 ^ 59
def prefixEnd_290239 : Nat := 4983230072969 + 3 ^ 40 * 290239 * 2
def baseEnd_290239 : Nat := 132472988160351264246863

theorem tailTrace_290239 : CollatzResearch.WordTrace tailWord_290239 prefixEnd_290239 132472988160351264246863 := by
  unfold tailWord_290239
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585885995521146719929771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7057257330347431146619847 10585885995521146719929771)
  ·
    refine ⟨15878828993281720079894657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10585885995521146719929771 15878828993281720079894657)
    ·
      refine ⟨11909121744961290059920993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15878828993281720079894657 11909121744961290059920993)
      ·
        refine ⟨8931841308720967544940745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11909121744961290059920993 8931841308720967544940745)
        ·
          refine ⟨6698880981540725658705559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8931841308720967544940745 6698880981540725658705559)
          ·
            refine ⟨10048321472311088488058339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698880981540725658705559 10048321472311088488058339)
            ·
              refine ⟨15072482208466632732087509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10048321472311088488058339 15072482208466632732087509)
              ·
                refine ⟨353261301760936704658301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15072482208466632732087509 353261301760936704658301)
                ·
                  refine ⟨132472988160351264246863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353261301760936704658301 132472988160351264246863)
                  ·
                    rfl

theorem cell20_290239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_290239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290239 prefixEnd_290239 := by exact prefixLift 290239
  have htrace : WordTrace (prefixWord ++ tailWord_290239) baseStart_290239 baseEnd_290239 := by
    simpa [prefixWord, tailWord_290239, baseEnd_290239] using wordTrace_append hprefix tailTrace_290239
  have hstable : (prefixWord ++ tailWord_290239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290239).length < 2 ^ (prefixWord ++ tailWord_290239).sum := by decide
  have hdescent : baseEnd_290239 < baseStart_290239 := by decide
  rcases family_descends (prefixWord ++ tailWord_290239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290284 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_290284 : Nat := 118140960795 + 290284 * 2 ^ 59
def prefixEnd_290284 : Nat := 4983230072969 + 3 ^ 40 * 290284 * 2
def baseEnd_290284 : Nat := 132493527386531107746679

theorem tailTrace_290284 : CollatzResearch.WordTrace tailWord_290284 prefixEnd_290284 132493527386531107746679 := by
  unfold tailWord_290284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293763640179059702658953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7058351520238746270211937 5293763640179059702658953)
  ·
    refine ⟨3970322730134294776994215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5293763640179059702658953 3970322730134294776994215)
    ·
      refine ⟨5955484095201442165491323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970322730134294776994215 5955484095201442165491323)
      ·
        refine ⟨8933226142802163248236985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5955484095201442165491323 8933226142802163248236985)
        ·
          refine ⟨6699919607101622436177739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8933226142802163248236985 6699919607101622436177739)
          ·
            refine ⟨10049879410652433654266609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6699919607101622436177739 10049879410652433654266609)
            ·
              refine ⟨7537409557989325240699957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10049879410652433654266609 7537409557989325240699957)
              ·
                refine ⟨706632146061499241315621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7537409557989325240699957 706632146061499241315621)
                ·
                  refine ⟨132493527386531107746679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706632146061499241315621 132493527386531107746679)
                  ·
                    rfl

theorem cell20_290284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_290284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290284 prefixEnd_290284 := by exact prefixLift 290284
  have htrace : WordTrace (prefixWord ++ tailWord_290284) baseStart_290284 baseEnd_290284 := by
    simpa [prefixWord, tailWord_290284, baseEnd_290284] using wordTrace_append hprefix tailTrace_290284
  have hstable : (prefixWord ++ tailWord_290284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290284).length < 2 ^ (prefixWord ++ tailWord_290284).sum := by decide
  have hdescent : baseEnd_290284 < baseStart_290284 := by decide
  rcases family_descends (prefixWord ++ tailWord_290284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290290 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_290290 : Nat := 118140960795 + 290290 * 2 ^ 59
def prefixEnd_290290 : Nat := 4983230072969 + 3 ^ 40 * 290290 * 2
def baseEnd_290290 : Nat := 132496265950021753546655

theorem tailTrace_290290 : CollatzResearch.WordTrace tailWord_290290 prefixEnd_290290 132496265950021753546655 := by
  unfold tailWord_290290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646936529584095607509081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7058497412224254953357549 2646936529584095607509081)
  ·
    refine ⟨1985202397188071705631811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2646936529584095607509081 1985202397188071705631811)
    ·
      refine ⟨2977803595782107558447717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1985202397188071705631811 2977803595782107558447717)
      ·
        refine ⟨558338174209145167208947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2977803595782107558447717 558338174209145167208947)
        ·
          refine ⟨837507261313717750813421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558338174209145167208947 837507261313717750813421)
          ·
            refine ⟨314065222992644156555033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 837507261313717750813421 314065222992644156555033)
            ·
              refine ⟨235548917244483117416275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314065222992644156555033 235548917244483117416275)
              ·
                refine ⟨353323375866724676124413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235548917244483117416275 353323375866724676124413)
                ·
                  refine ⟨132496265950021753546655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353323375866724676124413 132496265950021753546655)
                  ·
                    rfl

theorem cell20_290290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_290290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290290 prefixEnd_290290 := by exact prefixLift 290290
  have htrace : WordTrace (prefixWord ++ tailWord_290290) baseStart_290290 baseEnd_290290 := by
    simpa [prefixWord, tailWord_290290, baseEnd_290290] using wordTrace_append hprefix tailTrace_290290
  have hstable : (prefixWord ++ tailWord_290290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290290).length < 2 ^ (prefixWord ++ tailWord_290290).sum := by decide
  have hdescent : baseEnd_290290 < baseStart_290290 := by decide
  rcases family_descends (prefixWord ++ tailWord_290290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290332 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_290332 : Nat := 118140960795 + 290332 * 2 ^ 59
def prefixEnd_290332 : Nat := 4983230072969 + 3 ^ 40 * 290332 * 2
def baseEnd_290332 : Nat := 132515435894456274146483

theorem tailTrace_290332 : CollatzResearch.WordTrace tailWord_290332 prefixEnd_290332 132515435894456274146483 := by
  unfold tailWord_290332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294638992092111801532625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7059518656122815735376833 5294638992092111801532625)
  ·
    refine ⟨3970979244069083851149469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5294638992092111801532625 3970979244069083851149469)
    ·
      refine ⟨1489117216525906444181051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3970979244069083851149469 1489117216525906444181051)
      ·
        refine ⟨2233675824788859666271577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489117216525906444181051 2233675824788859666271577)
        ·
          refine ⟨1675256868591644749703683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2233675824788859666271577 1675256868591644749703683)
          ·
            refine ⟨2512885302887467124555525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675256868591644749703683 2512885302887467124555525)
            ·
              refine ⟨471165994291400085854161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2512885302887467124555525 471165994291400085854161)
              ·
                refine ⟨353374495718550064390621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471165994291400085854161 353374495718550064390621)
                ·
                  refine ⟨132515435894456274146483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353374495718550064390621 132515435894456274146483)
                  ·
                    rfl

theorem cell20_290332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_290332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290332 prefixEnd_290332 := by exact prefixLift 290332
  have htrace : WordTrace (prefixWord ++ tailWord_290332) baseStart_290332 baseEnd_290332 := by
    simpa [prefixWord, tailWord_290332, baseEnd_290332] using wordTrace_append hprefix tailTrace_290332
  have hstable : (prefixWord ++ tailWord_290332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290332).length < 2 ^ (prefixWord ++ tailWord_290332).sum := by decide
  have hdescent : baseEnd_290332 < baseStart_290332 := by decide
  rcases family_descends (prefixWord ++ tailWord_290332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290360 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_290360 : Nat := 118140960795 + 290360 * 2 ^ 59
def prefixEnd_290360 : Nat := 4983230072969 + 3 ^ 40 * 290360 * 2
def baseEnd_290360 : Nat := 132528215857412621213035

theorem tailTrace_290360 : CollatzResearch.WordTrace tailWord_290360 prefixEnd_290360 132528215857412621213035 := by
  unfold tailWord_290360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5295149614041392192542267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7060199485388522923389689 5295149614041392192542267)
  ·
    refine ⟨7942724421062088288813401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5295149614041392192542267 7942724421062088288813401)
    ·
      refine ⟨5957043315796566216610051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7942724421062088288813401 5957043315796566216610051)
      ·
        refine ⟨8935564973694849324915077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5957043315796566216610051 8935564973694849324915077)
        ·
          refine ⟨1675418432567784248421577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8935564973694849324915077 1675418432567784248421577)
          ·
            refine ⟨1256563824425838186316183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1675418432567784248421577 1256563824425838186316183)
            ·
              refine ⟨1884845736638757279474275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256563824425838186316183 1884845736638757279474275)
              ·
                refine ⟨2827268604958135919211413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884845736638757279474275 2827268604958135919211413)
                ·
                  refine ⟨132528215857412621213035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2827268604958135919211413 132528215857412621213035)
                  ·
                    rfl

theorem cell20_290360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_290360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290360 prefixEnd_290360 := by exact prefixLift 290360
  have htrace : WordTrace (prefixWord ++ tailWord_290360) baseStart_290360 baseEnd_290360 := by
    simpa [prefixWord, tailWord_290360, baseEnd_290360] using wordTrace_append hprefix tailTrace_290360
  have hstable : (prefixWord ++ tailWord_290360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290360).length < 2 ^ (prefixWord ++ tailWord_290360).sum := by decide
  have hdescent : baseEnd_290360 < baseStart_290360 := by decide
  rcases family_descends (prefixWord ++ tailWord_290360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290390 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_290390 : Nat := 118140960795 + 290390 * 2 ^ 59
def prefixEnd_290390 : Nat := 4983230072969 + 3 ^ 40 * 290390 * 2
def baseEnd_290390 : Nat := 132541908674865850212913

theorem tailTrace_290390 : CollatzResearch.WordTrace tailWord_290390 prefixEnd_290390 132541908674865850212913 := by
  unfold tailWord_290390
  simp only [CollatzResearch.WordTrace]
  refine ⟨661962088623381219292289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7060928945316066339117749 661962088623381219292289)
  ·
    refine ⟨496471566467535914469217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 661962088623381219292289 496471566467535914469217)
    ·
      refine ⟨372353674850651935851913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 496471566467535914469217 372353674850651935851913)
      ·
        refine ⟨279265256137988951888935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372353674850651935851913 279265256137988951888935)
        ·
          refine ⟨418897884206983427833403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279265256137988951888935 418897884206983427833403)
          ·
            refine ⟨628346826310475141750105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418897884206983427833403 628346826310475141750105)
            ·
              refine ⟨471260119732856356312579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628346826310475141750105 471260119732856356312579)
              ·
                refine ⟨706890179599284534468869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471260119732856356312579 706890179599284534468869)
                ·
                  refine ⟨132541908674865850212913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706890179599284534468869 132541908674865850212913)
                  ·
                    rfl

theorem cell20_290390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_290390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290390 prefixEnd_290390 := by exact prefixLift 290390
  have htrace : WordTrace (prefixWord ++ tailWord_290390) baseStart_290390 baseEnd_290390 := by
    simpa [prefixWord, tailWord_290390, baseEnd_290390] using wordTrace_append hprefix tailTrace_290390
  have hstable : (prefixWord ++ tailWord_290390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290390).length < 2 ^ (prefixWord ++ tailWord_290390).sum := by decide
  have hdescent : baseEnd_290390 < baseStart_290390 := by decide
  rcases family_descends (prefixWord ++ tailWord_290390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290391 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_290391 : Nat := 118140960795 + 290391 * 2 ^ 59
def prefixEnd_290391 : Nat := 4983230072969 + 3 ^ 40 * 290391 * 2
def baseEnd_290391 : Nat := 132542365102114291179575

theorem tailTrace_290391 : CollatzResearch.WordTrace tailWord_290391 prefixEnd_290391 132542365102114291179575 := by
  unfold tailWord_290391
  simp only [CollatzResearch.WordTrace]
  refine ⟨10591429890970476679463027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7060953260646984452975351 10591429890970476679463027)
  ·
    refine ⟨15887144836455715019194541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10591429890970476679463027 15887144836455715019194541)
    ·
      refine ⟨5957679313670893132197953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15887144836455715019194541 5957679313670893132197953)
      ·
        refine ⟨4468259485253169849148465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5957679313670893132197953 4468259485253169849148465)
        ·
          refine ⟨3351194613939877386861349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4468259485253169849148465 3351194613939877386861349)
          ·
            refine ⟨628348990113727010036503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3351194613939877386861349 628348990113727010036503)
            ·
              refine ⟨942523485170590515054755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628348990113727010036503 942523485170590515054755)
              ·
                refine ⟨1413785227755885772582133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942523485170590515054755 1413785227755885772582133)
                ·
                  refine ⟨132542365102114291179575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1413785227755885772582133 132542365102114291179575)
                  ·
                    rfl

theorem cell20_290391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_290391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290391 prefixEnd_290391 := by exact prefixLift 290391
  have htrace : WordTrace (prefixWord ++ tailWord_290391) baseStart_290391 baseEnd_290391 := by
    simpa [prefixWord, tailWord_290391, baseEnd_290391] using wordTrace_append hprefix tailTrace_290391
  have hstable : (prefixWord ++ tailWord_290391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290391).length < 2 ^ (prefixWord ++ tailWord_290391).sum := by decide
  have hdescent : baseEnd_290391 < baseStart_290391 := by decide
  rcases family_descends (prefixWord ++ tailWord_290391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290429 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_290429 : Nat := 118140960795 + 290429 * 2 ^ 59
def prefixEnd_290429 : Nat := 4983230072969 + 3 ^ 40 * 290429 * 2
def baseEnd_290429 : Nat := 132559709337555047912753

theorem tailTrace_290429 : CollatzResearch.WordTrace tailWord_290429 prefixEnd_290429 132559709337555047912753 := by
  unfold tailWord_290429
  simp only [CollatzResearch.WordTrace]
  refine ⟨10592815864832809169346341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7061877243221872779564227 10592815864832809169346341)
  ·
    refine ⟨1986152974656151719252439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10592815864832809169346341 1986152974656151719252439)
    ·
      refine ⟨2979229461984227578878659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1986152974656151719252439 2979229461984227578878659)
      ·
        refine ⟨4468844192976341368317989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979229461984227578878659 4468844192976341368317989)
        ·
          refine ⟨837908286183064006559623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4468844192976341368317989 837908286183064006559623)
          ·
            refine ⟨1256862429274596009839435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837908286183064006559623 1256862429274596009839435)
            ·
              refine ⟨1885293643911894014759153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256862429274596009839435 1885293643911894014759153)
              ·
                refine ⟨1413970232933920511069365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885293643911894014759153 1413970232933920511069365)
                ·
                  refine ⟨132559709337555047912753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1413970232933920511069365 132559709337555047912753)
                  ·
                    rfl

theorem cell20_290429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_290429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290429 prefixEnd_290429 := by exact prefixLift 290429
  have htrace : WordTrace (prefixWord ++ tailWord_290429) baseStart_290429 baseEnd_290429 := by
    simpa [prefixWord, tailWord_290429, baseEnd_290429] using wordTrace_append hprefix tailTrace_290429
  have hstable : (prefixWord ++ tailWord_290429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290429).length < 2 ^ (prefixWord ++ tailWord_290429).sum := by decide
  have hdescent : baseEnd_290429 < baseStart_290429 := by decide
  rcases family_descends (prefixWord ++ tailWord_290429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290453 : List Nat := [1, 3, 2, 1, 1, 1, 1, 8, 2]
def baseStart_290453 : Nat := 118140960795 + 290453 * 2 ^ 59
def prefixEnd_290453 : Nat := 4983230072969 + 3 ^ 40 * 290453 * 2
def baseEnd_290453 : Nat := 132570663591517631112655

theorem tailTrace_290453 : CollatzResearch.WordTrace tailWord_290453 prefixEnd_290453 132570663591517631112655 := by
  unfold tailWord_290453
  simp only [CollatzResearch.WordTrace]
  refine ⟨10593691216745861268220013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7062460811163907512146675 10593691216745861268220013)
  ·
    refine ⟨3972634206279697975582505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10593691216745861268220013 3972634206279697975582505)
    ·
      refine ⟨2979475654709773481686879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3972634206279697975582505 2979475654709773481686879)
      ·
        refine ⟨4469213482064660222530319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979475654709773481686879 4469213482064660222530319)
        ·
          refine ⟨6703820223096990333795479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4469213482064660222530319 6703820223096990333795479)
          ·
            refine ⟨10055730334645485500693219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703820223096990333795479 10055730334645485500693219)
            ·
              refine ⟨15083595501968228251039829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10055730334645485500693219 15083595501968228251039829)
              ·
                refine ⟨176760884788690174816873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 15083595501968228251039829 176760884788690174816873)
                ·
                  refine ⟨132570663591517631112655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176760884788690174816873 132570663591517631112655)
                  ·
                    rfl

theorem cell20_290453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_290453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290453 prefixEnd_290453 := by exact prefixLift 290453
  have htrace : WordTrace (prefixWord ++ tailWord_290453) baseStart_290453 baseEnd_290453 := by
    simpa [prefixWord, tailWord_290453, baseEnd_290453] using wordTrace_append hprefix tailTrace_290453
  have hstable : (prefixWord ++ tailWord_290453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290453).length < 2 ^ (prefixWord ++ tailWord_290453).sum := by decide
  have hdescent : baseEnd_290453 < baseStart_290453 := by decide
  rcases family_descends (prefixWord ++ tailWord_290453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290463 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 3]
def baseStart_290463 : Nat := 118140960795 + 290463 * 2 ^ 59
def prefixEnd_290463 : Nat := 4983230072969 + 3 ^ 40 * 290463 * 2
def baseEnd_290463 : Nat := 132575227864002040779281

theorem tailTrace_290463 : CollatzResearch.WordTrace tailWord_290463 prefixEnd_290463 132575227864002040779281 := by
  unfold tailWord_290463
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594055946709632976084043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7062703964473088650722695 10594055946709632976084043)
  ·
    refine ⟨15891083920064449464126065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10594055946709632976084043 15891083920064449464126065)
    ·
      refine ⟨11918312940048337098094549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15891083920064449464126065 11918312940048337098094549)
      ·
        refine ⟨279335459532382900736591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11918312940048337098094549 279335459532382900736591)
        ·
          refine ⟨419003189298574351104887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279335459532382900736591 419003189298574351104887)
          ·
            refine ⟨628504783947861526657331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419003189298574351104887 628504783947861526657331)
            ·
              refine ⟨942757175921792289985997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628504783947861526657331 942757175921792289985997)
              ·
                refine ⟨353533940970672108744749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942757175921792289985997 353533940970672108744749)
                ·
                  refine ⟨132575227864002040779281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353533940970672108744749 132575227864002040779281)
                  ·
                    rfl

theorem cell20_290463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_290463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290463 prefixEnd_290463 := by exact prefixLift 290463
  have htrace : WordTrace (prefixWord ++ tailWord_290463) baseStart_290463 baseEnd_290463 := by
    simpa [prefixWord, tailWord_290463, baseEnd_290463] using wordTrace_append hprefix tailTrace_290463
  have hstable : (prefixWord ++ tailWord_290463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290463).length < 2 ^ (prefixWord ++ tailWord_290463).sum := by decide
  have hdescent : baseEnd_290463 < baseStart_290463 := by decide
  rcases family_descends (prefixWord ++ tailWord_290463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290467 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 3]
def baseStart_290467 : Nat := 118140960795 + 290467 * 2 ^ 59
def prefixEnd_290467 : Nat := 4983230072969 + 3 ^ 40 * 290467 * 2
def baseEnd_290467 : Nat := 132577053572995804645931

theorem tailTrace_290467 : CollatzResearch.WordTrace tailWord_290467 prefixEnd_290467 132577053572995804645931 := by
  unfold tailWord_290467
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594201838695141659229655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7062801225796761106153103 10594201838695141659229655)
  ·
    refine ⟨15891302758042712488844483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10594201838695141659229655 15891302758042712488844483)
    ·
      refine ⟨23836954137064068733266725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15891302758042712488844483 23836954137064068733266725)
      ·
        refine ⟨4469428900699512887487511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23836954137064068733266725 4469428900699512887487511)
        ·
          refine ⟨6704143351049269331231267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4469428900699512887487511 6704143351049269331231267)
          ·
            refine ⟨10056215026573903996846901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6704143351049269331231267 10056215026573903996846901)
            ·
              refine ⟨942770158741303499704397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10056215026573903996846901 942770158741303499704397)
              ·
                refine ⟨353538809527988812389149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942770158741303499704397 353538809527988812389149)
                ·
                  refine ⟨132577053572995804645931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353538809527988812389149 132577053572995804645931)
                  ·
                    rfl

theorem cell20_290467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_290467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290467 prefixEnd_290467 := by exact prefixLift 290467
  have htrace : WordTrace (prefixWord ++ tailWord_290467) baseStart_290467 baseEnd_290467 := by
    simpa [prefixWord, tailWord_290467, baseEnd_290467] using wordTrace_append hprefix tailTrace_290467
  have hstable : (prefixWord ++ tailWord_290467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290467).length < 2 ^ (prefixWord ++ tailWord_290467).sum := by decide
  have hdescent : baseEnd_290467 < baseStart_290467 := by decide
  rcases family_descends (prefixWord ++ tailWord_290467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290488 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_290488 : Nat := 118140960795 + 290488 * 2 ^ 59
def prefixEnd_290488 : Nat := 4983230072969 + 3 ^ 40 * 290488 * 2
def baseEnd_290488 : Nat := 132586638545213064945845

theorem tailTrace_290488 : CollatzResearch.WordTrace tailWord_290488 prefixEnd_290488 132586638545213064945845 := by
  unfold tailWord_290488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5297483885809531122872059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7063311847746041497162745 5297483885809531122872059)
  ·
    refine ⟨7946225828714296684308089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5297483885809531122872059 7946225828714296684308089)
    ·
      refine ⟨5959669371535722513231067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7946225828714296684308089 5959669371535722513231067)
      ·
        refine ⟨8939504057303583769846601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5959669371535722513231067 8939504057303583769846601)
        ·
          refine ⟨6704628042977687827384951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8939504057303583769846601 6704628042977687827384951)
          ·
            refine ⟨10056942064466531741077427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6704628042977687827384951 10056942064466531741077427)
            ·
              refine ⟨15085413096699797611616141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10056942064466531741077427 15085413096699797611616141)
              ·
                refine ⟨5657029911262424104356053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15085413096699797611616141 5657029911262424104356053)
                ·
                  refine ⟨132586638545213064945845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5657029911262424104356053 132586638545213064945845)
                  ·
                    rfl

theorem cell20_290488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_290488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290488 prefixEnd_290488 := by exact prefixLift 290488
  have htrace : WordTrace (prefixWord ++ tailWord_290488) baseStart_290488 baseEnd_290488 := by
    simpa [prefixWord, tailWord_290488, baseEnd_290488] using wordTrace_append hprefix tailTrace_290488
  have hstable : (prefixWord ++ tailWord_290488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290488).length < 2 ^ (prefixWord ++ tailWord_290488).sum := by decide
  have hdescent : baseEnd_290488 < baseStart_290488 := by decide
  rcases family_descends (prefixWord ++ tailWord_290488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290529 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 4]
def baseStart_290529 : Nat := 118140960795 + 290529 * 2 ^ 59
def prefixEnd_290529 : Nat := 4983230072969 + 3 ^ 40 * 290529 * 2
def baseEnd_290529 : Nat := 132605352062399144579011

theorem tailTrace_290529 : CollatzResearch.WordTrace tailWord_290529 prefixEnd_290529 132605352062399144579011 := by
  unfold tailWord_290529
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596463164470526247986641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7064308776313684165324427 10596463164470526247986641)
  ·
    refine ⟨7947347373352894685989981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10596463164470526247986641 7947347373352894685989981)
    ·
      refine ⟨2980255265007335507246243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7947347373352894685989981 2980255265007335507246243)
      ·
        refine ⟨4470382897511003260869365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2980255265007335507246243 4470382897511003260869365)
        ·
          refine ⟨419098396641656555706503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4470382897511003260869365 419098396641656555706503)
          ·
            refine ⟨628647594962484833559755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419098396641656555706503 628647594962484833559755)
            ·
              refine ⟨942971392443727250339633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628647594962484833559755 942971392443727250339633)
              ·
                refine ⟨707228544332795437754725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942971392443727250339633 707228544332795437754725)
                ·
                  refine ⟨132605352062399144579011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707228544332795437754725 132605352062399144579011)
                  ·
                    rfl

theorem cell20_290529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_290529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290529 prefixEnd_290529 := by exact prefixLift 290529
  have htrace : WordTrace (prefixWord ++ tailWord_290529) baseStart_290529 baseEnd_290529 := by
    simpa [prefixWord, tailWord_290529, baseEnd_290529] using wordTrace_append hprefix tailTrace_290529
  have hstable : (prefixWord ++ tailWord_290529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290529).length < 2 ^ (prefixWord ++ tailWord_290529).sum := by decide
  have hdescent : baseEnd_290529 < baseStart_290529 := by decide
  rcases family_descends (prefixWord ++ tailWord_290529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290546 : List Nat := [3, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_290546 : Nat := 118140960795 + 290546 * 2 ^ 59
def prefixEnd_290546 : Nat := 4983230072969 + 3 ^ 40 * 290546 * 2
def baseEnd_290546 : Nat := 132613111325622641012275

theorem tailTrace_290546 : CollatzResearch.WordTrace tailWord_290546 prefixEnd_290546 132613111325622641012275 := by
  unfold tailWord_290546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649270801352234537838873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7064722136939292100903661 2649270801352234537838873)
  ·
    refine ⟨1986953101014175903379155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2649270801352234537838873 1986953101014175903379155)
    ·
      refine ⟨2980429651521263855068733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1986953101014175903379155 2980429651521263855068733)
      ·
        refine ⟨1117661119320473945650775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2980429651521263855068733 1117661119320473945650775)
        ·
          refine ⟨1676491678980710918476163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117661119320473945650775 1676491678980710918476163)
          ·
            refine ⟨2514737518471066377714245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676491678980710918476163 2514737518471066377714245)
            ·
              refine ⟨471513284713324945821421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2514737518471066377714245 471513284713324945821421)
              ·
                refine ⟨176817481767496854683033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 471513284713324945821421 176817481767496854683033)
                ·
                  refine ⟨132613111325622641012275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176817481767496854683033 132613111325622641012275)
                  ·
                    rfl

theorem cell20_290546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_290546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290546 prefixEnd_290546 := by exact prefixLift 290546
  have htrace : WordTrace (prefixWord ++ tailWord_290546) baseStart_290546 baseEnd_290546 := by
    simpa [prefixWord, tailWord_290546, baseEnd_290546] using wordTrace_append hprefix tailTrace_290546
  have hstable : (prefixWord ++ tailWord_290546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290546).length < 2 ^ (prefixWord ++ tailWord_290546).sum := by decide
  have hdescent : baseEnd_290546 < baseStart_290546 := by decide
  rcases family_descends (prefixWord ++ tailWord_290546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290588 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_290588 : Nat := 118140960795 + 290588 * 2 ^ 59
def prefixEnd_290588 : Nat := 4983230072969 + 3 ^ 40 * 290588 * 2
def baseEnd_290588 : Nat := 132632281270057161612103

theorem tailTrace_290588 : CollatzResearch.WordTrace tailWord_290588 prefixEnd_290588 132632281270057161612103 := by
  unfold tailWord_290588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299307535628389662192209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7065743380837852882922945 5299307535628389662192209)
  ·
    refine ⟨3974480651721292246644157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5299307535628389662192209 3974480651721292246644157)
    ·
      refine ⟨1490430244395484592491559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3974480651721292246644157 1490430244395484592491559)
      ·
        refine ⟨2235645366593226888737339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490430244395484592491559 2235645366593226888737339)
        ·
          refine ⟨3353468049889840333106009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235645366593226888737339 3353468049889840333106009)
          ·
            refine ⟨2515101037417380249829507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3353468049889840333106009 2515101037417380249829507)
            ·
              refine ⟨3772651556126070374744261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515101037417380249829507 3772651556126070374744261)
              ·
                refine ⟨707372166773638195264549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3772651556126070374744261 707372166773638195264549)
                ·
                  refine ⟨132632281270057161612103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707372166773638195264549 132632281270057161612103)
                  ·
                    rfl

theorem cell20_290588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_290588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290588 prefixEnd_290588 := by exact prefixLift 290588
  have htrace : WordTrace (prefixWord ++ tailWord_290588) baseStart_290588 baseEnd_290588 := by
    simpa [prefixWord, tailWord_290588, baseEnd_290588] using wordTrace_append hprefix tailTrace_290588
  have hstable : (prefixWord ++ tailWord_290588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290588).length < 2 ^ (prefixWord ++ tailWord_290588).sum := by decide
  have hdescent : baseEnd_290588 < baseStart_290588 := by decide
  rcases family_descends (prefixWord ++ tailWord_290588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290612 : List Nat := [2, 5, 1, 1, 2, 1, 8]
def baseStart_290612 : Nat := 118140960795 + 290612 * 2 ^ 59
def prefixEnd_290612 : Nat := 4983230072969 + 3 ^ 40 * 290612 * 2
def baseEnd_290612 : Nat := 14738137280446638312445

theorem tailTrace_290612 : CollatzResearch.WordTrace tailWord_290612 prefixEnd_290612 14738137280446638312445 := by
  unfold tailWord_290612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299745211584915711629045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7066326948779887615505393 5299745211584915711629045)
  ·
    refine ⟨496851113586085847965223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5299745211584915711629045 496851113586085847965223)
    ·
      refine ⟨745276670379128771947835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496851113586085847965223 745276670379128771947835)
      ·
        refine ⟨1117915005568693157921753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745276670379128771947835 1117915005568693157921753)
        ·
          refine ⟨838436254176519868441315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117915005568693157921753 838436254176519868441315)
          ·
            refine ⟨1257654381264779802661973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838436254176519868441315 1257654381264779802661973)
            ·
              refine ⟨14738137280446638312445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1257654381264779802661973 14738137280446638312445)
              ·
                rfl

theorem cell20_290612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 8].length) (baseStart_290612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290612 prefixEnd_290612 := by exact prefixLift 290612
  have htrace : WordTrace (prefixWord ++ tailWord_290612) baseStart_290612 baseEnd_290612 := by
    simpa [prefixWord, tailWord_290612, baseEnd_290612] using wordTrace_append hprefix tailTrace_290612
  have hstable : (prefixWord ++ tailWord_290612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290612).length < 2 ^ (prefixWord ++ tailWord_290612).sum := by decide
  have hdescent : baseEnd_290612 < baseStart_290612 := by decide
  rcases family_descends (prefixWord ++ tailWord_290612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290622 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_290622 : Nat := 118140960795 + 290622 * 2 ^ 59
def prefixEnd_290622 : Nat := 4983230072969 + 3 ^ 40 * 290622 * 2
def baseEnd_290622 : Nat := 132647799796504154478631

theorem tailTrace_290622 : CollatzResearch.WordTrace tailWord_290622 prefixEnd_290622 132647799796504154478631 := by
  unfold tailWord_290622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324981894141700391390265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7066570102089068754081413 1324981894141700391390265)
  ·
    refine ⟨993736420606275293542699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1324981894141700391390265 993736420606275293542699)
    ·
      refine ⟨1490604630909412940314049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993736420606275293542699 1490604630909412940314049)
      ·
        refine ⟨1117953473182059705235537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1490604630909412940314049 1117953473182059705235537)
        ·
          refine ⟨838465104886544778926653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117953473182059705235537 838465104886544778926653)
          ·
            refine ⟨314424414332454292097495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 838465104886544778926653 314424414332454292097495)
            ·
              refine ⟨471636621498681438146243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314424414332454292097495 471636621498681438146243)
              ·
                refine ⟨707454932248022157219365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471636621498681438146243 707454932248022157219365)
                ·
                  refine ⟨132647799796504154478631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707454932248022157219365 132647799796504154478631)
                  ·
                    rfl

theorem cell20_290622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_290622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290622 prefixEnd_290622 := by exact prefixLift 290622
  have htrace : WordTrace (prefixWord ++ tailWord_290622) baseStart_290622 baseEnd_290622 := by
    simpa [prefixWord, tailWord_290622, baseEnd_290622] using wordTrace_append hprefix tailTrace_290622
  have hstable : (prefixWord ++ tailWord_290622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290622).length < 2 ^ (prefixWord ++ tailWord_290622).sum := by decide
  have hdescent : baseEnd_290622 < baseStart_290622 := by decide
  rcases family_descends (prefixWord ++ tailWord_290622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290633 : List Nat := [1, 2, 1, 1, 2, 4, 4, 5]
def baseStart_290633 : Nat := 118140960795 + 290633 * 2 ^ 59
def prefixEnd_290633 : Nat := 4983230072969 + 3 ^ 40 * 290633 * 2
def baseEnd_290633 : Nat := 44217606832079001703973

theorem tailTrace_290633 : CollatzResearch.WordTrace tailWord_290633 prefixEnd_290633 44217606832079001703973 := by
  unfold tailWord_290633
  simp only [CollatzResearch.WordTrace]
  refine ⟨10600256356093752009772553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7066837570729168006515035 10600256356093752009772553)
  ·
    refine ⟨7950192267070314007329415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10600256356093752009772553 7950192267070314007329415)
    ·
      refine ⟨11925288400605471010994123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7950192267070314007329415 11925288400605471010994123)
      ·
        refine ⟨17887932600908206516491185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11925288400605471010994123 17887932600908206516491185)
        ·
          refine ⟨13415949450681154887368389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17887932600908206516491185 13415949450681154887368389)
          ·
            refine ⟨2515490522002716541381573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13415949450681154887368389 2515490522002716541381573)
            ·
              refine ⟨471654472875509351509045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2515490522002716541381573 471654472875509351509045)
              ·
                refine ⟨44217606832079001703973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 471654472875509351509045 44217606832079001703973)
                ·
                  rfl

theorem cell20_290633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_290633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290633 prefixEnd_290633 := by exact prefixLift 290633
  have htrace : WordTrace (prefixWord ++ tailWord_290633) baseStart_290633 baseEnd_290633 := by
    simpa [prefixWord, tailWord_290633, baseEnd_290633] using wordTrace_append hprefix tailTrace_290633
  have hstable : (prefixWord ++ tailWord_290633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290633).length < 2 ^ (prefixWord ++ tailWord_290633).sum := by decide
  have hdescent : baseEnd_290633 < baseStart_290633 := by decide
  rcases family_descends (prefixWord ++ tailWord_290633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290636 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_290636 : Nat := 118140960795 + 290636 * 2 ^ 59
def prefixEnd_290636 : Nat := 4983230072969 + 3 ^ 40 * 290636 * 2
def baseEnd_290636 : Nat := 132654189777982328011907

theorem tailTrace_290636 : CollatzResearch.WordTrace tailWord_290636 prefixEnd_290636 132654189777982328011907 := by
  unfold tailWord_290636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300182887541441761065881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7066910516721922348087841 5300182887541441761065881)
  ·
    refine ⟨3975137165656081320799411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5300182887541441761065881 3975137165656081320799411)
    ·
      refine ⟨5962705748484121981199117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975137165656081320799411 5962705748484121981199117)
      ·
        refine ⟨2236014655681545742949669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5962705748484121981199117 2236014655681545742949669)
        ·
          refine ⟨419252747940289826803063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2236014655681545742949669 419252747940289826803063)
          ·
            refine ⟨628879121910434740204595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419252747940289826803063 628879121910434740204595)
            ·
              refine ⟨943318682865652110306893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628879121910434740204595 943318682865652110306893)
              ·
                refine ⟨353744506074619541365085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 943318682865652110306893 353744506074619541365085)
                ·
                  refine ⟨132654189777982328011907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353744506074619541365085 132654189777982328011907)
                  ·
                    rfl

theorem cell20_290636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_290636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290636 prefixEnd_290636 := by exact prefixLift 290636
  have htrace : WordTrace (prefixWord ++ tailWord_290636) baseStart_290636 baseEnd_290636 := by
    simpa [prefixWord, tailWord_290636, baseEnd_290636] using wordTrace_append hprefix tailTrace_290636
  have hstable : (prefixWord ++ tailWord_290636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290636).length < 2 ^ (prefixWord ++ tailWord_290636).sum := by decide
  have hdescent : baseEnd_290636 < baseStart_290636 := by decide
  rcases family_descends (prefixWord ++ tailWord_290636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290681 : List Nat := [1, 2, 1, 3, 2, 2, 3, 4, 2]
def baseStart_290681 : Nat := 118140960795 + 290681 * 2 ^ 59
def prefixEnd_290681 : Nat := 4983230072969 + 3 ^ 40 * 290681 * 2
def baseEnd_290681 : Nat := 132674729004162171511723

theorem tailTrace_290681 : CollatzResearch.WordTrace tailWord_290681 prefixEnd_290681 132674729004162171511723 := by
  unfold tailWord_290681
  simp only [CollatzResearch.WordTrace]
  refine ⟨10602007059919856207519897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7068004706613237471679931 10602007059919856207519897)
  ·
    refine ⟨7951505294939892155639923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10602007059919856207519897 7951505294939892155639923)
    ·
      refine ⟨11927257942409838233459885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7951505294939892155639923 11927257942409838233459885)
      ·
        refine ⟨4472721728403689337547457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11927257942409838233459885 4472721728403689337547457)
        ·
          refine ⟨3354541296302767003160593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4472721728403689337547457 3354541296302767003160593)
          ·
            refine ⟨2515905972227075252370445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3354541296302767003160593 2515905972227075252370445)
            ·
              refine ⟨943464739585153219638917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2515905972227075252370445 943464739585153219638917)
              ·
                refine ⟨176899638672216228682297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 943464739585153219638917 176899638672216228682297)
                ·
                  refine ⟨132674729004162171511723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176899638672216228682297 132674729004162171511723)
                  ·
                    rfl

theorem cell20_290681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_290681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290681 prefixEnd_290681 := by exact prefixLift 290681
  have htrace : WordTrace (prefixWord ++ tailWord_290681) baseStart_290681 baseEnd_290681 := by
    simpa [prefixWord, tailWord_290681, baseEnd_290681] using wordTrace_append hprefix tailTrace_290681
  have hstable : (prefixWord ++ tailWord_290681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290681).length < 2 ^ (prefixWord ++ tailWord_290681).sum := by decide
  have hdescent : baseEnd_290681 < baseStart_290681 := by decide
  rcases family_descends (prefixWord ++ tailWord_290681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290723 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_290723 : Nat := 118140960795 + 290723 * 2 ^ 59
def prefixEnd_290723 : Nat := 4983230072969 + 3 ^ 40 * 290723 * 2
def baseEnd_290723 : Nat := 132693898948596692111551

theorem tailTrace_290723 : CollatzResearch.WordTrace tailWord_290723 prefixEnd_290723 132693898948596692111551 := by
  unfold tailWord_290723
  simp only [CollatzResearch.WordTrace]
  refine ⟨10603538925767697380548823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7069025950511798253699215 10603538925767697380548823)
  ·
    refine ⟨15905308388651546070823235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10603538925767697380548823 15905308388651546070823235)
    ·
      refine ⟨23857962582977319106234853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15905308388651546070823235 23857962582977319106234853)
      ·
        refine ⟨4473367984308247332419035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23857962582977319106234853 4473367984308247332419035)
        ·
          refine ⟨6710051976462370998628553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4473367984308247332419035 6710051976462370998628553)
          ·
            refine ⟨5032538982346778248971415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6710051976462370998628553 5032538982346778248971415)
            ·
              refine ⟨7548808473520167373457123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5032538982346778248971415 7548808473520167373457123)
              ·
                refine ⟨11323212710280251060185685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7548808473520167373457123 11323212710280251060185685)
                ·
                  refine ⟨132693898948596692111551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11323212710280251060185685 132693898948596692111551)
                  ·
                    rfl

theorem cell20_290723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_290723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290723 prefixEnd_290723 := by exact prefixLift 290723
  have htrace : WordTrace (prefixWord ++ tailWord_290723) baseStart_290723 baseEnd_290723 := by
    simpa [prefixWord, tailWord_290723, baseEnd_290723] using wordTrace_append hprefix tailTrace_290723
  have hstable : (prefixWord ++ tailWord_290723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290723).length < 2 ^ (prefixWord ++ tailWord_290723).sum := by decide
  have hdescent : baseEnd_290723 < baseStart_290723 := by decide
  rcases family_descends (prefixWord ++ tailWord_290723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290764 : List Nat := [2, 2, 1, 4, 1, 2, 4, 4]
def baseStart_290764 : Nat := 118140960795 + 290764 * 2 ^ 59
def prefixEnd_290764 : Nat := 4983230072969 + 3 ^ 40 * 290764 * 2
def baseEnd_290764 : Nat := 44237537488594257248239

theorem tailTrace_290764 : CollatzResearch.WordTrace tailWord_290764 prefixEnd_290764 44237537488594257248239 := by
  unfold tailWord_290764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5302517159309580691395673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7070022879079440921860897 5302517159309580691395673)
  ·
    refine ⟨3976887869482185518546755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5302517159309580691395673 3976887869482185518546755)
    ·
      refine ⟨5965331804223278277820133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3976887869482185518546755 5965331804223278277820133)
      ·
        refine ⟨1118499713291864677091275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5965331804223278277820133 1118499713291864677091275)
        ·
          refine ⟨1677749569937797015636913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118499713291864677091275 1677749569937797015636913)
          ·
            refine ⟨1258312177453347761727685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1677749569937797015636913 1258312177453347761727685)
            ·
              refine ⟨235933533272502705323941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1258312177453347761727685 235933533272502705323941)
              ·
                refine ⟨44237537488594257248239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235933533272502705323941 44237537488594257248239)
                ·
                  rfl

theorem cell20_290764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_290764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290764 prefixEnd_290764 := by exact prefixLift 290764
  have htrace : WordTrace (prefixWord ++ tailWord_290764) baseStart_290764 baseEnd_290764 := by
    simpa [prefixWord, tailWord_290764, baseEnd_290764] using wordTrace_append hprefix tailTrace_290764
  have hstable : (prefixWord ++ tailWord_290764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290764).length < 2 ^ (prefixWord ++ tailWord_290764).sum := by decide
  have hdescent : baseEnd_290764 < baseStart_290764 := by decide
  rcases family_descends (prefixWord ++ tailWord_290764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290770 : List Nat := [3, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_290770 : Nat := 118140960795 + 290770 * 2 ^ 59
def prefixEnd_290770 : Nat := 4983230072969 + 3 ^ 40 * 290770 * 2
def baseEnd_290770 : Nat := 132715351029273417544693

theorem tailTrace_290770 : CollatzResearch.WordTrace tailWord_290770 prefixEnd_290770 132715351029273417544693 := by
  unfold tailWord_290770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651313289149356101877441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7070168771064949605006509 2651313289149356101877441)
  ·
    refine ⟨1988484966862017076408081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2651313289149356101877441 1988484966862017076408081)
    ·
      refine ⟨1491363725146512807306061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1988484966862017076408081 1491363725146512807306061)
      ·
        refine ⟨559261396929942302739773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1491363725146512807306061 559261396929942302739773)
        ·
          refine ⟨209723023848728363527415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 559261396929942302739773 209723023848728363527415)
          ·
            refine ⟨314584535773092545291123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209723023848728363527415 314584535773092545291123)
            ·
              refine ⟨471876803659638817936685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314584535773092545291123 471876803659638817936685)
              ·
                refine ⟨176953801372364556726257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 471876803659638817936685 176953801372364556726257)
                ·
                  refine ⟨132715351029273417544693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176953801372364556726257 132715351029273417544693)
                  ·
                    rfl

theorem cell20_290770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_290770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290770 prefixEnd_290770 := by exact prefixLift 290770
  have htrace : WordTrace (prefixWord ++ tailWord_290770) baseStart_290770 baseEnd_290770 := by
    simpa [prefixWord, tailWord_290770, baseEnd_290770] using wordTrace_append hprefix tailTrace_290770
  have hstable : (prefixWord ++ tailWord_290770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290770).length < 2 ^ (prefixWord ++ tailWord_290770).sum := by decide
  have hdescent : baseEnd_290770 < baseStart_290770 := by decide
  rcases family_descends (prefixWord ++ tailWord_290770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290781 : List Nat := [1, 4, 3, 1, 4, 1, 6]
def baseStart_290781 : Nat := 118140960795 + 290781 * 2 ^ 59
def prefixEnd_290781 : Nat := 4983230072969 + 3 ^ 40 * 290781 * 2
def baseEnd_290781 : Nat := 14746707969889585353109

theorem tailTrace_290781 : CollatzResearch.WordTrace tailWord_290781 prefixEnd_290781 14746707969889585353109 := by
  unfold tailWord_290781
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605654359557573286160197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7070436239705048857440131 10605654359557573286160197)
  ·
    refine ⟨1988560192417044991155037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10605654359557573286160197 1988560192417044991155037)
    ·
      refine ⟨745710072156391871683139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1988560192417044991155037 745710072156391871683139)
      ·
        refine ⟨1118565108234587807524709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745710072156391871683139 1118565108234587807524709)
        ·
          refine ⟨209730957793985213910883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1118565108234587807524709 209730957793985213910883)
          ·
            refine ⟨314596436690977820866325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209730957793985213910883 314596436690977820866325)
            ·
              refine ⟨14746707969889585353109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 314596436690977820866325 14746707969889585353109)
              ·
                rfl

theorem cell20_290781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 6].length) (baseStart_290781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290781 prefixEnd_290781 := by exact prefixLift 290781
  have htrace : WordTrace (prefixWord ++ tailWord_290781) baseStart_290781 baseEnd_290781 := by
    simpa [prefixWord, tailWord_290781, baseEnd_290781] using wordTrace_append hprefix tailTrace_290781
  have hstable : (prefixWord ++ tailWord_290781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290781).length < 2 ^ (prefixWord ++ tailWord_290781).sum := by decide
  have hdescent : baseEnd_290781 < baseStart_290781 := by decide
  rcases family_descends (prefixWord ++ tailWord_290781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290791 : List Nat := [1, 1, 5, 2, 3, 1, 3, 2, 2]
def baseStart_290791 : Nat := 118140960795 + 290791 * 2 ^ 59
def prefixEnd_290791 : Nat := 4983230072969 + 3 ^ 40 * 290791 * 2
def baseEnd_290791 : Nat := 132724936001490677844607

theorem tailTrace_290791 : CollatzResearch.WordTrace tailWord_290791 prefixEnd_290791 132724936001490677844607 := by
  unfold tailWord_290791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10606019089521344994024227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7070679393014229996016151 10606019089521344994024227)
  ·
    refine ⟨15909028634282017491036341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10606019089521344994024227 15909028634282017491036341)
    ·
      refine ⟨1491471434463939139784657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15909028634282017491036341 1491471434463939139784657)
      ·
        refine ⟨1118603575847954354838493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1491471434463939139784657 1118603575847954354838493)
        ·
          refine ⟨419476340942982883064435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1118603575847954354838493 419476340942982883064435)
          ·
            refine ⟨629214511414474324596653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419476340942982883064435 629214511414474324596653)
            ·
              refine ⟨235955441780427871723745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 629214511414474324596653 235955441780427871723745)
              ·
                refine ⟨176966581335320903792809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235955441780427871723745 176966581335320903792809)
                ·
                  refine ⟨132724936001490677844607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176966581335320903792809 132724936001490677844607)
                  ·
                    rfl

theorem cell20_290791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 2].length) (baseStart_290791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290791 prefixEnd_290791 := by exact prefixLift 290791
  have htrace : WordTrace (prefixWord ++ tailWord_290791) baseStart_290791 baseEnd_290791 := by
    simpa [prefixWord, tailWord_290791, baseEnd_290791] using wordTrace_append hprefix tailTrace_290791
  have hstable : (prefixWord ++ tailWord_290791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290791).length < 2 ^ (prefixWord ++ tailWord_290791).sum := by decide
  have hdescent : baseEnd_290791 < baseStart_290791 := by decide
  rcases family_descends (prefixWord ++ tailWord_290791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290809 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 3]
def baseStart_290809 : Nat := 118140960795 + 290809 * 2 ^ 59
def prefixEnd_290809 : Nat := 4983230072969 + 3 ^ 40 * 290809 * 2
def baseEnd_290809 : Nat := 132733151691962615244533

theorem tailTrace_290809 : CollatzResearch.WordTrace tailWord_290809 prefixEnd_290809 132733151691962615244533 := by
  unfold tailWord_290809
  simp only [CollatzResearch.WordTrace]
  refine ⟨10606675603456134068179481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7071117068970756045452987 10606675603456134068179481)
  ·
    refine ⟨7955006702592100551134611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10606675603456134068179481 7955006702592100551134611)
    ·
      refine ⟨11932510053888150826701917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7955006702592100551134611 11932510053888150826701917)
      ·
        refine ⟨4474691270208056560013219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11932510053888150826701917 4474691270208056560013219)
        ·
          refine ⟨6712036905312084840019829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4474691270208056560013219 6712036905312084840019829)
          ·
            refine ⟨629253459873007953751859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6712036905312084840019829 629253459873007953751859)
            ·
              refine ⟨943880189809511930627789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629253459873007953751859 943880189809511930627789)
              ·
                refine ⟨353955071178566973985421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 943880189809511930627789 353955071178566973985421)
                ·
                  refine ⟨132733151691962615244533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353955071178566973985421 132733151691962615244533)
                  ·
                    rfl

theorem cell20_290809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_290809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290809 prefixEnd_290809 := by exact prefixLift 290809
  have htrace : WordTrace (prefixWord ++ tailWord_290809) baseStart_290809 baseEnd_290809 := by
    simpa [prefixWord, tailWord_290809, baseEnd_290809] using wordTrace_append hprefix tailTrace_290809
  have hstable : (prefixWord ++ tailWord_290809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290809).length < 2 ^ (prefixWord ++ tailWord_290809).sum := by decide
  have hdescent : baseEnd_290809 < baseStart_290809 := by decide
  rcases family_descends (prefixWord ++ tailWord_290809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290823 : List Nat := [1, 1, 4, 3, 1, 2, 2, 6]
def baseStart_290823 : Nat := 118140960795 + 290823 * 2 ^ 59
def prefixEnd_290823 : Nat := 4983230072969 + 3 ^ 40 * 290823 * 2
def baseEnd_290823 : Nat := 44246513891146929592603

theorem tailTrace_290823 : CollatzResearch.WordTrace tailWord_290823 prefixEnd_290823 44246513891146929592603 := by
  unfold tailWord_290823
  simp only [CollatzResearch.WordTrace]
  refine ⟨10607186225405414459189123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7071457483603609639459415 10607186225405414459189123)
  ·
    refine ⟨15910779338108121688783685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10607186225405414459189123 15910779338108121688783685)
    ·
      refine ⟨2983271125895272816646941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15910779338108121688783685 2983271125895272816646941)
      ·
        refine ⟨1118726672210727306242603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2983271125895272816646941 1118726672210727306242603)
        ·
          refine ⟨1678090008316090959363905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118726672210727306242603 1678090008316090959363905)
          ·
            refine ⟨1258567506237068219522929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678090008316090959363905 1258567506237068219522929)
            ·
              refine ⟨943925629677801164642197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258567506237068219522929 943925629677801164642197)
              ·
                refine ⟨44246513891146929592603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 943925629677801164642197 44246513891146929592603)
                ·
                  rfl

theorem cell20_290823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_290823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290823 prefixEnd_290823 := by exact prefixLift 290823
  have htrace : WordTrace (prefixWord ++ tailWord_290823) baseStart_290823 baseEnd_290823 := by
    simpa [prefixWord, tailWord_290823, baseEnd_290823] using wordTrace_append hprefix tailTrace_290823
  have hstable : (prefixWord ++ tailWord_290823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290823).length < 2 ^ (prefixWord ++ tailWord_290823).sum := by decide
  have hdescent : baseEnd_290823 < baseStart_290823 := by decide
  rcases family_descends (prefixWord ++ tailWord_290823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290847 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 3]
def baseStart_290847 : Nat := 118140960795 + 290847 * 2 ^ 59
def prefixEnd_290847 : Nat := 4983230072969 + 3 ^ 40 * 290847 * 2
def baseEnd_290847 : Nat := 132750495927403371977711

theorem tailTrace_290847 : CollatzResearch.WordTrace tailWord_290847 prefixEnd_290847 132750495927403371977711 := by
  unfold tailWord_290847
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608061577318466558062795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7072041051545644372041863 10608061577318466558062795)
  ·
    refine ⟨15912092365977699837094193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608061577318466558062795 15912092365977699837094193)
    ·
      refine ⟨11934069274483274877820645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15912092365977699837094193 11934069274483274877820645)
      ·
        refine ⟨2237637988965614039591371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11934069274483274877820645 2237637988965614039591371)
        ·
          refine ⟨3356456983448421059387057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237637988965614039591371 3356456983448421059387057)
          ·
            refine ⟨2517342737586315794540293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356456983448421059387057 2517342737586315794540293)
            ·
              refine ⟨472001763297434211476305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2517342737586315794540293 472001763297434211476305)
              ·
                refine ⟨354001322473075658607229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472001763297434211476305 354001322473075658607229)
                ·
                  refine ⟨132750495927403371977711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354001322473075658607229 132750495927403371977711)
                  ·
                    rfl

theorem cell20_290847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_290847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290847 prefixEnd_290847 := by exact prefixLift 290847
  have htrace : WordTrace (prefixWord ++ tailWord_290847) baseStart_290847 baseEnd_290847 := by
    simpa [prefixWord, tailWord_290847, baseEnd_290847] using wordTrace_append hprefix tailTrace_290847
  have hstable : (prefixWord ++ tailWord_290847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290847).length < 2 ^ (prefixWord ++ tailWord_290847).sum := by decide
  have hdescent : baseEnd_290847 < baseStart_290847 := by decide
  rcases family_descends (prefixWord ++ tailWord_290847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290875 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_290875 : Nat := 118140960795 + 290875 * 2 ^ 59
def prefixEnd_290875 : Nat := 4983230072969 + 3 ^ 40 * 290875 * 2
def baseEnd_290875 : Nat := 132763275890359719044263

theorem tailTrace_290875 : CollatzResearch.WordTrace tailWord_290875 prefixEnd_290875 132763275890359719044263 := by
  unfold tailWord_290875
  simp only [CollatzResearch.WordTrace]
  refine ⟨10609082821217027340082079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7072721880811351560054719 10609082821217027340082079)
  ·
    refine ⟨15913624231825541010123119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10609082821217027340082079 15913624231825541010123119)
    ·
      refine ⟨23870436347738311515184679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15913624231825541010123119 23870436347738311515184679)
      ·
        refine ⟨35805654521607467272777019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23870436347738311515184679 35805654521607467272777019)
        ·
          refine ⟨53708481782411200909165529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35805654521607467272777019 53708481782411200909165529)
          ·
            refine ⟨40281361336808400681874147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53708481782411200909165529 40281361336808400681874147)
            ·
              refine ⟨60422042005212601022811221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40281361336808400681874147 60422042005212601022811221)
              ·
                refine ⟨708070804748585168236069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 60422042005212601022811221 708070804748585168236069)
                ·
                  refine ⟨132763275890359719044263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708070804748585168236069 132763275890359719044263)
                  ·
                    rfl

theorem cell20_290875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_290875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290875 prefixEnd_290875 := by exact prefixLift 290875
  have htrace : WordTrace (prefixWord ++ tailWord_290875) baseStart_290875 baseEnd_290875 := by
    simpa [prefixWord, tailWord_290875, baseEnd_290875] using wordTrace_append hprefix tailTrace_290875
  have hstable : (prefixWord ++ tailWord_290875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290875).length < 2 ^ (prefixWord ++ tailWord_290875).sum := by decide
  have hdescent : baseEnd_290875 < baseStart_290875 := by decide
  rcases family_descends (prefixWord ++ tailWord_290875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290906 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_290906 : Nat := 118140960795 + 290906 * 2 ^ 59
def prefixEnd_290906 : Nat := 4983230072969 + 3 ^ 40 * 290906 * 2
def baseEnd_290906 : Nat := 132777425135061389010803

theorem tailTrace_290906 : CollatzResearch.WordTrace tailWord_290906 prefixEnd_290906 132777425135061389010803 := by
  unfold tailWord_290906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652553371026179908615143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7073475656069813089640381 2652553371026179908615143)
  ·
    refine ⟨3978830056539269862922715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2652553371026179908615143 3978830056539269862922715)
    ·
      refine ⟨5968245084808904794384073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3978830056539269862922715 5968245084808904794384073)
      ·
        refine ⟨4476183813606678595788055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5968245084808904794384073 4476183813606678595788055)
        ·
          refine ⟨6714275720410017893682083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476183813606678595788055 6714275720410017893682083)
          ·
            refine ⟨10071413580615026840523125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6714275720410017893682083 10071413580615026840523125)
            ·
              refine ⟨944195023182658766299043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10071413580615026840523125 944195023182658766299043)
              ·
                refine ⟨1416292534773988149448565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944195023182658766299043 1416292534773988149448565)
                ·
                  refine ⟨132777425135061389010803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1416292534773988149448565 132777425135061389010803)
                  ·
                    rfl

theorem cell20_290906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_290906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290906 prefixEnd_290906 := by exact prefixLift 290906
  have htrace : WordTrace (prefixWord ++ tailWord_290906) baseStart_290906 baseEnd_290906 := by
    simpa [prefixWord, tailWord_290906, baseEnd_290906] using wordTrace_append hprefix tailTrace_290906
  have hstable : (prefixWord ++ tailWord_290906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290906).length < 2 ^ (prefixWord ++ tailWord_290906).sum := by decide
  have hdescent : baseEnd_290906 < baseStart_290906 := by decide
  rcases family_descends (prefixWord ++ tailWord_290906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290909 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 4]
def baseStart_290909 : Nat := 118140960795 + 290909 * 2 ^ 59
def prefixEnd_290909 : Nat := 4983230072969 + 3 ^ 40 * 290909 * 2
def baseEnd_290909 : Nat := 132778794416806711910791

theorem tailTrace_290909 : CollatzResearch.WordTrace tailWord_290909 prefixEnd_290909 132778794416806711910791 := by
  unfold tailWord_290909
  simp only [CollatzResearch.WordTrace]
  refine ⟨10610322903093851146819781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7073548602062567431213187 10610322903093851146819781)
  ·
    refine ⟨1989435544330097090028709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10610322903093851146819781 1989435544330097090028709)
    ·
      refine ⟨373019164561893204380383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1989435544330097090028709 373019164561893204380383)
      ·
        refine ⟨559528746842839806570575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373019164561893204380383 559528746842839806570575)
        ·
          refine ⟨839293120264259709855863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559528746842839806570575 839293120264259709855863)
          ·
            refine ⟨1258939680396389564783795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839293120264259709855863 1258939680396389564783795)
            ·
              refine ⟨1888409520594584347175693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258939680396389564783795 1888409520594584347175693)
              ·
                refine ⟨708153570222969130190885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1888409520594584347175693 708153570222969130190885)
                ·
                  refine ⟨132778794416806711910791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708153570222969130190885 132778794416806711910791)
                  ·
                    rfl

theorem cell20_290909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_290909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290909 prefixEnd_290909 := by exact prefixLift 290909
  have htrace : WordTrace (prefixWord ++ tailWord_290909) baseStart_290909 baseEnd_290909 := by
    simpa [prefixWord, tailWord_290909, baseEnd_290909] using wordTrace_append hprefix tailTrace_290909
  have hstable : (prefixWord ++ tailWord_290909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290909).length < 2 ^ (prefixWord ++ tailWord_290909).sum := by decide
  have hdescent : baseEnd_290909 < baseStart_290909 := by decide
  rcases family_descends (prefixWord ++ tailWord_290909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290930 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_290930 : Nat := 118140960795 + 290930 * 2 ^ 59
def prefixEnd_290930 : Nat := 4983230072969 + 3 ^ 40 * 290930 * 2
def baseEnd_290930 : Nat := 132788379389023972210705

theorem tailTrace_290930 : CollatzResearch.WordTrace tailWord_290930 prefixEnd_290930 132788379389023972210705 := by
  unfold tailWord_290930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652772209004442933333561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7074059224011847822222829 2652772209004442933333561)
  ·
    refine ⟨1989579156753332200000171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2652772209004442933333561 1989579156753332200000171)
    ·
      refine ⟨2984368735129998300000257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989579156753332200000171 2984368735129998300000257)
      ·
        refine ⟨2238276551347498725000193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2984368735129998300000257 2238276551347498725000193)
        ·
          refine ⟨1678707413510624043750145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238276551347498725000193 1678707413510624043750145)
          ·
            refine ⟨1259030560132968032812609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678707413510624043750145 1259030560132968032812609)
            ·
              refine ⟨944272920099726024609457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259030560132968032812609 944272920099726024609457)
              ·
                refine ⟨708204690074794518457093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944272920099726024609457 708204690074794518457093)
                ·
                  refine ⟨132788379389023972210705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708204690074794518457093 132788379389023972210705)
                  ·
                    rfl

theorem cell20_290930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_290930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290930 prefixEnd_290930 := by exact prefixLift 290930
  have htrace : WordTrace (prefixWord ++ tailWord_290930) baseStart_290930 baseEnd_290930 := by
    simpa [prefixWord, tailWord_290930, baseEnd_290930] using wordTrace_append hprefix tailTrace_290930
  have hstable : (prefixWord ++ tailWord_290930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290930).length < 2 ^ (prefixWord ++ tailWord_290930).sum := by decide
  have hdescent : baseEnd_290930 < baseStart_290930 := by decide
  rcases family_descends (prefixWord ++ tailWord_290930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290937 : List Nat := [1, 2, 1, 3, 4, 2, 1, 6]
def baseStart_290937 : Nat := 118140960795 + 290937 * 2 ^ 59
def prefixEnd_290937 : Nat := 4983230072969 + 3 ^ 40 * 290937 * 2
def baseEnd_290937 : Nat := 44263858126587686325781

theorem tailTrace_290937 : CollatzResearch.WordTrace tailWord_290937 prefixEnd_290937 44263858126587686325781 := by
  unfold tailWord_290937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611344146992411928839065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7074229431328274619226043 10611344146992411928839065)
  ·
    refine ⟨7958508110244308946629299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10611344146992411928839065 7958508110244308946629299)
    ·
      refine ⟨11937762165366463419943949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7958508110244308946629299 11937762165366463419943949)
      ·
        refine ⟨4476660812012423782478981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11937762165366463419943949 4476660812012423782478981)
        ·
          refine ⟨839373902252329459214809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4476660812012423782478981 839373902252329459214809)
          ·
            refine ⟨629530426689247094411107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839373902252329459214809 629530426689247094411107)
            ·
              refine ⟨944295640033870641616661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629530426689247094411107 944295640033870641616661)
              ·
                refine ⟨44263858126587686325781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 944295640033870641616661 44263858126587686325781)
                ·
                  rfl

theorem cell20_290937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_290937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290937 prefixEnd_290937 := by exact prefixLift 290937
  have htrace : WordTrace (prefixWord ++ tailWord_290937) baseStart_290937 baseEnd_290937 := by
    simpa [prefixWord, tailWord_290937, baseEnd_290937] using wordTrace_append hprefix tailTrace_290937
  have hstable : (prefixWord ++ tailWord_290937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290937).length < 2 ^ (prefixWord ++ tailWord_290937).sum := by decide
  have hdescent : baseEnd_290937 < baseStart_290937 := by decide
  rcases family_descends (prefixWord ++ tailWord_290937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290947 : List Nat := [1, 1, 1, 3, 3, 3, 3, 3, 2]
def baseStart_290947 : Nat := 118140960795 + 290947 * 2 ^ 59
def prefixEnd_290947 : Nat := 4983230072969 + 3 ^ 40 * 290947 * 2
def baseEnd_290947 : Nat := 132796138652247468643969

theorem tailTrace_290947 : CollatzResearch.WordTrace tailWord_290947 prefixEnd_290947 132796138652247468643969 := by
  unfold tailWord_290947
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611708876956183636703095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7074472584637455757802063 10611708876956183636703095)
  ·
    refine ⟨15917563315434275455054643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10611708876956183636703095 15917563315434275455054643)
    ·
      refine ⟨23876344973151413182581965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15917563315434275455054643 23876344973151413182581965)
      ·
        refine ⟨8953629364931779943468237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23876344973151413182581965 8953629364931779943468237)
        ·
          refine ⟨3357611011849417478800589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8953629364931779943468237 3357611011849417478800589)
          ·
            refine ⟨1259104129443531554550221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3357611011849417478800589 1259104129443531554550221)
            ·
              refine ⟨472164048541324332956333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1259104129443531554550221 472164048541324332956333)
              ·
                refine ⟨177061518202996624858625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 472164048541324332956333 177061518202996624858625)
                ·
                  refine ⟨132796138652247468643969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177061518202996624858625 132796138652247468643969)
                  ·
                    rfl

theorem cell20_290947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 2].length) (baseStart_290947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290947 prefixEnd_290947 := by exact prefixLift 290947
  have htrace : WordTrace (prefixWord ++ tailWord_290947) baseStart_290947 baseEnd_290947 := by
    simpa [prefixWord, tailWord_290947, baseEnd_290947] using wordTrace_append hprefix tailTrace_290947
  have hstable : (prefixWord ++ tailWord_290947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290947).length < 2 ^ (prefixWord ++ tailWord_290947).sum := by decide
  have hdescent : baseEnd_290947 < baseStart_290947 := by decide
  rcases family_descends (prefixWord ++ tailWord_290947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290951 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_290951 : Nat := 118140960795 + 290951 * 2 ^ 59
def prefixEnd_290951 : Nat := 4983230072969 + 3 ^ 40 * 290951 * 2
def baseEnd_290951 : Nat := 132797964361241232510619

theorem tailTrace_290951 : CollatzResearch.WordTrace tailWord_290951 prefixEnd_290951 132797964361241232510619 := by
  unfold tailWord_290951
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611854768941692319848707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7074569845961128213232471 10611854768941692319848707)
  ·
    refine ⟨15917782153412538479773061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10611854768941692319848707 15917782153412538479773061)
    ·
      refine ⟨2984584153764850964957449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15917782153412538479773061 2984584153764850964957449)
      ·
        refine ⟨2238438115323638223718087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2984584153764850964957449 2238438115323638223718087)
        ·
          refine ⟨3357657172985457335577131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238438115323638223718087 3357657172985457335577131)
          ·
            refine ⟨5036485759478186003365697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357657172985457335577131 5036485759478186003365697)
            ·
              refine ⟨3777364319608639502524273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5036485759478186003365697 3777364319608639502524273)
              ·
                refine ⟨2833023239706479626893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3777364319608639502524273 2833023239706479626893205)
                ·
                  refine ⟨132797964361241232510619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2833023239706479626893205 132797964361241232510619)
                  ·
                    rfl

theorem cell20_290951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_290951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290951 prefixEnd_290951 := by exact prefixLift 290951
  have htrace : WordTrace (prefixWord ++ tailWord_290951) baseStart_290951 baseEnd_290951 := by
    simpa [prefixWord, tailWord_290951, baseEnd_290951] using wordTrace_append hprefix tailTrace_290951
  have hstable : (prefixWord ++ tailWord_290951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290951).length < 2 ^ (prefixWord ++ tailWord_290951).sum := by decide
  have hdescent : baseEnd_290951 < baseStart_290951 := by decide
  rcases family_descends (prefixWord ++ tailWord_290951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290974 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_290974 : Nat := 118140960795 + 290974 * 2 ^ 59
def prefixEnd_290974 : Nat := 4983230072969 + 3 ^ 40 * 290974 * 2
def baseEnd_290974 : Nat := 132808462187955374743859

theorem tailTrace_290974 : CollatzResearch.WordTrace tailWord_290974 prefixEnd_290974 132808462187955374743859 := by
  unfold tailWord_290974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326586705982295905991997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7075129098572244831957317 1326586705982295905991997)
  ·
    refine ⟨497470014743360964746999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1326586705982295905991997 497470014743360964746999)
    ·
      refine ⟨746205022115041447120499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497470014743360964746999 746205022115041447120499)
      ·
        refine ⟨1119307533172562170680749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746205022115041447120499 1119307533172562170680749)
        ·
          refine ⟨419740324939710814005281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1119307533172562170680749 419740324939710814005281)
          ·
            refine ⟨314805243704783110503961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419740324939710814005281 314805243704783110503961)
            ·
              refine ⟨236103932778587332877971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314805243704783110503961 236103932778587332877971)
              ·
                refine ⟨354155899167880999316957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236103932778587332877971 354155899167880999316957)
                ·
                  refine ⟨132808462187955374743859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354155899167880999316957 132808462187955374743859)
                  ·
                    rfl

theorem cell20_290974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_290974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290974 prefixEnd_290974 := by exact prefixLift 290974
  have htrace : WordTrace (prefixWord ++ tailWord_290974) baseStart_290974 baseEnd_290974 := by
    simpa [prefixWord, tailWord_290974, baseEnd_290974] using wordTrace_append hprefix tailTrace_290974
  have hstable : (prefixWord ++ tailWord_290974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290974).length < 2 ^ (prefixWord ++ tailWord_290974).sum := by decide
  have hdescent : baseEnd_290974 < baseStart_290974 := by decide
  rcases family_descends (prefixWord ++ tailWord_290974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290975 : List Nat := [1, 1, 2, 6, 1, 1, 1, 7]
def baseStart_290975 : Nat := 118140960795 + 290975 * 2 ^ 59
def prefixEnd_290975 : Nat := 4983230072969 + 3 ^ 40 * 290975 * 2
def baseEnd_290975 : Nat := 44269639538401271903507

theorem tailTrace_290975 : CollatzResearch.WordTrace tailWord_290975 prefixEnd_290975 44269639538401271903507 := by
  unfold tailWord_290975
  simp only [CollatzResearch.WordTrace]
  refine ⟨10612730120854744418722379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7075153413903162945814919 10612730120854744418722379)
  ·
    refine ⟨15919095181282116628083569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10612730120854744418722379 15919095181282116628083569)
    ·
      refine ⟨11939321385961587471062677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15919095181282116628083569 11939321385961587471062677)
      ·
        refine ⟨559655689966949412706063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11939321385961587471062677 559655689966949412706063)
        ·
          refine ⟨839483534950424119059095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559655689966949412706063 839483534950424119059095)
          ·
            refine ⟨1259225302425636178588643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839483534950424119059095 1259225302425636178588643)
            ·
              refine ⟨1888837953638454267882965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259225302425636178588643 1888837953638454267882965)
              ·
                refine ⟨44269639538401271903507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1888837953638454267882965 44269639538401271903507)
                ·
                  rfl

theorem cell20_290975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_290975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290975 prefixEnd_290975 := by exact prefixLift 290975
  have htrace : WordTrace (prefixWord ++ tailWord_290975) baseStart_290975 baseEnd_290975 := by
    simpa [prefixWord, tailWord_290975, baseEnd_290975] using wordTrace_append hprefix tailTrace_290975
  have hstable : (prefixWord ++ tailWord_290975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290975).length < 2 ^ (prefixWord ++ tailWord_290975).sum := by decide
  have hdescent : baseEnd_290975 < baseStart_290975 := by decide
  rcases family_descends (prefixWord ++ tailWord_290975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290978 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_290978 : Nat := 118140960795 + 290978 * 2 ^ 59
def prefixEnd_290978 : Nat := 4983230072969 + 3 ^ 40 * 290978 * 2
def baseEnd_290978 : Nat := 132810287896949138610509

theorem tailTrace_290978 : CollatzResearch.WordTrace tailWord_290978 prefixEnd_290978 132810287896949138610509 := by
  unfold tailWord_290978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653209884960968982770397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7075226359895917287387725 2653209884960968982770397)
  ·
    refine ⟨994953706860363368538899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2653209884960968982770397 994953706860363368538899)
    ·
      refine ⟨1492430560290545052808349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994953706860363368538899 1492430560290545052808349)
      ·
        refine ⟨559661460108954394803131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1492430560290545052808349 559661460108954394803131)
        ·
          refine ⟨839492190163431592204697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559661460108954394803131 839492190163431592204697)
          ·
            refine ⟨629619142622573694153523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839492190163431592204697 629619142622573694153523)
            ·
              refine ⟨944428713933860541230285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629619142622573694153523 944428713933860541230285)
              ·
                refine ⟨354160767725197702961357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944428713933860541230285 354160767725197702961357)
                ·
                  refine ⟨132810287896949138610509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354160767725197702961357 132810287896949138610509)
                  ·
                    rfl

theorem cell20_290978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_290978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_290978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_290978 prefixEnd_290978 := by exact prefixLift 290978
  have htrace : WordTrace (prefixWord ++ tailWord_290978) baseStart_290978 baseEnd_290978 := by
    simpa [prefixWord, tailWord_290978, baseEnd_290978] using wordTrace_append hprefix tailTrace_290978
  have hstable : (prefixWord ++ tailWord_290978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290978).length < 2 ^ (prefixWord ++ tailWord_290978).sum := by decide
  have hdescent : baseEnd_290978 < baseStart_290978 := by decide
  rcases family_descends (prefixWord ++ tailWord_290978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291051 : List Nat := [1, 1, 1, 1, 2, 5, 5, 4]
def baseStart_291051 : Nat := 118140960795 + 291051 * 2 ^ 59
def prefixEnd_291051 : Nat := 4983230072969 + 3 ^ 40 * 291051 * 2
def baseEnd_291051 : Nat := 44281202362028443058959

theorem tailTrace_291051 : CollatzResearch.WordTrace tailWord_291051 prefixEnd_291051 44281202362028443058959 := by
  unfold tailWord_291051
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615502068579409398489007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7077001379052939598992671 10615502068579409398489007)
  ·
    refine ⟨15923253102869114097733511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10615502068579409398489007 15923253102869114097733511)
    ·
      refine ⟨23884879654303671146600267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15923253102869114097733511 23884879654303671146600267)
      ·
        refine ⟨35827319481455506719900401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23884879654303671146600267 35827319481455506719900401)
        ·
          refine ⟨26870489611091630039925301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35827319481455506719900401 26870489611091630039925301)
          ·
            refine ⟨2519108401039840316242997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26870489611091630039925301 2519108401039840316242997)
            ·
              refine ⟨236166412597485029647781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2519108401039840316242997 236166412597485029647781)
              ·
                refine ⟨44281202362028443058959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236166412597485029647781 44281202362028443058959)
                ·
                  rfl

theorem cell20_291051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_291051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291051 prefixEnd_291051 := by exact prefixLift 291051
  have htrace : WordTrace (prefixWord ++ tailWord_291051) baseStart_291051 baseEnd_291051 := by
    simpa [prefixWord, tailWord_291051, baseEnd_291051] using wordTrace_append hprefix tailTrace_291051
  have hstable : (prefixWord ++ tailWord_291051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291051).length < 2 ^ (prefixWord ++ tailWord_291051).sum := by decide
  have hdescent : baseEnd_291051 < baseStart_291051 := by decide
  rcases family_descends (prefixWord ++ tailWord_291051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291102 : List Nat := [4, 3, 2, 1, 1, 3, 2, 4]
def baseStart_291102 : Nat := 118140960795 + 291102 * 2 ^ 59
def prefixEnd_291102 : Nat := 4983230072969 + 3 ^ 40 * 291102 * 2
def baseEnd_291102 : Nat := 44288961625251939492223

theorem tailTrace_291102 : CollatzResearch.WordTrace tailWord_291102 prefixEnd_291102 44288961625251939492223 := by
  unfold tailWord_291102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327170273924330638574445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7078241460929763405730373 1327170273924330638574445)
  ·
    refine ⟨497688852721623989465417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1327170273924330638574445 497688852721623989465417)
    ·
      refine ⟨373266639541217992099063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 497688852721623989465417 373266639541217992099063)
      ·
        refine ⟨559899959311826988148595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373266639541217992099063 559899959311826988148595)
        ·
          refine ⟨839849938967740482222893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559899959311826988148595 839849938967740482222893)
          ·
            refine ⟨314943727112902680833585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 839849938967740482222893 314943727112902680833585)
            ·
              refine ⟨236207795334677010625189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314943727112902680833585 236207795334677010625189)
              ·
                refine ⟨44288961625251939492223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236207795334677010625189 44288961625251939492223)
                ·
                  rfl

theorem cell20_291102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_291102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291102 prefixEnd_291102 := by exact prefixLift 291102
  have htrace : WordTrace (prefixWord ++ tailWord_291102) baseStart_291102 baseEnd_291102 := by
    simpa [prefixWord, tailWord_291102, baseEnd_291102] using wordTrace_append hprefix tailTrace_291102
  have hstable : (prefixWord ++ tailWord_291102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291102).length < 2 ^ (prefixWord ++ tailWord_291102).sum := by decide
  have hdescent : baseEnd_291102 < baseStart_291102 := by decide
  rcases family_descends (prefixWord ++ tailWord_291102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291106 : List Nat := [3, 3, 1, 1, 3, 1, 4, 4]
def baseStart_291106 : Nat := 118140960795 + 291106 * 2 ^ 59
def prefixEnd_291106 : Nat := 4983230072969 + 3 ^ 40 * 291106 * 2
def baseEnd_291106 : Nat := 44289570194916527447773

theorem tailTrace_291106 : CollatzResearch.WordTrace tailWord_291106 prefixEnd_291106 44289570194916527447773 := by
  unfold tailWord_291106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2654377020845038447935293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7078338722253435861160781 2654377020845038447935293)
  ·
    refine ⟨995391382816889417975735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2654377020845038447935293 995391382816889417975735)
    ·
      refine ⟨1493087074225334126963603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995391382816889417975735 1493087074225334126963603)
      ·
        refine ⟨2239630611338001190445405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1493087074225334126963603 2239630611338001190445405)
        ·
          refine ⟨839861479251750446417027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2239630611338001190445405 839861479251750446417027)
          ·
            refine ⟨1259792218877625669625541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839861479251750446417027 1259792218877625669625541)
            ·
              refine ⟨236211041039554813054789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1259792218877625669625541 236211041039554813054789)
              ·
                refine ⟨44289570194916527447773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236211041039554813054789 44289570194916527447773)
                ·
                  rfl

theorem cell20_291106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_291106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291106 prefixEnd_291106 := by exact prefixLift 291106
  have htrace : WordTrace (prefixWord ++ tailWord_291106) baseStart_291106 baseEnd_291106 := by
    simpa [prefixWord, tailWord_291106, baseEnd_291106] using wordTrace_append hprefix tailTrace_291106
  have hstable : (prefixWord ++ tailWord_291106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291106).length < 2 ^ (prefixWord ++ tailWord_291106).sum := by decide
  have hdescent : baseEnd_291106 < baseStart_291106 := by decide
  rcases family_descends (prefixWord ++ tailWord_291106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291120 : List Nat := [2, 1, 1, 1, 2, 2, 2, 7, 2]
def baseStart_291120 : Nat := 118140960795 + 291120 * 2 ^ 59
def prefixEnd_291120 : Nat := 4983230072969 + 3 ^ 40 * 291120 * 2
def baseEnd_291120 : Nat := 132875100566227755876595

theorem tailTrace_291120 : CollatzResearch.WordTrace tailWord_291120 prefixEnd_291120 132875100566227755876595 := by
  unfold tailWord_291120
  simp only [CollatzResearch.WordTrace]
  refine ⟨5309009352664717091375407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7078679136886289455167209 5309009352664717091375407)
  ·
    refine ⟨7963514028997075637063111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5309009352664717091375407 7963514028997075637063111)
    ·
      refine ⟨11945271043495613455594667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7963514028997075637063111 11945271043495613455594667)
      ·
        refine ⟨17917906565243420183392001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11945271043495613455594667 17917906565243420183392001)
        ·
          refine ⟨13438429923932565137544001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17917906565243420183392001 13438429923932565137544001)
          ·
            refine ⟨10078822442949423853158001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13438429923932565137544001 10078822442949423853158001)
            ·
              refine ⟨7559116832212067889868501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10078822442949423853158001 7559116832212067889868501)
              ·
                refine ⟨177166800754970341168793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7559116832212067889868501 177166800754970341168793)
                ·
                  refine ⟨132875100566227755876595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177166800754970341168793 132875100566227755876595)
                  ·
                    rfl

theorem cell20_291120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_291120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291120 prefixEnd_291120 := by exact prefixLift 291120
  have htrace : WordTrace (prefixWord ++ tailWord_291120) baseStart_291120 baseEnd_291120 := by
    simpa [prefixWord, tailWord_291120, baseEnd_291120] using wordTrace_append hprefix tailTrace_291120
  have hstable : (prefixWord ++ tailWord_291120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291120).length < 2 ^ (prefixWord ++ tailWord_291120).sum := by decide
  have hdescent : baseEnd_291120 < baseStart_291120 := by decide
  rcases family_descends (prefixWord ++ tailWord_291120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291155 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_291155 : Nat := 118140960795 + 291155 * 2 ^ 59
def prefixEnd_291155 : Nat := 4983230072969 + 3 ^ 40 * 291155 * 2
def baseEnd_291155 : Nat := 132891075519923189709785

theorem tailTrace_291155 : CollatzResearch.WordTrace tailWord_291155 prefixEnd_291155 132891075519923189709785 := by
  unfold tailWord_291155
  simp only [CollatzResearch.WordTrace]
  refine ⟨10619295260202635160274919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7079530173468423440183279 10619295260202635160274919)
  ·
    refine ⟨15928942890303952740412379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10619295260202635160274919 15928942890303952740412379)
    ·
      refine ⟨23893414335455929110618569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15928942890303952740412379 23893414335455929110618569)
      ·
        refine ⟨17920060751591946832963927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23893414335455929110618569 17920060751591946832963927)
        ·
          refine ⟨26880091127387920249445891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17920060751591946832963927 26880091127387920249445891)
          ·
            refine ⟨40320136691081880374168837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26880091127387920249445891 40320136691081880374168837)
            ·
              refine ⟨7560025629577852570156657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40320136691081880374168837 7560025629577852570156657)
              ·
                refine ⟨5670019222183389427617493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7560025629577852570156657 5670019222183389427617493)
                ·
                  refine ⟨132891075519923189709785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5670019222183389427617493 132891075519923189709785)
                  ·
                    rfl

theorem cell20_291155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_291155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291155 prefixEnd_291155 := by exact prefixLift 291155
  have htrace : WordTrace (prefixWord ++ tailWord_291155) baseStart_291155 baseEnd_291155 := by
    simpa [prefixWord, tailWord_291155, baseEnd_291155] using wordTrace_append hprefix tailTrace_291155
  have hstable : (prefixWord ++ tailWord_291155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291155).length < 2 ^ (prefixWord ++ tailWord_291155).sum := by decide
  have hdescent : baseEnd_291155 < baseStart_291155 := by decide
  rcases family_descends (prefixWord ++ tailWord_291155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291186 : List Nat := [3, 2, 1, 2, 1, 11]
def baseStart_291186 : Nat := 118140960795 + 291186 * 2 ^ 59
def prefixEnd_291186 : Nat := 4983230072969 + 3 ^ 40 * 291186 * 2
def baseEnd_291186 : Nat := 4922415732023142950975

theorem tailTrace_291186 : CollatzResearch.WordTrace tailWord_291186 prefixEnd_291186 4922415732023142950975 := by
  unfold tailWord_291186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655106480772581863663353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7080283948726884969768941 2655106480772581863663353)
  ·
    refine ⟨1991329860579436397747515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2655106480772581863663353 1991329860579436397747515)
    ·
      refine ⟨2986994790869154596621273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1991329860579436397747515 2986994790869154596621273)
      ·
        refine ⟨2240246093151865947465955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2986994790869154596621273 2240246093151865947465955)
        ·
          refine ⟨3360369139727798921198933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240246093151865947465955 3360369139727798921198933)
          ·
            refine ⟨4922415732023142950975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3360369139727798921198933 4922415732023142950975)
            ·
              rfl

theorem cell20_291186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 11].length) (baseStart_291186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291186 prefixEnd_291186 := by exact prefixLift 291186
  have htrace : WordTrace (prefixWord ++ tailWord_291186) baseStart_291186 baseEnd_291186 := by
    simpa [prefixWord, tailWord_291186, baseEnd_291186] using wordTrace_append hprefix tailTrace_291186
  have hstable : (prefixWord ++ tailWord_291186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291186).length < 2 ^ (prefixWord ++ tailWord_291186).sum := by decide
  have hdescent : baseEnd_291186 < baseStart_291186 := by decide
  rcases family_descends (prefixWord ++ tailWord_291186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291189 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 3]
def baseStart_291189 : Nat := 118140960795 + 291189 * 2 ^ 59
def prefixEnd_291189 : Nat := 4983230072969 + 3 ^ 40 * 291189 * 2
def baseEnd_291189 : Nat := 132906594046370182576313

theorem tailTrace_291189 : CollatzResearch.WordTrace tailWord_291189 prefixEnd_291189 132906594046370182576313 := by
  unfold tailWord_291189
  simp only [CollatzResearch.WordTrace]
  refine ⟨10620535342079458967012621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7080356894719639311341747 10620535342079458967012621)
  ·
    refine ⟨3982700753279797112629733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10620535342079458967012621 3982700753279797112629733)
    ·
      refine ⟨746756391239961958618075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3982700753279797112629733 746756391239961958618075)
      ·
        refine ⟨1120134586859942937927113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746756391239961958618075 1120134586859942937927113)
        ·
          refine ⟨840100940144957203445335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1120134586859942937927113 840100940144957203445335)
          ·
            refine ⟨1260151410217435805168003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840100940144957203445335 1260151410217435805168003)
            ·
              refine ⟨1890227115326153707752005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260151410217435805168003 1890227115326153707752005)
              ·
                refine ⟨354417584123653820203501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1890227115326153707752005 354417584123653820203501)
                ·
                  refine ⟨132906594046370182576313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354417584123653820203501 132906594046370182576313)
                  ·
                    rfl

theorem cell20_291189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_291189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291189 prefixEnd_291189 := by exact prefixLift 291189
  have htrace : WordTrace (prefixWord ++ tailWord_291189) baseStart_291189 baseEnd_291189 := by
    simpa [prefixWord, tailWord_291189, baseEnd_291189] using wordTrace_append hprefix tailTrace_291189
  have hstable : (prefixWord ++ tailWord_291189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291189).length < 2 ^ (prefixWord ++ tailWord_291189).sum := by decide
  have hdescent : baseEnd_291189 < baseStart_291189 := by decide
  rcases family_descends (prefixWord ++ tailWord_291189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291230 : List Nat := [4, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_291230 : Nat := 118140960795 + 291230 * 2 ^ 59
def prefixEnd_291230 : Nat := 4983230072969 + 3 ^ 40 * 291230 * 2
def baseEnd_291230 : Nat := 132925307563556262209479

theorem tailTrace_291230 : CollatzResearch.WordTrace tailWord_291230 prefixEnd_291230 132925307563556262209479 := by
  unfold tailWord_291230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327753841866365371156893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7081353823287281979503429 1327753841866365371156893)
  ·
    refine ⟨497907690699887014183835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1327753841866365371156893 497907690699887014183835)
    ·
      refine ⟨746861536049830521275753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497907690699887014183835 746861536049830521275753)
      ·
        refine ⟨560146152037372890956815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 746861536049830521275753 560146152037372890956815)
        ·
          refine ⟨840219228056059336435223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560146152037372890956815 840219228056059336435223)
          ·
            refine ⟨1260328842084089004652835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840219228056059336435223 1260328842084089004652835)
            ·
              refine ⟨1890493263126133506979253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260328842084089004652835 1890493263126133506979253)
              ·
                refine ⟨177233743418075016279305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1890493263126133506979253 177233743418075016279305)
                ·
                  refine ⟨132925307563556262209479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177233743418075016279305 132925307563556262209479)
                  ·
                    rfl

theorem cell20_291230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_291230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291230 prefixEnd_291230 := by exact prefixLift 291230
  have htrace : WordTrace (prefixWord ++ tailWord_291230) baseStart_291230 baseEnd_291230 := by
    simpa [prefixWord, tailWord_291230, baseEnd_291230] using wordTrace_append hprefix tailTrace_291230
  have hstable : (prefixWord ++ tailWord_291230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291230).length < 2 ^ (prefixWord ++ tailWord_291230).sum := by decide
  have hdescent : baseEnd_291230 < baseStart_291230 := by decide
  rcases family_descends (prefixWord ++ tailWord_291230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291255 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_291255 : Nat := 118140960795 + 291255 * 2 ^ 59
def prefixEnd_291255 : Nat := 4983230072969 + 3 ^ 40 * 291255 * 2
def baseEnd_291255 : Nat := 132936718244767286376043

theorem tailTrace_291255 : CollatzResearch.WordTrace tailWord_291255 prefixEnd_291255 132936718244767286376043 := by
  unfold tailWord_291255
  simp only [CollatzResearch.WordTrace]
  refine ⟨10622942559840352238915219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7081961706560234825943479 10622942559840352238915219)
  ·
    refine ⟨15934413839760528358372829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10622942559840352238915219 15934413839760528358372829)
    ·
      refine ⟨5975405189910198134389811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15934413839760528358372829 5975405189910198134389811)
      ·
        refine ⟨8963107784865297201584717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5975405189910198134389811 8963107784865297201584717)
        ·
          refine ⟨3361165419324486450594269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8963107784865297201584717 3361165419324486450594269)
          ·
            refine ⟨1260437032246682418972851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3361165419324486450594269 1260437032246682418972851)
            ·
              refine ⟨1890655548370023628459277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260437032246682418972851 1890655548370023628459277)
              ·
                refine ⟨708995830638758860672229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1890655548370023628459277 708995830638758860672229)
                ·
                  refine ⟨132936718244767286376043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708995830638758860672229 132936718244767286376043)
                  ·
                    rfl

theorem cell20_291255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_291255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291255 prefixEnd_291255 := by exact prefixLift 291255
  have htrace : WordTrace (prefixWord ++ tailWord_291255) baseStart_291255 baseEnd_291255 := by
    simpa [prefixWord, tailWord_291255, baseEnd_291255] using wordTrace_append hprefix tailTrace_291255
  have hstable : (prefixWord ++ tailWord_291255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291255).length < 2 ^ (prefixWord ++ tailWord_291255).sum := by decide
  have hdescent : baseEnd_291255 < baseStart_291255 := by decide
  rcases family_descends (prefixWord ++ tailWord_291255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291306 : List Nat := [3, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_291306 : Nat := 118140960795 + 291306 * 2 ^ 59
def prefixEnd_291306 : Nat := 4983230072969 + 3 ^ 40 * 291306 * 2
def baseEnd_291306 : Nat := 132959996034437775675835

theorem tailTrace_291306 : CollatzResearch.WordTrace tailWord_291306 prefixEnd_291306 132959996034437775675835 := by
  unfold tailWord_291306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656200670663896987255443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7083201788437058632681181 2656200670663896987255443)
  ·
    refine ⟨3984301005995845480883165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2656200670663896987255443 3984301005995845480883165)
    ·
      refine ⟨1494112877248442055331187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3984301005995845480883165 1494112877248442055331187)
      ·
        refine ⟨2241169315872663082996781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494112877248442055331187 2241169315872663082996781)
        ·
          refine ⟨840438493452248656123793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2241169315872663082996781 840438493452248656123793)
          ·
            refine ⟨630328870089186492092845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840438493452248656123793 630328870089186492092845)
            ·
              refine ⟨236373326283444934534817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 630328870089186492092845 236373326283444934534817)
              ·
                refine ⟨177279994712583700901113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236373326283444934534817 177279994712583700901113)
                ·
                  refine ⟨132959996034437775675835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177279994712583700901113 132959996034437775675835)
                  ·
                    rfl

theorem cell20_291306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_291306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291306 prefixEnd_291306 := by exact prefixLift 291306
  have htrace : WordTrace (prefixWord ++ tailWord_291306) baseStart_291306 baseEnd_291306 := by
    simpa [prefixWord, tailWord_291306, baseEnd_291306] using wordTrace_append hprefix tailTrace_291306
  have hstable : (prefixWord ++ tailWord_291306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291306).length < 2 ^ (prefixWord ++ tailWord_291306).sum := by decide
  have hdescent : baseEnd_291306 < baseStart_291306 := by decide
  rcases family_descends (prefixWord ++ tailWord_291306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291307 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_291307 : Nat := 118140960795 + 291307 * 2 ^ 59
def prefixEnd_291307 : Nat := 4983230072969 + 3 ^ 40 * 291307 * 2
def baseEnd_291307 : Nat := 132960452461686216642497

theorem tailTrace_291307 : CollatzResearch.WordTrace tailWord_291307 prefixEnd_291307 132960452461686216642497 := by
  unfold tailWord_291307
  simp only [CollatzResearch.WordTrace]
  refine ⟨10624839155651965119808175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7083226103767976746538783 10624839155651965119808175)
  ·
    refine ⟨15937258733477947679712263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10624839155651965119808175 15937258733477947679712263)
    ·
      refine ⟨23905888100216921519568395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15937258733477947679712263 23905888100216921519568395)
      ·
        refine ⟨35858832150325382279352593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23905888100216921519568395 35858832150325382279352593)
        ·
          refine ⟨26894124112744036709514445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35858832150325382279352593 26894124112744036709514445)
          ·
            refine ⟨10085296542279013766067917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26894124112744036709514445 10085296542279013766067917)
            ·
              refine ⟨3781986203354630162275469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10085296542279013766067917 3781986203354630162275469)
              ·
                refine ⟨1418244826257986310853301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3781986203354630162275469 1418244826257986310853301)
                ·
                  refine ⟨132960452461686216642497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1418244826257986310853301 132960452461686216642497)
                  ·
                    rfl

theorem cell20_291307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_291307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291307 prefixEnd_291307 := by exact prefixLift 291307
  have htrace : WordTrace (prefixWord ++ tailWord_291307) baseStart_291307 baseEnd_291307 := by
    simpa [prefixWord, tailWord_291307, baseEnd_291307] using wordTrace_append hprefix tailTrace_291307
  have hstable : (prefixWord ++ tailWord_291307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291307).length < 2 ^ (prefixWord ++ tailWord_291307).sum := by decide
  have hdescent : baseEnd_291307 < baseStart_291307 := by decide
  rcases family_descends (prefixWord ++ tailWord_291307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291310 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_291310 : Nat := 118140960795 + 291310 * 2 ^ 59
def prefixEnd_291310 : Nat := 4983230072969 + 3 ^ 40 * 291310 * 2
def baseEnd_291310 : Nat := 132961821743431539542485

theorem tailTrace_291310 : CollatzResearch.WordTrace tailWord_291310 prefixEnd_291310 132961821743431539542485 := by
  unfold tailWord_291310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328118571830137079020923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7083299049760731088111589 1328118571830137079020923)
  ·
    refine ⟨1992177857745205618531385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1328118571830137079020923 1992177857745205618531385)
    ·
      refine ⟨1494133393308904213898539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1992177857745205618531385 1494133393308904213898539)
      ·
        refine ⟨2241200089963356320847809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494133393308904213898539 2241200089963356320847809)
        ·
          refine ⟨1680900067472517240635857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2241200089963356320847809 1680900067472517240635857)
          ·
            refine ⟨1260675050604387930476893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1680900067472517240635857 1260675050604387930476893)
            ·
              refine ⟨472753143976645473928835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1260675050604387930476893 472753143976645473928835)
              ·
                refine ⟨709129715964968210893253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472753143976645473928835 709129715964968210893253)
                ·
                  refine ⟨132961821743431539542485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 709129715964968210893253 132961821743431539542485)
                  ·
                    rfl

theorem cell20_291310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_291310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291310 prefixEnd_291310 := by exact prefixLift 291310
  have htrace : WordTrace (prefixWord ++ tailWord_291310) baseStart_291310 baseEnd_291310 := by
    simpa [prefixWord, tailWord_291310, baseEnd_291310] using wordTrace_append hprefix tailTrace_291310
  have hstable : (prefixWord ++ tailWord_291310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291310).length < 2 ^ (prefixWord ++ tailWord_291310).sum := by decide
  have hdescent : baseEnd_291310 < baseStart_291310 := by decide
  rcases family_descends (prefixWord ++ tailWord_291310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291338 : List Nat := [3, 1, 2, 2, 2, 1, 1, 8]
def baseStart_291338 : Nat := 118140960795 + 291338 * 2 ^ 59
def prefixEnd_291338 : Nat := 4983230072969 + 3 ^ 40 * 291338 * 2
def baseEnd_291338 : Nat := 44324867235462628869679

theorem tailTrace_291338 : CollatzResearch.WordTrace tailWord_291338 prefixEnd_291338 44324867235462628869679 := by
  unfold tailWord_291338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656492454634914353546667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7083979879026438276124445 2656492454634914353546667)
  ·
    refine ⟨3984738681952371530320001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2656492454634914353546667 3984738681952371530320001)
    ·
      refine ⟨2988554011464278647740001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3984738681952371530320001 2988554011464278647740001)
      ·
        refine ⟨2241415508598208985805001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2988554011464278647740001 2241415508598208985805001)
        ·
          refine ⟨1681061631448656739353751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2241415508598208985805001 1681061631448656739353751)
          ·
            refine ⟨2521592447172985109030627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681061631448656739353751 2521592447172985109030627)
            ·
              refine ⟨3782388670759477663545941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521592447172985109030627 3782388670759477663545941)
              ·
                refine ⟨44324867235462628869679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3782388670759477663545941 44324867235462628869679)
                ·
                  rfl

theorem cell20_291338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_291338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291338 prefixEnd_291338 := by exact prefixLift 291338
  have htrace : WordTrace (prefixWord ++ tailWord_291338) baseStart_291338 baseEnd_291338 := by
    simpa [prefixWord, tailWord_291338, baseEnd_291338] using wordTrace_append hprefix tailTrace_291338
  have hstable : (prefixWord ++ tailWord_291338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291338).length < 2 ^ (prefixWord ++ tailWord_291338).sum := by decide
  have hdescent : baseEnd_291338 < baseStart_291338 := by decide
  rcases family_descends (prefixWord ++ tailWord_291338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291345 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_291345 : Nat := 118140960795 + 291345 * 2 ^ 59
def prefixEnd_291345 : Nat := 4983230072969 + 3 ^ 40 * 291345 * 2
def baseEnd_291345 : Nat := 132977796697126973375675

theorem tailTrace_291345 : CollatzResearch.WordTrace tailWord_291345 prefixEnd_291345 132977796697126973375675 := by
  unfold tailWord_291345
  simp only [CollatzResearch.WordTrace]
  refine ⟨10626225129514297609691489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7084150086342865073127659 10626225129514297609691489)
  ·
    refine ⟨7969668847135723207268617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10626225129514297609691489 7969668847135723207268617)
    ·
      refine ⟨5977251635351792405451463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7969668847135723207268617 5977251635351792405451463)
      ·
        refine ⟨8965877453027688608177195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5977251635351792405451463 8965877453027688608177195)
        ·
          refine ⟨13448816179541532912265793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8965877453027688608177195 13448816179541532912265793)
          ·
            refine ⟨10086612134656149684199345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13448816179541532912265793 10086612134656149684199345)
            ·
              refine ⟨7564959100992112263149509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10086612134656149684199345 7564959100992112263149509)
              ·
                refine ⟨1418429831436021049340533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7564959100992112263149509 1418429831436021049340533)
                ·
                  refine ⟨132977796697126973375675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1418429831436021049340533 132977796697126973375675)
                  ·
                    rfl

theorem cell20_291345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_291345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291345 prefixEnd_291345 := by exact prefixLift 291345
  have htrace : WordTrace (prefixWord ++ tailWord_291345) baseStart_291345 baseEnd_291345 := by
    simpa [prefixWord, tailWord_291345, baseEnd_291345] using wordTrace_append hprefix tailTrace_291345
  have hstable : (prefixWord ++ tailWord_291345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291345).length < 2 ^ (prefixWord ++ tailWord_291345).sum := by decide
  have hdescent : baseEnd_291345 < baseStart_291345 := by decide
  rcases family_descends (prefixWord ++ tailWord_291345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291365 : List Nat := [1, 3, 1, 2, 2, 1, 6, 2, 2]
def baseStart_291365 : Nat := 118140960795 + 291365 * 2 ^ 59
def prefixEnd_291365 : Nat := 4983230072969 + 3 ^ 40 * 291365 * 2
def baseEnd_291365 : Nat := 132986925242095792708927

theorem tailTrace_291365 : CollatzResearch.WordTrace tailWord_291365 prefixEnd_291365 132986925242095792708927 := by
  unfold tailWord_291365
  simp only [CollatzResearch.WordTrace]
  refine ⟨10626954589441841025419549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7084636392961227350279699 10626954589441841025419549)
  ·
    refine ⟨3985107971040690384532331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10626954589441841025419549 3985107971040690384532331)
    ·
      refine ⟨5977661956561035576798497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3985107971040690384532331 5977661956561035576798497)
      ·
        refine ⟨4483246467420776682598873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5977661956561035576798497 4483246467420776682598873)
        ·
          refine ⟨3362434850565582511949155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4483246467420776682598873 3362434850565582511949155)
          ·
            refine ⟨5043652275848373767923733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362434850565582511949155 5043652275848373767923733)
            ·
              refine ⟨236421200430392520371425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5043652275848373767923733 236421200430392520371425)
              ·
                refine ⟨177315900322794390278569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236421200430392520371425 177315900322794390278569)
                ·
                  refine ⟨132986925242095792708927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177315900322794390278569 132986925242095792708927)
                  ·
                    rfl

theorem cell20_291365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_291365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291365 prefixEnd_291365 := by exact prefixLift 291365
  have htrace : WordTrace (prefixWord ++ tailWord_291365) baseStart_291365 baseEnd_291365 := by
    simpa [prefixWord, tailWord_291365, baseEnd_291365] using wordTrace_append hprefix tailTrace_291365
  have hstable : (prefixWord ++ tailWord_291365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291365).length < 2 ^ (prefixWord ++ tailWord_291365).sum := by decide
  have hdescent : baseEnd_291365 < baseStart_291365 := by decide
  rcases family_descends (prefixWord ++ tailWord_291365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291376 : List Nat := [2, 1, 1, 1, 2, 3, 5, 5]
def baseStart_291376 : Nat := 118140960795 + 291376 * 2 ^ 59
def prefixEnd_291376 : Nat := 4983230072969 + 3 ^ 40 * 291376 * 2
def baseEnd_291376 : Nat := 44330648647276214447405

theorem tailTrace_291376 : CollatzResearch.WordTrace tailWord_291376 prefixEnd_291376 44330648647276214447405 := by
  unfold tailWord_291376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5313677896200994952034991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7084903861601326602713321 5313677896200994952034991)
  ·
    refine ⟨7970516844301492428052487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5313677896200994952034991 7970516844301492428052487)
    ·
      refine ⟨11955775266452238642078731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970516844301492428052487 11955775266452238642078731)
      ·
        refine ⟨17933662899678357963118097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955775266452238642078731 17933662899678357963118097)
        ·
          refine ⟨13450247174758768472338573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17933662899678357963118097 13450247174758768472338573)
          ·
            refine ⟨5043842690534538177126965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13450247174758768472338573 5043842690534538177126965)
            ·
              refine ⟨472860252237612954105653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5043842690534538177126965 472860252237612954105653)
              ·
                refine ⟨44330648647276214447405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 472860252237612954105653 44330648647276214447405)
                ·
                  rfl

theorem cell20_291376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_291376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291376 prefixEnd_291376 := by exact prefixLift 291376
  have htrace : WordTrace (prefixWord ++ tailWord_291376) baseStart_291376 baseEnd_291376 := by
    simpa [prefixWord, tailWord_291376, baseEnd_291376] using wordTrace_append hprefix tailTrace_291376
  have hstable : (prefixWord ++ tailWord_291376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291376).length < 2 ^ (prefixWord ++ tailWord_291376).sum := by decide
  have hdescent : baseEnd_291376 < baseStart_291376 := by decide
  rcases family_descends (prefixWord ++ tailWord_291376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291424 : List Nat := [2, 1, 1, 3, 2, 1, 4, 4, 2]
def baseStart_291424 : Nat := 118140960795 + 291424 * 2 ^ 59
def prefixEnd_291424 : Nat := 4983230072969 + 3 ^ 40 * 291424 * 2
def baseEnd_291424 : Nat := 133013854449753809742019

theorem tailTrace_291424 : CollatzResearch.WordTrace tailWord_291424 prefixEnd_291424 133013854449753809742019 := by
  unfold tailWord_291424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5314553248114047050908663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7086070997485396067878217 5314553248114047050908663)
  ·
    refine ⟨7971829872171070576362995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5314553248114047050908663 7971829872171070576362995)
    ·
      refine ⟨11957744808256605864544493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7971829872171070576362995 11957744808256605864544493)
      ·
        refine ⟨4484154303096227199204185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11957744808256605864544493 4484154303096227199204185)
        ·
          refine ⟨3363115727322170399403139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4484154303096227199204185 3363115727322170399403139)
          ·
            refine ⟨5044673590983255599104709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363115727322170399403139 5044673590983255599104709)
            ·
              refine ⟨945876298309360424832133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5044673590983255599104709 945876298309360424832133)
              ·
                refine ⟨177351805933005079656025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 945876298309360424832133 177351805933005079656025)
                ·
                  refine ⟨133013854449753809742019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177351805933005079656025 133013854449753809742019)
                  ·
                    rfl

theorem cell20_291424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_291424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291424 prefixEnd_291424 := by exact prefixLift 291424
  have htrace : WordTrace (prefixWord ++ tailWord_291424) baseStart_291424 baseEnd_291424 := by
    simpa [prefixWord, tailWord_291424, baseEnd_291424] using wordTrace_append hprefix tailTrace_291424
  have hstable : (prefixWord ++ tailWord_291424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291424).length < 2 ^ (prefixWord ++ tailWord_291424).sum := by decide
  have hdescent : baseEnd_291424 < baseStart_291424 := by decide
  rcases family_descends (prefixWord ++ tailWord_291424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291459 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_291459 : Nat := 118140960795 + 291459 * 2 ^ 59
def prefixEnd_291459 : Nat := 4983230072969 + 3 ^ 40 * 291459 * 2
def baseEnd_291459 : Nat := 133029829403449243575209

theorem tailTrace_291459 : CollatzResearch.WordTrace tailWord_291459 prefixEnd_291459 133029829403449243575209 := by
  unfold tailWord_291459
  simp only [CollatzResearch.WordTrace]
  refine ⟨10630383051101295079341431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7086922034067530052894287 10630383051101295079341431)
  ·
    refine ⟨15945574576651942619012147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10630383051101295079341431 15945574576651942619012147)
    ·
      refine ⟨23918361864977913928518221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15945574576651942619012147 23918361864977913928518221)
      ·
        refine ⟨8969385699366717723194333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23918361864977913928518221 8969385699366717723194333)
        ·
          refine ⟨3363519637262519146197875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8969385699366717723194333 3363519637262519146197875)
          ·
            refine ⟨5045279455893778719296813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363519637262519146197875 5045279455893778719296813)
            ·
              refine ⟨1891979795960167019736305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5045279455893778719296813 1891979795960167019736305)
              ·
                refine ⟨1418984846970125264802229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891979795960167019736305 1418984846970125264802229)
                ·
                  refine ⟨133029829403449243575209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1418984846970125264802229 133029829403449243575209)
                  ·
                    rfl

theorem cell20_291459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_291459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291459 prefixEnd_291459 := by exact prefixLift 291459
  have htrace : WordTrace (prefixWord ++ tailWord_291459) baseStart_291459 baseEnd_291459 := by
    simpa [prefixWord, tailWord_291459, baseEnd_291459] using wordTrace_append hprefix tailTrace_291459
  have hstable : (prefixWord ++ tailWord_291459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291459).length < 2 ^ (prefixWord ++ tailWord_291459).sum := by decide
  have hdescent : baseEnd_291459 < baseStart_291459 := by decide
  rcases family_descends (prefixWord ++ tailWord_291459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291479 : List Nat := [1, 1, 3, 3, 2, 1, 5, 2, 2]
def baseStart_291479 : Nat := 118140960795 + 291479 * 2 ^ 59
def prefixEnd_291479 : Nat := 4983230072969 + 3 ^ 40 * 291479 * 2
def baseEnd_291479 : Nat := 133038957948418062908461

theorem tailTrace_291479 : CollatzResearch.WordTrace tailWord_291479 prefixEnd_291479 133038957948418062908461 := by
  unfold tailWord_291479
  simp only [CollatzResearch.WordTrace]
  refine ⟨10631112511028838495069491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7087408340685892330046327 10631112511028838495069491)
  ·
    refine ⟨15946668766543257742604237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10631112511028838495069491 15946668766543257742604237)
    ·
      refine ⟨5980000787453721653476589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15946668766543257742604237 5980000787453721653476589)
      ·
        refine ⟨2242500295295145620053721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5980000787453721653476589 2242500295295145620053721)
        ·
          refine ⟨1681875221471359215040291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2242500295295145620053721 1681875221471359215040291)
          ·
            refine ⟨2522812832207038822560437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681875221471359215040291 2522812832207038822560437)
            ·
              refine ⟨236513703019409889615041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2522812832207038822560437 236513703019409889615041)
              ·
                refine ⟨177385277264557417211281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236513703019409889615041 177385277264557417211281)
                ·
                  refine ⟨133038957948418062908461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177385277264557417211281 133038957948418062908461)
                  ·
                    rfl

theorem cell20_291479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 2].length) (baseStart_291479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291479 prefixEnd_291479 := by exact prefixLift 291479
  have htrace : WordTrace (prefixWord ++ tailWord_291479) baseStart_291479 baseEnd_291479 := by
    simpa [prefixWord, tailWord_291479, baseEnd_291479] using wordTrace_append hprefix tailTrace_291479
  have hstable : (prefixWord ++ tailWord_291479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291479).length < 2 ^ (prefixWord ++ tailWord_291479).sum := by decide
  have hdescent : baseEnd_291479 < baseStart_291479 := by decide
  rcases family_descends (prefixWord ++ tailWord_291479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291489 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 3]
def baseStart_291489 : Nat := 118140960795 + 291489 * 2 ^ 59
def prefixEnd_291489 : Nat := 4983230072969 + 3 ^ 40 * 291489 * 2
def baseEnd_291489 : Nat := 133043522220902472575087

theorem tailTrace_291489 : CollatzResearch.WordTrace tailWord_291489 prefixEnd_291489 133043522220902472575087 := by
  unfold tailWord_291489
  simp only [CollatzResearch.WordTrace]
  refine ⟨10631477240992610202933521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7087651493995073468622347 10631477240992610202933521)
  ·
    refine ⟨7973607930744457652200141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10631477240992610202933521 7973607930744457652200141)
    ·
      refine ⟨2990102974029171619575053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7973607930744457652200141 2990102974029171619575053)
      ·
        refine ⟨1121288615260939357340645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2990102974029171619575053 1121288615260939357340645)
        ·
          refine ⟨210241615361426129501371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1121288615260939357340645 210241615361426129501371)
          ·
            refine ⟨315362423042139194252057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210241615361426129501371 315362423042139194252057)
            ·
              refine ⟨236521817281604395689043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315362423042139194252057 236521817281604395689043)
              ·
                refine ⟨354782725922406593533565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236521817281604395689043 354782725922406593533565)
                ·
                  refine ⟨133043522220902472575087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354782725922406593533565 133043522220902472575087)
                  ·
                    rfl

theorem cell20_291489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_291489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291489 prefixEnd_291489 := by exact prefixLift 291489
  have htrace : WordTrace (prefixWord ++ tailWord_291489) baseStart_291489 baseEnd_291489 := by
    simpa [prefixWord, tailWord_291489, baseEnd_291489] using wordTrace_append hprefix tailTrace_291489
  have hstable : (prefixWord ++ tailWord_291489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291489).length < 2 ^ (prefixWord ++ tailWord_291489).sum := by decide
  have hdescent : baseEnd_291489 < baseStart_291489 := by decide
  rcases family_descends (prefixWord ++ tailWord_291489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291504 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_291504 : Nat := 118140960795 + 291504 * 2 ^ 59
def prefixEnd_291504 : Nat := 4983230072969 + 3 ^ 40 * 291504 * 2
def baseEnd_291504 : Nat := 133050368629629087075025

theorem tailTrace_291504 : CollatzResearch.WordTrace tailWord_291504 prefixEnd_291504 133050368629629087075025 := by
  unfold tailWord_291504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316012167969133882364783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7088016223958845176486377 5316012167969133882364783)
  ·
    refine ⟨7974018251953700823547175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5316012167969133882364783 7974018251953700823547175)
    ·
      refine ⟨11961027377930551235320763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974018251953700823547175 11961027377930551235320763)
      ·
        refine ⟨17941541066895826852981145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961027377930551235320763 17941541066895826852981145)
        ·
          refine ⟨13456155800171870139735859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17941541066895826852981145 13456155800171870139735859)
          ·
            refine ⟨20184233700257805209603789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13456155800171870139735859 20184233700257805209603789)
            ·
              refine ⟨7569087637596676953601421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20184233700257805209603789 7569087637596676953601421)
              ·
                refine ⟨2838407864098753857600533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7569087637596676953601421 2838407864098753857600533)
                ·
                  refine ⟨133050368629629087075025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2838407864098753857600533 133050368629629087075025)
                  ·
                    rfl

theorem cell20_291504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_291504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291504 prefixEnd_291504 := by exact prefixLift 291504
  have htrace : WordTrace (prefixWord ++ tailWord_291504) baseStart_291504 baseEnd_291504 := by
    simpa [prefixWord, tailWord_291504, baseEnd_291504] using wordTrace_append hprefix tailTrace_291504
  have hstable : (prefixWord ++ tailWord_291504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291504).length < 2 ^ (prefixWord ++ tailWord_291504).sum := by decide
  have hdescent : baseEnd_291504 < baseStart_291504 := by decide
  rcases family_descends (prefixWord ++ tailWord_291504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291534 : List Nat := [4, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_291534 : Nat := 118140960795 + 291534 * 2 ^ 59
def prefixEnd_291534 : Nat := 4983230072969 + 3 ^ 40 * 291534 * 2
def baseEnd_291534 : Nat := 133064061447082316074903

theorem tailTrace_291534 : CollatzResearch.WordTrace tailWord_291534 prefixEnd_291534 133064061447082316074903 := by
  unfold tailWord_291534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329139815728697861040207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7088745683886388592214437 1329139815728697861040207)
  ·
    refine ⟨1993709723593046791560311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1329139815728697861040207 1993709723593046791560311)
    ·
      refine ⟨2990564585389570187340467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1993709723593046791560311 2990564585389570187340467)
      ·
        refine ⟨4485846878084355281010701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2990564585389570187340467 4485846878084355281010701)
        ·
          refine ⟨1682192579281633230379013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4485846878084355281010701 1682192579281633230379013)
          ·
            refine ⟨315411108615306230696065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1682192579281633230379013 315411108615306230696065)
            ·
              refine ⟨236558331461479673022049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315411108615306230696065 236558331461479673022049)
              ·
                refine ⟨177418748596109754766537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236558331461479673022049 177418748596109754766537)
                ·
                  refine ⟨133064061447082316074903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177418748596109754766537 133064061447082316074903)
                  ·
                    rfl

theorem cell20_291534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_291534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291534 prefixEnd_291534 := by exact prefixLift 291534
  have htrace : WordTrace (prefixWord ++ tailWord_291534) baseStart_291534 baseEnd_291534 := by
    simpa [prefixWord, tailWord_291534, baseEnd_291534] using wordTrace_append hprefix tailTrace_291534
  have hstable : (prefixWord ++ tailWord_291534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291534).length < 2 ^ (prefixWord ++ tailWord_291534).sum := by decide
  have hdescent : baseEnd_291534 < baseStart_291534 := by decide
  rcases family_descends (prefixWord ++ tailWord_291534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291541 : List Nat := [1, 3, 2, 5, 2, 1, 1, 5]
def baseStart_291541 : Nat := 118140960795 + 291541 * 2 ^ 59
def prefixEnd_291541 : Nat := 4983230072969 + 3 ^ 40 * 291541 * 2
def baseEnd_291541 : Nat := 44355752145940467613847

theorem tailTrace_291541 : CollatzResearch.WordTrace tailWord_291541 prefixEnd_291541 44355752145940467613847 := by
  unfold tailWord_291541
  simp only [CollatzResearch.WordTrace]
  refine ⟨10633373836804223083826477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7088915891202815389217651 10633373836804223083826477)
  ·
    refine ⟨3987515188801583656434929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10633373836804223083826477 3987515188801583656434929)
    ·
      refine ⟨2990636391601187742326197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3987515188801583656434929 2990636391601187742326197)
      ·
        refine ⟨280372161712611350843081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2990636391601187742326197 280372161712611350843081)
        ·
          refine ⟨210279121284458513132311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280372161712611350843081 210279121284458513132311)
          ·
            refine ⟨315418681926687769698467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210279121284458513132311 315418681926687769698467)
            ·
              refine ⟨473128022890031654547701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315418681926687769698467 473128022890031654547701)
              ·
                refine ⟨44355752145940467613847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 473128022890031654547701 44355752145940467613847)
                ·
                  rfl

theorem cell20_291541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5].length) (baseStart_291541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291541 prefixEnd_291541 := by exact prefixLift 291541
  have htrace : WordTrace (prefixWord ++ tailWord_291541) baseStart_291541 baseEnd_291541 := by
    simpa [prefixWord, tailWord_291541, baseEnd_291541] using wordTrace_append hprefix tailTrace_291541
  have hstable : (prefixWord ++ tailWord_291541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291541).length < 2 ^ (prefixWord ++ tailWord_291541).sum := by decide
  have hdescent : baseEnd_291541 < baseStart_291541 := by decide
  rcases family_descends (prefixWord ++ tailWord_291541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291576 : List Nat := [2, 1, 2, 1, 1, 2, 6, 3, 2]
def baseStart_291576 : Nat := 118140960795 + 291576 * 2 ^ 59
def prefixEnd_291576 : Nat := 4983230072969 + 3 ^ 40 * 291576 * 2
def baseEnd_291576 : Nat := 133083231391516836674731

theorem tailTrace_291576 : CollatzResearch.WordTrace tailWord_291576 prefixEnd_291576 133083231391516836674731 := by
  unfold tailWord_291576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5317325195838712030675291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7089766927784949374233721 5317325195838712030675291)
  ·
    refine ⟨7975987793758068046012937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5317325195838712030675291 7975987793758068046012937)
    ·
      refine ⟨5981990845318551034509703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7975987793758068046012937 5981990845318551034509703)
      ·
        refine ⟨8972986267977826551764555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5981990845318551034509703 8972986267977826551764555)
        ·
          refine ⟨13459479401966739827646833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8972986267977826551764555 13459479401966739827646833)
          ·
            refine ⟨10094609551475054870735125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13459479401966739827646833 10094609551475054870735125)
            ·
              refine ⟨473184822725393197065709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10094609551475054870735125 473184822725393197065709)
              ·
                refine ⟨177444308522022448899641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473184822725393197065709 177444308522022448899641)
                ·
                  refine ⟨133083231391516836674731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177444308522022448899641 133083231391516836674731)
                  ·
                    rfl

theorem cell20_291576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_291576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291576 prefixEnd_291576 := by exact prefixLift 291576
  have htrace : WordTrace (prefixWord ++ tailWord_291576) baseStart_291576 baseEnd_291576 := by
    simpa [prefixWord, tailWord_291576, baseEnd_291576] using wordTrace_append hprefix tailTrace_291576
  have hstable : (prefixWord ++ tailWord_291576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291576).length < 2 ^ (prefixWord ++ tailWord_291576).sum := by decide
  have hdescent : baseEnd_291576 < baseStart_291576 := by decide
  rcases family_descends (prefixWord ++ tailWord_291576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291586 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_291586 : Nat := 118140960795 + 291586 * 2 ^ 59
def prefixEnd_291586 : Nat := 4983230072969 + 3 ^ 40 * 291586 * 2
def baseEnd_291586 : Nat := 133087795664001246341357

theorem tailTrace_291586 : CollatzResearch.WordTrace tailWord_291586 prefixEnd_291586 133087795664001246341357 := by
  unfold tailWord_291586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2658753780410298942303653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7090010081094130512809741 2658753780410298942303653)
  ·
    refine ⟨498516333826931051681935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2658753780410298942303653 498516333826931051681935)
    ·
      refine ⟨747774500740396577522903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 498516333826931051681935 747774500740396577522903)
      ·
        refine ⟨1121661751110594866284355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747774500740396577522903 1121661751110594866284355)
        ·
          refine ⟨1682492626665892299426533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121661751110594866284355 1682492626665892299426533)
          ·
            refine ⟨315467367499854806142475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1682492626665892299426533 315467367499854806142475)
            ·
              refine ⟨473201051249782209213713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315467367499854806142475 473201051249782209213713)
              ·
                refine ⟨354900788437336656910285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473201051249782209213713 354900788437336656910285)
                ·
                  refine ⟨133087795664001246341357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354900788437336656910285 133087795664001246341357)
                  ·
                    rfl

theorem cell20_291586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_291586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291586 prefixEnd_291586 := by exact prefixLift 291586
  have htrace : WordTrace (prefixWord ++ tailWord_291586) baseStart_291586 baseEnd_291586 := by
    simpa [prefixWord, tailWord_291586, baseEnd_291586] using wordTrace_append hprefix tailTrace_291586
  have hstable : (prefixWord ++ tailWord_291586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291586).length < 2 ^ (prefixWord ++ tailWord_291586).sum := by decide
  have hdescent : baseEnd_291586 < baseStart_291586 := by decide
  rcases family_descends (prefixWord ++ tailWord_291586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291625 : List Nat := [1, 2, 1, 1, 1, 1, 1, 12]
def baseStart_291625 : Nat := 118140960795 + 291625 * 2 ^ 59
def prefixEnd_291625 : Nat := 4983230072969 + 3 ^ 40 * 291625 * 2
def baseEnd_291625 : Nat := 44368532108896814680399

theorem tailTrace_291625 : CollatzResearch.WordTrace tailWord_291625 prefixEnd_291625 44368532108896814680399 := by
  unfold tailWord_291625
  simp only [CollatzResearch.WordTrace]
  refine ⟨10636437568499905429884329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7090958378999936953256219 10636437568499905429884329)
  ·
    refine ⟨7977328176374929072413247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10636437568499905429884329 7977328176374929072413247)
    ·
      refine ⟨11965992264562393608619871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7977328176374929072413247 11965992264562393608619871)
      ·
        refine ⟨17948988396843590412929807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11965992264562393608619871 17948988396843590412929807)
        ·
          refine ⟨26923482595265385619394711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17948988396843590412929807 26923482595265385619394711)
          ·
            refine ⟨40385223892898078429092067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26923482595265385619394711 40385223892898078429092067)
            ·
              refine ⟨60577835839347117643638101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40385223892898078429092067 60577835839347117643638101)
              ·
                refine ⟨44368532108896814680399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 60577835839347117643638101 44368532108896814680399)
                ·
                  rfl

theorem cell20_291625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_291625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291625 prefixEnd_291625 := by exact prefixLift 291625
  have htrace : WordTrace (prefixWord ++ tailWord_291625) baseStart_291625 baseEnd_291625 := by
    simpa [prefixWord, tailWord_291625, baseEnd_291625] using wordTrace_append hprefix tailTrace_291625
  have hstable : (prefixWord ++ tailWord_291625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291625).length < 2 ^ (prefixWord ++ tailWord_291625).sum := by decide
  have hdescent : baseEnd_291625 < baseStart_291625 := by decide
  rcases family_descends (prefixWord ++ tailWord_291625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291638 : List Nat := [5, 1, 2, 2, 2, 2, 6]
def baseStart_291638 : Nat := 118140960795 + 291638 * 2 ^ 59
def prefixEnd_291638 : Nat := 4983230072969 + 3 ^ 40 * 291638 * 2
def baseEnd_291638 : Nat := 14790169986768908511979

theorem tailTrace_291638 : CollatzResearch.WordTrace tailWord_291638 prefixEnd_291638 14790169986768908511979 := by
  unfold tailWord_291638
  simp only [CollatzResearch.WordTrace]
  refine ⟨664806982340800540631723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7091274478301872433405045 664806982340800540631723)
  ·
    refine ⟨997210473511200810947585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664806982340800540631723 997210473511200810947585)
    ·
      refine ⟨747907855133400608210689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 997210473511200810947585 747907855133400608210689)
      ·
        refine ⟨560930891350050456158017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 747907855133400608210689 560930891350050456158017)
        ·
          refine ⟨420698168512537842118513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560930891350050456158017 420698168512537842118513)
          ·
            refine ⟨315523626384403381588885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420698168512537842118513 315523626384403381588885)
            ·
              refine ⟨14790169986768908511979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 315523626384403381588885 14790169986768908511979)
              ·
                rfl

theorem cell20_291638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 6].length) (baseStart_291638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291638 prefixEnd_291638 := by exact prefixLift 291638
  have htrace : WordTrace (prefixWord ++ tailWord_291638) baseStart_291638 baseEnd_291638 := by
    simpa [prefixWord, tailWord_291638, baseEnd_291638] using wordTrace_append hprefix tailTrace_291638
  have hstable : (prefixWord ++ tailWord_291638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291638).length < 2 ^ (prefixWord ++ tailWord_291638).sum := by decide
  have hdescent : baseEnd_291638 < baseStart_291638 := by decide
  rcases family_descends (prefixWord ++ tailWord_291638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291666 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_291666 : Nat := 118140960795 + 291666 * 2 ^ 59
def prefixEnd_291666 : Nat := 4983230072969 + 3 ^ 40 * 291666 * 2
def baseEnd_291666 : Nat := 133124309843876523674363

theorem tailTrace_291666 : CollatzResearch.WordTrace tailWord_291666 prefixEnd_291666 133124309843876523674363 := by
  unfold tailWord_291666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2659483240337842358031713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7091955307567579621417901 2659483240337842358031713)
  ·
    refine ⟨1994612430253381768523785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2659483240337842358031713 1994612430253381768523785)
    ·
      refine ⟨1495959322690036326392839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1994612430253381768523785 1495959322690036326392839)
      ·
        refine ⟨2243938984035054489589259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1495959322690036326392839 2243938984035054489589259)
        ·
          refine ⟨3365908476052581734383889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243938984035054489589259 3365908476052581734383889)
          ·
            refine ⟨2524431357039436300787917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3365908476052581734383889 2524431357039436300787917)
            ·
              refine ⟨946661758889788612795469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2524431357039436300787917 946661758889788612795469)
              ·
                refine ⟨354998159583670729798301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 946661758889788612795469 354998159583670729798301)
                ·
                  refine ⟨133124309843876523674363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354998159583670729798301 133124309843876523674363)
                  ·
                    rfl

theorem cell20_291666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_291666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291666 prefixEnd_291666 := by exact prefixLift 291666
  have htrace : WordTrace (prefixWord ++ tailWord_291666) baseStart_291666 baseEnd_291666 := by
    simpa [prefixWord, tailWord_291666, baseEnd_291666] using wordTrace_append hprefix tailTrace_291666
  have hstable : (prefixWord ++ tailWord_291666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291666).length < 2 ^ (prefixWord ++ tailWord_291666).sum := by decide
  have hdescent : baseEnd_291666 < baseStart_291666 := by decide
  rcases family_descends (prefixWord ++ tailWord_291666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291745 : List Nat := [1, 2, 3, 4, 1, 2, 2, 3, 2]
def baseStart_291745 : Nat := 118140960795 + 291745 * 2 ^ 59
def prefixEnd_291745 : Nat := 4983230072969 + 3 ^ 40 * 291745 * 2
def baseEnd_291745 : Nat := 133160367596503360040707

theorem tailTrace_291745 : CollatzResearch.WordTrace tailWord_291745 prefixEnd_291745 133160367596503360040707 := by
  unfold tailWord_291745
  simp only [CollatzResearch.WordTrace]
  refine ⟨10640814328065165924252689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7093876218710110616168459 10640814328065165924252689)
  ·
    refine ⟨7980610746048874443189517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10640814328065165924252689 7980610746048874443189517)
    ·
      refine ⟨2992729029768327916196069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7980610746048874443189517 2992729029768327916196069)
      ·
        refine ⟨561136693081561484286763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2992729029768327916196069 561136693081561484286763)
        ·
          refine ⟨841705039622342226430145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561136693081561484286763 841705039622342226430145)
          ·
            refine ⟨631278779716756669822609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841705039622342226430145 631278779716756669822609)
            ·
              refine ⟨473459084787567502366957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631278779716756669822609 473459084787567502366957)
              ·
                refine ⟨177547156795337813387609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473459084787567502366957 177547156795337813387609)
                ·
                  refine ⟨133160367596503360040707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177547156795337813387609 133160367596503360040707)
                  ·
                    rfl

theorem cell20_291745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_291745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291745 prefixEnd_291745 := by exact prefixLift 291745
  have htrace : WordTrace (prefixWord ++ tailWord_291745) baseStart_291745 baseEnd_291745 := by
    simpa [prefixWord, tailWord_291745, baseEnd_291745] using wordTrace_append hprefix tailTrace_291745
  have hstable : (prefixWord ++ tailWord_291745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291745).length < 2 ^ (prefixWord ++ tailWord_291745).sum := by decide
  have hdescent : baseEnd_291745 < baseStart_291745 := by decide
  rcases family_descends (prefixWord ++ tailWord_291745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291763 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 3]
def baseStart_291763 : Nat := 118140960795 + 291763 * 2 ^ 59
def prefixEnd_291763 : Nat := 4983230072969 + 3 ^ 40 * 291763 * 2
def baseEnd_291763 : Nat := 133168583286975297440633

theorem tailTrace_291763 : CollatzResearch.WordTrace tailWord_291763 prefixEnd_291763 133168583286975297440633 := by
  unfold tailWord_291763
  simp only [CollatzResearch.WordTrace]
  refine ⟨10641470841999954998407943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7094313894666636665605295 10641470841999954998407943)
  ·
    refine ⟨15962206262999932497611915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10641470841999954998407943 15962206262999932497611915)
    ·
      refine ⟨23943309394499898746417873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15962206262999932497611915 23943309394499898746417873)
      ·
        refine ⟨17957482045874924059813405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23943309394499898746417873 17957482045874924059813405)
        ·
          refine ⟨6734055767203096522430027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17957482045874924059813405 6734055767203096522430027)
          ·
            refine ⟨10101083650804644783645041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6734055767203096522430027 10101083650804644783645041)
            ·
              refine ⟨7575812738103483587733781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10101083650804644783645041 7575812738103483587733781)
              ·
                refine ⟨355116222098600793175021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7575812738103483587733781 355116222098600793175021)
                ·
                  refine ⟨133168583286975297440633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355116222098600793175021 133168583286975297440633)
                  ·
                    rfl

theorem cell20_291763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_291763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291763 prefixEnd_291763 := by exact prefixLift 291763
  have htrace : WordTrace (prefixWord ++ tailWord_291763) baseStart_291763 baseEnd_291763 := by
    simpa [prefixWord, tailWord_291763, baseEnd_291763] using wordTrace_append hprefix tailTrace_291763
  have hstable : (prefixWord ++ tailWord_291763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291763).length < 2 ^ (prefixWord ++ tailWord_291763).sum := by decide
  have hdescent : baseEnd_291763 < baseStart_291763 := by decide
  rcases family_descends (prefixWord ++ tailWord_291763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291782 : List Nat := [6, 1, 3, 1, 2, 1, 2, 4]
def baseStart_291782 : Nat := 118140960795 + 291782 * 2 ^ 59
def prefixEnd_291782 : Nat := 4983230072969 + 3 ^ 40 * 291782 * 2
def baseEnd_291782 : Nat := 44392418468231891935741

theorem tailTrace_291782 : CollatzResearch.WordTrace tailWord_291782 prefixEnd_291782 44392418468231891935741 := by
  unfold tailWord_291782
  simp only [CollatzResearch.WordTrace]
  refine ⟨332567619654097538854675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7094775885954080828899733 332567619654097538854675)
  ·
    refine ⟨498851429481146308282013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 332567619654097538854675 498851429481146308282013)
    ·
      refine ⟨187069286055429865605755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 498851429481146308282013 187069286055429865605755)
      ·
        refine ⟨280603929083144798408633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187069286055429865605755 280603929083144798408633)
        ·
          refine ⟨210452946812358598806475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280603929083144798408633 210452946812358598806475)
          ·
            refine ⟨315679420218537898209713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210452946812358598806475 315679420218537898209713)
            ·
              refine ⟨236759565163903423657285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315679420218537898209713 236759565163903423657285)
              ·
                refine ⟨44392418468231891935741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236759565163903423657285 44392418468231891935741)
                ·
                  rfl

theorem cell20_291782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_291782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291782 prefixEnd_291782 := by exact prefixLift 291782
  have htrace : WordTrace (prefixWord ++ tailWord_291782) baseStart_291782 baseEnd_291782 := by
    simpa [prefixWord, tailWord_291782, baseEnd_291782] using wordTrace_append hprefix tailTrace_291782
  have hstable : (prefixWord ++ tailWord_291782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291782).length < 2 ^ (prefixWord ++ tailWord_291782).sum := by decide
  have hdescent : baseEnd_291782 < baseStart_291782 := by decide
  rcases family_descends (prefixWord ++ tailWord_291782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291801 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_291801 : Nat := 118140960795 + 291801 * 2 ^ 59
def prefixEnd_291801 : Nat := 4983230072969 + 3 ^ 40 * 291801 * 2
def baseEnd_291801 : Nat := 133185927522416054173811

theorem tailTrace_291801 : CollatzResearch.WordTrace tailWord_291801 prefixEnd_291801 133185927522416054173811 := by
  unfold tailWord_291801
  simp only [CollatzResearch.WordTrace]
  refine ⟨10642856815862287488291257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7095237877241524992194171 10642856815862287488291257)
  ·
    refine ⟨7982142611896715616218443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10642856815862287488291257 7982142611896715616218443)
    ·
      refine ⟨11973213917845073424327665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7982142611896715616218443 11973213917845073424327665)
      ·
        refine ⟨8979910438383805068245749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11973213917845073424327665 8979910438383805068245749)
        ·
          refine ⟨841866603598481725148039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8979910438383805068245749 841866603598481725148039)
          ·
            refine ⟨1262799905397722587722059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841866603598481725148039 1262799905397722587722059)
            ·
              refine ⟨1894199858096583881583089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262799905397722587722059 1894199858096583881583089)
              ·
                refine ⟨1420649893572437911187317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894199858096583881583089 1420649893572437911187317)
                ·
                  refine ⟨133185927522416054173811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1420649893572437911187317 133185927522416054173811)
                  ·
                    rfl

theorem cell20_291801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_291801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291801 prefixEnd_291801 := by exact prefixLift 291801
  have htrace : WordTrace (prefixWord ++ tailWord_291801) baseStart_291801 baseEnd_291801 := by
    simpa [prefixWord, tailWord_291801, baseEnd_291801] using wordTrace_append hprefix tailTrace_291801
  have hstable : (prefixWord ++ tailWord_291801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291801).length < 2 ^ (prefixWord ++ tailWord_291801).sum := by decide
  have hdescent : baseEnd_291801 < baseStart_291801 := by decide
  rcases family_descends (prefixWord ++ tailWord_291801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291825 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_291825 : Nat := 118140960795 + 291825 * 2 ^ 59
def prefixEnd_291825 : Nat := 4983230072969 + 3 ^ 40 * 291825 * 2
def baseEnd_291825 : Nat := 133196881776378637373713

theorem tailTrace_291825 : CollatzResearch.WordTrace tailWord_291825 prefixEnd_291825 133196881776378637373713 := by
  unfold tailWord_291825
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643732167775339587164929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7095821445183559724776619 10643732167775339587164929)
  ·
    refine ⟨7982799125831504690373697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10643732167775339587164929 7982799125831504690373697)
    ·
      refine ⟨5987099344373628517780273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7982799125831504690373697 5987099344373628517780273)
      ·
        refine ⟨4490324508280221388335205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5987099344373628517780273 4490324508280221388335205)
        ·
          refine ⟨841935845302541510312851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4490324508280221388335205 841935845302541510312851)
          ·
            refine ⟨1262903767953812265469277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841935845302541510312851 1262903767953812265469277)
            ·
              refine ⟨473588912982679599550979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1262903767953812265469277 473588912982679599550979)
              ·
                refine ⟨710383369474019399326469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473588912982679599550979 710383369474019399326469)
                ·
                  refine ⟨133196881776378637373713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710383369474019399326469 133196881776378637373713)
                  ·
                    rfl

theorem cell20_291825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_291825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291825 prefixEnd_291825 := by exact prefixLift 291825
  have htrace : WordTrace (prefixWord ++ tailWord_291825) baseStart_291825 baseEnd_291825 := by
    simpa [prefixWord, tailWord_291825, baseEnd_291825] using wordTrace_append hprefix tailTrace_291825
  have hstable : (prefixWord ++ tailWord_291825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291825).length < 2 ^ (prefixWord ++ tailWord_291825).sum := by decide
  have hdescent : baseEnd_291825 < baseStart_291825 := by decide
  rcases family_descends (prefixWord ++ tailWord_291825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291876 : List Nat := [2, 3, 1, 4, 1, 3, 2, 2, 2]
def baseStart_291876 : Nat := 118140960795 + 291876 * 2 ^ 59
def prefixEnd_291876 : Nat := 4983230072969 + 3 ^ 40 * 291876 * 2
def baseEnd_291876 : Nat := 133220159566049126673505

theorem tailTrace_291876 : CollatzResearch.WordTrace tailWord_291876 prefixEnd_291876 133220159566049126673505 := by
  unfold tailWord_291876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322796145295287648635741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7097061527060383531514321 5322796145295287648635741)
  ·
    refine ⟨1996048554485732868238403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5322796145295287648635741 1996048554485732868238403)
    ·
      refine ⟨2994072831728599302357605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996048554485732868238403 2994072831728599302357605)
      ·
        refine ⟨561388655949112369192051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2994072831728599302357605 561388655949112369192051)
        ·
          refine ⟨842082983923668553788077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561388655949112369192051 842082983923668553788077)
          ·
            refine ⟨315781118971375707670529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 842082983923668553788077 315781118971375707670529)
            ·
              refine ⟨236835839228531780752897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315781118971375707670529 236835839228531780752897)
              ·
                refine ⟨177626879421398835564673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236835839228531780752897 177626879421398835564673)
                ·
                  refine ⟨133220159566049126673505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177626879421398835564673 133220159566049126673505)
                  ·
                    rfl

theorem cell20_291876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_291876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291876 prefixEnd_291876 := by exact prefixLift 291876
  have htrace : WordTrace (prefixWord ++ tailWord_291876) baseStart_291876 baseEnd_291876 := by
    simpa [prefixWord, tailWord_291876, baseEnd_291876] using wordTrace_append hprefix tailTrace_291876
  have hstable : (prefixWord ++ tailWord_291876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291876).length < 2 ^ (prefixWord ++ tailWord_291876).sum := by decide
  have hdescent : baseEnd_291876 < baseStart_291876 := by decide
  rcases family_descends (prefixWord ++ tailWord_291876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291884 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_291884 : Nat := 118140960795 + 291884 * 2 ^ 59
def prefixEnd_291884 : Nat := 4983230072969 + 3 ^ 40 * 291884 * 2
def baseEnd_291884 : Nat := 133223810984036654406805

theorem tailTrace_291884 : CollatzResearch.WordTrace tailWord_291884 prefixEnd_291884 133223810984036654406805 := by
  unfold tailWord_291884
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322942037280796331781353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7097256049707728442375137 5322942037280796331781353)
  ·
    refine ⟨3992206527960597248836015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5322942037280796331781353 3992206527960597248836015)
    ·
      refine ⟨5988309791940895873254023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3992206527960597248836015 5988309791940895873254023)
      ·
        refine ⟨8982464687911343809881035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988309791940895873254023 8982464687911343809881035)
        ·
          refine ⟨13473697031867015714821553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8982464687911343809881035 13473697031867015714821553)
          ·
            refine ⟨10105272773900261786116165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13473697031867015714821553 10105272773900261786116165)
            ·
              refine ⟨1894738645106299084896781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10105272773900261786116165 1894738645106299084896781)
              ·
                refine ⟨710526991914862156836293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1894738645106299084896781 710526991914862156836293)
                ·
                  refine ⟨133223810984036654406805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710526991914862156836293 133223810984036654406805)
                  ·
                    rfl

theorem cell20_291884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_291884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291884 prefixEnd_291884 := by exact prefixLift 291884
  have htrace : WordTrace (prefixWord ++ tailWord_291884) baseStart_291884 baseEnd_291884 := by
    simpa [prefixWord, tailWord_291884, baseEnd_291884] using wordTrace_append hprefix tailTrace_291884
  have hstable : (prefixWord ++ tailWord_291884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291884).length < 2 ^ (prefixWord ++ tailWord_291884).sum := by decide
  have hdescent : baseEnd_291884 < baseStart_291884 := by decide
  rcases family_descends (prefixWord ++ tailWord_291884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291901 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_291901 : Nat := 118140960795 + 291901 * 2 ^ 59
def prefixEnd_291901 : Nat := 4983230072969 + 3 ^ 40 * 291901 * 2
def baseEnd_291901 : Nat := 133231570247260150840069

theorem tailTrace_291901 : CollatzResearch.WordTrace tailWord_291901 prefixEnd_291901 133231570247260150840069 := by
  unfold tailWord_291901
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646504115500004566931557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7097669410333336377954371 10646504115500004566931557)
  ·
    refine ⟨1996219521656250856299667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10646504115500004566931557 1996219521656250856299667)
    ·
      refine ⟨2994329282484376284449501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996219521656250856299667 2994329282484376284449501)
      ·
        refine ⟨1122873480931641106668563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2994329282484376284449501 1122873480931641106668563)
        ·
          refine ⟨1684310221397461660002845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122873480931641106668563 1684310221397461660002845)
          ·
            refine ⟨631616333024048122501067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1684310221397461660002845 631616333024048122501067)
            ·
              refine ⟨947424499536072183751601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631616333024048122501067 947424499536072183751601)
              ·
                refine ⟨710568374652054137813701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947424499536072183751601 710568374652054137813701)
                ·
                  refine ⟨133231570247260150840069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710568374652054137813701 133231570247260150840069)
                  ·
                    rfl

theorem cell20_291901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_291901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291901 prefixEnd_291901 := by exact prefixLift 291901
  have htrace : WordTrace (prefixWord ++ tailWord_291901) baseStart_291901 baseEnd_291901 := by
    simpa [prefixWord, tailWord_291901, baseEnd_291901] using wordTrace_append hprefix tailTrace_291901
  have hstable : (prefixWord ++ tailWord_291901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291901).length < 2 ^ (prefixWord ++ tailWord_291901).sum := by decide
  have hdescent : baseEnd_291901 < baseStart_291901 := by decide
  rcases family_descends (prefixWord ++ tailWord_291901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291918 : List Nat := [4, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_291918 : Nat := 118140960795 + 291918 * 2 ^ 59
def prefixEnd_291918 : Nat := 4983230072969 + 3 ^ 40 * 291918 * 2
def baseEnd_291918 : Nat := 133239329510483647273333

theorem tailTrace_291918 : CollatzResearch.WordTrace tailWord_291918 prefixEnd_291918 133239329510483647273333 := by
  unfold tailWord_291918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330890519554802058787551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7098082770958944313533605 1330890519554802058787551)
  ·
    refine ⟨1996335779332203088181327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1330890519554802058787551 1996335779332203088181327)
    ·
      refine ⟨2994503668998304632271991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996335779332203088181327 2994503668998304632271991)
      ·
        refine ⟨4491755503497456948407987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2994503668998304632271991 4491755503497456948407987)
        ·
          refine ⟨6737633255246185422611981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491755503497456948407987 6737633255246185422611981)
          ·
            refine ⟨2526612470717319533479493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6737633255246185422611981 2526612470717319533479493)
            ·
              refine ⟨473739838259497412527405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2526612470717319533479493 473739838259497412527405)
              ·
                refine ⟨177652439347311529697777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473739838259497412527405 177652439347311529697777)
                ·
                  refine ⟨133239329510483647273333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177652439347311529697777 133239329510483647273333)
                  ·
                    rfl

theorem cell20_291918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_291918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291918 prefixEnd_291918 := by exact prefixLift 291918
  have htrace : WordTrace (prefixWord ++ tailWord_291918) baseStart_291918 baseEnd_291918 := by
    simpa [prefixWord, tailWord_291918, baseEnd_291918] using wordTrace_append hprefix tailTrace_291918
  have hstable : (prefixWord ++ tailWord_291918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291918).length < 2 ^ (prefixWord ++ tailWord_291918).sum := by decide
  have hdescent : baseEnd_291918 < baseStart_291918 := by decide
  rcases family_descends (prefixWord ++ tailWord_291918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291949 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 3]
def baseStart_291949 : Nat := 118140960795 + 291949 * 2 ^ 59
def prefixEnd_291949 : Nat := 4983230072969 + 3 ^ 40 * 291949 * 2
def baseEnd_291949 : Nat := 133253478755185317239873

theorem tailTrace_291949 : CollatzResearch.WordTrace tailWord_291949 prefixEnd_291949 133253478755185317239873 := by
  unfold tailWord_291949
  simp only [CollatzResearch.WordTrace]
  refine ⟨10648254819326108764678901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7098836546217405843119267 10648254819326108764678901)
  ·
    refine ⟨998273889311822696688647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10648254819326108764678901 998273889311822696688647)
    ·
      refine ⟨1497410833967734045032971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998273889311822696688647 1497410833967734045032971)
      ·
        refine ⟨2246116250951601067549457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497410833967734045032971 2246116250951601067549457)
        ·
          refine ⟨1684587188213700800662093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2246116250951601067549457 1684587188213700800662093)
          ·
            refine ⟨631720195580137800248285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1684587188213700800662093 631720195580137800248285)
            ·
              refine ⟨236895073342551675093107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631720195580137800248285 236895073342551675093107)
              ·
                refine ⟨355342610013827512639661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236895073342551675093107 355342610013827512639661)
                ·
                  refine ⟨133253478755185317239873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355342610013827512639661 133253478755185317239873)
                  ·
                    rfl

theorem cell20_291949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_291949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291949 prefixEnd_291949 := by exact prefixLift 291949
  have htrace : WordTrace (prefixWord ++ tailWord_291949) baseStart_291949 baseEnd_291949 := by
    simpa [prefixWord, tailWord_291949, baseEnd_291949] using wordTrace_append hprefix tailTrace_291949
  have hstable : (prefixWord ++ tailWord_291949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291949).length < 2 ^ (prefixWord ++ tailWord_291949).sum := by decide
  have hdescent : baseEnd_291949 < baseStart_291949 := by decide
  rcases family_descends (prefixWord ++ tailWord_291949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291960 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_291960 : Nat := 118140960795 + 291960 * 2 ^ 59
def prefixEnd_291960 : Nat := 4983230072969 + 3 ^ 40 * 291960 * 2
def baseEnd_291960 : Nat := 133258499454918167873161

theorem tailTrace_291960 : CollatzResearch.WordTrace tailWord_291960 prefixEnd_291960 133258499454918167873161 := by
  unfold tailWord_291960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324328011143128821664667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7099104014857505095552889 5324328011143128821664667)
  ·
    refine ⟨7986492016714693232497001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5324328011143128821664667 7986492016714693232497001)
    ·
      refine ⟨5989869012536019924372751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7986492016714693232497001 5989869012536019924372751)
      ·
        refine ⟨8984803518804029886559127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5989869012536019924372751 8984803518804029886559127)
        ·
          refine ⟨13477205278206044829838691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8984803518804029886559127 13477205278206044829838691)
          ·
            refine ⟨20215807917309067244758037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13477205278206044829838691 20215807917309067244758037)
            ·
              refine ⟨947615996123862527098033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20215807917309067244758037 947615996123862527098033)
              ·
                refine ⟨710711997092896895323525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947615996123862527098033 710711997092896895323525)
                ·
                  refine ⟨133258499454918167873161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710711997092896895323525 133258499454918167873161)
                  ·
                    rfl

theorem cell20_291960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_291960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291960 prefixEnd_291960 := by exact prefixLift 291960
  have htrace : WordTrace (prefixWord ++ tailWord_291960) baseStart_291960 baseEnd_291960 := by
    simpa [prefixWord, tailWord_291960, baseEnd_291960] using wordTrace_append hprefix tailTrace_291960
  have hstable : (prefixWord ++ tailWord_291960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291960).length < 2 ^ (prefixWord ++ tailWord_291960).sum := by decide
  have hdescent : baseEnd_291960 < baseStart_291960 := by decide
  rcases family_descends (prefixWord ++ tailWord_291960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291973 : List Nat := [1, 3, 1, 1, 6, 2, 1, 3, 2]
def baseStart_291973 : Nat := 118140960795 + 291973 * 2 ^ 59
def prefixEnd_291973 : Nat := 4983230072969 + 3 ^ 40 * 291973 * 2
def baseEnd_291973 : Nat := 133264433009147900439775

theorem tailTrace_291973 : CollatzResearch.WordTrace tailWord_291973 prefixEnd_291973 133264433009147900439775 := by
  unfold tailWord_291973
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649130171239160863552573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7099420114159440575701715 10649130171239160863552573)
  ·
    refine ⟨3993423814214685323832215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10649130171239160863552573 3993423814214685323832215)
    ·
      refine ⟨5990135721322027985748323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993423814214685323832215 5990135721322027985748323)
      ·
        refine ⟨8985203581983041978622485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5990135721322027985748323 8985203581983041978622485)
        ·
          refine ⟨421181417905455092747929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8985203581983041978622485 421181417905455092747929)
          ·
            refine ⟨315886063429091319560947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421181417905455092747929 315886063429091319560947)
            ·
              refine ⟨473829095143636979341421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315886063429091319560947 473829095143636979341421)
              ·
                refine ⟨177685910678863867253033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473829095143636979341421 177685910678863867253033)
                ·
                  refine ⟨133264433009147900439775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177685910678863867253033 133264433009147900439775)
                  ·
                    rfl

theorem cell20_291973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_291973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291973 prefixEnd_291973 := by exact prefixLift 291973
  have htrace : WordTrace (prefixWord ++ tailWord_291973) baseStart_291973 baseEnd_291973 := by
    simpa [prefixWord, tailWord_291973, baseEnd_291973] using wordTrace_append hprefix tailTrace_291973
  have hstable : (prefixWord ++ tailWord_291973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291973).length < 2 ^ (prefixWord ++ tailWord_291973).sum := by decide
  have hdescent : baseEnd_291973 < baseStart_291973 := by decide
  rcases family_descends (prefixWord ++ tailWord_291973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291991 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_291991 : Nat := 118140960795 + 291991 * 2 ^ 59
def prefixEnd_291991 : Nat := 4983230072969 + 3 ^ 40 * 291991 * 2
def baseEnd_291991 : Nat := 133272648699619837839701

theorem tailTrace_291991 : CollatzResearch.WordTrace tailWord_291991 prefixEnd_291991 133272648699619837839701 := by
  unfold tailWord_291991
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649786685173949937707827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7099857790115966625138551 10649786685173949937707827)
  ·
    refine ⟨15974680027760924906561741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10649786685173949937707827 15974680027760924906561741)
    ·
      refine ⟨5990505010410346839960653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15974680027760924906561741 5990505010410346839960653)
      ·
        refine ⟨2246439378903880064985245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5990505010410346839960653 2246439378903880064985245)
        ·
          refine ⟨842414767088955024369467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2246439378903880064985245 842414767088955024369467)
          ·
            refine ⟨1263622150633432536554201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842414767088955024369467 1263622150633432536554201)
            ·
              refine ⟨947716612975074402415651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263622150633432536554201 947716612975074402415651)
              ·
                refine ⟨1421574919462611603623477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947716612975074402415651 1421574919462611603623477)
                ·
                  refine ⟨133272648699619837839701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1421574919462611603623477 133272648699619837839701)
                  ·
                    rfl

theorem cell20_291991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_291991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291991 prefixEnd_291991 := by exact prefixLift 291991
  have htrace : WordTrace (prefixWord ++ tailWord_291991) baseStart_291991 baseEnd_291991 := by
    simpa [prefixWord, tailWord_291991, baseEnd_291991] using wordTrace_append hprefix tailTrace_291991
  have hstable : (prefixWord ++ tailWord_291991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291991).length < 2 ^ (prefixWord ++ tailWord_291991).sum := by decide
  have hdescent : baseEnd_291991 < baseStart_291991 := by decide
  rcases family_descends (prefixWord ++ tailWord_291991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291994 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_291994 : Nat := 118140960795 + 291994 * 2 ^ 59
def prefixEnd_291994 : Nat := 4983230072969 + 3 ^ 40 * 291994 * 2
def baseEnd_291994 : Nat := 133274017981365160739689

theorem tailTrace_291994 : CollatzResearch.WordTrace tailWord_291994 prefixEnd_291994 133274017981365160739689 := by
  unfold tailWord_291994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662474026040770362516759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7099930736108720966711357 2662474026040770362516759)
  ·
    refine ⟨3993711039061155543775139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662474026040770362516759 3993711039061155543775139)
    ·
      refine ⟨5990566558591733315662709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993711039061155543775139 5990566558591733315662709)
      ·
        refine ⟨561615614867974998343379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5990566558591733315662709 561615614867974998343379)
        ·
          refine ⟨842423422301962497515069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561615614867974998343379 842423422301962497515069)
          ·
            refine ⟨315908783363235936568151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 842423422301962497515069 315908783363235936568151)
            ·
              refine ⟨473863175044853904852227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315908783363235936568151 473863175044853904852227)
              ·
                refine ⟨710794762567280857278341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473863175044853904852227 710794762567280857278341)
                ·
                  refine ⟨133274017981365160739689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710794762567280857278341 133274017981365160739689)
                  ·
                    rfl

theorem cell20_291994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_291994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_291994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_291994 prefixEnd_291994 := by exact prefixLift 291994
  have htrace : WordTrace (prefixWord ++ tailWord_291994) baseStart_291994 baseEnd_291994 := by
    simpa [prefixWord, tailWord_291994, baseEnd_291994] using wordTrace_append hprefix tailTrace_291994
  have hstable : (prefixWord ++ tailWord_291994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291994).length < 2 ^ (prefixWord ++ tailWord_291994).sum := by decide
  have hdescent : baseEnd_291994 < baseStart_291994 := by decide
  rcases family_descends (prefixWord ++ tailWord_291994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292005 : List Nat := [1, 3, 1, 2, 1, 4, 1, 7]
def baseStart_292005 : Nat := 118140960795 + 292005 * 2 ^ 59
def prefixEnd_292005 : Nat := 4983230072969 + 3 ^ 40 * 292005 * 2
def baseEnd_292005 : Nat := 44426346227032670457659

theorem tailTrace_292005 : CollatzResearch.WordTrace tailWord_292005 prefixEnd_292005 44426346227032670457659 := by
  unfold tailWord_292005
  simp only [CollatzResearch.WordTrace]
  refine ⟨10650297307123230328717469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7100198204748820219144979 10650297307123230328717469)
  ·
    refine ⟨3993861490171211373269051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10650297307123230328717469 3993861490171211373269051)
    ·
      refine ⟨5990792235256817059903577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993861490171211373269051 5990792235256817059903577)
      ·
        refine ⟨4493094176442612794927683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5990792235256817059903577 4493094176442612794927683)
        ·
          refine ⟨6739641264663919192391525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493094176442612794927683 6739641264663919192391525)
          ·
            refine ⟨1263682737124484848573411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6739641264663919192391525 1263682737124484848573411)
            ·
              refine ⟨1895524105686727272860117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263682737124484848573411 1895524105686727272860117)
              ·
                refine ⟨44426346227032670457659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1895524105686727272860117 44426346227032670457659)
                ·
                  rfl

theorem cell20_292005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_292005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292005 prefixEnd_292005 := by exact prefixLift 292005
  have htrace : WordTrace (prefixWord ++ tailWord_292005) baseStart_292005 baseEnd_292005 := by
    simpa [prefixWord, tailWord_292005, baseEnd_292005] using wordTrace_append hprefix tailTrace_292005
  have hstable : (prefixWord ++ tailWord_292005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292005).length < 2 ^ (prefixWord ++ tailWord_292005).sum := by decide
  have hdescent : baseEnd_292005 < baseStart_292005 := by decide
  rcases family_descends (prefixWord ++ tailWord_292005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292012 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_292012 : Nat := 118140960795 + 292012 * 2 ^ 59
def prefixEnd_292012 : Nat := 4983230072969 + 3 ^ 40 * 292012 * 2
def baseEnd_292012 : Nat := 133282233671837098139615

theorem tailTrace_292012 : CollatzResearch.WordTrace tailWord_292012 prefixEnd_292012 133282233671837098139615 := by
  unfold tailWord_292012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325276309048935262111145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7100368412065247016148193 5325276309048935262111145)
  ·
    refine ⟨3993957231786701446583359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5325276309048935262111145 3993957231786701446583359)
    ·
      refine ⟨5990935847680052169875039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993957231786701446583359 5990935847680052169875039)
      ·
        refine ⟨8986403771520078254812559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5990935847680052169875039 8986403771520078254812559)
        ·
          refine ⟨13479605657280117382218839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8986403771520078254812559 13479605657280117382218839)
          ·
            refine ⟨20219408485920176073328259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13479605657280117382218839 20219408485920176073328259)
            ·
              refine ⟨30329112728880264109992389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20219408485920176073328259 30329112728880264109992389)
              ·
                refine ⟨5686708636665049520623573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30329112728880264109992389 5686708636665049520623573)
                ·
                  refine ⟨133282233671837098139615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5686708636665049520623573 133282233671837098139615)
                  ·
                    rfl

theorem cell20_292012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_292012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292012 prefixEnd_292012 := by exact prefixLift 292012
  have htrace : WordTrace (prefixWord ++ tailWord_292012) baseStart_292012 baseEnd_292012 := by
    simpa [prefixWord, tailWord_292012, baseEnd_292012] using wordTrace_append hprefix tailTrace_292012
  have hstable : (prefixWord ++ tailWord_292012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292012).length < 2 ^ (prefixWord ++ tailWord_292012).sum := by decide
  have hdescent : baseEnd_292012 < baseStart_292012 := by decide
  rcases family_descends (prefixWord ++ tailWord_292012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292074 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_292074 : Nat := 118140960795 + 292074 * 2 ^ 59
def prefixEnd_292074 : Nat := 4983230072969 + 3 ^ 40 * 292074 * 2
def baseEnd_292074 : Nat := 133310532161240438072695

theorem tailTrace_292074 : CollatzResearch.WordTrace tailWord_292074 prefixEnd_292074 133310532161240438072695 := by
  unfold tailWord_292074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663203485968313778244819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7101875962582170075319517 2663203485968313778244819)
  ·
    refine ⟨3994805228952470667367229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663203485968313778244819 3994805228952470667367229)
    ·
      refine ⟨1498051960857176500262711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3994805228952470667367229 1498051960857176500262711)
      ·
        refine ⟨2247077941285764750394067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498051960857176500262711 2247077941285764750394067)
        ·
          refine ⟨3370616911928647125591101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247077941285764750394067 3370616911928647125591101)
          ·
            refine ⟨1263981341973242672096663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3370616911928647125591101 1263981341973242672096663)
            ·
              refine ⟨1895972012959864008144995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263981341973242672096663 1895972012959864008144995)
              ·
                refine ⟨2843958019439796012217493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895972012959864008144995 2843958019439796012217493)
                ·
                  refine ⟨133310532161240438072695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2843958019439796012217493 133310532161240438072695)
                  ·
                    rfl

theorem cell20_292074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_292074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292074 prefixEnd_292074 := by exact prefixLift 292074
  have htrace : WordTrace (prefixWord ++ tailWord_292074) baseStart_292074 baseEnd_292074 := by
    simpa [prefixWord, tailWord_292074, baseEnd_292074] using wordTrace_append hprefix tailTrace_292074
  have hstable : (prefixWord ++ tailWord_292074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292074).length < 2 ^ (prefixWord ++ tailWord_292074).sum := by decide
  have hdescent : baseEnd_292074 < baseStart_292074 := by decide
  rcases family_descends (prefixWord ++ tailWord_292074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292077 : List Nat := [1, 5, 1, 2, 2, 2, 3, 4]
def baseStart_292077 : Nat := 118140960795 + 292077 * 2 ^ 59
def prefixEnd_292077 : Nat := 4983230072969 + 3 ^ 40 * 292077 * 2
def baseEnd_292077 : Nat := 44437300480995253657561

theorem tailTrace_292077 : CollatzResearch.WordTrace tailWord_292077 prefixEnd_292077 44437300480995253657561 := by
  unfold tailWord_292077
  simp only [CollatzResearch.WordTrace]
  refine ⟨10652923362862386625338485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7101948908574924416892323 10652923362862386625338485)
  ·
    refine ⟨998711565268348746125483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10652923362862386625338485 998711565268348746125483)
    ·
      refine ⟨1498067347902523119188225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998711565268348746125483 1498067347902523119188225)
      ·
        refine ⟨1123550510926892339391169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1498067347902523119188225 1123550510926892339391169)
        ·
          refine ⟨842662883195169254543377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123550510926892339391169 842662883195169254543377)
          ·
            refine ⟨631997162396376940907533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842662883195169254543377 631997162396376940907533)
            ·
              refine ⟨236998935898641352840325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631997162396376940907533 236998935898641352840325)
              ·
                refine ⟨44437300480995253657561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236998935898641352840325 44437300480995253657561)
                ·
                  rfl

theorem cell20_292077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_292077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292077 prefixEnd_292077 := by exact prefixLift 292077
  have htrace : WordTrace (prefixWord ++ tailWord_292077) baseStart_292077 baseEnd_292077 := by
    simpa [prefixWord, tailWord_292077, baseEnd_292077] using wordTrace_append hprefix tailTrace_292077
  have hstable : (prefixWord ++ tailWord_292077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292077).length < 2 ^ (prefixWord ++ tailWord_292077).sum := by decide
  have hdescent : baseEnd_292077 < baseStart_292077 := by decide
  rcases family_descends (prefixWord ++ tailWord_292077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292119 : List Nat := [1, 1, 3, 4, 1, 1, 2, 7]
def baseStart_292119 : Nat := 118140960795 + 292119 * 2 ^ 59
def prefixEnd_292119 : Nat := 4983230072969 + 3 ^ 40 * 292119 * 2
def baseEnd_292119 : Nat := 44443690462473427190837

theorem tailTrace_292119 : CollatzResearch.WordTrace tailWord_292119 prefixEnd_292119 44443690462473427190837 := by
  unfold tailWord_292119
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654455228710227798367411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7102970152473485198911607 10654455228710227798367411)
  ·
    refine ⟨15981682843065341697551117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10654455228710227798367411 15981682843065341697551117)
    ·
      refine ⟨5993131066149503136581669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15981682843065341697551117 5993131066149503136581669)
      ·
        refine ⟨1123712074903031838109063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5993131066149503136581669 1123712074903031838109063)
        ·
          refine ⟨1685568112354547757163595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123712074903031838109063 1685568112354547757163595)
          ·
            refine ⟨2528352168531821635745393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685568112354547757163595 2528352168531821635745393)
            ·
              refine ⟨1896264126398866226809045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528352168531821635745393 1896264126398866226809045)
              ·
                refine ⟨44443690462473427190837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1896264126398866226809045 44443690462473427190837)
                ·
                  rfl

theorem cell20_292119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_292119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292119 prefixEnd_292119 := by exact prefixLift 292119
  have htrace : WordTrace (prefixWord ++ tailWord_292119) baseStart_292119 baseEnd_292119 := by
    simpa [prefixWord, tailWord_292119, baseEnd_292119] using wordTrace_append hprefix tailTrace_292119
  have hstable : (prefixWord ++ tailWord_292119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292119).length < 2 ^ (prefixWord ++ tailWord_292119).sum := by decide
  have hdescent : baseEnd_292119 < baseStart_292119 := by decide
  rcases family_descends (prefixWord ++ tailWord_292119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292136 : List Nat := [2, 1, 5, 1, 2, 2, 1, 6]
def baseStart_292136 : Nat := 118140960795 + 292136 * 2 ^ 59
def prefixEnd_292136 : Nat := 4983230072969 + 3 ^ 40 * 292136 * 2
def baseEnd_292136 : Nat := 44446276883547926001925

theorem tailTrace_292136 : CollatzResearch.WordTrace tailWord_292136 prefixEnd_292136 44446276883547926001925 := by
  unfold tailWord_292136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327537634824319850868131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7103383513099093134490841 5327537634824319850868131)
  ·
    refine ⟨7991306452236479776302197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5327537634824319850868131 7991306452236479776302197)
    ·
      refine ⟨749184979897169979028331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7991306452236479776302197 749184979897169979028331)
      ·
        refine ⟨1123777469845754968542497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749184979897169979028331 1123777469845754968542497)
        ·
          refine ⟨842833102384316226406873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123777469845754968542497 842833102384316226406873)
          ·
            refine ⟨632124826788237169805155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842833102384316226406873 632124826788237169805155)
            ·
              refine ⟨948187240182355754707733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632124826788237169805155 948187240182355754707733)
              ·
                refine ⟨44446276883547926001925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 948187240182355754707733 44446276883547926001925)
                ·
                  rfl

theorem cell20_292136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_292136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292136 prefixEnd_292136 := by exact prefixLift 292136
  have htrace : WordTrace (prefixWord ++ tailWord_292136) baseStart_292136 baseEnd_292136 := by
    simpa [prefixWord, tailWord_292136, baseEnd_292136] using wordTrace_append hprefix tailTrace_292136
  have hstable : (prefixWord ++ tailWord_292136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292136).length < 2 ^ (prefixWord ++ tailWord_292136).sum := by decide
  have hdescent : baseEnd_292136 < baseStart_292136 := by decide
  rcases family_descends (prefixWord ++ tailWord_292136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292146 : List Nat := [3, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_292146 : Nat := 118140960795 + 292146 * 2 ^ 59
def prefixEnd_292146 : Nat := 4983230072969 + 3 ^ 40 * 292146 * 2
def baseEnd_292146 : Nat := 133343394923128187672401

theorem tailTrace_292146 : CollatzResearch.WordTrace tailWord_292146 prefixEnd_292146 133343394923128187672401 := by
  unfold tailWord_292146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663859999903102852400073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7103626666408274273066861 2663859999903102852400073)
  ·
    refine ⟨1997894999927327139300055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2663859999903102852400073 1997894999927327139300055)
    ·
      refine ⟨2996842499890990708950083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1997894999927327139300055 2996842499890990708950083)
      ·
        refine ⟨4495263749836486063425125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996842499890990708950083 4495263749836486063425125)
        ·
          refine ⟨842861953094341136892211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4495263749836486063425125 842861953094341136892211)
          ·
            refine ⟨1264292929641511705338317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842861953094341136892211 1264292929641511705338317)
            ·
              refine ⟨474109848615566889501869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264292929641511705338317 474109848615566889501869)
              ·
                refine ⟨177791193230837583563201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 474109848615566889501869 177791193230837583563201)
                ·
                  refine ⟨133343394923128187672401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177791193230837583563201 133343394923128187672401)
                  ·
                    rfl

theorem cell20_292146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_292146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292146 prefixEnd_292146 := by exact prefixLift 292146
  have htrace : WordTrace (prefixWord ++ tailWord_292146) baseStart_292146 baseEnd_292146 := by
    simpa [prefixWord, tailWord_292146, baseEnd_292146] using wordTrace_append hprefix tailTrace_292146
  have hstable : (prefixWord ++ tailWord_292146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292146).length < 2 ^ (prefixWord ++ tailWord_292146).sum := by decide
  have hdescent : baseEnd_292146 < baseStart_292146 := by decide
  rcases family_descends (prefixWord ++ tailWord_292146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292153 : List Nat := [1, 2, 1, 6, 3, 1, 6]
def baseStart_292153 : Nat := 118140960795 + 292153 * 2 ^ 59
def prefixEnd_292153 : Nat := 4983230072969 + 3 ^ 40 * 292153 * 2
def baseEnd_292153 : Nat := 14816287768207474937671

theorem tailTrace_292153 : CollatzResearch.WordTrace tailWord_292153 prefixEnd_292153 14816287768207474937671 := by
  unfold tailWord_292153
  simp only [CollatzResearch.WordTrace]
  refine ⟨10655695310587051605105113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7103796873724701070070075 10655695310587051605105113)
  ·
    refine ⟨7991771482940288703828835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10655695310587051605105113 7991771482940288703828835)
    ·
      refine ⟨11987657224410433055743253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7991771482940288703828835 11987657224410433055743253)
      ·
        refine ⟨561921432394239049487965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11987657224410433055743253 561921432394239049487965)
        ·
          refine ⟨210720537147839643557987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 561921432394239049487965 210720537147839643557987)
          ·
            refine ⟨316080805721759465336981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210720537147839643557987 316080805721759465336981)
            ·
              refine ⟨14816287768207474937671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 316080805721759465336981 14816287768207474937671)
              ·
                rfl

theorem cell20_292153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 6].length) (baseStart_292153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292153 prefixEnd_292153 := by exact prefixLift 292153
  have htrace : WordTrace (prefixWord ++ tailWord_292153) baseStart_292153 baseEnd_292153 := by
    simpa [prefixWord, tailWord_292153, baseEnd_292153] using wordTrace_append hprefix tailTrace_292153
  have hstable : (prefixWord ++ tailWord_292153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292153).length < 2 ^ (prefixWord ++ tailWord_292153).sum := by decide
  have hdescent : baseEnd_292153 < baseStart_292153 := by decide
  rcases family_descends (prefixWord ++ tailWord_292153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292167 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 4]
def baseStart_292167 : Nat := 118140960795 + 292167 * 2 ^ 59
def prefixEnd_292167 : Nat := 4983230072969 + 3 ^ 40 * 292167 * 2
def baseEnd_292167 : Nat := 133352979895345447972315

theorem tailTrace_292167 : CollatzResearch.WordTrace tailWord_292167 prefixEnd_292167 133352979895345447972315 := by
  unfold tailWord_292167
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656205932536331996114755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7104137288357554664076503 10656205932536331996114755)
  ·
    refine ⟨15984308898804497994172133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10656205932536331996114755 15984308898804497994172133)
    ·
      refine ⟨2997057918525843373907275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15984308898804497994172133 2997057918525843373907275)
      ·
        refine ⟨4495586877788765060860913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997057918525843373907275 4495586877788765060860913)
        ·
          refine ⟨3371690158341573795645685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4495586877788765060860913 3371690158341573795645685)
          ·
            refine ⟨316095952344522543341783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3371690158341573795645685 316095952344522543341783)
            ·
              refine ⟨474143928516783815012675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316095952344522543341783 474143928516783815012675)
              ·
                refine ⟨711215892775175722519013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474143928516783815012675 711215892775175722519013)
                ·
                  refine ⟨133352979895345447972315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711215892775175722519013 133352979895345447972315)
                  ·
                    rfl

theorem cell20_292167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_292167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292167 prefixEnd_292167 := by exact prefixLift 292167
  have htrace : WordTrace (prefixWord ++ tailWord_292167) baseStart_292167 baseEnd_292167 := by
    simpa [prefixWord, tailWord_292167, baseEnd_292167] using wordTrace_append hprefix tailTrace_292167
  have hstable : (prefixWord ++ tailWord_292167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292167).length < 2 ^ (prefixWord ++ tailWord_292167).sum := by decide
  have hdescent : baseEnd_292167 < baseStart_292167 := by decide
  rcases family_descends (prefixWord ++ tailWord_292167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292173 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 3]
def baseStart_292173 : Nat := 118140960795 + 292173 * 2 ^ 59
def prefixEnd_292173 : Nat := 4983230072969 + 3 ^ 40 * 292173 * 2
def baseEnd_292173 : Nat := 133355718458836093772291

theorem tailTrace_292173 : CollatzResearch.WordTrace tailWord_292173 prefixEnd_292173 133355718458836093772291 := by
  unfold tailWord_292173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656424770514595020833173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7104283180343063347222115 10656424770514595020833173)
  ·
    refine ⟨499519911117871641601555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10656424770514595020833173 499519911117871641601555)
    ·
      refine ⟨749279866676807462402333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499519911117871641601555 749279866676807462402333)
      ·
        refine ⟨280979950003802798400875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 749279866676807462402333 280979950003802798400875)
        ·
          refine ⟨421469925005704197601313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280979950003802798400875 421469925005704197601313)
          ·
            refine ⟨316102443754278148200985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421469925005704197601313 316102443754278148200985)
            ·
              refine ⟨237076832815708611150739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316102443754278148200985 237076832815708611150739)
              ·
                refine ⟨355615249223562916726109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237076832815708611150739 355615249223562916726109)
                ·
                  refine ⟨133355718458836093772291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355615249223562916726109 133355718458836093772291)
                  ·
                    rfl

theorem cell20_292173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_292173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292173 prefixEnd_292173 := by exact prefixLift 292173
  have htrace : WordTrace (prefixWord ++ tailWord_292173) baseStart_292173 baseEnd_292173 := by
    simpa [prefixWord, tailWord_292173, baseEnd_292173] using wordTrace_append hprefix tailTrace_292173
  have hstable : (prefixWord ++ tailWord_292173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292173).length < 2 ^ (prefixWord ++ tailWord_292173).sum := by decide
  have hdescent : baseEnd_292173 < baseStart_292173 := by decide
  rcases family_descends (prefixWord ++ tailWord_292173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292195 : List Nat := [1, 1, 1, 5, 2, 2, 2, 6]
def baseStart_292195 : Nat := 118140960795 + 292195 * 2 ^ 59
def prefixEnd_292195 : Nat := 4983230072969 + 3 ^ 40 * 292195 * 2
def baseEnd_292195 : Nat := 44455253286100598346289

theorem tailTrace_292195 : CollatzResearch.WordTrace tailWord_292195 prefixEnd_292195 44455253286100598346289 := by
  unfold tailWord_292195
  simp only [CollatzResearch.WordTrace]
  refine ⟨10657227176434892778134039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7104818117623261852089359 10657227176434892778134039)
  ·
    refine ⟨15985840764652339167201059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10657227176434892778134039 15985840764652339167201059)
    ·
      refine ⟨23978761146978508750801589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15985840764652339167201059 23978761146978508750801589)
      ·
        refine ⟨2248008857529235195387649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23978761146978508750801589 2248008857529235195387649)
        ·
          refine ⟨1686006643146926396540737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2248008857529235195387649 1686006643146926396540737)
          ·
            refine ⟨1264504982360194797405553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686006643146926396540737 1264504982360194797405553)
            ·
              refine ⟨948378736770146098054165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264504982360194797405553 948378736770146098054165)
              ·
                refine ⟨44455253286100598346289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 948378736770146098054165 44455253286100598346289)
                ·
                  rfl

theorem cell20_292195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_292195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292195 prefixEnd_292195 := by exact prefixLift 292195
  have htrace : WordTrace (prefixWord ++ tailWord_292195) baseStart_292195 baseEnd_292195 := by
    simpa [prefixWord, tailWord_292195, baseEnd_292195] using wordTrace_append hprefix tailTrace_292195
  have hstable : (prefixWord ++ tailWord_292195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292195).length < 2 ^ (prefixWord ++ tailWord_292195).sum := by decide
  have hdescent : baseEnd_292195 < baseStart_292195 := by decide
  rcases family_descends (prefixWord ++ tailWord_292195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292219 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 3]
def baseStart_292219 : Nat := 118140960795 + 292219 * 2 ^ 59
def prefixEnd_292219 : Nat := 4983230072969 + 3 ^ 40 * 292219 * 2
def baseEnd_292219 : Nat := 133376714112264378238769

theorem tailTrace_292219 : CollatzResearch.WordTrace tailWord_292219 prefixEnd_292219 133376714112264378238769 := by
  unfold tailWord_292219
  simp only [CollatzResearch.WordTrace]
  refine ⟨10658102528347944877007711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7105401685565296584671807 10658102528347944877007711)
  ·
    refine ⟨15987153792521917315511567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10658102528347944877007711 15987153792521917315511567)
    ·
      refine ⟨23980730688782875973267351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15987153792521917315511567 23980730688782875973267351)
      ·
        refine ⟨35971096033174313959901027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23980730688782875973267351 35971096033174313959901027)
        ·
          refine ⟨53956644049761470939851541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35971096033174313959901027 53956644049761470939851541)
          ·
            refine ⟨2529217689832568950305541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53956644049761470939851541 2529217689832568950305541)
            ·
              refine ⟨474228316843606678182289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2529217689832568950305541 474228316843606678182289)
              ·
                refine ⟨355671237632705008636717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474228316843606678182289 355671237632705008636717)
                ·
                  refine ⟨133376714112264378238769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355671237632705008636717 133376714112264378238769)
                  ·
                    rfl

theorem cell20_292219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_292219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292219 prefixEnd_292219 := by exact prefixLift 292219
  have htrace : WordTrace (prefixWord ++ tailWord_292219) baseStart_292219 baseEnd_292219 := by
    simpa [prefixWord, tailWord_292219, baseEnd_292219] using wordTrace_append hprefix tailTrace_292219
  have hstable : (prefixWord ++ tailWord_292219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292219).length < 2 ^ (prefixWord ++ tailWord_292219).sum := by decide
  have hdescent : baseEnd_292219 < baseStart_292219 := by decide
  rcases family_descends (prefixWord ++ tailWord_292219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292250 : List Nat := [3, 1, 1, 4, 1, 1, 5, 4]
def baseStart_292250 : Nat := 118140960795 + 292250 * 2 ^ 59
def prefixEnd_292250 : Nat := 4983230072969 + 3 ^ 40 * 292250 * 2
def baseEnd_292250 : Nat := 44463621118988682735103

theorem tailTrace_292250 : CollatzResearch.WordTrace tailWord_292250 prefixEnd_292250 44463621118988682735103 := by
  unfold tailWord_292250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664808297808909292846551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7106155460823758114257469 2664808297808909292846551)
  ·
    refine ⟨3997212446713363939269827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2664808297808909292846551 3997212446713363939269827)
    ·
      refine ⟨5995818670070045908904741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3997212446713363939269827 5995818670070045908904741)
      ·
        refine ⟨1124216000638133607919639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5995818670070045908904741 1124216000638133607919639)
        ·
          refine ⟨1686324000957200411879459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124216000638133607919639 1686324000957200411879459)
          ·
            refine ⟨2529486001435800617819189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686324000957200411879459 2529486001435800617819189)
            ·
              refine ⟨237139312634606307920549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2529486001435800617819189 237139312634606307920549)
              ·
                refine ⟨44463621118988682735103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 237139312634606307920549 44463621118988682735103)
                ·
                  rfl

theorem cell20_292250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_292250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292250 prefixEnd_292250 := by exact prefixLift 292250
  have htrace : WordTrace (prefixWord ++ tailWord_292250) baseStart_292250 baseEnd_292250 := by
    simpa [prefixWord, tailWord_292250, baseEnd_292250] using wordTrace_append hprefix tailTrace_292250
  have hstable : (prefixWord ++ tailWord_292250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292250).length < 2 ^ (prefixWord ++ tailWord_292250).sum := by decide
  have hdescent : baseEnd_292250 < baseStart_292250 := by decide
  rcases family_descends (prefixWord ++ tailWord_292250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292281 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 4]
def baseStart_292281 : Nat := 118140960795 + 292281 * 2 ^ 59
def prefixEnd_292281 : Nat := 4983230072969 + 3 ^ 40 * 292281 * 2
def baseEnd_292281 : Nat := 133405012601667718171849

theorem tailTrace_292281 : CollatzResearch.WordTrace tailWord_292281 prefixEnd_292281 133405012601667718171849 := by
  unfold tailWord_292281
  simp only [CollatzResearch.WordTrace]
  refine ⟨10660363854123329465764697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7106909236082219643843131 10660363854123329465764697)
  ·
    refine ⟨7995272890592497099323523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10660363854123329465764697 7995272890592497099323523)
    ·
      refine ⟨11992909335888745648985285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7995272890592497099323523 11992909335888745648985285)
      ·
        refine ⟨2248670500479139809184741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11992909335888745648985285 2248670500479139809184741)
        ·
          refine ⟨421625718839838714222139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2248670500479139809184741 421625718839838714222139)
          ·
            refine ⟨632438578259758071333209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421625718839838714222139 632438578259758071333209)
            ·
              refine ⟨474328933694818553499907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632438578259758071333209 474328933694818553499907)
              ·
                refine ⟨711493400542227830249861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474328933694818553499907 711493400542227830249861)
                ·
                  refine ⟨133405012601667718171849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711493400542227830249861 133405012601667718171849)
                  ·
                    rfl

theorem cell20_292281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_292281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292281 prefixEnd_292281 := by exact prefixLift 292281
  have htrace : WordTrace (prefixWord ++ tailWord_292281) baseStart_292281 baseEnd_292281 := by
    simpa [prefixWord, tailWord_292281, baseEnd_292281] using wordTrace_append hprefix tailTrace_292281
  have hstable : (prefixWord ++ tailWord_292281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292281).length < 2 ^ (prefixWord ++ tailWord_292281).sum := by decide
  have hdescent : baseEnd_292281 < baseStart_292281 := by decide
  rcases family_descends (prefixWord ++ tailWord_292281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292302 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_292302 : Nat := 118140960795 + 292302 * 2 ^ 59
def prefixEnd_292302 : Nat := 4983230072969 + 3 ^ 40 * 292302 * 2
def baseEnd_292302 : Nat := 133414597573884978471763

theorem tailTrace_292302 : CollatzResearch.WordTrace tailWord_292302 prefixEnd_292302 133414597573884978471763 := by
  unfold tailWord_292302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1332641223380906256534895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7107419858031500034852773 1332641223380906256534895)
  ·
    refine ⟨1998961835071359384802343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1332641223380906256534895 1998961835071359384802343)
    ·
      refine ⟨2998442752607039077203515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1998961835071359384802343 2998442752607039077203515)
      ·
        refine ⟨4497664128910558615805273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2998442752607039077203515 4497664128910558615805273)
        ·
          refine ⟨3373248096682918961853955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4497664128910558615805273 3373248096682918961853955)
          ·
            refine ⟨5059872145024378442780933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373248096682918961853955 5059872145024378442780933)
            ·
              refine ⟨948726027192070958021425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5059872145024378442780933 948726027192070958021425)
              ·
                refine ⟨711544520394053218516069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948726027192070958021425 711544520394053218516069)
                ·
                  refine ⟨133414597573884978471763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711544520394053218516069 133414597573884978471763)
                  ·
                    rfl

theorem cell20_292302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_292302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292302 prefixEnd_292302 := by exact prefixLift 292302
  have htrace : WordTrace (prefixWord ++ tailWord_292302) baseStart_292302 baseEnd_292302 := by
    simpa [prefixWord, tailWord_292302, baseEnd_292302] using wordTrace_append hprefix tailTrace_292302
  have hstable : (prefixWord ++ tailWord_292302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292302).length < 2 ^ (prefixWord ++ tailWord_292302).sum := by decide
  have hdescent : baseEnd_292302 < baseStart_292302 := by decide
  rcases family_descends (prefixWord ++ tailWord_292302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292309 : List Nat := [1, 3, 2, 3, 1, 1, 3, 6]
def baseStart_292309 : Nat := 118140960795 + 292309 * 2 ^ 59
def prefixEnd_292309 : Nat := 4983230072969 + 3 ^ 40 * 292309 * 2
def baseEnd_292309 : Nat := 44472597521541355079467

theorem tailTrace_292309 : CollatzResearch.WordTrace tailWord_292309 prefixEnd_292309 44472597521541355079467 := by
  unfold tailWord_292309
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661385098021890247783981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7107590065347926831855987 10661385098021890247783981)
  ·
    refine ⟨3998019411758208842918993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10661385098021890247783981 3998019411758208842918993)
    ·
      refine ⟨2998514558818656632189245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3998019411758208842918993 2998514558818656632189245)
      ·
        refine ⟨1124442959556996237070967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2998514558818656632189245 1124442959556996237070967)
        ·
          refine ⟨1686664439335494355606451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124442959556996237070967 1686664439335494355606451)
          ·
            refine ⟨2529996659003241533409677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686664439335494355606451 2529996659003241533409677)
            ·
              refine ⟨948748747126215575028629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2529996659003241533409677 948748747126215575028629)
              ·
                refine ⟨44472597521541355079467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 948748747126215575028629 44472597521541355079467)
                ·
                  rfl

theorem cell20_292309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_292309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292309 prefixEnd_292309 := by exact prefixLift 292309
  have htrace : WordTrace (prefixWord ++ tailWord_292309) baseStart_292309 baseEnd_292309 := by
    simpa [prefixWord, tailWord_292309, baseEnd_292309] using wordTrace_append hprefix tailTrace_292309
  have hstable : (prefixWord ++ tailWord_292309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292309).length < 2 ^ (prefixWord ++ tailWord_292309).sum := by decide
  have hdescent : baseEnd_292309 < baseStart_292309 := by decide
  rcases family_descends (prefixWord ++ tailWord_292309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292336 : List Nat := [2, 1, 1, 1, 3, 5, 3, 2, 2]
def baseStart_292336 : Nat := 118140960795 + 292336 * 2 ^ 59
def prefixEnd_292336 : Nat := 4983230072969 + 3 ^ 40 * 292336 * 2
def baseEnd_292336 : Nat := 133430116100331971338291

theorem tailTrace_292336 : CollatzResearch.WordTrace tailWord_292336 prefixEnd_292336 133430116100331971338291 := by
  unfold tailWord_292336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5331184934462036929508431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7108246579282715906011241 5331184934462036929508431)
  ·
    refine ⟨7996777401693055394262647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5331184934462036929508431 7996777401693055394262647)
    ·
      refine ⟨11995166102539583091393971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7996777401693055394262647 11995166102539583091393971)
      ·
        refine ⟨17992749153809374637090957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11995166102539583091393971 17992749153809374637090957)
        ·
          refine ⟨6747280932678515488909109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17992749153809374637090957 6747280932678515488909109)
          ·
            refine ⟨632557587438610827085229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6747280932678515488909109 632557587438610827085229)
            ·
              refine ⟨237209095289479060156961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 632557587438610827085229 237209095289479060156961)
              ·
                refine ⟨177906821467109295117721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237209095289479060156961 177906821467109295117721)
                ·
                  refine ⟨133430116100331971338291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177906821467109295117721 133430116100331971338291)
                  ·
                    rfl

theorem cell20_292336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_292336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292336 prefixEnd_292336 := by exact prefixLift 292336
  have htrace : WordTrace (prefixWord ++ tailWord_292336) baseStart_292336 baseEnd_292336 := by
    simpa [prefixWord, tailWord_292336, baseEnd_292336] using wordTrace_append hprefix tailTrace_292336
  have hstable : (prefixWord ++ tailWord_292336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292336).length < 2 ^ (prefixWord ++ tailWord_292336).sum := by decide
  have hdescent : baseEnd_292336 < baseStart_292336 := by decide
  rcases family_descends (prefixWord ++ tailWord_292336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292361 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_292361 : Nat := 118140960795 + 292361 * 2 ^ 59
def prefixEnd_292361 : Nat := 4983230072969 + 3 ^ 40 * 292361 * 2
def baseEnd_292361 : Nat := 133441526781542995504855

theorem tailTrace_292361 : CollatzResearch.WordTrace tailWord_292361 prefixEnd_292361 133441526781542995504855 := by
  unfold tailWord_292361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10663281693833503128676937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7108854462555668752451291 10663281693833503128676937)
  ·
    refine ⟨7997461270375127346507703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10663281693833503128676937 7997461270375127346507703)
    ·
      refine ⟨11996191905562691019761555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7997461270375127346507703 11996191905562691019761555)
      ·
        refine ⟨17994287858344036529642333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11996191905562691019761555 17994287858344036529642333)
        ·
          refine ⟨6747857946879013698615875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17994287858344036529642333 6747857946879013698615875)
          ·
            refine ⟨10121786920318520547923813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6747857946879013698615875 10121786920318520547923813)
            ·
              refine ⟨1897835047559722602735715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10121786920318520547923813 1897835047559722602735715)
              ·
                refine ⟨2846752571339583904103573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897835047559722602735715 2846752571339583904103573)
                ·
                  refine ⟨133441526781542995504855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2846752571339583904103573 133441526781542995504855)
                  ·
                    rfl

theorem cell20_292361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_292361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292361 prefixEnd_292361 := by exact prefixLift 292361
  have htrace : WordTrace (prefixWord ++ tailWord_292361) baseStart_292361 baseEnd_292361 := by
    simpa [prefixWord, tailWord_292361, baseEnd_292361] using wordTrace_append hprefix tailTrace_292361
  have hstable : (prefixWord ++ tailWord_292361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292361).length < 2 ^ (prefixWord ++ tailWord_292361).sum := by decide
  have hdescent : baseEnd_292361 < baseStart_292361 := by decide
  rcases family_descends (prefixWord ++ tailWord_292361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292409 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 3]
def baseStart_292409 : Nat := 118140960795 + 292409 * 2 ^ 59
def prefixEnd_292409 : Nat := 4983230072969 + 3 ^ 40 * 292409 * 2
def baseEnd_292409 : Nat := 133463435289468161904659

theorem tailTrace_292409 : CollatzResearch.WordTrace tailWord_292409 prefixEnd_292409 133463435289468161904659 := by
  unfold tailWord_292409
  simp only [CollatzResearch.WordTrace]
  refine ⟨10665032397659607326424281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7110021598439738217616187 10665032397659607326424281)
  ·
    refine ⟨7998774298244705494818211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10665032397659607326424281 7998774298244705494818211)
    ·
      refine ⟨11998161447367058242227317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7998774298244705494818211 11998161447367058242227317)
      ·
        refine ⟨1124827635690661710208811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11998161447367058242227317 1124827635690661710208811)
        ·
          refine ⟨1687241453535992565313217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124827635690661710208811 1687241453535992565313217)
          ·
            refine ⟨1265431090151994423984913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687241453535992565313217 1265431090151994423984913)
            ·
              refine ⟨949073317613995817988685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265431090151994423984913 949073317613995817988685)
              ·
                refine ⟨355902494105248431745757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 949073317613995817988685 355902494105248431745757)
                ·
                  refine ⟨133463435289468161904659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355902494105248431745757 133463435289468161904659)
                  ·
                    rfl

theorem cell20_292409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_292409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292409 prefixEnd_292409 := by exact prefixLift 292409
  have htrace : WordTrace (prefixWord ++ tailWord_292409) baseStart_292409 baseEnd_292409 := by
    simpa [prefixWord, tailWord_292409, baseEnd_292409] using wordTrace_append hprefix tailTrace_292409
  have hstable : (prefixWord ++ tailWord_292409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292409).length < 2 ^ (prefixWord ++ tailWord_292409).sum := by decide
  have hdescent : baseEnd_292409 < baseStart_292409 := by decide
  rcases family_descends (prefixWord ++ tailWord_292409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
