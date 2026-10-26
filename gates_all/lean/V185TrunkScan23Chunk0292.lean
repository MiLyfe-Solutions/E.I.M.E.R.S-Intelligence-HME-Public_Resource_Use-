import V185TrunkScan23Chunk0291

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1726958 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_1726958 : Nat := 118140960795 + 1726958 * 2 ^ 59
def prefixEnd_1726958 : Nat := 4983230072969 + 3 ^ 40 * 1726958 * 2
def baseEnd_1726958 : Nat := 886759524127359502582871

theorem tailTrace_1726958 : CollatzResearch.WordTrace tailWord_1726958 prefixEnd_1726958 886759524127359502582871 := by
  unfold tailWord_1726958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873416609691697723757691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41991555251689054526707685 7873416609691697723757691)
  ·
    refine ⟨11810124914537546585636537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7873416609691697723757691 11810124914537546585636537)
    ·
      refine ⟨8857593685903159939227403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11810124914537546585636537 8857593685903159939227403)
      ·
        refine ⟨13286390528854739908841105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857593685903159939227403 13286390528854739908841105)
        ·
          refine ⟨9964792896641054931630829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13286390528854739908841105 9964792896641054931630829)
          ·
            refine ⟨3736797336240395599361561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9964792896641054931630829 3736797336240395599361561)
            ·
              refine ⟨2802598002180296699521171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3736797336240395599361561 2802598002180296699521171)
              ·
                refine ⟨4203897003270445049281757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802598002180296699521171 4203897003270445049281757)
                ·
                  refine ⟨1576461376226416893480659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4203897003270445049281757 1576461376226416893480659)
                  ·
                    refine ⟨2364692064339625340220989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1576461376226416893480659 2364692064339625340220989)
                    ·
                      refine ⟨886759524127359502582871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2364692064339625340220989 886759524127359502582871)
                      ·
                        rfl

theorem cell23_1726958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_1726958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726958 prefixEnd_1726958 := by exact prefixLift 1726958
  have htrace : WordTrace (prefixWord ++ tailWord_1726958) baseStart_1726958 baseEnd_1726958 := by
    simpa [prefixWord, tailWord_1726958, baseEnd_1726958] using wordTrace_append hprefix tailTrace_1726958
  have hstable : (prefixWord ++ tailWord_1726958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726958).length < 2 ^ (prefixWord ++ tailWord_1726958).sum := by decide
  have hdescent : baseEnd_1726958 < baseStart_1726958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727004 : List Nat := [2, 2, 3, 1, 2, 4, 9]
def baseStart_1727004 : Nat := 118140960795 + 1727004 * 2 ^ 59
def prefixEnd_1727004 : Nat := 4983230072969 + 3 ^ 40 * 1727004 * 2
def baseEnd_1727004 : Nat := 10947940052314399044539

theorem tailTrace_1727004 : CollatzResearch.WordTrace tailWord_1727004 prefixEnd_1727004 10947940052314399044539 := by
  unfold tailWord_1727004
  simp only [CollatzResearch.WordTrace]
  refine ⟨31494505317683465823118033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41992673756911287764157377 31494505317683465823118033)
  ·
    refine ⟨23620878988262599367338525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31494505317683465823118033 23620878988262599367338525)
    ·
      refine ⟨8857829620598474762751947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23620878988262599367338525 8857829620598474762751947)
      ·
        refine ⟨13286744430897712144127921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857829620598474762751947 13286744430897712144127921)
        ·
          refine ⟨9965058323173284108095941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13286744430897712144127921 9965058323173284108095941)
          ·
            refine ⟨1868448435594990770267989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9965058323173284108095941 1868448435594990770267989)
            ·
              refine ⟨10947940052314399044539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1868448435594990770267989 10947940052314399044539)
              ·
                rfl

theorem cell23_1727004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 9].length) (baseStart_1727004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727004 prefixEnd_1727004 := by exact prefixLift 1727004
  have htrace : WordTrace (prefixWord ++ tailWord_1727004) baseStart_1727004 baseEnd_1727004 := by
    simpa [prefixWord, tailWord_1727004, baseEnd_1727004] using wordTrace_append hprefix tailTrace_1727004
  have hstable : (prefixWord ++ tailWord_1727004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727004).length < 2 ^ (prefixWord ++ tailWord_1727004).sum := by decide
  have hdescent : baseEnd_1727004 < baseStart_1727004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727084 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_1727084 : Nat := 118140960795 + 1727084 * 2 ^ 59
def prefixEnd_1727084 : Nat := 4983230072969 + 3 ^ 40 * 1727084 * 2
def baseEnd_1727084 : Nat := 886824222689826009607291

theorem tailTrace_1727084 : CollatzResearch.WordTrace tailWord_1727084 prefixEnd_1727084 886824222689826009607291 := by
  unfold tailWord_1727084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31495964237538552654574153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41994618983384736872765537 31495964237538552654574153)
  ·
    refine ⟨23621973178153914490930615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31495964237538552654574153 23621973178153914490930615)
    ·
      refine ⟨35432959767230871736395923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23621973178153914490930615 35432959767230871736395923)
      ·
        refine ⟨53149439650846307604593885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35432959767230871736395923 53149439650846307604593885)
        ·
          refine ⟨19931039869067365351722707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53149439650846307604593885 19931039869067365351722707)
          ·
            refine ⟨29896559803601048027584061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19931039869067365351722707 29896559803601048027584061)
            ·
              refine ⟨11211209926350393010344023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29896559803601048027584061 11211209926350393010344023)
              ·
                refine ⟨16816814889525589515516035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11211209926350393010344023 16816814889525589515516035)
                ·
                  refine ⟨25225222334288384273274053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16816814889525589515516035 25225222334288384273274053)
                  ·
                    refine ⟨4729729187679072051238885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25225222334288384273274053 4729729187679072051238885)
                    ·
                      refine ⟨886824222689826009607291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4729729187679072051238885 886824222689826009607291)
                      ·
                        rfl

theorem cell23_1727084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_1727084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727084 prefixEnd_1727084 := by exact prefixLift 1727084
  have htrace : WordTrace (prefixWord ++ tailWord_1727084) baseStart_1727084 baseEnd_1727084 := by
    simpa [prefixWord, tailWord_1727084, baseEnd_1727084] using wordTrace_append hprefix tailTrace_1727084
  have hstable : (prefixWord ++ tailWord_1727084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727084).length < 2 ^ (prefixWord ++ tailWord_1727084).sum := by decide
  have hdescent : baseEnd_1727084 < baseStart_1727084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727122 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1727122 : Nat := 118140960795 + 1727122 * 2 ^ 59
def prefixEnd_1727122 : Nat := 4983230072969 + 3 ^ 40 * 1727122 * 2
def baseEnd_1727122 : Nat := 886843734954696860932117

theorem tailTrace_1727122 : CollatzResearch.WordTrace tailWord_1727122 prefixEnd_1727122 886843734954696860932117 := by
  unfold tailWord_1727122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748328612234859449757905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41995542965959625199354413 15748328612234859449757905)
  ·
    refine ⟨11811246459176144587318429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15748328612234859449757905 11811246459176144587318429)
    ·
      refine ⟨4429217422191054220244411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11811246459176144587318429 4429217422191054220244411)
      ·
        refine ⟨6643826133286581330366617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4429217422191054220244411 6643826133286581330366617)
        ·
          refine ⟨4982869599964935997774963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6643826133286581330366617 4982869599964935997774963)
          ·
            refine ⟨7474304399947403996662445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982869599964935997774963 7474304399947403996662445)
            ·
              refine ⟨2802864149980276498748417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7474304399947403996662445 2802864149980276498748417)
              ·
                refine ⟨2102148112485207374061313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2802864149980276498748417 2102148112485207374061313)
                ·
                  refine ⟨1576611084363905530545985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102148112485207374061313 1576611084363905530545985)
                  ·
                    refine ⟨1182458313272929147909489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1576611084363905530545985 1182458313272929147909489)
                    ·
                      refine ⟨886843734954696860932117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182458313272929147909489 886843734954696860932117)
                      ·
                        rfl

theorem cell23_1727122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1727122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727122 prefixEnd_1727122 := by exact prefixLift 1727122
  have htrace : WordTrace (prefixWord ++ tailWord_1727122) baseStart_1727122 baseEnd_1727122 := by
    simpa [prefixWord, tailWord_1727122, baseEnd_1727122] using wordTrace_append hprefix tailTrace_1727122
  have hstable : (prefixWord ++ tailWord_1727122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727122).length < 2 ^ (prefixWord ++ tailWord_1727122).sum := by decide
  have hdescent : baseEnd_1727122 < baseStart_1727122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727154 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_1727154 : Nat := 118140960795 + 1727154 * 2 ^ 59
def prefixEnd_1727154 : Nat := 4983230072969 + 3 ^ 40 * 1727154 * 2
def baseEnd_1727154 : Nat := 295620055445213578577323

theorem tailTrace_1727154 : CollatzResearch.WordTrace tailWord_1727154 prefixEnd_1727154 295620055445213578577323 := by
  unfold tailWord_1727154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748620396205876816049129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41996321056549004842797677 15748620396205876816049129)
  ·
    refine ⟨11811465297154407612036847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15748620396205876816049129 11811465297154407612036847)
    ·
      refine ⟨17717197945731611418055271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11811465297154407612036847 17717197945731611418055271)
      ·
        refine ⟨26575796918597417127082907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17717197945731611418055271 26575796918597417127082907)
        ·
          refine ⟨39863695377896125690624361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26575796918597417127082907 39863695377896125690624361)
          ·
            refine ⟨29897771533422094267968271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39863695377896125690624361 29897771533422094267968271)
            ·
              refine ⟨44846657300133141401952407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29897771533422094267968271 44846657300133141401952407)
              ·
                refine ⟨67269985950199712102928611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44846657300133141401952407 67269985950199712102928611)
                ·
                  refine ⟨100904978925299568154392917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67269985950199712102928611 100904978925299568154392917)
                  ·
                    refine ⟨295620055445213578577323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 100904978925299568154392917 295620055445213578577323)
                    ·
                      rfl

theorem cell23_1727154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_1727154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727154 prefixEnd_1727154 := by exact prefixLift 1727154
  have htrace : WordTrace (prefixWord ++ tailWord_1727154) baseStart_1727154 baseEnd_1727154 := by
    simpa [prefixWord, tailWord_1727154, baseEnd_1727154] using wordTrace_append hprefix tailTrace_1727154
  have hstable : (prefixWord ++ tailWord_1727154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727154).length < 2 ^ (prefixWord ++ tailWord_1727154).sum := by decide
  have hdescent : baseEnd_1727154 < baseStart_1727154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727161 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1727161 : Nat := 118140960795 + 1727161 * 2 ^ 59
def prefixEnd_1727161 : Nat := 4983230072969 + 3 ^ 40 * 1727161 * 2
def baseEnd_1727161 : Nat := 886863760700222208344437

theorem tailTrace_1727161 : CollatzResearch.WordTrace tailWord_1727161 prefixEnd_1727161 886863760700222208344437 := by
  unfold tailWord_1727161
  simp only [CollatzResearch.WordTrace]
  refine ⟨62994736895798147459701337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41996491263865431639800891 62994736895798147459701337)
  ·
    refine ⟨47246052671848610594776003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62994736895798147459701337 47246052671848610594776003)
    ·
      refine ⟨70869079007772915892164005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47246052671848610594776003 70869079007772915892164005)
      ·
        refine ⟨13287952313957421729780751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70869079007772915892164005 13287952313957421729780751)
        ·
          refine ⟨19931928470936132594671127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13287952313957421729780751 19931928470936132594671127)
          ·
            refine ⟨29897892706404198892006691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19931928470936132594671127 29897892706404198892006691)
            ·
              refine ⟨44846839059606298338010037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29897892706404198892006691 44846839059606298338010037)
              ·
                refine ⟨4204391161838090469188441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44846839059606298338010037 4204391161838090469188441)
                ·
                  refine ⟨3153293371378567851891331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204391161838090469188441 3153293371378567851891331)
                  ·
                    refine ⟨4729940057067851777836997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3153293371378567851891331 4729940057067851777836997)
                    ·
                      refine ⟨886863760700222208344437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4729940057067851777836997 886863760700222208344437)
                      ·
                        rfl

theorem cell23_1727161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1727161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727161 prefixEnd_1727161 := by exact prefixLift 1727161
  have htrace : WordTrace (prefixWord ++ tailWord_1727161) baseStart_1727161 baseEnd_1727161 := by
    simpa [prefixWord, tailWord_1727161, baseEnd_1727161] using wordTrace_append hprefix tailTrace_1727161
  have hstable : (prefixWord ++ tailWord_1727161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727161).length < 2 ^ (prefixWord ++ tailWord_1727161).sum := by decide
  have hdescent : baseEnd_1727161 < baseStart_1727161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727178 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_1727178 : Nat := 118140960795 + 1727178 * 2 ^ 59
def prefixEnd_1727178 : Nat := 4983230072969 + 3 ^ 40 * 1727178 * 2
def baseEnd_1727178 : Nat := 886872489871348641831859

theorem tailTrace_1727178 : CollatzResearch.WordTrace tailWord_1727178 prefixEnd_1727178 886872489871348641831859 := by
  unfold tailWord_1727178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748839234184139840767547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41996904624491039575380125 15748839234184139840767547)
  ·
    refine ⟨23623258851276209761151321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15748839234184139840767547 23623258851276209761151321)
    ·
      refine ⟨17717444138457157320863491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23623258851276209761151321 17717444138457157320863491)
      ·
        refine ⟨26576166207685735981295237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17717444138457157320863491 26576166207685735981295237)
        ·
          refine ⟨4983031163941075496492857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26576166207685735981295237 4983031163941075496492857)
          ·
            refine ⟨3737273372955806622369643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4983031163941075496492857 3737273372955806622369643)
            ·
              refine ⟨5605910059433709933554465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737273372955806622369643 5605910059433709933554465)
              ·
                refine ⟨4204432544575282450165849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5605910059433709933554465 4204432544575282450165849)
                ·
                  refine ⟨3153324408431461837624387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204432544575282450165849 3153324408431461837624387)
                  ·
                    refine ⟨4729986612647192756436581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3153324408431461837624387 4729986612647192756436581)
                    ·
                      refine ⟨886872489871348641831859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4729986612647192756436581 886872489871348641831859)
                      ·
                        rfl

theorem cell23_1727178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_1727178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727178 prefixEnd_1727178 := by exact prefixLift 1727178
  have htrace : WordTrace (prefixWord ++ tailWord_1727178) baseStart_1727178 baseEnd_1727178 := by
    simpa [prefixWord, tailWord_1727178, baseEnd_1727178] using wordTrace_append hprefix tailTrace_1727178
  have hstable : (prefixWord ++ tailWord_1727178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727178).length < 2 ^ (prefixWord ++ tailWord_1727178).sum := by decide
  have hdescent : baseEnd_1727178 < baseStart_1727178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727239 : List Nat := [1, 1, 4, 4, 1, 3, 2, 2, 1, 4]
def baseStart_1727239 : Nat := 118140960795 + 1727239 * 2 ^ 59
def prefixEnd_1727239 : Nat := 4983230072969 + 3 ^ 40 * 1727239 * 2
def baseEnd_1727239 : Nat := 295634604063757634389693

theorem tailTrace_1727239 : CollatzResearch.WordTrace tailWord_1727239 prefixEnd_1727239 295634604063757634389693 := by
  unfold tailWord_1727239
  simp only [CollatzResearch.WordTrace]
  refine ⟨62997581789515566781040771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41998387859677044520693847 62997581789515566781040771)
  ·
    refine ⟨94496372684273350171561157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62997581789515566781040771 94496372684273350171561157)
    ·
      refine ⟨17718069878301253157167717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94496372684273350171561157 17718069878301253157167717)
      ·
        refine ⟨3322138102181484966968947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17718069878301253157167717 3322138102181484966968947)
        ·
          refine ⟨4983207153272227450453421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322138102181484966968947 4983207153272227450453421)
          ·
            refine ⟨1868702682477085293920033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4983207153272227450453421 1868702682477085293920033)
            ·
              refine ⟨1401527011857813970440025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868702682477085293920033 1401527011857813970440025)
              ·
                refine ⟨1051145258893360477830019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401527011857813970440025 1051145258893360477830019)
                ·
                  refine ⟨1576717888340040716745029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051145258893360477830019 1576717888340040716745029)
                  ·
                    refine ⟨295634604063757634389693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1576717888340040716745029 295634604063757634389693)
                    ·
                      rfl

theorem cell23_1727239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_1727239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727239 prefixEnd_1727239 := by exact prefixLift 1727239
  have htrace : WordTrace (prefixWord ++ tailWord_1727239) baseStart_1727239 baseEnd_1727239 := by
    simpa [prefixWord, tailWord_1727239, baseEnd_1727239] using wordTrace_append hprefix tailTrace_1727239
  have hstable : (prefixWord ++ tailWord_1727239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727239).length < 2 ^ (prefixWord ++ tailWord_1727239).sum := by decide
  have hdescent : baseEnd_1727239 < baseStart_1727239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727251 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 4]
def baseStart_1727251 : Nat := 118140960795 + 1727251 * 2 ^ 59
def prefixEnd_1727251 : Nat := 4983230072969 + 3 ^ 40 * 1727251 * 2
def baseEnd_1727251 : Nat := 886909973959126856219023

theorem tailTrace_1727251 : CollatzResearch.WordTrace tailWord_1727251 prefixEnd_1727251 886909973959126856219023 := by
  unfold tailWord_1727251
  simp only [CollatzResearch.WordTrace]
  refine ⟨62998019465472092830477607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41998679643648061886985071 62998019465472092830477607)
  ·
    refine ⟨94497029198208139245716411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62998019465472092830477607 94497029198208139245716411)
    ·
      refine ⟨141745543797312208868574617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94497029198208139245716411 141745543797312208868574617)
      ·
        refine ⟨106309157847984156651430963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141745543797312208868574617 106309157847984156651430963)
        ·
          refine ⟨159463736771976234977146445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106309157847984156651430963 159463736771976234977146445)
          ·
            refine ⟨59798901289491088116429917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159463736771976234977146445 59798901289491088116429917)
            ·
              refine ⟨22424587983559158043661219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59798901289491088116429917 22424587983559158043661219)
              ·
                refine ⟨33636881975338737065491829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22424587983559158043661219 33636881975338737065491829)
                ·
                  refine ⟨3153457685188006599889859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33636881975338737065491829 3153457685188006599889859)
                  ·
                    refine ⟨4730186527782009899834789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3153457685188006599889859 4730186527782009899834789)
                    ·
                      refine ⟨886909973959126856219023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4730186527782009899834789 886909973959126856219023)
                      ·
                        rfl

theorem cell23_1727251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_1727251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727251 prefixEnd_1727251 := by exact prefixLift 1727251
  have htrace : WordTrace (prefixWord ++ tailWord_1727251) baseStart_1727251 baseEnd_1727251 := by
    simpa [prefixWord, tailWord_1727251, baseEnd_1727251] using wordTrace_append hprefix tailTrace_1727251
  have hstable : (prefixWord ++ tailWord_1727251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727251).length < 2 ^ (prefixWord ++ tailWord_1727251).sum := by decide
  have hdescent : baseEnd_1727251 < baseStart_1727251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727285 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_1727285 : Nat := 118140960795 + 1727285 * 2 ^ 59
def prefixEnd_1727285 : Nat := 4983230072969 + 3 ^ 40 * 1727285 * 2
def baseEnd_1727285 : Nat := 886927432301379723193867

theorem tailTrace_1727285 : CollatzResearch.WordTrace tailWord_1727285 prefixEnd_1727285 886927432301379723193867 := by
  unfold tailWord_1727285
  simp only [CollatzResearch.WordTrace]
  refine ⟨62999259547348916637215309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41999506364899277758143539 62999259547348916637215309)
  ·
    refine ⟨23624722330255843738955741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62999259547348916637215309 23624722330255843738955741)
    ·
      refine ⟨8859270873845941402108403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23624722330255843738955741 8859270873845941402108403)
      ·
        refine ⟨13288906310768912103162605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8859270873845941402108403 13288906310768912103162605)
        ·
          refine ⟨4983339866538342038685977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13288906310768912103162605 4983339866538342038685977)
          ·
            refine ⟨3737504899903756529014483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4983339866538342038685977 3737504899903756529014483)
            ·
              refine ⟨5606257349855634793521725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737504899903756529014483 5606257349855634793521725)
              ·
                refine ⟨2102346506195863047570647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5606257349855634793521725 2102346506195863047570647)
                ·
                  refine ⟨3153519759293794571355971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102346506195863047570647 3153519759293794571355971)
                  ·
                    refine ⟨4730279638940691857033957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3153519759293794571355971 4730279638940691857033957)
                    ·
                      refine ⟨886927432301379723193867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4730279638940691857033957 886927432301379723193867)
                      ·
                        rfl

theorem cell23_1727285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_1727285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727285 prefixEnd_1727285 := by exact prefixLift 1727285
  have htrace : WordTrace (prefixWord ++ tailWord_1727285) baseStart_1727285 baseEnd_1727285 := by
    simpa [prefixWord, tailWord_1727285, baseEnd_1727285] using wordTrace_append hprefix tailTrace_1727285
  have hstable : (prefixWord ++ tailWord_1727285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727285).length < 2 ^ (prefixWord ++ tailWord_1727285).sum := by decide
  have hdescent : baseEnd_1727285 < baseStart_1727285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727295 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 2, 4]
def baseStart_1727295 : Nat := 118140960795 + 1727295 * 2 ^ 59
def prefixEnd_1727295 : Nat := 4983230072969 + 3 ^ 40 * 1727295 * 2
def baseEnd_1727295 : Nat := 295644189035974894689607

theorem tailTrace_1727295 : CollatzResearch.WordTrace tailWord_1727295 prefixEnd_1727295 295644189035974894689607 := by
  unfold tailWord_1727295
  simp only [CollatzResearch.WordTrace]
  refine ⟨62999624277312688345079339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41999749518208458896719559 62999624277312688345079339)
  ·
    refine ⟨94499436415969032517619009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62999624277312688345079339 94499436415969032517619009)
    ·
      refine ⟨70874577311976774388214257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94499436415969032517619009 70874577311976774388214257)
      ·
        refine ⟨53155932983982580791160693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70874577311976774388214257 53155932983982580791160693)
        ·
          refine ⟨4983368717248366949171315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53155932983982580791160693 4983368717248366949171315)
          ·
            refine ⟨7475053075872550423756973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983368717248366949171315 7475053075872550423756973)
            ·
              refine ⟨2803144903452206408908865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7475053075872550423756973 2803144903452206408908865)
              ·
                refine ⟨2102358677589154806681649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2803144903452206408908865 2102358677589154806681649)
                ·
                  refine ⟨1576769008191866105011237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102358677589154806681649 1576769008191866105011237)
                  ·
                    refine ⟨295644189035974894689607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1576769008191866105011237 295644189035974894689607)
                    ·
                      rfl

theorem cell23_1727295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_1727295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727295 prefixEnd_1727295 := by exact prefixLift 1727295
  have htrace : WordTrace (prefixWord ++ tailWord_1727295) baseStart_1727295 baseEnd_1727295 := by
    simpa [prefixWord, tailWord_1727295, baseEnd_1727295] using wordTrace_append hprefix tailTrace_1727295
  have hstable : (prefixWord ++ tailWord_1727295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727295).length < 2 ^ (prefixWord ++ tailWord_1727295).sum := by decide
  have hdescent : baseEnd_1727295 < baseStart_1727295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727335 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1727335 : Nat := 118140960795 + 1727335 * 2 ^ 59
def prefixEnd_1727335 : Nat := 4983230072969 + 3 ^ 40 * 1727335 * 2
def baseEnd_1727335 : Nat := 886953106334104527568637

theorem tailTrace_1727335 : CollatzResearch.WordTrace tailWord_1727335 prefixEnd_1727335 886953106334104527568637 := by
  unfold tailWord_1727335
  simp only [CollatzResearch.WordTrace]
  refine ⟨63001083197167775176535459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42000722131445183451023639 63001083197167775176535459)
  ·
    refine ⟨94501624795751662764803189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63001083197167775176535459 94501624795751662764803189)
    ·
      refine ⟨8859527324601718384200299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94501624795751662764803189 8859527324601718384200299)
      ·
        refine ⟨13289290986902577576300449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8859527324601718384200299 13289290986902577576300449)
        ·
          refine ⟨9966968240176933182225337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13289290986902577576300449 9966968240176933182225337)
          ·
            refine ⟨7475226180132699886669003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9966968240176933182225337 7475226180132699886669003)
            ·
              refine ⟨11212839270199049830003505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475226180132699886669003 11212839270199049830003505)
              ·
                refine ⟨8409629452649287372502629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11212839270199049830003505 8409629452649287372502629)
                ·
                  refine ⟨1576805522371741382344243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8409629452649287372502629 1576805522371741382344243)
                  ·
                    refine ⟨2365208283557612073516365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1576805522371741382344243 2365208283557612073516365)
                    ·
                      refine ⟨886953106334104527568637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2365208283557612073516365 886953106334104527568637)
                      ·
                        rfl

theorem cell23_1727335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1727335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727335 prefixEnd_1727335 := by exact prefixLift 1727335
  have htrace : WordTrace (prefixWord ++ tailWord_1727335) baseStart_1727335 baseEnd_1727335 := by
    simpa [prefixWord, tailWord_1727335, baseEnd_1727335] using wordTrace_append hprefix tailTrace_1727335
  have hstable : (prefixWord ++ tailWord_1727335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727335).length < 2 ^ (prefixWord ++ tailWord_1727335).sum := by decide
  have hdescent : baseEnd_1727335 < baseStart_1727335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727336 : List Nat := [2, 1, 4, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1727336 : Nat := 118140960795 + 1727336 * 2 ^ 59
def prefixEnd_1727336 : Nat := 4983230072969 + 3 ^ 40 * 1727336 * 2
def baseEnd_1727336 : Nat := 886953619814759023656133

theorem tailTrace_1727336 : CollatzResearch.WordTrace tailWord_1727336 prefixEnd_1727336 886953619814759023656133 := by
  unfold tailWord_1727336
  simp only [CollatzResearch.WordTrace]
  refine ⟨31500559835082076173660931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42000746446776101564881241 31500559835082076173660931)
  ·
    refine ⟨47250839752623114260491397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31500559835082076173660931 47250839752623114260491397)
    ·
      refine ⟨8859532453616833923842137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47250839752623114260491397 8859532453616833923842137)
      ·
        refine ⟨6644649340212625442881603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8859532453616833923842137 6644649340212625442881603)
        ·
          refine ⟨9966974010318938164322405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6644649340212625442881603 9966974010318938164322405)
          ·
            refine ⟨1868807626934800905810451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9966974010318938164322405 1868807626934800905810451)
            ·
              refine ⟨2803211440402201358715677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868807626934800905810451 2803211440402201358715677)
              ·
                refine ⟨1051204290150825509518379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2803211440402201358715677 1051204290150825509518379)
                ·
                  refine ⟨1576806435226238264277569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051204290150825509518379 1576806435226238264277569)
                  ·
                    refine ⟨1182604826419678698208177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1576806435226238264277569 1182604826419678698208177)
                    ·
                      refine ⟨886953619814759023656133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182604826419678698208177 886953619814759023656133)
                      ·
                        rfl

theorem cell23_1727336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1727336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727336 prefixEnd_1727336 := by exact prefixLift 1727336
  have htrace : WordTrace (prefixWord ++ tailWord_1727336) baseStart_1727336 baseEnd_1727336 := by
    simpa [prefixWord, tailWord_1727336, baseEnd_1727336] using wordTrace_append hprefix tailTrace_1727336
  have hstable : (prefixWord ++ tailWord_1727336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727336).length < 2 ^ (prefixWord ++ tailWord_1727336).sum := by decide
  have hdescent : baseEnd_1727336 < baseStart_1727336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727351 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 4, 6]
def baseStart_1727351 : Nat := 118140960795 + 1727351 * 2 ^ 59
def prefixEnd_1727351 : Nat := 4983230072969 + 3 ^ 40 * 1727351 * 2
def baseEnd_1727351 : Nat := 295653774008192154989521

theorem tailTrace_1727351 : CollatzResearch.WordTrace tailWord_1727351 prefixEnd_1727351 295653774008192154989521 := by
  unfold tailWord_1727351
  simp only [CollatzResearch.WordTrace]
  refine ⟨63001666765109809909117907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42001111176739873272745271 63001666765109809909117907)
  ·
    refine ⟨94502500147664714863676861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63001666765109809909117907 94502500147664714863676861)
    ·
      refine ⟨35438437555374268073878823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94502500147664714863676861 35438437555374268073878823)
      ·
        refine ⟨53157656333061402110818235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35438437555374268073878823 53157656333061402110818235)
        ·
          refine ⟨79736484499592103166227353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53157656333061402110818235 79736484499592103166227353)
          ·
            refine ⟨59802363374694077374670515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79736484499592103166227353 59802363374694077374670515)
            ·
              refine ⟨89703545062041116062005773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59802363374694077374670515 89703545062041116062005773)
              ·
                refine ⟨33638829398265418523252165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89703545062041116062005773 33638829398265418523252165)
                ·
                  refine ⟨6307280512174765973109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33638829398265418523252165 6307280512174765973109781)
                  ·
                    refine ⟨295653774008192154989521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6307280512174765973109781 295653774008192154989521)
                    ·
                      rfl

theorem cell23_1727351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_1727351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727351 prefixEnd_1727351 := by exact prefixLift 1727351
  have htrace : WordTrace (prefixWord ++ tailWord_1727351) baseStart_1727351 baseEnd_1727351 := by
    simpa [prefixWord, tailWord_1727351, baseEnd_1727351] using wordTrace_append hprefix tailTrace_1727351
  have hstable : (prefixWord ++ tailWord_1727351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727351).length < 2 ^ (prefixWord ++ tailWord_1727351).sum := by decide
  have hdescent : baseEnd_1727351 < baseStart_1727351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727369 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 2, 1, 3]
def baseStart_1727369 : Nat := 118140960795 + 1727369 * 2 ^ 59
def prefixEnd_1727369 : Nat := 4983230072969 + 3 ^ 40 * 1727369 * 2
def baseEnd_1727369 : Nat := 886970564676357394543481

theorem tailTrace_1727369 : CollatzResearch.WordTrace tailWord_1727369 prefixEnd_1727369 886970564676357394543481 := by
  unfold tailWord_1727369
  simp only [CollatzResearch.WordTrace]
  refine ⟨63002323279044598983273161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42001548852696399322182107 63002323279044598983273161)
  ·
    refine ⟨47251742459283449237454871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63002323279044598983273161 47251742459283449237454871)
    ·
      refine ⟨70877613688925173856182307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47251742459283449237454871 70877613688925173856182307)
      ·
        refine ⟨106316420533387760784273461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70877613688925173856182307 106316420533387760784273461)
        ·
          refine ⟨9967164425005102573525637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106316420533387760784273461 9967164425005102573525637)
          ·
            refine ⟨1868843329688456732536057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9967164425005102573525637 1868843329688456732536057)
            ·
              refine ⟨1401632497266342549402043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868843329688456732536057 1401632497266342549402043)
              ·
                refine ⟨2102448745899513824103065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401632497266342549402043 2102448745899513824103065)
                ·
                  refine ⟨1576836559424635368077299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102448745899513824103065 1576836559424635368077299)
                  ·
                    refine ⟨2365254839136953052115949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1576836559424635368077299 2365254839136953052115949)
                    ·
                      refine ⟨886970564676357394543481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2365254839136953052115949 886970564676357394543481)
                      ·
                        rfl

theorem cell23_1727369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 1, 3].length) (baseStart_1727369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727369 prefixEnd_1727369 := by exact prefixLift 1727369
  have htrace : WordTrace (prefixWord ++ tailWord_1727369) baseStart_1727369 baseEnd_1727369 := by
    simpa [prefixWord, tailWord_1727369, baseEnd_1727369] using wordTrace_append hprefix tailTrace_1727369
  have hstable : (prefixWord ++ tailWord_1727369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727369).length < 2 ^ (prefixWord ++ tailWord_1727369).sum := by decide
  have hdescent : baseEnd_1727369 < baseStart_1727369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727412 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1727412 : Nat := 118140960795 + 1727412 * 2 ^ 59
def prefixEnd_1727412 : Nat := 4983230072969 + 3 ^ 40 * 1727412 * 2
def baseEnd_1727412 : Nat := 886992644344500726305783

theorem tailTrace_1727412 : CollatzResearch.WordTrace tailWord_1727412 prefixEnd_1727412 886992644344500726305783 := by
  unfold tailWord_1727412
  simp only [CollatzResearch.WordTrace]
  refine ⟨31501945808944408663544245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42002594411925878218058993 31501945808944408663544245)
  ·
    refine ⟨2953307419588538312207273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31501945808944408663544245 2953307419588538312207273)
    ·
      refine ⟨2214980564691403734155455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2953307419588538312207273 2214980564691403734155455)
      ·
        refine ⟨3322470847037105601233183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214980564691403734155455 3322470847037105601233183)
        ·
          refine ⟨4983706270555658401849775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322470847037105601233183 4983706270555658401849775)
          ·
            refine ⟨7475559405833487602774663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983706270555658401849775 7475559405833487602774663)
            ·
              refine ⟨11213339108750231404161995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475559405833487602774663 11213339108750231404161995)
              ·
                refine ⟨16820008663125347106242993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11213339108750231404161995 16820008663125347106242993)
                ·
                  refine ⟨12615006497344010329682245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16820008663125347106242993 12615006497344010329682245)
                  ·
                    refine ⟨2365313718252001936815421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12615006497344010329682245 2365313718252001936815421)
                    ·
                      refine ⟨886992644344500726305783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2365313718252001936815421 886992644344500726305783)
                      ·
                        rfl

theorem cell23_1727412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1727412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727412 prefixEnd_1727412 := by exact prefixLift 1727412
  have htrace : WordTrace (prefixWord ++ tailWord_1727412) baseStart_1727412 baseEnd_1727412 := by
    simpa [prefixWord, tailWord_1727412, baseEnd_1727412] using wordTrace_append hprefix tailTrace_1727412
  have hstable : (prefixWord ++ tailWord_1727412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727412).length < 2 ^ (prefixWord ++ tailWord_1727412).sum := by decide
  have hdescent : baseEnd_1727412 < baseStart_1727412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727445 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_1727445 : Nat := 118140960795 + 1727445 * 2 ^ 59
def prefixEnd_1727445 : Nat := 4983230072969 + 3 ^ 40 * 1727445 * 2
def baseEnd_1727445 : Nat := 295669863068699699064377

theorem tailTrace_1727445 : CollatzResearch.WordTrace tailWord_1727445 prefixEnd_1727445 295669863068699699064377 := by
  unfold tailWord_1727445
  simp only [CollatzResearch.WordTrace]
  refine ⟨63005095226769263963039789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42003396817846175975359859 63005095226769263963039789)
  ·
    refine ⟨23626910710038473986139921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63005095226769263963039789 23626910710038473986139921)
    ·
      refine ⟨17720183032528855489604941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23626910710038473986139921 17720183032528855489604941)
      ·
        refine ⟨6645068637198320808601853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17720183032528855489604941 6645068637198320808601853)
        ·
          refine ⟨2491900738949370303225695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6645068637198320808601853 2491900738949370303225695)
          ·
            refine ⟨3737851108424055454838543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491900738949370303225695 3737851108424055454838543)
            ·
              refine ⟨5606776662636083182257815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737851108424055454838543 5606776662636083182257815)
              ·
                refine ⟨8410164993954124773386723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606776662636083182257815 8410164993954124773386723)
                ·
                  refine ⟨12615247490931187160080085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410164993954124773386723 12615247490931187160080085)
                  ·
                    refine ⟨295669863068699699064377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12615247490931187160080085 295669863068699699064377)
                    ·
                      rfl

theorem cell23_1727445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_1727445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727445 prefixEnd_1727445 := by exact prefixLift 1727445
  have htrace : WordTrace (prefixWord ++ tailWord_1727445) baseStart_1727445 baseEnd_1727445 := by
    simpa [prefixWord, tailWord_1727445, baseEnd_1727445] using wordTrace_append hprefix tailTrace_1727445
  have hstable : (prefixWord ++ tailWord_1727445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727445).length < 2 ^ (prefixWord ++ tailWord_1727445).sum := by decide
  have hdescent : baseEnd_1727445 < baseStart_1727445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727509 : List Nat := [1, 3, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_1727509 : Nat := 118140960795 + 1727509 * 2 ^ 59
def prefixEnd_1727509 : Nat := 4983230072969 + 3 ^ 40 * 1727509 * 2
def baseEnd_1727509 : Nat := 295680817322662282264279

theorem tailTrace_1727509 : CollatzResearch.WordTrace tailWord_1727509 prefixEnd_1727509 295680817322662282264279 := by
  unfold tailWord_1727509
  simp only [CollatzResearch.WordTrace]
  refine ⟨63007429498537402893369581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42004952999024935262246387 63007429498537402893369581)
  ·
    refine ⟨23627786061951526085013593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63007429498537402893369581 23627786061951526085013593)
    ·
      refine ⟨17720839546463644563760195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23627786061951526085013593 17720839546463644563760195)
      ·
        refine ⟨26581259319695466845640293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17720839546463644563760195 26581259319695466845640293)
        ·
          refine ⟨4983986122442900033557555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26581259319695466845640293 4983986122442900033557555)
          ·
            refine ⟨7475979183664350050336333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983986122442900033557555 7475979183664350050336333)
            ·
              refine ⟨2803492193874131268876125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7475979183664350050336333 2803492193874131268876125)
              ·
                refine ⟨1051309572702799225828547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2803492193874131268876125 1051309572702799225828547)
                ·
                  refine ⟨1576964359054198838742821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051309572702799225828547 1576964359054198838742821)
                  ·
                    refine ⟨295680817322662282264279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1576964359054198838742821 295680817322662282264279)
                    ·
                      rfl

theorem cell23_1727509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_1727509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727509 prefixEnd_1727509 := by exact prefixLift 1727509
  have htrace : WordTrace (prefixWord ++ tailWord_1727509) baseStart_1727509 baseEnd_1727509 := by
    simpa [prefixWord, tailWord_1727509, baseEnd_1727509] using wordTrace_append hprefix tailTrace_1727509
  have hstable : (prefixWord ++ tailWord_1727509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727509).length < 2 ^ (prefixWord ++ tailWord_1727509).sum := by decide
  have hdescent : baseEnd_1727509 < baseStart_1727509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727555 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 4]
def baseStart_1727555 : Nat := 118140960795 + 1727555 * 2 ^ 59
def prefixEnd_1727555 : Nat := 4983230072969 + 3 ^ 40 * 1727555 * 2
def baseEnd_1727555 : Nat := 887066072078093666817625

theorem tailTrace_1727555 : CollatzResearch.WordTrace tailWord_1727555 prefixEnd_1727555 887066072078093666817625 := by
  unfold tailWord_1727555
  simp only [CollatzResearch.WordTrace]
  refine ⟨63009107256370752749544119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42006071504247168499696079 63009107256370752749544119)
  ·
    refine ⟨94513660884556129124316179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63009107256370752749544119 94513660884556129124316179)
    ·
      refine ⟨141770491326834193686474269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94513660884556129124316179 141770491326834193686474269)
      ·
        refine ⟨53163934247562822632427851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141770491326834193686474269 53163934247562822632427851)
        ·
          refine ⟨79745901371344233948641777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53163934247562822632427851 79745901371344233948641777)
          ·
            refine ⟨59809426028508175461481333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79745901371344233948641777 59809426028508175461481333)
            ·
              refine ⟨5607133690172641449513875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59809426028508175461481333 5607133690172641449513875)
              ·
                refine ⟨8410700535258962174270813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607133690172641449513875 8410700535258962174270813)
                ·
                  refine ⟨3154012700722110815351555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8410700535258962174270813 3154012700722110815351555)
                  ·
                    refine ⟨4731019051083166223027333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3154012700722110815351555 4731019051083166223027333)
                    ·
                      refine ⟨887066072078093666817625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4731019051083166223027333 887066072078093666817625)
                      ·
                        rfl

theorem cell23_1727555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_1727555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727555 prefixEnd_1727555 := by exact prefixLift 1727555
  have htrace : WordTrace (prefixWord ++ tailWord_1727555) baseStart_1727555 baseEnd_1727555 := by
    simpa [prefixWord, tailWord_1727555, baseEnd_1727555] using wordTrace_append hprefix tailTrace_1727555
  have hstable : (prefixWord ++ tailWord_1727555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727555).length < 2 ^ (prefixWord ++ tailWord_1727555).sum := by decide
  have hdescent : baseEnd_1727555 < baseStart_1727555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727559 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_1727559 : Nat := 118140960795 + 1727559 * 2 ^ 59
def prefixEnd_1727559 : Nat := 4983230072969 + 3 ^ 40 * 1727559 * 2
def baseEnd_1727559 : Nat := 887068126000711651167607

theorem tailTrace_1727559 : CollatzResearch.WordTrace tailWord_1727559 prefixEnd_1727559 887068126000711651167607 := by
  unfold tailWord_1727559
  simp only [CollatzResearch.WordTrace]
  refine ⟨63009253148356261432689731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42006168765570840955126487 63009253148356261432689731)
  ·
    refine ⟨94513879722534392149034597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63009253148356261432689731 94513879722534392149034597)
    ·
      refine ⟨17721352447975198527943987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94513879722534392149034597 17721352447975198527943987)
      ·
        refine ⟨26582028671962797791915981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17721352447975198527943987 26582028671962797791915981)
        ·
          refine ⟨9968260751986049171968493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26582028671962797791915981 9968260751986049171968493)
          ·
            refine ⟨3738097781994768439488185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9968260751986049171968493 3738097781994768439488185)
            ·
              refine ⟨2803573336496076329616139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3738097781994768439488185 2803573336496076329616139)
              ·
                refine ⟨4205360004744114494424209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803573336496076329616139 4205360004744114494424209)
                ·
                  refine ⟨3154020003558085870818157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205360004744114494424209 3154020003558085870818157)
                  ·
                    refine ⟨1182757501334282201556809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3154020003558085870818157 1182757501334282201556809)
                    ·
                      refine ⟨887068126000711651167607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182757501334282201556809 887068126000711651167607)
                      ·
                        rfl

theorem cell23_1727559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_1727559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727559 prefixEnd_1727559 := by exact prefixLift 1727559
  have htrace : WordTrace (prefixWord ++ tailWord_1727559) baseStart_1727559 baseEnd_1727559 := by
    simpa [prefixWord, tailWord_1727559, baseEnd_1727559] using wordTrace_append hprefix tailTrace_1727559
  have hstable : (prefixWord ++ tailWord_1727559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727559).length < 2 ^ (prefixWord ++ tailWord_1727559).sum := by decide
  have hdescent : baseEnd_1727559 < baseStart_1727559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727572 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_1727572 : Nat := 118140960795 + 1727572 * 2 ^ 59
def prefixEnd_1727572 : Nat := 4983230072969 + 3 ^ 40 * 1727572 * 2
def baseEnd_1727572 : Nat := 887074801249220100305047

theorem tailTrace_1727572 : CollatzResearch.WordTrace tailWord_1727572 prefixEnd_1727572 887074801249220100305047 := by
  unfold tailWord_1727572
  simp only [CollatzResearch.WordTrace]
  refine ⟨31504863648654582326456485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42006484864872776435275313 31504863648654582326456485)
  ·
    refine ⟨5907161934122734186210591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31504863648654582326456485 5907161934122734186210591)
    ·
      refine ⟨8860742901184101279315887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5907161934122734186210591 8860742901184101279315887)
      ·
        refine ⟨13291114351776151918973831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8860742901184101279315887 13291114351776151918973831)
        ·
          refine ⟨19936671527664227878460747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13291114351776151918973831 19936671527664227878460747)
          ·
            refine ⟨29905007291496341817691121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19936671527664227878460747 29905007291496341817691121)
            ·
              refine ⟨22428755468622256363268341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29905007291496341817691121 22428755468622256363268341)
              ·
                refine ⟨2102695825183336534056407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22428755468622256363268341 2102695825183336534056407)
                ·
                  refine ⟨3154043737775004801084611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102695825183336534056407 3154043737775004801084611)
                  ·
                    refine ⟨4731065606662507201626917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3154043737775004801084611 4731065606662507201626917)
                    ·
                      refine ⟨887074801249220100305047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4731065606662507201626917 887074801249220100305047)
                      ·
                        rfl

theorem cell23_1727572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_1727572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727572 prefixEnd_1727572 := by exact prefixLift 1727572
  have htrace : WordTrace (prefixWord ++ tailWord_1727572) baseStart_1727572 baseEnd_1727572 := by
    simpa [prefixWord, tailWord_1727572, baseEnd_1727572] using wordTrace_append hprefix tailTrace_1727572
  have hstable : (prefixWord ++ tailWord_1727572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727572).length < 2 ^ (prefixWord ++ tailWord_1727572).sum := by decide
  have hdescent : baseEnd_1727572 < baseStart_1727572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727589 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 3, 2, 2]
def baseStart_1727589 : Nat := 118140960795 + 1727589 * 2 ^ 59
def prefixEnd_1727589 : Nat := 4983230072969 + 3 ^ 40 * 1727589 * 2
def baseEnd_1727589 : Nat := 887083530420346533792469

theorem tailTrace_1727589 : CollatzResearch.WordTrace tailWord_1727589 prefixEnd_1727589 887083530420346533792469 := by
  unfold tailWord_1727589
  simp only [CollatzResearch.WordTrace]
  refine ⟨63010347338247576556281821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42006898225498384370854547 63010347338247576556281821)
  ·
    refine ⟨23628880251842841208605683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63010347338247576556281821 23628880251842841208605683)
    ·
      refine ⟨35443320377764261812908525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23628880251842841208605683 35443320377764261812908525)
      ·
        refine ⟨13291245141661598179840697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35443320377764261812908525 13291245141661598179840697)
        ·
          refine ⟨9968433856246198634880523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13291245141661598179840697 9968433856246198634880523)
          ·
            refine ⟨14952650784369297952320785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968433856246198634880523 14952650784369297952320785)
            ·
              refine ⟨11214488088276973464240589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14952650784369297952320785 11214488088276973464240589)
              ·
                refine ⟨4205433033103865049090221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11214488088276973464240589 4205433033103865049090221)
                ·
                  refine ⟨1577037387413949393408833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4205433033103865049090221 1577037387413949393408833)
                  ·
                    refine ⟨1182778040560462045056625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577037387413949393408833 1182778040560462045056625)
                    ·
                      refine ⟨887083530420346533792469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182778040560462045056625 887083530420346533792469)
                      ·
                        rfl

theorem cell23_1727589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_1727589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727589 prefixEnd_1727589 := by exact prefixLift 1727589
  have htrace : WordTrace (prefixWord ++ tailWord_1727589) baseStart_1727589 baseEnd_1727589 := by
    simpa [prefixWord, tailWord_1727589, baseEnd_1727589] using wordTrace_append hprefix tailTrace_1727589
  have hstable : (prefixWord ++ tailWord_1727589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727589).length < 2 ^ (prefixWord ++ tailWord_1727589).sum := by decide
  have hdescent : baseEnd_1727589 < baseStart_1727589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727602 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1727602 : Nat := 118140960795 + 1727602 * 2 ^ 59
def prefixEnd_1727602 : Nat := 4983230072969 + 3 ^ 40 * 1727602 * 2
def baseEnd_1727602 : Nat := 887090205668854982929909

theorem tailTrace_1727602 : CollatzResearch.WordTrace tailWord_1727602 prefixEnd_1727602 887090205668854982929909 := by
  unfold tailWord_1727602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15752705371800119944126265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42007214324800319851003373 15752705371800119944126265)
  ·
    refine ⟨11814529028850089958094699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15752705371800119944126265 11814529028850089958094699)
    ·
      refine ⟨17721793543275134937142049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11814529028850089958094699 17721793543275134937142049)
      ·
        refine ⟨13291345157456351202856537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17721793543275134937142049 13291345157456351202856537)
        ·
          refine ⟨9968508868092263402142403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13291345157456351202856537 9968508868092263402142403)
          ·
            refine ⟨14952763302138395103213605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968508868092263402142403 14952763302138395103213605)
            ·
              refine ⟨2803643119150949081852551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14952763302138395103213605 2803643119150949081852551)
              ·
                refine ⟨4205464678726423622778827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803643119150949081852551 4205464678726423622778827)
                ·
                  refine ⟨6308197018089635434168241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205464678726423622778827 6308197018089635434168241)
                  ·
                    refine ⟨4731147763567226575626181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6308197018089635434168241 4731147763567226575626181)
                    ·
                      refine ⟨887090205668854982929909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4731147763567226575626181 887090205668854982929909)
                      ·
                        rfl

theorem cell23_1727602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1727602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727602 prefixEnd_1727602 := by exact prefixLift 1727602
  have htrace : WordTrace (prefixWord ++ tailWord_1727602) baseStart_1727602 baseEnd_1727602 := by
    simpa [prefixWord, tailWord_1727602, baseEnd_1727602] using wordTrace_append hprefix tailTrace_1727602
  have hstable : (prefixWord ++ tailWord_1727602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727602).length < 2 ^ (prefixWord ++ tailWord_1727602).sum := by decide
  have hdescent : baseEnd_1727602 < baseStart_1727602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727606 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_1727606 : Nat := 118140960795 + 1727606 * 2 ^ 59
def prefixEnd_1727606 : Nat := 4983230072969 + 3 ^ 40 * 1727606 * 2
def baseEnd_1727606 : Nat := 887092259591472967279891

theorem tailTrace_1727606 : CollatzResearch.WordTrace tailWord_1727606 prefixEnd_1727606 887092259591472967279891 := by
  unfold tailWord_1727606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3938185461199124278728167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42007311586123992306433781 3938185461199124278728167)
  ·
    refine ⟨5907278191798686418092251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3938185461199124278728167 5907278191798686418092251)
    ·
      refine ⟨8860917287698029627138377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5907278191798686418092251 8860917287698029627138377)
      ·
        refine ⟨6645687965773522220353783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8860917287698029627138377 6645687965773522220353783)
        ·
          refine ⟨9968531948660283330530675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6645687965773522220353783 9968531948660283330530675)
          ·
            refine ⟨14952797922990424995796013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968531948660283330530675 14952797922990424995796013)
            ·
              refine ⟨5607299221121409373423505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14952797922990424995796013 5607299221121409373423505)
              ·
                refine ⟨4205474415841057030067629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607299221121409373423505 4205474415841057030067629)
                ·
                  refine ⟨1577052905940396386275361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4205474415841057030067629 1577052905940396386275361)
                  ·
                    refine ⟨1182789679455297289706521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577052905940396386275361 1182789679455297289706521)
                    ·
                      refine ⟨887092259591472967279891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182789679455297289706521 887092259591472967279891)
                      ·
                        rfl

theorem cell23_1727606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_1727606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727606 prefixEnd_1727606 := by exact prefixLift 1727606
  have htrace : WordTrace (prefixWord ++ tailWord_1727606) baseStart_1727606 baseEnd_1727606 := by
    simpa [prefixWord, tailWord_1727606, baseEnd_1727606] using wordTrace_append hprefix tailTrace_1727606
  have hstable : (prefixWord ++ tailWord_1727606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727606).length < 2 ^ (prefixWord ++ tailWord_1727606).sum := by decide
  have hdescent : baseEnd_1727606 < baseStart_1727606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727632 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 5, 3, 2]
def baseStart_1727632 : Nat := 118140960795 + 1727632 * 2 ^ 59
def prefixEnd_1727632 : Nat := 4983230072969 + 3 ^ 40 * 1727632 * 2
def baseEnd_1727632 : Nat := 887105610088489865554771

theorem tailTrace_1727632 : CollatzResearch.WordTrace tailWord_1727632 prefixEnd_1727632 887105610088489865554771 := by
  unfold tailWord_1727632
  simp only [CollatzResearch.WordTrace]
  refine ⟨31505957838545897450048575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42007943784727863266731433 31505957838545897450048575)
  ·
    refine ⟨47258936757818846175072863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31505957838545897450048575 47258936757818846175072863)
    ·
      refine ⟨70888405136728269262609295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47258936757818846175072863 70888405136728269262609295)
      ·
        refine ⟨106332607705092403893913943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70888405136728269262609295 106332607705092403893913943)
        ·
          refine ⟨159498911557638605840870915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106332607705092403893913943 159498911557638605840870915)
          ·
            refine ⟨239248367336457908761306373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159498911557638605840870915 239248367336457908761306373)
            ·
              refine ⟨44859068875585857892744945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239248367336457908761306373 44859068875585857892744945)
              ·
                refine ⟨33644301656689393419558709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44859068875585857892744945 33644301656689393419558709)
                ·
                  refine ⟨3154153280314630633083629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33644301656689393419558709 3154153280314630633083629)
                  ·
                    refine ⟨1182807480117986487406361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3154153280314630633083629 1182807480117986487406361)
                    ·
                      refine ⟨887105610088489865554771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182807480117986487406361 887105610088489865554771)
                      ·
                        rfl

theorem cell23_1727632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 3, 2].length) (baseStart_1727632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727632 prefixEnd_1727632 := by exact prefixLift 1727632
  have htrace : WordTrace (prefixWord ++ tailWord_1727632) baseStart_1727632 baseEnd_1727632 := by
    simpa [prefixWord, tailWord_1727632, baseEnd_1727632] using wordTrace_append hprefix tailTrace_1727632
  have hstable : (prefixWord ++ tailWord_1727632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727632).length < 2 ^ (prefixWord ++ tailWord_1727632).sum := by decide
  have hdescent : baseEnd_1727632 < baseStart_1727632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727639 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_1727639 : Nat := 118140960795 + 1727639 * 2 ^ 59
def prefixEnd_1727639 : Nat := 4983230072969 + 3 ^ 40 * 1727639 * 2
def baseEnd_1727639 : Nat := 887109204453071338167239

theorem tailTrace_1727639 : CollatzResearch.WordTrace tailWord_1727639 prefixEnd_1727639 887109204453071338167239 := by
  unfold tailWord_1727639
  simp only [CollatzResearch.WordTrace]
  refine ⟨63012170988066435095601971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42008113992044290063734647 63012170988066435095601971)
  ·
    refine ⟨94518256482099652643402957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63012170988066435095601971 94518256482099652643402957)
    ·
      refine ⟨35444346180787369741276109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94518256482099652643402957 35444346180787369741276109)
      ·
        refine ⟨13291629817795263652978541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35444346180787369741276109 13291629817795263652978541)
        ·
          refine ⟨4984361181673223869866953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13291629817795263652978541 4984361181673223869866953)
          ·
            refine ⟨3738270886254917902400215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984361181673223869866953 3738270886254917902400215)
            ·
              refine ⟨5607406329382376853600323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738270886254917902400215 5607406329382376853600323)
              ·
                refine ⟨8411109494073565280400485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607406329382376853600323 8411109494073565280400485)
                ·
                  refine ⟨1577083030138793490075091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8411109494073565280400485 1577083030138793490075091)
                  ·
                    refine ⟨2365624545208190235112637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1577083030138793490075091 2365624545208190235112637)
                    ·
                      refine ⟨887109204453071338167239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2365624545208190235112637 887109204453071338167239)
                      ·
                        rfl

theorem cell23_1727639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_1727639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727639 prefixEnd_1727639 := by exact prefixLift 1727639
  have htrace : WordTrace (prefixWord ++ tailWord_1727639) baseStart_1727639 baseEnd_1727639 := by
    simpa [prefixWord, tailWord_1727639, baseEnd_1727639] using wordTrace_append hprefix tailTrace_1727639
  have hstable : (prefixWord ++ tailWord_1727639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727639).length < 2 ^ (prefixWord ++ tailWord_1727639).sum := by decide
  have hdescent : baseEnd_1727639 < baseStart_1727639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727666 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_1727666 : Nat := 118140960795 + 1727666 * 2 ^ 59
def prefixEnd_1727666 : Nat := 4983230072969 + 3 ^ 40 * 1727666 * 2
def baseEnd_1727666 : Nat := 887123068430742732529615

theorem tailTrace_1727666 : CollatzResearch.WordTrace tailWord_1727666 prefixEnd_1727666 887123068430742732529615 := by
  unfold tailWord_1727666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15753288939742154676708713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42008770505979079137889901 15753288939742154676708713)
  ·
    refine ⟨11814966704806616007531535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15753288939742154676708713 11814966704806616007531535)
    ·
      refine ⟨17722450057209924011297303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11814966704806616007531535 17722450057209924011297303)
      ·
        refine ⟨26583675085814886016945955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17722450057209924011297303 26583675085814886016945955)
        ·
          refine ⟨39875512628722329025418933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26583675085814886016945955 39875512628722329025418933)
          ·
            refine ⟨3738329308942718346133025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39875512628722329025418933 3738329308942718346133025)
            ·
              refine ⟨2803746981707038759599769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3738329308942718346133025 2803746981707038759599769)
              ·
                refine ⟨2102810236280279069699827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2803746981707038759599769 2102810236280279069699827)
                ·
                  refine ⟨3154215354420418604549741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102810236280279069699827 3154215354420418604549741)
                  ·
                    refine ⟨1182830757907656976706153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3154215354420418604549741 1182830757907656976706153)
                    ·
                      refine ⟨887123068430742732529615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182830757907656976706153 887123068430742732529615)
                      ·
                        rfl

theorem cell23_1727666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_1727666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727666 prefixEnd_1727666 := by exact prefixLift 1727666
  have htrace : WordTrace (prefixWord ++ tailWord_1727666) baseStart_1727666 baseEnd_1727666 := by
    simpa [prefixWord, tailWord_1727666, baseEnd_1727666] using wordTrace_append hprefix tailTrace_1727666
  have hstable : (prefixWord ++ tailWord_1727666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727666).length < 2 ^ (prefixWord ++ tailWord_1727666).sum := by decide
  have hdescent : baseEnd_1727666 < baseStart_1727666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727675 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4]
def baseStart_1727675 : Nat := 118140960795 + 1727675 * 2 ^ 59
def prefixEnd_1727675 : Nat := 4983230072969 + 3 ^ 40 * 1727675 * 2
def baseEnd_1727675 : Nat := 887127689756633197317073

theorem tailTrace_1727675 : CollatzResearch.WordTrace tailWord_1727675 prefixEnd_1727675 887127689756633197317073 := by
  unfold tailWord_1727675
  simp only [CollatzResearch.WordTrace]
  refine ⟨63013484015936013243912479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42008989343957342162608319 63013484015936013243912479)
  ·
    refine ⟨94520226023904019865868719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63013484015936013243912479 94520226023904019865868719)
    ·
      refine ⟨141780339035856029798803079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94520226023904019865868719 141780339035856029798803079)
      ·
        refine ⟨212670508553784044698204619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141780339035856029798803079 212670508553784044698204619)
        ·
          refine ⟨319005762830676067047306929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212670508553784044698204619 319005762830676067047306929)
          ·
            refine ⟨239254322123007050285480197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319005762830676067047306929 239254322123007050285480197)
            ·
              refine ⟨44860185398063821928527537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239254322123007050285480197 44860185398063821928527537)
              ·
                refine ⟨33645139048547866446395653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44860185398063821928527537 33645139048547866446395653)
                ·
                  refine ⟨6308463571602724958699185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33645139048547866446395653 6308463571602724958699185)
                  ·
                    refine ⟨4731347678702043719024389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6308463571602724958699185 4731347678702043719024389)
                    ·
                      refine ⟨887127689756633197317073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4731347678702043719024389 887127689756633197317073)
                      ·
                        rfl

theorem cell23_1727675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_1727675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727675 prefixEnd_1727675 := by exact prefixLift 1727675
  have htrace : WordTrace (prefixWord ++ tailWord_1727675) baseStart_1727675 baseEnd_1727675 := by
    simpa [prefixWord, tailWord_1727675, baseEnd_1727675] using wordTrace_append hprefix tailTrace_1727675
  have hstable : (prefixWord ++ tailWord_1727675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727675).length < 2 ^ (prefixWord ++ tailWord_1727675).sum := by decide
  have hdescent : baseEnd_1727675 < baseStart_1727675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727679 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 4, 2, 2]
def baseStart_1727679 : Nat := 118140960795 + 1727679 * 2 ^ 59
def prefixEnd_1727679 : Nat := 4983230072969 + 3 ^ 40 * 1727679 * 2
def baseEnd_1727679 : Nat := 887129743679251181667055

theorem tailTrace_1727679 : CollatzResearch.WordTrace tailWord_1727679 prefixEnd_1727679 887129743679251181667055 := by
  unfold tailWord_1727679
  simp only [CollatzResearch.WordTrace]
  refine ⟨63013629907921521927058091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42009086605281014618038727 63013629907921521927058091)
  ·
    refine ⟨94520444861882282890587137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63013629907921521927058091 94520444861882282890587137)
    ·
      refine ⟨70890333646411712167940353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94520444861882282890587137 70890333646411712167940353)
      ·
        refine ⟨53167750234808784125955265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70890333646411712167940353 53167750234808784125955265)
        ·
          refine ⟨39875812676106588094466449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53167750234808784125955265 39875812676106588094466449)
          ·
            refine ⟨29906859507079941070849837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39875812676106588094466449 29906859507079941070849837)
            ·
              refine ⟨11215072315154977901568689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29906859507079941070849837 11215072315154977901568689)
              ·
                refine ⟨8411304236366233426176517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11215072315154977901568689 8411304236366233426176517)
                ·
                  refine ⟨1577119544318668767408097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8411304236366233426176517 1577119544318668767408097)
                  ·
                    refine ⟨1182839658239001575556073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577119544318668767408097 1182839658239001575556073)
                    ·
                      refine ⟨887129743679251181667055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182839658239001575556073 887129743679251181667055)
                      ·
                        rfl

theorem cell23_1727679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_1727679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727679 prefixEnd_1727679 := by exact prefixLift 1727679
  have htrace : WordTrace (prefixWord ++ tailWord_1727679) baseStart_1727679 baseEnd_1727679 := by
    simpa [prefixWord, tailWord_1727679, baseEnd_1727679] using wordTrace_append hprefix tailTrace_1727679
  have hstable : (prefixWord ++ tailWord_1727679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727679).length < 2 ^ (prefixWord ++ tailWord_1727679).sum := by decide
  have hdescent : baseEnd_1727679 < baseStart_1727679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727713 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_1727713 : Nat := 118140960795 + 1727713 * 2 ^ 59
def prefixEnd_1727713 : Nat := 4983230072969 + 3 ^ 40 * 1727713 * 2
def baseEnd_1727713 : Nat := 887147202021504048641899

theorem tailTrace_1727713 : CollatzResearch.WordTrace tailWord_1727713 prefixEnd_1727713 887147202021504048641899 := by
  unfold tailWord_1727713
  simp only [CollatzResearch.WordTrace]
  refine ⟨63014869989798345733795793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42009913326532230489197195 63014869989798345733795793)
  ·
    refine ⟨47261152492348759300346845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63014869989798345733795793 47261152492348759300346845)
    ·
      refine ⟨17722932184630784737630067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47261152492348759300346845 17722932184630784737630067)
      ·
        refine ⟨26584398276946177106445101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17722932184630784737630067 26584398276946177106445101)
        ·
          refine ⟨9969149353854816414916913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26584398276946177106445101 9969149353854816414916913)
          ·
            refine ⟨7476862015391112311187685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9969149353854816414916913 7476862015391112311187685)
            ·
              refine ⟨1401911627885833558347691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7476862015391112311187685 1401911627885833558347691)
              ·
                refine ⟨2102867441828750337521537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401911627885833558347691 2102867441828750337521537)
                ·
                  refine ⟨1577150581371562753141153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102867441828750337521537 1577150581371562753141153)
                  ·
                    refine ⟨1182862936028672064855865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577150581371562753141153 1182862936028672064855865)
                    ·
                      refine ⟨887147202021504048641899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182862936028672064855865 887147202021504048641899)
                      ·
                        rfl

theorem cell23_1727713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_1727713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727713 prefixEnd_1727713 := by exact prefixLift 1727713
  have htrace : WordTrace (prefixWord ++ tailWord_1727713) baseStart_1727713 baseEnd_1727713 := by
    simpa [prefixWord, tailWord_1727713, baseEnd_1727713] using wordTrace_append hprefix tailTrace_1727713
  have hstable : (prefixWord ++ tailWord_1727713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727713).length < 2 ^ (prefixWord ++ tailWord_1727713).sum := by decide
  have hdescent : baseEnd_1727713 < baseStart_1727713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727779 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 3, 4]
def baseStart_1727779 : Nat := 118140960795 + 1727779 * 2 ^ 59
def prefixEnd_1727779 : Nat := 4983230072969 + 3 ^ 40 * 1727779 * 2
def baseEnd_1727779 : Nat := 295727030581566930138865

theorem tailTrace_1727779 : CollatzResearch.WordTrace tailWord_1727779 prefixEnd_1727779 295727030581566930138865 := by
  unfold tailWord_1727779
  simp only [CollatzResearch.WordTrace]
  refine ⟨63017277207559239005698391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42011518138372826003798927 63017277207559239005698391)
  ·
    refine ⟨94525915811338858508547587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63017277207559239005698391 94525915811338858508547587)
    ·
      refine ⟨141788873717008287762821381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94525915811338858508547587 141788873717008287762821381)
      ·
        refine ⟨26585413821939053955529009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141788873717008287762821381 26585413821939053955529009)
        ·
          refine ⟨19939060366454290466646757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26585413821939053955529009 19939060366454290466646757)
          ·
            refine ⟨3738573818710179462496267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19939060366454290466646757 3738573818710179462496267)
            ·
              refine ⟨5607860728065269193744401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738573818710179462496267 5607860728065269193744401)
              ·
                refine ⟨4205895546048951895308301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607860728065269193744401 4205895546048951895308301)
                ·
                  refine ⟨1577210829768356960740613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4205895546048951895308301 1577210829768356960740613)
                  ·
                    refine ⟨295727030581566930138865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577210829768356960740613 295727030581566930138865)
                    ·
                      rfl

theorem cell23_1727779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 4].length) (baseStart_1727779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727779 prefixEnd_1727779 := by exact prefixLift 1727779
  have htrace : WordTrace (prefixWord ++ tailWord_1727779) baseStart_1727779 baseEnd_1727779 := by
    simpa [prefixWord, tailWord_1727779, baseEnd_1727779] using wordTrace_append hprefix tailTrace_1727779
  have hstable : (prefixWord ++ tailWord_1727779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727779).length < 2 ^ (prefixWord ++ tailWord_1727779).sum := by decide
  have hdescent : baseEnd_1727779 < baseStart_1727779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727786 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1727786 : Nat := 118140960795 + 1727786 * 2 ^ 59
def prefixEnd_1727786 : Nat := 4983230072969 + 3 ^ 40 * 1727786 * 2
def baseEnd_1727786 : Nat := 887184686109282263029063

theorem tailTrace_1727786 : CollatzResearch.WordTrace tailWord_1727786 prefixEnd_1727786 887184686109282263029063 := by
  unfold tailWord_1727786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15754383129633469800300803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42011688345689252800802141 15754383129633469800300803)
  ·
    refine ⟨23631574694450204700451205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15754383129633469800300803 23631574694450204700451205)
    ·
      refine ⟨4430920255209413381334601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23631574694450204700451205 4430920255209413381334601)
      ·
        refine ⟨3323190191407060036000951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430920255209413381334601 3323190191407060036000951)
        ·
          refine ⟨4984785287110590054001427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323190191407060036000951 4984785287110590054001427)
          ·
            refine ⟨7477177930665885081002141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984785287110590054001427 7477177930665885081002141)
            ·
              refine ⟨2803941723999706905375803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7477177930665885081002141 2803941723999706905375803)
              ·
                refine ⟨4205912585999560358063705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803941723999706905375803 4205912585999560358063705)
                ·
                  refine ⟨3154434439499670268547779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205912585999560358063705 3154434439499670268547779)
                  ·
                    refine ⟨4731651659249505402821669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3154434439499670268547779 4731651659249505402821669)
                    ·
                      refine ⟨887184686109282263029063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4731651659249505402821669 887184686109282263029063)
                      ·
                        rfl

theorem cell23_1727786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1727786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727786 prefixEnd_1727786 := by exact prefixLift 1727786
  have htrace : WordTrace (prefixWord ++ tailWord_1727786) baseStart_1727786 baseEnd_1727786 := by
    simpa [prefixWord, tailWord_1727786, baseEnd_1727786] using wordTrace_append hprefix tailTrace_1727786
  have hstable : (prefixWord ++ tailWord_1727786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727786).length < 2 ^ (prefixWord ++ tailWord_1727786).sum := by decide
  have hdescent : baseEnd_1727786 < baseStart_1727786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727809 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 8]
def baseStart_1727809 : Nat := 118140960795 + 1727809 * 2 ^ 59
def prefixEnd_1727809 : Nat := 4983230072969 + 3 ^ 40 * 1727809 * 2
def baseEnd_1727809 : Nat := 98577388462703963671273

theorem tailTrace_1727809 : CollatzResearch.WordTrace tailWord_1727809 prefixEnd_1727809 98577388462703963671273 := by
  unfold tailWord_1727809
  simp only [CollatzResearch.WordTrace]
  refine ⟨63018371397450554129290481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42012247598300369419526987 63018371397450554129290481)
  ·
    refine ⟨47263778548087915596967861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63018371397450554129290481 47263778548087915596967861)
    ·
      refine ⟨4430979238883242087215737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47263778548087915596967861 4430979238883242087215737)
      ·
        refine ⟨3323234429162431565411803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430979238883242087215737 3323234429162431565411803)
        ·
          refine ⟨4984851643743647348117705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323234429162431565411803 4984851643743647348117705)
          ·
            refine ⟨3738638732807735511088279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984851643743647348117705 3738638732807735511088279)
            ·
              refine ⟨5607958099211603266632419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738638732807735511088279 5607958099211603266632419)
              ·
                refine ⟨8411937148817404899948629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607958099211603266632419 8411937148817404899948629)
                ·
                  refine ⟨98577388462703963671273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8411937148817404899948629 98577388462703963671273)
                  ·
                    rfl

theorem cell23_1727809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 8].length) (baseStart_1727809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727809 prefixEnd_1727809 := by exact prefixLift 1727809
  have htrace : WordTrace (prefixWord ++ tailWord_1727809) baseStart_1727809 baseEnd_1727809 := by
    simpa [prefixWord, tailWord_1727809, baseEnd_1727809] using wordTrace_append hprefix tailTrace_1727809
  have hstable : (prefixWord ++ tailWord_1727809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727809).length < 2 ^ (prefixWord ++ tailWord_1727809).sum := by decide
  have hdescent : baseEnd_1727809 < baseStart_1727809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727869 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1727869 : Nat := 118140960795 + 1727869 * 2 ^ 59
def prefixEnd_1727869 : Nat := 4983230072969 + 3 ^ 40 * 1727869 * 2
def baseEnd_1727869 : Nat := 295742435001201812763727

theorem tailTrace_1727869 : CollatzResearch.WordTrace tailWord_1727869 prefixEnd_1727869 295742435001201812763727 := by
  unfold tailWord_1727869
  simp only [CollatzResearch.WordTrace]
  refine ⟨63020559777233184376474661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42013706518155456250983107 63020559777233184376474661)
  ·
    refine ⟨11816354958231222070588999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63020559777233184376474661 11816354958231222070588999)
    ·
      refine ⟨17724532437346833105883499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11816354958231222070588999 17724532437346833105883499)
      ·
        refine ⟨26586798656020249658825249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17724532437346833105883499 26586798656020249658825249)
        ·
          refine ⟨19940098992015187244118937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26586798656020249658825249 19940098992015187244118937)
          ·
            refine ⟨14955074244011390433089203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19940098992015187244118937 14955074244011390433089203)
            ·
              refine ⟨22432611366017085649633805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14955074244011390433089203 22432611366017085649633805)
              ·
                refine ⟨8412229262256407118612677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22432611366017085649633805 8412229262256407118612677)
                ·
                  refine ⟨1577292986673076334739877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8412229262256407118612677 1577292986673076334739877)
                  ·
                    refine ⟨295742435001201812763727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577292986673076334739877 295742435001201812763727)
                    ·
                      rfl

theorem cell23_1727869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1727869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727869 prefixEnd_1727869 := by exact prefixLift 1727869
  have htrace : WordTrace (prefixWord ++ tailWord_1727869) baseStart_1727869 baseEnd_1727869 := by
    simpa [prefixWord, tailWord_1727869, baseEnd_1727869] using wordTrace_append hprefix tailTrace_1727869
  have hstable : (prefixWord ++ tailWord_1727869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727869).length < 2 ^ (prefixWord ++ tailWord_1727869).sum := by decide
  have hdescent : baseEnd_1727869 < baseStart_1727869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727879 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1727879 : Nat := 118140960795 + 1727879 * 2 ^ 59
def prefixEnd_1727879 : Nat := 4983230072969 + 3 ^ 40 * 1727879 * 2
def baseEnd_1727879 : Nat := 887232439810150399166135

theorem tailTrace_1727879 : CollatzResearch.WordTrace tailWord_1727879 prefixEnd_1727879 887232439810150399166135 := by
  unfold tailWord_1727879
  simp only [CollatzResearch.WordTrace]
  refine ⟨63020924507196956084338691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42013949671464637389559127 63020924507196956084338691)
  ·
    refine ⟨94531386760795434126508037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63020924507196956084338691 94531386760795434126508037)
    ·
      refine ⟨17724635017649143898720257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94531386760795434126508037 17724635017649143898720257)
      ·
        refine ⟨13293476263236857924040193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17724635017649143898720257 13293476263236857924040193)
        ·
          refine ⟨9970107197427643443030145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13293476263236857924040193 9970107197427643443030145)
          ·
            refine ⟨7477580398070732582272609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9970107197427643443030145 7477580398070732582272609)
            ·
              refine ⟨5608185298553049436704457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7477580398070732582272609 5608185298553049436704457)
              ·
                refine ⟨4206138973914787077528343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608185298553049436704457 4206138973914787077528343)
                ·
                  refine ⟨6309208460872180616292515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206138973914787077528343 6309208460872180616292515)
                  ·
                    refine ⟨9463812691308270924438773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6309208460872180616292515 9463812691308270924438773)
                    ·
                      refine ⟨887232439810150399166135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9463812691308270924438773 887232439810150399166135)
                      ·
                        rfl

theorem cell23_1727879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1727879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727879 prefixEnd_1727879 := by exact prefixLift 1727879
  have htrace : WordTrace (prefixWord ++ tailWord_1727879) baseStart_1727879 baseEnd_1727879 := by
    simpa [prefixWord, tailWord_1727879, baseEnd_1727879] using wordTrace_append hprefix tailTrace_1727879
  have hstable : (prefixWord ++ tailWord_1727879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727879).length < 2 ^ (prefixWord ++ tailWord_1727879).sum := by decide
  have hdescent : baseEnd_1727879 < baseStart_1727879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727890 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1727890 : Nat := 118140960795 + 1727890 * 2 ^ 59
def prefixEnd_1727890 : Nat := 4983230072969 + 3 ^ 40 * 1727890 * 2
def baseEnd_1727890 : Nat := 295746029365783285376195

theorem tailTrace_1727890 : CollatzResearch.WordTrace tailWord_1727890 prefixEnd_1727890 295746029365783285376195 := by
  unfold tailWord_1727890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15755331427539276240747281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42014217140104736641992749 15755331427539276240747281)
  ·
    refine ⟨11816498570654457180560461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15755331427539276240747281 11816498570654457180560461)
    ·
      refine ⟨4431186963995421442710173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11816498570654457180560461 4431186963995421442710173)
      ·
        refine ⟨1661695111498283041016315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4431186963995421442710173 1661695111498283041016315)
        ·
          refine ⟨2492542667247424561524473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661695111498283041016315 2492542667247424561524473)
          ·
            refine ⟨1869407000435568421143355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2492542667247424561524473 1869407000435568421143355)
            ·
              refine ⟨2804110500653352631715033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869407000435568421143355 2804110500653352631715033)
              ·
                refine ⟨2103082875490014473786275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804110500653352631715033 2103082875490014473786275)
                ·
                  refine ⟨3154624313235021710679413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103082875490014473786275 3154624313235021710679413)
                  ·
                    refine ⟨295746029365783285376195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3154624313235021710679413 295746029365783285376195)
                    ·
                      rfl

theorem cell23_1727890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1727890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727890 prefixEnd_1727890 := by exact prefixLift 1727890
  have htrace : WordTrace (prefixWord ++ tailWord_1727890) baseStart_1727890 baseEnd_1727890 := by
    simpa [prefixWord, tailWord_1727890, baseEnd_1727890] using wordTrace_append hprefix tailTrace_1727890
  have hstable : (prefixWord ++ tailWord_1727890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727890).length < 2 ^ (prefixWord ++ tailWord_1727890).sum := by decide
  have hdescent : baseEnd_1727890 < baseStart_1727890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727906 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1727906 : Nat := 118140960795 + 1727906 * 2 ^ 59
def prefixEnd_1727906 : Nat := 4983230072969 + 3 ^ 40 * 1727906 * 2
def baseEnd_1727906 : Nat := 887246303787821793528511

theorem tailTrace_1727906 : CollatzResearch.WordTrace tailWord_1727906 prefixEnd_1727906 887246303787821793528511 := by
  unfold tailWord_1727906
  simp only [CollatzResearch.WordTrace]
  refine ⟨15755477319524784923892893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42014606185399426463714381 15755477319524784923892893)
  ·
    refine ⟨5908303994821794346459835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15755477319524784923892893 5908303994821794346459835)
    ·
      refine ⟨8862455992232691519689753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908303994821794346459835 8862455992232691519689753)
      ·
        refine ⟨6646841994174518639767315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8862455992232691519689753 6646841994174518639767315)
        ·
          refine ⟨9970262991261777959650973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6646841994174518639767315 9970262991261777959650973)
          ·
            refine ⟨3738848621723166734869115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9970262991261777959650973 3738848621723166734869115)
            ·
              refine ⟨5608272932584750102303673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738848621723166734869115 5608272932584750102303673)
              ·
                refine ⟨4206204699438562576727755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608272932584750102303673 4206204699438562576727755)
                ·
                  refine ⟨6309307049157843865091633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206204699438562576727755 6309307049157843865091633)
                  ·
                    refine ⟨4731980286868382898818725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6309307049157843865091633 4731980286868382898818725)
                    ·
                      refine ⟨887246303787821793528511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4731980286868382898818725 887246303787821793528511)
                      ·
                        rfl

theorem cell23_1727906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1727906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727906 prefixEnd_1727906 := by exact prefixLift 1727906
  have htrace : WordTrace (prefixWord ++ tailWord_1727906) baseStart_1727906 baseEnd_1727906 := by
    simpa [prefixWord, tailWord_1727906, baseEnd_1727906] using wordTrace_append hprefix tailTrace_1727906
  have hstable : (prefixWord ++ tailWord_1727906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727906).length < 2 ^ (prefixWord ++ tailWord_1727906).sum := by decide
  have hdescent : baseEnd_1727906 < baseStart_1727906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727936 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 3, 3, 2]
def baseStart_1727936 : Nat := 118140960795 + 1727936 * 2 ^ 59
def prefixEnd_1727936 : Nat := 4983230072969 + 3 ^ 40 * 1727936 * 2
def baseEnd_1727936 : Nat := 887261708207456676153373

theorem tailTrace_1727936 : CollatzResearch.WordTrace tailWord_1727936 prefixEnd_1727936 887261708207456676153373 := by
  unfold tailWord_1727936
  simp only [CollatzResearch.WordTrace]
  refine ⟨31511501733995227409581831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42015335645326969879442441 31511501733995227409581831)
  ·
    refine ⟨47267252600992841114372747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31511501733995227409581831 47267252600992841114372747)
    ·
      refine ⟨70900878901489261671559121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47267252600992841114372747 70900878901489261671559121)
      ·
        refine ⟨53175659176116946253669341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70900878901489261671559121 53175659176116946253669341)
        ·
          refine ⟨19940872191043854845126003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53175659176116946253669341 19940872191043854845126003)
          ·
            refine ⟨29911308286565782267689005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19940872191043854845126003 29911308286565782267689005)
            ·
              refine ⟨11216740607462168350383377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29911308286565782267689005 11216740607462168350383377)
              ·
                refine ⟨8412555455596626262787533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11216740607462168350383377 8412555455596626262787533)
                ·
                  refine ⟨3154708295848734848545325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8412555455596626262787533 3154708295848734848545325)
                  ·
                    refine ⟨1183015610943275568204497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3154708295848734848545325 1183015610943275568204497)
                    ·
                      refine ⟨887261708207456676153373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183015610943275568204497 887261708207456676153373)
                      ·
                        rfl

theorem cell23_1727936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_1727936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727936 prefixEnd_1727936 := by exact prefixLift 1727936
  have htrace : WordTrace (prefixWord ++ tailWord_1727936) baseStart_1727936 baseEnd_1727936 := by
    simpa [prefixWord, tailWord_1727936, baseEnd_1727936] using wordTrace_append hprefix tailTrace_1727936
  have hstable : (prefixWord ++ tailWord_1727936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727936).length < 2 ^ (prefixWord ++ tailWord_1727936).sum := by decide
  have hdescent : baseEnd_1727936 < baseStart_1727936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727999 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 3]
def baseStart_1727999 : Nat := 118140960795 + 1727999 * 2 ^ 59
def prefixEnd_1727999 : Nat := 4983230072969 + 3 ^ 40 * 1727999 * 2
def baseEnd_1727999 : Nat := 887294057488689929665583

theorem tailTrace_1727999 : CollatzResearch.WordTrace tailWord_1727999 prefixEnd_1727999 887294057488689929665583 := by
  unfold tailWord_1727999
  simp only [CollatzResearch.WordTrace]
  refine ⟨63025301266762216578707051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42016867511174811052471367 63025301266762216578707051)
  ·
    refine ⟨94537951900143324868060577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63025301266762216578707051 94537951900143324868060577)
    ·
      refine ⟨70903463925107493651045433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94537951900143324868060577 70903463925107493651045433)
      ·
        refine ⟨53177597943830620238284075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70903463925107493651045433 53177597943830620238284075)
        ·
          refine ⟨79766396915745930357426113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53177597943830620238284075 79766396915745930357426113)
          ·
            refine ⟨59824797686809447768069585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79766396915745930357426113 59824797686809447768069585)
            ·
              refine ⟨44868598265107085826052189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59824797686809447768069585 44868598265107085826052189)
              ·
                refine ⟨16825724349415157184769571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44868598265107085826052189 16825724349415157184769571)
                ·
                  refine ⟨25238586524122735777154357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16825724349415157184769571 25238586524122735777154357)
                  ·
                    refine ⟨2366117486636506479108221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25238586524122735777154357 2366117486636506479108221)
                    ·
                      refine ⟨887294057488689929665583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2366117486636506479108221 887294057488689929665583)
                      ·
                        rfl

theorem cell23_1727999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_1727999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1727999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1727999 prefixEnd_1727999 := by exact prefixLift 1727999
  have htrace : WordTrace (prefixWord ++ tailWord_1727999) baseStart_1727999 baseEnd_1727999 := by
    simpa [prefixWord, tailWord_1727999, baseEnd_1727999] using wordTrace_append hprefix tailTrace_1727999
  have hstable : (prefixWord ++ tailWord_1727999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727999).length < 2 ^ (prefixWord ++ tailWord_1727999).sum := by decide
  have hdescent : baseEnd_1727999 < baseStart_1727999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728019 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 1, 7]
def baseStart_1728019 : Nat := 118140960795 + 1728019 * 2 ^ 59
def prefixEnd_1728019 : Nat := 4983230072969 + 3 ^ 40 * 1728019 * 2
def baseEnd_1728019 : Nat := 295768109033926617138497

theorem tailTrace_1728019 : CollatzResearch.WordTrace tailWord_1728019 prefixEnd_1728019 295768109033926617138497 := by
  unfold tailWord_1728019
  simp only [CollatzResearch.WordTrace]
  refine ⟨63026030726689759994435111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42017353817793173329623407 63026030726689759994435111)
  ·
    refine ⟨94539046090034639991652667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63026030726689759994435111 94539046090034639991652667)
    ·
      refine ⟨141808569135051959987479001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94539046090034639991652667 141808569135051959987479001)
      ·
        refine ⟨106356426851288969990609251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141808569135051959987479001 106356426851288969990609251)
        ·
          refine ⟨159534640276933454985913877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106356426851288969990609251 159534640276933454985913877)
          ·
            refine ⟨7478186262981255702464713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159534640276933454985913877 7478186262981255702464713)
            ·
              refine ⟨5608639697235941776848535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7478186262981255702464713 5608639697235941776848535)
              ·
                refine ⟨8412959545853912665272803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608639697235941776848535 8412959545853912665272803)
                ·
                  refine ⟨12619439318780868997909205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412959545853912665272803 12619439318780868997909205)
                  ·
                    refine ⟨295768109033926617138497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12619439318780868997909205 295768109033926617138497)
                    ·
                      rfl

theorem cell23_1728019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 7].length) (baseStart_1728019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728019 prefixEnd_1728019 := by exact prefixLift 1728019
  have htrace : WordTrace (prefixWord ++ tailWord_1728019) baseStart_1728019 baseEnd_1728019 := by
    simpa [prefixWord, tailWord_1728019, baseEnd_1728019] using wordTrace_append hprefix tailTrace_1728019
  have hstable : (prefixWord ++ tailWord_1728019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728019).length < 2 ^ (prefixWord ++ tailWord_1728019).sum := by decide
  have hdescent : baseEnd_1728019 < baseStart_1728019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728026 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2]
def baseStart_1728026 : Nat := 118140960795 + 1728026 * 2 ^ 59
def prefixEnd_1728026 : Nat := 4983230072969 + 3 ^ 40 * 1728026 * 2
def baseEnd_1728026 : Nat := 887307921466361324027959

theorem tailTrace_1728026 : CollatzResearch.WordTrace tailWord_1728026 prefixEnd_1728026 887307921466361324027959 := by
  unfold tailWord_1728026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15756571509416100047484983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42017524025109600126626621 15756571509416100047484983)
  ·
    refine ⟨23634857264124150071227475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15756571509416100047484983 23634857264124150071227475)
    ·
      refine ⟨35452285896186225106841213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23634857264124150071227475 35452285896186225106841213)
      ·
        refine ⟨13294607211069834415065455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35452285896186225106841213 13294607211069834415065455)
        ·
          refine ⟨19941910816604751622598183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13294607211069834415065455 19941910816604751622598183)
          ·
            refine ⟨29912866224907127433897275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19941910816604751622598183 29912866224907127433897275)
            ·
              refine ⟨44869299337360691150845913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29912866224907127433897275 44869299337360691150845913)
              ·
                refine ⟨33651974503020518363134435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44869299337360691150845913 33651974503020518363134435)
                ·
                  refine ⟨50477961754530777544701653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33651974503020518363134435 50477961754530777544701653)
                  ·
                    refine ⟨1183077228621815098703945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50477961754530777544701653 1183077228621815098703945)
                    ·
                      refine ⟨887307921466361324027959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183077228621815098703945 887307921466361324027959)
                      ·
                        rfl

theorem cell23_1728026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_1728026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728026 prefixEnd_1728026 := by exact prefixLift 1728026
  have htrace : WordTrace (prefixWord ++ tailWord_1728026) baseStart_1728026 baseEnd_1728026 := by
    simpa [prefixWord, tailWord_1728026, baseEnd_1728026] using wordTrace_append hprefix tailTrace_1728026
  have hstable : (prefixWord ++ tailWord_1728026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728026).length < 2 ^ (prefixWord ++ tailWord_1728026).sum := by decide
  have hdescent : baseEnd_1728026 < baseStart_1728026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728040 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 7]
def baseStart_1728040 : Nat := 118140960795 + 1728040 * 2 ^ 59
def prefixEnd_1728040 : Nat := 4983230072969 + 3 ^ 40 * 1728040 * 2
def baseEnd_1728040 : Nat := 98590567799502696583655

theorem tailTrace_1728040 : CollatzResearch.WordTrace tailWord_1728040 prefixEnd_1728040 98590567799502696583655 := by
  unfold tailWord_1728040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31513398329806840290474787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42017864439742453720633049 31513398329806840290474787)
  ·
    refine ⟨47270097494710260435712181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31513398329806840290474787 47270097494710260435712181)
    ·
      refine ⟨4431571640129086915848017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47270097494710260435712181 4431571640129086915848017)
      ·
        refine ⟨3323678730096815186886013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4431571640129086915848017 3323678730096815186886013)
        ·
          refine ⟨1246379523786305695082255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3323678730096815186886013 1246379523786305695082255)
          ·
            refine ⟨1869569285679458542623383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246379523786305695082255 1869569285679458542623383)
            ·
              refine ⟨2804353928519187813935075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869569285679458542623383 2804353928519187813935075)
              ·
                refine ⟨4206530892778781720902613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804353928519187813935075 4206530892778781720902613)
                ·
                  refine ⟨98590567799502696583655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4206530892778781720902613 98590567799502696583655)
                  ·
                    rfl

theorem cell23_1728040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 7].length) (baseStart_1728040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728040 prefixEnd_1728040 := by exact prefixLift 1728040
  have htrace : WordTrace (prefixWord ++ tailWord_1728040) baseStart_1728040 baseEnd_1728040 := by
    simpa [prefixWord, tailWord_1728040, baseEnd_1728040] using wordTrace_append hprefix tailTrace_1728040
  have hstable : (prefixWord ++ tailWord_1728040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728040).length < 2 ^ (prefixWord ++ tailWord_1728040).sum := by decide
  have hdescent : baseEnd_1728040 < baseStart_1728040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728046 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1728046 : Nat := 118140960795 + 1728046 * 2 ^ 59
def prefixEnd_1728046 : Nat := 4983230072969 + 3 ^ 40 * 1728046 * 2
def baseEnd_1728046 : Nat := 887318191079451245777867

theorem tailTrace_1728046 : CollatzResearch.WordTrace tailWord_1728046 prefixEnd_1728046 887318191079451245777867 := by
  unfold tailWord_1728046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878376937198992950708499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42018010331727962403778661 7878376937198992950708499)
  ·
    refine ⟨11817565405798489426062749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7878376937198992950708499 11817565405798489426062749)
    ·
      refine ⟨4431587027174433534773531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11817565405798489426062749 4431587027174433534773531)
      ·
        refine ⟨6647380540761650302160297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431587027174433534773531 6647380540761650302160297)
        ·
          refine ⟨4985535405571237726620223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6647380540761650302160297 4985535405571237726620223)
          ·
            refine ⟨7478303108356856589930335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985535405571237726620223 7478303108356856589930335)
            ·
              refine ⟨11217454662535284884895503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7478303108356856589930335 11217454662535284884895503)
              ·
                refine ⟨16826181993802927327343255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11217454662535284884895503 16826181993802927327343255)
                ·
                  refine ⟨25239272990704390991014883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16826181993802927327343255 25239272990704390991014883)
                  ·
                    refine ⟨37858909486056586486522325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25239272990704390991014883 37858909486056586486522325)
                    ·
                      refine ⟨887318191079451245777867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37858909486056586486522325 887318191079451245777867)
                      ·
                        rfl

theorem cell23_1728046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1728046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728046 prefixEnd_1728046 := by exact prefixLift 1728046
  have htrace : WordTrace (prefixWord ++ tailWord_1728046) baseStart_1728046 baseEnd_1728046 := by
    simpa [prefixWord, tailWord_1728046, baseEnd_1728046] using wordTrace_append hprefix tailTrace_1728046
  have hstable : (prefixWord ++ tailWord_1728046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728046).length < 2 ^ (prefixWord ++ tailWord_1728046).sum := by decide
  have hdescent : baseEnd_1728046 < baseStart_1728046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728100 : List Nat := [2, 3, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1728100 : Nat := 118140960795 + 1728100 * 2 ^ 59
def prefixEnd_1728100 : Nat := 4983230072969 + 3 ^ 40 * 1728100 * 2
def baseEnd_1728100 : Nat := 295781973011598011500873

theorem tailTrace_1728100 : CollatzResearch.WordTrace tailWord_1728100 prefixEnd_1728100 295781973011598011500873 := by
  unfold tailWord_1728100
  simp only [CollatzResearch.WordTrace]
  refine ⟨31514492519698155414066877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42019323359597540552089169 31514492519698155414066877)
  ·
    refine ⟨11817934694886808280275079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31514492519698155414066877 11817934694886808280275079)
    ·
      refine ⟨17726902042330212420412619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11817934694886808280275079 17726902042330212420412619)
      ·
        refine ⟨26590353063495318630618929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17726902042330212420412619 26590353063495318630618929)
        ·
          refine ⟨19942764797621488972964197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26590353063495318630618929 19942764797621488972964197)
          ·
            refine ⟨3739268399554029182430787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19942764797621488972964197 3739268399554029182430787)
            ·
              refine ⟨5608902599331043773646181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739268399554029182430787 5608902599331043773646181)
              ·
                refine ⟨1051669237374570707558659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5608902599331043773646181 1051669237374570707558659)
                ·
                  refine ⟨1577503856061856061337989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051669237374570707558659 1577503856061856061337989)
                  ·
                    refine ⟨295781973011598011500873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577503856061856061337989 295781973011598011500873)
                    ·
                      rfl

theorem cell23_1728100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1728100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728100 prefixEnd_1728100 := by exact prefixLift 1728100
  have htrace : WordTrace (prefixWord ++ tailWord_1728100) baseStart_1728100 baseEnd_1728100 := by
    simpa [prefixWord, tailWord_1728100, baseEnd_1728100] using wordTrace_append hprefix tailTrace_1728100
  have hstable : (prefixWord ++ tailWord_1728100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728100).length < 2 ^ (prefixWord ++ tailWord_1728100).sum := by decide
  have hdescent : baseEnd_1728100 < baseStart_1728100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728119 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1728119 : Nat := 118140960795 + 1728119 * 2 ^ 59
def prefixEnd_1728119 : Nat := 4983230072969 + 3 ^ 40 * 1728119 * 2
def baseEnd_1728119 : Nat := 887355675167229460165031

theorem tailTrace_1728119 : CollatzResearch.WordTrace tailWord_1728119 prefixEnd_1728119 887355675167229460165031 := by
  unfold tailWord_1728119
  simp only [CollatzResearch.WordTrace]
  refine ⟨63029678026327477073075411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42019785350884984715383607 63029678026327477073075411)
  ·
    refine ⟨94544517039491215609613117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63029678026327477073075411 94544517039491215609613117)
    ·
      refine ⟨35454193889809205853604919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94544517039491215609613117 35454193889809205853604919)
      ·
        refine ⟨53181290834713808780407379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35454193889809205853604919 53181290834713808780407379)
        ·
          refine ⟨79771936252070713170611069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53181290834713808780407379 79771936252070713170611069)
          ·
            refine ⟨29914476094526517438979151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79771936252070713170611069 29914476094526517438979151)
            ·
              refine ⟨44871714141789776158468727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29914476094526517438979151 44871714141789776158468727)
              ·
                refine ⟨67307571212684664237703091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44871714141789776158468727 67307571212684664237703091)
                ·
                  refine ⟨100961356819026996356554637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67307571212684664237703091 100961356819026996356554637)
                  ·
                    refine ⟨37860508807135123633707989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100961356819026996356554637 37860508807135123633707989)
                    ·
                      refine ⟨887355675167229460165031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37860508807135123633707989 887355675167229460165031)
                      ·
                        rfl

theorem cell23_1728119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1728119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728119 prefixEnd_1728119 := by exact prefixLift 1728119
  have htrace : WordTrace (prefixWord ++ tailWord_1728119) baseStart_1728119 baseEnd_1728119 := by
    simpa [prefixWord, tailWord_1728119, baseEnd_1728119] using wordTrace_append hprefix tailTrace_1728119
  have hstable : (prefixWord ++ tailWord_1728119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728119).length < 2 ^ (prefixWord ++ tailWord_1728119).sum := by decide
  have hdescent : baseEnd_1728119 < baseStart_1728119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728123 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 3]
def baseStart_1728123 : Nat := 118140960795 + 1728123 * 2 ^ 59
def prefixEnd_1728123 : Nat := 4983230072969 + 3 ^ 40 * 1728123 * 2
def baseEnd_1728123 : Nat := 887357729089847444515013

theorem tailTrace_1728123 : CollatzResearch.WordTrace tailWord_1728123 prefixEnd_1728123 887357729089847444515013 := by
  unfold tailWord_1728123
  simp only [CollatzResearch.WordTrace]
  refine ⟨63029823918312985756221023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42019882612208657170814015 63029823918312985756221023)
  ·
    refine ⟨94544735877469478634331535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63029823918312985756221023 94544735877469478634331535)
    ·
      refine ⟨141817103816204217951497303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94544735877469478634331535 141817103816204217951497303)
      ·
        refine ⟨212725655724306326927245955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141817103816204217951497303 212725655724306326927245955)
        ·
          refine ⟨319088483586459490390868933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212725655724306326927245955 319088483586459490390868933)
          ·
            refine ⟨59829090672461154448287925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319088483586459490390868933 59829090672461154448287925)
            ·
              refine ⟨5608977250543233229526993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59829090672461154448287925 5608977250543233229526993)
              ·
                refine ⟨4206732937907424922145245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608977250543233229526993 4206732937907424922145245)
                ·
                  refine ⟨1577524851715284345804467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4206732937907424922145245 1577524851715284345804467)
                  ·
                    refine ⟨2366287277572926518706701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1577524851715284345804467 2366287277572926518706701)
                    ·
                      refine ⟨887357729089847444515013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2366287277572926518706701 887357729089847444515013)
                      ·
                        rfl

theorem cell23_1728123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 3].length) (baseStart_1728123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728123 prefixEnd_1728123 := by exact prefixLift 1728123
  have htrace : WordTrace (prefixWord ++ tailWord_1728123) baseStart_1728123 baseEnd_1728123 := by
    simpa [prefixWord, tailWord_1728123, baseEnd_1728123] using wordTrace_append hprefix tailTrace_1728123
  have hstable : (prefixWord ++ tailWord_1728123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728123).length < 2 ^ (prefixWord ++ tailWord_1728123).sum := by decide
  have hdescent : baseEnd_1728123 < baseStart_1728123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728133 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 1, 5, 2]
def baseStart_1728133 : Nat := 118140960795 + 1728133 * 2 ^ 59
def prefixEnd_1728133 : Nat := 4983230072969 + 3 ^ 40 * 1728133 * 2
def baseEnd_1728133 : Nat := 887362863896392405389967

theorem tailTrace_1728133 : CollatzResearch.WordTrace tailWord_1728133 prefixEnd_1728133 887362863896392405389967 := by
  unfold tailWord_1728133
  simp only [CollatzResearch.WordTrace]
  refine ⟨63030188648276757464085053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42020125765517838309390035 63030188648276757464085053)
  ·
    refine ⟨23636320743103784049031895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63030188648276757464085053 23636320743103784049031895)
    ·
      refine ⟨35454481114655676073547843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23636320743103784049031895 35454481114655676073547843)
      ·
        refine ⟨53181721671983514110321765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35454481114655676073547843 53181721671983514110321765)
        ·
          refine ⟨9971572813496908895685331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53181721671983514110321765 9971572813496908895685331)
          ·
            refine ⟨14957359220245363343527997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9971572813496908895685331 14957359220245363343527997)
            ·
              refine ⟨5609009707592011253822999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14957359220245363343527997 5609009707592011253822999)
              ·
                refine ⟨8413514561388016880734499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609009707592011253822999 8413514561388016880734499)
                ·
                  refine ⟨12620271842082025321101749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8413514561388016880734499 12620271842082025321101749)
                  ·
                    refine ⟨1183150485195189873853289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12620271842082025321101749 1183150485195189873853289)
                    ·
                      refine ⟨887362863896392405389967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183150485195189873853289 887362863896392405389967)
                      ·
                        rfl

theorem cell23_1728133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_1728133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728133 prefixEnd_1728133 := by exact prefixLift 1728133
  have htrace : WordTrace (prefixWord ++ tailWord_1728133) baseStart_1728133 baseEnd_1728133 := by
    simpa [prefixWord, tailWord_1728133, baseEnd_1728133] using wordTrace_append hprefix tailTrace_1728133
  have hstable : (prefixWord ++ tailWord_1728133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728133).length < 2 ^ (prefixWord ++ tailWord_1728133).sum := by decide
  have hdescent : baseEnd_1728133 < baseStart_1728133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728186 : List Nat := [3, 1, 1, 1, 2, 5, 1, 9]
def baseStart_1728186 : Nat := 118140960795 + 1728186 * 2 ^ 59
def prefixEnd_1728186 : Nat := 4983230072969 + 3 ^ 40 * 1728186 * 2
def baseEnd_1728186 : Nat := 32866299198928914741749

theorem tailTrace_1728186 : CollatzResearch.WordTrace tailWord_1728186 prefixEnd_1728186 32866299198928914741749 := by
  unfold tailWord_1728186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758030429271186878941103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42021414478056498343842941 15758030429271186878941103)
  ·
    refine ⟨23637045643906780318411655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15758030429271186878941103 23637045643906780318411655)
    ·
      refine ⟨35455568465860170477617483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23637045643906780318411655 35455568465860170477617483)
      ·
        refine ⟨53183352698790255716426225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35455568465860170477617483 53183352698790255716426225)
        ·
          refine ⟨39887514524092691787319669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53183352698790255716426225 39887514524092691787319669)
          ·
            refine ⟨3739454486633689855061219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39887514524092691787319669 3739454486633689855061219)
            ·
              refine ⟨5609181729950534782591829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739454486633689855061219 5609181729950534782591829)
              ·
                refine ⟨32866299198928914741749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5609181729950534782591829 32866299198928914741749)
                ·
                  rfl

theorem cell23_1728186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_1728186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728186 prefixEnd_1728186 := by exact prefixLift 1728186
  have htrace : WordTrace (prefixWord ++ tailWord_1728186) baseStart_1728186 baseEnd_1728186 := by
    simpa [prefixWord, tailWord_1728186, baseEnd_1728186] using wordTrace_append hprefix tailTrace_1728186
  have hstable : (prefixWord ++ tailWord_1728186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728186).length < 2 ^ (prefixWord ++ tailWord_1728186).sum := by decide
  have hdescent : baseEnd_1728186 < baseStart_1728186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728216 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 2, 7]
def baseStart_1728216 : Nat := 118140960795 + 1728216 * 2 ^ 59
def prefixEnd_1728216 : Nat := 4983230072969 + 3 ^ 40 * 1728216 * 2
def baseEnd_1728216 : Nat := 295801827596905193550695

theorem tailTrace_1728216 : CollatzResearch.WordTrace tailWord_1728216 prefixEnd_1728216 295801827596905193550695 := by
  unfold tailWord_1728216
  simp only [CollatzResearch.WordTrace]
  refine ⟨31516607953488031319678251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42022143937984041759571001 31516607953488031319678251)
  ·
    refine ⟨47274911930232046979517377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31516607953488031319678251 47274911930232046979517377)
    ·
      refine ⟨35456183947674035234638033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47274911930232046979517377 35456183947674035234638033)
      ·
        refine ⟨26592137960755526425978525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35456183947674035234638033 26592137960755526425978525)
        ·
          refine ⟨9972051735283322409741947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26592137960755526425978525 9972051735283322409741947)
          ·
            refine ⟨14958077602924983614612921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972051735283322409741947 14958077602924983614612921)
            ·
              refine ⟨11218558202193737710959691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14958077602924983614612921 11218558202193737710959691)
              ·
                refine ⟨16827837303290606566439537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11218558202193737710959691 16827837303290606566439537)
                ·
                  refine ⟨12620877977467954924829653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16827837303290606566439537 12620877977467954924829653)
                  ·
                    refine ⟨295801827596905193550695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12620877977467954924829653 295801827596905193550695)
                    ·
                      rfl

theorem cell23_1728216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_1728216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728216 prefixEnd_1728216 := by exact prefixLift 1728216
  have htrace : WordTrace (prefixWord ++ tailWord_1728216) baseStart_1728216 baseEnd_1728216 := by
    simpa [prefixWord, tailWord_1728216, baseEnd_1728216] using wordTrace_append hprefix tailTrace_1728216
  have hstable : (prefixWord ++ tailWord_1728216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728216).length < 2 ^ (prefixWord ++ tailWord_1728216).sum := by decide
  have hdescent : baseEnd_1728216 < baseStart_1728216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728220 : List Nat := [2, 2, 5, 1, 2, 1, 2, 8]
def baseStart_1728220 : Nat := 118140960795 + 1728220 * 2 ^ 59
def prefixEnd_1728220 : Nat := 4983230072969 + 3 ^ 40 * 1728220 * 2
def baseEnd_1728220 : Nat := 32866945804197539444521

theorem tailTrace_1728220 : CollatzResearch.WordTrace tailWord_1728220 prefixEnd_1728220 32866945804197539444521 := by
  unfold tailWord_1728220
  simp only [CollatzResearch.WordTrace]
  refine ⟨31516680899480785661251057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42022241199307714215001409 31516680899480785661251057)
  ·
    refine ⟨23637510674610589245938293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31516680899480785661251057 23637510674610589245938293)
    ·
      refine ⟨2216016625744742741806715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23637510674610589245938293 2216016625744742741806715)
      ·
        refine ⟨3324024938617114112710073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216016625744742741806715 3324024938617114112710073)
        ·
          refine ⟨2493018703962835584532555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324024938617114112710073 2493018703962835584532555)
          ·
            refine ⟨3739528055944253376798833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493018703962835584532555 3739528055944253376798833)
            ·
              refine ⟨2804646041958190032599125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739528055944253376798833 2804646041958190032599125)
              ·
                refine ⟨32866945804197539444521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2804646041958190032599125 32866945804197539444521)
                ·
                  rfl

theorem cell23_1728220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 8].length) (baseStart_1728220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728220 prefixEnd_1728220 := by exact prefixLift 1728220
  have htrace : WordTrace (prefixWord ++ tailWord_1728220) baseStart_1728220 baseEnd_1728220 := by
    simpa [prefixWord, tailWord_1728220, baseEnd_1728220] using wordTrace_append hprefix tailTrace_1728220
  have hstable : (prefixWord ++ tailWord_1728220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728220).length < 2 ^ (prefixWord ++ tailWord_1728220).sum := by decide
  have hdescent : baseEnd_1728220 < baseStart_1728220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728240 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 1, 3, 2]
def baseStart_1728240 : Nat := 118140960795 + 1728240 * 2 ^ 59
def prefixEnd_1728240 : Nat := 4983230072969 + 3 ^ 40 * 1728240 * 2
def baseEnd_1728240 : Nat := 887417806326423486751975

theorem tailTrace_1728240 : CollatzResearch.WordTrace tailWord_1728240 prefixEnd_1728240 887417806326423486751975 := by
  unfold tailWord_1728240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31517045629444557369115087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42022727505926076492153449 31517045629444557369115087)
  ·
    refine ⟨47275568444166836053672631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31517045629444557369115087 47275568444166836053672631)
    ·
      refine ⟨70913352666250254080508947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47275568444166836053672631 70913352666250254080508947)
      ·
        refine ⟨106370028999375381120763421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70913352666250254080508947 106370028999375381120763421)
        ·
          refine ⟨39888760874765767920286283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106370028999375381120763421 39888760874765767920286283)
          ·
            refine ⟨59833141312148651880429425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39888760874765767920286283 59833141312148651880429425)
            ·
              refine ⟨44874855984111488910322069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59833141312148651880429425 44874855984111488910322069)
              ·
                refine ⟨2103508874255226042671347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44874855984111488910322069 2103508874255226042671347)
                ·
                  refine ⟨3155263311382839064007021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103508874255226042671347 3155263311382839064007021)
                  ·
                    refine ⟨1183223741768564649002633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155263311382839064007021 1183223741768564649002633)
                    ·
                      refine ⟨887417806326423486751975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183223741768564649002633 887417806326423486751975)
                      ·
                        rfl

theorem cell23_1728240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 3, 2].length) (baseStart_1728240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728240 prefixEnd_1728240 := by exact prefixLift 1728240
  have htrace : WordTrace (prefixWord ++ tailWord_1728240) baseStart_1728240 baseEnd_1728240 := by
    simpa [prefixWord, tailWord_1728240, baseEnd_1728240] using wordTrace_append hprefix tailTrace_1728240
  have hstable : (prefixWord ++ tailWord_1728240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728240).length < 2 ^ (prefixWord ++ tailWord_1728240).sum := by decide
  have hdescent : baseEnd_1728240 < baseStart_1728240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728287 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 2, 2, 2]
def baseStart_1728287 : Nat := 118140960795 + 1728287 * 2 ^ 59
def prefixEnd_1728287 : Nat := 4983230072969 + 3 ^ 40 * 1728287 * 2
def baseEnd_1728287 : Nat := 887441939917184802864259

theorem tailTrace_1728287 : CollatzResearch.WordTrace tailWord_1728287 prefixEnd_1728287 887441939917184802864259 := by
  unfold tailWord_1728287
  simp only [CollatzResearch.WordTrace]
  refine ⟨63035805489718841765191115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42023870326479227843460743 63035805489718841765191115)
  ·
    refine ⟨94553708234578262647786673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63035805489718841765191115 94553708234578262647786673)
    ·
      refine ⟨70915281175933696985840005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94553708234578262647786673 70915281175933696985840005)
      ·
        refine ⟨13296615220487568184845001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70915281175933696985840005 13296615220487568184845001)
        ·
          refine ⟨9972461415365676138633751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13296615220487568184845001 9972461415365676138633751)
          ·
            refine ⟨14958692123048514207950627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972461415365676138633751 14958692123048514207950627)
            ·
              refine ⟨22438038184572771311925941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14958692123048514207950627 22438038184572771311925941)
              ·
                refine ⟨2103566079803697310493057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22438038184572771311925941 2103566079803697310493057)
                ·
                  refine ⟨1577674559852772982869793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103566079803697310493057 1577674559852772982869793)
                  ·
                    refine ⟨1183255919889579737152345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577674559852772982869793 1183255919889579737152345)
                    ·
                      refine ⟨887441939917184802864259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183255919889579737152345 887441939917184802864259)
                      ·
                        rfl

theorem cell23_1728287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_1728287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728287 prefixEnd_1728287 := by exact prefixLift 1728287
  have htrace : WordTrace (prefixWord ++ tailWord_1728287) baseStart_1728287 baseEnd_1728287 := by
    simpa [prefixWord, tailWord_1728287, baseEnd_1728287] using wordTrace_append hprefix tailTrace_1728287
  have hstable : (prefixWord ++ tailWord_1728287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728287).length < 2 ^ (prefixWord ++ tailWord_1728287).sum := by decide
  have hdescent : baseEnd_1728287 < baseStart_1728287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728293 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 7]
def baseStart_1728293 : Nat := 118140960795 + 1728293 * 2 ^ 59
def prefixEnd_1728293 : Nat := 4983230072969 + 3 ^ 40 * 1728293 * 2
def baseEnd_1728293 : Nat := 98605002311234642154359

theorem tailTrace_1728293 : CollatzResearch.WordTrace tailWord_1728293 prefixEnd_1728293 98605002311234642154359 := by
  unfold tailWord_1728293
  simp only [CollatzResearch.WordTrace]
  refine ⟨63036024327697104789909533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42024016218464736526606355 63036024327697104789909533)
  ·
    refine ⟨23638509122886414296216075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63036024327697104789909533 23638509122886414296216075)
    ·
      refine ⟨35457763684329621444324113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23638509122886414296216075 35457763684329621444324113)
      ·
        refine ⟨26593322763247216083243085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35457763684329621444324113 26593322763247216083243085)
        ·
          refine ⟨9972496036217706031216157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26593322763247216083243085 9972496036217706031216157)
          ·
            refine ⟨3739686013581639761706059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9972496036217706031216157 3739686013581639761706059)
            ·
              refine ⟨5609529020372459642559089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739686013581639761706059 5609529020372459642559089)
              ·
                refine ⟨4207146765279344731919317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5609529020372459642559089 4207146765279344731919317)
                ·
                  refine ⟨98605002311234642154359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4207146765279344731919317 98605002311234642154359)
                  ·
                    rfl

theorem cell23_1728293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_1728293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728293 prefixEnd_1728293 := by exact prefixLift 1728293
  have htrace : WordTrace (prefixWord ++ tailWord_1728293) baseStart_1728293 baseEnd_1728293 := by
    simpa [prefixWord, tailWord_1728293, baseEnd_1728293] using wordTrace_append hprefix tailTrace_1728293
  have hstable : (prefixWord ++ tailWord_1728293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728293).length < 2 ^ (prefixWord ++ tailWord_1728293).sum := by decide
  have hdescent : baseEnd_1728293 < baseStart_1728293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728360 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1728360 : Nat := 118140960795 + 1728360 * 2 ^ 59
def prefixEnd_1728360 : Nat := 4983230072969 + 3 ^ 40 * 1728360 * 2
def baseEnd_1728360 : Nat := 887479424004963017251423

theorem tailTrace_1728360 : CollatzResearch.WordTrace tailWord_1728360 prefixEnd_1728360 887479424004963017251423 := by
  unfold tailWord_1728360
  simp only [CollatzResearch.WordTrace]
  refine ⟨31519234009227187616299267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42025645345636250155065689 31519234009227187616299267)
  ·
    refine ⟨47278851013840781424448901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31519234009227187616299267 47278851013840781424448901)
    ·
      refine ⟨8864784565095146517084169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47278851013840781424448901 8864784565095146517084169)
      ·
        refine ⟨6648588423821359887813127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8864784565095146517084169 6648588423821359887813127)
        ·
          refine ⟨9972882635732039831719691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6648588423821359887813127 9972882635732039831719691)
          ·
            refine ⟨14959323953598059747579537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972882635732039831719691 14959323953598059747579537)
            ·
              refine ⟨11219492965198544810684653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14959323953598059747579537 11219492965198544810684653)
              ·
                refine ⟨4207309861949454304006745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11219492965198544810684653 4207309861949454304006745)
                ·
                  refine ⟨3155482396462090728005059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207309861949454304006745 3155482396462090728005059)
                  ·
                    refine ⟨4733223594693136092007589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3155482396462090728005059 4733223594693136092007589)
                    ·
                      refine ⟨887479424004963017251423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4733223594693136092007589 887479424004963017251423)
                      ·
                        rfl

theorem cell23_1728360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1728360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728360 prefixEnd_1728360 := by exact prefixLift 1728360
  have htrace : WordTrace (prefixWord ++ tailWord_1728360) baseStart_1728360 baseEnd_1728360 := by
    simpa [prefixWord, tailWord_1728360, baseEnd_1728360] using wordTrace_append hprefix tailTrace_1728360
  have hstable : (prefixWord ++ tailWord_1728360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728360).length < 2 ^ (prefixWord ++ tailWord_1728360).sum := by decide
  have hdescent : baseEnd_1728360 < baseStart_1728360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728383 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 6]
def baseStart_1728383 : Nat := 118140960795 + 1728383 * 2 ^ 59
def prefixEnd_1728383 : Nat := 4983230072969 + 3 ^ 40 * 1728383 * 2
def baseEnd_1728383 : Nat := 98610137117779603029313

theorem tailTrace_1728383 : CollatzResearch.WordTrace tailWord_1728383 prefixEnd_1728383 98610137117779603029313 := by
  unfold tailWord_1728383
  simp only [CollatzResearch.WordTrace]
  refine ⟨63039306897371050160685803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42026204598247366773790535 63039306897371050160685803)
  ·
    refine ⟨94558960346056575241028705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63039306897371050160685803 94558960346056575241028705)
    ·
      refine ⟨70919220259542431430771529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94558960346056575241028705 70919220259542431430771529)
      ·
        refine ⟨53189415194656823573078647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70919220259542431430771529 53189415194656823573078647)
        ·
          refine ⟨79784122791985235359617971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53189415194656823573078647 79784122791985235359617971)
          ·
            refine ⟨119676184187977853039426957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79784122791985235359617971 119676184187977853039426957)
            ·
              refine ⟨44878569070491694889785109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119676184187977853039426957 44878569070491694889785109)
              ·
                refine ⟨2103682925179298197958677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44878569070491694889785109 2103682925179298197958677)
                ·
                  refine ⟨98610137117779603029313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2103682925179298197958677 98610137117779603029313)
                  ·
                    rfl

theorem cell23_1728383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 6].length) (baseStart_1728383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728383 prefixEnd_1728383 := by exact prefixLift 1728383
  have htrace : WordTrace (prefixWord ++ tailWord_1728383) baseStart_1728383 baseEnd_1728383 := by
    simpa [prefixWord, tailWord_1728383, baseEnd_1728383] using wordTrace_append hprefix tailTrace_1728383
  have hstable : (prefixWord ++ tailWord_1728383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728383).length < 2 ^ (prefixWord ++ tailWord_1728383).sum := by decide
  have hdescent : baseEnd_1728383 < baseStart_1728383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728387 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 3, 4]
def baseStart_1728387 : Nat := 118140960795 + 1728387 * 2 ^ 59
def prefixEnd_1728387 : Nat := 4983230072969 + 3 ^ 40 * 1728387 * 2
def baseEnd_1728387 : Nat := 295831095994211470537933

theorem tailTrace_1728387 : CollatzResearch.WordTrace tailWord_1728387 prefixEnd_1728387 295831095994211470537933 := by
  unfold tailWord_1728387
  simp only [CollatzResearch.WordTrace]
  refine ⟨63039452789356558843831415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42026301859571039229220943 63039452789356558843831415)
  ·
    refine ⟨94559179184034838265747123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63039452789356558843831415 94559179184034838265747123)
    ·
      refine ⟨141838768776052257398620685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94559179184034838265747123 141838768776052257398620685)
      ·
        refine ⟨53189538291019596524482757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141838768776052257398620685 53189538291019596524482757)
        ·
          refine ⟨9973038429566174348340517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53189538291019596524482757 9973038429566174348340517)
          ·
            refine ⟨1869944705543657690313847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9973038429566174348340517 1869944705543657690313847)
            ·
              refine ⟨2804917058315486535470771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869944705543657690313847 2804917058315486535470771)
              ·
                refine ⟨4207375587473229803206157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804917058315486535470771 4207375587473229803206157)
                ·
                  refine ⟨1577765845302461176202309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4207375587473229803206157 1577765845302461176202309)
                  ·
                    refine ⟨295831095994211470537933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577765845302461176202309 295831095994211470537933)
                    ·
                      rfl

theorem cell23_1728387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 4].length) (baseStart_1728387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728387 prefixEnd_1728387 := by exact prefixLift 1728387
  have htrace : WordTrace (prefixWord ++ tailWord_1728387) baseStart_1728387 baseEnd_1728387 := by
    simpa [prefixWord, tailWord_1728387, baseEnd_1728387] using wordTrace_append hprefix tailTrace_1728387
  have hstable : (prefixWord ++ tailWord_1728387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728387).length < 2 ^ (prefixWord ++ tailWord_1728387).sum := by decide
  have hdescent : baseEnd_1728387 < baseStart_1728387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728460 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_1728460 : Nat := 118140960795 + 1728460 * 2 ^ 59
def prefixEnd_1728460 : Nat := 4983230072969 + 3 ^ 40 * 1728460 * 2
def baseEnd_1728460 : Nat := 295843590690137542000321

theorem tailTrace_1728460 : CollatzResearch.WordTrace tailWord_1728460 prefixEnd_1728460 295843590690137542000321 := by
  unfold tailWord_1728460
  simp only [CollatzResearch.WordTrace]
  refine ⟨31521057659046046155619417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42028076878728061540825889 31521057659046046155619417)
  ·
    refine ⟨23640793244284534616714563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31521057659046046155619417 23640793244284534616714563)
    ·
      refine ⟨35461189866426801925071845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23640793244284534616714563 35461189866426801925071845)
      ·
        refine ⟨6648973099955025360950971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35461189866426801925071845 6648973099955025360950971)
        ·
          refine ⟨9973459649932538041426457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6648973099955025360950971 9973459649932538041426457)
          ·
            refine ⟨7480094737449403531069843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9973459649932538041426457 7480094737449403531069843)
            ·
              refine ⟨11220142106174105296604765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7480094737449403531069843 11220142106174105296604765)
              ·
                refine ⟨4207553289815289486226787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11220142106174105296604765 4207553289815289486226787)
                ·
                  refine ⟨6311329934722934229340181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207553289815289486226787 6311329934722934229340181)
                  ·
                    refine ⟨295843590690137542000321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6311329934722934229340181 295843590690137542000321)
                    ·
                      rfl

theorem cell23_1728460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_1728460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728460 prefixEnd_1728460 := by exact prefixLift 1728460
  have htrace : WordTrace (prefixWord ++ tailWord_1728460) baseStart_1728460 baseEnd_1728460 := by
    simpa [prefixWord, tailWord_1728460, baseEnd_1728460] using wordTrace_append hprefix tailTrace_1728460
  have hstable : (prefixWord ++ tailWord_1728460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728460).length < 2 ^ (prefixWord ++ tailWord_1728460).sum := by decide
  have hdescent : baseEnd_1728460 < baseStart_1728460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728494 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1728494 : Nat := 118140960795 + 1728494 * 2 ^ 59
def prefixEnd_1728494 : Nat := 4983230072969 + 3 ^ 40 * 1728494 * 2
def baseEnd_1728494 : Nat := 295849410137555164325269

theorem tailTrace_1728494 : CollatzResearch.WordTrace tailWord_1728494 prefixEnd_1728494 295849410137555164325269 := by
  unfold tailWord_1728494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880419424996114514747067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42028903599979277411984357 7880419424996114514747067)
  ·
    refine ⟨11820629137494171772120601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7880419424996114514747067 11820629137494171772120601)
    ·
      refine ⟨8865471853120628829090451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11820629137494171772120601 8865471853120628829090451)
      ·
        refine ⟨13298207779680943243635677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865471853120628829090451 13298207779680943243635677)
        ·
          refine ⟨4986827917380353716363379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13298207779680943243635677 4986827917380353716363379)
          ·
            refine ⟨7480241876070530574545069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4986827917380353716363379 7480241876070530574545069)
            ·
              refine ⟨2805090703526448965454401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7480241876070530574545069 2805090703526448965454401)
              ·
                refine ⟨2103818027644836724090801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805090703526448965454401 2103818027644836724090801)
                ·
                  refine ⟨1577863520733627543068101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103818027644836724090801 1577863520733627543068101)
                  ·
                    refine ⟨295849410137555164325269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577863520733627543068101 295849410137555164325269)
                    ·
                      rfl

theorem cell23_1728494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1728494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728494 prefixEnd_1728494 := by exact prefixLift 1728494
  have htrace : WordTrace (prefixWord ++ tailWord_1728494) baseStart_1728494 baseEnd_1728494 := by
    simpa [prefixWord, tailWord_1728494, baseEnd_1728494] using wordTrace_append hprefix tailTrace_1728494
  have hstable : (prefixWord ++ tailWord_1728494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728494).length < 2 ^ (prefixWord ++ tailWord_1728494).sum := by decide
  have hdescent : baseEnd_1728494 < baseStart_1728494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728517 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_1728517 : Nat := 118140960795 + 1728517 * 2 ^ 59
def prefixEnd_1728517 : Nat := 4983230072969 + 3 ^ 40 * 1728517 * 2
def baseEnd_1728517 : Nat := 887560040467718902988201

theorem tailTrace_1728517 : CollatzResearch.WordTrace tailWord_1728517 prefixEnd_1728517 887560040467718902988201 := by
  unfold tailWord_1728517
  simp only [CollatzResearch.WordTrace]
  refine ⟨63044194278885591046063805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42029462852590394030709203 63044194278885591046063805)
  ·
    refine ⟨23641572854582096642273927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63044194278885591046063805 23641572854582096642273927)
    ·
      refine ⟨35462359281873144963410891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23641572854582096642273927 35462359281873144963410891)
      ·
        refine ⟨53193538922809717445116337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35462359281873144963410891 53193538922809717445116337)
        ·
          refine ⟨39895154192107288083837253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53193538922809717445116337 39895154192107288083837253)
          ·
            refine ⟨7480341411020116515719485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39895154192107288083837253 7480341411020116515719485)
            ·
              refine ⟨2805128029132543693394807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7480341411020116515719485 2805128029132543693394807)
              ·
                refine ⟨4207692043698815540092211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805128029132543693394807 4207692043698815540092211)
                ·
                  refine ⟨6311538065548223310138317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207692043698815540092211 6311538065548223310138317)
                  ·
                    refine ⟨2366826774580583741301869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6311538065548223310138317 2366826774580583741301869)
                    ·
                      refine ⟨887560040467718902988201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2366826774580583741301869 887560040467718902988201)
                      ·
                        rfl

theorem cell23_1728517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_1728517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728517 prefixEnd_1728517 := by exact prefixLift 1728517
  have htrace : WordTrace (prefixWord ++ tailWord_1728517) baseStart_1728517 baseEnd_1728517 := by
    simpa [prefixWord, tailWord_1728517, baseEnd_1728517] using wordTrace_append hprefix tailTrace_1728517
  have hstable : (prefixWord ++ tailWord_1728517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728517).length < 2 ^ (prefixWord ++ tailWord_1728517).sum := by decide
  have hdescent : baseEnd_1728517 < baseStart_1728517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728535 : List Nat := [1, 1, 3, 5, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1728535 : Nat := 118140960795 + 1728535 * 2 ^ 59
def prefixEnd_1728535 : Nat := 4983230072969 + 3 ^ 40 * 1728535 * 2
def baseEnd_1728535 : Nat := 887569283119499832563119

theorem tailTrace_1728535 : CollatzResearch.WordTrace tailWord_1728535 prefixEnd_1728535 887569283119499832563119 := by
  unfold tailWord_1728535
  simp only [CollatzResearch.WordTrace]
  refine ⟨63044850792820380120219059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42029900528546920080146039 63044850792820380120219059)
  ·
    refine ⟨94567276189230570180328589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63044850792820380120219059 94567276189230570180328589)
    ·
      refine ⟨35462728570961463817623221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94567276189230570180328589 35462728570961463817623221)
      ·
        refine ⟨3324630803527637232902177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35462728570961463817623221 3324630803527637232902177)
        ·
          refine ⟨2493473102645727924676633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324630803527637232902177 2493473102645727924676633)
          ·
            refine ⟨1870104826984295943507475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2493473102645727924676633 1870104826984295943507475)
            ·
              refine ⟨2805157240476443915261213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870104826984295943507475 2805157240476443915261213)
              ·
                refine ⟨1051933965178666468222955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2805157240476443915261213 1051933965178666468222955)
                ·
                  refine ⟨1577900947767999702334433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051933965178666468222955 1577900947767999702334433)
                  ·
                    refine ⟨1183425710825999776750825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577900947767999702334433 1183425710825999776750825)
                    ·
                      refine ⟨887569283119499832563119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183425710825999776750825 887569283119499832563119)
                      ·
                        rfl

theorem cell23_1728535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1728535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728535 prefixEnd_1728535 := by exact prefixLift 1728535
  have htrace : WordTrace (prefixWord ++ tailWord_1728535) baseStart_1728535 baseEnd_1728535 := by
    simpa [prefixWord, tailWord_1728535, baseEnd_1728535] using wordTrace_append hprefix tailTrace_1728535
  have hstable : (prefixWord ++ tailWord_1728535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728535).length < 2 ^ (prefixWord ++ tailWord_1728535).sum := by decide
  have hdescent : baseEnd_1728535 < baseStart_1728535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728552 : List Nat := [2, 1, 5, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1728552 : Nat := 118140960795 + 1728552 * 2 ^ 59
def prefixEnd_1728552 : Nat := 4983230072969 + 3 ^ 40 * 1728552 * 2
def baseEnd_1728552 : Nat := 887578012290626266050541

theorem tailTrace_1728552 : CollatzResearch.WordTrace tailWord_1728552 prefixEnd_1728552 887578012290626266050541 := by
  unfold tailWord_1728552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31522735416879396011793955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42030313889172528015725273 31522735416879396011793955)
  ·
    refine ⟨47284103125319094017690933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31522735416879396011793955 47284103125319094017690933)
    ·
      refine ⟨4432884667998665064158525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47284103125319094017690933 4432884667998665064158525)
      ·
        refine ⟨1662331750499499399059447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4432884667998665064158525 1662331750499499399059447)
        ·
          refine ⟨2493497625749249098589171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662331750499499399059447 2493497625749249098589171)
          ·
            refine ⟨3740246438623873647883757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493497625749249098589171 3740246438623873647883757)
            ·
              refine ⟨1402592414483952617956409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3740246438623873647883757 1402592414483952617956409)
              ·
                refine ⟨1051944310862964463467307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402592414483952617956409 1051944310862964463467307)
                ·
                  refine ⟨1577916466294446695200961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051944310862964463467307 1577916466294446695200961)
                  ·
                    refine ⟨1183437349720835021400721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577916466294446695200961 1183437349720835021400721)
                    ·
                      refine ⟨887578012290626266050541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183437349720835021400721 887578012290626266050541)
                      ·
                        rfl

theorem cell23_1728552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1728552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728552 prefixEnd_1728552 := by exact prefixLift 1728552
  have htrace : WordTrace (prefixWord ++ tailWord_1728552) baseStart_1728552 baseEnd_1728552 := by
    simpa [prefixWord, tailWord_1728552, baseEnd_1728552] using wordTrace_append hprefix tailTrace_1728552
  have hstable : (prefixWord ++ tailWord_1728552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728552).length < 2 ^ (prefixWord ++ tailWord_1728552).sum := by decide
  have hdescent : baseEnd_1728552 < baseStart_1728552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728568 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 2, 1, 3]
def baseStart_1728568 : Nat := 118140960795 + 1728568 * 2 ^ 59
def prefixEnd_1728568 : Nat := 4983230072969 + 3 ^ 40 * 1728568 * 2
def baseEnd_1728568 : Nat := 887586227981098203450467

theorem tailTrace_1728568 : CollatzResearch.WordTrace tailWord_1728568 prefixEnd_1728568 887586227981098203450467 := by
  unfold tailWord_1728568
  simp only [CollatzResearch.WordTrace]
  refine ⟨31523027200850413378085179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42030702934467217837446905 31523027200850413378085179)
  ·
    refine ⟨47284540801275620067127769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31523027200850413378085179 47284540801275620067127769)
    ·
      refine ⟨35463405600956715050345827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47284540801275620067127769 35463405600956715050345827)
      ·
        refine ⟨53195108401435072575518741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35463405600956715050345827 53195108401435072575518741)
        ·
          refine ⟨2493520706317269026977441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53195108401435072575518741 2493520706317269026977441)
          ·
            refine ⟨1870140529737951770233081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2493520706317269026977441 1870140529737951770233081)
            ·
              refine ⟨1402605397303463827674811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870140529737951770233081 1402605397303463827674811)
              ·
                refine ⟨2103908095955195741512217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402605397303463827674811 2103908095955195741512217)
                ·
                  refine ⟨1577931071966396806134163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103908095955195741512217 1577931071966396806134163)
                  ·
                    refine ⟨2366896607949595209201245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1577931071966396806134163 2366896607949595209201245)
                    ·
                      refine ⟨887586227981098203450467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2366896607949595209201245 887586227981098203450467)
                      ·
                        rfl

theorem cell23_1728568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_1728568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728568 prefixEnd_1728568 := by exact prefixLift 1728568
  have htrace : WordTrace (prefixWord ++ tailWord_1728568) baseStart_1728568 baseEnd_1728568 := by
    simpa [prefixWord, tailWord_1728568, baseEnd_1728568] using wordTrace_append hprefix tailTrace_1728568
  have hstable : (prefixWord ++ tailWord_1728568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728568).length < 2 ^ (prefixWord ++ tailWord_1728568).sum := by decide
  have hdescent : baseEnd_1728568 < baseStart_1728568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728570 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_1728570 : Nat := 118140960795 + 1728570 * 2 ^ 59
def prefixEnd_1728570 : Nat := 4983230072969 + 3 ^ 40 * 1728570 * 2
def baseEnd_1728570 : Nat := 887587254942407195625457

theorem tailTrace_1728570 : CollatzResearch.WordTrace tailWord_1728570 prefixEnd_1728570 887587254942407195625457 := by
  unfold tailWord_1728570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15761531836923395274435791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42030751565129054065162109 15761531836923395274435791)
  ·
    refine ⟨23642297755385092911653687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15761531836923395274435791 23642297755385092911653687)
    ·
      refine ⟨35463446633077639367480531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23642297755385092911653687 35463446633077639367480531)
      ·
        refine ⟨53195169949616459051220797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35463446633077639367480531 53195169949616459051220797)
        ·
          refine ⟨19948188731106172144207799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53195169949616459051220797 19948188731106172144207799)
          ·
            refine ⟨29922283096659258216311699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19948188731106172144207799 29922283096659258216311699)
            ·
              refine ⟨44883424644988887324467549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29922283096659258216311699 44883424644988887324467549)
              ·
                refine ⟨16831284241870832746675331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44883424644988887324467549 16831284241870832746675331)
                ·
                  refine ⟨25246926362806249120012997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16831284241870832746675331 25246926362806249120012997)
                  ·
                    refine ⟨4733798693026171710002437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25246926362806249120012997 4733798693026171710002437)
                    ·
                      refine ⟨887587254942407195625457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4733798693026171710002437 887587254942407195625457)
                      ·
                        rfl

theorem cell23_1728570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_1728570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728570 prefixEnd_1728570 := by exact prefixLift 1728570
  have htrace : WordTrace (prefixWord ++ tailWord_1728570) baseStart_1728570 baseEnd_1728570 := by
    simpa [prefixWord, tailWord_1728570, baseEnd_1728570] using wordTrace_append hprefix tailTrace_1728570
  have hstable : (prefixWord ++ tailWord_1728570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728570).length < 2 ^ (prefixWord ++ tailWord_1728570).sum := by decide
  have hdescent : baseEnd_1728570 < baseStart_1728570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728577 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1728577 : Nat := 118140960795 + 1728577 * 2 ^ 59
def prefixEnd_1728577 : Nat := 4983230072969 + 3 ^ 40 * 1728577 * 2
def baseEnd_1728577 : Nat := 887590849306988668237925

theorem tailTrace_1728577 : CollatzResearch.WordTrace tailWord_1728577 prefixEnd_1728577 887590849306988668237925 := by
  unfold tailWord_1728577
  simp only [CollatzResearch.WordTrace]
  refine ⟨63046382658668221293247985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42030921772445480862165323 63046382658668221293247985)
  ·
    refine ⟨47284786994001165969935989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63046382658668221293247985 47284786994001165969935989)
    ·
      refine ⟨4432948780687609309681499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47284786994001165969935989 4432948780687609309681499)
      ·
        refine ⟨6649423171031413964522249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4432948780687609309681499 6649423171031413964522249)
        ·
          refine ⟨4987067378273560473391687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6649423171031413964522249 4987067378273560473391687)
          ·
            refine ⟨7480601067410340710087531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987067378273560473391687 7480601067410340710087531)
            ·
              refine ⟨11220901601115511065131297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7480601067410340710087531 11220901601115511065131297)
              ·
                refine ⟨8415676200836633298848473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11220901601115511065131297 8415676200836633298848473)
                ·
                  refine ⟨6311757150627474974136355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8415676200836633298848473 6311757150627474974136355)
                  ·
                    refine ⟨9467635725941212461204533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6311757150627474974136355 9467635725941212461204533)
                    ·
                      refine ⟨887590849306988668237925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9467635725941212461204533 887590849306988668237925)
                      ·
                        rfl

theorem cell23_1728577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1728577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728577 prefixEnd_1728577 := by exact prefixLift 1728577
  have htrace : WordTrace (prefixWord ++ tailWord_1728577) baseStart_1728577 baseEnd_1728577 := by
    simpa [prefixWord, tailWord_1728577, baseEnd_1728577] using wordTrace_append hprefix tailTrace_1728577
  have hstable : (prefixWord ++ tailWord_1728577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728577).length < 2 ^ (prefixWord ++ tailWord_1728577).sum := by decide
  have hdescent : baseEnd_1728577 < baseStart_1728577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728617 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 7, 2]
def baseStart_1728617 : Nat := 118140960795 + 1728617 * 2 ^ 59
def prefixEnd_1728617 : Nat := 4983230072969 + 3 ^ 40 * 1728617 * 2
def baseEnd_1728617 : Nat := 887611388533168511737741

theorem tailTrace_1728617 : CollatzResearch.WordTrace tailWord_1728617 prefixEnd_1728617 887611388533168511737741 := by
  unfold tailWord_1728617
  simp only [CollatzResearch.WordTrace]
  refine ⟨63047841578523308124704105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42031894385682205416469403 63047841578523308124704105)
  ·
    refine ⟨47285881183892481093528079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63047841578523308124704105 47285881183892481093528079)
    ·
      refine ⟨70928821775838721640292119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47285881183892481093528079 70928821775838721640292119)
      ·
        refine ⟨106393232663758082460438179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70928821775838721640292119 106393232663758082460438179)
        ·
          refine ⟨159589848995637123690657269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106393232663758082460438179 159589848995637123690657269)
          ·
            refine ⟨14961548343340980345999119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159589848995637123690657269 14961548343340980345999119)
            ·
              refine ⟨22442322515011470518998679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14961548343340980345999119 22442322515011470518998679)
              ·
                refine ⟨33663483772517205778498019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22442322515011470518998679 33663483772517205778498019)
                ·
                  refine ⟨50495225658775808667747029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33663483772517205778498019 50495225658775808667747029)
                  ·
                    refine ⟨1183481851377558015650321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50495225658775808667747029 1183481851377558015650321)
                    ·
                      refine ⟨887611388533168511737741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183481851377558015650321 887611388533168511737741)
                      ·
                        rfl

theorem cell23_1728617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 7, 2].length) (baseStart_1728617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728617 prefixEnd_1728617 := by exact prefixLift 1728617
  have htrace : WordTrace (prefixWord ++ tailWord_1728617) baseStart_1728617 baseEnd_1728617 := by
    simpa [prefixWord, tailWord_1728617, baseEnd_1728617] using wordTrace_append hprefix tailTrace_1728617
  have hstable : (prefixWord ++ tailWord_1728617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728617).length < 2 ^ (prefixWord ++ tailWord_1728617).sum := by decide
  have hdescent : baseEnd_1728617 < baseStart_1728617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728697 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1728697 : Nat := 118140960795 + 1728697 * 2 ^ 59
def prefixEnd_1728697 : Nat := 4983230072969 + 3 ^ 40 * 1728697 * 2
def baseEnd_1728697 : Nat := 887652466985528198737373

theorem tailTrace_1728697 : CollatzResearch.WordTrace tailWord_1728697 prefixEnd_1728697 887652466985528198737373 := by
  unfold tailWord_1728697
  simp only [CollatzResearch.WordTrace]
  refine ⟨63050759418233481787616345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42033839612155654525077563 63050759418233481787616345)
  ·
    refine ⟨47288069563675111340712259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63050759418233481787616345 47288069563675111340712259)
    ·
      refine ⟨70932104345512667011068389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47288069563675111340712259 70932104345512667011068389)
      ·
        refine ⟨13299769564783625064575323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70932104345512667011068389 13299769564783625064575323)
        ·
          refine ⟨19949654347175437596862985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13299769564783625064575323 19949654347175437596862985)
          ·
            refine ⟨14962240760381578197647239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19949654347175437596862985 14962240760381578197647239)
            ·
              refine ⟨22443361140572367296470859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14962240760381578197647239 22443361140572367296470859)
              ·
                refine ⟨33665041710858550944706289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22443361140572367296470859 33665041710858550944706289)
                ·
                  refine ⟨25248781283143913208529717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33665041710858550944706289 25248781283143913208529717)
                  ·
                    refine ⟨2367073245294741863299661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25248781283143913208529717 2367073245294741863299661)
                    ·
                      refine ⟨887652466985528198737373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2367073245294741863299661 887652466985528198737373)
                      ·
                        rfl

theorem cell23_1728697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1728697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728697 prefixEnd_1728697 := by exact prefixLift 1728697
  have htrace : WordTrace (prefixWord ++ tailWord_1728697) baseStart_1728697 baseEnd_1728697 := by
    simpa [prefixWord, tailWord_1728697, baseEnd_1728697] using wordTrace_append hprefix tailTrace_1728697
  have hstable : (prefixWord ++ tailWord_1728697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728697).length < 2 ^ (prefixWord ++ tailWord_1728697).sum := by decide
  have hdescent : baseEnd_1728697 < baseStart_1728697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728708 : List Nat := [2, 3, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1728708 : Nat := 118140960795 + 1728708 * 2 ^ 59
def prefixEnd_1728708 : Nat := 4983230072969 + 3 ^ 40 * 1728708 * 2
def baseEnd_1728708 : Nat := 295886038424242551899941

theorem tailTrace_1728708 : CollatzResearch.WordTrace tailWord_1728708 prefixEnd_1728708 295886038424242551899941 := by
  unfold tailWord_1728708
  simp only [CollatzResearch.WordTrace]
  refine ⟨31525580310596815333133389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42034107080795753777511185 31525580310596815333133389)
  ·
    refine ⟨11822092616473805749925021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31525580310596815333133389 11822092616473805749925021)
    ·
      refine ⟨4433284731177677156221883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11822092616473805749925021 4433284731177677156221883)
      ·
        refine ⟨6649927096766515734332825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4433284731177677156221883 6649927096766515734332825)
        ·
          refine ⟨4987445322574886800749619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6649927096766515734332825 4987445322574886800749619)
          ·
            refine ⟨7481167983862330201124429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987445322574886800749619 7481167983862330201124429)
            ·
              refine ⟨2805437993948373825421661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7481167983862330201124429 2805437993948373825421661)
              ·
                refine ⟨1052039247730640184533123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2805437993948373825421661 1052039247730640184533123)
                ·
                  refine ⟨1578058871595960276799685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052039247730640184533123 1578058871595960276799685)
                  ·
                    refine ⟨295886038424242551899941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1578058871595960276799685 295886038424242551899941)
                    ·
                      rfl

theorem cell23_1728708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1728708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728708 prefixEnd_1728708 := by exact prefixLift 1728708
  have htrace : WordTrace (prefixWord ++ tailWord_1728708) baseStart_1728708 baseEnd_1728708 := by
    simpa [prefixWord, tailWord_1728708, baseEnd_1728708] using wordTrace_append hprefix tailTrace_1728708
  have hstable : (prefixWord ++ tailWord_1728708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728708).length < 2 ^ (prefixWord ++ tailWord_1728708).sum := by decide
  have hdescent : baseEnd_1728708 < baseStart_1728708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728725 : List Nat := [1, 3, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_1728725 : Nat := 118140960795 + 1728725 * 2 ^ 59
def prefixEnd_1728725 : Nat := 4983230072969 + 3 ^ 40 * 1728725 * 2
def baseEnd_1728725 : Nat := 295888948147951363062415

theorem tailTrace_1728725 : CollatzResearch.WordTrace tailWord_1728725 prefixEnd_1728725 295888948147951363062415 := by
  unfold tailWord_1728725
  simp only [CollatzResearch.WordTrace]
  refine ⟨63051780662132042569635629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42034520441421361713090419 63051780662132042569635629)
  ·
    refine ⟨23644417748299515963613361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63051780662132042569635629 23644417748299515963613361)
    ·
      refine ⟨17733313311224636972710021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23644417748299515963613361 17733313311224636972710021)
      ·
        refine ⟨3324996245854619432383129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17733313311224636972710021 3324996245854619432383129)
        ·
          refine ⟨2493747184390964574287347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324996245854619432383129 2493747184390964574287347)
          ·
            refine ⟨3740620776586446861431021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493747184390964574287347 3740620776586446861431021)
            ·
              refine ⟨1402732791219917573036633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3740620776586446861431021 1402732791219917573036633)
              ·
                refine ⟨1052049593414938179777475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402732791219917573036633 1052049593414938179777475)
                ·
                  refine ⟨1578074390122407269666213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052049593414938179777475 1578074390122407269666213)
                  ·
                    refine ⟨295888948147951363062415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1578074390122407269666213 295888948147951363062415)
                    ·
                      rfl

theorem cell23_1728725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_1728725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728725 prefixEnd_1728725 := by exact prefixLift 1728725
  have htrace : WordTrace (prefixWord ++ tailWord_1728725) baseStart_1728725 baseEnd_1728725 := by
    simpa [prefixWord, tailWord_1728725, baseEnd_1728725] using wordTrace_append hprefix tailTrace_1728725
  have hstable : (prefixWord ++ tailWord_1728725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728725).length < 2 ^ (prefixWord ++ tailWord_1728725).sum := by decide
  have hdescent : baseEnd_1728725 < baseStart_1728725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728747 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 1, 6]
def baseStart_1728747 : Nat := 118140960795 + 1728747 * 2 ^ 59
def prefixEnd_1728747 : Nat := 4983230072969 + 3 ^ 40 * 1728747 * 2
def baseEnd_1728747 : Nat := 295892713672751001037381

theorem tailTrace_1728747 : CollatzResearch.WordTrace tailWord_1728747 prefixEnd_1728747 295892713672751001037381 := by
  unfold tailWord_1728747
  simp only [CollatzResearch.WordTrace]
  refine ⟨63052583068052340326936495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42035055378701560217957663 63052583068052340326936495)
  ·
    refine ⟨94578874602078510490404743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63052583068052340326936495 94578874602078510490404743)
    ·
      refine ⟨141868311903117765735607115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94578874602078510490404743 141868311903117765735607115)
      ·
        refine ⟨212802467854676648603410673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141868311903117765735607115 212802467854676648603410673)
        ·
          refine ⟨159601850891007486452558005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212802467854676648603410673 159601850891007486452558005)
          ·
            refine ⟨14962673521031951854927313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159601850891007486452558005 14962673521031951854927313)
            ·
              refine ⟨11222005140773963891195485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14962673521031951854927313 11222005140773963891195485)
              ·
                refine ⟨4208251927790236459198307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11222005140773963891195485 4208251927790236459198307)
                ·
                  refine ⟨6312377891685354688797461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208251927790236459198307 6312377891685354688797461)
                  ·
                    refine ⟨295892713672751001037381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6312377891685354688797461 295892713672751001037381)
                    ·
                      rfl

theorem cell23_1728747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 6].length) (baseStart_1728747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728747 prefixEnd_1728747 := by exact prefixLift 1728747
  have htrace : WordTrace (prefixWord ++ tailWord_1728747) baseStart_1728747 baseEnd_1728747 := by
    simpa [prefixWord, tailWord_1728747, baseEnd_1728747] using wordTrace_append hprefix tailTrace_1728747
  have hstable : (prefixWord ++ tailWord_1728747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728747).length < 2 ^ (prefixWord ++ tailWord_1728747).sum := by decide
  have hdescent : baseEnd_1728747 < baseStart_1728747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728751 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 1, 5]
def baseStart_1728751 : Nat := 118140960795 + 1728751 * 2 ^ 59
def prefixEnd_1728751 : Nat := 4983230072969 + 3 ^ 40 * 1728751 * 2
def baseEnd_1728751 : Nat := 295893398313623662487375

theorem tailTrace_1728751 : CollatzResearch.WordTrace tailWord_1728751 prefixEnd_1728751 295893398313623662487375 := by
  unfold tailWord_1728751
  simp only [CollatzResearch.WordTrace]
  refine ⟨63052728960037849010082107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42035152640025232673388071 63052728960037849010082107)
  ·
    refine ⟨94579093440056773515123161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63052728960037849010082107 94579093440056773515123161)
    ·
      refine ⟨70934320080042580136342371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94579093440056773515123161 70934320080042580136342371)
      ·
        refine ⟨106401480120063870204513557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70934320080042580136342371 106401480120063870204513557)
        ·
          refine ⟨4987569380627993915836573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106401480120063870204513557 4987569380627993915836573)
          ·
            refine ⟨1870338517735497718438715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4987569380627993915836573 1870338517735497718438715)
            ·
              refine ⟨2805507776603246577658073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870338517735497718438715 2805507776603246577658073)
              ·
                refine ⟨2104130832452434933243555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805507776603246577658073 2104130832452434933243555)
                ·
                  refine ⟨3156196248678652399865333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104130832452434933243555 3156196248678652399865333)
                  ·
                    refine ⟨295893398313623662487375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3156196248678652399865333 295893398313623662487375)
                    ·
                      rfl

theorem cell23_1728751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_1728751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728751 prefixEnd_1728751 := by exact prefixLift 1728751
  have htrace : WordTrace (prefixWord ++ tailWord_1728751) baseStart_1728751 baseEnd_1728751 := by
    simpa [prefixWord, tailWord_1728751, baseEnd_1728751] using wordTrace_append hprefix tailTrace_1728751
  have hstable : (prefixWord ++ tailWord_1728751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728751).length < 2 ^ (prefixWord ++ tailWord_1728751).sum := by decide
  have hdescent : baseEnd_1728751 < baseStart_1728751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728764 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_1728764 : Nat := 118140960795 + 1728764 * 2 ^ 59
def prefixEnd_1728764 : Nat := 4983230072969 + 3 ^ 40 * 1728764 * 2
def baseEnd_1728764 : Nat := 295895623396459812199855

theorem tailTrace_1728764 : CollatzResearch.WordTrace tailWord_1728764 prefixEnd_1728764 295895623396459812199855 := by
  unfold tailWord_1728764
  simp only [CollatzResearch.WordTrace]
  refine ⟨31526601554495376115152673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42035468739327168153536897 31526601554495376115152673)
  ·
    refine ⟨23644951165871532086364505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31526601554495376115152673 23644951165871532086364505)
    ·
      refine ⟨17733713374403649064773379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23644951165871532086364505 17733713374403649064773379)
      ·
        refine ⟨26600570061605473597160069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17733713374403649064773379 26600570061605473597160069)
        ·
          refine ⟨4987606886551026299467513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26600570061605473597160069 4987606886551026299467513)
          ·
            refine ⟨3740705164913269724600635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987606886551026299467513 3740705164913269724600635)
            ·
              refine ⟨5611057747369904586900953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740705164913269724600635 5611057747369904586900953)
              ·
                refine ⟨4208293310527428440175715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5611057747369904586900953 4208293310527428440175715)
                ·
                  refine ⟨6312439965791142660263573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208293310527428440175715 6312439965791142660263573)
                  ·
                    refine ⟨295895623396459812199855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6312439965791142660263573 295895623396459812199855)
                    ·
                      rfl

theorem cell23_1728764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_1728764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728764 prefixEnd_1728764 := by exact prefixLift 1728764
  have htrace : WordTrace (prefixWord ++ tailWord_1728764) baseStart_1728764 baseEnd_1728764 := by
    simpa [prefixWord, tailWord_1728764, baseEnd_1728764] using wordTrace_append hprefix tailTrace_1728764
  have hstable : (prefixWord ++ tailWord_1728764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728764).length < 2 ^ (prefixWord ++ tailWord_1728764).sum := by decide
  have hdescent : baseEnd_1728764 < baseStart_1728764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728771 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 1, 1, 4]
def baseStart_1728771 : Nat := 118140960795 + 1728771 * 2 ^ 59
def prefixEnd_1728771 : Nat := 4983230072969 + 3 ^ 40 * 1728771 * 2
def baseEnd_1728771 : Nat := 887690464553960909212033

theorem tailTrace_1728771 : CollatzResearch.WordTrace tailWord_1728771 prefixEnd_1728771 887690464553960909212033 := by
  unfold tailWord_1728771
  simp only [CollatzResearch.WordTrace]
  refine ⟨63053458419965392425810167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42035638946643594950540111 63053458419965392425810167)
  ·
    refine ⟨94580187629948088638715251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63053458419965392425810167 94580187629948088638715251)
    ·
      refine ⟨141870281444922132958072877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94580187629948088638715251 141870281444922132958072877)
      ·
        refine ⟨53201355541845799859277329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141870281444922132958072877 53201355541845799859277329)
        ·
          refine ⟨39901016656384349894457997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53201355541845799859277329 39901016656384349894457997)
          ·
            refine ⟨14962881246144131210421749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39901016656384349894457997 14962881246144131210421749)
            ·
              refine ⟨1402770116826012300977039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14962881246144131210421749 1402770116826012300977039)
              ·
                refine ⟨2104155175239018451465559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402770116826012300977039 2104155175239018451465559)
                ·
                  refine ⟨3156232762858527677198339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104155175239018451465559 3156232762858527677198339)
                  ·
                    refine ⟨4734349144287791515797509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156232762858527677198339 4734349144287791515797509)
                    ·
                      refine ⟨887690464553960909212033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4734349144287791515797509 887690464553960909212033)
                      ·
                        rfl

theorem cell23_1728771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_1728771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728771 prefixEnd_1728771 := by exact prefixLift 1728771
  have htrace : WordTrace (prefixWord ++ tailWord_1728771) baseStart_1728771 baseEnd_1728771 := by
    simpa [prefixWord, tailWord_1728771, baseEnd_1728771] using wordTrace_append hprefix tailTrace_1728771
  have hstable : (prefixWord ++ tailWord_1728771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728771).length < 2 ^ (prefixWord ++ tailWord_1728771).sum := by decide
  have hdescent : baseEnd_1728771 < baseStart_1728771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728798 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1728798 : Nat := 118140960795 + 1728798 * 2 ^ 59
def prefixEnd_1728798 : Nat := 4983230072969 + 3 ^ 40 * 1728798 * 2
def baseEnd_1728798 : Nat := 295901442843877434524803

theorem tailTrace_1728798 : CollatzResearch.WordTrace tailWord_1728798 prefixEnd_1728798 295901442843877434524803 := by
  unfold tailWord_1728798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881805398858447004630381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42036295460578384024695365 7881805398858447004630381)
  ·
    refine ⟨2955677024571917626736393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7881805398858447004630381 2955677024571917626736393)
    ·
      refine ⟨2216757768428938220052295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2955677024571917626736393 2216757768428938220052295)
      ·
        refine ⟨3325136652643407330078443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216757768428938220052295 3325136652643407330078443)
        ·
          refine ⟨4987704978965110995117665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325136652643407330078443 4987704978965110995117665)
          ·
            refine ⟨3740778734223833246338249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987704978965110995117665 3740778734223833246338249)
            ·
              refine ⟨2805584050667874934753687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3740778734223833246338249 2805584050667874934753687)
              ·
                refine ⟨4208376076001812402130531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805584050667874934753687 4208376076001812402130531)
                ·
                  refine ⟨6312564114002718603195797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208376076001812402130531 6312564114002718603195797)
                  ·
                    refine ⟨295901442843877434524803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6312564114002718603195797 295901442843877434524803)
                    ·
                      rfl

theorem cell23_1728798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1728798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728798 prefixEnd_1728798 := by exact prefixLift 1728798
  have htrace : WordTrace (prefixWord ++ tailWord_1728798) baseStart_1728798 baseEnd_1728798 := by
    simpa [prefixWord, tailWord_1728798, baseEnd_1728798] using wordTrace_append hprefix tailTrace_1728798
  have hstable : (prefixWord ++ tailWord_1728798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728798).length < 2 ^ (prefixWord ++ tailWord_1728798).sum := by decide
  have hdescent : baseEnd_1728798 < baseStart_1728798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728821 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_1728821 : Nat := 118140960795 + 1728821 * 2 ^ 59
def prefixEnd_1728821 : Nat := 4983230072969 + 3 ^ 40 * 1728821 * 2
def baseEnd_1728821 : Nat := 887716138586685713586803

theorem tailTrace_1728821 : CollatzResearch.WordTrace tailWord_1728821 prefixEnd_1728821 887716138586685713586803 := by
  unfold tailWord_1728821
  simp only [CollatzResearch.WordTrace]
  refine ⟨63055282069784250965130317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42036854713189500643420211 63055282069784250965130317)
  ·
    refine ⟨23645730776169094111923869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63055282069784250965130317 23645730776169094111923869)
    ·
      refine ⟨8867149041063410291971451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23645730776169094111923869 8867149041063410291971451)
      ·
        refine ⟨13300723561595115437957177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8867149041063410291971451 13300723561595115437957177)
        ·
          refine ⟨9975542671196336578467883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13300723561595115437957177 9975542671196336578467883)
          ·
            refine ⟨14963314006794504867701825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9975542671196336578467883 14963314006794504867701825)
            ·
              refine ⟨11222485505095878650776369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14963314006794504867701825 11222485505095878650776369)
              ·
                refine ⟨8416864128821908988082277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11222485505095878650776369 8416864128821908988082277)
                ·
                  refine ⟨1578162024154107935265427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8416864128821908988082277 1578162024154107935265427)
                  ·
                    refine ⟨2367243036231161902898141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1578162024154107935265427 2367243036231161902898141)
                    ·
                      refine ⟨887716138586685713586803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2367243036231161902898141 887716138586685713586803)
                      ·
                        rfl

theorem cell23_1728821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_1728821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728821 prefixEnd_1728821 := by exact prefixLift 1728821
  have htrace : WordTrace (prefixWord ++ tailWord_1728821) baseStart_1728821 baseEnd_1728821 := by
    simpa [prefixWord, tailWord_1728821, baseEnd_1728821] using wordTrace_append hprefix tailTrace_1728821
  have hstable : (prefixWord ++ tailWord_1728821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728821).length < 2 ^ (prefixWord ++ tailWord_1728821).sum := by decide
  have hdescent : baseEnd_1728821 < baseStart_1728821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728825 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1728825 : Nat := 118140960795 + 1728825 * 2 ^ 59
def prefixEnd_1728825 : Nat := 4983230072969 + 3 ^ 40 * 1728825 * 2
def baseEnd_1728825 : Nat := 887718192509303697936785

theorem tailTrace_1728825 : CollatzResearch.WordTrace tailWord_1728825 prefixEnd_1728825 887718192509303697936785 := by
  unfold tailWord_1728825
  simp only [CollatzResearch.WordTrace]
  refine ⟨63055427961769759648275929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42036951974513173098850619 63055427961769759648275929)
  ·
    refine ⟨47291570971327319736206947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63055427961769759648275929 47291570971327319736206947)
    ·
      refine ⟨70937356456990979604310421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47291570971327319736206947 70937356456990979604310421)
      ·
        refine ⟨3325188583921452168952051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70937356456990979604310421 3325188583921452168952051)
        ·
          refine ⟨4987782875882178253428077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325188583921452168952051 4987782875882178253428077)
          ·
            refine ⟨1870418578455816845035529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4987782875882178253428077 1870418578455816845035529)
            ·
              refine ⟨1402813933841862633776647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870418578455816845035529 1402813933841862633776647)
              ·
                refine ⟨2104220900762793950664971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402813933841862633776647 2104220900762793950664971)
                ·
                  refine ⟨3156331351144190925997457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104220900762793950664971 3156331351144190925997457)
                  ·
                    refine ⟨2367248513358143194498093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3156331351144190925997457 2367248513358143194498093)
                    ·
                      refine ⟨887718192509303697936785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2367248513358143194498093 887718192509303697936785)
                      ·
                        rfl

theorem cell23_1728825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1728825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728825 prefixEnd_1728825 := by exact prefixLift 1728825
  have htrace : WordTrace (prefixWord ++ tailWord_1728825) baseStart_1728825 baseEnd_1728825 := by
    simpa [prefixWord, tailWord_1728825, baseEnd_1728825] using wordTrace_append hprefix tailTrace_1728825
  have hstable : (prefixWord ++ tailWord_1728825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728825).length < 2 ^ (prefixWord ++ tailWord_1728825).sum := by decide
  have hdescent : baseEnd_1728825 < baseStart_1728825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728847 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_1728847 : Nat := 118140960795 + 1728847 * 2 ^ 59
def prefixEnd_1728847 : Nat := 4983230072969 + 3 ^ 40 * 1728847 * 2
def baseEnd_1728847 : Nat := 887729489083702611861683

theorem tailTrace_1728847 : CollatzResearch.WordTrace tailWord_1728847 prefixEnd_1728847 887729489083702611861683 := by
  unfold tailWord_1728847
  simp only [CollatzResearch.WordTrace]
  refine ⟨63056230367690057405576795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42037486911793371603717863 63056230367690057405576795)
  ·
    refine ⟨94584345551535086108365193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63056230367690057405576795 94584345551535086108365193)
    ·
      refine ⟨70938259163651314581273895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94584345551535086108365193 70938259163651314581273895)
      ·
        refine ⟨106407388745476971871910843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70938259163651314581273895 106407388745476971871910843)
        ·
          refine ⟨159611083118215457807866265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106407388745476971871910843 159611083118215457807866265)
          ·
            refine ⟨119708312338661593355899699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159611083118215457807866265 119708312338661593355899699)
            ·
              refine ⟨179562468507992390033849549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119708312338661593355899699 179562468507992390033849549)
              ·
                refine ⟨67335925690497146262693581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179562468507992390033849549 67335925690497146262693581)
                ·
                  refine ⟨25250972133936429848510093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67335925690497146262693581 25250972133936429848510093)
                  ·
                    refine ⟨9469114550226161193191285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25250972133936429848510093 9469114550226161193191285)
                    ·
                      refine ⟨887729489083702611861683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9469114550226161193191285 887729489083702611861683)
                      ·
                        rfl

theorem cell23_1728847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_1728847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728847 prefixEnd_1728847 := by exact prefixLift 1728847
  have htrace : WordTrace (prefixWord ++ tailWord_1728847) baseStart_1728847 baseEnd_1728847 := by
    simpa [prefixWord, tailWord_1728847, baseEnd_1728847] using wordTrace_append hprefix tailTrace_1728847
  have hstable : (prefixWord ++ tailWord_1728847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728847).length < 2 ^ (prefixWord ++ tailWord_1728847).sum := by decide
  have hdescent : baseEnd_1728847 < baseStart_1728847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728931 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 2, 5]
def baseStart_1728931 : Nat := 118140960795 + 1728931 * 2 ^ 59
def prefixEnd_1728931 : Nat := 4983230072969 + 3 ^ 40 * 1728931 * 2
def baseEnd_1728931 : Nat := 295924207152893427737099

theorem tailTrace_1728931 : CollatzResearch.WordTrace tailWord_1728931 prefixEnd_1728931 295924207152893427737099 := by
  unfold tailWord_1728931
  simp only [CollatzResearch.WordTrace]
  refine ⟨63059294099385739751634647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42039529399590493167756431 63059294099385739751634647)
  ·
    refine ⟨94588941149078609627451971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63059294099385739751634647 94588941149078609627451971)
    ·
      refine ⟨141883411723617914441177957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94588941149078609627451971 141883411723617914441177957)
      ·
        refine ⟨26603139698178358957720867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141883411723617914441177957 26603139698178358957720867)
        ·
          refine ⟨39904709547267538436581301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26603139698178358957720867 39904709547267538436581301)
          ·
            refine ⟨3741066520056331728429497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39904709547267538436581301 3741066520056331728429497)
            ·
              refine ⟨2805799890042248796322123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3741066520056331728429497 2805799890042248796322123)
              ·
                refine ⟨4208699835063373194483185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805799890042248796322123 4208699835063373194483185)
                ·
                  refine ⟨3156524876297529895862389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208699835063373194483185 3156524876297529895862389)
                  ·
                    refine ⟨295924207152893427737099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3156524876297529895862389 295924207152893427737099)
                    ·
                      rfl

theorem cell23_1728931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 5].length) (baseStart_1728931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728931 prefixEnd_1728931 := by exact prefixLift 1728931
  have htrace : WordTrace (prefixWord ++ tailWord_1728931) baseStart_1728931 baseEnd_1728931 := by
    simpa [prefixWord, tailWord_1728931, baseEnd_1728931] using wordTrace_append hprefix tailTrace_1728931
  have hstable : (prefixWord ++ tailWord_1728931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728931).length < 2 ^ (prefixWord ++ tailWord_1728931).sum := by decide
  have hdescent : baseEnd_1728931 < baseStart_1728931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728951 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_1728951 : Nat := 118140960795 + 1728951 * 2 ^ 59
def prefixEnd_1728951 : Nat := 4983230072969 + 3 ^ 40 * 1728951 * 2
def baseEnd_1728951 : Nat := 887782891071770204961205

theorem tailTrace_1728951 : CollatzResearch.WordTrace tailWord_1728951 prefixEnd_1728951 887782891071770204961205 := by
  unfold tailWord_1728951
  simp only [CollatzResearch.WordTrace]
  refine ⟨63060023559313283167362707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42040015706208855444908471 63060023559313283167362707)
  ·
    refine ⟨94590035338969924751044061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63060023559313283167362707 94590035338969924751044061)
    ·
      refine ⟨35471263252113721781641523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94590035338969924751044061 35471263252113721781641523)
      ·
        refine ⟨53206894878170582672462285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35471263252113721781641523 53206894878170582672462285)
        ·
          refine ⟨19952585579313968502173357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53206894878170582672462285 19952585579313968502173357)
          ·
            refine ⟨7482219592242738188315009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19952585579313968502173357 7482219592242738188315009)
            ·
              refine ⟨5611664694182053641236257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7482219592242738188315009 5611664694182053641236257)
              ·
                refine ⟨4208748520636540230927193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5611664694182053641236257 4208748520636540230927193)
                ·
                  refine ⟨3156561390477405173195395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208748520636540230927193 3156561390477405173195395)
                  ·
                    refine ⟨4734842085716107759793093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156561390477405173195395 4734842085716107759793093)
                    ·
                      refine ⟨887782891071770204961205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4734842085716107759793093 887782891071770204961205)
                      ·
                        rfl

theorem cell23_1728951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_1728951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728951 prefixEnd_1728951 := by exact prefixLift 1728951
  have htrace : WordTrace (prefixWord ++ tailWord_1728951) baseStart_1728951 baseEnd_1728951 := by
    simpa [prefixWord, tailWord_1728951, baseEnd_1728951] using wordTrace_append hprefix tailTrace_1728951
  have hstable : (prefixWord ++ tailWord_1728951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728951).length < 2 ^ (prefixWord ++ tailWord_1728951).sum := by decide
  have hdescent : baseEnd_1728951 < baseStart_1728951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728968 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_1728968 : Nat := 118140960795 + 1728968 * 2 ^ 59
def prefixEnd_1728968 : Nat := 4983230072969 + 3 ^ 40 * 1728968 * 2
def baseEnd_1728968 : Nat := 887791620242896638448627

theorem tailTrace_1728968 : CollatzResearch.WordTrace tailWord_1728968 prefixEnd_1728968 887791620242896638448627 := by
  unfold tailWord_1728968
  simp only [CollatzResearch.WordTrace]
  refine ⟨31530321800125847535365779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42040429066834463380487705 31530321800125847535365779)
  ·
    refine ⟨47295482700188771303048669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31530321800125847535365779 47295482700188771303048669)
    ·
      refine ⟨17735806012570789238643251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47295482700188771303048669 17735806012570789238643251)
      ·
        refine ⟨26603709018856183857964877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17735806012570789238643251 26603709018856183857964877)
        ·
          refine ⟨9976390882071068946736829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26603709018856183857964877 9976390882071068946736829)
          ·
            refine ⟨3741146580776650855026311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9976390882071068946736829 3741146580776650855026311)
            ·
              refine ⟨5611719871164976282539467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741146580776650855026311 5611719871164976282539467)
              ·
                refine ⟨8417579806747464423809201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611719871164976282539467 8417579806747464423809201)
                ·
                  refine ⟨6313184855060598317856901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8417579806747464423809201 6313184855060598317856901)
                  ·
                    refine ⟨1183722160323862184598169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6313184855060598317856901 1183722160323862184598169)
                    ·
                      refine ⟨887791620242896638448627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183722160323862184598169 887791620242896638448627)
                      ·
                        rfl

theorem cell23_1728968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_1728968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728968 prefixEnd_1728968 := by exact prefixLift 1728968
  have htrace : WordTrace (prefixWord ++ tailWord_1728968) baseStart_1728968 baseEnd_1728968 := by
    simpa [prefixWord, tailWord_1728968, baseEnd_1728968] using wordTrace_append hprefix tailTrace_1728968
  have hstable : (prefixWord ++ tailWord_1728968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728968).length < 2 ^ (prefixWord ++ tailWord_1728968).sum := by decide
  have hdescent : baseEnd_1728968 < baseStart_1728968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728974 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_1728974 : Nat := 118140960795 + 1728974 * 2 ^ 59
def prefixEnd_1728974 : Nat := 4983230072969 + 3 ^ 40 * 1728974 * 2
def baseEnd_1728974 : Nat := 98643855680758179441511

theorem tailTrace_1728974 : CollatzResearch.WordTrace tailWord_1728974 prefixEnd_1728974 98643855680758179441511 := by
  unfold tailWord_1728974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882607804778744761931247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42040574958819972063633317 7882607804778744761931247)
  ·
    refine ⟨11823911707168117142896871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7882607804778744761931247 11823911707168117142896871)
    ·
      refine ⟨17735867560752175714345307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823911707168117142896871 17735867560752175714345307)
      ·
        refine ⟨26603801341128263571517961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17735867560752175714345307 26603801341128263571517961)
        ·
          refine ⟨19952851005846197678638471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26603801341128263571517961 19952851005846197678638471)
          ·
            refine ⟨29929276508769296517957707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19952851005846197678638471 29929276508769296517957707)
            ·
              refine ⟨44893914763153944776936561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29929276508769296517957707 44893914763153944776936561)
              ·
                refine ⟨33670436072365458582702421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44893914763153944776936561 33670436072365458582702421)
                ·
                  refine ⟨98643855680758179441511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 33670436072365458582702421 98643855680758179441511)
                  ·
                    rfl

theorem cell23_1728974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_1728974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1728974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1728974 prefixEnd_1728974 := by exact prefixLift 1728974
  have htrace : WordTrace (prefixWord ++ tailWord_1728974) baseStart_1728974 baseEnd_1728974 := by
    simpa [prefixWord, tailWord_1728974, baseEnd_1728974] using wordTrace_append hprefix tailTrace_1728974
  have hstable : (prefixWord ++ tailWord_1728974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728974).length < 2 ^ (prefixWord ++ tailWord_1728974).sum := by decide
  have hdescent : baseEnd_1728974 < baseStart_1728974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729038 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_1729038 : Nat := 118140960795 + 1729038 * 2 ^ 59
def prefixEnd_1729038 : Nat := 4983230072969 + 3 ^ 40 * 1729038 * 2
def baseEnd_1729038 : Nat := 295942521296237121524435

theorem tailTrace_1729038 : CollatzResearch.WordTrace tailWord_1729038 prefixEnd_1729038 295942521296237121524435 := by
  unfold tailWord_1729038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882899588749762128222471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42042131139998731350519845 7882899588749762128222471)
  ·
    refine ⟨11824349383124643192333707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7882899588749762128222471 11824349383124643192333707)
    ·
      refine ⟨17736524074686964788500561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11824349383124643192333707 17736524074686964788500561)
      ·
        refine ⟨13302393056015223591375421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17736524074686964788500561 13302393056015223591375421)
        ·
          refine ⟨4988397396005708846765783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13302393056015223591375421 4988397396005708846765783)
          ·
            refine ⟨7482596094008563270148675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988397396005708846765783 7482596094008563270148675)
            ·
              refine ⟨11223894141012844905223013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7482596094008563270148675 11223894141012844905223013)
              ·
                refine ⟨2104480151439908419729315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11223894141012844905223013 2104480151439908419729315)
                ·
                  refine ⟨3156720227159862629593973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104480151439908419729315 3156720227159862629593973)
                  ·
                    refine ⟨295942521296237121524435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3156720227159862629593973 295942521296237121524435)
                    ·
                      rfl

theorem cell23_1729038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_1729038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729038 prefixEnd_1729038 := by exact prefixLift 1729038
  have htrace : WordTrace (prefixWord ++ tailWord_1729038) baseStart_1729038 baseEnd_1729038 := by
    simpa [prefixWord, tailWord_1729038, baseEnd_1729038] using wordTrace_append hprefix tailTrace_1729038
  have hstable : (prefixWord ++ tailWord_1729038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729038).length < 2 ^ (prefixWord ++ tailWord_1729038).sum := by decide
  have hdescent : baseEnd_1729038 < baseStart_1729038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729052 : List Nat := [2, 2, 3, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_1729052 : Nat := 118140960795 + 1729052 * 2 ^ 59
def prefixEnd_1729052 : Nat := 4983230072969 + 3 ^ 40 * 1729052 * 2
def baseEnd_1729052 : Nat := 887834752617874309798241

theorem tailTrace_1729052 : CollatzResearch.WordTrace tailWord_1729052 prefixEnd_1729052 887834752617874309798241 := by
  unfold tailWord_1729052
  simp only [CollatzResearch.WordTrace]
  refine ⟨31531853665973688708394705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42042471554631584944526273 31531853665973688708394705)
  ·
    refine ⟨23648890249480266531296029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31531853665973688708394705 23648890249480266531296029)
    ·
      refine ⟨8868333843555099949236011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23648890249480266531296029 8868333843555099949236011)
      ·
        refine ⟨13302500765332649923854017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8868333843555099949236011 13302500765332649923854017)
        ·
          refine ⟨9976875573999487442890513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13302500765332649923854017 9976875573999487442890513)
          ·
            refine ⟨7482656680499615582167885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9976875573999487442890513 7482656680499615582167885)
            ·
              refine ⟨2805996255187355843312957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7482656680499615582167885 2805996255187355843312957)
              ·
                refine ⟨1052248595695258441242359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2805996255187355843312957 1052248595695258441242359)
                ·
                  refine ⟨1578372893542887661863539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052248595695258441242359 1578372893542887661863539)
                  ·
                    refine ⟨2367559340314331492795309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1578372893542887661863539 2367559340314331492795309)
                    ·
                      refine ⟨887834752617874309798241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2367559340314331492795309 887834752617874309798241)
                      ·
                        rfl

theorem cell23_1729052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_1729052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729052 prefixEnd_1729052 := by exact prefixLift 1729052
  have htrace : WordTrace (prefixWord ++ tailWord_1729052) baseStart_1729052 baseEnd_1729052 := by
    simpa [prefixWord, tailWord_1729052, baseEnd_1729052] using wordTrace_append hprefix tailTrace_1729052
  have hstable : (prefixWord ++ tailWord_1729052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729052).length < 2 ^ (prefixWord ++ tailWord_1729052).sum := by decide
  have hdescent : baseEnd_1729052 < baseStart_1729052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729061 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_1729061 : Nat := 118140960795 + 1729061 * 2 ^ 59
def prefixEnd_1729061 : Nat := 4983230072969 + 3 ^ 40 * 1729061 * 2
def baseEnd_1729061 : Nat := 887839373943764774585699

theorem tailTrace_1729061 : CollatzResearch.WordTrace tailWord_1729061 prefixEnd_1729061 887839373943764774585699 := by
  unfold tailWord_1729061
  simp only [CollatzResearch.WordTrace]
  refine ⟨63064035588914771953867037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42042690392609847969244691 63064035588914771953867037)
  ·
    refine ⟨23649013345843039482700139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63064035588914771953867037 23649013345843039482700139)
    ·
      refine ⟨35473520018764559224050209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23649013345843039482700139 35473520018764559224050209)
      ·
        refine ⟨26605140014073419418037657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35473520018764559224050209 26605140014073419418037657)
        ·
          refine ⟨19953855010555064563528243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26605140014073419418037657 19953855010555064563528243)
          ·
            refine ⟨29930782515832596845292365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19953855010555064563528243 29930782515832596845292365)
            ·
              refine ⟨11224043443437223816984637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29930782515832596845292365 11224043443437223816984637)
              ·
                refine ⟨4209016291288958931369239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11224043443437223816984637 4209016291288958931369239)
                ·
                  refine ⟨6313524436933438397053859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209016291288958931369239 6313524436933438397053859)
                  ·
                    refine ⟨9470286655400157595580789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313524436933438397053859 9470286655400157595580789)
                    ·
                      refine ⟨887839373943764774585699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9470286655400157595580789 887839373943764774585699)
                      ·
                        rfl

theorem cell23_1729061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_1729061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729061 prefixEnd_1729061 := by exact prefixLift 1729061
  have htrace : WordTrace (prefixWord ++ tailWord_1729061) baseStart_1729061 baseEnd_1729061 := by
    simpa [prefixWord, tailWord_1729061, baseEnd_1729061] using wordTrace_append hprefix tailTrace_1729061
  have hstable : (prefixWord ++ tailWord_1729061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729061).length < 2 ^ (prefixWord ++ tailWord_1729061).sum := by decide
  have hdescent : baseEnd_1729061 < baseStart_1729061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729081 : List Nat := [1, 2, 1, 5, 1, 1, 4, 8]
def baseStart_1729081 : Nat := 118140960795 + 1729081 * 2 ^ 59
def prefixEnd_1729081 : Nat := 4983230072969 + 3 ^ 40 * 1729081 * 2
def baseEnd_1729081 : Nat := 32883320131735359123541

theorem tailTrace_1729081 : CollatzResearch.WordTrace tailWord_1729081 prefixEnd_1729081 32883320131735359123541 := by
  unfold tailWord_1729081
  simp only [CollatzResearch.WordTrace]
  refine ⟨63064765048842315369595097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42043176699228210246396731 63064765048842315369595097)
  ·
    refine ⟨47298573786631736527196323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63064765048842315369595097 47298573786631736527196323)
    ·
      refine ⟨70947860679947604790794485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47298573786631736527196323 70947860679947604790794485)
      ·
        refine ⟨6651361938745087949136983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70947860679947604790794485 6651361938745087949136983)
        ·
          refine ⟨9977042908117631923705475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6651361938745087949136983 9977042908117631923705475)
          ·
            refine ⟨14965564362176447885558213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9977042908117631923705475 14965564362176447885558213)
            ·
              refine ⟨2806043317908083978542165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14965564362176447885558213 2806043317908083978542165)
              ·
                refine ⟨32883320131735359123541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2806043317908083978542165 32883320131735359123541)
                ·
                  rfl

theorem cell23_1729081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 8].length) (baseStart_1729081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729081 prefixEnd_1729081 := by exact prefixLift 1729081
  have htrace : WordTrace (prefixWord ++ tailWord_1729081) baseStart_1729081 baseEnd_1729081 := by
    simpa [prefixWord, tailWord_1729081, baseEnd_1729081] using wordTrace_append hprefix tailTrace_1729081
  have hstable : (prefixWord ++ tailWord_1729081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729081).length < 2 ^ (prefixWord ++ tailWord_1729081).sum := by decide
  have hdescent : baseEnd_1729081 < baseStart_1729081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729085 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_1729085 : Nat := 118140960795 + 1729085 * 2 ^ 59
def prefixEnd_1729085 : Nat := 4983230072969 + 3 ^ 40 * 1729085 * 2
def baseEnd_1729085 : Nat := 295950565826490893561863

theorem tailTrace_1729085 : CollatzResearch.WordTrace tailWord_1729085 prefixEnd_1729085 295950565826490893561863 := by
  unfold tailWord_1729085
  simp only [CollatzResearch.WordTrace]
  refine ⟨63064910940827824052740709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42043273960551882701827139 63064910940827824052740709)
  ·
    refine ⟨11824670801405217009888883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63064910940827824052740709 11824670801405217009888883)
    ·
      refine ⟨17737006202107825514833325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11824670801405217009888883 17737006202107825514833325)
      ·
        refine ⟨6651377325790434568062497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17737006202107825514833325 6651377325790434568062497)
        ·
          refine ⟨4988532994342825926046873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6651377325790434568062497 4988532994342825926046873)
          ·
            refine ⟨3741399745757119444535155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4988532994342825926046873 3741399745757119444535155)
            ·
              refine ⟨5612099618635679166802733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741399745757119444535155 5612099618635679166802733)
              ·
                refine ⟨2104537356988379687551025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5612099618635679166802733 2104537356988379687551025)
                ·
                  refine ⟨1578403017741284765663269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2104537356988379687551025 1578403017741284765663269)
                  ·
                    refine ⟨295950565826490893561863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1578403017741284765663269 295950565826490893561863)
                    ·
                      rfl

theorem cell23_1729085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_1729085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729085 prefixEnd_1729085 := by exact prefixLift 1729085
  have htrace : WordTrace (prefixWord ++ tailWord_1729085) baseStart_1729085 baseEnd_1729085 := by
    simpa [prefixWord, tailWord_1729085, baseEnd_1729085] using wordTrace_append hprefix tailTrace_1729085
  have hstable : (prefixWord ++ tailWord_1729085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729085).length < 2 ^ (prefixWord ++ tailWord_1729085).sum := by decide
  have hdescent : baseEnd_1729085 < baseStart_1729085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729091 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1729091 : Nat := 118140960795 + 1729091 * 2 ^ 59
def prefixEnd_1729091 : Nat := 4983230072969 + 3 ^ 40 * 1729091 * 2
def baseEnd_1729091 : Nat := 887854778363399657210561

theorem tailTrace_1729091 : CollatzResearch.WordTrace tailWord_1729091 prefixEnd_1729091 887854778363399657210561 := by
  unfold tailWord_1729091
  simp only [CollatzResearch.WordTrace]
  refine ⟨63065129778806087077459127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42043419852537391384972751 63065129778806087077459127)
  ·
    refine ⟨94597694668209130616188691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63065129778806087077459127 94597694668209130616188691)
    ·
      refine ⟨141896542002313695924283037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94597694668209130616188691 141896542002313695924283037)
      ·
        refine ⟨53211203250867635971606139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141896542002313695924283037 53211203250867635971606139)
        ·
          refine ⟨79816804876301453957409209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53211203250867635971606139 79816804876301453957409209)
          ·
            refine ⟨59862603657226090468056907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79816804876301453957409209 59862603657226090468056907)
            ·
              refine ⟨89793905485839135702085361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59862603657226090468056907 89793905485839135702085361)
              ·
                refine ⟨67345429114379351776564021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89793905485839135702085361 67345429114379351776564021)
                ·
                  refine ⟨6313633979473064229052877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67345429114379351776564021 6313633979473064229052877)
                  ·
                    refine ⟨2367612742302399085894829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6313633979473064229052877 2367612742302399085894829)
                    ·
                      refine ⟨887854778363399657210561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2367612742302399085894829 887854778363399657210561)
                      ·
                        rfl

theorem cell23_1729091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1729091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729091 prefixEnd_1729091 := by exact prefixLift 1729091
  have htrace : WordTrace (prefixWord ++ tailWord_1729091) baseStart_1729091 baseEnd_1729091 := by
    simpa [prefixWord, tailWord_1729091, baseEnd_1729091] using wordTrace_append hprefix tailTrace_1729091
  have hstable : (prefixWord ++ tailWord_1729091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729091).length < 2 ^ (prefixWord ++ tailWord_1729091).sum := by decide
  have hdescent : baseEnd_1729091 < baseStart_1729091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729095 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_1729095 : Nat := 118140960795 + 1729095 * 2 ^ 59
def prefixEnd_1729095 : Nat := 4983230072969 + 3 ^ 40 * 1729095 * 2
def baseEnd_1729095 : Nat := 887856832286017641560543

theorem tailTrace_1729095 : CollatzResearch.WordTrace tailWord_1729095 prefixEnd_1729095 887856832286017641560543 := by
  unfold tailWord_1729095
  simp only [CollatzResearch.WordTrace]
  refine ⟨63065275670791595760604739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42043517113861063840403159 63065275670791595760604739)
  ·
    refine ⟨94597913506187393640907109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63065275670791595760604739 94597913506187393640907109)
    ·
      refine ⟨17737108782410136307670083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94597913506187393640907109 17737108782410136307670083)
      ·
        refine ⟨26605663173615204461505125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17737108782410136307670083 26605663173615204461505125)
        ·
          refine ⟨4988561845052850836532211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26605663173615204461505125 4988561845052850836532211)
          ·
            refine ⟨7482842767579276254798317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988561845052850836532211 7482842767579276254798317)
            ·
              refine ⟨2806066037842228595549369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7482842767579276254798317 2806066037842228595549369)
              ·
                refine ⟨2104549528381671446662027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806066037842228595549369 2104549528381671446662027)
                ·
                  refine ⟨3156824292572507169993041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104549528381671446662027 3156824292572507169993041)
                  ·
                    refine ⟨2367618219429380377494781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3156824292572507169993041 2367618219429380377494781)
                    ·
                      refine ⟨887856832286017641560543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2367618219429380377494781 887856832286017641560543)
                      ·
                        rfl

theorem cell23_1729095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_1729095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729095 prefixEnd_1729095 := by exact prefixLift 1729095
  have htrace : WordTrace (prefixWord ++ tailWord_1729095) baseStart_1729095 baseEnd_1729095 := by
    simpa [prefixWord, tailWord_1729095, baseEnd_1729095] using wordTrace_append hprefix tailTrace_1729095
  have hstable : (prefixWord ++ tailWord_1729095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729095).length < 2 ^ (prefixWord ++ tailWord_1729095).sum := by decide
  have hdescent : baseEnd_1729095 < baseStart_1729095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729108 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1729108 : Nat := 118140960795 + 1729108 * 2 ^ 59
def prefixEnd_1729108 : Nat := 4983230072969 + 3 ^ 40 * 1729108 * 2
def baseEnd_1729108 : Nat := 887863507534526090697983

theorem tailTrace_1729108 : CollatzResearch.WordTrace tailWord_1729108 prefixEnd_1729108 887863507534526090697983 := by
  unfold tailWord_1729108
  simp only [CollatzResearch.WordTrace]
  refine ⟨31532874909872249490413989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42043833213162999320551985 31532874909872249490413989)
  ·
    refine ⟨5912414045601046779452623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31532874909872249490413989 5912414045601046779452623)
    ·
      refine ⟨8868621068401570169178935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5912414045601046779452623 8868621068401570169178935)
      ·
        refine ⟨13302931602602355253768403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8868621068401570169178935 13302931602602355253768403)
        ·
          refine ⟨19954397403903532880652605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13302931602602355253768403 19954397403903532880652605)
          ·
            refine ⟨7482899026463824830244727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19954397403903532880652605 7482899026463824830244727)
            ·
              refine ⟨11224348539695737245367091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7482899026463824830244727 11224348539695737245367091)
              ·
                refine ⟨16836522809543605868050637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11224348539695737245367091 16836522809543605868050637)
                ·
                  refine ⟨6313696053578852200518989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16836522809543605868050637 6313696053578852200518989)
                  ·
                    refine ⟨2367636020092069575194621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6313696053578852200518989 2367636020092069575194621)
                    ·
                      refine ⟨887863507534526090697983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2367636020092069575194621 887863507534526090697983)
                      ·
                        rfl

theorem cell23_1729108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1729108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729108 prefixEnd_1729108 := by exact prefixLift 1729108
  have htrace : WordTrace (prefixWord ++ tailWord_1729108) baseStart_1729108 baseEnd_1729108 := by
    simpa [prefixWord, tailWord_1729108, baseEnd_1729108] using wordTrace_append hprefix tailTrace_1729108
  have hstable : (prefixWord ++ tailWord_1729108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729108).length < 2 ^ (prefixWord ++ tailWord_1729108).sum := by decide
  have hdescent : baseEnd_1729108 < baseStart_1729108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729142 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1729142 : Nat := 118140960795 + 1729142 * 2 ^ 59
def prefixEnd_1729142 : Nat := 4983230072969 + 3 ^ 40 * 1729142 * 2
def baseEnd_1729142 : Nat := 887880965876778957672827

theorem tailTrace_1729142 : CollatzResearch.WordTrace tailWord_1729142 prefixEnd_1729142 887880965876778957672827 := by
  unfold tailWord_1729142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941686868851332674222855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42044659934414215191710453 3941686868851332674222855)
  ·
    refine ⟨5912530303276999011334283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3941686868851332674222855 5912530303276999011334283)
    ·
      refine ⟨8868795454915498517001425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5912530303276999011334283 8868795454915498517001425)
      ·
        refine ⟨6651596591186623887751069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8868795454915498517001425 6651596591186623887751069)
        ·
          refine ⟨2494348721694983957906651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6651596591186623887751069 2494348721694983957906651)
          ·
            refine ⟨3741523082542475936859977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494348721694983957906651 3741523082542475936859977)
            ·
              refine ⟨2806142311906856952644983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3741523082542475936859977 2806142311906856952644983)
              ·
                refine ⟨4209213467860285428967475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806142311906856952644983 4209213467860285428967475)
                ·
                  refine ⟨6313820201790428143451213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209213467860285428967475 6313820201790428143451213)
                  ·
                    refine ⟨2367682575671410553794205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6313820201790428143451213 2367682575671410553794205)
                    ·
                      refine ⟨887880965876778957672827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2367682575671410553794205 887880965876778957672827)
                      ·
                        rfl

theorem cell23_1729142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1729142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729142 prefixEnd_1729142 := by exact prefixLift 1729142
  have htrace : WordTrace (prefixWord ++ tailWord_1729142) baseStart_1729142 baseEnd_1729142 := by
    simpa [prefixWord, tailWord_1729142, baseEnd_1729142] using wordTrace_append hprefix tailTrace_1729142
  have hstable : (prefixWord ++ tailWord_1729142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729142).length < 2 ^ (prefixWord ++ tailWord_1729142).sum := by decide
  have hdescent : baseEnd_1729142 < baseStart_1729142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729151 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1729151 : Nat := 118140960795 + 1729151 * 2 ^ 59
def prefixEnd_1729151 : Nat := 4983230072969 + 3 ^ 40 * 1729151 * 2
def baseEnd_1729151 : Nat := 887885587202669422460285

theorem tailTrace_1729151 : CollatzResearch.WordTrace tailWord_1729151 prefixEnd_1729151 887885587202669422460285 := by
  unfold tailWord_1729151
  simp only [CollatzResearch.WordTrace]
  refine ⟨63067318158588717324643307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42044878772392478216428871 63067318158588717324643307)
  ·
    refine ⟨94600977237883075986964961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63067318158588717324643307 94600977237883075986964961)
    ·
      refine ⟨70950732928412306990223721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94600977237883075986964961 70950732928412306990223721)
      ·
        refine ⟨53213049696309230242667791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70950732928412306990223721 53213049696309230242667791)
        ·
          refine ⟨79819574544463845364001687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53213049696309230242667791 79819574544463845364001687)
          ·
            refine ⟨119729361816695768046002531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79819574544463845364001687 119729361816695768046002531)
            ·
              refine ⟨179594042725043652069003797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119729361816695768046002531 179594042725043652069003797)
              ·
                refine ⟨8418470752736421190734553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179594042725043652069003797 8418470752736421190734553)
                ·
                  refine ⟨6313853064552315893050915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8418470752736421190734553 6313853064552315893050915)
                  ·
                    refine ⟨9470779596828473839576373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6313853064552315893050915 9470779596828473839576373)
                    ·
                      refine ⟨887885587202669422460285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9470779596828473839576373 887885587202669422460285)
                      ·
                        rfl

theorem cell23_1729151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1729151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729151 prefixEnd_1729151 := by exact prefixLift 1729151
  have htrace : WordTrace (prefixWord ++ tailWord_1729151) baseStart_1729151 baseEnd_1729151 := by
    simpa [prefixWord, tailWord_1729151, baseEnd_1729151] using wordTrace_append hprefix tailTrace_1729151
  have hstable : (prefixWord ++ tailWord_1729151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729151).length < 2 ^ (prefixWord ++ tailWord_1729151).sum := by decide
  have hdescent : baseEnd_1729151 < baseStart_1729151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729161 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_1729161 : Nat := 118140960795 + 1729161 * 2 ^ 59
def prefixEnd_1729161 : Nat := 4983230072969 + 3 ^ 40 * 1729161 * 2
def baseEnd_1729161 : Nat := 887890722009214383335239

theorem tailTrace_1729161 : CollatzResearch.WordTrace tailWord_1729161 prefixEnd_1729161 887890722009214383335239 := by
  unfold tailWord_1729161
  simp only [CollatzResearch.WordTrace]
  refine ⟨63067682888552489032507337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42045121925701659355004891 63067682888552489032507337)
  ·
    refine ⟨47300762166414366774380503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63067682888552489032507337 47300762166414366774380503)
    ·
      refine ⟨70951143249621550161570755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47300762166414366774380503 70951143249621550161570755)
      ·
        refine ⟨106426714874432325242356133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70951143249621550161570755 106426714874432325242356133)
        ·
          refine ⟨19955009038956060982941775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106426714874432325242356133 19955009038956060982941775)
          ·
            refine ⟨29932513558434091474412663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19955009038956060982941775 29932513558434091474412663)
            ·
              refine ⟨44898770337651137211618995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29932513558434091474412663 44898770337651137211618995)
              ·
                refine ⟨67348155506476705817428493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44898770337651137211618995 67348155506476705817428493)
                ·
                  refine ⟨25255558314928764681535685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67348155506476705817428493 25255558314928764681535685)
                  ·
                    refine ⟨4735417184049143377787941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25255558314928764681535685 4735417184049143377787941)
                    ·
                      refine ⟨887890722009214383335239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4735417184049143377787941 887890722009214383335239)
                      ·
                        rfl

theorem cell23_1729161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_1729161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729161 prefixEnd_1729161 := by exact prefixLift 1729161
  have htrace : WordTrace (prefixWord ++ tailWord_1729161) baseStart_1729161 baseEnd_1729161 := by
    simpa [prefixWord, tailWord_1729161, baseEnd_1729161] using wordTrace_append hprefix tailTrace_1729161
  have hstable : (prefixWord ++ tailWord_1729161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729161).length < 2 ^ (prefixWord ++ tailWord_1729161).sum := by decide
  have hdescent : baseEnd_1729161 < baseStart_1729161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729188 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 7]
def baseStart_1729188 : Nat := 118140960795 + 1729188 * 2 ^ 59
def prefixEnd_1729188 : Nat := 4983230072969 + 3 ^ 40 * 1729188 * 2
def baseEnd_1729188 : Nat := 98656065109653975299735

theorem tailTrace_1729188 : CollatzResearch.WordTrace tailWord_1729188 prefixEnd_1729188 98656065109653975299735 := by
  unfold tailWord_1729188
  simp only [CollatzResearch.WordTrace]
  refine ⟨31534333829727336321870109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42045778439636448429160145 31534333829727336321870109)
  ·
    refine ⟨11825375186147751120701291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31534333829727336321870109 11825375186147751120701291)
    ·
      refine ⟨17738062779221626681051937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11825375186147751120701291 17738062779221626681051937)
      ·
        refine ⟨13303547084416220010788953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17738062779221626681051937 13303547084416220010788953)
        ·
          refine ⟨9977660313312165008091715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13303547084416220010788953 9977660313312165008091715)
          ·
            refine ⟨14966490469968247512137573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9977660313312165008091715 14966490469968247512137573)
            ·
              refine ⟨2806216963119046408525795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14966490469968247512137573 2806216963119046408525795)
              ·
                refine ⟨4209325444678569612788693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806216963119046408525795 4209325444678569612788693)
                ·
                  refine ⟨98656065109653975299735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4209325444678569612788693 98656065109653975299735)
                  ·
                    rfl

theorem cell23_1729188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_1729188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729188 prefixEnd_1729188 := by exact prefixLift 1729188
  have htrace : WordTrace (prefixWord ++ tailWord_1729188) baseStart_1729188 baseEnd_1729188 := by
    simpa [prefixWord, tailWord_1729188, baseEnd_1729188] using wordTrace_append hprefix tailTrace_1729188
  have hstable : (prefixWord ++ tailWord_1729188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729188).length < 2 ^ (prefixWord ++ tailWord_1729188).sum := by decide
  have hdescent : baseEnd_1729188 < baseStart_1729188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729199 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 2, 2, 2]
def baseStart_1729199 : Nat := 118140960795 + 1729199 * 2 ^ 59
def prefixEnd_1729199 : Nat := 4983230072969 + 3 ^ 40 * 1729199 * 2
def baseEnd_1729199 : Nat := 887910234274085234660065

theorem tailTrace_1729199 : CollatzResearch.WordTrace tailWord_1729199 prefixEnd_1729199 887910234274085234660065 := by
  unfold tailWord_1729199
  simp only [CollatzResearch.WordTrace]
  refine ⟨63069068862414821522390651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42046045908276547681593767 63069068862414821522390651)
  ·
    refine ⟨94603603293622232283585977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63069068862414821522390651 94603603293622232283585977)
    ·
      refine ⟨70952702470216674212689483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94603603293622232283585977 70952702470216674212689483)
      ·
        refine ⟨106429053705325011319034225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70952702470216674212689483 106429053705325011319034225)
        ·
          refine ⟨79821790278993758489275669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106429053705325011319034225 79821790278993758489275669)
          ·
            refine ⟨3741646419327832429184797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79821790278993758489275669 3741646419327832429184797)
            ·
              refine ⟨1403117407247937160944299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3741646419327832429184797 1403117407247937160944299)
              ·
                refine ⟨2104676110871905741416449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403117407247937160944299 2104676110871905741416449)
                ·
                  refine ⟨1578507083153929306062337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2104676110871905741416449 1578507083153929306062337)
                  ·
                    refine ⟨1183880312365446979546753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1578507083153929306062337 1183880312365446979546753)
                    ·
                      refine ⟨887910234274085234660065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183880312365446979546753 887910234274085234660065)
                      ·
                        rfl

theorem cell23_1729199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 2, 2].length) (baseStart_1729199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729199 prefixEnd_1729199 := by exact prefixLift 1729199
  have htrace : WordTrace (prefixWord ++ tailWord_1729199) baseStart_1729199 baseEnd_1729199 := by
    simpa [prefixWord, tailWord_1729199, baseEnd_1729199] using wordTrace_append hprefix tailTrace_1729199
  have hstable : (prefixWord ++ tailWord_1729199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729199).length < 2 ^ (prefixWord ++ tailWord_1729199).sum := by decide
  have hdescent : baseEnd_1729199 < baseStart_1729199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729211 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5]
def baseStart_1729211 : Nat := 118140960795 + 1729211 * 2 ^ 59
def prefixEnd_1729211 : Nat := 4983230072969 + 3 ^ 40 * 1729211 * 2
def baseEnd_1729211 : Nat := 887916396041939187710009

theorem tailTrace_1729211 : CollatzResearch.WordTrace tailWord_1729211 prefixEnd_1729211 887916396041939187710009 := by
  unfold tailWord_1729211
  simp only [CollatzResearch.WordTrace]
  refine ⟨63069506538371347571827487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42046337692247565047884991 63069506538371347571827487)
  ·
    refine ⟨94604259807557021357741231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63069506538371347571827487 94604259807557021357741231)
    ·
      refine ⟨141906389711335532036611847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94604259807557021357741231 141906389711335532036611847)
      ·
        refine ⟨212859584567003298054917771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141906389711335532036611847 212859584567003298054917771)
        ·
          refine ⟨319289376850504947082376657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212859584567003298054917771 319289376850504947082376657)
          ·
            refine ⟨239467032637878710311782493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319289376850504947082376657 239467032637878710311782493)
            ·
              refine ⟨89800137239204516366918435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239467032637878710311782493 89800137239204516366918435)
              ·
                refine ⟨134700205858806774550377653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89800137239204516366918435 134700205858806774550377653)
                ·
                  refine ⟨12628144299263135114097905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134700205858806774550377653 12628144299263135114097905)
                  ·
                    refine ⟨9471108224447351335573429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12628144299263135114097905 9471108224447351335573429)
                    ·
                      refine ⟨887916396041939187710009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9471108224447351335573429 887916396041939187710009)
                      ·
                        rfl

theorem cell23_1729211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_1729211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729211 prefixEnd_1729211 := by exact prefixLift 1729211
  have htrace : WordTrace (prefixWord ++ tailWord_1729211) baseStart_1729211 baseEnd_1729211 := by
    simpa [prefixWord, tailWord_1729211, baseEnd_1729211] using wordTrace_append hprefix tailTrace_1729211
  have hstable : (prefixWord ++ tailWord_1729211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729211).length < 2 ^ (prefixWord ++ tailWord_1729211).sum := by decide
  have hdescent : baseEnd_1729211 < baseStart_1729211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729315 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 1, 5, 2]
def baseStart_1729315 : Nat := 118140960795 + 1729315 * 2 ^ 59
def prefixEnd_1729315 : Nat := 4983230072969 + 3 ^ 40 * 1729315 * 2
def baseEnd_1729315 : Nat := 887969798030006780809531

theorem tailTrace_1729315 : CollatzResearch.WordTrace tailWord_1729315 prefixEnd_1729315 887969798030006780809531 := by
  unfold tailWord_1729315
  simp only [CollatzResearch.WordTrace]
  refine ⟨63073299729994573333613399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42048866486663048889075599 63073299729994573333613399)
  ·
    refine ⟨94609949594991860000420099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63073299729994573333613399 94609949594991860000420099)
    ·
      refine ⟨141914924392487790000630149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94609949594991860000420099 141914924392487790000630149)
      ·
        refine ⟨26609048323591460625118153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141914924392487790000630149 26609048323591460625118153)
        ·
          refine ⟨19956786242693595468838615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26609048323591460625118153 19956786242693595468838615)
          ·
            refine ⟨29935179364040393203257923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19956786242693595468838615 29935179364040393203257923)
            ·
              refine ⟨44902769046060589804886885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29935179364040393203257923 44902769046060589804886885)
              ·
                refine ⟨8419269196136360588416291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44902769046060589804886885 8419269196136360588416291)
                ·
                  refine ⟨12628903794204540882624437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8419269196136360588416291 12628903794204540882624437)
                  ·
                    refine ⟨1183959730706675707746041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12628903794204540882624437 1183959730706675707746041)
                    ·
                      refine ⟨887969798030006780809531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1183959730706675707746041 887969798030006780809531)
                      ·
                        rfl

theorem cell23_1729315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_1729315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729315 prefixEnd_1729315 := by exact prefixLift 1729315
  have htrace : WordTrace (prefixWord ++ tailWord_1729315) baseStart_1729315 baseEnd_1729315 := by
    simpa [prefixWord, tailWord_1729315, baseEnd_1729315] using wordTrace_append hprefix tailTrace_1729315
  have hstable : (prefixWord ++ tailWord_1729315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729315).length < 2 ^ (prefixWord ++ tailWord_1729315).sum := by decide
  have hdescent : baseEnd_1729315 < baseStart_1729315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729365 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1729365 : Nat := 118140960795 + 1729365 * 2 ^ 59
def prefixEnd_1729365 : Nat := 4983230072969 + 3 ^ 40 * 1729365 * 2
def baseEnd_1729365 : Nat := 887995472062731585184301

theorem tailTrace_1729365 : CollatzResearch.WordTrace tailWord_1729365 prefixEnd_1729365 887995472062731585184301 := by
  unfold tailWord_1729365
  simp only [CollatzResearch.WordTrace]
  refine ⟨63075123379813431872933549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42050082253208954581955699 63075123379813431872933549)
  ·
    refine ⟨23653171267430036952350081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63075123379813431872933549 23653171267430036952350081)
    ·
      refine ⟨17739878450572527714262561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23653171267430036952350081 17739878450572527714262561)
      ·
        refine ⟨13304908837929395785696921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17739878450572527714262561 13304908837929395785696921)
        ·
          refine ⟨9978681628447046839272691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13304908837929395785696921 9978681628447046839272691)
          ·
            refine ⟨14968022442670570258909037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9978681628447046839272691 14968022442670570258909037)
            ·
              refine ⟨5613008416001463847090889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14968022442670570258909037 5613008416001463847090889)
              ·
                refine ⟨4209756312001097885318167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5613008416001463847090889 4209756312001097885318167)
                ·
                  refine ⟨6314634468001646827977251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209756312001097885318167 6314634468001646827977251)
                  ·
                    refine ⟨9471951702002470241965877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6314634468001646827977251 9471951702002470241965877)
                    ·
                      refine ⟨887995472062731585184301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9471951702002470241965877 887995472062731585184301)
                      ·
                        rfl

theorem cell23_1729365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1729365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729365 prefixEnd_1729365 := by exact prefixLift 1729365
  have htrace : WordTrace (prefixWord ++ tailWord_1729365) baseStart_1729365 baseEnd_1729365 := by
    simpa [prefixWord, tailWord_1729365, baseEnd_1729365] using wordTrace_append hprefix tailTrace_1729365
  have hstable : (prefixWord ++ tailWord_1729365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729365).length < 2 ^ (prefixWord ++ tailWord_1729365).sum := by decide
  have hdescent : baseEnd_1729365 < baseStart_1729365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729372 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1729372 : Nat := 118140960795 + 1729372 * 2 ^ 59
def prefixEnd_1729372 : Nat := 4983230072969 + 3 ^ 40 * 1729372 * 2
def baseEnd_1729372 : Nat := 295999688809104352598923

theorem tailTrace_1729372 : CollatzResearch.WordTrace tailWord_1729372 prefixEnd_1729372 295999688809104352598923 := by
  unfold tailWord_1729372
  simp only [CollatzResearch.WordTrace]
  refine ⟨31537689345394036034219185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42050252460525381378958913 31537689345394036034219185)
  ·
    refine ⟨23653267009045527025664389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31537689345394036034219185 23653267009045527025664389)
    ·
      refine ⟨4434987564196036317312073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23653267009045527025664389 4434987564196036317312073)
      ·
        refine ⟨3326240673147027237984055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4434987564196036317312073 3326240673147027237984055)
        ·
          refine ⟨4989361009720540856976083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326240673147027237984055 4989361009720540856976083)
          ·
            refine ⟨7484041514580811285464125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989361009720540856976083 7484041514580811285464125)
            ·
              refine ⟨2806515567967804232049047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7484041514580811285464125 2806515567967804232049047)
              ·
                refine ⟨4209773351951706348073571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806515567967804232049047 4209773351951706348073571)
                ·
                  refine ⟨6314660027927559522110357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209773351951706348073571 6314660027927559522110357)
                  ·
                    refine ⟨295999688809104352598923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6314660027927559522110357 295999688809104352598923)
                    ·
                      rfl

theorem cell23_1729372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1729372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729372 prefixEnd_1729372 := by exact prefixLift 1729372
  have htrace : WordTrace (prefixWord ++ tailWord_1729372) baseStart_1729372 baseEnd_1729372 := by
    simpa [prefixWord, tailWord_1729372, baseEnd_1729372] using wordTrace_append hprefix tailTrace_1729372
  have hstable : (prefixWord ++ tailWord_1729372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729372).length < 2 ^ (prefixWord ++ tailWord_1729372).sum := by decide
  have hdescent : baseEnd_1729372 < baseStart_1729372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729379 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 3, 2, 2]
def baseStart_1729379 : Nat := 118140960795 + 1729379 * 2 ^ 59
def prefixEnd_1729379 : Nat := 4983230072969 + 3 ^ 40 * 1729379 * 2
def baseEnd_1729379 : Nat := 888002660791894530409237

theorem tailTrace_1729379 : CollatzResearch.WordTrace tailWord_1729379 prefixEnd_1729379 888002660791894530409237 := by
  unfold tailWord_1729379
  simp only [CollatzResearch.WordTrace]
  refine ⟨63075634001762712263943191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42050422667841808175962127 63075634001762712263943191)
  ·
    refine ⟨94613451002644068395914787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63075634001762712263943191 94613451002644068395914787)
    ·
      refine ⟨141920176503966102593872181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94613451002644068395914787 141920176503966102593872181)
      ·
        refine ⟨13305016547246822118175517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141920176503966102593872181 13305016547246822118175517)
        ·
          refine ⟨4989381205217558294315819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13305016547246822118175517 4989381205217558294315819)
          ·
            refine ⟨7484071807826337441473729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989381205217558294315819 7484071807826337441473729)
            ·
              refine ⟨5613053855869753081105297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7484071807826337441473729 5613053855869753081105297)
              ·
                refine ⟨4209790391902314810828973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5613053855869753081105297 4209790391902314810828973)
                ·
                  refine ⟨1578671396963368054060865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4209790391902314810828973 1578671396963368054060865)
                  ·
                    refine ⟨1184003547722526040545649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1578671396963368054060865 1184003547722526040545649)
                    ·
                      refine ⟨888002660791894530409237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184003547722526040545649 888002660791894530409237)
                      ·
                        rfl

theorem cell23_1729379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_1729379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729379 prefixEnd_1729379 := by exact prefixLift 1729379
  have htrace : WordTrace (prefixWord ++ tailWord_1729379) baseStart_1729379 baseEnd_1729379 := by
    simpa [prefixWord, tailWord_1729379, baseEnd_1729379] using wordTrace_append hprefix tailTrace_1729379
  have hstable : (prefixWord ++ tailWord_1729379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729379).length < 2 ^ (prefixWord ++ tailWord_1729379).sum := by decide
  have hdescent : baseEnd_1729379 < baseStart_1729379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729390 : List Nat := [4, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1729390 : Nat := 118140960795 + 1729390 * 2 ^ 59
def prefixEnd_1729390 : Nat := 4983230072969 + 3 ^ 40 * 1729390 * 2
def baseEnd_1729390 : Nat := 888008309079093987371687

theorem tailTrace_1729390 : CollatzResearch.WordTrace tailWord_1729390 prefixEnd_1729390 888008309079093987371687 := by
  unfold tailWord_1729390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884504400590357642824203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42050690136481907428395749 7884504400590357642824203)
  ·
    refine ⟨11826756600885536464236305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7884504400590357642824203 11826756600885536464236305)
    ·
      refine ⟨8870067450664152348177229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11826756600885536464236305 8870067450664152348177229)
      ·
        refine ⟨3326275293999057130566461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8870067450664152348177229 3326275293999057130566461)
        ·
          refine ⟨1247353235249646423962423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3326275293999057130566461 1247353235249646423962423)
          ·
            refine ⟨1871029852874469635943635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247353235249646423962423 1871029852874469635943635)
            ·
              refine ⟨2806544779311704453915453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871029852874469635943635 2806544779311704453915453)
              ·
                refine ⟨1052454292241889170218295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2806544779311704453915453 1052454292241889170218295)
                ·
                  refine ⟨1578681438362833755327443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052454292241889170218295 1578681438362833755327443)
                  ·
                    refine ⟨2368022157544250632991165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1578681438362833755327443 2368022157544250632991165)
                    ·
                      refine ⟨888008309079093987371687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2368022157544250632991165 888008309079093987371687)
                      ·
                        rfl

theorem cell23_1729390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1729390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729390 prefixEnd_1729390 := by exact prefixLift 1729390
  have htrace : WordTrace (prefixWord ++ tailWord_1729390) baseStart_1729390 baseEnd_1729390 := by
    simpa [prefixWord, tailWord_1729390, baseEnd_1729390] using wordTrace_append hprefix tailTrace_1729390
  have hstable : (prefixWord ++ tailWord_1729390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729390).length < 2 ^ (prefixWord ++ tailWord_1729390).sum := by decide
  have hdescent : baseEnd_1729390 < baseStart_1729390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729395 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 3]
def baseStart_1729395 : Nat := 118140960795 + 1729395 * 2 ^ 59
def prefixEnd_1729395 : Nat := 4983230072969 + 3 ^ 40 * 1729395 * 2
def baseEnd_1729395 : Nat := 888010876482366467809163

theorem tailTrace_1729395 : CollatzResearch.WordTrace tailWord_1729395 prefixEnd_1729395 888010876482366467809163 := by
  unfold tailWord_1729395
  simp only [CollatzResearch.WordTrace]
  refine ⟨63076217569704746996525639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42050811713136497997683759 63076217569704746996525639)
  ·
    refine ⟨94614326354557120494788459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63076217569704746996525639 94614326354557120494788459)
    ·
      refine ⟨141921489531835680742182689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94614326354557120494788459 141921489531835680742182689)
      ·
        refine ⟨106441117148876760556637017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141921489531835680742182689 106441117148876760556637017)
        ·
          refine ⟨79830837861657570417477763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106441117148876760556637017 79830837861657570417477763)
          ·
            refine ⟨119746256792486355626216645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79830837861657570417477763 119746256792486355626216645)
            ·
              refine ⟨22452423148591191679915621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119746256792486355626216645 22452423148591191679915621)
              ·
                refine ⟨4209829340360848439984179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22452423148591191679915621 4209829340360848439984179)
                ·
                  refine ⟨6314744010541272659976269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209829340360848439984179 6314744010541272659976269)
                  ·
                    refine ⟨2368029003952977247491101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6314744010541272659976269 2368029003952977247491101)
                    ·
                      refine ⟨888010876482366467809163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2368029003952977247491101 888010876482366467809163)
                      ·
                        rfl

theorem cell23_1729395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_1729395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729395 prefixEnd_1729395 := by exact prefixLift 1729395
  have htrace : WordTrace (prefixWord ++ tailWord_1729395) baseStart_1729395 baseEnd_1729395 := by
    simpa [prefixWord, tailWord_1729395, baseEnd_1729395] using wordTrace_append hprefix tailTrace_1729395
  have hstable : (prefixWord ++ tailWord_1729395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729395).length < 2 ^ (prefixWord ++ tailWord_1729395).sum := by decide
  have hdescent : baseEnd_1729395 < baseStart_1729395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729413 : List Nat := [1, 3, 1, 1, 3, 4, 3, 2, 1, 2, 2]
def baseStart_1729413 : Nat := 118140960795 + 1729413 * 2 ^ 59
def prefixEnd_1729413 : Nat := 4983230072969 + 3 ^ 40 * 1729413 * 2
def baseEnd_1729413 : Nat := 888020119134147397384081

theorem tailTrace_1729413 : CollatzResearch.WordTrace tailWord_1729413 prefixEnd_1729413 888020119134147397384081 := by
  unfold tailWord_1729413
  simp only [CollatzResearch.WordTrace]
  refine ⟨63076874083639536070680893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42051249389093024047120595 63076874083639536070680893)
  ·
    refine ⟨23653827781364826026505335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63076874083639536070680893 23653827781364826026505335)
    ·
      refine ⟨35480741672047239039758003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23653827781364826026505335 35480741672047239039758003)
      ·
        refine ⟨53221112508070858559637005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35480741672047239039758003 53221112508070858559637005)
        ·
          refine ⟨19957917190526571959863877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53221112508070858559637005 19957917190526571959863877)
          ·
            refine ⟨3742109473223732242474477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19957917190526571959863877 3742109473223732242474477)
            ·
              refine ⟨1403291052458899590927929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3742109473223732242474477 1403291052458899590927929)
              ·
                refine ⟨1052468289344174693195947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403291052458899590927929 1052468289344174693195947)
                ·
                  refine ⟨1578702434016262039793921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052468289344174693195947 1578702434016262039793921)
                  ·
                    refine ⟨1184026825512196529845441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1578702434016262039793921 1184026825512196529845441)
                    ·
                      refine ⟨888020119134147397384081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184026825512196529845441 888020119134147397384081)
                      ·
                        rfl

theorem cell23_1729413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_1729413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729413 prefixEnd_1729413 := by exact prefixLift 1729413
  have htrace : WordTrace (prefixWord ++ tailWord_1729413) baseStart_1729413 baseEnd_1729413 := by
    simpa [prefixWord, tailWord_1729413, baseEnd_1729413] using wordTrace_append hprefix tailTrace_1729413
  have hstable : (prefixWord ++ tailWord_1729413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729413).length < 2 ^ (prefixWord ++ tailWord_1729413).sum := by decide
  have hdescent : baseEnd_1729413 < baseStart_1729413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729429 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_1729429 : Nat := 118140960795 + 1729429 * 2 ^ 59
def prefixEnd_1729429 : Nat := 4983230072969 + 3 ^ 40 * 1729429 * 2
def baseEnd_1729429 : Nat := 888028334824619334784007

theorem tailTrace_1729429 : CollatzResearch.WordTrace tailWord_1729429 prefixEnd_1729429 888028334824619334784007 := by
  unfold tailWord_1729429
  simp only [CollatzResearch.WordTrace]
  refine ⟨63077457651581570803263341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42051638434387713868842227 63077457651581570803263341)
  ·
    refine ⟨23654046619343089051223753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63077457651581570803263341 23654046619343089051223753)
    ·
      refine ⟨17740534964507316788417815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23654046619343089051223753 17740534964507316788417815)
      ·
        refine ⟨26610802446760975182626723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17740534964507316788417815 26610802446760975182626723)
        ·
          refine ⟨39916203670141462773940085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26610802446760975182626723 39916203670141462773940085)
          ·
            refine ⟨3742144094075762135056883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39916203670141462773940085 3742144094075762135056883)
            ·
              refine ⟨5613216141113643202585325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742144094075762135056883 5613216141113643202585325)
              ·
                refine ⟨2104956052917616200969497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613216141113643202585325 2104956052917616200969497)
                ·
                  refine ⟨1578717039688212150727123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2104956052917616200969497 1578717039688212150727123)
                  ·
                    refine ⟨2368075559532318226090685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1578717039688212150727123 2368075559532318226090685)
                    ·
                      refine ⟨888028334824619334784007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2368075559532318226090685 888028334824619334784007)
                      ·
                        rfl

theorem cell23_1729429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_1729429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729429 prefixEnd_1729429 := by exact prefixLift 1729429
  have htrace : WordTrace (prefixWord ++ tailWord_1729429) baseStart_1729429 baseEnd_1729429 := by
    simpa [prefixWord, tailWord_1729429, baseEnd_1729429] using wordTrace_append hprefix tailTrace_1729429
  have hstable : (prefixWord ++ tailWord_1729429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729429).length < 2 ^ (prefixWord ++ tailWord_1729429).sum := by decide
  have hdescent : baseEnd_1729429 < baseStart_1729429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729439 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 3, 3, 2]
def baseStart_1729439 : Nat := 118140960795 + 1729439 * 2 ^ 59
def prefixEnd_1729439 : Nat := 4983230072969 + 3 ^ 40 * 1729439 * 2
def baseEnd_1729439 : Nat := 888033469631164295658961

theorem tailTrace_1729439 : CollatzResearch.WordTrace tailWord_1729439 prefixEnd_1729439 888033469631164295658961 := by
  unfold tailWord_1729439
  simp only [CollatzResearch.WordTrace]
  refine ⟨63077822381545342511127371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42051881587696895007418247 63077822381545342511127371)
  ·
    refine ⟨94616733572318013766691057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63077822381545342511127371 94616733572318013766691057)
    ·
      refine ⟨70962550179238510325018293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94616733572318013766691057 70962550179238510325018293)
      ·
        refine ⟨6652739079303610342970465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70962550179238510325018293 6652739079303610342970465)
        ·
          refine ⟨4989554309477707757227849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6652739079303610342970465 4989554309477707757227849)
          ·
            refine ⟨3742165732108280817920887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4989554309477707757227849 3742165732108280817920887)
            ·
              refine ⟨5613248598162421226881331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742165732108280817920887 5613248598162421226881331)
              ·
                refine ⟨8419872897243631840321997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613248598162421226881331 8419872897243631840321997)
                ·
                  refine ⟨3157452336466361940120749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8419872897243631840321997 3157452336466361940120749)
                  ·
                    refine ⟨1184044626174885727545281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157452336466361940120749 1184044626174885727545281)
                    ·
                      refine ⟨888033469631164295658961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184044626174885727545281 888033469631164295658961)
                      ·
                        rfl

theorem cell23_1729439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_1729439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729439 prefixEnd_1729439 := by exact prefixLift 1729439
  have htrace : WordTrace (prefixWord ++ tailWord_1729439) baseStart_1729439 baseEnd_1729439 := by
    simpa [prefixWord, tailWord_1729439, baseEnd_1729439] using wordTrace_append hprefix tailTrace_1729439
  have hstable : (prefixWord ++ tailWord_1729439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729439).length < 2 ^ (prefixWord ++ tailWord_1729439).sum := by decide
  have hdescent : baseEnd_1729439 < baseStart_1729439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729452 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 1, 4, 2]
def baseStart_1729452 : Nat := 118140960795 + 1729452 * 2 ^ 59
def prefixEnd_1729452 : Nat := 4983230072969 + 3 ^ 40 * 1729452 * 2
def baseEnd_1729452 : Nat := 888040144879672744796401

theorem tailTrace_1729452 : CollatzResearch.WordTrace tailWord_1729452 prefixEnd_1729452 888040144879672744796401 := by
  unfold tailWord_1729452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31539148265249122865675305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42052197686998830487567073 31539148265249122865675305)
  ·
    refine ⟨23654361198936842149256479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31539148265249122865675305 23654361198936842149256479)
    ·
      refine ⟨35481541798405263223884719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23654361198936842149256479 35481541798405263223884719)
      ·
        refine ⟨53222312697607894835827079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35481541798405263223884719 53222312697607894835827079)
        ·
          refine ⟨79833469046411842253740619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53222312697607894835827079 79833469046411842253740619)
          ·
            refine ⟨119750203569617763380610929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79833469046411842253740619 119750203569617763380610929)
            ·
              refine ⟨89812652677213322535458197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119750203569617763380610929 89812652677213322535458197)
              ·
                refine ⟨4209968094244374493849603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89812652677213322535458197 4209968094244374493849603)
                ·
                  refine ⟨6314952141366561740774405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209968094244374493849603 6314952141366561740774405)
                  ·
                    refine ⟨1184053526506230326395201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6314952141366561740774405 1184053526506230326395201)
                    ·
                      refine ⟨888040144879672744796401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184053526506230326395201 888040144879672744796401)
                      ·
                        rfl

theorem cell23_1729452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_1729452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729452 prefixEnd_1729452 := by exact prefixLift 1729452
  have htrace : WordTrace (prefixWord ++ tailWord_1729452) baseStart_1729452 baseEnd_1729452 := by
    simpa [prefixWord, tailWord_1729452, baseEnd_1729452] using wordTrace_append hprefix tailTrace_1729452
  have hstable : (prefixWord ++ tailWord_1729452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729452).length < 2 ^ (prefixWord ++ tailWord_1729452).sum := by decide
  have hdescent : baseEnd_1729452 < baseStart_1729452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729486 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_1729486 : Nat := 118140960795 + 1729486 * 2 ^ 59
def prefixEnd_1729486 : Nat := 4983230072969 + 3 ^ 40 * 1729486 * 2
def baseEnd_1729486 : Nat := 888057603221925611771245

theorem tailTrace_1729486 : CollatzResearch.WordTrace tailWord_1729486 prefixEnd_1729486 888057603221925611771245 := by
  unfold tailWord_1729486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884942076546883692261039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42053024408250046358725541 7884942076546883692261039)
  ·
    refine ⟨11827413114820325538391559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7884942076546883692261039 11827413114820325538391559)
    ·
      refine ⟨17741119672230488307587339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827413114820325538391559 17741119672230488307587339)
      ·
        refine ⟨26611679508345732461381009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17741119672230488307587339 26611679508345732461381009)
        ·
          refine ⟨19958759631259299346035757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26611679508345732461381009 19958759631259299346035757)
          ·
            refine ⟨7484534861722237254763409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19958759631259299346035757 7484534861722237254763409)
            ·
              refine ⟨5613401146291677941072557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7484534861722237254763409 5613401146291677941072557)
              ·
                refine ⟨2105025429859379227902209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613401146291677941072557 2105025429859379227902209)
                ·
                  refine ⟨1578769072394534420926657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2105025429859379227902209 1578769072394534420926657)
                  ·
                    refine ⟨1184076804295900815694993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1578769072394534420926657 1184076804295900815694993)
                    ·
                      refine ⟨888057603221925611771245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184076804295900815694993 888057603221925611771245)
                      ·
                        rfl

theorem cell23_1729486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_1729486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729486 prefixEnd_1729486 := by exact prefixLift 1729486
  have htrace : WordTrace (prefixWord ++ tailWord_1729486) baseStart_1729486 baseEnd_1729486 := by
    simpa [prefixWord, tailWord_1729486, baseEnd_1729486] using wordTrace_append hprefix tailTrace_1729486
  have hstable : (prefixWord ++ tailWord_1729486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729486).length < 2 ^ (prefixWord ++ tailWord_1729486).sum := by decide
  have hdescent : baseEnd_1729486 < baseStart_1729486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729492 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 7]
def baseStart_1729492 : Nat := 118140960795 + 1729492 * 2 ^ 59
def prefixEnd_1729492 : Nat := 4983230072969 + 3 ^ 40 * 1729492 * 2
def baseEnd_1729492 : Nat := 98673409345094732032913

theorem tailTrace_1729492 : CollatzResearch.WordTrace tailWord_1729492 prefixEnd_1729492 98673409345094732032913 := by
  unfold tailWord_1729492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31539877725176666281403365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42053170300235555041871153 31539877725176666281403365)
  ·
    refine ⟨5913727073470624927763131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31539877725176666281403365 5913727073470624927763131)
    ·
      refine ⟨8870590610205937391644697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5913727073470624927763131 8870590610205937391644697)
      ·
        refine ⟨6652942957654453043733523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8870590610205937391644697 6652942957654453043733523)
        ·
          refine ⟨9979414436481679565600285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6652942957654453043733523 9979414436481679565600285)
          ·
            refine ⟨3742280413680629837100107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9979414436481679565600285 3742280413680629837100107)
            ·
              refine ⟨5613420620520944755650161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742280413680629837100107 5613420620520944755650161)
              ·
                refine ⟨4210065465390708566737621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5613420620520944755650161 4210065465390708566737621)
                ·
                  refine ⟨98673409345094732032913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4210065465390708566737621 98673409345094732032913)
                  ·
                    rfl

theorem cell23_1729492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_1729492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729492 prefixEnd_1729492 := by exact prefixLift 1729492
  have htrace : WordTrace (prefixWord ++ tailWord_1729492) baseStart_1729492 baseEnd_1729492 := by
    simpa [prefixWord, tailWord_1729492, baseEnd_1729492] using wordTrace_append hprefix tailTrace_1729492
  have hstable : (prefixWord ++ tailWord_1729492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729492).length < 2 ^ (prefixWord ++ tailWord_1729492).sum := by decide
  have hdescent : baseEnd_1729492 < baseStart_1729492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729555 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4]
def baseStart_1729555 : Nat := 118140960795 + 1729555 * 2 ^ 59
def prefixEnd_1729555 : Nat := 4983230072969 + 3 ^ 40 * 1729555 * 2
def baseEnd_1729555 : Nat := 888093033387085841808427

theorem tailTrace_1729555 : CollatzResearch.WordTrace tailWord_1729555 prefixEnd_1729555 888093033387085841808427 := by
  unfold tailWord_1729555
  simp only [CollatzResearch.WordTrace]
  refine ⟨63082053249125094322350119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42054702166083396214900079 63082053249125094322350119)
  ·
    refine ⟨94623079873687641483525179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63082053249125094322350119 94623079873687641483525179)
    ·
      refine ⟨141934619810531462225287769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94623079873687641483525179 141934619810531462225287769)
      ·
        refine ⟨106450964857898596668965827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141934619810531462225287769 106450964857898596668965827)
        ·
          refine ⟨159676447286847895003448741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106450964857898596668965827 159676447286847895003448741)
          ·
            refine ⟨29939333866283980313146639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159676447286847895003448741 29939333866283980313146639)
            ·
              refine ⟨44909000799425970469719959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29939333866283980313146639 44909000799425970469719959)
              ·
                refine ⟨67363501199138955704579939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44909000799425970469719959 67363501199138955704579939)
                ·
                  refine ⟨101045251798708433556869909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67363501199138955704579939 101045251798708433556869909)
                  ·
                    refine ⟨4736496178064457822978277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101045251798708433556869909 4736496178064457822978277)
                    ·
                      refine ⟨888093033387085841808427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4736496178064457822978277 888093033387085841808427)
                      ·
                        rfl

theorem cell23_1729555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_1729555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729555 prefixEnd_1729555 := by exact prefixLift 1729555
  have htrace : WordTrace (prefixWord ++ tailWord_1729555) baseStart_1729555 baseEnd_1729555 := by
    simpa [prefixWord, tailWord_1729555, baseEnd_1729555] using wordTrace_append hprefix tailTrace_1729555
  have hstable : (prefixWord ++ tailWord_1729555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729555).length < 2 ^ (prefixWord ++ tailWord_1729555).sum := by decide
  have hdescent : baseEnd_1729555 < baseStart_1729555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729562 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1729562 : Nat := 118140960795 + 1729562 * 2 ^ 59
def prefixEnd_1729562 : Nat := 4983230072969 + 3 ^ 40 * 1729562 * 2
def baseEnd_1729562 : Nat := 888096627751667314420895

theorem tailTrace_1729562 : CollatzResearch.WordTrace tailWord_1729562 prefixEnd_1729562 888096627751667314420895 := by
  unfold tailWord_1729562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15770577140024933629463735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42054872373399823011903293 15770577140024933629463735)
  ·
    refine ⟨23655865710037400444195603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15770577140024933629463735 23655865710037400444195603)
    ·
      refine ⟨35483798565056100666293405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23655865710037400444195603 35483798565056100666293405)
      ·
        refine ⟨13306424461896037749860027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35483798565056100666293405 13306424461896037749860027)
        ·
          refine ⟨19959636692844056624790041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306424461896037749860027 19959636692844056624790041)
          ·
            refine ⟨14969727519633042468592531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19959636692844056624790041 14969727519633042468592531)
            ·
              refine ⟨22454591279449563702888797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14969727519633042468592531 22454591279449563702888797)
              ·
                refine ⟨8420471729793586388583299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22454591279449563702888797 8420471729793586388583299)
                ·
                  refine ⟨12630707594690379582874949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8420471729793586388583299 12630707594690379582874949)
                  ·
                    refine ⟨2368257674004446171789053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12630707594690379582874949 2368257674004446171789053)
                    ·
                      refine ⟨888096627751667314420895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2368257674004446171789053 888096627751667314420895)
                      ·
                        rfl

theorem cell23_1729562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1729562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729562 prefixEnd_1729562 := by exact prefixLift 1729562
  have htrace : WordTrace (prefixWord ++ tailWord_1729562) baseStart_1729562 baseEnd_1729562 := by
    simpa [prefixWord, tailWord_1729562, baseEnd_1729562] using wordTrace_append hprefix tailTrace_1729562
  have hstable : (prefixWord ++ tailWord_1729562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729562).length < 2 ^ (prefixWord ++ tailWord_1729562).sum := by decide
  have hdescent : baseEnd_1729562 < baseStart_1729562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729582 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_1729582 : Nat := 118140960795 + 1729582 * 2 ^ 59
def prefixEnd_1729582 : Nat := 4983230072969 + 3 ^ 40 * 1729582 * 2
def baseEnd_1729582 : Nat := 98678544151639692907867

theorem tailTrace_1729582 : CollatzResearch.WordTrace tailWord_1729582 prefixEnd_1729582 98678544151639692907867 := by
  unfold tailWord_1729582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885379752503409741697875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42055358680018185289055333 7885379752503409741697875)
  ·
    refine ⟨11828069628755114612546813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7885379752503409741697875 11828069628755114612546813)
    ·
      refine ⟨4435526110783167979705055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11828069628755114612546813 4435526110783167979705055)
      ·
        refine ⟨6653289166174751969557583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4435526110783167979705055 6653289166174751969557583)
        ·
          refine ⟨9979933749262127954336375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6653289166174751969557583 9979933749262127954336375)
          ·
            refine ⟨14969900623893191931504563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9979933749262127954336375 14969900623893191931504563)
            ·
              refine ⟨22454850935839787897256845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14969900623893191931504563 22454850935839787897256845)
              ·
                refine ⟨8420569100939920461471317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22454850935839787897256845 8420569100939920461471317)
                ·
                  refine ⟨98678544151639692907867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8420569100939920461471317 98678544151639692907867)
                  ·
                    rfl

theorem cell23_1729582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_1729582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729582 prefixEnd_1729582 := by exact prefixLift 1729582
  have htrace : WordTrace (prefixWord ++ tailWord_1729582) baseStart_1729582 baseEnd_1729582 := by
    simpa [prefixWord, tailWord_1729582, baseEnd_1729582] using wordTrace_append hprefix tailTrace_1729582
  have hstable : (prefixWord ++ tailWord_1729582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729582).length < 2 ^ (prefixWord ++ tailWord_1729582).sum := by decide
  have hdescent : baseEnd_1729582 < baseStart_1729582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729619 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 2, 3, 2]
def baseStart_1729619 : Nat := 118140960795 + 1729619 * 2 ^ 59
def prefixEnd_1729619 : Nat := 4983230072969 + 3 ^ 40 * 1729619 * 2
def baseEnd_1729619 : Nat := 888125896148973591408133

theorem tailTrace_1729619 : CollatzResearch.WordTrace tailWord_1729619 prefixEnd_1729619 888125896148973591408133 := by
  unfold tailWord_1729619
  simp only [CollatzResearch.WordTrace]
  refine ⟨63084387520893233252679911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42056258347262155501786607 63084387520893233252679911)
  ·
    refine ⟨94626581281339849879019867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63084387520893233252679911 94626581281339849879019867)
    ·
      refine ⟨141939871922009774818529801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94626581281339849879019867 141939871922009774818529801)
      ·
        refine ⟨106454903941507331113897351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141939871922009774818529801 106454903941507331113897351)
        ·
          refine ⟨159682355912260996670846027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106454903941507331113897351 159682355912260996670846027)
          ·
            refine ⟨239523533868391495006269041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159682355912260996670846027 239523533868391495006269041)
            ·
              refine ⟨179642650401293621254701781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239523533868391495006269041 179642650401293621254701781)
              ·
                refine ⟨4210374618780319248157073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179642650401293621254701781 4210374618780319248157073)
                ·
                  refine ⟨3157780964085239436117805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210374618780319248157073 3157780964085239436117805)
                  ·
                    refine ⟨1184167861531964788544177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157780964085239436117805 1184167861531964788544177)
                    ·
                      refine ⟨888125896148973591408133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184167861531964788544177 888125896148973591408133)
                      ·
                        rfl

theorem cell23_1729619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3, 2].length) (baseStart_1729619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729619 prefixEnd_1729619 := by exact prefixLift 1729619
  have htrace : WordTrace (prefixWord ++ tailWord_1729619) baseStart_1729619 baseEnd_1729619 := by
    simpa [prefixWord, tailWord_1729619, baseEnd_1729619] using wordTrace_append hprefix tailTrace_1729619
  have hstable : (prefixWord ++ tailWord_1729619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729619).length < 2 ^ (prefixWord ++ tailWord_1729619).sum := by decide
  have hdescent : baseEnd_1729619 < baseStart_1729619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729683 : List Nat := [1, 1, 1, 2, 1, 2, 5, 5, 1, 2, 2]
def baseStart_1729683 : Nat := 118140960795 + 1729683 * 2 ^ 59
def prefixEnd_1729683 : Nat := 4983230072969 + 3 ^ 40 * 1729683 * 2
def baseEnd_1729683 : Nat := 888158758910861341007839

theorem tailTrace_1729683 : CollatzResearch.WordTrace tailWord_1729683 prefixEnd_1729683 888158758910861341007839 := by
  unfold tailWord_1729683
  simp only [CollatzResearch.WordTrace]
  refine ⟨63086721792661372183009703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42057814528440914788673135 63086721792661372183009703)
  ·
    refine ⟨94630082688992058274514555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63086721792661372183009703 94630082688992058274514555)
    ·
      refine ⟨141945124033488087411771833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94630082688992058274514555 141945124033488087411771833)
      ·
        refine ⟨106458843025116065558828875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141945124033488087411771833 106458843025116065558828875)
        ·
          refine ⟨159688264537674098338243313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106458843025116065558828875 159688264537674098338243313)
          ·
            refine ⟨119766198403255573753682485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159688264537674098338243313 119766198403255573753682485)
            ·
              refine ⟨11228081100305210039407733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119766198403255573753682485 11228081100305210039407733)
              ·
                refine ⟨1052632603153613441194475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11228081100305210039407733 1052632603153613441194475)
                ·
                  refine ⟨1578948904730420161791713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052632603153613441194475 1578948904730420161791713)
                  ·
                    refine ⟨1184211678547815121343785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1578948904730420161791713 1184211678547815121343785)
                    ·
                      refine ⟨888158758910861341007839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184211678547815121343785 888158758910861341007839)
                      ·
                        rfl

theorem cell23_1729683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 2, 2].length) (baseStart_1729683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729683 prefixEnd_1729683 := by exact prefixLift 1729683
  have htrace : WordTrace (prefixWord ++ tailWord_1729683) baseStart_1729683 baseEnd_1729683 := by
    simpa [prefixWord, tailWord_1729683, baseEnd_1729683] using wordTrace_append hprefix tailTrace_1729683
  have hstable : (prefixWord ++ tailWord_1729683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729683).length < 2 ^ (prefixWord ++ tailWord_1729683).sum := by decide
  have hdescent : baseEnd_1729683 < baseStart_1729683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729700 : List Nat := [2, 3, 1, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_1729700 : Nat := 118140960795 + 1729700 * 2 ^ 59
def prefixEnd_1729700 : Nat := 4983230072969 + 3 ^ 40 * 1729700 * 2
def baseEnd_1729700 : Nat := 888167488081987774495261

theorem tailTrace_1729700 : CollatzResearch.WordTrace tailWord_1729700 prefixEnd_1729700 888167488081987774495261 := by
  unfold tailWord_1729700
  simp only [CollatzResearch.WordTrace]
  refine ⟨31543670916799892043189277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42058227889066522724252369 31543670916799892043189277)
  ·
    refine ⟨11828876593799959516195979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31543670916799892043189277 11828876593799959516195979)
    ·
      refine ⟨17743314890699939274293969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11828876593799959516195979 17743314890699939274293969)
      ·
        refine ⟨13307486168024954455720477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17743314890699939274293969 13307486168024954455720477)
        ·
          refine ⟨4990307313009357920895179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13307486168024954455720477 4990307313009357920895179)
          ·
            refine ⟨7485460969514036881342769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990307313009357920895179 7485460969514036881342769)
            ·
              refine ⟨5614095727135527661007077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7485460969514036881342769 5614095727135527661007077)
              ·
                refine ⟨1052642948837911436438827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5614095727135527661007077 1052642948837911436438827)
                ·
                  refine ⟨1578964423256867154658241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052642948837911436438827 1578964423256867154658241)
                  ·
                    refine ⟨1184223317442650365993681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1578964423256867154658241 1184223317442650365993681)
                    ·
                      refine ⟨888167488081987774495261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184223317442650365993681 888167488081987774495261)
                      ·
                        rfl

theorem cell23_1729700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_1729700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729700 prefixEnd_1729700 := by exact prefixLift 1729700
  have htrace : WordTrace (prefixWord ++ tailWord_1729700) baseStart_1729700 baseEnd_1729700 := by
    simpa [prefixWord, tailWord_1729700, baseEnd_1729700] using wordTrace_append hprefix tailTrace_1729700
  have hstable : (prefixWord ++ tailWord_1729700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729700).length < 2 ^ (prefixWord ++ tailWord_1729700).sum := by decide
  have hdescent : baseEnd_1729700 < baseStart_1729700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729767 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1729767 : Nat := 118140960795 + 1729767 * 2 ^ 59
def prefixEnd_1729767 : Nat := 4983230072969 + 3 ^ 40 * 1729767 * 2
def baseEnd_1729767 : Nat := 888201891285839012357453

theorem tailTrace_1729767 : CollatzResearch.WordTrace tailWord_1729767 prefixEnd_1729767 888201891285839012357453 := by
  unfold tailWord_1729767
  simp only [CollatzResearch.WordTrace]
  refine ⟨63089785524357054529067555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42059857016238036352711703 63089785524357054529067555)
  ·
    refine ⟨94634678286535581793601333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63089785524357054529067555 94634678286535581793601333)
    ·
      refine ⟨8872001089362710793150125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94634678286535581793601333 8872001089362710793150125)
      ·
        refine ⟨3327000408511016547431297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8872001089362710793150125 3327000408511016547431297)
        ·
          refine ⟨2495250306383262410573473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3327000408511016547431297 2495250306383262410573473)
          ·
            refine ⟨1871437729787446807930105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2495250306383262410573473 1871437729787446807930105)
            ·
              refine ⟨1403578297340585105947579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871437729787446807930105 1403578297340585105947579)
              ·
                refine ⟨2105367446010877658921369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403578297340585105947579 2105367446010877658921369)
                ·
                  refine ⟨1579025584508158244191027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2105367446010877658921369 1579025584508158244191027)
                  ·
                    refine ⟨2368538376762237366286541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1579025584508158244191027 2368538376762237366286541)
                    ·
                      refine ⟨888201891285839012357453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2368538376762237366286541 888201891285839012357453)
                      ·
                        rfl

theorem cell23_1729767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1729767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729767 prefixEnd_1729767 := by exact prefixLift 1729767
  have htrace : WordTrace (prefixWord ++ tailWord_1729767) baseStart_1729767 baseEnd_1729767 := by
    simpa [prefixWord, tailWord_1729767, baseEnd_1729767] using wordTrace_append hprefix tailTrace_1729767
  have hstable : (prefixWord ++ tailWord_1729767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729767).length < 2 ^ (prefixWord ++ tailWord_1729767).sum := by decide
  have hdescent : baseEnd_1729767 < baseStart_1729767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729789 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1729789 : Nat := 118140960795 + 1729789 * 2 ^ 59
def prefixEnd_1729789 : Nat := 4983230072969 + 3 ^ 40 * 1729789 * 2
def baseEnd_1729789 : Nat := 888213187860237926282351

theorem tailTrace_1729789 : CollatzResearch.WordTrace tailWord_1729789 prefixEnd_1729789 888213187860237926282351 := by
  unfold tailWord_1729789
  simp only [CollatzResearch.WordTrace]
  refine ⟨63090587930277352286368421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42060391953518234857578947 63090587930277352286368421)
  ·
    refine ⟨11829485236927003553694079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63090587930277352286368421 11829485236927003553694079)
    ·
      refine ⟨17744227855390505330541119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11829485236927003553694079 17744227855390505330541119)
      ·
        refine ⟨26616341783085757995811679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17744227855390505330541119 26616341783085757995811679)
        ·
          refine ⟨39924512674628636993717519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26616341783085757995811679 39924512674628636993717519)
          ·
            refine ⟨59886769011942955490576279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39924512674628636993717519 59886769011942955490576279)
            ·
              refine ⟨89830153517914433235864419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59886769011942955490576279 89830153517914433235864419)
              ·
                refine ⟨134745230276871649853796629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89830153517914433235864419 134745230276871649853796629)
                ·
                  refine ⟨6316182669228358586896717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134745230276871649853796629 6316182669228358586896717)
                  ·
                    refine ⟨2368568500960634470086269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6316182669228358586896717 2368568500960634470086269)
                    ·
                      refine ⟨888213187860237926282351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2368568500960634470086269 888213187860237926282351)
                      ·
                        rfl

theorem cell23_1729789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1729789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729789 prefixEnd_1729789 := by exact prefixLift 1729789
  have htrace : WordTrace (prefixWord ++ tailWord_1729789) baseStart_1729789 baseEnd_1729789 := by
    simpa [prefixWord, tailWord_1729789, baseEnd_1729789] using wordTrace_append hprefix tailTrace_1729789
  have hstable : (prefixWord ++ tailWord_1729789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729789).length < 2 ^ (prefixWord ++ tailWord_1729789).sum := by decide
  have hdescent : baseEnd_1729789 < baseStart_1729789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729809 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 2, 5]
def baseStart_1729809 : Nat := 118140960795 + 1729809 * 2 ^ 59
def prefixEnd_1729809 : Nat := 4983230072969 + 3 ^ 40 * 1729809 * 2
def baseEnd_1729809 : Nat := 296074485824442616010753

theorem tailTrace_1729809 : CollatzResearch.WordTrace tailWord_1729809 prefixEnd_1729809 296074485824442616010753 := by
  unfold tailWord_1729809
  simp only [CollatzResearch.WordTrace]
  refine ⟨63091317390204895702096481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42060878260136597134730987 63091317390204895702096481)
  ·
    refine ⟨47318488042653671776572361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63091317390204895702096481 47318488042653671776572361)
    ·
      refine ⟨35488866031990253832429271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47318488042653671776572361 35488866031990253832429271)
      ·
        refine ⟨53233299047985380748643907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35488866031990253832429271 53233299047985380748643907)
        ·
          refine ⟨79849948571978071122965861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53233299047985380748643907 79849948571978071122965861)
          ·
            refine ⟨14971865357245888335556099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79849948571978071122965861 14971865357245888335556099)
            ·
              refine ⟨22457798035868832503334149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14971865357245888335556099 22457798035868832503334149)
              ·
                refine ⟨4210837131725406094375153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22457798035868832503334149 4210837131725406094375153)
                ·
                  refine ⟨3158127848794054570781365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210837131725406094375153 3158127848794054570781365)
                  ·
                    refine ⟨296074485824442616010753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3158127848794054570781365 296074485824442616010753)
                    ·
                      rfl

theorem cell23_1729809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_1729809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729809 prefixEnd_1729809 := by exact prefixLift 1729809
  have htrace : WordTrace (prefixWord ++ tailWord_1729809) baseStart_1729809 baseEnd_1729809 := by
    simpa [prefixWord, tailWord_1729809, baseEnd_1729809] using wordTrace_append hprefix tailTrace_1729809
  have hstable : (prefixWord ++ tailWord_1729809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729809).length < 2 ^ (prefixWord ++ tailWord_1729809).sum := by decide
  have hdescent : baseEnd_1729809 < baseStart_1729809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729816 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 2, 5, 2]
def baseStart_1729816 : Nat := 118140960795 + 1729816 * 2 ^ 59
def prefixEnd_1729816 : Nat := 4983230072969 + 3 ^ 40 * 1729816 * 2
def baseEnd_1729816 : Nat := 888227051837909320644727

theorem tailTrace_1729816 : CollatzResearch.WordTrace tailWord_1729816 prefixEnd_1729816 888227051837909320644727 := by
  unfold tailWord_1729816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31545786350589767948800651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42061048467453023931734201 31545786350589767948800651)
  ·
    refine ⟨47318679525884651923200977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31545786350589767948800651 47318679525884651923200977)
    ·
      refine ⟨35489009644413488942400733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47318679525884651923200977 35489009644413488942400733)
      ·
        refine ⟨13308378616655058353400275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35489009644413488942400733 13308378616655058353400275)
        ·
          refine ⟨19962567924982587530100413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13308378616655058353400275 19962567924982587530100413)
          ·
            refine ⟨7485962971868470323787655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19962567924982587530100413 7485962971868470323787655)
            ·
              refine ⟨11228944457802705485681483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485962971868470323787655 11228944457802705485681483)
              ·
                refine ⟨16843416686704058228522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11228944457802705485681483 16843416686704058228522225)
                ·
                  refine ⟨12632562515028043671391669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16843416686704058228522225 12632562515028043671391669)
                  ·
                    refine ⟨1184302735783879094192969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12632562515028043671391669 1184302735783879094192969)
                    ·
                      refine ⟨888227051837909320644727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184302735783879094192969 888227051837909320644727)
                      ·
                        rfl

theorem cell23_1729816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_1729816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729816 prefixEnd_1729816 := by exact prefixLift 1729816
  have htrace : WordTrace (prefixWord ++ tailWord_1729816) baseStart_1729816 baseEnd_1729816 := by
    simpa [prefixWord, tailWord_1729816, baseEnd_1729816] using wordTrace_append hprefix tailTrace_1729816
  have hstable : (prefixWord ++ tailWord_1729816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729816).length < 2 ^ (prefixWord ++ tailWord_1729816).sum := by decide
  have hdescent : baseEnd_1729816 < baseStart_1729816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729866 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_1729866 : Nat := 118140960795 + 1729866 * 2 ^ 59
def prefixEnd_1729866 : Nat := 4983230072969 + 3 ^ 40 * 1729866 * 2
def baseEnd_1729866 : Nat := 888252725870634125019497

theorem tailTrace_1729866 : CollatzResearch.WordTrace tailWord_1729866 prefixEnd_1729866 888252725870634125019497 := by
  unfold tailWord_1729866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15773349087749598609230363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42062264233998929624614301 15773349087749598609230363)
  ·
    refine ⟨23660023631624397913845545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15773349087749598609230363 23660023631624397913845545)
    ·
      refine ⟨17745017723718298435384159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23660023631624397913845545 17745017723718298435384159)
      ·
        refine ⟨26617526585577447653076239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17745017723718298435384159 26617526585577447653076239)
        ·
          refine ⟨39926289878366171479614359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26617526585577447653076239 39926289878366171479614359)
          ·
            refine ⟨59889434817549257219421539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39926289878366171479614359 59889434817549257219421539)
            ·
              refine ⟨89834152226323885829132309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59889434817549257219421539 89834152226323885829132309)
              ·
                refine ⟨4210975885608932148240577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89834152226323885829132309 4210975885608932148240577)
                ·
                  refine ⟨3158231914206699111180433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210975885608932148240577 3158231914206699111180433)
                  ·
                    refine ⟨2368673935655024333385325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3158231914206699111180433 2368673935655024333385325)
                    ·
                      refine ⟨888252725870634125019497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2368673935655024333385325 888252725870634125019497)
                      ·
                        rfl

theorem cell23_1729866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_1729866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729866 prefixEnd_1729866 := by exact prefixLift 1729866
  have htrace : WordTrace (prefixWord ++ tailWord_1729866) baseStart_1729866 baseEnd_1729866 := by
    simpa [prefixWord, tailWord_1729866, baseEnd_1729866] using wordTrace_append hprefix tailTrace_1729866
  have hstable : (prefixWord ++ tailWord_1729866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729866).length < 2 ^ (prefixWord ++ tailWord_1729866).sum := by decide
  have hdescent : baseEnd_1729866 < baseStart_1729866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729873 : List Nat := [1, 2, 2, 1, 4, 1, 1, 6, 1, 4]
def baseStart_1729873 : Nat := 118140960795 + 1729873 * 2 ^ 59
def prefixEnd_1729873 : Nat := 4983230072969 + 3 ^ 40 * 1729873 * 2
def baseEnd_1729873 : Nat := 296085440078405199210655

theorem tailTrace_1729873 : CollatzResearch.WordTrace tailWord_1729873 prefixEnd_1729873 296085440078405199210655 := by
  unfold tailWord_1729873
  simp only [CollatzResearch.WordTrace]
  refine ⟨63093651661973034632426273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42062434441315356421617515 63093651661973034632426273)
  ·
    refine ⟨47320238746479775974319705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63093651661973034632426273 47320238746479775974319705)
    ·
      refine ⟨35490179059859831980739779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47320238746479775974319705 35490179059859831980739779)
      ·
        refine ⟨53235268589789747971109669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35490179059859831980739779 53235268589789747971109669)
        ·
          refine ⟨9981612860585577744583063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53235268589789747971109669 9981612860585577744583063)
          ·
            refine ⟨14972419290878366616874595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9981612860585577744583063 14972419290878366616874595)
            ·
              refine ⟨22458628936317549925311893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14972419290878366616874595 22458628936317549925311893)
              ·
                refine ⟨1052748231389885152748995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22458628936317549925311893 1052748231389885152748995)
                ·
                  refine ⟨1579122347084827729123493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052748231389885152748995 1579122347084827729123493)
                  ·
                    refine ⟨296085440078405199210655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579122347084827729123493 296085440078405199210655)
                    ·
                      rfl

theorem cell23_1729873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_1729873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729873 prefixEnd_1729873 := by exact prefixLift 1729873
  have htrace : WordTrace (prefixWord ++ tailWord_1729873) baseStart_1729873 baseEnd_1729873 := by
    simpa [prefixWord, tailWord_1729873, baseEnd_1729873] using wordTrace_append hprefix tailTrace_1729873
  have hstable : (prefixWord ++ tailWord_1729873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729873).length < 2 ^ (prefixWord ++ tailWord_1729873).sum := by decide
  have hdescent : baseEnd_1729873 < baseStart_1729873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729916 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_1729916 : Nat := 118140960795 + 1729916 * 2 ^ 59
def prefixEnd_1729916 : Nat := 4983230072969 + 3 ^ 40 * 1729916 * 2
def baseEnd_1729916 : Nat := 296092799967786309798089

theorem tailTrace_1729916 : CollatzResearch.WordTrace tailWord_1729916 prefixEnd_1729916 296092799967786309798089 := by
  unfold tailWord_1729916
  simp only [CollatzResearch.WordTrace]
  refine ⟨31547610000408626488120801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42063480000544835317494401 31547610000408626488120801)
  ·
    refine ⟨23660707500306469866090601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31547610000408626488120801 23660707500306469866090601)
    ·
      refine ⟨17745530625229852399567951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23660707500306469866090601 17745530625229852399567951)
      ·
        refine ⟨26618295937844778599351927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17745530625229852399567951 26618295937844778599351927)
        ·
          refine ⟨39927443906767167899027891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26618295937844778599351927 39927443906767167899027891)
          ·
            refine ⟨59891165860150751848541837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39927443906767167899027891 59891165860150751848541837)
            ·
              refine ⟨22459187197556531943203189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59891165860150751848541837 22459187197556531943203189)
              ·
                refine ⟨2105548799770924869675299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22459187197556531943203189 2105548799770924869675299)
                ·
                  refine ⟨3158323199656387304512949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105548799770924869675299 3158323199656387304512949)
                  ·
                    refine ⟨296092799967786309798089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3158323199656387304512949 296092799967786309798089)
                    ·
                      rfl

theorem cell23_1729916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_1729916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729916 prefixEnd_1729916 := by exact prefixLift 1729916
  have htrace : WordTrace (prefixWord ++ tailWord_1729916) baseStart_1729916 baseEnd_1729916 := by
    simpa [prefixWord, tailWord_1729916, baseEnd_1729916] using wordTrace_append hprefix tailTrace_1729916
  have hstable : (prefixWord ++ tailWord_1729916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729916).length < 2 ^ (prefixWord ++ tailWord_1729916).sum := by decide
  have hdescent : baseEnd_1729916 < baseStart_1729916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729923 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 4, 3, 2]
def baseStart_1729923 : Nat := 118140960795 + 1729923 * 2 ^ 59
def prefixEnd_1729923 : Nat := 4983230072969 + 3 ^ 40 * 1729923 * 2
def baseEnd_1729923 : Nat := 888281994267940402006735

theorem tailTrace_1729923 : CollatzResearch.WordTrace tailWord_1729923 prefixEnd_1729923 888281994267940402006735 := by
  unfold tailWord_1729923
  simp only [CollatzResearch.WordTrace]
  refine ⟨63095475311791893171746423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42063650207861262114497615 63095475311791893171746423)
  ·
    refine ⟨94643212967687839757619635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63095475311791893171746423 94643212967687839757619635)
    ·
      refine ⟨141964819451531759636429453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94643212967687839757619635 141964819451531759636429453)
      ·
        refine ⟨53236807294324409863661045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141964819451531759636429453 53236807294324409863661045)
        ·
          refine ⟨4990950683842913424718223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53236807294324409863661045 4990950683842913424718223)
          ·
            refine ⟨7486426025764370137077335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990950683842913424718223 7486426025764370137077335)
            ·
              refine ⟨11229639038646555205616003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7486426025764370137077335 11229639038646555205616003)
              ·
                refine ⟨16844458557969832808424005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11229639038646555205616003 16844458557969832808424005)
                ·
                  refine ⟨3158335979619343651579501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16844458557969832808424005 3158335979619343651579501)
                  ·
                    refine ⟨1184375992357253869342313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158335979619343651579501 1184375992357253869342313)
                    ·
                      refine ⟨888281994267940402006735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184375992357253869342313 888281994267940402006735)
                      ·
                        rfl

theorem cell23_1729923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_1729923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729923 prefixEnd_1729923 := by exact prefixLift 1729923
  have htrace : WordTrace (prefixWord ++ tailWord_1729923) baseStart_1729923 baseEnd_1729923 := by
    simpa [prefixWord, tailWord_1729923, baseEnd_1729923] using wordTrace_append hprefix tailTrace_1729923
  have hstable : (prefixWord ++ tailWord_1729923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729923).length < 2 ^ (prefixWord ++ tailWord_1729923).sum := by decide
  have hdescent : baseEnd_1729923 < baseStart_1729923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729946 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_1729946 : Nat := 118140960795 + 1729946 * 2 ^ 59
def prefixEnd_1729946 : Nat := 4983230072969 + 3 ^ 40 * 1729946 * 2
def baseEnd_1729946 : Nat := 296097934774331270673043

theorem tailTrace_1729946 : CollatzResearch.WordTrace tailWord_1729946 prefixEnd_1729946 296097934774331270673043 := by
  unfold tailWord_1729946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15774078547677142024958423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42064209460472378733222461 15774078547677142024958423)
  ·
    refine ⟨23661117821515713037437635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15774078547677142024958423 23661117821515713037437635)
    ·
      refine ⟨35491676732273569556156453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23661117821515713037437635 35491676732273569556156453)
      ·
        refine ⟨6654689387301294291779335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35491676732273569556156453 6654689387301294291779335)
        ·
          refine ⟨9982034080951941437669003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6654689387301294291779335 9982034080951941437669003)
          ·
            refine ⟨14973051121427912156503505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982034080951941437669003 14973051121427912156503505)
            ·
              refine ⟨11229788341070934117377629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14973051121427912156503505 11229788341070934117377629)
              ·
                refine ⟨4211170627901600294016611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11229788341070934117377629 4211170627901600294016611)
                ·
                  refine ⟨6316755941852400441024917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4211170627901600294016611 6316755941852400441024917)
                  ·
                    refine ⟨296097934774331270673043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6316755941852400441024917 296097934774331270673043)
                    ·
                      rfl

theorem cell23_1729946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_1729946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729946 prefixEnd_1729946 := by exact prefixLift 1729946
  have htrace : WordTrace (prefixWord ++ tailWord_1729946) baseStart_1729946 baseEnd_1729946 := by
    simpa [prefixWord, tailWord_1729946, baseEnd_1729946] using wordTrace_append hprefix tailTrace_1729946
  have hstable : (prefixWord ++ tailWord_1729946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729946).length < 2 ^ (prefixWord ++ tailWord_1729946).sum := by decide
  have hdescent : baseEnd_1729946 < baseStart_1729946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729950 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1729950 : Nat := 118140960795 + 1729950 * 2 ^ 59
def prefixEnd_1729950 : Nat := 4983230072969 + 3 ^ 40 * 1729950 * 2
def baseEnd_1729950 : Nat := 296098619415203932123037

theorem tailTrace_1729950 : CollatzResearch.WordTrace tailWord_1729950 prefixEnd_1729950 296098619415203932123037 := by
  unfold tailWord_1729950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887057510336759597872413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42064306721796051188652869 7887057510336759597872413)
  ·
    refine ⟨2957646566376284849202155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7887057510336759597872413 2957646566376284849202155)
    ·
      refine ⟨4436469849564427273803233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2957646566376284849202155 4436469849564427273803233)
      ·
        refine ⟨3327352387173320455352425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4436469849564427273803233 3327352387173320455352425)
        ·
          refine ⟨2495514290379990341514319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3327352387173320455352425 2495514290379990341514319)
          ·
            refine ⟨3743271435569985512271479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495514290379990341514319 3743271435569985512271479)
            ·
              refine ⟨5614907153354978268407219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743271435569985512271479 5614907153354978268407219)
              ·
                refine ⟨8422360730032467402610829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614907153354978268407219 8422360730032467402610829)
                ·
                  refine ⟨3158385273762175275979061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8422360730032467402610829 3158385273762175275979061)
                  ·
                    refine ⟨296098619415203932123037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3158385273762175275979061 296098619415203932123037)
                    ·
                      rfl

theorem cell23_1729950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1729950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729950 prefixEnd_1729950 := by exact prefixLift 1729950
  have htrace : WordTrace (prefixWord ++ tailWord_1729950) baseStart_1729950 baseEnd_1729950 := by
    simpa [prefixWord, tailWord_1729950, baseEnd_1729950] using wordTrace_append hprefix tailTrace_1729950
  have hstable : (prefixWord ++ tailWord_1729950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729950).length < 2 ^ (prefixWord ++ tailWord_1729950).sum := by decide
  have hdescent : baseEnd_1729950 < baseStart_1729950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729973 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1729973 : Nat := 118140960795 + 1729973 * 2 ^ 59
def prefixEnd_1729973 : Nat := 4983230072969 + 3 ^ 40 * 1729973 * 2
def baseEnd_1729973 : Nat := 888307668300665206381505

theorem tailTrace_1729973 : CollatzResearch.WordTrace tailWord_1729973 prefixEnd_1729973 888307668300665206381505 := by
  unfold tailWord_1729973
  simp only [CollatzResearch.WordTrace]
  refine ⟨63097298961610751711066573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42064865974407167807377715 63097298961610751711066573)
  ·
    refine ⟨23661487110604031891649965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63097298961610751711066573 23661487110604031891649965)
    ·
      refine ⟨8873057666476511959368737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23661487110604031891649965 8873057666476511959368737)
      ·
        refine ⟨6654793249857383969526553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8873057666476511959368737 6654793249857383969526553)
        ·
          refine ⟨4991094937393037977144915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6654793249857383969526553 4991094937393037977144915)
          ·
            refine ⟨7486642406089556965717373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991094937393037977144915 7486642406089556965717373)
            ·
              refine ⟨2807490902283583862144015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7486642406089556965717373 2807490902283583862144015)
              ·
                refine ⟨4211236353425375793216023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807490902283583862144015 4211236353425375793216023)
                ·
                  refine ⟨6316854530138063689824035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4211236353425375793216023 6316854530138063689824035)
                  ·
                    refine ⟨9475281795207095534736053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6316854530138063689824035 9475281795207095534736053)
                    ·
                      refine ⟨888307668300665206381505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9475281795207095534736053 888307668300665206381505)
                      ·
                        rfl

theorem cell23_1729973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1729973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1729973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1729973 prefixEnd_1729973 := by exact prefixLift 1729973
  have htrace : WordTrace (prefixWord ++ tailWord_1729973) baseStart_1729973 baseEnd_1729973 := by
    simpa [prefixWord, tailWord_1729973, baseEnd_1729973] using wordTrace_append hprefix tailTrace_1729973
  have hstable : (prefixWord ++ tailWord_1729973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729973).length < 2 ^ (prefixWord ++ tailWord_1729973).sum := by decide
  have hdescent : baseEnd_1729973 < baseStart_1729973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730037 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1730037 : Nat := 118140960795 + 1730037 * 2 ^ 59
def prefixEnd_1730037 : Nat := 4983230072969 + 3 ^ 40 * 1730037 * 2
def baseEnd_1730037 : Nat := 888340531062552955981211

theorem tailTrace_1730037 : CollatzResearch.WordTrace tailWord_1730037 prefixEnd_1730037 888340531062552955981211 := by
  unfold tailWord_1730037
  simp only [CollatzResearch.WordTrace]
  refine ⟨63099633233378890641396365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42066422155585927094264243 63099633233378890641396365)
  ·
    refine ⟨23662362462517083990523637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63099633233378890641396365 23662362462517083990523637)
    ·
      refine ⟨2218346480860976624111591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23662362462517083990523637 2218346480860976624111591)
      ·
        refine ⟨3327519721291464936167387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218346480860976624111591 3327519721291464936167387)
        ·
          refine ⟨4991279581937197404251081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327519721291464936167387 4991279581937197404251081)
          ·
            refine ⟨3743459686452898053188311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4991279581937197404251081 3743459686452898053188311)
            ·
              refine ⟨5615189529679347079782467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743459686452898053188311 5615189529679347079782467)
              ·
                refine ⟨8422784294519020619673701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615189529679347079782467 8422784294519020619673701)
                ·
                  refine ⟨1579272055222316366188819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8422784294519020619673701 1579272055222316366188819)
                  ·
                    refine ⟨2368908082833474549283229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1579272055222316366188819 2368908082833474549283229)
                    ·
                      refine ⟨888340531062552955981211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2368908082833474549283229 888340531062552955981211)
                      ·
                        rfl

theorem cell23_1730037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1730037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730037 prefixEnd_1730037 := by exact prefixLift 1730037
  have htrace : WordTrace (prefixWord ++ tailWord_1730037) baseStart_1730037 baseEnd_1730037 := by
    simpa [prefixWord, tailWord_1730037, baseEnd_1730037] using wordTrace_append hprefix tailTrace_1730037
  have hstable : (prefixWord ++ tailWord_1730037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730037).length < 2 ^ (prefixWord ++ tailWord_1730037).sum := by decide
  have hdescent : baseEnd_1730037 < baseStart_1730037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730113 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1730113 : Nat := 118140960795 + 1730113 * 2 ^ 59
def prefixEnd_1730113 : Nat := 4983230072969 + 3 ^ 40 * 1730113 * 2
def baseEnd_1730113 : Nat := 296126518530764886210287

theorem tailTrace_1730113 : CollatzResearch.WordTrace tailWord_1730113 prefixEnd_1730113 296126518530764886210287 := by
  unfold tailWord_1730113
  simp only [CollatzResearch.WordTrace]
  refine ⟨63102405181103555621162993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42068270120735703747441995 63102405181103555621162993)
  ·
    refine ⟨47326803885827666715872245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63102405181103555621162993 47326803885827666715872245)
    ·
      refine ⟨4436887864296343754613023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47326803885827666715872245 4436887864296343754613023)
      ·
        refine ⟨6655331796444515631919535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436887864296343754613023 6655331796444515631919535)
        ·
          refine ⟨9982997694666773447879303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655331796444515631919535 9982997694666773447879303)
          ·
            refine ⟨14974496542000160171818955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982997694666773447879303 14974496542000160171818955)
            ·
              refine ⟨22461744813000240257728433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14974496542000160171818955 22461744813000240257728433)
              ·
                refine ⟨16846308609750180193296325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22461744813000240257728433 16846308609750180193296325)
                ·
                  refine ⟨3158682864328158786243061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16846308609750180193296325 3158682864328158786243061)
                  ·
                    refine ⟨296126518530764886210287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3158682864328158786243061 296126518530764886210287)
                    ·
                      rfl

theorem cell23_1730113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1730113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730113 prefixEnd_1730113 := by exact prefixLift 1730113
  have htrace : WordTrace (prefixWord ++ tailWord_1730113) baseStart_1730113 baseEnd_1730113 := by
    simpa [prefixWord, tailWord_1730113, baseEnd_1730113] using wordTrace_append hprefix tailTrace_1730113
  have hstable : (prefixWord ++ tailWord_1730113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730113).length < 2 ^ (prefixWord ++ tailWord_1730113).sum := by decide
  have hdescent : baseEnd_1730113 < baseStart_1730113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730130 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1730130 : Nat := 118140960795 + 1730130 * 2 ^ 59
def prefixEnd_1730130 : Nat := 4983230072969 + 3 ^ 40 * 1730130 * 2
def baseEnd_1730130 : Nat := 296129428254473697372761

theorem tailTrace_1730130 : CollatzResearch.WordTrace tailWord_1730130 prefixEnd_1730130 296129428254473697372761 := by
  unfold tailWord_1730130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15775756305510491881132961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42068683481361311683021229 15775756305510491881132961)
  ·
    refine ⟨11831817229132868910849721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15775756305510491881132961 11831817229132868910849721)
    ·
      refine ⟨8873862921849651683137291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11831817229132868910849721 8873862921849651683137291)
      ·
        refine ⟨13310794382774477524705937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8873862921849651683137291 13310794382774477524705937)
        ·
          refine ⟨9983095787080858143529453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13310794382774477524705937 9983095787080858143529453)
          ·
            refine ⟨3743660920155321803823545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9983095787080858143529453 3743660920155321803823545)
            ·
              refine ⟨2807745690116491352867659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3743660920155321803823545 2807745690116491352867659)
              ·
                refine ⟨4211618535174737029301489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807745690116491352867659 4211618535174737029301489)
                ·
                  refine ⟨3158713901381052771976117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211618535174737029301489 3158713901381052771976117)
                  ·
                    refine ⟨296129428254473697372761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3158713901381052771976117 296129428254473697372761)
                    ·
                      rfl

theorem cell23_1730130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1730130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730130 prefixEnd_1730130 := by exact prefixLift 1730130
  have htrace : WordTrace (prefixWord ++ tailWord_1730130) baseStart_1730130 baseEnd_1730130 := by
    simpa [prefixWord, tailWord_1730130, baseEnd_1730130] using wordTrace_append hprefix tailTrace_1730130
  have hstable : (prefixWord ++ tailWord_1730130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730130).length < 2 ^ (prefixWord ++ tailWord_1730130).sum := by decide
  have hdescent : baseEnd_1730130 < baseStart_1730130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730184 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1730184 : Nat := 118140960795 + 1730184 * 2 ^ 59
def prefixEnd_1730184 : Nat := 4983230072969 + 3 ^ 40 * 1730184 * 2
def baseEnd_1730184 : Nat := 888416012718763880843035

theorem tailTrace_1730184 : CollatzResearch.WordTrace tailWord_1730184 prefixEnd_1730184 888416012718763880843035 := by
  unfold tailWord_1730184
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552497381923167373498803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42069996509230889831331737 31552497381923167373498803)
  ·
    refine ⟨47328746072884751060248205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31552497381923167373498803 47328746072884751060248205)
    ·
      refine ⟨17748279777331781647593077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47328746072884751060248205 17748279777331781647593077)
      ·
        refine ⟨1663901229124854529461851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17748279777331781647593077 1663901229124854529461851)
        ·
          refine ⟨2495851843687281794192777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663901229124854529461851 2495851843687281794192777)
          ·
            refine ⟨1871888882765461345644583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2495851843687281794192777 1871888882765461345644583)
            ·
              refine ⟨2807833324148192018466875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871888882765461345644583 2807833324148192018466875)
              ·
                refine ⟨4211749986222288027700313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807833324148192018466875 4211749986222288027700313)
                ·
                  refine ⟨3158812489666716020775235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211749986222288027700313 3158812489666716020775235)
                  ·
                    refine ⟨4738218734500074031162853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3158812489666716020775235 4738218734500074031162853)
                    ·
                      refine ⟨888416012718763880843035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4738218734500074031162853 888416012718763880843035)
                      ·
                        rfl

theorem cell23_1730184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1730184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730184 prefixEnd_1730184 := by exact prefixLift 1730184
  have htrace : WordTrace (prefixWord ++ tailWord_1730184) baseStart_1730184 baseEnd_1730184 := by
    simpa [prefixWord, tailWord_1730184, baseEnd_1730184] using wordTrace_append hprefix tailTrace_1730184
  have hstable : (prefixWord ++ tailWord_1730184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730184).length < 2 ^ (prefixWord ++ tailWord_1730184).sum := by decide
  have hdescent : baseEnd_1730184 < baseStart_1730184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730240 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 2, 6, 2]
def baseStart_1730240 : Nat := 118140960795 + 1730240 * 2 ^ 59
def prefixEnd_1730240 : Nat := 4983230072969 + 3 ^ 40 * 1730240 * 2
def baseEnd_1730240 : Nat := 888444767635415661742777

theorem tailTrace_1730240 : CollatzResearch.WordTrace tailWord_1730240 prefixEnd_1730240 888444767635415661742777 := by
  unfold tailWord_1730240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31553518625821728155518087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42071358167762304207357449 31553518625821728155518087)
  ·
    refine ⟨47330277938732592233277131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31553518625821728155518087 47330277938732592233277131)
    ·
      refine ⟨70995416908098888349915697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47330277938732592233277131 70995416908098888349915697)
      ·
        refine ⟨53246562681074166262436773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70995416908098888349915697 53246562681074166262436773)
        ·
          refine ⟨9983730502701406174206895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53246562681074166262436773 9983730502701406174206895)
          ·
            refine ⟨14975595754052109261310343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9983730502701406174206895 14975595754052109261310343)
            ·
              refine ⟨22463393631078163891965515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14975595754052109261310343 22463393631078163891965515)
              ·
                refine ⟨33695090446617245837948273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22463393631078163891965515 33695090446617245837948273)
                ·
                  refine ⟨25271317834962934378461205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33695090446617245837948273 25271317834962934378461205)
                  ·
                    refine ⟨1184593023513887548990369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25271317834962934378461205 1184593023513887548990369)
                    ·
                      refine ⟨888444767635415661742777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184593023513887548990369 888444767635415661742777)
                      ·
                        rfl

theorem cell23_1730240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_1730240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730240 prefixEnd_1730240 := by exact prefixLift 1730240
  have htrace : WordTrace (prefixWord ++ tailWord_1730240) baseStart_1730240 baseEnd_1730240 := by
    simpa [prefixWord, tailWord_1730240, baseEnd_1730240] using wordTrace_append hprefix tailTrace_1730240
  have hstable : (prefixWord ++ tailWord_1730240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730240).length < 2 ^ (prefixWord ++ tailWord_1730240).sum := by decide
  have hdescent : baseEnd_1730240 < baseStart_1730240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730243 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 3]
def baseStart_1730243 : Nat := 118140960795 + 1730243 * 2 ^ 59
def prefixEnd_1730243 : Nat := 4983230072969 + 3 ^ 40 * 1730243 * 2
def baseEnd_1730243 : Nat := 888446308077379150005263

theorem tailTrace_1730243 : CollatzResearch.WordTrace tailWord_1730243 prefixEnd_1730243 888446308077379150005263 := by
  unfold tailWord_1730243
  simp only [CollatzResearch.WordTrace]
  refine ⟨63107146670632587823395383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42071431113755058548930255 63107146670632587823395383)
  ·
    refine ⟨94660720005948881735093075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63107146670632587823395383 94660720005948881735093075)
    ·
      refine ⟨141991080008923322602639613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94660720005948881735093075 141991080008923322602639613)
      ·
        refine ⟨53246655003346245975989855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141991080008923322602639613 53246655003346245975989855)
        ·
          refine ⟨79869982505019368963984783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53246655003346245975989855 79869982505019368963984783)
          ·
            refine ⟨119804973757529053445977175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79869982505019368963984783 119804973757529053445977175)
            ·
              refine ⟨179707460636293580168965763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119804973757529053445977175 179707460636293580168965763)
              ·
                refine ⟨269561190954440370253448645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179707460636293580168965763 269561190954440370253448645)
                ·
                  refine ⟨50542723303957569422521621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269561190954440370253448645 50542723303957569422521621)
                  ·
                    refine ⟨2369190154873011066680701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50542723303957569422521621 2369190154873011066680701)
                    ·
                      refine ⟨888446308077379150005263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369190154873011066680701 888446308077379150005263)
                      ·
                        rfl

theorem cell23_1730243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_1730243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730243 prefixEnd_1730243 := by exact prefixLift 1730243
  have htrace : WordTrace (prefixWord ++ tailWord_1730243) baseStart_1730243 baseEnd_1730243 := by
    simpa [prefixWord, tailWord_1730243, baseEnd_1730243] using wordTrace_append hprefix tailTrace_1730243
  have hstable : (prefixWord ++ tailWord_1730243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730243).length < 2 ^ (prefixWord ++ tailWord_1730243).sum := by decide
  have hdescent : baseEnd_1730243 < baseStart_1730243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730268 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1730268 : Nat := 118140960795 + 1730268 * 2 ^ 59
def prefixEnd_1730268 : Nat := 4983230072969 + 3 ^ 40 * 1730268 * 2
def baseEnd_1730268 : Nat := 888459145093741552192649

theorem tailTrace_1730268 : CollatzResearch.WordTrace tailWord_1730268 prefixEnd_1730268 888459145093741552192649 := by
  unfold tailWord_1730268
  simp only [CollatzResearch.WordTrace]
  refine ⟨31554029247771008546527729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42072038997028011395370305 31554029247771008546527729)
  ·
    refine ⟨23665521935828256409895797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31554029247771008546527729 23665521935828256409895797)
    ·
      refine ⟨2218642681483899038427731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23665521935828256409895797 2218642681483899038427731)
      ·
        refine ⟨3327964022225848557641597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218642681483899038427731 3327964022225848557641597)
        ·
          refine ⟨1247986508334693209115599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3327964022225848557641597 1247986508334693209115599)
          ·
            refine ⟨1871979762502039813673399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247986508334693209115599 1871979762502039813673399)
            ·
              refine ⟨2807969643753059720510099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871979762502039813673399 2807969643753059720510099)
              ·
                refine ⟨4211954465629589580765149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807969643753059720510099 4211954465629589580765149)
                ·
                  refine ⟨1579482924611096092786931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4211954465629589580765149 1579482924611096092786931)
                  ·
                    refine ⟨2369224386916644139180397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1579482924611096092786931 2369224386916644139180397)
                    ·
                      refine ⟨888459145093741552192649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369224386916644139180397 888459145093741552192649)
                      ·
                        rfl

theorem cell23_1730268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1730268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730268 prefixEnd_1730268 := by exact prefixLift 1730268
  have htrace : WordTrace (prefixWord ++ tailWord_1730268) baseStart_1730268 baseEnd_1730268 := by
    simpa [prefixWord, tailWord_1730268, baseEnd_1730268] using wordTrace_append hprefix tailTrace_1730268
  have hstable : (prefixWord ++ tailWord_1730268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730268).length < 2 ^ (prefixWord ++ tailWord_1730268).sum := by decide
  have hdescent : baseEnd_1730268 < baseStart_1730268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730280 : List Nat := [2, 1, 4, 1, 3, 2, 2, 8]
def baseStart_1730280 : Nat := 118140960795 + 1730280 * 2 ^ 59
def prefixEnd_1730280 : Nat := 4983230072969 + 3 ^ 40 * 1730280 * 2
def baseEnd_1730280 : Nat := 32906122476355389083059

theorem tailTrace_1730280 : CollatzResearch.WordTrace tailWord_1730280 prefixEnd_1730280 32906122476355389083059 := by
  unfold tailWord_1730280
  simp only [CollatzResearch.WordTrace]
  refine ⟨31554248085749271571246147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42072330780999028761661529 31554248085749271571246147)
  ·
    refine ⟨47331372128623907356869221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31554248085749271571246147 47331372128623907356869221)
    ·
      refine ⟨8874632274116982629412979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47331372128623907356869221 8874632274116982629412979)
      ·
        refine ⟨13311948411175473944119469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8874632274116982629412979 13311948411175473944119469)
        ·
          refine ⟨4991980654190802729044801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13311948411175473944119469 4991980654190802729044801)
          ·
            refine ⟨3743985490643102046783601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4991980654190802729044801 3743985490643102046783601)
            ·
              refine ⟨2807989117982326535087701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3743985490643102046783601 2807989117982326535087701)
              ·
                refine ⟨32906122476355389083059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2807989117982326535087701 32906122476355389083059)
                ·
                  rfl

theorem cell23_1730280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 8].length) (baseStart_1730280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730280 prefixEnd_1730280 := by exact prefixLift 1730280
  have htrace : WordTrace (prefixWord ++ tailWord_1730280) baseStart_1730280 baseEnd_1730280 := by
    simpa [prefixWord, tailWord_1730280, baseEnd_1730280] using wordTrace_append hprefix tailTrace_1730280
  have hstable : (prefixWord ++ tailWord_1730280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730280).length < 2 ^ (prefixWord ++ tailWord_1730280).sum := by decide
  have hdescent : baseEnd_1730280 < baseStart_1730280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730294 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1730294 : Nat := 118140960795 + 1730294 * 2 ^ 59
def prefixEnd_1730294 : Nat := 4983230072969 + 3 ^ 40 * 1730294 * 2
def baseEnd_1730294 : Nat := 888472495590758450467529

theorem tailTrace_1730294 : CollatzResearch.WordTrace tailWord_1730294 prefixEnd_1730294 888472495590758450467529 := by
  unfold tailWord_1730294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944312924590488970843871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42072671195631882355667957 3944312924590488970843871)
  ·
    refine ⟨5916469386885733456265807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3944312924590488970843871 5916469386885733456265807)
    ·
      refine ⟨8874704080328600184398711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5916469386885733456265807 8874704080328600184398711)
      ·
        refine ⟨13312056120492900276598067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8874704080328600184398711 13312056120492900276598067)
        ·
          refine ⟨19968084180739350414897101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13312056120492900276598067 19968084180739350414897101)
          ·
            refine ⟨7488031567777256405586413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19968084180739350414897101 7488031567777256405586413)
            ·
              refine ⟨2808011837916471152094905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7488031567777256405586413 2808011837916471152094905)
              ·
                refine ⟨2106008878437353364071179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808011837916471152094905 2106008878437353364071179)
                ·
                  refine ⟨3159013317656030046106769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106008878437353364071179 3159013317656030046106769)
                  ·
                    refine ⟨2369259988242022534580077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3159013317656030046106769 2369259988242022534580077)
                    ·
                      refine ⟨888472495590758450467529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369259988242022534580077 888472495590758450467529)
                      ·
                        rfl

theorem cell23_1730294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1730294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730294 prefixEnd_1730294 := by exact prefixLift 1730294
  have htrace : WordTrace (prefixWord ++ tailWord_1730294) baseStart_1730294 baseEnd_1730294 := by
    simpa [prefixWord, tailWord_1730294, baseEnd_1730294] using wordTrace_append hprefix tailTrace_1730294
  have hstable : (prefixWord ++ tailWord_1730294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730294).length < 2 ^ (prefixWord ++ tailWord_1730294).sum := by decide
  have hdescent : baseEnd_1730294 < baseStart_1730294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730303 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1730303 : Nat := 118140960795 + 1730303 * 2 ^ 59
def prefixEnd_1730303 : Nat := 4983230072969 + 3 ^ 40 * 1730303 * 2
def baseEnd_1730303 : Nat := 888477116916648915254987

theorem tailTrace_1730303 : CollatzResearch.WordTrace tailWord_1730303 prefixEnd_1730303 888477116916648915254987 := by
  unfold tailWord_1730303
  simp only [CollatzResearch.WordTrace]
  refine ⟨63109335050415218070579563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42072890033610145380386375 63109335050415218070579563)
  ·
    refine ⟨94664002575622827105869345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63109335050415218070579563 94664002575622827105869345)
    ·
      refine ⟨70998001931717120329402009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94664002575622827105869345 70998001931717120329402009)
      ·
        refine ⟨53248501448787840247051507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70998001931717120329402009 53248501448787840247051507)
        ·
          refine ⟨79872752173181760370577261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53248501448787840247051507 79872752173181760370577261)
          ·
            refine ⟨29952282064943160138966473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79872752173181760370577261 29952282064943160138966473)
            ·
              refine ⟨22464211548707370104224855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29952282064943160138966473 22464211548707370104224855)
              ·
                refine ⟨33696317323061055156337283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22464211548707370104224855 33696317323061055156337283)
                ·
                  refine ⟨50544475984591582734505925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33696317323061055156337283 50544475984591582734505925)
                  ·
                    refine ⟨9477089247110921762719861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50544475984591582734505925 9477089247110921762719861)
                    ·
                      refine ⟨888477116916648915254987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9477089247110921762719861 888477116916648915254987)
                      ·
                        rfl

theorem cell23_1730303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1730303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730303 prefixEnd_1730303 := by exact prefixLift 1730303
  have htrace : WordTrace (prefixWord ++ tailWord_1730303) baseStart_1730303 baseEnd_1730303 := by
    simpa [prefixWord, tailWord_1730303, baseEnd_1730303] using wordTrace_append hprefix tailTrace_1730303
  have hstable : (prefixWord ++ tailWord_1730303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730303).length < 2 ^ (prefixWord ++ tailWord_1730303).sum := by decide
  have hdescent : baseEnd_1730303 < baseStart_1730303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730311 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1730311 : Nat := 118140960795 + 1730311 * 2 ^ 59
def prefixEnd_1730311 : Nat := 4983230072969 + 3 ^ 40 * 1730311 * 2
def baseEnd_1730311 : Nat := 888481224761884883954951

theorem tailTrace_1730311 : CollatzResearch.WordTrace tailWord_1730311 prefixEnd_1730311 888481224761884883954951 := by
  unfold tailWord_1730311
  simp only [CollatzResearch.WordTrace]
  refine ⟨63109626834386235436870787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42073084556257490291247191 63109626834386235436870787)
  ·
    refine ⟨94664440251579353155306181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63109626834386235436870787 94664440251579353155306181)
    ·
      refine ⟨17749582547171128716619909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94664440251579353155306181 17749582547171128716619909)
      ·
        refine ⟨3328046727594586634366233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17749582547171128716619909 3328046727594586634366233)
        ·
          refine ⟨2496035045695939975774675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328046727594586634366233 2496035045695939975774675)
          ·
            refine ⟨3744052568543909963662013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496035045695939975774675 3744052568543909963662013)
            ·
              refine ⟨1404019713203966236373255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3744052568543909963662013 1404019713203966236373255)
              ·
                refine ⟨2106029569805949354559883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404019713203966236373255 2106029569805949354559883)
                ·
                  refine ⟨3159044354708924031839825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106029569805949354559883 3159044354708924031839825)
                  ·
                    refine ⟨2369283266031693023879869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3159044354708924031839825 2369283266031693023879869)
                    ·
                      refine ⟨888481224761884883954951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369283266031693023879869 888481224761884883954951)
                      ·
                        rfl

theorem cell23_1730311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1730311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730311 prefixEnd_1730311 := by exact prefixLift 1730311
  have htrace : WordTrace (prefixWord ++ tailWord_1730311) baseStart_1730311 baseEnd_1730311 := by
    simpa [prefixWord, tailWord_1730311, baseEnd_1730311] using wordTrace_append hprefix tailTrace_1730311
  have hstable : (prefixWord ++ tailWord_1730311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730311).length < 2 ^ (prefixWord ++ tailWord_1730311).sum := by decide
  have hdescent : baseEnd_1730311 < baseStart_1730311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730330 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1730330 : Nat := 118140960795 + 1730330 * 2 ^ 59
def prefixEnd_1730330 : Nat := 4983230072969 + 3 ^ 40 * 1730330 * 2
def baseEnd_1730330 : Nat := 888490980894320309617363

theorem tailTrace_1730330 : CollatzResearch.WordTrace tailWord_1730330 prefixEnd_1730330 888490980894320309617363 := by
  unfold tailWord_1730330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15777579955329350420453111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42073546547544934454541629 15777579955329350420453111)
  ·
    refine ⟨23666369932994025630679667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15777579955329350420453111 23666369932994025630679667)
    ·
      refine ⟨35499554899491038446019501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23666369932994025630679667 35499554899491038446019501)
      ·
        refine ⟨13312333087309139417257313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35499554899491038446019501 13312333087309139417257313)
        ·
          refine ⟨9984249815481854562942985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13312333087309139417257313 9984249815481854562942985)
          ·
            refine ⟨7488187361611390922207239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9984249815481854562942985 7488187361611390922207239)
            ·
              refine ⟨11232281042417086383310859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488187361611390922207239 11232281042417086383310859)
              ·
                refine ⟨16848421563625629574966289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11232281042417086383310859 16848421563625629574966289)
                ·
                  refine ⟨12636316172719222181224717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16848421563625629574966289 12636316172719222181224717)
                  ·
                    refine ⟨4738618564769708317959269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12636316172719222181224717 4738618564769708317959269)
                    ·
                      refine ⟨888490980894320309617363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4738618564769708317959269 888490980894320309617363)
                      ·
                        rfl

theorem cell23_1730330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1730330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730330 prefixEnd_1730330 := by exact prefixLift 1730330
  have htrace : WordTrace (prefixWord ++ tailWord_1730330) baseStart_1730330 baseEnd_1730330 := by
    simpa [prefixWord, tailWord_1730330, baseEnd_1730330] using wordTrace_append hprefix tailTrace_1730330
  have hstable : (prefixWord ++ tailWord_1730330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730330).length < 2 ^ (prefixWord ++ tailWord_1730330).sum := by decide
  have hdescent : baseEnd_1730330 < baseStart_1730330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730340 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1730340 : Nat := 118140960795 + 1730340 * 2 ^ 59
def prefixEnd_1730340 : Nat := 4983230072969 + 3 ^ 40 * 1730340 * 2
def baseEnd_1730340 : Nat := 296165371900288423497439

theorem tailTrace_1730340 : CollatzResearch.WordTrace tailWord_1730340 prefixEnd_1730340 296165371900288423497439 := by
  unfold tailWord_1730340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31555342275640586694838237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42073789700854115593117649 31555342275640586694838237)
  ·
    refine ⟨11833253353365220010564339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31555342275640586694838237 11833253353365220010564339)
    ·
      refine ⟨17749880030047830015846509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11833253353365220010564339 17749880030047830015846509)
      ·
        refine ⟨6656205011267936255942441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17749880030047830015846509 6656205011267936255942441)
        ·
          refine ⟨4992153758450952191956831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6656205011267936255942441 4992153758450952191956831)
          ·
            refine ⟨7488230637676428287935247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992153758450952191956831 7488230637676428287935247)
            ·
              refine ⟨11232345956514642431902871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488230637676428287935247 11232345956514642431902871)
              ·
                refine ⟨16848518934771963647854307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11232345956514642431902871 16848518934771963647854307)
                ·
                  refine ⟨25272778402157945471781461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16848518934771963647854307 25272778402157945471781461)
                  ·
                    refine ⟨296165371900288423497439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25272778402157945471781461 296165371900288423497439)
                    ·
                      rfl

theorem cell23_1730340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1730340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730340 prefixEnd_1730340 := by exact prefixLift 1730340
  have htrace : WordTrace (prefixWord ++ tailWord_1730340) baseStart_1730340 baseEnd_1730340 := by
    simpa [prefixWord, tailWord_1730340, baseEnd_1730340] using wordTrace_append hprefix tailTrace_1730340
  have hstable : (prefixWord ++ tailWord_1730340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730340).length < 2 ^ (prefixWord ++ tailWord_1730340).sum := by decide
  have hdescent : baseEnd_1730340 < baseStart_1730340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730374 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1730374 : Nat := 118140960795 + 1730374 * 2 ^ 59
def prefixEnd_1730374 : Nat := 4983230072969 + 3 ^ 40 * 1730374 * 2
def baseEnd_1730374 : Nat := 296171191347706045822387

theorem tailTrace_1730374 : CollatzResearch.WordTrace tailWord_1730374 prefixEnd_1730374 296171191347706045822387 := by
  unfold tailWord_1730374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972247644786187412387943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42074616422105331464276117 1972247644786187412387943)
  ·
    refine ⟨2958371467179281118581915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972247644786187412387943 2958371467179281118581915)
    ·
      refine ⟨4437557200768921677872873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958371467179281118581915 4437557200768921677872873)
      ·
        refine ⟨3328167900576691258404655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4437557200768921677872873 3328167900576691258404655)
        ·
          refine ⟨4992251850865036887606983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328167900576691258404655 4992251850865036887606983)
          ·
            refine ⟨7488377776297555331410475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992251850865036887606983 7488377776297555331410475)
            ·
              refine ⟨11232566664446332997115713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488377776297555331410475 11232566664446332997115713)
              ·
                refine ⟨8424424998334749747836785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11232566664446332997115713 8424424998334749747836785)
                ·
                  refine ⟨6318318748751062310877589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8424424998334749747836785 6318318748751062310877589)
                  ·
                    refine ⟨296171191347706045822387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6318318748751062310877589 296171191347706045822387)
                    ·
                      rfl

theorem cell23_1730374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1730374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730374 prefixEnd_1730374 := by exact prefixLift 1730374
  have htrace : WordTrace (prefixWord ++ tailWord_1730374) baseStart_1730374 baseEnd_1730374 := by
    simpa [prefixWord, tailWord_1730374, baseEnd_1730374] using wordTrace_append hprefix tailTrace_1730374
  have hstable : (prefixWord ++ tailWord_1730374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730374).length < 2 ^ (prefixWord ++ tailWord_1730374).sum := by decide
  have hdescent : baseEnd_1730374 < baseStart_1730374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730400 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 1, 7]
def baseStart_1730400 : Nat := 118140960795 + 1730400 * 2 ^ 59
def prefixEnd_1730400 : Nat := 4983230072969 + 3 ^ 40 * 1730400 * 2
def baseEnd_1730400 : Nat := 296175641513378345247347

theorem tailTrace_1730400 : CollatzResearch.WordTrace tailWord_1730400 prefixEnd_1730400 296175641513378345247347 := by
  unfold tailWord_1730400
  simp only [CollatzResearch.WordTrace]
  refine ⟨31556436465531901818430327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42075248620709202424573769 31556436465531901818430327)
  ·
    refine ⟨47334654698297852727645491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31556436465531901818430327 47334654698297852727645491)
    ·
      refine ⟨71001982047446779091468237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47334654698297852727645491 71001982047446779091468237)
      ·
        refine ⟨26625743267792542159300589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71001982047446779091468237 26625743267792542159300589)
        ·
          refine ⟨9984653725422203309737721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26625743267792542159300589 9984653725422203309737721)
          ·
            refine ⟨7488490294066652482303291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9984653725422203309737721 7488490294066652482303291)
            ·
              refine ⟨11232735441099978723454937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488490294066652482303291 11232735441099978723454937)
              ·
                refine ⟨8424551580824984042591203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11232735441099978723454937 8424551580824984042591203)
                ·
                  refine ⟨12636827371237476063886805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8424551580824984042591203 12636827371237476063886805)
                  ·
                    refine ⟨296175641513378345247347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12636827371237476063886805 296175641513378345247347)
                    ·
                      rfl

theorem cell23_1730400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_1730400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730400 prefixEnd_1730400 := by exact prefixLift 1730400
  have htrace : WordTrace (prefixWord ++ tailWord_1730400) baseStart_1730400 baseEnd_1730400 := by
    simpa [prefixWord, tailWord_1730400, baseEnd_1730400] using wordTrace_append hprefix tailTrace_1730400
  have hstable : (prefixWord ++ tailWord_1730400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730400).length < 2 ^ (prefixWord ++ tailWord_1730400).sum := by decide
  have hdescent : baseEnd_1730400 < baseStart_1730400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730437 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_1730437 : Nat := 118140960795 + 1730437 * 2 ^ 59
def prefixEnd_1730437 : Nat := 4983230072969 + 3 ^ 40 * 1730437 * 2
def baseEnd_1730437 : Nat := 888545923324351390979371

theorem tailTrace_1730437 : CollatzResearch.WordTrace tailWord_1730437 prefixEnd_1730437 888545923324351390979371 := by
  unfold tailWord_1730437
  simp only [CollatzResearch.WordTrace]
  refine ⟨63114222431929758955957565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42076148287953172637305043 63114222431929758955957565)
  ·
    refine ⟨23667833411973659608484087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63114222431929758955957565 23667833411973659608484087)
    ·
      refine ⟨35501750117960489412726131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23667833411973659608484087 35501750117960489412726131)
      ·
        refine ⟨53252625176940734119089197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35501750117960489412726131 53252625176940734119089197)
        ·
          refine ⟨19969734441352775294658449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53252625176940734119089197 19969734441352775294658449)
          ·
            refine ⟨14977300831014581470993837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19969734441352775294658449 14977300831014581470993837)
            ·
              refine ⟨5616487811630468051622689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14977300831014581470993837 5616487811630468051622689)
              ·
                refine ⟨4212365858722851038717017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616487811630468051622689 4212365858722851038717017)
                ·
                  refine ⟨3159274394042138279037763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4212365858722851038717017 3159274394042138279037763)
                  ·
                    refine ⟨4738911591063207418556645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3159274394042138279037763 4738911591063207418556645)
                    ·
                      refine ⟨888545923324351390979371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4738911591063207418556645 888545923324351390979371)
                      ·
                        rfl

theorem cell23_1730437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_1730437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730437 prefixEnd_1730437 := by exact prefixLift 1730437
  have htrace : WordTrace (prefixWord ++ tailWord_1730437) baseStart_1730437 baseEnd_1730437 := by
    simpa [prefixWord, tailWord_1730437, baseEnd_1730437] using wordTrace_append hprefix tailTrace_1730437
  have hstable : (prefixWord ++ tailWord_1730437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730437).length < 2 ^ (prefixWord ++ tailWord_1730437).sum := by decide
  have hdescent : baseEnd_1730437 < baseStart_1730437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730494 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1730494 : Nat := 118140960795 + 1730494 * 2 ^ 59
def prefixEnd_1730494 : Nat := 4983230072969 + 3 ^ 40 * 1730494 * 2
def baseEnd_1730494 : Nat := 98730576857961963107401

theorem tailTrace_1730494 : CollatzResearch.WordTrace tailWord_1730494 prefixEnd_1730494 98730576857961963107401 := by
  unfold tailWord_1730494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889537674090407211347817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42077534261815505127188357 7889537674090407211347817)
  ·
    refine ⟨5917153255567805408510863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7889537674090407211347817 5917153255567805408510863)
    ·
      refine ⟨8875729883351708112766295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5917153255567805408510863 8875729883351708112766295)
      ·
        refine ⟨13313594825027562169149443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8875729883351708112766295 13313594825027562169149443)
        ·
          refine ⟨19970392237541343253724165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13313594825027562169149443 19970392237541343253724165)
          ·
            refine ⟨3744448544539001860073281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19970392237541343253724165 3744448544539001860073281)
            ·
              refine ⟨2808336408404251395054961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3744448544539001860073281 2808336408404251395054961)
              ·
                refine ⟨2106252306303188546291221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808336408404251395054961 2106252306303188546291221)
                ·
                  refine ⟨98730576857961963107401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2106252306303188546291221 98730576857961963107401)
                  ·
                    rfl

theorem cell23_1730494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1730494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730494 prefixEnd_1730494 := by exact prefixLift 1730494
  have htrace : WordTrace (prefixWord ++ tailWord_1730494) baseStart_1730494 baseEnd_1730494 := by
    simpa [prefixWord, tailWord_1730494, baseEnd_1730494] using wordTrace_append hprefix tailTrace_1730494
  have hstable : (prefixWord ++ tailWord_1730494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730494).length < 2 ^ (prefixWord ++ tailWord_1730494).sum := by decide
  have hdescent : baseEnd_1730494 < baseStart_1730494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730521 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 3]
def baseStart_1730521 : Nat := 118140960795 + 1730521 * 2 ^ 59
def prefixEnd_1730521 : Nat := 4983230072969 + 3 ^ 40 * 1730521 * 2
def baseEnd_1730521 : Nat := 888589055699329062328985

theorem tailTrace_1730521 : CollatzResearch.WordTrace tailWord_1730521 prefixEnd_1730521 888589055699329062328985 := by
  unfold tailWord_1730521
  simp only [CollatzResearch.WordTrace]
  refine ⟨63117286163625441302015417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42078190775750294201343611 63117286163625441302015417)
  ·
    refine ⟨47337964622719080976511563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63117286163625441302015417 47337964622719080976511563)
    ·
      refine ⟨71006946934078621464767345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47337964622719080976511563 71006946934078621464767345)
      ·
        refine ⟨53255210200558966098575509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71006946934078621464767345 53255210200558966098575509)
        ·
          refine ⟨2496337978151201535870727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53255210200558966098575509 2496337978151201535870727)
          ·
            refine ⟨3744506967226802303806091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496337978151201535870727 3744506967226802303806091)
            ·
              refine ⟨5616760450840203455709137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744506967226802303806091 5616760450840203455709137)
              ·
                refine ⟨4212570338130152591781853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616760450840203455709137 4212570338130152591781853)
                ·
                  refine ⟨1579713876798807221918195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4212570338130152591781853 1579713876798807221918195)
                  ·
                    refine ⟨2369570815198210832877293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1579713876798807221918195 2369570815198210832877293)
                    ·
                      refine ⟨888589055699329062328985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369570815198210832877293 888589055699329062328985)
                      ·
                        rfl

theorem cell23_1730521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_1730521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730521 prefixEnd_1730521 := by exact prefixLift 1730521
  have htrace : WordTrace (prefixWord ++ tailWord_1730521) baseStart_1730521 baseEnd_1730521 := by
    simpa [prefixWord, tailWord_1730521, baseEnd_1730521] using wordTrace_append hprefix tailTrace_1730521
  have hstable : (prefixWord ++ tailWord_1730521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730521).length < 2 ^ (prefixWord ++ tailWord_1730521).sum := by decide
  have hdescent : baseEnd_1730521 < baseStart_1730521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730531 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 2, 3, 2]
def baseStart_1730531 : Nat := 118140960795 + 1730531 * 2 ^ 59
def prefixEnd_1730531 : Nat := 4983230072969 + 3 ^ 40 * 1730531 * 2
def baseEnd_1730531 : Nat := 888594190505874023203939

theorem tailTrace_1730531 : CollatzResearch.WordTrace tailWord_1730531 prefixEnd_1730531 888594190505874023203939 := by
  unfold tailWord_1730531
  simp only [CollatzResearch.WordTrace]
  refine ⟨63117650893589213009879447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42078433929059475339919631 63117650893589213009879447)
  ·
    refine ⟨94676476340383819514819171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63117650893589213009879447 94676476340383819514819171)
    ·
      refine ⟨142014714510575729272228757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94676476340383819514819171 142014714510575729272228757)
      ·
        refine ⟨6656939742683237309635723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142014714510575729272228757 6656939742683237309635723)
        ·
          refine ⟨9985409614024855964453585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656939742683237309635723 9985409614024855964453585)
          ·
            refine ⟨7489057210518641973340189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9985409614024855964453585 7489057210518641973340189)
            ·
              refine ⟨2808396453944490740002571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7489057210518641973340189 2808396453944490740002571)
              ·
                refine ⟨4212594680916736110003857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808396453944490740002571 4212594680916736110003857)
                ·
                  refine ⟨3159446010687552082502893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4212594680916736110003857 3159446010687552082502893)
                  ·
                    refine ⟨1184792254007832030938585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159446010687552082502893 1184792254007832030938585)
                    ·
                      refine ⟨888594190505874023203939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184792254007832030938585 888594190505874023203939)
                      ·
                        rfl

theorem cell23_1730531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_1730531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730531 prefixEnd_1730531 := by exact prefixLift 1730531
  have htrace : WordTrace (prefixWord ++ tailWord_1730531) baseStart_1730531 baseEnd_1730531 := by
    simpa [prefixWord, tailWord_1730531, baseEnd_1730531] using wordTrace_append hprefix tailTrace_1730531
  have hstable : (prefixWord ++ tailWord_1730531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730531).length < 2 ^ (prefixWord ++ tailWord_1730531).sum := by decide
  have hdescent : baseEnd_1730531 < baseStart_1730531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730538 : List Nat := [3, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_1730538 : Nat := 118140960795 + 1730538 * 2 ^ 59
def prefixEnd_1730538 : Nat := 4983230072969 + 3 ^ 40 * 1730538 * 2
def baseEnd_1730538 : Nat := 888597784870455495816407

theorem tailTrace_1730538 : CollatzResearch.WordTrace tailWord_1730538 prefixEnd_1730538 888597784870455495816407 := by
  unfold tailWord_1730538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779476551140963301346067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42078604136375902136922845 15779476551140963301346067)
  ·
    refine ⟨23669214826711444952019101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15779476551140963301346067 23669214826711444952019101)
    ·
      refine ⟨8875955560016791857007163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23669214826711444952019101 8875955560016791857007163)
      ·
        refine ⟨13313933340025187785510745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8875955560016791857007163 13313933340025187785510745)
        ·
          refine ⟨9985450005018890839133059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13313933340025187785510745 9985450005018890839133059)
          ·
            refine ⟨14978175007528336258699589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9985450005018890839133059 14978175007528336258699589)
            ·
              refine ⟨2808407813911563048506173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14978175007528336258699589 2808407813911563048506173)
              ·
                refine ⟨1053152930216836143189815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2808407813911563048506173 1053152930216836143189815)
                ·
                  refine ⟨1579729395325254214784723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053152930216836143189815 1579729395325254214784723)
                  ·
                    refine ⟨2369594092987881322177085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1579729395325254214784723 2369594092987881322177085)
                    ·
                      refine ⟨888597784870455495816407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369594092987881322177085 888597784870455495816407)
                      ·
                        rfl

theorem cell23_1730538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_1730538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730538 prefixEnd_1730538 := by exact prefixLift 1730538
  have htrace : WordTrace (prefixWord ++ tailWord_1730538) baseStart_1730538 baseEnd_1730538 := by
    simpa [prefixWord, tailWord_1730538, baseEnd_1730538] using wordTrace_append hprefix tailTrace_1730538
  have hstable : (prefixWord ++ tailWord_1730538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730538).length < 2 ^ (prefixWord ++ tailWord_1730538).sum := by decide
  have hdescent : baseEnd_1730538 < baseStart_1730538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730557 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1730557 : Nat := 118140960795 + 1730557 * 2 ^ 59
def prefixEnd_1730557 : Nat := 4983230072969 + 3 ^ 40 * 1730557 * 2
def baseEnd_1730557 : Nat := 888607541002890921478819

theorem tailTrace_1730557 : CollatzResearch.WordTrace tailWord_1730557 prefixEnd_1730557 888607541002890921478819 := by
  unfold tailWord_1730557
  simp only [CollatzResearch.WordTrace]
  refine ⟨63118599191495019450325925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42079066127663346300217283 63118599191495019450325925)
  ·
    refine ⟨11834737348405316146936111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63118599191495019450325925 11834737348405316146936111)
    ·
      refine ⟨17752106022607974220404167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834737348405316146936111 17752106022607974220404167)
      ·
        refine ⟨26628159033911961330606251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17752106022607974220404167 26628159033911961330606251)
        ·
          refine ⟨39942238550867941995909377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628159033911961330606251 39942238550867941995909377)
          ·
            refine ⟨29956678913150956496932033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39942238550867941995909377 29956678913150956496932033)
            ·
              refine ⟨22467509184863217372699025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29956678913150956496932033 22467509184863217372699025)
              ·
                refine ⟨16850631888647413029524269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22467509184863217372699025 16850631888647413029524269)
                ·
                  refine ⟨6318986958242779886071601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16850631888647413029524269 6318986958242779886071601)
                  ·
                    refine ⟨4739240218682084914553701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6318986958242779886071601 4739240218682084914553701)
                    ·
                      refine ⟨888607541002890921478819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4739240218682084914553701 888607541002890921478819)
                      ·
                        rfl

theorem cell23_1730557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1730557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730557 prefixEnd_1730557 := by exact prefixLift 1730557
  have htrace : WordTrace (prefixWord ++ tailWord_1730557) baseStart_1730557 baseEnd_1730557 := by
    simpa [prefixWord, tailWord_1730557, baseEnd_1730557] using wordTrace_append hprefix tailTrace_1730557
  have hstable : (prefixWord ++ tailWord_1730557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730557).length < 2 ^ (prefixWord ++ tailWord_1730557).sum := by decide
  have hdescent : baseEnd_1730557 < baseStart_1730557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730571 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 2, 4]
def baseStart_1730571 : Nat := 118140960795 + 1730571 * 2 ^ 59
def prefixEnd_1730571 : Nat := 4983230072969 + 3 ^ 40 * 1730571 * 2
def baseEnd_1730571 : Nat := 296204909910684622234585

theorem tailTrace_1730571 : CollatzResearch.WordTrace tailWord_1730571 prefixEnd_1730571 296204909910684622234585 := by
  unfold tailWord_1730571
  simp only [CollatzResearch.WordTrace]
  refine ⟨63119109813444299841335567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42079406542296199894223711 63119109813444299841335567)
  ·
    refine ⟨94678664720166449762003351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63119109813444299841335567 94678664720166449762003351)
    ·
      refine ⟨142017997080249674643005027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94678664720166449762003351 142017997080249674643005027)
      ·
        refine ⟨213026995620374511964507541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142017997080249674643005027 213026995620374511964507541)
        ·
          refine ⟨9985640419705055248336291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213026995620374511964507541 9985640419705055248336291)
          ·
            refine ⟨14978460629557582872504437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9985640419705055248336291 14978460629557582872504437)
            ·
              refine ⟨1404230684021023394297291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14978460629557582872504437 1404230684021023394297291)
              ·
                refine ⟨2106346026031535091445937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404230684021023394297291 2106346026031535091445937)
                ·
                  refine ⟨1579759519523651318584453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106346026031535091445937 1579759519523651318584453)
                  ·
                    refine ⟨296204909910684622234585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579759519523651318584453 296204909910684622234585)
                    ·
                      rfl

theorem cell23_1730571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 4].length) (baseStart_1730571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730571 prefixEnd_1730571 := by exact prefixLift 1730571
  have htrace : WordTrace (prefixWord ++ tailWord_1730571) baseStart_1730571 baseEnd_1730571 := by
    simpa [prefixWord, tailWord_1730571, baseEnd_1730571] using wordTrace_append hprefix tailTrace_1730571
  have hstable : (prefixWord ++ tailWord_1730571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730571).length < 2 ^ (prefixWord ++ tailWord_1730571).sum := by decide
  have hdescent : baseEnd_1730571 < baseStart_1730571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730594 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_1730594 : Nat := 118140960795 + 1730594 * 2 ^ 59
def prefixEnd_1730594 : Nat := 4983230072969 + 3 ^ 40 * 1730594 * 2
def baseEnd_1730594 : Nat := 888626539787107276716149

theorem tailTrace_1730594 : CollatzResearch.WordTrace tailWord_1730594 prefixEnd_1730594 888626539787107276716149 := by
  unfold tailWord_1730594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779987173090243692355709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42079965794907316512948557 15779987173090243692355709)
  ·
    refine ⟨5917495189908841384633391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15779987173090243692355709 5917495189908841384633391)
    ·
      refine ⟨8876242784863262076950087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5917495189908841384633391 8876242784863262076950087)
      ·
        refine ⟨13314364177294893115425131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8876242784863262076950087 13314364177294893115425131)
        ·
          refine ⟨19971546265942339673137697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13314364177294893115425131 19971546265942339673137697)
          ·
            refine ⟨14978659699456754754853273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19971546265942339673137697 14978659699456754754853273)
            ·
              refine ⟨11233994774592566066139955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14978659699456754754853273 11233994774592566066139955)
              ·
                refine ⟨16850992161888849099209933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11233994774592566066139955 16850992161888849099209933)
                ·
                  refine ⟨6319122060708318412203725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16850992161888849099209933 6319122060708318412203725)
                  ·
                    refine ⟨2369670772765619404576397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6319122060708318412203725 2369670772765619404576397)
                    ·
                      refine ⟨888626539787107276716149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369670772765619404576397 888626539787107276716149)
                      ·
                        rfl

theorem cell23_1730594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_1730594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730594 prefixEnd_1730594 := by exact prefixLift 1730594
  have htrace : WordTrace (prefixWord ++ tailWord_1730594) baseStart_1730594 baseEnd_1730594 := by
    simpa [prefixWord, tailWord_1730594, baseEnd_1730594] using wordTrace_append hprefix tailTrace_1730594
  have hstable : (prefixWord ++ tailWord_1730594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730594).length < 2 ^ (prefixWord ++ tailWord_1730594).sum := by decide
  have hdescent : baseEnd_1730594 < baseStart_1730594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730612 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1730612 : Nat := 118140960795 + 1730612 * 2 ^ 59
def prefixEnd_1730612 : Nat := 4983230072969 + 3 ^ 40 * 1730612 * 2
def baseEnd_1730612 : Nat := 888635782438888206291067

theorem tailTrace_1730612 : CollatzResearch.WordTrace tailWord_1730612 prefixEnd_1730612 888635782438888206291067 := by
  unfold tailWord_1730612
  simp only [CollatzResearch.WordTrace]
  refine ⟨31560302603147881921789045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42080403470863842562385393 31560302603147881921789045)
  ·
    refine ⟨2958778369045113930167723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31560302603147881921789045 2958778369045113930167723)
    ·
      refine ⟨4438167553567670895251585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958778369045113930167723 4438167553567670895251585)
      ·
        refine ⟨3328625665175753171438689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438167553567670895251585 3328625665175753171438689)
        ·
          refine ⟨2496469248881814878579017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328625665175753171438689 2496469248881814878579017)
          ·
            refine ⟨1872351936661361158934263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496469248881814878579017 1872351936661361158934263)
            ·
              refine ⟨2808527904992041738401395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872351936661361158934263 2808527904992041738401395)
              ·
                refine ⟨4212791857488062607602093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808527904992041738401395 4212791857488062607602093)
                ·
                  refine ⟨1579796946558023477850785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4212791857488062607602093 1579796946558023477850785)
                  ·
                    refine ⟨1184847709918517608388089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1579796946558023477850785 1184847709918517608388089)
                    ·
                      refine ⟨888635782438888206291067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184847709918517608388089 888635782438888206291067)
                      ·
                        rfl

theorem cell23_1730612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1730612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730612 prefixEnd_1730612 := by exact prefixLift 1730612
  have htrace : WordTrace (prefixWord ++ tailWord_1730612) baseStart_1730612 baseEnd_1730612 := by
    simpa [prefixWord, tailWord_1730612, baseEnd_1730612] using wordTrace_append hprefix tailTrace_1730612
  have hstable : (prefixWord ++ tailWord_1730612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730612).length < 2 ^ (prefixWord ++ tailWord_1730612).sum := by decide
  have hdescent : baseEnd_1730612 < baseStart_1730612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730614 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1730614 : Nat := 118140960795 + 1730614 * 2 ^ 59
def prefixEnd_1730614 : Nat := 4983230072969 + 3 ^ 40 * 1730614 * 2
def baseEnd_1730614 : Nat := 296212269800065732822019

theorem tailTrace_1730614 : CollatzResearch.WordTrace tailWord_1730614 prefixEnd_1730614 296212269800065732822019 := by
  unfold tailWord_1730614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945042384518032386571931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42080452101525678790100597 3945042384518032386571931)
  ·
    refine ⟨5917563576777048579857897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3945042384518032386571931 5917563576777048579857897)
    ·
      refine ⟨4438172682582786434893423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5917563576777048579857897 4438172682582786434893423)
      ·
        refine ⟨6657259023874179652340135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438172682582786434893423 6657259023874179652340135)
        ·
          refine ⟨9985888535811269478510203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657259023874179652340135 9985888535811269478510203)
          ·
            refine ⟨14978832803716904217765305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9985888535811269478510203 14978832803716904217765305)
            ·
              refine ⟨11234124602787678163323979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14978832803716904217765305 11234124602787678163323979)
              ·
                refine ⟨16851186904181517244985969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11234124602787678163323979 16851186904181517244985969)
                ·
                  refine ⟨12638390178136137933739477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16851186904181517244985969 12638390178136137933739477)
                  ·
                    refine ⟨296212269800065732822019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12638390178136137933739477 296212269800065732822019)
                    ·
                      rfl

theorem cell23_1730614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1730614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730614 prefixEnd_1730614 := by exact prefixLift 1730614
  have htrace : WordTrace (prefixWord ++ tailWord_1730614) baseStart_1730614 baseEnd_1730614 := by
    simpa [prefixWord, tailWord_1730614, baseEnd_1730614] using wordTrace_append hprefix tailTrace_1730614
  have hstable : (prefixWord ++ tailWord_1730614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730614).length < 2 ^ (prefixWord ++ tailWord_1730614).sum := by decide
  have hdescent : baseEnd_1730614 < baseStart_1730614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730621 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1730621 : Nat := 118140960795 + 1730621 * 2 ^ 59
def prefixEnd_1730621 : Nat := 4983230072969 + 3 ^ 40 * 1730621 * 2
def baseEnd_1730621 : Nat := 888640403764778671078525

theorem tailTrace_1730621 : CollatzResearch.WordTrace tailWord_1730621 prefixEnd_1730621 888640403764778671078525 := by
  unfold tailWord_1730621
  simp only [CollatzResearch.WordTrace]
  refine ⟨63120933463263158380655717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42080622308842105587103811 63120933463263158380655717)
  ·
    refine ⟨11835175024361842196372947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63120933463263158380655717 11835175024361842196372947)
    ·
      refine ⟨17752762536542763294559421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11835175024361842196372947 17752762536542763294559421)
      ·
        refine ⟨6657285951203536235459783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17752762536542763294559421 6657285951203536235459783)
        ·
          refine ⟨9985928926805304353189675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657285951203536235459783 9985928926805304353189675)
          ·
            refine ⟨14978893390207956529784513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9985928926805304353189675 14978893390207956529784513)
            ·
              refine ⟨11234170042655967397338385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14978893390207956529784513 11234170042655967397338385)
              ·
                refine ⟨8425627531991975548003789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11234170042655967397338385 8425627531991975548003789)
                ·
                  refine ⟨3159610324496990830501421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8425627531991975548003789 3159610324496990830501421)
                  ·
                    refine ⟨1184853871686371561438033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159610324496990830501421 1184853871686371561438033)
                    ·
                      refine ⟨888640403764778671078525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184853871686371561438033 888640403764778671078525)
                      ·
                        rfl

theorem cell23_1730621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1730621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730621 prefixEnd_1730621 := by exact prefixLift 1730621
  have htrace : WordTrace (prefixWord ++ tailWord_1730621) baseStart_1730621 baseEnd_1730621 := by
    simpa [prefixWord, tailWord_1730621, baseEnd_1730621] using wordTrace_append hprefix tailTrace_1730621
  have hstable : (prefixWord ++ tailWord_1730621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730621).length < 2 ^ (prefixWord ++ tailWord_1730621).sum := by decide
  have hdescent : baseEnd_1730621 < baseStart_1730621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730622 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1730622 : Nat := 118140960795 + 1730622 * 2 ^ 59
def prefixEnd_1730622 : Nat := 4983230072969 + 3 ^ 40 * 1730622 * 2
def baseEnd_1730622 : Nat := 296213639081811055722007

theorem tailTrace_1730622 : CollatzResearch.WordTrace tailWord_1730622 prefixEnd_1730622 296213639081811055722007 := by
  unfold tailWord_1730622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7890121242032441943930265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42080646624173023700961413 7890121242032441943930265)
  ·
    refine ⟨5917590931524331457947699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7890121242032441943930265 5917590931524331457947699)
    ·
      refine ⟨8876386397286497186921549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5917590931524331457947699 8876386397286497186921549)
      ·
        refine ⟨3328644898982436445095581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8876386397286497186921549 3328644898982436445095581)
        ·
          refine ⟨1248241837118413666910843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3328644898982436445095581 1248241837118413666910843)
          ·
            refine ⟨1872362755677620500366265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248241837118413666910843 1872362755677620500366265)
            ·
              refine ⟨1404272066758215375274699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872362755677620500366265 1404272066758215375274699)
              ·
                refine ⟨2106408100137323062912049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404272066758215375274699 2106408100137323062912049)
                ·
                  refine ⟨1579806075102992297184037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106408100137323062912049 1579806075102992297184037)
                  ·
                    refine ⟨296213639081811055722007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579806075102992297184037 296213639081811055722007)
                    ·
                      rfl

theorem cell23_1730622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1730622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730622 prefixEnd_1730622 := by exact prefixLift 1730622
  have htrace : WordTrace (prefixWord ++ tailWord_1730622) baseStart_1730622 baseEnd_1730622 := by
    simpa [prefixWord, tailWord_1730622, baseEnd_1730622] using wordTrace_append hprefix tailTrace_1730622
  have hstable : (prefixWord ++ tailWord_1730622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730622).length < 2 ^ (prefixWord ++ tailWord_1730622).sum := by decide
  have hdescent : baseEnd_1730622 < baseStart_1730622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730638 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_1730638 : Nat := 118140960795 + 1730638 * 2 ^ 59
def prefixEnd_1730638 : Nat := 4983230072969 + 3 ^ 40 * 1730638 * 2
def baseEnd_1730638 : Nat := 888649132935905104565947

theorem tailTrace_1730638 : CollatzResearch.WordTrace tailWord_1730638 prefixEnd_1730638 888649132935905104565947 := by
  unfold tailWord_1730638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7890194188025196285503071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42081035669467713522683045 7890194188025196285503071)
  ·
    refine ⟨11835291282037794428254607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7890194188025196285503071 11835291282037794428254607)
    ·
      refine ⟨17752936923056691642381911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11835291282037794428254607 17752936923056691642381911)
      ·
        refine ⟨26629405384585037463572867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17752936923056691642381911 26629405384585037463572867)
        ·
          refine ⟨39944108076877556195359301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26629405384585037463572867 39944108076877556195359301)
          ·
            refine ⟨7489520264414541786629869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39944108076877556195359301 7489520264414541786629869)
            ·
              refine ⟨2808570099155453169986201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7489520264414541786629869 2808570099155453169986201)
              ·
                refine ⟨2106427574366589877489651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808570099155453169986201 2106427574366589877489651)
                ·
                  refine ⟨3159641361549884816234477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106427574366589877489651 3159641361549884816234477)
                  ·
                    refine ⟨1184865510581206806087929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159641361549884816234477 1184865510581206806087929)
                    ·
                      refine ⟨888649132935905104565947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184865510581206806087929 888649132935905104565947)
                      ·
                        rfl

theorem cell23_1730638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_1730638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730638 prefixEnd_1730638 := by exact prefixLift 1730638
  have htrace : WordTrace (prefixWord ++ tailWord_1730638) baseStart_1730638 baseEnd_1730638 := by
    simpa [prefixWord, tailWord_1730638, baseEnd_1730638] using wordTrace_append hprefix tailTrace_1730638
  have hstable : (prefixWord ++ tailWord_1730638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730638).length < 2 ^ (prefixWord ++ tailWord_1730638).sum := by decide
  have hdescent : baseEnd_1730638 < baseStart_1730638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730668 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 2, 2, 2]
def baseStart_1730668 : Nat := 118140960795 + 1730668 * 2 ^ 59
def prefixEnd_1730668 : Nat := 4983230072969 + 3 ^ 40 * 1730668 * 2
def baseEnd_1730668 : Nat := 888664537355539987190809

theorem tailTrace_1730668 : CollatzResearch.WordTrace tailWord_1730668 prefixEnd_1730668 888664537355539987190809 := by
  unfold tailWord_1730668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31561323847046442703808329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42081765129395256938411105 31561323847046442703808329)
  ·
    refine ⟨23670992885284832027856247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31561323847046442703808329 23670992885284832027856247)
    ·
      refine ⟨35506489327927248041784371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23670992885284832027856247 35506489327927248041784371)
      ·
        refine ⟨53259733991890872062676557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35506489327927248041784371 53259733991890872062676557)
        ·
          refine ⟨19972400246959077023503709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53259733991890872062676557 19972400246959077023503709)
          ·
            refine ⟨7489650092609653883813891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19972400246959077023503709 7489650092609653883813891)
            ·
              refine ⟨11234475138914480825720837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489650092609653883813891 11234475138914480825720837)
              ·
                refine ⟨2106464088546465154822657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11234475138914480825720837 2106464088546465154822657)
                ·
                  refine ⟨1579848066409848866116993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106464088546465154822657 1579848066409848866116993)
                  ·
                    refine ⟨1184886049807386649587745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1579848066409848866116993 1184886049807386649587745)
                    ·
                      refine ⟨888664537355539987190809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184886049807386649587745 888664537355539987190809)
                      ·
                        rfl

theorem cell23_1730668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_1730668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730668 prefixEnd_1730668 := by exact prefixLift 1730668
  have htrace : WordTrace (prefixWord ++ tailWord_1730668) baseStart_1730668 baseEnd_1730668 := by
    simpa [prefixWord, tailWord_1730668, baseEnd_1730668] using wordTrace_append hprefix tailTrace_1730668
  have hstable : (prefixWord ++ tailWord_1730668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730668).length < 2 ^ (prefixWord ++ tailWord_1730668).sum := by decide
  have hdescent : baseEnd_1730668 < baseStart_1730668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730684 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_1730684 : Nat := 118140960795 + 1730684 * 2 ^ 59
def prefixEnd_1730684 : Nat := 4983230072969 + 3 ^ 40 * 1730684 * 2
def baseEnd_1730684 : Nat := 888672753046011924590735

theorem tailTrace_1730684 : CollatzResearch.WordTrace tailWord_1730684 prefixEnd_1730684 888672753046011924590735 := by
  unfold tailWord_1730684
  simp only [CollatzResearch.WordTrace]
  refine ⟨31561615631017460070099553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42082154174689946760132737 31561615631017460070099553)
  ·
    refine ⟨23671211723263095052574665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31561615631017460070099553 23671211723263095052574665)
    ·
      refine ⟨17753408792447321289430999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23671211723263095052574665 17753408792447321289430999)
      ·
        refine ⟨26630113188670981934146499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17753408792447321289430999 26630113188670981934146499)
        ·
          refine ⟨39945169783006472901219749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26630113188670981934146499 39945169783006472901219749)
          ·
            refine ⟨7489719334313713668978703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39945169783006472901219749 7489719334313713668978703)
            ·
              refine ⟨11234579001470570503468055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489719334313713668978703 11234579001470570503468055)
              ·
                refine ⟨16851868502205855755202083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11234579001470570503468055 16851868502205855755202083)
                ·
                  refine ⟨25277802753308783632803125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16851868502205855755202083 25277802753308783632803125)
                  ·
                    refine ⟨2369794008122698465575293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25277802753308783632803125 2369794008122698465575293)
                    ·
                      refine ⟨888672753046011924590735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369794008122698465575293 888672753046011924590735)
                      ·
                        rfl

theorem cell23_1730684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_1730684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730684 prefixEnd_1730684 := by exact prefixLift 1730684
  have htrace : WordTrace (prefixWord ++ tailWord_1730684) baseStart_1730684 baseEnd_1730684 := by
    simpa [prefixWord, tailWord_1730684, baseEnd_1730684] using wordTrace_append hprefix tailTrace_1730684
  have hstable : (prefixWord ++ tailWord_1730684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730684).length < 2 ^ (prefixWord ++ tailWord_1730684).sum := by decide
  have hdescent : baseEnd_1730684 < baseStart_1730684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730744 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_1730744 : Nat := 118140960795 + 1730744 * 2 ^ 59
def prefixEnd_1730744 : Nat := 4983230072969 + 3 ^ 40 * 1730744 * 2
def baseEnd_1730744 : Nat := 888703561885281689840459

theorem tailTrace_1730744 : CollatzResearch.WordTrace tailWord_1730744 prefixEnd_1730744 888703561885281689840459 := by
  unfold tailWord_1730744
  simp only [CollatzResearch.WordTrace]
  refine ⟨31562709820908775193691643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42083613094545033591588857 31562709820908775193691643)
  ·
    refine ⟨47344064731363162790537465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31562709820908775193691643 47344064731363162790537465)
    ·
      refine ⟨35508048548522372092903099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47344064731363162790537465 35508048548522372092903099)
      ·
        refine ⟨53262072822783558139354649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35508048548522372092903099 53262072822783558139354649)
        ·
          refine ⟨39946554617087668604515987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53262072822783558139354649 39946554617087668604515987)
          ·
            refine ⟨59919831925631502906773981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39946554617087668604515987 59919831925631502906773981)
            ·
              refine ⟨22469936972111813590040243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59919831925631502906773981 22469936972111813590040243)
              ·
                refine ⟨33704905458167720385060365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22469936972111813590040243 33704905458167720385060365)
                ·
                  refine ⟨12639339546812895144397637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33704905458167720385060365 12639339546812895144397637)
                  ·
                    refine ⟨2369876165027417839574557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12639339546812895144397637 2369876165027417839574557)
                    ·
                      refine ⟨888703561885281689840459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2369876165027417839574557 888703561885281689840459)
                      ·
                        rfl

theorem cell23_1730744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_1730744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730744 prefixEnd_1730744 := by exact prefixLift 1730744
  have htrace : WordTrace (prefixWord ++ tailWord_1730744) baseStart_1730744 baseEnd_1730744 := by
    simpa [prefixWord, tailWord_1730744, baseEnd_1730744] using wordTrace_append hprefix tailTrace_1730744
  have hstable : (prefixWord ++ tailWord_1730744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730744).length < 2 ^ (prefixWord ++ tailWord_1730744).sum := by decide
  have hdescent : baseEnd_1730744 < baseStart_1730744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730781 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 8]
def baseStart_1730781 : Nat := 118140960795 + 1730781 * 2 ^ 59
def prefixEnd_1730781 : Nat := 4983230072969 + 3 ^ 40 * 1730781 * 2
def baseEnd_1730781 : Nat := 98746951185499782786421

theorem tailTrace_1730781 : CollatzResearch.WordTrace tailWord_1730781 prefixEnd_1730781 98746951185499782786421 := by
  unfold tailWord_1730781
  simp only [CollatzResearch.WordTrace]
  refine ⟨63126769142683505706480197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42084512761789003804320131 63126769142683505706480197)
  ·
    refine ⟨11836269214253157319965037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63126769142683505706480197 11836269214253157319965037)
    ·
      refine ⟨4438600955344933994986889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11836269214253157319965037 4438600955344933994986889)
      ·
        refine ⟨3328950716508700496240167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438600955344933994986889 3328950716508700496240167)
        ·
          refine ⟨4993426074763050744360251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328950716508700496240167 4993426074763050744360251)
          ·
            refine ⟨7490139112144576116540377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993426074763050744360251 7490139112144576116540377)
            ·
              refine ⟨5617604334108432087405283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7490139112144576116540377 5617604334108432087405283)
              ·
                refine ⟨8426406501162648131107925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617604334108432087405283 8426406501162648131107925)
                ·
                  refine ⟨98746951185499782786421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8426406501162648131107925 98746951185499782786421)
                  ·
                    rfl

theorem cell23_1730781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_1730781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730781 prefixEnd_1730781 := by exact prefixLift 1730781
  have htrace : WordTrace (prefixWord ++ tailWord_1730781) baseStart_1730781 baseEnd_1730781 := by
    simpa [prefixWord, tailWord_1730781, baseEnd_1730781] using wordTrace_append hprefix tailTrace_1730781
  have hstable : (prefixWord ++ tailWord_1730781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730781).length < 2 ^ (prefixWord ++ tailWord_1730781).sum := by decide
  have hdescent : baseEnd_1730781 < baseStart_1730781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730785 : List Nat := [1, 2, 3, 1, 3, 1, 5, 2, 1, 4]
def baseStart_1730785 : Nat := 118140960795 + 1730785 * 2 ^ 59
def prefixEnd_1730785 : Nat := 4983230072969 + 3 ^ 40 * 1730785 * 2
def baseEnd_1730785 : Nat := 296241538197372009809257

theorem tailTrace_1730785 : CollatzResearch.WordTrace tailWord_1730785 prefixEnd_1730785 296241538197372009809257 := by
  unfold tailWord_1730785
  simp only [CollatzResearch.WordTrace]
  refine ⟨63126915034669014389625809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42084610023112676259750539 63126915034669014389625809)
  ·
    refine ⟨47345186276001760792219357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63126915034669014389625809 47345186276001760792219357)
    ·
      refine ⟨17754444853500660297082259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47345186276001760792219357 17754444853500660297082259)
      ·
        refine ⟨26631667280250990445623389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17754444853500660297082259 26631667280250990445623389)
        ·
          refine ⟨9986875230094121417108771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26631667280250990445623389 9986875230094121417108771)
          ·
            refine ⟨14980312845141182125663157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986875230094121417108771 14980312845141182125663157)
            ·
              refine ⟨1404404329231985824280921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14980312845141182125663157 1404404329231985824280921)
              ·
                refine ⟨1053303246923989368210691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404404329231985824280921 1053303246923989368210691)
                ·
                  refine ⟨1579954870385984052316037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053303246923989368210691 1579954870385984052316037)
                  ·
                    refine ⟨296241538197372009809257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579954870385984052316037 296241538197372009809257)
                    ·
                      rfl

theorem cell23_1730785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_1730785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730785 prefixEnd_1730785 := by exact prefixLift 1730785
  have htrace : WordTrace (prefixWord ++ tailWord_1730785) baseStart_1730785 baseEnd_1730785 := by
    simpa [prefixWord, tailWord_1730785, baseEnd_1730785] using wordTrace_append hprefix tailTrace_1730785
  have hstable : (prefixWord ++ tailWord_1730785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730785).length < 2 ^ (prefixWord ++ tailWord_1730785).sum := by decide
  have hdescent : baseEnd_1730785 < baseStart_1730785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730801 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 3, 5, 2]
def baseStart_1730801 : Nat := 118140960795 + 1730801 * 2 ^ 59
def prefixEnd_1730801 : Nat := 4983230072969 + 3 ^ 40 * 1730801 * 2
def baseEnd_1730801 : Nat := 888732830282587966827697

theorem tailTrace_1730801 : CollatzResearch.WordTrace tailWord_1730801 prefixEnd_1730801 888732830282587966827697 := by
  unfold tailWord_1730801
  simp only [CollatzResearch.WordTrace]
  refine ⟨63127498602611049122208257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42084999068407366081472171 63127498602611049122208257)
  ·
    refine ⟨47345623951958286841656193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63127498602611049122208257 47345623951958286841656193)
    ·
      refine ⟨35509217963968715131242145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47345623951958286841656193 35509217963968715131242145)
      ·
        refine ⟨26631913472976536348431609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35509217963968715131242145 26631913472976536348431609)
        ·
          refine ⟨19973935104732402261323707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26631913472976536348431609 19973935104732402261323707)
          ·
            refine ⟨29960902657098603391985561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19973935104732402261323707 29960902657098603391985561)
            ·
              refine ⟨22470676992823952543989171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29960902657098603391985561 22470676992823952543989171)
              ·
                refine ⟨33706015489235928815983757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22470676992823952543989171 33706015489235928815983757)
                ·
                  refine ⟨12639755808463473305993909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33706015489235928815983757 12639755808463473305993909)
                  ·
                    refine ⟨1184977107043450622436929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12639755808463473305993909 1184977107043450622436929)
                    ·
                      refine ⟨888732830282587966827697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1184977107043450622436929 888732830282587966827697)
                      ·
                        rfl

theorem cell23_1730801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_1730801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730801 prefixEnd_1730801 := by exact prefixLift 1730801
  have htrace : WordTrace (prefixWord ++ tailWord_1730801) baseStart_1730801 baseEnd_1730801 := by
    simpa [prefixWord, tailWord_1730801, baseEnd_1730801] using wordTrace_append hprefix tailTrace_1730801
  have hstable : (prefixWord ++ tailWord_1730801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730801).length < 2 ^ (prefixWord ++ tailWord_1730801).sum := by decide
  have hdescent : baseEnd_1730801 < baseStart_1730801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730828 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_1730828 : Nat := 118140960795 + 1730828 * 2 ^ 59
def prefixEnd_1730828 : Nat := 4983230072969 + 3 ^ 40 * 1730828 * 2
def baseEnd_1730828 : Nat := 296248898086753120396691

theorem tailTrace_1730828 : CollatzResearch.WordTrace tailWord_1730828 prefixEnd_1730828 296248898086753120396691 := by
  unfold tailWord_1730828
  simp only [CollatzResearch.WordTrace]
  refine ⟨31564241686756616366720569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42085655582342155155627425 31564241686756616366720569)
  ·
    refine ⟨23673181265067462275040427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31564241686756616366720569 23673181265067462275040427)
    ·
      refine ⟨35509771897601193412560641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23673181265067462275040427 35509771897601193412560641)
      ·
        refine ⟨26632328923200895059420481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35509771897601193412560641 26632328923200895059420481)
        ·
          refine ⟨19974246692400671294565361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26632328923200895059420481 19974246692400671294565361)
          ·
            refine ⟨14980685019300503470924021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19974246692400671294565361 14980685019300503470924021)
            ·
              refine ⟨1404439220559422200399127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14980685019300503470924021 1404439220559422200399127)
              ·
                refine ⟨2106658830839133300598691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404439220559422200399127 2106658830839133300598691)
                ·
                  refine ⟨3159988246258699950898037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106658830839133300598691 3159988246258699950898037)
                  ·
                    refine ⟨296248898086753120396691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3159988246258699950898037 296248898086753120396691)
                    ·
                      rfl

theorem cell23_1730828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_1730828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730828 prefixEnd_1730828 := by exact prefixLift 1730828
  have htrace : WordTrace (prefixWord ++ tailWord_1730828) baseStart_1730828 baseEnd_1730828 := by
    simpa [prefixWord, tailWord_1730828, baseEnd_1730828] using wordTrace_append hprefix tailTrace_1730828
  have hstable : (prefixWord ++ tailWord_1730828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730828).length < 2 ^ (prefixWord ++ tailWord_1730828).sum := by decide
  have hdescent : baseEnd_1730828 < baseStart_1730828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730831 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 4]
def baseStart_1730831 : Nat := 118140960795 + 1730831 * 2 ^ 59
def prefixEnd_1730831 : Nat := 4983230072969 + 3 ^ 40 * 1730831 * 2
def baseEnd_1730831 : Nat := 888748234702222849452559

theorem tailTrace_1730831 : CollatzResearch.WordTrace tailWord_1730831 prefixEnd_1730831 888748234702222849452559 := by
  unfold tailWord_1730831
  simp only [CollatzResearch.WordTrace]
  refine ⟨63128592792502364245800347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42085728528334909497200231 63128592792502364245800347)
  ·
    refine ⟨94692889188753546368700521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63128592792502364245800347 94692889188753546368700521)
    ·
      refine ⟨71019666891565159776525391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94692889188753546368700521 71019666891565159776525391)
      ·
        refine ⟨106529500337347739664788087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71019666891565159776525391 106529500337347739664788087)
        ·
          refine ⟨159794250506021609497182131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106529500337347739664788087 159794250506021609497182131)
          ·
            refine ⟨239691375759032414245773197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159794250506021609497182131 239691375759032414245773197)
            ·
              refine ⟨89884265909637155342164949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239691375759032414245773197 89884265909637155342164949)
              ·
                refine ⟨2106662482257120828331991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89884265909637155342164949 2106662482257120828331991)
                ·
                  refine ⟨3159993723385681242497987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106662482257120828331991 3159993723385681242497987)
                  ·
                    refine ⟨4739990585078521863746981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3159993723385681242497987 4739990585078521863746981)
                    ·
                      refine ⟨888748234702222849452559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4739990585078521863746981 888748234702222849452559)
                      ·
                        rfl

theorem cell23_1730831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_1730831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730831 prefixEnd_1730831 := by exact prefixLift 1730831
  have htrace : WordTrace (prefixWord ++ tailWord_1730831) baseStart_1730831 baseEnd_1730831 := by
    simpa [prefixWord, tailWord_1730831, baseEnd_1730831] using wordTrace_append hprefix tailTrace_1730831
  have hstable : (prefixWord ++ tailWord_1730831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730831).length < 2 ^ (prefixWord ++ tailWord_1730831).sum := by decide
  have hdescent : baseEnd_1730831 < baseStart_1730831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730842 : List Nat := [3, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3]
def baseStart_1730842 : Nat := 118140960795 + 1730842 * 2 ^ 59
def prefixEnd_1730842 : Nat := 4983230072969 + 3 ^ 40 * 1730842 * 2
def baseEnd_1730842 : Nat := 888753882989422306415009

theorem tailTrace_1730842 : CollatzResearch.WordTrace tailWord_1730842 prefixEnd_1730842 888753882989422306415009 := by
  unfold tailWord_1730842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15782248498865628281112695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42085995996975008749633853 15782248498865628281112695)
  ·
    refine ⟨23673372748298442421669043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15782248498865628281112695 23673372748298442421669043)
    ·
      refine ⟨35510059122447663632503565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23673372748298442421669043 35510059122447663632503565)
      ·
        refine ⟨13316272170917873862188837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35510059122447663632503565 13316272170917873862188837)
        ·
          refine ⟨2496801032047101349160407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13316272170917873862188837 2496801032047101349160407)
          ·
            refine ⟨3745201548070652023740611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496801032047101349160407 3745201548070652023740611)
            ·
              refine ⟨5617802322105978035610917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745201548070652023740611 5617802322105978035610917)
              ·
                refine ⟨1053337935394870881677047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5617802322105978035610917 1053337935394870881677047)
                ·
                  refine ⟨1580006903092306322515571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053337935394870881677047 1580006903092306322515571)
                  ·
                    refine ⟨2370010354638459483773357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1580006903092306322515571 2370010354638459483773357)
                    ·
                      refine ⟨888753882989422306415009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2370010354638459483773357 888753882989422306415009)
                      ·
                        rfl

theorem cell23_1730842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_1730842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730842 prefixEnd_1730842 := by exact prefixLift 1730842
  have htrace : WordTrace (prefixWord ++ tailWord_1730842) baseStart_1730842 baseEnd_1730842 := by
    simpa [prefixWord, tailWord_1730842, baseEnd_1730842] using wordTrace_append hprefix tailTrace_1730842
  have hstable : (prefixWord ++ tailWord_1730842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730842).length < 2 ^ (prefixWord ++ tailWord_1730842).sum := by decide
  have hdescent : baseEnd_1730842 < baseStart_1730842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730851 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1730851 : Nat := 118140960795 + 1730851 * 2 ^ 59
def prefixEnd_1730851 : Nat := 4983230072969 + 3 ^ 40 * 1730851 * 2
def baseEnd_1730851 : Nat := 888758504315312771202467

theorem tailTrace_1730851 : CollatzResearch.WordTrace tailWord_1730851 prefixEnd_1730851 888758504315312771202467 := by
  unfold tailWord_1730851
  simp only [CollatzResearch.WordTrace]
  refine ⟨63129322252429907661528407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42086214834953271774352271 63129322252429907661528407)
  ·
    refine ⟨94693983378644861492292611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63129322252429907661528407 94693983378644861492292611)
    ·
      refine ⟨142040975067967292238438917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94693983378644861492292611 142040975067967292238438917)
      ·
        refine ⟨26632682825243867294707297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142040975067967292238438917 26632682825243867294707297)
        ·
          refine ⟨19974512118932900471030473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26632682825243867294707297 19974512118932900471030473)
          ·
            refine ⟨14980884089199675353272855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19974512118932900471030473 14980884089199675353272855)
            ·
              refine ⟨22471326133799513029909283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14980884089199675353272855 22471326133799513029909283)
              ·
                refine ⟨33706989200699269544863925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22471326133799513029909283 33706989200699269544863925)
                ·
                  refine ⟨3160030237565556519830993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33706989200699269544863925 3160030237565556519830993)
                  ·
                    refine ⟨2370022678174167389873245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3160030237565556519830993 2370022678174167389873245)
                    ·
                      refine ⟨888758504315312771202467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2370022678174167389873245 888758504315312771202467)
                      ·
                        rfl

theorem cell23_1730851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1730851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730851 prefixEnd_1730851 := by exact prefixLift 1730851
  have htrace : WordTrace (prefixWord ++ tailWord_1730851) baseStart_1730851 baseEnd_1730851 := by
    simpa [prefixWord, tailWord_1730851, baseEnd_1730851] using wordTrace_append hprefix tailTrace_1730851
  have hstable : (prefixWord ++ tailWord_1730851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730851).length < 2 ^ (prefixWord ++ tailWord_1730851).sum := by decide
  have hdescent : baseEnd_1730851 < baseStart_1730851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730878 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1730878 : Nat := 118140960795 + 1730878 * 2 ^ 59
def prefixEnd_1730878 : Nat := 4983230072969 + 3 ^ 40 * 1730878 * 2
def baseEnd_1730878 : Nat := 888772368292984165564843

theorem tailTrace_1730878 : CollatzResearch.WordTrace tailWord_1730878 prefixEnd_1730878 888772368292984165564843 := by
  unfold tailWord_1730878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891288377916511409095161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42086871348888060848507525 7891288377916511409095161)
  ·
    refine ⟨5918466283437383556821371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7891288377916511409095161 5918466283437383556821371)
    ·
      refine ⟨8877699425156075335232057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918466283437383556821371 8877699425156075335232057)
      ·
        refine ⟨6658274568867056501424043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8877699425156075335232057 6658274568867056501424043)
        ·
          refine ⟨9987411853300584752136065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6658274568867056501424043 9987411853300584752136065)
          ·
            refine ⟨7490558889975438564102049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9987411853300584752136065 7490558889975438564102049)
            ·
              refine ⟨5617919167481578923076537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7490558889975438564102049 5617919167481578923076537)
              ·
                refine ⟨4213439375611184192307403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5617919167481578923076537 4213439375611184192307403)
                ·
                  refine ⟨6320159063416776288461105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213439375611184192307403 6320159063416776288461105)
                  ·
                    refine ⟨4740119297562582216345829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6320159063416776288461105 4740119297562582216345829)
                    ·
                      refine ⟨888772368292984165564843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4740119297562582216345829 888772368292984165564843)
                      ·
                        rfl

theorem cell23_1730878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1730878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730878 prefixEnd_1730878 := by exact prefixLift 1730878
  have htrace : WordTrace (prefixWord ++ tailWord_1730878) baseStart_1730878 baseEnd_1730878 := by
    simpa [prefixWord, tailWord_1730878, baseEnd_1730878] using wordTrace_append hprefix tailTrace_1730878
  have hstable : (prefixWord ++ tailWord_1730878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730878).length < 2 ^ (prefixWord ++ tailWord_1730878).sum := by decide
  have hdescent : baseEnd_1730878 < baseStart_1730878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730941 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1730941 : Nat := 118140960795 + 1730941 * 2 ^ 59
def prefixEnd_1730941 : Nat := 4983230072969 + 3 ^ 40 * 1730941 * 2
def baseEnd_1730941 : Nat := 888804717574217419077053

theorem tailTrace_1730941 : CollatzResearch.WordTrace tailWord_1730941 prefixEnd_1730941 888804717574217419077053 := by
  unfold tailWord_1730941
  simp only [CollatzResearch.WordTrace]
  refine ⟨63132604822103853032304677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42088403214735902021536451 63132604822103853032304677)
  ·
    refine ⟨11837363404144472443557127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63132604822103853032304677 11837363404144472443557127)
    ·
      refine ⟨17756045106216708665335691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11837363404144472443557127 17756045106216708665335691)
      ·
        refine ⟨26634067659325062998003537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17756045106216708665335691 26634067659325062998003537)
        ·
          refine ⟨19975550744493797248502653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26634067659325062998003537 19975550744493797248502653)
          ·
            refine ⟨7490831529185173968188495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19975550744493797248502653 7490831529185173968188495)
            ·
              refine ⟨11236247293777760952282743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7490831529185173968188495 11236247293777760952282743)
              ·
                refine ⟨16854370940666641428424115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11236247293777760952282743 16854370940666641428424115)
                ·
                  refine ⟨25281556410999962142636173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16854370940666641428424115 25281556410999962142636173)
                  ·
                    refine ⟨9480583654124985803488565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25281556410999962142636173 9480583654124985803488565)
                    ·
                      refine ⟨888804717574217419077053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9480583654124985803488565 888804717574217419077053)
                      ·
                        rfl

theorem cell23_1730941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1730941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730941 prefixEnd_1730941 := by exact prefixLift 1730941
  have htrace : WordTrace (prefixWord ++ tailWord_1730941) baseStart_1730941 baseEnd_1730941 := by
    simpa [prefixWord, tailWord_1730941, baseEnd_1730941] using wordTrace_append hprefix tailTrace_1730941
  have hstable : (prefixWord ++ tailWord_1730941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730941).length < 2 ^ (prefixWord ++ tailWord_1730941).sum := by decide
  have hdescent : baseEnd_1730941 < baseStart_1730941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730955 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 4, 2, 2]
def baseStart_1730955 : Nat := 118140960795 + 1730955 * 2 ^ 59
def prefixEnd_1730955 : Nat := 4983230072969 + 3 ^ 40 * 1730955 * 2
def baseEnd_1730955 : Nat := 888811906303380364301989

theorem tailTrace_1730955 : CollatzResearch.WordTrace tailWord_1730955 prefixEnd_1730955 888811906303380364301989 := by
  unfold tailWord_1730955
  simp only [CollatzResearch.WordTrace]
  refine ⟨63133115444053133423314319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42088743629368755615542879 63133115444053133423314319)
  ·
    refine ⟨94699673166079700134971479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63133115444053133423314319 94699673166079700134971479)
    ·
      refine ⟨142049509749119550202457219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94699673166079700134971479 142049509749119550202457219)
      ·
        refine ⟨213074264623679325303685829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142049509749119550202457219 213074264623679325303685829)
        ·
          refine ⟨39951424616939873494441093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213074264623679325303685829 39951424616939873494441093)
          ·
            refine ⟨7490892115676226280207705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39951424616939873494441093 7490892115676226280207705)
            ·
              refine ⟨5618169086757169710155779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7490892115676226280207705 5618169086757169710155779)
              ·
                refine ⟨8427253630135754565233669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618169086757169710155779 8427253630135754565233669)
                ·
                  refine ⟨1580110055650453980981313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8427253630135754565233669 1580110055650453980981313)
                  ·
                    refine ⟨1185082541737840485735985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1580110055650453980981313 1185082541737840485735985)
                    ·
                      refine ⟨888811906303380364301989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185082541737840485735985 888811906303380364301989)
                      ·
                        rfl

theorem cell23_1730955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 2, 2].length) (baseStart_1730955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1730955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1730955 prefixEnd_1730955 := by exact prefixLift 1730955
  have htrace : WordTrace (prefixWord ++ tailWord_1730955) baseStart_1730955 baseEnd_1730955 := by
    simpa [prefixWord, tailWord_1730955, baseEnd_1730955] using wordTrace_append hprefix tailTrace_1730955
  have hstable : (prefixWord ++ tailWord_1730955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730955).length < 2 ^ (prefixWord ++ tailWord_1730955).sum := by decide
  have hdescent : baseEnd_1730955 < baseStart_1730955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731011 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4]
def baseStart_1731011 : Nat := 118140960795 + 1731011 * 2 ^ 59
def prefixEnd_1731011 : Nat := 4983230072969 + 3 ^ 40 * 1731011 * 2
def baseEnd_1731011 : Nat := 888840661220032145201731

theorem tailTrace_1731011 : CollatzResearch.WordTrace tailWord_1731011 prefixEnd_1731011 888840661220032145201731 := by
  unfold tailWord_1731011
  simp only [CollatzResearch.WordTrace]
  refine ⟨63135157931850254987352887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42090105287900169991568591 63135157931850254987352887)
  ·
    refine ⟨94702736897775382481029331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63135157931850254987352887 94702736897775382481029331)
    ·
      refine ⟨142054105346663073721543997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94702736897775382481029331 142054105346663073721543997)
      ·
        refine ⟨53270289504998652645578999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142054105346663073721543997 53270289504998652645578999)
        ·
          refine ⟨79905434257497978968368499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53270289504998652645578999 79905434257497978968368499)
          ·
            refine ⟨119858151386246968452552749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79905434257497978968368499 119858151386246968452552749)
            ·
              refine ⟨44946806769842613169707281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119858151386246968452552749 44946806769842613169707281)
              ·
                refine ⟨33710105077381959877280461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44946806769842613169707281 33710105077381959877280461)
                ·
                  refine ⟨12641289404018234953980173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33710105077381959877280461 12641289404018234953980173)
                  ·
                    refine ⟨4740483526506838107742565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12641289404018234953980173 4740483526506838107742565)
                    ·
                      refine ⟨888840661220032145201731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4740483526506838107742565 888840661220032145201731)
                      ·
                        rfl

theorem cell23_1731011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_1731011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731011 prefixEnd_1731011 := by exact prefixLift 1731011
  have htrace : WordTrace (prefixWord ++ tailWord_1731011) baseStart_1731011 baseEnd_1731011 := by
    simpa [prefixWord, tailWord_1731011, baseEnd_1731011] using wordTrace_append hprefix tailTrace_1731011
  have hstable : (prefixWord ++ tailWord_1731011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731011).length < 2 ^ (prefixWord ++ tailWord_1731011).sum := by decide
  have hdescent : baseEnd_1731011 < baseStart_1731011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731012 : List Nat := [2, 3, 3, 2, 2, 1, 1, 4, 5]
def baseStart_1731012 : Nat := 118140960795 + 1731012 * 2 ^ 59
def prefixEnd_1731012 : Nat := 4983230072969 + 3 ^ 40 * 1731012 * 2
def baseEnd_1731012 : Nat := 98760130522298515698803

theorem tailTrace_1731012 : CollatzResearch.WordTrace tailWord_1731012 prefixEnd_1731012 98760130522298515698803 := by
  unfold tailWord_1731012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31567597202423316079069645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42090129603231088105426193 31567597202423316079069645)
  ·
    refine ⟨11837848950908743529651117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31567597202423316079069645 11837848950908743529651117)
    ·
      refine ⟨4439193356590778823619169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11837848950908743529651117 4439193356590778823619169)
      ·
        refine ⟨3329395017443084117714377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4439193356590778823619169 3329395017443084117714377)
        ·
          refine ⟨2497046263082313088285783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329395017443084117714377 2497046263082313088285783)
          ·
            refine ⟨3745569394623469632428675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497046263082313088285783 3745569394623469632428675)
            ·
              refine ⟨5618354091935204448643013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745569394623469632428675 5618354091935204448643013)
              ·
                refine ⟨1053441392237850834120565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5618354091935204448643013 1053441392237850834120565)
                ·
                  refine ⟨98760130522298515698803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053441392237850834120565 98760130522298515698803)
                  ·
                    rfl

theorem cell23_1731012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_1731012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731012 prefixEnd_1731012 := by exact prefixLift 1731012
  have htrace : WordTrace (prefixWord ++ tailWord_1731012) baseStart_1731012 baseEnd_1731012 := by
    simpa [prefixWord, tailWord_1731012, baseEnd_1731012] using wordTrace_append hprefix tailTrace_1731012
  have hstable : (prefixWord ++ tailWord_1731012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731012).length < 2 ^ (prefixWord ++ tailWord_1731012).sum := by decide
  have hdescent : baseEnd_1731012 < baseStart_1731012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731042 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1731042 : Nat := 118140960795 + 1731042 * 2 ^ 59
def prefixEnd_1731042 : Nat := 4983230072969 + 3 ^ 40 * 1731042 * 2
def baseEnd_1731042 : Nat := 296285526373440507971363

theorem tailTrace_1731042 : CollatzResearch.WordTrace tailWord_1731042 prefixEnd_1731042 296285526373440507971363 := by
  unfold tailWord_1731042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15784072148684486820432845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42090859063158631521154253 15784072148684486820432845)
  ·
    refine ⟨5919027055756682557662317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15784072148684486820432845 5919027055756682557662317)
    ·
      refine ⟨2219635145908755959123369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5919027055756682557662317 2219635145908755959123369)
      ·
        refine ⟨1664726359431566969342527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2219635145908755959123369 1664726359431566969342527)
        ·
          refine ⟨2497089539147350454013791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664726359431566969342527 2497089539147350454013791)
          ·
            refine ⟨3745634308721025681020687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497089539147350454013791 3745634308721025681020687)
            ·
              refine ⟨5618451463081538521531031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745634308721025681020687 5618451463081538521531031)
              ·
                refine ⟨8427677194622307782296547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618451463081538521531031 8427677194622307782296547)
                ·
                  refine ⟨12641515791933461673444821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427677194622307782296547 12641515791933461673444821)
                  ·
                    refine ⟨296285526373440507971363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12641515791933461673444821 296285526373440507971363)
                    ·
                      rfl

theorem cell23_1731042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1731042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731042 prefixEnd_1731042 := by exact prefixLift 1731042
  have htrace : WordTrace (prefixWord ++ tailWord_1731042) baseStart_1731042 baseEnd_1731042 := by
    simpa [prefixWord, tailWord_1731042, baseEnd_1731042] using wordTrace_append hprefix tailTrace_1731042
  have hstable : (prefixWord ++ tailWord_1731042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731042).length < 2 ^ (prefixWord ++ tailWord_1731042).sum := by decide
  have hdescent : baseEnd_1731042 < baseStart_1731042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731045 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1731045 : Nat := 118140960795 + 1731045 * 2 ^ 59
def prefixEnd_1731045 : Nat := 4983230072969 + 3 ^ 40 * 1731045 * 2
def baseEnd_1731045 : Nat := 888858119562285012176575

theorem tailTrace_1731045 : CollatzResearch.WordTrace tailWord_1731045 prefixEnd_1731045 888858119562285012176575 := by
  unfold tailWord_1731045
  simp only [CollatzResearch.WordTrace]
  refine ⟨63136398013727078794090589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42090932009151385862727059 63136398013727078794090589)
  ·
    refine ⟨23676149255147654547783971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63136398013727078794090589 23676149255147654547783971)
    ·
      refine ⟨35514223882721481821675957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23676149255147654547783971 35514223882721481821675957)
      ·
        refine ⟨3329458489005138920782121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35514223882721481821675957 3329458489005138920782121)
        ·
          refine ⟨2497093866753854190586591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329458489005138920782121 2497093866753854190586591)
          ·
            refine ⟨3745640800130781285879887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497093866753854190586591 3745640800130781285879887)
            ·
              refine ⟨5618461200196171928819831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745640800130781285879887 5618461200196171928819831)
              ·
                refine ⟨8427691800294257893229747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618461200196171928819831 8427691800294257893229747)
                ·
                  refine ⟨12641537700441386839844621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427691800294257893229747 12641537700441386839844621)
                  ·
                    refine ⟨4740576637665520064941733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12641537700441386839844621 4740576637665520064941733)
                    ·
                      refine ⟨888858119562285012176575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4740576637665520064941733 888858119562285012176575)
                      ·
                        rfl

theorem cell23_1731045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1731045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731045 prefixEnd_1731045 := by exact prefixLift 1731045
  have htrace : WordTrace (prefixWord ++ tailWord_1731045) baseStart_1731045 baseEnd_1731045 := by
    simpa [prefixWord, tailWord_1731045, baseEnd_1731045] using wordTrace_append hprefix tailTrace_1731045
  have hstable : (prefixWord ++ tailWord_1731045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731045).length < 2 ^ (prefixWord ++ tailWord_1731045).sum := by decide
  have hdescent : baseEnd_1731045 < baseStart_1731045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731051 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 8]
def baseStart_1731051 : Nat := 118140960795 + 1731051 * 2 ^ 59
def prefixEnd_1731051 : Nat := 4983230072969 + 3 ^ 40 * 1731051 * 2
def baseEnd_1731051 : Nat := 98762355605134665411283

theorem tailTrace_1731051 : CollatzResearch.WordTrace tailWord_1731051 prefixEnd_1731051 98762355605134665411283 := by
  unfold tailWord_1731051
  simp only [CollatzResearch.WordTrace]
  refine ⟨63136616851705341818809007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42091077901136894545872671 63136616851705341818809007)
  ·
    refine ⟨94704925277558012728213511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63136616851705341818809007 94704925277558012728213511)
    ·
      refine ⟨142057387916337019092320267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94704925277558012728213511 142057387916337019092320267)
      ·
        refine ⟨213086081874505528638480401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142057387916337019092320267 213086081874505528638480401)
        ·
          refine ⟨159814561405879146478860301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213086081874505528638480401 159814561405879146478860301)
          ·
            refine ⟨59930460527204679929572613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159814561405879146478860301 59930460527204679929572613)
            ·
              refine ⟨11236961348850877486794865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59930460527204679929572613 11236961348850877486794865)
              ·
                refine ⟨8427721011638158115096149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11236961348850877486794865 8427721011638158115096149)
                ·
                  refine ⟨98762355605134665411283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8427721011638158115096149 98762355605134665411283)
                  ·
                    rfl

theorem cell23_1731051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 8].length) (baseStart_1731051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731051 prefixEnd_1731051 := by exact prefixLift 1731051
  have htrace : WordTrace (prefixWord ++ tailWord_1731051) baseStart_1731051 baseEnd_1731051 := by
    simpa [prefixWord, tailWord_1731051, baseEnd_1731051] using wordTrace_append hprefix tailTrace_1731051
  have hstable : (prefixWord ++ tailWord_1731051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731051).length < 2 ^ (prefixWord ++ tailWord_1731051).sum := by decide
  have hdescent : baseEnd_1731051 < baseStart_1731051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731071 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1731071 : Nat := 118140960795 + 1731071 * 2 ^ 59
def prefixEnd_1731071 : Nat := 4983230072969 + 3 ^ 40 * 1731071 * 2
def baseEnd_1731071 : Nat := 888871470059301910451455

theorem tailTrace_1731071 : CollatzResearch.WordTrace tailWord_1731071 prefixEnd_1731071 888871470059301910451455 := by
  unfold tailWord_1731071
  simp only [CollatzResearch.WordTrace]
  refine ⟨63137346311632885234537067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42091564207755256823024711 63137346311632885234537067)
  ·
    refine ⟨94706019467449327851805601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63137346311632885234537067 94706019467449327851805601)
    ·
      refine ⟨71029514600586995888854201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94706019467449327851805601 71029514600586995888854201)
      ·
        refine ⟨53272135950440246916640651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71029514600586995888854201 53272135950440246916640651)
        ·
          refine ⟨79908203925660370374960977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53272135950440246916640651 79908203925660370374960977)
          ·
            refine ⟨59931152944245277781220733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79908203925660370374960977 59931152944245277781220733)
            ·
              refine ⟨22474182354091979167957775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59931152944245277781220733 22474182354091979167957775)
              ·
                refine ⟨33711273531137968751936663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22474182354091979167957775 33711273531137968751936663)
                ·
                  refine ⟨50566910296706953127904995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33711273531137968751936663 50566910296706953127904995)
                  ·
                    refine ⟨75850365445060429691857493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50566910296706953127904995 75850365445060429691857493)
                    ·
                      refine ⟨888871470059301910451455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 75850365445060429691857493 888871470059301910451455)
                      ·
                        rfl

theorem cell23_1731071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1731071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731071 prefixEnd_1731071 := by exact prefixLift 1731071
  have htrace : WordTrace (prefixWord ++ tailWord_1731071) baseStart_1731071 baseEnd_1731071 := by
    simpa [prefixWord, tailWord_1731071, baseEnd_1731071] using wordTrace_append hprefix tailTrace_1731071
  have hstable : (prefixWord ++ tailWord_1731071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731071).length < 2 ^ (prefixWord ++ tailWord_1731071).sum := by decide
  have hdescent : baseEnd_1731071 < baseStart_1731071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731081 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 9]
def baseStart_1731081 : Nat := 118140960795 + 1731081 * 2 ^ 59
def prefixEnd_1731081 : Nat := 4983230072969 + 3 ^ 40 * 1731081 * 2
def baseEnd_1731081 : Nat := 296292201621948957108803

theorem tailTrace_1731081 : CollatzResearch.WordTrace tailWord_1731081 prefixEnd_1731081 296292201621948957108803 := by
  unfold tailWord_1731081
  simp only [CollatzResearch.WordTrace]
  refine ⟨63137711041596656942401097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42091807361064437961600731 63137711041596656942401097)
  ·
    refine ⟨47353283281197492706800823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63137711041596656942401097 47353283281197492706800823)
    ·
      refine ⟨71029924921796239060201235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47353283281197492706800823 71029924921796239060201235)
      ·
        refine ⟨106544887382694358590301853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71029924921796239060201235 106544887382694358590301853)
        ·
          refine ⟨39954332768510384471363195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106544887382694358590301853 39954332768510384471363195)
          ·
            refine ⟨59931499152765576707044793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39954332768510384471363195 59931499152765576707044793)
            ·
              refine ⟨44948624364574182530283595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59931499152765576707044793 44948624364574182530283595)
              ·
                refine ⟨67422936546861273795425393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44948624364574182530283595 67422936546861273795425393)
                ·
                  refine ⟨50567202410145955346569045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67422936546861273795425393 50567202410145955346569045)
                  ·
                    refine ⟨296292201621948957108803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50567202410145955346569045 296292201621948957108803)
                    ·
                      rfl

theorem cell23_1731081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_1731081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731081 prefixEnd_1731081 := by exact prefixLift 1731081
  have htrace : WordTrace (prefixWord ++ tailWord_1731081) baseStart_1731081 baseEnd_1731081 := by
    simpa [prefixWord, tailWord_1731081, baseEnd_1731081] using wordTrace_append hprefix tailTrace_1731081
  have hstable : (prefixWord ++ tailWord_1731081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731081).length < 2 ^ (prefixWord ++ tailWord_1731081).sum := by decide
  have hdescent : baseEnd_1731081 < baseStart_1731081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731098 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_1731098 : Nat := 118140960795 + 1731098 * 2 ^ 59
def prefixEnd_1731098 : Nat := 4983230072969 + 3 ^ 40 * 1731098 * 2
def baseEnd_1731098 : Nat := 296295111345657768271277

theorem tailTrace_1731098 : CollatzResearch.WordTrace tailWord_1731098 prefixEnd_1731098 296295111345657768271277 := by
  unfold tailWord_1731098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15784582770633767211442487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42092220721690045897179965 15784582770633767211442487)
  ·
    refine ⟨23676874155950650817163731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15784582770633767211442487 23676874155950650817163731)
    ·
      refine ⟨35515311233925976225745597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23676874155950650817163731 35515311233925976225745597)
      ·
        refine ⟨13318241712722241084654599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35515311233925976225745597 13318241712722241084654599)
        ·
          refine ⟨19977362569083361626981899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13318241712722241084654599 19977362569083361626981899)
          ·
            refine ⟨29966043853625042440472849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19977362569083361626981899 29966043853625042440472849)
            ·
              refine ⟨22474532890218781830354637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29966043853625042440472849 22474532890218781830354637)
              ·
                refine ⟨8427949833832043186382989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22474532890218781830354637 8427949833832043186382989)
                ·
                  refine ⟨3160481187687016194893621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8427949833832043186382989 3160481187687016194893621)
                  ·
                    refine ⟨296295111345657768271277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3160481187687016194893621 296295111345657768271277)
                    ·
                      rfl

theorem cell23_1731098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_1731098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731098 prefixEnd_1731098 := by exact prefixLift 1731098
  have htrace : WordTrace (prefixWord ++ tailWord_1731098) baseStart_1731098 baseEnd_1731098 := by
    simpa [prefixWord, tailWord_1731098, baseEnd_1731098] using wordTrace_append hprefix tailTrace_1731098
  have hstable : (prefixWord ++ tailWord_1731098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731098).length < 2 ^ (prefixWord ++ tailWord_1731098).sum := by decide
  have hdescent : baseEnd_1731098 < baseStart_1731098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731105 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1731105 : Nat := 118140960795 + 1731105 * 2 ^ 59
def prefixEnd_1731105 : Nat := 4983230072969 + 3 ^ 40 * 1731105 * 2
def baseEnd_1731105 : Nat := 888888928401554777426299

theorem tailTrace_1731105 : CollatzResearch.WordTrace tailWord_1731105 prefixEnd_1731105 888888928401554777426299 := by
  unfold tailWord_1731105
  simp only [CollatzResearch.WordTrace]
  refine ⟨63138586393509709041274769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42092390929006472694183179 63138586393509709041274769)
  ·
    refine ⟨47353939795132281780956077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63138586393509709041274769 47353939795132281780956077)
    ·
      refine ⟨17757727423174605667858529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47353939795132281780956077 17757727423174605667858529)
      ·
        refine ⟨13318295567380954250893897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17757727423174605667858529 13318295567380954250893897)
        ·
          refine ⟨9988721675535715688170423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13318295567380954250893897 9988721675535715688170423)
          ·
            refine ⟨14983082513303573532255635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9988721675535715688170423 14983082513303573532255635)
            ·
              refine ⟨22474623769955360298383453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14983082513303573532255635 22474623769955360298383453)
              ·
                refine ⟨8427983913733260111893795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22474623769955360298383453 8427983913733260111893795)
                ·
                  refine ⟨12641975870599890167840693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427983913733260111893795 12641975870599890167840693)
                  ·
                    refine ⟨1185185237868739703235065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12641975870599890167840693 1185185237868739703235065)
                    ·
                      refine ⟨888888928401554777426299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185185237868739703235065 888888928401554777426299)
                      ·
                        rfl

theorem cell23_1731105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1731105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731105 prefixEnd_1731105 := by exact prefixLift 1731105
  have htrace : WordTrace (prefixWord ++ tailWord_1731105) baseStart_1731105 baseEnd_1731105 := by
    simpa [prefixWord, tailWord_1731105, baseEnd_1731105] using wordTrace_append hprefix tailTrace_1731105
  have hstable : (prefixWord ++ tailWord_1731105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731105).length < 2 ^ (prefixWord ++ tailWord_1731105).sum := by decide
  have hdescent : baseEnd_1731105 < baseStart_1731105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731148 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1731148 : Nat := 118140960795 + 1731148 * 2 ^ 59
def prefixEnd_1731148 : Nat := 4983230072969 + 3 ^ 40 * 1731148 * 2
def baseEnd_1731148 : Nat := 888911008069698109188601

theorem tailTrace_1731148 : CollatzResearch.WordTrace tailWord_1731148 prefixEnd_1731148 888911008069698109188601 := by
  unfold tailWord_1731148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31570077366176963692545049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42093436488235951590060065 31570077366176963692545049)
  ·
    refine ⟨23677558024632722769408787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31570077366176963692545049 23677558024632722769408787)
    ·
      refine ⟨35516337036949084154113181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23677558024632722769408787 35516337036949084154113181)
      ·
        refine ⟨13318626388855906557792443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35516337036949084154113181 13318626388855906557792443)
        ·
          refine ⟨19977939583283859836688665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13318626388855906557792443 19977939583283859836688665)
          ·
            refine ⟨14983454687462894877516499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19977939583283859836688665 14983454687462894877516499)
            ·
              refine ⟨22475182031194342316274749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14983454687462894877516499 22475182031194342316274749)
              ·
                refine ⟨8428193261697878368603031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22475182031194342316274749 8428193261697878368603031)
                ·
                  refine ⟨12642289892546817552904547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8428193261697878368603031 12642289892546817552904547)
                  ·
                    refine ⟨18963434838820226329356821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12642289892546817552904547 18963434838820226329356821)
                    ·
                      refine ⟨888911008069698109188601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18963434838820226329356821 888911008069698109188601)
                      ·
                        rfl

theorem cell23_1731148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1731148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731148 prefixEnd_1731148 := by exact prefixLift 1731148
  have htrace : WordTrace (prefixWord ++ tailWord_1731148) baseStart_1731148 baseEnd_1731148 := by
    simpa [prefixWord, tailWord_1731148, baseEnd_1731148] using wordTrace_append hprefix tailTrace_1731148
  have hstable : (prefixWord ++ tailWord_1731148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731148).length < 2 ^ (prefixWord ++ tailWord_1731148).sum := by decide
  have hdescent : baseEnd_1731148 < baseStart_1731148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731149 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1731149 : Nat := 118140960795 + 1731149 * 2 ^ 59
def prefixEnd_1731149 : Nat := 4983230072969 + 3 ^ 40 * 1731149 * 2
def baseEnd_1731149 : Nat := 296303840516784201758699

theorem tailTrace_1731149 : CollatzResearch.WordTrace tailWord_1731149 prefixEnd_1731149 296303840516784201758699 := by
  unfold tailWord_1731149
  simp only [CollatzResearch.WordTrace]
  refine ⟨63140191205350304555876501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42093460803566869703917667 63140191205350304555876501)
  ·
    refine ⟨2959696462750795526056711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63140191205350304555876501 2959696462750795526056711)
    ·
      refine ⟨4439544694126193289085067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959696462750795526056711 4439544694126193289085067)
      ·
        refine ⟨6659317041189289933627601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439544694126193289085067 6659317041189289933627601)
        ·
          refine ⟨4994487780891967450220701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6659317041189289933627601 4994487780891967450220701)
          ·
            refine ⟨1872932917834487793832763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4994487780891967450220701 1872932917834487793832763)
            ·
              refine ⟨2809399376751731690749145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872932917834487793832763 2809399376751731690749145)
              ·
                refine ⟨2107049532563798768061859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809399376751731690749145 2107049532563798768061859)
                ·
                  refine ⟨3160574298845698152092789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107049532563798768061859 3160574298845698152092789)
                  ·
                    refine ⟨296303840516784201758699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3160574298845698152092789 296303840516784201758699)
                    ·
                      rfl

theorem cell23_1731149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1731149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731149 prefixEnd_1731149 := by exact prefixLift 1731149
  have htrace : WordTrace (prefixWord ++ tailWord_1731149) baseStart_1731149 baseEnd_1731149 := by
    simpa [prefixWord, tailWord_1731149, baseEnd_1731149] using wordTrace_append hprefix tailTrace_1731149
  have hstable : (prefixWord ++ tailWord_1731149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731149).length < 2 ^ (prefixWord ++ tailWord_1731149).sum := by decide
  have hdescent : baseEnd_1731149 < baseStart_1731149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731295 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 4, 5]
def baseStart_1731295 : Nat := 118140960795 + 1731295 * 2 ^ 59
def prefixEnd_1731295 : Nat := 4983230072969 + 3 ^ 40 * 1731295 * 2
def baseEnd_1731295 : Nat := 296328829908636344683475

theorem tailTrace_1731295 : CollatzResearch.WordTrace tailWord_1731295 prefixEnd_1731295 296328829908636344683475 := by
  unfold tailWord_1731295
  simp only [CollatzResearch.WordTrace]
  refine ⟨63145516262821371490691339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42097010841880914327127559 63145516262821371490691339)
  ·
    refine ⟨94718274394232057236037009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63145516262821371490691339 94718274394232057236037009)
    ·
      refine ⟨71038705795674042927027757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94718274394232057236037009 71038705795674042927027757)
      ·
        refine ⟨26639514673377766097635409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71038705795674042927027757 26639514673377766097635409)
        ·
          refine ⟨19979636005033324573226557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26639514673377766097635409 19979636005033324573226557)
          ·
            refine ⟨7492363501887496714959959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19979636005033324573226557 7492363501887496714959959)
            ·
              refine ⟨11238545252831245072439939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492363501887496714959959 11238545252831245072439939)
              ·
                refine ⟨16857817879246867608659909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11238545252831245072439939 16857817879246867608659909)
                ·
                  refine ⟨3160840852358787676623733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16857817879246867608659909 3160840852358787676623733)
                  ·
                    refine ⟨296328829908636344683475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3160840852358787676623733 296328829908636344683475)
                    ·
                      rfl

theorem cell23_1731295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_1731295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731295 prefixEnd_1731295 := by exact prefixLift 1731295
  have htrace : WordTrace (prefixWord ++ tailWord_1731295) baseStart_1731295 baseEnd_1731295 := by
    simpa [prefixWord, tailWord_1731295, baseEnd_1731295] using wordTrace_append hprefix tailTrace_1731295
  have hstable : (prefixWord ++ tailWord_1731295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731295).length < 2 ^ (prefixWord ++ tailWord_1731295).sum := by decide
  have hdescent : baseEnd_1731295 < baseStart_1731295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731315 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 4]
def baseStart_1731315 : Nat := 118140960795 + 1731315 * 2 ^ 59
def prefixEnd_1731315 : Nat := 4983230072969 + 3 ^ 40 * 1731315 * 2
def baseEnd_1731315 : Nat := 888996759338998955800333

theorem tailTrace_1731315 : CollatzResearch.WordTrace tailWord_1731315 prefixEnd_1731315 888996759338998955800333 := by
  unfold tailWord_1731315
  simp only [CollatzResearch.WordTrace]
  refine ⟨63146245722748914906419399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42097497148499276604279599 63146245722748914906419399)
  ·
    refine ⟨94719368584123372359629099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63146245722748914906419399 94719368584123372359629099)
    ·
      refine ⟨142079052876185058539443649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94719368584123372359629099 142079052876185058539443649)
      ·
        refine ⟨106559289657138793904582737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142079052876185058539443649 106559289657138793904582737)
        ·
          refine ⟨79919467242854095428437053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106559289657138793904582737 79919467242854095428437053)
          ·
            refine ⟨29969800216070285785663895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79919467242854095428437053 29969800216070285785663895)
            ·
              refine ⟨44954700324105428678495843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29969800216070285785663895 44954700324105428678495843)
              ·
                refine ⟨67432050486158143017743765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44954700324105428678495843 67432050486158143017743765)
                ·
                  refine ⟨3160877366538662953956739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67432050486158143017743765 3160877366538662953956739)
                  ·
                    refine ⟨4741316049807994430935109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3160877366538662953956739 4741316049807994430935109)
                    ·
                      refine ⟨888996759338998955800333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4741316049807994430935109 888996759338998955800333)
                      ·
                        rfl

theorem cell23_1731315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_1731315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731315 prefixEnd_1731315 := by exact prefixLift 1731315
  have htrace : WordTrace (prefixWord ++ tailWord_1731315) baseStart_1731315 baseEnd_1731315 := by
    simpa [prefixWord, tailWord_1731315, baseEnd_1731315] using wordTrace_append hprefix tailTrace_1731315
  have hstable : (prefixWord ++ tailWord_1731315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731315).length < 2 ^ (prefixWord ++ tailWord_1731315).sum := by decide
  have hdescent : baseEnd_1731315 < baseStart_1731315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731386 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_1731386 : Nat := 118140960795 + 1731386 * 2 ^ 59
def prefixEnd_1731386 : Nat := 4983230072969 + 3 ^ 40 * 1731386 * 2
def baseEnd_1731386 : Nat := 889033216465468178012507

theorem tailTrace_1731386 : CollatzResearch.WordTrace tailWord_1731386 prefixEnd_1731386 889033216465468178012507 := by
  unfold tailWord_1731386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15787208826372923508063503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42099223536994462688169341 15787208826372923508063503)
  ·
    refine ⟨23680813239559385262095255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15787208826372923508063503 23680813239559385262095255)
    ·
      refine ⟨35521219859339077893142883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23680813239559385262095255 35521219859339077893142883)
      ·
        refine ⟨53281829789008616839714325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35521219859339077893142883 53281829789008616839714325)
        ·
          refine ⟨2497585771359778914361609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53281829789008616839714325 2497585771359778914361609)
          ·
            refine ⟨1873189328519834185771207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2497585771359778914361609 1873189328519834185771207)
            ·
              refine ⟨2809783992779751278656811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873189328519834185771207 2809783992779751278656811)
              ·
                refine ⟨4214675989169626917985217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809783992779751278656811 4214675989169626917985217)
                ·
                  refine ⟨3161006991877220188488913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4214675989169626917985217 3161006991877220188488913)
                  ·
                    refine ⟨2370755243907915141366685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3161006991877220188488913 2370755243907915141366685)
                    ·
                      refine ⟨889033216465468178012507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2370755243907915141366685 889033216465468178012507)
                      ·
                        rfl

theorem cell23_1731386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_1731386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731386 prefixEnd_1731386 := by exact prefixLift 1731386
  have htrace : WordTrace (prefixWord ++ tailWord_1731386) baseStart_1731386 baseEnd_1731386 := by
    simpa [prefixWord, tailWord_1731386, baseEnd_1731386] using wordTrace_append hprefix tailTrace_1731386
  have hstable : (prefixWord ++ tailWord_1731386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731386).length < 2 ^ (prefixWord ++ tailWord_1731386).sum := by decide
  have hdescent : baseEnd_1731386 < baseStart_1731386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731452 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_1731452 : Nat := 118140960795 + 1731452 * 2 ^ 59
def prefixEnd_1731452 : Nat := 4983230072969 + 3 ^ 40 * 1731452 * 2
def baseEnd_1731452 : Nat := 889067106188664919787203

theorem tailTrace_1731452 : CollatzResearch.WordTrace tailWord_1731452 prefixEnd_1731452 889067106188664919787203 := by
  unfold tailWord_1731452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31575621261626293652078305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42100828348835058202771073 31575621261626293652078305)
  ·
    refine ⟨23681715946219720239058729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31575621261626293652078305 23681715946219720239058729)
    ·
      refine ⟨17761286959664790179294047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23681715946219720239058729 17761286959664790179294047)
      ·
        refine ⟨26641930439497185268941071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17761286959664790179294047 26641930439497185268941071)
        ·
          refine ⟨39962895659245777903411607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26641930439497185268941071 39962895659245777903411607)
          ·
            refine ⟨59944343488868666855117411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39962895659245777903411607 59944343488868666855117411)
            ·
              refine ⟨89916515233303000282676117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59944343488868666855117411 89916515233303000282676117)
              ·
                refine ⟨4214836651561078138250443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89916515233303000282676117 4214836651561078138250443)
                ·
                  refine ⟨6322254977341617207375665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214836651561078138250443 6322254977341617207375665)
                  ·
                    refine ⟨4741691233006212905531749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6322254977341617207375665 4741691233006212905531749)
                    ·
                      refine ⟨889067106188664919787203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4741691233006212905531749 889067106188664919787203)
                      ·
                        rfl

theorem cell23_1731452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_1731452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731452 prefixEnd_1731452 := by exact prefixLift 1731452
  have htrace : WordTrace (prefixWord ++ tailWord_1731452) baseStart_1731452 baseEnd_1731452 := by
    simpa [prefixWord, tailWord_1731452, baseEnd_1731452] using wordTrace_append hprefix tailTrace_1731452
  have hstable : (prefixWord ++ tailWord_1731452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731452).length < 2 ^ (prefixWord ++ tailWord_1731452).sum := by decide
  have hdescent : baseEnd_1731452 < baseStart_1731452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731459 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 3]
def baseStart_1731459 : Nat := 118140960795 + 1731459 * 2 ^ 59
def prefixEnd_1731459 : Nat := 4983230072969 + 3 ^ 40 * 1731459 * 2
def baseEnd_1731459 : Nat := 889070700553246392399671

theorem tailTrace_1731459 : CollatzResearch.WordTrace tailWord_1731459 prefixEnd_1731459 889070700553246392399671 := by
  unfold tailWord_1731459
  simp only [CollatzResearch.WordTrace]
  refine ⟨63151497834227227499661431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42100998556151484999774287 63151497834227227499661431)
  ·
    refine ⟨94727246751340841249492147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63151497834227227499661431 94727246751340841249492147)
    ·
      refine ⟨142090870127011261874238221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94727246751340841249492147 142090870127011261874238221)
      ·
        refine ⟨53284076297629223202839333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142090870127011261874238221 53284076297629223202839333)
        ·
          refine ⟨9990764305805479350532375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53284076297629223202839333 9990764305805479350532375)
          ·
            refine ⟨14986146458708219025798563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9990764305805479350532375 14986146458708219025798563)
            ·
              refine ⟨22479219688062328538697845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14986146458708219025798563 22479219688062328538697845)
              ·
                refine ⟨2107426845755843300502923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22479219688062328538697845 2107426845755843300502923)
                ·
                  refine ⟨3161140268633764950754385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107426845755843300502923 3161140268633764950754385)
                  ·
                    refine ⟨2370855201475323713065789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3161140268633764950754385 2370855201475323713065789)
                    ·
                      refine ⟨889070700553246392399671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2370855201475323713065789 889070700553246392399671)
                      ·
                        rfl

theorem cell23_1731459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_1731459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731459 prefixEnd_1731459 := by exact prefixLift 1731459
  have htrace : WordTrace (prefixWord ++ tailWord_1731459) baseStart_1731459 baseEnd_1731459 := by
    simpa [prefixWord, tailWord_1731459, baseEnd_1731459] using wordTrace_append hprefix tailTrace_1731459
  have hstable : (prefixWord ++ tailWord_1731459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731459).length < 2 ^ (prefixWord ++ tailWord_1731459).sum := by decide
  have hdescent : baseEnd_1731459 < baseStart_1731459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731499 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 3, 3, 2]
def baseStart_1731499 : Nat := 118140960795 + 1731499 * 2 ^ 59
def prefixEnd_1731499 : Nat := 4983230072969 + 3 ^ 40 * 1731499 * 2
def baseEnd_1731499 : Nat := 889091239779426235899487

theorem tailTrace_1731499 : CollatzResearch.WordTrace tailWord_1731499 prefixEnd_1731499 889091239779426235899487 := by
  unfold tailWord_1731499
  simp only [CollatzResearch.WordTrace]
  refine ⟨63152956754082314331117551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42101971169388209554078367 63152956754082314331117551)
  ·
    refine ⟨94729435131123471496676327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63152956754082314331117551 94729435131123471496676327)
    ·
      refine ⟨142094152696685207245014491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94729435131123471496676327 142094152696685207245014491)
      ·
        refine ⟨213141229045027810867521737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142094152696685207245014491 213141229045027810867521737)
        ·
          refine ⟨159855921783770858150641303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213141229045027810867521737 159855921783770858150641303)
          ·
            refine ⟨239783882675656287225961955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159855921783770858150641303 239783882675656287225961955)
            ·
              refine ⟨359675824013484430838942933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239783882675656287225961955 359675824013484430838942933)
              ·
                refine ⟨8429902125316041347787725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 359675824013484430838942933 8429902125316041347787725)
                ·
                  refine ⟨3161213296993515505420397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8429902125316041347787725 3161213296993515505420397)
                  ·
                    refine ⟨1185454986372568314532649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161213296993515505420397 1185454986372568314532649)
                    ·
                      refine ⟨889091239779426235899487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185454986372568314532649 889091239779426235899487)
                      ·
                        rfl

theorem cell23_1731499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3, 2].length) (baseStart_1731499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731499 prefixEnd_1731499 := by exact prefixLift 1731499
  have htrace : WordTrace (prefixWord ++ tailWord_1731499) baseStart_1731499 baseEnd_1731499 := by
    simpa [prefixWord, tailWord_1731499, baseEnd_1731499] using wordTrace_append hprefix tailTrace_1731499
  have hstable : (prefixWord ++ tailWord_1731499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731499).length < 2 ^ (prefixWord ++ tailWord_1731499).sum := by decide
  have hdescent : baseEnd_1731499 < baseStart_1731499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731546 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2]
def baseStart_1731546 : Nat := 118140960795 + 1731546 * 2 ^ 59
def prefixEnd_1731546 : Nat := 4983230072969 + 3 ^ 40 * 1731546 * 2
def baseEnd_1731546 : Nat := 889115373370187552011771

theorem tailTrace_1731546 : CollatzResearch.WordTrace tailWord_1731546 prefixEnd_1731546 889115373370187552011771 := by
  unfold tailWord_1731546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788667746228010339519623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42103113989941360905385661 15788667746228010339519623)
  ·
    refine ⟨23683001619342015509279435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15788667746228010339519623 23683001619342015509279435)
    ·
      refine ⟨35524502429013023263919153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23683001619342015509279435 35524502429013023263919153)
      ·
        refine ⟨26643376821759767447939365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35524502429013023263919153 26643376821759767447939365)
        ·
          refine ⟨4995633154079956396488631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26643376821759767447939365 4995633154079956396488631)
          ·
            refine ⟨7493449731119934594732947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995633154079956396488631 7493449731119934594732947)
            ·
              refine ⟨11240174596679901892099421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7493449731119934594732947 11240174596679901892099421)
              ·
                refine ⟨4215065473754963209537283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11240174596679901892099421 4215065473754963209537283)
                ·
                  refine ⟨6322598210632444814305925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215065473754963209537283 6322598210632444814305925)
                  ·
                    refine ⟨1185487164493583402682361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322598210632444814305925 1185487164493583402682361)
                    ·
                      refine ⟨889115373370187552011771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185487164493583402682361 889115373370187552011771)
                      ·
                        rfl

theorem cell23_1731546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_1731546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731546 prefixEnd_1731546 := by exact prefixLift 1731546
  have htrace : WordTrace (prefixWord ++ tailWord_1731546) baseStart_1731546 baseEnd_1731546 := by
    simpa [prefixWord, tailWord_1731546, baseEnd_1731546] using wordTrace_append hprefix tailTrace_1731546
  have hstable : (prefixWord ++ tailWord_1731546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731546).length < 2 ^ (prefixWord ++ tailWord_1731546).sum := by decide
  have hdescent : baseEnd_1731546 < baseStart_1731546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731580 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_1731580 : Nat := 118140960795 + 1731580 * 2 ^ 59
def prefixEnd_1731580 : Nat := 4983230072969 + 3 ^ 40 * 1731580 * 2
def baseEnd_1731580 : Nat := 889132831712440418986615

theorem tailTrace_1731580 : CollatzResearch.WordTrace tailWord_1731580 prefixEnd_1731580 889132831712440418986615 := by
  unfold tailWord_1731580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31577955533394432582408097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42103940711192576776544129 31577955533394432582408097)
  ·
    refine ⟨23683466650045824436806073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31577955533394432582408097 23683466650045824436806073)
    ·
      refine ⟨17762599987534368327604555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23683466650045824436806073 17762599987534368327604555)
      ·
        refine ⟨26643899981301552491406833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17762599987534368327604555 26643899981301552491406833)
        ·
          refine ⟨19982924985976164368555125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26643899981301552491406833 19982924985976164368555125)
          ·
            refine ⟨1873399217435265409552043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19982924985976164368555125 1873399217435265409552043)
            ·
              refine ⟨2810098826152898114328065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873399217435265409552043 2810098826152898114328065)
              ·
                refine ⟨2107574119614673585746049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810098826152898114328065 2107574119614673585746049)
                ·
                  refine ⟨1580680589711005189309537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2107574119614673585746049 1580680589711005189309537)
                  ·
                    refine ⟨1185510442283253891982153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1580680589711005189309537 1185510442283253891982153)
                    ·
                      refine ⟨889132831712440418986615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185510442283253891982153 889132831712440418986615)
                      ·
                        rfl

theorem cell23_1731580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_1731580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731580 prefixEnd_1731580 := by exact prefixLift 1731580
  have htrace : WordTrace (prefixWord ++ tailWord_1731580) baseStart_1731580 baseEnd_1731580 := by
    simpa [prefixWord, tailWord_1731580, baseEnd_1731580] using wordTrace_append hprefix tailTrace_1731580
  have hstable : (prefixWord ++ tailWord_1731580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731580).length < 2 ^ (prefixWord ++ tailWord_1731580).sum := by decide
  have hdescent : baseEnd_1731580 < baseStart_1731580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731619 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1731619 : Nat := 118140960795 + 1731619 * 2 ^ 59
def prefixEnd_1731619 : Nat := 4983230072969 + 3 ^ 40 * 1731619 * 2
def baseEnd_1731619 : Nat := 889152857457965766398935

theorem tailTrace_1731619 : CollatzResearch.WordTrace tailWord_1731619 prefixEnd_1731619 889152857457965766398935 := by
  unfold tailWord_1731619
  simp only [CollatzResearch.WordTrace]
  refine ⟨63157333513647574825485911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42104889009098383216990607 63157333513647574825485911)
  ·
    refine ⟨94736000270471362238228867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63157333513647574825485911 94736000270471362238228867)
    ·
      refine ⟨142104000405707043357343301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94736000270471362238228867 142104000405707043357343301)
      ·
        refine ⟨26644500076070070629501869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142104000405707043357343301 26644500076070070629501869)
        ·
          refine ⟨9991687528526276486063201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26644500076070070629501869 9991687528526276486063201)
          ·
            refine ⟨7493765646394707364547401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9991687528526276486063201 7493765646394707364547401)
            ·
              refine ⟨5620324234796030523410551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493765646394707364547401 5620324234796030523410551)
              ·
                refine ⟨8430486352194045785115827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620324234796030523410551 8430486352194045785115827)
                ·
                  refine ⟨12645729528291068677673741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8430486352194045785115827 12645729528291068677673741)
                  ·
                    refine ⟨4742148573109150754127653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12645729528291068677673741 4742148573109150754127653)
                    ·
                      refine ⟨889152857457965766398935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4742148573109150754127653 889152857457965766398935)
                      ·
                        rfl

theorem cell23_1731619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1731619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731619 prefixEnd_1731619 := by exact prefixLift 1731619
  have htrace : WordTrace (prefixWord ++ tailWord_1731619) baseStart_1731619 baseEnd_1731619 := by
    simpa [prefixWord, tailWord_1731619, baseEnd_1731619] using wordTrace_append hprefix tailTrace_1731619
  have hstable : (prefixWord ++ tailWord_1731619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731619).length < 2 ^ (prefixWord ++ tailWord_1731619).sum := by decide
  have hdescent : baseEnd_1731619 < baseStart_1731619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731720 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1731720 : Nat := 118140960795 + 1731720 * 2 ^ 59
def prefixEnd_1731720 : Nat := 4983230072969 + 3 ^ 40 * 1731720 * 2
def baseEnd_1731720 : Nat := 889204719004069871235971

theorem tailTrace_1731720 : CollatzResearch.WordTrace tailWord_1731720 prefixEnd_1731720 889204719004069871235971 := by
  unfold tailWord_1731720
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580508643140834537456307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42107344857521112716608409 31580508643140834537456307)
  ·
    refine ⟨47370762964711251806184461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31580508643140834537456307 47370762964711251806184461)
    ·
      refine ⟨17764036111766719427319173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47370762964711251806184461 17764036111766719427319173)
      ·
        refine ⟨3330756770956259892622345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17764036111766719427319173 3330756770956259892622345)
        ·
          refine ⟨2498067578217194919466759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3330756770956259892622345 2498067578217194919466759)
          ·
            refine ⟨3747101367325792379200139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498067578217194919466759 3747101367325792379200139)
            ·
              refine ⟨5620652050988688568800209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747101367325792379200139 5620652050988688568800209)
              ·
                refine ⟨4215489038241516426600157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620652050988688568800209 4215489038241516426600157)
                ·
                  refine ⟨1580808389340568659975059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4215489038241516426600157 1580808389340568659975059)
                  ·
                    refine ⟨2371212584010852989962589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1580808389340568659975059 2371212584010852989962589)
                    ·
                      refine ⟨889204719004069871235971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2371212584010852989962589 889204719004069871235971)
                      ·
                        rfl

theorem cell23_1731720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1731720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731720 prefixEnd_1731720 := by exact prefixLift 1731720
  have htrace : WordTrace (prefixWord ++ tailWord_1731720) baseStart_1731720 baseEnd_1731720 := by
    simpa [prefixWord, tailWord_1731720, baseEnd_1731720] using wordTrace_append hprefix tailTrace_1731720
  have hstable : (prefixWord ++ tailWord_1731720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731720).length < 2 ^ (prefixWord ++ tailWord_1731720).sum := by decide
  have hdescent : baseEnd_1731720 < baseStart_1731720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731730 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_1731730 : Nat := 118140960795 + 1731730 * 2 ^ 59
def prefixEnd_1731730 : Nat := 4983230072969 + 3 ^ 40 * 1731730 * 2
def baseEnd_1731730 : Nat := 889209853810614832110925

theorem tailTrace_1731730 : CollatzResearch.WordTrace tailWord_1731730 prefixEnd_1731730 889209853810614832110925 := by
  unfold tailWord_1731730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15790345504061360195694161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42107588010830293855184429 15790345504061360195694161)
  ·
    refine ⟨11842759128046020146770621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15790345504061360195694161 11842759128046020146770621)
    ·
      refine ⟨4441034673017257555038983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11842759128046020146770621 4441034673017257555038983)
      ·
        refine ⟨6661552009525886332558475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441034673017257555038983 6661552009525886332558475)
        ·
          refine ⟨9992328014288829498837713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661552009525886332558475 9992328014288829498837713)
          ·
            refine ⟨7494246010716622124128285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9992328014288829498837713 7494246010716622124128285)
            ·
              refine ⟨2810342254018733296548107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7494246010716622124128285 2810342254018733296548107)
              ·
                refine ⟨4215513381028099944822161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810342254018733296548107 4215513381028099944822161)
                ·
                  refine ⟨3161635035771074958616621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4215513381028099944822161 3161635035771074958616621)
                  ·
                    refine ⟨1185613138414153109481233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161635035771074958616621 1185613138414153109481233)
                    ·
                      refine ⟨889209853810614832110925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185613138414153109481233 889209853810614832110925)
                      ·
                        rfl

theorem cell23_1731730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_1731730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731730 prefixEnd_1731730 := by exact prefixLift 1731730
  have htrace : WordTrace (prefixWord ++ tailWord_1731730) baseStart_1731730 baseEnd_1731730 := by
    simpa [prefixWord, tailWord_1731730, baseEnd_1731730] using wordTrace_append hprefix tailTrace_1731730
  have hstable : (prefixWord ++ tailWord_1731730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731730).length < 2 ^ (prefixWord ++ tailWord_1731730).sum := by decide
  have hdescent : baseEnd_1731730 < baseStart_1731730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731736 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 1, 6]
def baseStart_1731736 : Nat := 118140960795 + 1731736 * 2 ^ 59
def prefixEnd_1731736 : Nat := 4983230072969 + 3 ^ 40 * 1731736 * 2
def baseEnd_1731736 : Nat := 296404311564847269545299

theorem tailTrace_1731736 : CollatzResearch.WordTrace tailWord_1731736 prefixEnd_1731736 296404311564847269545299 := by
  unfold tailWord_1731736
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580800427111851903747531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42107733902815802538330041 31580800427111851903747531)
  ·
    refine ⟨47371200640667777855621297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31580800427111851903747531 47371200640667777855621297)
    ·
      refine ⟨35528400480500833391715973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47371200640667777855621297 35528400480500833391715973)
      ·
        refine ⟨6661575090093906260946745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35528400480500833391715973 6661575090093906260946745)
        ·
          refine ⟨4996181317570429695710059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6661575090093906260946745 4996181317570429695710059)
          ·
            refine ⟨7494271976355644543565089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996181317570429695710059 7494271976355644543565089)
            ·
              refine ⟨5620703982266733407673817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7494271976355644543565089 5620703982266733407673817)
              ·
                refine ⟨4215527986700050055755363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620703982266733407673817 4215527986700050055755363)
                ·
                  refine ⟨6323291980050075083633045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215527986700050055755363 6323291980050075083633045)
                  ·
                    refine ⟨296404311564847269545299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6323291980050075083633045 296404311564847269545299)
                    ·
                      rfl

theorem cell23_1731736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_1731736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731736 prefixEnd_1731736 := by exact prefixLift 1731736
  have htrace : WordTrace (prefixWord ++ tailWord_1731736) baseStart_1731736 baseEnd_1731736 := by
    simpa [prefixWord, tailWord_1731736, baseEnd_1731736] using wordTrace_append hprefix tailTrace_1731736
  have hstable : (prefixWord ++ tailWord_1731736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731736).length < 2 ^ (prefixWord ++ tailWord_1731736).sum := by decide
  have hdescent : baseEnd_1731736 < baseStart_1731736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731740 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1731740 : Nat := 118140960795 + 1731740 * 2 ^ 59
def prefixEnd_1731740 : Nat := 4983230072969 + 3 ^ 40 * 1731740 * 2
def baseEnd_1731740 : Nat := 296404996205719930995293

theorem tailTrace_1731740 : CollatzResearch.WordTrace tailWord_1731740 prefixEnd_1731740 296404996205719930995293 := by
  unfold tailWord_1731740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580873373104606245320337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42107831164139474993760449 31580873373104606245320337)
  ·
    refine ⟨23685655029828454683990253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31580873373104606245320337 23685655029828454683990253)
    ·
      refine ⟨8882120636185670506496345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23685655029828454683990253 8882120636185670506496345)
      ·
        refine ⟨6661590477139252879872259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8882120636185670506496345 6661590477139252879872259)
        ·
          refine ⟨9992385715708879319808389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661590477139252879872259 9992385715708879319808389)
          ·
            refine ⟨1873572321695414872464073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9992385715708879319808389 1873572321695414872464073)
            ·
              refine ⟨1405179241271561154348055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873572321695414872464073 1405179241271561154348055)
              ·
                refine ⟨2107768861907341731522083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405179241271561154348055 2107768861907341731522083)
                ·
                  refine ⟨3161653292861012597283125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107768861907341731522083 3161653292861012597283125)
                  ·
                    refine ⟨296404996205719930995293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3161653292861012597283125 296404996205719930995293)
                    ·
                      rfl

theorem cell23_1731740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1731740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731740 prefixEnd_1731740 := by exact prefixLift 1731740
  have htrace : WordTrace (prefixWord ++ tailWord_1731740) baseStart_1731740 baseEnd_1731740 := by
    simpa [prefixWord, tailWord_1731740, baseEnd_1731740] using wordTrace_append hprefix tailTrace_1731740
  have hstable : (prefixWord ++ tailWord_1731740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731740).length < 2 ^ (prefixWord ++ tailWord_1731740).sum := by decide
  have hdescent : baseEnd_1731740 < baseStart_1731740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731749 : List Nat := [1, 3, 1, 2, 1, 5, 10]
def baseStart_1731749 : Nat := 118140960795 + 1731749 * 2 ^ 59
def prefixEnd_1731749 : Nat := 4983230072969 + 3 ^ 40 * 1731749 * 2
def baseEnd_1731749 : Nat := 10978019875840126639177

theorem tailTrace_1731749 : CollatzResearch.WordTrace tailWord_1731749 prefixEnd_1731749 10978019875840126639177 := by
  unfold tailWord_1731749
  simp only [CollatzResearch.WordTrace]
  refine ⟨63162075003176607027718301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42108050002117738018478867 63162075003176607027718301)
  ·
    refine ⟨23685778126191227635394363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63162075003176607027718301 23685778126191227635394363)
    ·
      refine ⟨35528667189286841453091545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23685778126191227635394363 35528667189286841453091545)
      ·
        refine ⟨26646500391965131089818659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35528667189286841453091545 26646500391965131089818659)
        ·
          refine ⟨39969750587947696634727989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26646500391965131089818659 39969750587947696634727989)
          ·
            refine ⟨3747164117620096559505749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39969750587947696634727989 3747164117620096559505749)
            ·
              refine ⟨10978019875840126639177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3747164117620096559505749 10978019875840126639177)
              ·
                rfl

theorem cell23_1731749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 10].length) (baseStart_1731749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731749 prefixEnd_1731749 := by exact prefixLift 1731749
  have htrace : WordTrace (prefixWord ++ tailWord_1731749) baseStart_1731749 baseEnd_1731749 := by
    simpa [prefixWord, tailWord_1731749, baseEnd_1731749] using wordTrace_append hprefix tailTrace_1731749
  have hstable : (prefixWord ++ tailWord_1731749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731749).length < 2 ^ (prefixWord ++ tailWord_1731749).sum := by decide
  have hdescent : baseEnd_1731749 < baseStart_1731749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731777 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1731777 : Nat := 118140960795 + 1731777 * 2 ^ 59
def prefixEnd_1731777 : Nat := 4983230072969 + 3 ^ 40 * 1731777 * 2
def baseEnd_1731777 : Nat := 889233987401376148223209

theorem tailTrace_1731777 : CollatzResearch.WordTrace tailWord_1731777 prefixEnd_1731777 889233987401376148223209 := by
  unfold tailWord_1731777
  simp only [CollatzResearch.WordTrace]
  refine ⟨63163096247075167809737585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42108730831383445206491723 63163096247075167809737585)
  ·
    refine ⟨47372322185306375857303189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63163096247075167809737585 47372322185306375857303189)
    ·
      refine ⟨2220577602436236368311087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47372322185306375857303189 2220577602436236368311087)
      ·
        refine ⟨3330866403654354552466631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220577602436236368311087 3330866403654354552466631)
        ·
          refine ⟨4996299605481531828699947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330866403654354552466631 4996299605481531828699947)
          ·
            refine ⟨7494449408222297743049921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996299605481531828699947 7494449408222297743049921)
            ·
              refine ⟨5620837056166723307287441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7494449408222297743049921 5620837056166723307287441)
              ·
                refine ⟨4215627792125042480465581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620837056166723307287441 4215627792125042480465581)
                ·
                  refine ⟨1580860422046890930174593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4215627792125042480465581 1580860422046890930174593)
                  ·
                    refine ⟨1185645316535168197630945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1580860422046890930174593 1185645316535168197630945)
                    ·
                      refine ⟨889233987401376148223209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185645316535168197630945 889233987401376148223209)
                      ·
                        rfl

theorem cell23_1731777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1731777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731777 prefixEnd_1731777 := by exact prefixLift 1731777
  have htrace : WordTrace (prefixWord ++ tailWord_1731777) baseStart_1731777 baseEnd_1731777 := by
    simpa [prefixWord, tailWord_1731777, baseEnd_1731777] using wordTrace_append hprefix tailTrace_1731777
  have hstable : (prefixWord ++ tailWord_1731777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731777).length < 2 ^ (prefixWord ++ tailWord_1731777).sum := by decide
  have hdescent : baseEnd_1731777 < baseStart_1731777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731816 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1731816 : Nat := 118140960795 + 1731816 * 2 ^ 59
def prefixEnd_1731816 : Nat := 4983230072969 + 3 ^ 40 * 1731816 * 2
def baseEnd_1731816 : Nat := 889254013146901495635529

theorem tailTrace_1731816 : CollatzResearch.WordTrace tailWord_1731816 prefixEnd_1731816 889254013146901495635529 := by
  unfold tailWord_1731816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31582259346966938735203651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42109679129289251646938201 31582259346966938735203651)
  ·
    refine ⟨47373389020450408102805477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31582259346966938735203651 47373389020450408102805477)
    ·
      refine ⟨8882510441334451519276027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47373389020450408102805477 8882510441334451519276027)
      ·
        refine ⟨13323765662001677278914041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8882510441334451519276027 13323765662001677278914041)
        ·
          refine ⟨9992824246501257959185531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13323765662001677278914041 9992824246501257959185531)
          ·
            refine ⟨14989236369751886938778297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9992824246501257959185531 14989236369751886938778297)
            ·
              refine ⟨11241927277313915204083723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14989236369751886938778297 11241927277313915204083723)
              ·
                refine ⟨16862890915970872806125585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11241927277313915204083723 16862890915970872806125585)
                ·
                  refine ⟨12647168186978154604594189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16862890915970872806125585 12647168186978154604594189)
                  ·
                    refine ⟨4742688070116807976722821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12647168186978154604594189 4742688070116807976722821)
                    ·
                      refine ⟨889254013146901495635529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4742688070116807976722821 889254013146901495635529)
                      ·
                        rfl

theorem cell23_1731816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1731816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731816 prefixEnd_1731816 := by exact prefixLift 1731816
  have htrace : WordTrace (prefixWord ++ tailWord_1731816) baseStart_1731816 baseEnd_1731816 := by
    simpa [prefixWord, tailWord_1731816, baseEnd_1731816] using wordTrace_append hprefix tailTrace_1731816
  have hstable : (prefixWord ++ tailWord_1731816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731816).length < 2 ^ (prefixWord ++ tailWord_1731816).sum := by decide
  have hdescent : baseEnd_1731816 < baseStart_1731816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731827 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 2, 1, 3]
def baseStart_1731827 : Nat := 118140960795 + 1731827 * 2 ^ 59
def prefixEnd_1731827 : Nat := 4983230072969 + 3 ^ 40 * 1731827 * 2
def baseEnd_1731827 : Nat := 889259661434100952597979

theorem tailTrace_1731827 : CollatzResearch.WordTrace tailWord_1731827 prefixEnd_1731827 889259661434100952597979 := by
  unfold tailWord_1731827
  simp only [CollatzResearch.WordTrace]
  refine ⟨63164919896894026349057735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42109946597929350899371823 63164919896894026349057735)
  ·
    refine ⟨94747379845341039523586603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63164919896894026349057735 94747379845341039523586603)
    ·
      refine ⟨142121069768011559285379905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94747379845341039523586603 142121069768011559285379905)
      ·
        refine ⟨106590802326008669464034929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142121069768011559285379905 106590802326008669464034929)
        ·
          refine ⟨79943101744506502098026197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106590802326008669464034929 79943101744506502098026197)
          ·
            refine ⟨1873666447136871142922489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 79943101744506502098026197 1873666447136871142922489)
            ·
              refine ⟨1405249835352653357191867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873666447136871142922489 1405249835352653357191867)
              ·
                refine ⟨2107874753028980035787801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405249835352653357191867 2107874753028980035787801)
                ·
                  refine ⟨1580906064771735026840851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2107874753028980035787801 1580906064771735026840851)
                  ·
                    refine ⟨2371359097157602540261277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1580906064771735026840851 2371359097157602540261277)
                    ·
                      refine ⟨889259661434100952597979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2371359097157602540261277 889259661434100952597979)
                      ·
                        rfl

theorem cell23_1731827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 1, 3].length) (baseStart_1731827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731827 prefixEnd_1731827 := by exact prefixLift 1731827
  have htrace : WordTrace (prefixWord ++ tailWord_1731827) baseStart_1731827 baseEnd_1731827 := by
    simpa [prefixWord, tailWord_1731827, baseEnd_1731827] using wordTrace_append hprefix tailTrace_1731827
  have hstable : (prefixWord ++ tailWord_1731827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731827).length < 2 ^ (prefixWord ++ tailWord_1731827).sum := by decide
  have hdescent : baseEnd_1731827 < baseStart_1731827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731833 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 1, 4, 2]
def baseStart_1731833 : Nat := 118140960795 + 1731833 * 2 ^ 59
def prefixEnd_1731833 : Nat := 4983230072969 + 3 ^ 40 * 1731833 * 2
def baseEnd_1731833 : Nat := 889262742318027929122951

theorem tailTrace_1731833 : CollatzResearch.WordTrace tailWord_1731833 prefixEnd_1731833 889262742318027929122951 := by
  unfold tailWord_1731833
  simp only [CollatzResearch.WordTrace]
  refine ⟨63165138734872289373776153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42110092489914859582517435 63165138734872289373776153)
  ·
    refine ⟨47373854051154217030332115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63165138734872289373776153 47373854051154217030332115)
    ·
      refine ⟨71060781076731325545498173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47373854051154217030332115 71060781076731325545498173)
      ·
        refine ⟨26647792903774247079561815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71060781076731325545498173 26647792903774247079561815)
        ·
          refine ⟨39971689355661370619342723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26647792903774247079561815 39971689355661370619342723)
          ·
            refine ⟨59957534033492055929014085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39971689355661370619342723 59957534033492055929014085)
            ·
              refine ⟨11242037631279760486690141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59957534033492055929014085 11242037631279760486690141)
              ·
                refine ⟨4215764111729910182508803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11242037631279760486690141 4215764111729910182508803)
                ·
                  refine ⟨6323646167594865273763205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215764111729910182508803 6323646167594865273763205)
                  ·
                    refine ⟨1185683656424037238830601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6323646167594865273763205 1185683656424037238830601)
                    ·
                      refine ⟨889262742318027929122951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185683656424037238830601 889262742318027929122951)
                      ·
                        rfl

theorem cell23_1731833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_1731833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731833 prefixEnd_1731833 := by exact prefixLift 1731833
  have htrace : WordTrace (prefixWord ++ tailWord_1731833) baseStart_1731833 baseEnd_1731833 := by
    simpa [prefixWord, tailWord_1731833, baseEnd_1731833] using wordTrace_append hprefix tailTrace_1731833
  have hstable : (prefixWord ++ tailWord_1731833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731833).length < 2 ^ (prefixWord ++ tailWord_1731833).sum := by decide
  have hdescent : baseEnd_1731833 < baseStart_1731833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731903 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 2, 5]
def baseStart_1731903 : Nat := 118140960795 + 1731903 * 2 ^ 59
def prefixEnd_1731903 : Nat := 4983230072969 + 3 ^ 40 * 1731903 * 2
def baseEnd_1731903 : Nat := 296432895321280885082543

theorem tailTrace_1731903 : CollatzResearch.WordTrace tailWord_1731903 prefixEnd_1731903 296432895321280885082543 := by
  unfold tailWord_1731903
  simp only [CollatzResearch.WordTrace]
  refine ⟨63167691844618691328824363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42111794563079127552549575 63167691844618691328824363)
  ·
    refine ⟨94751537766928036993236545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63167691844618691328824363 94751537766928036993236545)
    ·
      refine ⟨71063653325196027744927409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94751537766928036993236545 71063653325196027744927409)
      ·
        refine ⟨53297739993897020808695557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71063653325196027744927409 53297739993897020808695557)
        ·
          refine ⟨9993326248855691401630417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53297739993897020808695557 9993326248855691401630417)
          ·
            refine ⟨7494994686641768551222813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9993326248855691401630417 7494994686641768551222813)
            ·
              refine ⟨2810623007490663206708555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7494994686641768551222813 2810623007490663206708555)
              ·
                refine ⟨4215934511235994810062833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810623007490663206708555 4215934511235994810062833)
                ·
                  refine ⟨3161950883426996107547125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4215934511235994810062833 3161950883426996107547125)
                  ·
                    refine ⟨296432895321280885082543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3161950883426996107547125 296432895321280885082543)
                    ·
                      rfl

theorem cell23_1731903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_1731903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731903 prefixEnd_1731903 := by exact prefixLift 1731903
  have htrace : WordTrace (prefixWord ++ tailWord_1731903) baseStart_1731903 baseEnd_1731903 := by
    simpa [prefixWord, tailWord_1731903, baseEnd_1731903] using wordTrace_append hprefix tailTrace_1731903
  have hstable : (prefixWord ++ tailWord_1731903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731903).length < 2 ^ (prefixWord ++ tailWord_1731903).sum := by decide
  have hdescent : baseEnd_1731903 < baseStart_1731903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731923 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 4, 4, 2]
def baseStart_1731923 : Nat := 118140960795 + 1731923 * 2 ^ 59
def prefixEnd_1731923 : Nat := 4983230072969 + 3 ^ 40 * 1731923 * 2
def baseEnd_1731923 : Nat := 889308955576932576997537

theorem tailTrace_1731923 : CollatzResearch.WordTrace tailWord_1731923 prefixEnd_1731923 889308955576932576997537 := by
  unfold tailWord_1731923
  simp only [CollatzResearch.WordTrace]
  refine ⟨63168421304546234744552423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42112280869697489829701615 63168421304546234744552423)
  ·
    refine ⟨94752631956819352116828635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63168421304546234744552423 94752631956819352116828635)
    ·
      refine ⟨142128947935229028175242953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94752631956819352116828635 142128947935229028175242953)
      ·
        refine ⟨106596710951421771131432215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142128947935229028175242953 106596710951421771131432215)
        ·
          refine ⟨159895066427132656697148323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106596710951421771131432215 159895066427132656697148323)
          ·
            refine ⟨239842599640698985045722485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159895066427132656697148323 239842599640698985045722485)
            ·
              refine ⟨22485243716315529848036483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239842599640698985045722485 22485243716315529848036483)
              ·
                refine ⟨33727865574473294772054725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22485243716315529848036483 33727865574473294772054725)
                ·
                  refine ⟨6323974795213742769760261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33727865574473294772054725 6323974795213742769760261)
                  ·
                    refine ⟨1185745274102576769330049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6323974795213742769760261 1185745274102576769330049)
                    ·
                      refine ⟨889308955576932576997537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185745274102576769330049 889308955576932576997537)
                      ·
                        rfl

theorem cell23_1731923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4, 2].length) (baseStart_1731923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731923 prefixEnd_1731923 := by exact prefixLift 1731923
  have htrace : WordTrace (prefixWord ++ tailWord_1731923) baseStart_1731923 baseEnd_1731923 := by
    simpa [prefixWord, tailWord_1731923, baseEnd_1731923] using wordTrace_append hprefix tailTrace_1731923
  have hstable : (prefixWord ++ tailWord_1731923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731923).length < 2 ^ (prefixWord ++ tailWord_1731923).sum := by decide
  have hdescent : baseEnd_1731923 < baseStart_1731923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731940 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_1731940 : Nat := 118140960795 + 1731940 * 2 ^ 59
def prefixEnd_1731940 : Nat := 4983230072969 + 3 ^ 40 * 1731940 * 2
def baseEnd_1731940 : Nat := 889317684748059010484959

theorem tailTrace_1731940 : CollatzResearch.WordTrace tailWord_1731940 prefixEnd_1731940 889317684748059010484959 := by
  unfold tailWord_1731940
  simp only [CollatzResearch.WordTrace]
  refine ⟨31584520672742323323960637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42112694230323097765280849 31584520672742323323960637)
  ·
    refine ⟨11844195252278371246485239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31584520672742323323960637 11844195252278371246485239)
    ·
      refine ⟨17766292878417556869727859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11844195252278371246485239 17766292878417556869727859)
      ·
        refine ⟨26649439317626335304591789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17766292878417556869727859 26649439317626335304591789)
        ·
          refine ⟨9993539744109875739221921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26649439317626335304591789 9993539744109875739221921)
          ·
            refine ⟨7495154808082406804416441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9993539744109875739221921 7495154808082406804416441)
            ·
              refine ⟨5621366106061805103312331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495154808082406804416441 5621366106061805103312331)
              ·
                refine ⟨8432049159092707654968497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621366106061805103312331 8432049159092707654968497)
                ·
                  refine ⟨6324036869319530741226373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432049159092707654968497 6324036869319530741226373)
                  ·
                    refine ⟨1185756912997412013979945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324036869319530741226373 1185756912997412013979945)
                    ·
                      refine ⟨889317684748059010484959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185756912997412013979945 889317684748059010484959)
                      ·
                        rfl

theorem cell23_1731940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_1731940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731940 prefixEnd_1731940 := by exact prefixLift 1731940
  have htrace : WordTrace (prefixWord ++ tailWord_1731940) baseStart_1731940 baseEnd_1731940 := by
    simpa [prefixWord, tailWord_1731940, baseEnd_1731940] using wordTrace_append hprefix tailTrace_1731940
  have hstable : (prefixWord ++ tailWord_1731940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731940).length < 2 ^ (prefixWord ++ tailWord_1731940).sum := by decide
  have hdescent : baseEnd_1731940 < baseStart_1731940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731983 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 11, 2]
def baseStart_1731983 : Nat := 118140960795 + 1731983 * 2 ^ 59
def prefixEnd_1731983 : Nat := 4983230072969 + 3 ^ 40 * 1731983 * 2
def baseEnd_1731983 : Nat := 889339764416202342247261

theorem tailTrace_1731983 : CollatzResearch.WordTrace tailWord_1731983 prefixEnd_1731983 889339764416202342247261 := by
  unfold tailWord_1731983
  simp only [CollatzResearch.WordTrace]
  refine ⟨63170609684328864991736603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42113739789552576661157735 63170609684328864991736603)
  ·
    refine ⟨94755914526493297487604905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63170609684328864991736603 94755914526493297487604905)
    ·
      refine ⟨71066935894869973115703679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94755914526493297487604905 71066935894869973115703679)
      ·
        refine ⟨106600403842304959673555519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71066935894869973115703679 106600403842304959673555519)
        ·
          refine ⟨159900605763457439510333279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106600403842304959673555519 159900605763457439510333279)
          ·
            refine ⟨239850908645186159265499919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159900605763457439510333279 239850908645186159265499919)
            ·
              refine ⟨359776362967779238898249879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239850908645186159265499919 359776362967779238898249879)
              ·
                refine ⟨539664544451668858347374819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359776362967779238898249879 539664544451668858347374819)
                ·
                  refine ⟨809496816677503287521062229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539664544451668858347374819 809496816677503287521062229)
                  ·
                    refine ⟨1185786352554936456329681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 809496816677503287521062229 1185786352554936456329681)
                    ·
                      refine ⟨889339764416202342247261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185786352554936456329681 889339764416202342247261)
                      ·
                        rfl

theorem cell23_1731983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11, 2].length) (baseStart_1731983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731983 prefixEnd_1731983 := by exact prefixLift 1731983
  have htrace : WordTrace (prefixWord ++ tailWord_1731983) baseStart_1731983 baseEnd_1731983 := by
    simpa [prefixWord, tailWord_1731983, baseEnd_1731983] using wordTrace_append hprefix tailTrace_1731983
  have hstable : (prefixWord ++ tailWord_1731983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731983).length < 2 ^ (prefixWord ++ tailWord_1731983).sum := by decide
  have hdescent : baseEnd_1731983 < baseStart_1731983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731997 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 6]
def baseStart_1731997 : Nat := 118140960795 + 1731997 * 2 ^ 59
def prefixEnd_1731997 : Nat := 4983230072969 + 3 ^ 40 * 1731997 * 2
def baseEnd_1731997 : Nat := 98816328127262809719133

theorem tailTrace_1731997 : CollatzResearch.WordTrace tailWord_1731997 prefixEnd_1731997 98816328127262809719133 := by
  unfold tailWord_1731997
  simp only [CollatzResearch.WordTrace]
  refine ⟨63171120306278145382746245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42114080204185430255164163 63171120306278145382746245)
  ·
    refine ⟨11844585057427152259264921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63171120306278145382746245 11844585057427152259264921)
    ·
      refine ⟨8883438793070364194448691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11844585057427152259264921 8883438793070364194448691)
      ·
        refine ⟨13325158189605546291673037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8883438793070364194448691 13325158189605546291673037)
        ·
          refine ⟨4996934321102079859377389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13325158189605546291673037 4996934321102079859377389)
          ·
            refine ⟨1873850370413279947266521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4996934321102079859377389 1873850370413279947266521)
            ·
              refine ⟨1405387777809959960449891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873850370413279947266521 1405387777809959960449891)
              ·
                refine ⟨2108081666714939940674837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405387777809959960449891 2108081666714939940674837)
                ·
                  refine ⟨98816328127262809719133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2108081666714939940674837 98816328127262809719133)
                  ·
                    rfl

theorem cell23_1731997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_1731997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1731997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1731997 prefixEnd_1731997 := by exact prefixLift 1731997
  have htrace : WordTrace (prefixWord ++ tailWord_1731997) baseStart_1731997 baseEnd_1731997 := by
    simpa [prefixWord, tailWord_1731997, baseEnd_1731997] using wordTrace_append hprefix tailTrace_1731997
  have hstable : (prefixWord ++ tailWord_1731997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731997).length < 2 ^ (prefixWord ++ tailWord_1731997).sum := by decide
  have hdescent : baseEnd_1731997 < baseStart_1731997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732000 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 4, 3, 2]
def baseStart_1732000 : Nat := 118140960795 + 1732000 * 2 ^ 59
def prefixEnd_1732000 : Nat := 4983230072969 + 3 ^ 40 * 1732000 * 2
def baseEnd_1732000 : Nat := 889348493587328775734683

theorem tailTrace_1732000 : CollatzResearch.WordTrace tailWord_1732000 prefixEnd_1732000 889348493587328775734683 := by
  unfold tailWord_1732000
  simp only [CollatzResearch.WordTrace]
  refine ⟨31585614862633638447552727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42114153150178184596736969 31585614862633638447552727)
  ·
    refine ⟨47378422293950457671329091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31585614862633638447552727 47378422293950457671329091)
    ·
      refine ⟨71067633440925686506993637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47378422293950457671329091 71067633440925686506993637)
      ·
        refine ⟨13325181270173566220061307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71067633440925686506993637 13325181270173566220061307)
        ·
          refine ⟨19987771905260349330091961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13325181270173566220061307 19987771905260349330091961)
          ·
            refine ⟨14990828928945261997568971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19987771905260349330091961 14990828928945261997568971)
            ·
              refine ⟨22486243393417892996353457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14990828928945261997568971 22486243393417892996353457)
              ·
                refine ⟨16864682545063419747265093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22486243393417892996353457 16864682545063419747265093)
                ·
                  refine ⟨3162127977199391202612205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16864682545063419747265093 3162127977199391202612205)
                  ·
                    refine ⟨1185797991449771700979577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162127977199391202612205 1185797991449771700979577)
                    ·
                      refine ⟨889348493587328775734683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185797991449771700979577 889348493587328775734683)
                      ·
                        rfl

theorem cell23_1732000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_1732000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732000 prefixEnd_1732000 := by exact prefixLift 1732000
  have htrace : WordTrace (prefixWord ++ tailWord_1732000) baseStart_1732000 baseEnd_1732000 := by
    simpa [prefixWord, tailWord_1732000, baseEnd_1732000] using wordTrace_append hprefix tailTrace_1732000
  have hstable : (prefixWord ++ tailWord_1732000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732000).length < 2 ^ (prefixWord ++ tailWord_1732000).sum := by decide
  have hdescent : baseEnd_1732000 < baseStart_1732000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732017 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1732017 : Nat := 118140960795 + 1732017 * 2 ^ 59
def prefixEnd_1732017 : Nat := 4983230072969 + 3 ^ 40 * 1732017 * 2
def baseEnd_1732017 : Nat := 889357222758455209222105

theorem tailTrace_1732017 : CollatzResearch.WordTrace tailWord_1732017 prefixEnd_1732017 889357222758455209222105 := by
  unfold tailWord_1732017
  simp only [CollatzResearch.WordTrace]
  refine ⟨63171849766205688798474305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42114566510803792532316203 63171849766205688798474305)
  ·
    refine ⟨47378887324654266598855729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63171849766205688798474305 47378887324654266598855729)
    ·
      refine ⟨35534165493490699949141797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47378887324654266598855729 35534165493490699949141797)
      ·
        refine ⟨6662656030029506240464087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35534165493490699949141797 6662656030029506240464087)
        ·
          refine ⟨9993984045044259360696131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662656030029506240464087 9993984045044259360696131)
          ·
            refine ⟨14990976067566389041044197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993984045044259360696131 14990976067566389041044197)
            ·
              refine ⟨2810808012668697945195787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14990976067566389041044197 2810808012668697945195787)
              ·
                refine ⟨4216212019003046917793681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810808012668697945195787 4216212019003046917793681)
                ·
                  refine ⟨3162159014252285188345261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216212019003046917793681 3162159014252285188345261)
                  ·
                    refine ⟨1185809630344606945629473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162159014252285188345261 1185809630344606945629473)
                    ·
                      refine ⟨889357222758455209222105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185809630344606945629473 889357222758455209222105)
                      ·
                        rfl

theorem cell23_1732017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1732017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732017 prefixEnd_1732017 := by exact prefixLift 1732017
  have htrace : WordTrace (prefixWord ++ tailWord_1732017) baseStart_1732017 baseEnd_1732017 := by
    simpa [prefixWord, tailWord_1732017, baseEnd_1732017] using wordTrace_append hprefix tailTrace_1732017
  have hstable : (prefixWord ++ tailWord_1732017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732017).length < 2 ^ (prefixWord ++ tailWord_1732017).sum := by decide
  have hdescent : baseEnd_1732017 < baseStart_1732017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732023 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 1, 6]
def baseStart_1732023 : Nat := 118140960795 + 1732023 * 2 ^ 59
def prefixEnd_1732023 : Nat := 4983230072969 + 3 ^ 40 * 1732023 * 2
def baseEnd_1732023 : Nat := 296453434547460728582359

theorem tailTrace_1732023 : CollatzResearch.WordTrace tailWord_1732023 prefixEnd_1732023 296453434547460728582359 := by
  unfold tailWord_1732023
  simp only [CollatzResearch.WordTrace]
  refine ⟨63172068604183951823192723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42114712402789301215461815 63172068604183951823192723)
  ·
    refine ⟨94758102906275927734789085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63172068604183951823192723 94758102906275927734789085)
    ·
      refine ⟨35534288589853472900545907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94758102906275927734789085 35534288589853472900545907)
      ·
        refine ⟨53301432884780209350818861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35534288589853472900545907 53301432884780209350818861)
        ·
          refine ⟨19988037331792578506557073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53301432884780209350818861 19988037331792578506557073)
          ·
            refine ⟨14991027998844433879917805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19988037331792578506557073 14991027998844433879917805)
            ·
              refine ⟨5621635499566662704969177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14991027998844433879917805 5621635499566662704969177)
              ·
                refine ⟨4216226624674997028726883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621635499566662704969177 4216226624674997028726883)
                ·
                  refine ⟨6324339937012495543090325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216226624674997028726883 6324339937012495543090325)
                  ·
                    refine ⟨296453434547460728582359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6324339937012495543090325 296453434547460728582359)
                    ·
                      rfl

theorem cell23_1732023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_1732023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732023 prefixEnd_1732023 := by exact prefixLift 1732023
  have htrace : WordTrace (prefixWord ++ tailWord_1732023) baseStart_1732023 baseEnd_1732023 := by
    simpa [prefixWord, tailWord_1732023, baseEnd_1732023] using wordTrace_append hprefix tailTrace_1732023
  have hstable : (prefixWord ++ tailWord_1732023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732023).length < 2 ^ (prefixWord ++ tailWord_1732023).sum := by decide
  have hdescent : baseEnd_1732023 < baseStart_1732023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732080 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3]
def baseStart_1732080 : Nat := 118140960795 + 1732080 * 2 ^ 59
def prefixEnd_1732080 : Nat := 4983230072969 + 3 ^ 40 * 1732080 * 2
def baseEnd_1732080 : Nat := 889389572039688462734315

theorem tailTrace_1732080 : CollatzResearch.WordTrace tailWord_1732080 prefixEnd_1732080 889389572039688462734315 := by
  unfold tailWord_1732080
  simp only [CollatzResearch.WordTrace]
  refine ⟨31587073782488725279008847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42116098376651633705345129 31587073782488725279008847)
  ·
    refine ⟨47380610673733087918513271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31587073782488725279008847 47380610673733087918513271)
    ·
      refine ⟨71070916010599631877769907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47380610673733087918513271 71070916010599631877769907)
      ·
        refine ⟨106606374015899447816654861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71070916010599631877769907 106606374015899447816654861)
        ·
          refine ⟨39977390255962292931245573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106606374015899447816654861 39977390255962292931245573)
          ·
            refine ⟨7495760672992929924608545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39977390255962292931245573 7495760672992929924608545)
            ·
              refine ⟨5621820504744697443456409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495760672992929924608545 5621820504744697443456409)
              ·
                refine ⟨4216365378558523082592307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621820504744697443456409 4216365378558523082592307)
                ·
                  refine ⟨6324548067837784623888461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216365378558523082592307 6324548067837784623888461)
                  ·
                    refine ⟨2371705525439169233958173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6324548067837784623888461 2371705525439169233958173)
                    ·
                      refine ⟨889389572039688462734315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2371705525439169233958173 889389572039688462734315)
                      ·
                        rfl

theorem cell23_1732080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_1732080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732080 prefixEnd_1732080 := by exact prefixLift 1732080
  have htrace : WordTrace (prefixWord ++ tailWord_1732080) baseStart_1732080 baseEnd_1732080 := by
    simpa [prefixWord, tailWord_1732080, baseEnd_1732080] using wordTrace_append hprefix tailTrace_1732080
  have hstable : (prefixWord ++ tailWord_1732080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732080).length < 2 ^ (prefixWord ++ tailWord_1732080).sum := by decide
  have hdescent : baseEnd_1732080 < baseStart_1732080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732081 : List Nat := [1, 2, 2, 2, 3, 3, 2, 3, 1, 2, 2]
def baseStart_1732081 : Nat := 118140960795 + 1732081 * 2 ^ 59
def prefixEnd_1732081 : Nat := 4983230072969 + 3 ^ 40 * 1732081 * 2
def baseEnd_1732081 : Nat := 889390085520342958821811

theorem tailTrace_1732081 : CollatzResearch.WordTrace tailWord_1732081 prefixEnd_1732081 889390085520342958821811 := by
  unfold tailWord_1732081
  simp only [CollatzResearch.WordTrace]
  refine ⟨63174184037973827728804097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42116122691982551819202731 63174184037973827728804097)
  ·
    refine ⟨47380638028480370796603073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63174184037973827728804097 47380638028480370796603073)
    ·
      refine ⟨35535478521360278097452305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47380638028480370796603073 35535478521360278097452305)
      ·
        refine ⟨26651608891020208573089229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35535478521360278097452305 26651608891020208573089229)
        ·
          refine ⟨9994353334132578214908461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26651608891020208573089229 9994353334132578214908461)
          ·
            refine ⟨3747882500299716830590673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9994353334132578214908461 3747882500299716830590673)
            ·
              refine ⟨2810911875224787622943005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3747882500299716830590673 2810911875224787622943005)
              ·
                refine ⟨1054091953209295358603627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2810911875224787622943005 1054091953209295358603627)
                ·
                  refine ⟨1581137929813943037905441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054091953209295358603627 1581137929813943037905441)
                  ·
                    refine ⟨1185853447360457278429081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581137929813943037905441 1185853447360457278429081)
                    ·
                      refine ⟨889390085520342958821811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185853447360457278429081 889390085520342958821811)
                      ·
                        rfl

theorem cell23_1732081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_1732081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732081 prefixEnd_1732081 := by exact prefixLift 1732081
  have htrace : WordTrace (prefixWord ++ tailWord_1732081) baseStart_1732081 baseEnd_1732081 := by
    simpa [prefixWord, tailWord_1732081, baseEnd_1732081] using wordTrace_append hprefix tailTrace_1732081
  have hstable : (prefixWord ++ tailWord_1732081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732081).length < 2 ^ (prefixWord ++ tailWord_1732081).sum := by decide
  have hdescent : baseEnd_1732081 < baseStart_1732081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732098 : List Nat := [3, 4, 1, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1732098 : Nat := 118140960795 + 1732098 * 2 ^ 59
def prefixEnd_1732098 : Nat := 4983230072969 + 3 ^ 40 * 1732098 * 2
def baseEnd_1732098 : Nat := 889398814691469392309233

theorem tailTrace_1732098 : CollatzResearch.WordTrace tailWord_1732098 prefixEnd_1732098 889398814691469392309233 := by
  unfold tailWord_1732098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15793701019728059908043237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42116536052608159754781965 15793701019728059908043237)
  ·
    refine ⟨2961318941199011232758107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15793701019728059908043237 2961318941199011232758107)
    ·
      refine ⟨4441978411798516849137161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961318941199011232758107 4441978411798516849137161)
      ·
        refine ⟨3331483808848887636852871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4441978411798516849137161 3331483808848887636852871)
        ·
          refine ⟨4997225713273331455279307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331483808848887636852871 4997225713273331455279307)
          ·
            refine ⟨7495838569909997182918961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997225713273331455279307 7495838569909997182918961)
            ·
              refine ⟨5621878927432497887189221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495838569909997182918961 5621878927432497887189221)
              ·
                refine ⟨1054102298893593353847979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5621878927432497887189221 1054102298893593353847979)
                ·
                  refine ⟨1581153448340390030771969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054102298893593353847979 1581153448340390030771969)
                  ·
                    refine ⟨1185865086255292523078977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581153448340390030771969 1185865086255292523078977)
                    ·
                      refine ⟨889398814691469392309233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185865086255292523078977 889398814691469392309233)
                      ·
                        rfl

theorem cell23_1732098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1732098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732098 prefixEnd_1732098 := by exact prefixLift 1732098
  have htrace : WordTrace (prefixWord ++ tailWord_1732098) baseStart_1732098 baseEnd_1732098 := by
    simpa [prefixWord, tailWord_1732098, baseEnd_1732098] using wordTrace_append hprefix tailTrace_1732098
  have hstable : (prefixWord ++ tailWord_1732098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732098).length < 2 ^ (prefixWord ++ tailWord_1732098).sum := by decide
  have hdescent : baseEnd_1732098 < baseStart_1732098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732113 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 2, 6]
def baseStart_1732113 : Nat := 118140960795 + 1732113 * 2 ^ 59
def prefixEnd_1732113 : Nat := 4983230072969 + 3 ^ 40 * 1732113 * 2
def baseEnd_1732113 : Nat := 296468838967095611207221

theorem tailTrace_1732113 : CollatzResearch.WordTrace tailWord_1732113 prefixEnd_1732113 296468838967095611207221 := by
  unfold tailWord_1732113
  simp only [CollatzResearch.WordTrace]
  refine ⟨63175351173857897193968993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42116900782571931462645995 63175351173857897193968993)
  ·
    refine ⟨47381513380393422895476745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63175351173857897193968993 47381513380393422895476745)
    ·
      refine ⟨35536135035295067171607559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47381513380393422895476745 35536135035295067171607559)
      ·
        refine ⟨53304202552942600757411339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35536135035295067171607559 53304202552942600757411339)
        ·
          refine ⟨79956303829413901136117009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53304202552942600757411339 79956303829413901136117009)
          ·
            refine ⟨59967227872060425852087757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79956303829413901136117009 59967227872060425852087757)
            ·
              refine ⟨22487710452022659694532909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59967227872060425852087757 22487710452022659694532909)
              ·
                refine ⟨8432891419508497385449841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22487710452022659694532909 8432891419508497385449841)
                ·
                  refine ⟨6324668564631373039087381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432891419508497385449841 6324668564631373039087381)
                  ·
                    refine ⟨296468838967095611207221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6324668564631373039087381 296468838967095611207221)
                    ·
                      rfl

theorem cell23_1732113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_1732113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732113 prefixEnd_1732113 := by exact prefixLift 1732113
  have htrace : WordTrace (prefixWord ++ tailWord_1732113) baseStart_1732113 baseEnd_1732113 := by
    simpa [prefixWord, tailWord_1732113, baseEnd_1732113] using wordTrace_append hprefix tailTrace_1732113
  have hstable : (prefixWord ++ tailWord_1732113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732113).length < 2 ^ (prefixWord ++ tailWord_1732113).sum := by decide
  have hdescent : baseEnd_1732113 < baseStart_1732113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732124 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_1732124 : Nat := 118140960795 + 1732124 * 2 ^ 59
def prefixEnd_1732124 : Nat := 4983230072969 + 3 ^ 40 * 1732124 * 2
def baseEnd_1732124 : Nat := 889412165188486290584113

theorem tailTrace_1732124 : CollatzResearch.WordTrace tailWord_1732124 prefixEnd_1732124 889412165188486290584113 := by
  unfold tailWord_1732124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31587876188409023036309713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42117168251212030715079617 31587876188409023036309713)
  ·
    refine ⟨23690907141306767277232285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31587876188409023036309713 23690907141306767277232285)
    ·
      refine ⟨8884090177990037728962107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23690907141306767277232285 8884090177990037728962107)
      ·
        refine ⟨13326135266985056593443161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8884090177990037728962107 13326135266985056593443161)
        ·
          refine ⟨9994601450238792445082371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13326135266985056593443161 9994601450238792445082371)
          ·
            refine ⟨14991902175358188667623557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994601450238792445082371 14991902175358188667623557)
            ·
              refine ⟨2810981657879660375179417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14991902175358188667623557 2810981657879660375179417)
              ·
                refine ⟨2108236243409745281384563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810981657879660375179417 2108236243409745281384563)
                ·
                  refine ⟨3162354365114617922076845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108236243409745281384563 3162354365114617922076845)
                  ·
                    refine ⟨1185882886917981720778817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162354365114617922076845 1185882886917981720778817)
                    ·
                      refine ⟨889412165188486290584113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185882886917981720778817 889412165188486290584113)
                      ·
                        rfl

theorem cell23_1732124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_1732124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732124 prefixEnd_1732124 := by exact prefixLift 1732124
  have htrace : WordTrace (prefixWord ++ tailWord_1732124) baseStart_1732124 baseEnd_1732124 := by
    simpa [prefixWord, tailWord_1732124, baseEnd_1732124] using wordTrace_append hprefix tailTrace_1732124
  have hstable : (prefixWord ++ tailWord_1732124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732124).length < 2 ^ (prefixWord ++ tailWord_1732124).sum := by decide
  have hdescent : baseEnd_1732124 < baseStart_1732124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732154 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2]
def baseStart_1732154 : Nat := 118140960795 + 1732154 * 2 ^ 59
def prefixEnd_1732154 : Nat := 4983230072969 + 3 ^ 40 * 1732154 * 2
def baseEnd_1732154 : Nat := 889427569608121173208975

theorem tailTrace_1732154 : CollatzResearch.WordTrace tailWord_1732154 prefixEnd_1732154 889427569608121173208975 := by
  unfold tailWord_1732154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15794211641677340299052879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42117897711139574130807677 15794211641677340299052879)
  ·
    refine ⟨23691317462516010448579319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15794211641677340299052879 23691317462516010448579319)
    ·
      refine ⟨35536976193774015672868979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23691317462516010448579319 35536976193774015672868979)
      ·
        refine ⟨53305464290661023509303469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35536976193774015672868979 53305464290661023509303469)
        ·
          refine ⟨19989549108997883815988801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53305464290661023509303469 19989549108997883815988801)
          ·
            refine ⟨14992161831748412861991601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19989549108997883815988801 14992161831748412861991601)
            ·
              refine ⟨11244121373811309646493701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14992161831748412861991601 11244121373811309646493701)
              ·
                refine ⟨2108272757589620558717569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11244121373811309646493701 2108272757589620558717569)
                ·
                  refine ⟨1581204568192215419038177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108272757589620558717569 1581204568192215419038177)
                  ·
                    refine ⟨1185903426144161564278633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581204568192215419038177 1185903426144161564278633)
                    ·
                      refine ⟨889427569608121173208975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185903426144161564278633 889427569608121173208975)
                      ·
                        rfl

theorem cell23_1732154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_1732154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732154 prefixEnd_1732154 := by exact prefixLift 1732154
  have htrace : WordTrace (prefixWord ++ tailWord_1732154) baseStart_1732154 baseEnd_1732154 := by
    simpa [prefixWord, tailWord_1732154, baseEnd_1732154] using wordTrace_append hprefix tailTrace_1732154
  have hstable : (prefixWord ++ tailWord_1732154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732154).length < 2 ^ (prefixWord ++ tailWord_1732154).sum := by decide
  have hdescent : baseEnd_1732154 < baseStart_1732154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732170 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_1732170 : Nat := 118140960795 + 1732170 * 2 ^ 59
def prefixEnd_1732170 : Nat := 4983230072969 + 3 ^ 40 * 1732170 * 2
def baseEnd_1732170 : Nat := 889435785298593110608901

theorem tailTrace_1732170 : CollatzResearch.WordTrace tailWord_1732170 prefixEnd_1732170 889435785298593110608901 := by
  unfold tailWord_1732170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15794357533662848982198491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42118286756434263952529309 15794357533662848982198491)
  ·
    refine ⟨23691536300494273473297737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15794357533662848982198491 23691536300494273473297737)
    ·
      refine ⟨17768652225370705104973303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23691536300494273473297737 17768652225370705104973303)
      ·
        refine ⟨26652978338056057657459955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768652225370705104973303 26652978338056057657459955)
        ·
          refine ⟨39979467507084086486189933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26652978338056057657459955 39979467507084086486189933)
          ·
            refine ⟨14992300315156532432321225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39979467507084086486189933 14992300315156532432321225)
            ·
              refine ⟨11244225236367399324240919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14992300315156532432321225 11244225236367399324240919)
              ·
                refine ⟨16866337854551098986361379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11244225236367399324240919 16866337854551098986361379)
                ·
                  refine ⟨25299506781826648479542069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16866337854551098986361379 25299506781826648479542069)
                  ·
                    refine ⟨2371828760796248294957069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25299506781826648479542069 2371828760796248294957069)
                    ·
                      refine ⟨889435785298593110608901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2371828760796248294957069 889435785298593110608901)
                      ·
                        rfl

theorem cell23_1732170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_1732170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732170 prefixEnd_1732170 := by exact prefixLift 1732170
  have htrace : WordTrace (prefixWord ++ tailWord_1732170) baseStart_1732170 baseEnd_1732170 := by
    simpa [prefixWord, tailWord_1732170, baseEnd_1732170] using wordTrace_append hprefix tailTrace_1732170
  have hstable : (prefixWord ++ tailWord_1732170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732170).length < 2 ^ (prefixWord ++ tailWord_1732170).sum := by decide
  have hdescent : baseEnd_1732170 < baseStart_1732170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732203 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 4, 8]
def baseStart_1732203 : Nat := 118140960795 + 1732203 * 2 ^ 59
def prefixEnd_1732203 : Nat := 4983230072969 + 3 ^ 40 * 1732203 * 2
def baseEnd_1732203 : Nat := 296484243386730493832083

theorem tailTrace_1732203 : CollatzResearch.WordTrace tailWord_1732203 prefixEnd_1732203 296484243386730493832083 := by
  unfold tailWord_1732203
  simp only [CollatzResearch.WordTrace]
  refine ⟨63178633743531842564745263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42119089162354561709830175 63178633743531842564745263)
  ·
    refine ⟨94767950615297763847117895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63178633743531842564745263 94767950615297763847117895)
    ·
      refine ⟨142151925922946645770676843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94767950615297763847117895 142151925922946645770676843)
      ·
        refine ⟨213227888884419968656015265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142151925922946645770676843 213227888884419968656015265)
        ·
          refine ⟨159920916663314976492011449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213227888884419968656015265 159920916663314976492011449)
          ·
            refine ⟨119940687497486232369008587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159920916663314976492011449 119940687497486232369008587)
            ·
              refine ⟨179911031246229348553512881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119940687497486232369008587 179911031246229348553512881)
              ·
                refine ⟨134933273434672011415134661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179911031246229348553512881 134933273434672011415134661)
                ·
                  refine ⟨25299988769001002140337749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134933273434672011415134661 25299988769001002140337749)
                  ·
                    refine ⟨296484243386730493832083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25299988769001002140337749 296484243386730493832083)
                    ·
                      rfl

theorem cell23_1732203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_1732203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732203 prefixEnd_1732203 := by exact prefixLift 1732203
  have htrace : WordTrace (prefixWord ++ tailWord_1732203) baseStart_1732203 baseEnd_1732203 := by
    simpa [prefixWord, tailWord_1732203, baseEnd_1732203] using wordTrace_append hprefix tailTrace_1732203
  have hstable : (prefixWord ++ tailWord_1732203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732203).length < 2 ^ (prefixWord ++ tailWord_1732203).sum := by decide
  have hdescent : baseEnd_1732203 < baseStart_1732203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732214 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_1732214 : Nat := 118140960795 + 1732214 * 2 ^ 59
def prefixEnd_1732214 : Nat := 4983230072969 + 3 ^ 40 * 1732214 * 2
def baseEnd_1732214 : Nat := 889458378447390938458699

theorem tailTrace_1732214 : CollatzResearch.WordTrace tailWord_1732214 prefixEnd_1732214 889458378447390938458699 := by
  unfold tailWord_1732214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948689684155749465212231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42119356630994660962263797 3948689684155749465212231)
  ·
    refine ⟨5923034526233624197818347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948689684155749465212231 5923034526233624197818347)
    ·
      refine ⟨8884551789350436296727521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5923034526233624197818347 8884551789350436296727521)
      ·
        refine ⟨6663413842012827222545641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8884551789350436296727521 6663413842012827222545641)
        ·
          refine ⟨4997560381509620416909231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6663413842012827222545641 4997560381509620416909231)
          ·
            refine ⟨7496340572264430625363847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997560381509620416909231 7496340572264430625363847)
            ·
              refine ⟨11244510858396645938045771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496340572264430625363847 11244510858396645938045771)
              ·
                refine ⟨16866766287594968907068657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11244510858396645938045771 16866766287594968907068657)
                ·
                  refine ⟨12650074715696226680301493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16866766287594968907068657 12650074715696226680301493)
                  ·
                    refine ⟨1185944504596521251278265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12650074715696226680301493 1185944504596521251278265)
                    ·
                      refine ⟨889458378447390938458699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185944504596521251278265 889458378447390938458699)
                      ·
                        rfl

theorem cell23_1732214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_1732214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732214 prefixEnd_1732214 := by exact prefixLift 1732214
  have htrace : WordTrace (prefixWord ++ tailWord_1732214) baseStart_1732214 baseEnd_1732214 := by
    simpa [prefixWord, tailWord_1732214, baseEnd_1732214] using wordTrace_append hprefix tailTrace_1732214
  have hstable : (prefixWord ++ tailWord_1732214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732214).length < 2 ^ (prefixWord ++ tailWord_1732214).sum := by decide
  have hdescent : baseEnd_1732214 < baseStart_1732214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732244 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1732244 : Nat := 118140960795 + 1732244 * 2 ^ 59
def prefixEnd_1732244 : Nat := 4983230072969 + 3 ^ 40 * 1732244 * 2
def baseEnd_1732244 : Nat := 889473782867025821083561

theorem tailTrace_1732244 : CollatzResearch.WordTrace tailWord_1732244 prefixEnd_1732244 889473782867025821083561 := by
  unfold tailWord_1732244
  simp only [CollatzResearch.WordTrace]
  refine ⟨31590064568191653283493893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42120086090922204377991857 31590064568191653283493893)
  ·
    refine ⟨5923137106535934990655105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31590064568191653283493893 5923137106535934990655105)
    ·
      refine ⟨4442352829901951242991329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5923137106535934990655105 4442352829901951242991329)
      ·
        refine ⟨3331764622426463432243497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4442352829901951242991329 3331764622426463432243497)
        ·
          refine ⟨2498823466819847574182623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331764622426463432243497 2498823466819847574182623)
          ·
            refine ⟨3748235200229771361273935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498823466819847574182623 3748235200229771361273935)
            ·
              refine ⟨5622352800344657041910903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748235200229771361273935 5622352800344657041910903)
              ·
                refine ⟨8433529200516985562866355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622352800344657041910903 8433529200516985562866355)
                ·
                  refine ⟨12650293800775478344299533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433529200516985562866355 12650293800775478344299533)
                  ·
                    refine ⟨4743860175290804379112325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12650293800775478344299533 4743860175290804379112325)
                    ·
                      refine ⟨889473782867025821083561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4743860175290804379112325 889473782867025821083561)
                      ·
                        rfl

theorem cell23_1732244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1732244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732244 prefixEnd_1732244 := by exact prefixLift 1732244
  have htrace : WordTrace (prefixWord ++ tailWord_1732244) baseStart_1732244 baseEnd_1732244 := by
    simpa [prefixWord, tailWord_1732244, baseEnd_1732244] using wordTrace_append hprefix tailTrace_1732244
  have hstable : (prefixWord ++ tailWord_1732244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732244).length < 2 ^ (prefixWord ++ tailWord_1732244).sum := by decide
  have hdescent : baseEnd_1732244 < baseStart_1732244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732247 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1732247 : Nat := 118140960795 + 1732247 * 2 ^ 59
def prefixEnd_1732247 : Nat := 4983230072969 + 3 ^ 40 * 1732247 * 2
def baseEnd_1732247 : Nat := 889475323308989309346047

theorem tailTrace_1732247 : CollatzResearch.WordTrace tailWord_1732247 prefixEnd_1732247 889475323308989309346047 := by
  unfold tailWord_1732247
  simp only [CollatzResearch.WordTrace]
  refine ⟨63180238555372438079346995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42120159036914958719564663 63180238555372438079346995)
  ·
    refine ⟨94770357833058657119020493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63180238555372438079346995 94770357833058657119020493)
    ·
      refine ⟨35538884187396996419632685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94770357833058657119020493 35538884187396996419632685)
      ·
        refine ⟨13327081570273873657362257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35538884187396996419632685 13327081570273873657362257)
        ·
          refine ⟨9995311177705405243021693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13327081570273873657362257 9995311177705405243021693)
          ·
            refine ⟨3748241691639526966133135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9995311177705405243021693 3748241691639526966133135)
            ·
              refine ⟨5622362537459290449199703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748241691639526966133135 5622362537459290449199703)
              ·
                refine ⟨8433543806188935673799555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622362537459290449199703 8433543806188935673799555)
                ·
                  refine ⟨12650315709283403510699333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433543806188935673799555 12650315709283403510699333)
                  ·
                    refine ⟨2371934195490638158256125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12650315709283403510699333 2371934195490638158256125)
                    ·
                      refine ⟨889475323308989309346047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2371934195490638158256125 889475323308989309346047)
                      ·
                        rfl

theorem cell23_1732247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1732247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732247 prefixEnd_1732247 := by exact prefixLift 1732247
  have htrace : WordTrace (prefixWord ++ tailWord_1732247) baseStart_1732247 baseEnd_1732247 := by
    simpa [prefixWord, tailWord_1732247, baseEnd_1732247] using wordTrace_append hprefix tailTrace_1732247
  have hstable : (prefixWord ++ tailWord_1732247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732247).length < 2 ^ (prefixWord ++ tailWord_1732247).sum := by decide
  have hdescent : baseEnd_1732247 < baseStart_1732247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732280 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 5, 5]
def baseStart_1732280 : Nat := 118140960795 + 1732280 * 2 ^ 59
def prefixEnd_1732280 : Nat := 4983230072969 + 3 ^ 40 * 1732280 * 2
def baseEnd_1732280 : Nat := 296497422723529226744465

theorem tailTrace_1732280 : CollatzResearch.WordTrace tailWord_1732280 prefixEnd_1732280 296497422723529226744465 := by
  unfold tailWord_1732280
  simp only [CollatzResearch.WordTrace]
  refine ⟨31590721082126442357649147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42120961442835256476865529 31590721082126442357649147)
  ·
    refine ⟨47386081623189663536473721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31590721082126442357649147 47386081623189663536473721)
    ·
      refine ⟨35539561217392247652355291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47386081623189663536473721 35539561217392247652355291)
      ·
        refine ⟨53309341826088371478532937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35539561217392247652355291 53309341826088371478532937)
        ·
          refine ⟨39982006369566278608899703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53309341826088371478532937 39982006369566278608899703)
          ·
            refine ⟨59973009554349417913349555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39982006369566278608899703 59973009554349417913349555)
            ·
              refine ⟨89959514331524126870024333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59973009554349417913349555 89959514331524126870024333)
              ·
                refine ⟨33734817874321547576259125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89959514331524126870024333 33734817874321547576259125)
                ·
                  refine ⟨3162639175717645085274293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33734817874321547576259125 3162639175717645085274293)
                  ·
                    refine ⟨296497422723529226744465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3162639175717645085274293 296497422723529226744465)
                    ·
                      rfl

theorem cell23_1732280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_1732280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732280 prefixEnd_1732280 := by exact prefixLift 1732280
  have htrace : WordTrace (prefixWord ++ tailWord_1732280) baseStart_1732280 baseEnd_1732280 := by
    simpa [prefixWord, tailWord_1732280, baseEnd_1732280] using wordTrace_append hprefix tailTrace_1732280
  have hstable : (prefixWord ++ tailWord_1732280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732280).length < 2 ^ (prefixWord ++ tailWord_1732280).sum := by decide
  have hdescent : baseEnd_1732280 < baseStart_1732280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732284 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 6]
def baseStart_1732284 : Nat := 118140960795 + 1732284 * 2 ^ 59
def prefixEnd_1732284 : Nat := 4983230072969 + 3 ^ 40 * 1732284 * 2
def baseEnd_1732284 : Nat := 98832702454800629398153

theorem tailTrace_1732284 : CollatzResearch.WordTrace tailWord_1732284 prefixEnd_1732284 98832702454800629398153 := by
  unfold tailWord_1732284
  simp only [CollatzResearch.WordTrace]
  refine ⟨31590794028119196699221953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42121058704158928932295937 31590794028119196699221953)
  ·
    refine ⟨23693095521089397524416465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31590794028119196699221953 23693095521089397524416465)
    ·
      refine ⟨17769821640817048143312349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23693095521089397524416465 17769821640817048143312349)
      ·
        refine ⟨6663683115306393053742131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17769821640817048143312349 6663683115306393053742131)
        ·
          refine ⟨9995524672959589580613197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663683115306393053742131 9995524672959589580613197)
          ·
            refine ⟨3748321752359846092729949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9995524672959589580613197 3748321752359846092729949)
            ·
              refine ⟨1405620657134942284773731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3748321752359846092729949 1405620657134942284773731)
              ·
                refine ⟨2108430985702413427160597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405620657134942284773731 2108430985702413427160597)
                ·
                  refine ⟨98832702454800629398153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2108430985702413427160597 98832702454800629398153)
                  ·
                    rfl

theorem cell23_1732284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_1732284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732284 prefixEnd_1732284 := by exact prefixLift 1732284
  have htrace : WordTrace (prefixWord ++ tailWord_1732284) baseStart_1732284 baseEnd_1732284 := by
    simpa [prefixWord, tailWord_1732284, baseEnd_1732284] using wordTrace_append hprefix tailTrace_1732284
  have hstable : (prefixWord ++ tailWord_1732284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732284).length < 2 ^ (prefixWord ++ tailWord_1732284).sum := by decide
  have hdescent : baseEnd_1732284 < baseStart_1732284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732287 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 3, 5, 2]
def baseStart_1732287 : Nat := 118140960795 + 1732287 * 2 ^ 59
def prefixEnd_1732287 : Nat := 4983230072969 + 3 ^ 40 * 1732287 * 2
def baseEnd_1732287 : Nat := 889495862535169152845863

theorem tailTrace_1732287 : CollatzResearch.WordTrace tailWord_1732287 prefixEnd_1732287 889495862535169152845863 := by
  unfold tailWord_1732287
  simp only [CollatzResearch.WordTrace]
  refine ⟨63181697475227524910803115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42121131650151683273868743 63181697475227524910803115)
  ·
    refine ⟨94772546212841287366204673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63181697475227524910803115 94772546212841287366204673)
    ·
      refine ⟨71079409659630965524653505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94772546212841287366204673 71079409659630965524653505)
      ·
        refine ⟨53309557244723224143490129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71079409659630965524653505 53309557244723224143490129)
        ·
          refine ⟨39982167933542418107617597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53309557244723224143490129 39982167933542418107617597)
          ·
            refine ⟨14993312975078406790356599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39982167933542418107617597 14993312975078406790356599)
            ·
              refine ⟨22489969462617610185534899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14993312975078406790356599 22489969462617610185534899)
              ·
                refine ⟨33734954193926415278302349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22489969462617610185534899 33734954193926415278302349)
                ·
                  refine ⟨12650607822722405729363381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33734954193926415278302349 12650607822722405729363381)
                  ·
                    refine ⟨1185994483380225537127817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12650607822722405729363381 1185994483380225537127817)
                    ·
                      refine ⟨889495862535169152845863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1185994483380225537127817 889495862535169152845863)
                      ·
                        rfl

theorem cell23_1732287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_1732287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732287 prefixEnd_1732287 := by exact prefixLift 1732287
  have htrace : WordTrace (prefixWord ++ tailWord_1732287) baseStart_1732287 baseEnd_1732287 := by
    simpa [prefixWord, tailWord_1732287, baseEnd_1732287] using wordTrace_append hprefix tailTrace_1732287
  have hstable : (prefixWord ++ tailWord_1732287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732287).length < 2 ^ (prefixWord ++ tailWord_1732287).sum := by decide
  have hdescent : baseEnd_1732287 < baseStart_1732287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732321 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_1732321 : Nat := 118140960795 + 1732321 * 2 ^ 59
def prefixEnd_1732321 : Nat := 4983230072969 + 3 ^ 40 * 1732321 * 2
def baseEnd_1732321 : Nat := 889513320877422019820707

theorem tailTrace_1732321 : CollatzResearch.WordTrace tailWord_1732321 prefixEnd_1732321 889513320877422019820707 := by
  unfold tailWord_1732321
  simp only [CollatzResearch.WordTrace]
  refine ⟨63182937557104348717540817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42121958371402899145027211 63182937557104348717540817)
  ·
    refine ⟨47387203167828261538155613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63182937557104348717540817 47387203167828261538155613)
    ·
      refine ⟨17770201187935598076808355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47387203167828261538155613 17770201187935598076808355)
      ·
        refine ⟨26655301781903397115212533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17770201187935598076808355 26655301781903397115212533)
        ·
          refine ⟨2498934542053443479551175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26655301781903397115212533 2498934542053443479551175)
          ·
            refine ⟨3748401813080165219326763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498934542053443479551175 3748401813080165219326763)
            ·
              refine ⟨5622602719620247828990145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748401813080165219326763 5622602719620247828990145)
              ·
                refine ⟨4216952039715185871742609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5622602719620247828990145 4216952039715185871742609)
                ·
                  refine ⟨3162714029786389403806957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216952039715185871742609 3162714029786389403806957)
                  ·
                    refine ⟨1186017761169896026427609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162714029786389403806957 1186017761169896026427609)
                    ·
                      refine ⟨889513320877422019820707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186017761169896026427609 889513320877422019820707)
                      ·
                        rfl

theorem cell23_1732321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_1732321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732321 prefixEnd_1732321 := by exact prefixLift 1732321
  have htrace : WordTrace (prefixWord ++ tailWord_1732321) baseStart_1732321 baseEnd_1732321 := by
    simpa [prefixWord, tailWord_1732321, baseEnd_1732321] using wordTrace_append hprefix tailTrace_1732321
  have hstable : (prefixWord ++ tailWord_1732321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732321).length < 2 ^ (prefixWord ++ tailWord_1732321).sum := by decide
  have hdescent : baseEnd_1732321 < baseStart_1732321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732337 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_1732337 : Nat := 118140960795 + 1732337 * 2 ^ 59
def prefixEnd_1732337 : Nat := 4983230072969 + 3 ^ 40 * 1732337 * 2
def baseEnd_1732337 : Nat := 889521536567893957220633

theorem tailTrace_1732337 : CollatzResearch.WordTrace tailWord_1732337 prefixEnd_1732337 889521536567893957220633 := by
  unfold tailWord_1732337
  simp only [CollatzResearch.WordTrace]
  refine ⟨63183521125046383450123265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42122347416697588966748843 63183521125046383450123265)
  ·
    refine ⟨47387640843784787587592449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63183521125046383450123265 47387640843784787587592449)
    ·
      refine ⟨35540730632838590690694337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47387640843784787587592449 35540730632838590690694337)
      ·
        refine ⟨26655547974628943018020753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35540730632838590690694337 26655547974628943018020753)
        ·
          refine ⟨19991660980971707263515565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26655547974628943018020753 19991660980971707263515565)
          ·
            refine ⟨7496872867864390223818337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19991660980971707263515565 7496872867864390223818337)
            ·
              refine ⟨5622654650898292667863753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7496872867864390223818337 5622654650898292667863753)
              ·
                refine ⟨4216990988173719500897815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5622654650898292667863753 4216990988173719500897815)
                ·
                  refine ⟨6325486482260579251346723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216990988173719500897815 6325486482260579251346723)
                  ·
                    refine ⟨9488229723390868877020085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6325486482260579251346723 9488229723390868877020085)
                    ·
                      refine ⟨889521536567893957220633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9488229723390868877020085 889521536567893957220633)
                      ·
                        rfl

theorem cell23_1732337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_1732337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732337 prefixEnd_1732337 := by exact prefixLift 1732337
  have htrace : WordTrace (prefixWord ++ tailWord_1732337) baseStart_1732337 baseEnd_1732337 := by
    simpa [prefixWord, tailWord_1732337, baseEnd_1732337] using wordTrace_append hprefix tailTrace_1732337
  have hstable : (prefixWord ++ tailWord_1732337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732337).length < 2 ^ (prefixWord ++ tailWord_1732337).sum := by decide
  have hdescent : baseEnd_1732337 < baseStart_1732337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732385 : List Nat := [1, 2, 3, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1732385 : Nat := 118140960795 + 1732385 * 2 ^ 59
def prefixEnd_1732385 : Nat := 4983230072969 + 3 ^ 40 * 1732385 * 2
def baseEnd_1732385 : Nat := 889546183639309769420413

theorem tailTrace_1732385 : CollatzResearch.WordTrace tailWord_1732385 prefixEnd_1732385 889546183639309769420413 := by
  unfold tailWord_1732385
  simp only [CollatzResearch.WordTrace]
  refine ⟨63185271828872487647870609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42123514552581658431913739 63185271828872487647870609)
  ·
    refine ⟨47388953871654365735902957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63185271828872487647870609 47388953871654365735902957)
    ·
      refine ⟨17770857701870387150963609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47388953871654365735902957 17770857701870387150963609)
      ·
        refine ⟨13328143276402790363222707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17770857701870387150963609 13328143276402790363222707)
        ·
          refine ⟨19992214914604185544834061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13328143276402790363222707 19992214914604185544834061)
          ·
            refine ⟨7497080592976569579312773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19992214914604185544834061 7497080592976569579312773)
            ·
              refine ⟨1405702611183106796121145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7497080592976569579312773 1405702611183106796121145)
              ·
                refine ⟨1054276958387330097090859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405702611183106796121145 1054276958387330097090859)
                ·
                  refine ⟨1581415437580995145636289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054276958387330097090859 1581415437580995145636289)
                  ·
                    refine ⟨1186061578185746359227217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581415437580995145636289 1186061578185746359227217)
                    ·
                      refine ⟨889546183639309769420413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186061578185746359227217 889546183639309769420413)
                      ·
                        rfl

theorem cell23_1732385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1732385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732385 prefixEnd_1732385 := by exact prefixLift 1732385
  have htrace : WordTrace (prefixWord ++ tailWord_1732385) baseStart_1732385 baseEnd_1732385 := by
    simpa [prefixWord, tailWord_1732385, baseEnd_1732385] using wordTrace_append hprefix tailTrace_1732385
  have hstable : (prefixWord ++ tailWord_1732385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732385).length < 2 ^ (prefixWord ++ tailWord_1732385).sum := by decide
  have hdescent : baseEnd_1732385 < baseStart_1732385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732401 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_1732401 : Nat := 118140960795 + 1732401 * 2 ^ 59
def prefixEnd_1732401 : Nat := 4983230072969 + 3 ^ 40 * 1732401 * 2
def baseEnd_1732401 : Nat := 889554399329781706820339

theorem tailTrace_1732401 : CollatzResearch.WordTrace tailWord_1732401 prefixEnd_1732401 889554399329781706820339 := by
  unfold tailWord_1732401
  simp only [CollatzResearch.WordTrace]
  refine ⟨63185855396814522380453057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42123903597876348253635371 63185855396814522380453057)
  ·
    refine ⟨47389391547610891785339793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63185855396814522380453057 47389391547610891785339793)
    ·
      refine ⟨35542043660708168839004845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47389391547610891785339793 35542043660708168839004845)
      ·
        refine ⟨13328266372765563314626817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35542043660708168839004845 13328266372765563314626817)
        ·
          refine ⟨9996199779574172485970113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13328266372765563314626817 9996199779574172485970113)
          ·
            refine ⟨7497149834680629364477585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9996199779574172485970113 7497149834680629364477585)
            ·
              refine ⟨5622862376010472023358189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7497149834680629364477585 5622862376010472023358189)
              ·
                refine ⟨2108573391003927008759321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5622862376010472023358189 2108573391003927008759321)
                ·
                  refine ⟨1581430043252945256569491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108573391003927008759321 1581430043252945256569491)
                  ·
                    refine ⟨2372145064879417884854237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1581430043252945256569491 2372145064879417884854237)
                    ·
                      refine ⟨889554399329781706820339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2372145064879417884854237 889554399329781706820339)
                      ·
                        rfl

theorem cell23_1732401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_1732401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732401 prefixEnd_1732401 := by exact prefixLift 1732401
  have htrace : WordTrace (prefixWord ++ tailWord_1732401) baseStart_1732401 baseEnd_1732401 := by
    simpa [prefixWord, tailWord_1732401, baseEnd_1732401] using wordTrace_append hprefix tailTrace_1732401
  have hstable : (prefixWord ++ tailWord_1732401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732401).length < 2 ^ (prefixWord ++ tailWord_1732401).sum := by decide
  have hdescent : baseEnd_1732401 < baseStart_1732401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732422 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1732422 : Nat := 118140960795 + 1732422 * 2 ^ 59
def prefixEnd_1732422 : Nat := 4983230072969 + 3 ^ 40 * 1732422 * 2
def baseEnd_1732422 : Nat := 889565182423526124657743

theorem tailTrace_1732422 : CollatzResearch.WordTrace tailWord_1732422 prefixEnd_1732422 889565182423526124657743 := by
  unfold tailWord_1732422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974581916554326342717735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42124414219825628644645013 1974581916554326342717735)
  ·
    refine ⟨2961872874831489514076603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974581916554326342717735 2961872874831489514076603)
    ·
      refine ⟨4442809312247234271114905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961872874831489514076603 4442809312247234271114905)
      ·
        refine ⟨3332106984185425703336179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4442809312247234271114905 3332106984185425703336179)
        ·
          refine ⟨4998160476278138555004269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3332106984185425703336179 4998160476278138555004269)
          ·
            refine ⟨1874310178604301958126601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4998160476278138555004269 1874310178604301958126601)
            ·
              refine ⟨1405732633953226468594951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874310178604301958126601 1405732633953226468594951)
              ·
                refine ⟨2108598950929839702892427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405732633953226468594951 2108598950929839702892427)
                ·
                  refine ⟨3162898426394759554338641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108598950929839702892427 3162898426394759554338641)
                  ·
                    refine ⟨2372173819796069665753981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3162898426394759554338641 2372173819796069665753981)
                    ·
                      refine ⟨889565182423526124657743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2372173819796069665753981 889565182423526124657743)
                      ·
                        rfl

theorem cell23_1732422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1732422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732422 prefixEnd_1732422 := by exact prefixLift 1732422
  have htrace : WordTrace (prefixWord ++ tailWord_1732422) baseStart_1732422 baseEnd_1732422 := by
    simpa [prefixWord, tailWord_1732422, baseEnd_1732422] using wordTrace_append hprefix tailTrace_1732422
  have hstable : (prefixWord ++ tailWord_1732422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732422).length < 2 ^ (prefixWord ++ tailWord_1732422).sum := by decide
  have hdescent : baseEnd_1732422 < baseStart_1732422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732428 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 1, 3, 2]
def baseStart_1732428 : Nat := 118140960795 + 1732428 * 2 ^ 59
def prefixEnd_1732428 : Nat := 4983230072969 + 3 ^ 40 * 1732428 * 2
def baseEnd_1732428 : Nat := 889568263307453101182715

theorem tailTrace_1732428 : CollatzResearch.WordTrace tailWord_1732428 prefixEnd_1732428 889568263307453101182715 := by
  unfold tailWord_1732428
  simp only [CollatzResearch.WordTrace]
  refine ⟨31593420083858352995842969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42124560111811137327790625 31593420083858352995842969)
  ·
    refine ⟨23695065062893764746882227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31593420083858352995842969 23695065062893764746882227)
    ·
      refine ⟨35542597594340647120323341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23695065062893764746882227 35542597594340647120323341)
      ·
        refine ⟨13328474097877742670121253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35542597594340647120323341 13328474097877742670121253)
        ·
          refine ⟨2499088893352076750647735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13328474097877742670121253 2499088893352076750647735)
          ·
            refine ⟨3748633340028115125971603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499088893352076750647735 3748633340028115125971603)
            ·
              refine ⟨5622950010042172688957405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748633340028115125971603 5622950010042172688957405)
              ·
                refine ⟨2108606253765814758359027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5622950010042172688957405 2108606253765814758359027)
                ·
                  refine ⟨3162909380648722137538541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108606253765814758359027 3162909380648722137538541)
                  ·
                    refine ⟨1186091017743270801576953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162909380648722137538541 1186091017743270801576953)
                    ·
                      refine ⟨889568263307453101182715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186091017743270801576953 889568263307453101182715)
                      ·
                        rfl

theorem cell23_1732428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_1732428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732428 prefixEnd_1732428 := by exact prefixLift 1732428
  have htrace : WordTrace (prefixWord ++ tailWord_1732428) baseStart_1732428 baseEnd_1732428 := by
    simpa [prefixWord, tailWord_1732428, baseEnd_1732428] using wordTrace_append hprefix tailTrace_1732428
  have hstable : (prefixWord ++ tailWord_1732428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732428).length < 2 ^ (prefixWord ++ tailWord_1732428).sum := by decide
  have hdescent : baseEnd_1732428 < baseStart_1732428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732441 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 4, 2, 2]
def baseStart_1732441 : Nat := 118140960795 + 1732441 * 2 ^ 59
def prefixEnd_1732441 : Nat := 4983230072969 + 3 ^ 40 * 1732441 * 2
def baseEnd_1732441 : Nat := 889574938555961550320155

theorem tailTrace_1732441 : CollatzResearch.WordTrace tailWord_1732441 prefixEnd_1732441 889574938555961550320155 := by
  unfold tailWord_1732441
  simp only [CollatzResearch.WordTrace]
  refine ⟨63187314316669609211909177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42124876211113072807939451 63187314316669609211909177)
  ·
    refine ⟨47390485737502206908931883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63187314316669609211909177 47390485737502206908931883)
    ·
      refine ⟨71085728606253310363397825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47390485737502206908931883 71085728606253310363397825)
      ·
        refine ⟨53314296454689982772548369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71085728606253310363397825 53314296454689982772548369)
        ·
          refine ⟨39985722341017487079411277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53314296454689982772548369 39985722341017487079411277)
          ·
            refine ⟨14994645877881557654779229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39985722341017487079411277 14994645877881557654779229)
            ·
              refine ⟨5622992204205584120542211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14994645877881557654779229 5622992204205584120542211)
              ·
                refine ⟨8434488306308376180813317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622992204205584120542211 8434488306308376180813317)
                ·
                  refine ⟨1581466557432820533902497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8434488306308376180813317 1581466557432820533902497)
                  ·
                    refine ⟨1186099918074615400426873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581466557432820533902497 1186099918074615400426873)
                    ·
                      refine ⟨889574938555961550320155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186099918074615400426873 889574938555961550320155)
                      ·
                        rfl

theorem cell23_1732441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_1732441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732441 prefixEnd_1732441 := by exact prefixLift 1732441
  have htrace : WordTrace (prefixWord ++ tailWord_1732441) baseStart_1732441 baseEnd_1732441 := by
    simpa [prefixWord, tailWord_1732441, baseEnd_1732441] using wordTrace_append hprefix tailTrace_1732441
  have hstable : (prefixWord ++ tailWord_1732441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732441).length < 2 ^ (prefixWord ++ tailWord_1732441).sum := by decide
  have hdescent : baseEnd_1732441 < baseStart_1732441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732447 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 7]
def baseStart_1732447 : Nat := 118140960795 + 1732447 * 2 ^ 59
def prefixEnd_1732447 : Nat := 4983230072969 + 3 ^ 40 * 1732447 * 2
def baseEnd_1732447 : Nat := 98842002159987614093903

theorem tailTrace_1732447 : CollatzResearch.WordTrace tailWord_1732447 prefixEnd_1732447 98842002159987614093903 := by
  unfold tailWord_1732447
  simp only [CollatzResearch.WordTrace]
  refine ⟨63187533154647872236627595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42125022103098581491085063 63187533154647872236627595)
  ·
    refine ⟨94781299731971808354941393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63187533154647872236627595 94781299731971808354941393)
    ·
      refine ⟨71085974798978856266206045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94781299731971808354941393 71085974798978856266206045)
      ·
        refine ⟨26657240549617071099827267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71085974798978856266206045 26657240549617071099827267)
        ·
          refine ⟨39985860824425606649740901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26657240549617071099827267 39985860824425606649740901)
          ·
            refine ⟨7497348904579801246826419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39985860824425606649740901 7497348904579801246826419)
            ·
              refine ⟨11246023356869701870239629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7497348904579801246826419 11246023356869701870239629)
              ·
                refine ⟨4217258758826138201339861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11246023356869701870239629 4217258758826138201339861)
                ·
                  refine ⟨98842002159987614093903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4217258758826138201339861 98842002159987614093903)
                  ·
                    rfl

theorem cell23_1732447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 7].length) (baseStart_1732447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732447 prefixEnd_1732447 := by exact prefixLift 1732447
  have htrace : WordTrace (prefixWord ++ tailWord_1732447) baseStart_1732447 baseEnd_1732447 := by
    simpa [prefixWord, tailWord_1732447, baseEnd_1732447] using wordTrace_append hprefix tailTrace_1732447
  have hstable : (prefixWord ++ tailWord_1732447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732447).length < 2 ^ (prefixWord ++ tailWord_1732447).sum := by decide
  have hdescent : baseEnd_1732447 < baseStart_1732447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732517 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1732517 : Nat := 118140960795 + 1732517 * 2 ^ 59
def prefixEnd_1732517 : Nat := 4983230072969 + 3 ^ 40 * 1732517 * 2
def baseEnd_1732517 : Nat := 889613963085703252969805

theorem tailTrace_1732517 : CollatzResearch.WordTrace tailWord_1732517 prefixEnd_1732517 889613963085703252969805 := by
  unfold tailWord_1732517
  simp only [CollatzResearch.WordTrace]
  refine ⟨63190086264394274191675805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42126724176262849461117203 63190086264394274191675805)
  ·
    refine ⟨23696282349147852821878427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63190086264394274191675805 23696282349147852821878427)
    ·
      refine ⟨35544423523721779232817641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23696282349147852821878427 35544423523721779232817641)
      ·
        refine ⟨26658317642791334424613231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35544423523721779232817641 26658317642791334424613231)
        ·
          refine ⟨39987476464187001636919847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26658317642791334424613231 39987476464187001636919847)
          ·
            refine ⟨59981214696280502455379771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39987476464187001636919847 59981214696280502455379771)
            ·
              refine ⟨89971822044420753683069657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59981214696280502455379771 89971822044420753683069657)
              ·
                refine ⟨67478866533315565262302243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89971822044420753683069657 67478866533315565262302243)
                ·
                  refine ⟨101218299799973347893453365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67478866533315565262302243 101218299799973347893453365)
                  ·
                    refine ⟨9489215606247501365011253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101218299799973347893453365 9489215606247501365011253)
                    ·
                      refine ⟨889613963085703252969805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9489215606247501365011253 889613963085703252969805)
                      ·
                        rfl

theorem cell23_1732517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1732517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732517 prefixEnd_1732517 := by exact prefixLift 1732517
  have htrace : WordTrace (prefixWord ++ tailWord_1732517) baseStart_1732517 baseEnd_1732517 := by
    simpa [prefixWord, tailWord_1732517, baseEnd_1732517] using wordTrace_append hprefix tailTrace_1732517
  have hstable : (prefixWord ++ tailWord_1732517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732517).length < 2 ^ (prefixWord ++ tailWord_1732517).sum := by decide
  have hdescent : baseEnd_1732517 < baseStart_1732517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732554 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 6]
def baseStart_1732554 : Nat := 118140960795 + 1732554 * 2 ^ 59
def prefixEnd_1732554 : Nat := 4983230072969 + 3 ^ 40 * 1732554 * 2
def baseEnd_1732554 : Nat := 98848106874435512023015

theorem tailTrace_1732554 : CollatzResearch.WordTrace tailWord_1732554 prefixEnd_1732554 98848106874435512023015 := by
  unfold tailWord_1732554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15797858941315057377693179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42127623843506819673848477 15797858941315057377693179)
  ·
    refine ⟨23696788411972586066539769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15797858941315057377693179 23696788411972586066539769)
    ·
      refine ⟨17772591308979439549904827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23696788411972586066539769 17772591308979439549904827)
      ·
        refine ⟨26658886963469159324857241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17772591308979439549904827 26658886963469159324857241)
        ·
          refine ⟨19994165222601869493642931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26658886963469159324857241 19994165222601869493642931)
          ·
            refine ⟨29991247833902804240464397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19994165222601869493642931 29991247833902804240464397)
            ·
              refine ⟨11246717937713551590174149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29991247833902804240464397 11246717937713551590174149)
              ·
                refine ⟨2108759613321290923157653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11246717937713551590174149 2108759613321290923157653)
                ·
                  refine ⟨98848106874435512023015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2108759613321290923157653 98848106874435512023015)
                  ·
                    rfl

theorem cell23_1732554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_1732554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732554 prefixEnd_1732554 := by exact prefixLift 1732554
  have htrace : WordTrace (prefixWord ++ tailWord_1732554) baseStart_1732554 baseEnd_1732554 := by
    simpa [prefixWord, tailWord_1732554, baseEnd_1732554] using wordTrace_append hprefix tailTrace_1732554
  have hstable : (prefixWord ++ tailWord_1732554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732554).length < 2 ^ (prefixWord ++ tailWord_1732554).sum := by decide
  have hdescent : baseEnd_1732554 < baseStart_1732554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732558 : List Nat := [4, 1, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_1732558 : Nat := 118140960795 + 1732558 * 2 ^ 59
def prefixEnd_1732558 : Nat := 4983230072969 + 3 ^ 40 * 1732558 * 2
def baseEnd_1732558 : Nat := 296545005264179197519039

theorem tailTrace_1732558 : CollatzResearch.WordTrace tailWord_1732558 prefixEnd_1732558 296545005264179197519039 := by
  unfold tailWord_1732558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7898947707155717274239791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42127721104830492129278885 7898947707155717274239791)
  ·
    refine ⟨11848421560733575911359687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7898947707155717274239791 11848421560733575911359687)
    ·
      refine ⟨17772632341100363867039531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11848421560733575911359687 17772632341100363867039531)
      ·
        refine ⟨26658948511650545800559297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17772632341100363867039531 26658948511650545800559297)
        ·
          refine ⟨19994211383737909350419473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26658948511650545800559297 19994211383737909350419473)
          ·
            refine ⟨14995658537803432012814605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19994211383737909350419473 14995658537803432012814605)
            ·
              refine ⟨5623371951676287004805477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14995658537803432012814605 5623371951676287004805477)
              ·
                refine ⟨1054382240939303813401027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5623371951676287004805477 1054382240939303813401027)
                ·
                  refine ⟨1581573361408955720101541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054382240939303813401027 1581573361408955720101541)
                  ·
                    refine ⟨296545005264179197519039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1581573361408955720101541 296545005264179197519039)
                    ·
                      rfl

theorem cell23_1732558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_1732558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732558 prefixEnd_1732558 := by exact prefixLift 1732558
  have htrace : WordTrace (prefixWord ++ tailWord_1732558) baseStart_1732558 baseEnd_1732558 := by
    simpa [prefixWord, tailWord_1732558, baseEnd_1732558] using wordTrace_append hprefix tailTrace_1732558
  have hstable : (prefixWord ++ tailWord_1732558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732558).length < 2 ^ (prefixWord ++ tailWord_1732558).sum := by decide
  have hdescent : baseEnd_1732558 < baseStart_1732558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732591 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 1, 5, 2]
def baseStart_1732591 : Nat := 118140960795 + 1732591 * 2 ^ 59
def prefixEnd_1732591 : Nat := 4983230072969 + 3 ^ 40 * 1732591 * 2
def baseEnd_1732591 : Nat := 889651960654135963444465

theorem tailTrace_1732591 : CollatzResearch.WordTrace tailWord_1732591 prefixEnd_1732591 889651960654135963444465 := by
  unfold tailWord_1732591
  simp only [CollatzResearch.WordTrace]
  refine ⟨63192785266126184829869627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42128523510750789886579751 63192785266126184829869627)
  ·
    refine ⟨94789177899189277244804441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63192785266126184829869627 94789177899189277244804441)
    ·
      refine ⟨71091883424391957933603331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94789177899189277244804441 71091883424391957933603331)
      ·
        refine ⟨106637825136587936900404997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71091883424391957933603331 106637825136587936900404997)
        ·
          refine ⟨19994592213110238168825937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106637825136587936900404997 19994592213110238168825937)
          ·
            refine ⟨14995944159832678626619453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19994592213110238168825937 14995944159832678626619453)
            ·
              refine ⟨5623479059937254484982295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14995944159832678626619453 5623479059937254484982295)
              ·
                refine ⟨8435218589905881727473443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623479059937254484982295 8435218589905881727473443)
                ·
                  refine ⟨12652827884858822591210165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8435218589905881727473443 12652827884858822591210165)
                  ·
                    refine ⟨1186202614205514617925953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12652827884858822591210165 1186202614205514617925953)
                    ·
                      refine ⟨889651960654135963444465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186202614205514617925953 889651960654135963444465)
                      ·
                        rfl

theorem cell23_1732591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5, 2].length) (baseStart_1732591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732591 prefixEnd_1732591 := by exact prefixLift 1732591
  have htrace : WordTrace (prefixWord ++ tailWord_1732591) baseStart_1732591 baseEnd_1732591 := by
    simpa [prefixWord, tailWord_1732591, baseEnd_1732591] using wordTrace_append hprefix tailTrace_1732591
  have hstable : (prefixWord ++ tailWord_1732591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732591).length < 2 ^ (prefixWord ++ tailWord_1732591).sum := by decide
  have hdescent : baseEnd_1732591 < baseStart_1732591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732601 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 1, 5]
def baseStart_1732601 : Nat := 118140960795 + 1732601 * 2 ^ 59
def prefixEnd_1732601 : Nat := 4983230072969 + 3 ^ 40 * 1732601 * 2
def baseEnd_1732601 : Nat := 296552365153560308106473

theorem tailTrace_1732601 : CollatzResearch.WordTrace tailWord_1732601 prefixEnd_1732601 296552365153560308106473 := by
  unfold tailWord_1732601
  simp only [CollatzResearch.WordTrace]
  refine ⟨63193149996089956537733657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42128766664059971025155771 63193149996089956537733657)
  ·
    refine ⟨47394862497067467403300243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63193149996089956537733657 47394862497067467403300243)
    ·
      refine ⟨71092293745601201104950365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47394862497067467403300243 71092293745601201104950365)
      ·
        refine ⟨26659610154600450414356387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71092293745601201104950365 26659610154600450414356387)
        ·
          refine ⟨39989415231900675621534581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26659610154600450414356387 39989415231900675621534581)
          ·
            refine ⟨3749007677990688339518867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39989415231900675621534581 3749007677990688339518867)
            ·
              refine ⟨5623511516986032509278301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749007677990688339518867 5623511516986032509278301)
              ·
                refine ⟨2108816818869762190979363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5623511516986032509278301 2108816818869762190979363)
                ·
                  refine ⟨3163225228304643286469045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108816818869762190979363 3163225228304643286469045)
                  ·
                    refine ⟨296552365153560308106473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3163225228304643286469045 296552365153560308106473)
                    ·
                      rfl

theorem cell23_1732601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_1732601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732601 prefixEnd_1732601 := by exact prefixLift 1732601
  have htrace : WordTrace (prefixWord ++ tailWord_1732601) baseStart_1732601 baseEnd_1732601 := by
    simpa [prefixWord, tailWord_1732601, baseEnd_1732601] using wordTrace_append hprefix tailTrace_1732601
  have hstable : (prefixWord ++ tailWord_1732601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732601).length < 2 ^ (prefixWord ++ tailWord_1732601).sum := by decide
  have hdescent : baseEnd_1732601 < baseStart_1732601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732615 : List Nat := [1, 1, 4, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_1732615 : Nat := 118140960795 + 1732615 * 2 ^ 59
def prefixEnd_1732615 : Nat := 4983230072969 + 3 ^ 40 * 1732615 * 2
def baseEnd_1732615 : Nat := 889664284189843869544355

theorem tailTrace_1732615 : CollatzResearch.WordTrace tailWord_1732615 prefixEnd_1732615 889664284189843869544355 := by
  unfold tailWord_1732615
  simp only [CollatzResearch.WordTrace]
  refine ⟨63193660618039236928743299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42129107078692824619162199 63193660618039236928743299)
  ·
    refine ⟨94790490927058855393114949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63193660618039236928743299 94790490927058855393114949)
    ·
      refine ⟨17773217048823535386209053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94790490927058855393114949 17773217048823535386209053)
      ·
        refine ⟨6664956393308825769828395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17773217048823535386209053 6664956393308825769828395)
        ·
          refine ⟨9997434589963238654742593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664956393308825769828395 9997434589963238654742593)
          ·
            refine ⟨7498075942472428991056945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9997434589963238654742593 7498075942472428991056945)
            ·
              refine ⟨5623556956854321743292709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498075942472428991056945 5623556956854321743292709)
              ·
                refine ⟨1054416929410185326867383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5623556956854321743292709 1054416929410185326867383)
                ·
                  refine ⟨1581625394115277990301075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054416929410185326867383 1581625394115277990301075)
                  ·
                    refine ⟨2372438091172916985451613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1581625394115277990301075 2372438091172916985451613)
                    ·
                      refine ⟨889664284189843869544355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2372438091172916985451613 889664284189843869544355)
                      ·
                        rfl

theorem cell23_1732615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_1732615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732615 prefixEnd_1732615 := by exact prefixLift 1732615
  have htrace : WordTrace (prefixWord ++ tailWord_1732615) baseStart_1732615 baseEnd_1732615 := by
    simpa [prefixWord, tailWord_1732615, baseEnd_1732615] using wordTrace_append hprefix tailTrace_1732615
  have hstable : (prefixWord ++ tailWord_1732615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732615).length < 2 ^ (prefixWord ++ tailWord_1732615).sum := by decide
  have hdescent : baseEnd_1732615 < baseStart_1732615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732624 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_1732624 : Nat := 118140960795 + 1732624 * 2 ^ 59
def prefixEnd_1732624 : Nat := 4983230072969 + 3 ^ 40 * 1732624 * 2
def baseEnd_1732624 : Nat := 889668905515734334331813

theorem tailTrace_1732624 : CollatzResearch.WordTrace tailWord_1732624 prefixEnd_1732624 889668905515734334331813 := by
  unfold tailWord_1732624
  simp only [CollatzResearch.WordTrace]
  refine ⟨31596994437503315732910463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42129325916671087643880617 31596994437503315732910463)
  ·
    refine ⟨47395491656254973599365695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31596994437503315732910463 47395491656254973599365695)
    ·
      refine ⟨71093237484382460399048543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47395491656254973599365695 71093237484382460399048543)
      ·
        refine ⟨106639856226573690598572815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71093237484382460399048543 106639856226573690598572815)
        ·
          refine ⟨159959784339860535897859223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106639856226573690598572815 159959784339860535897859223)
          ·
            refine ⟨239939676509790803846788835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159959784339860535897859223 239939676509790803846788835)
            ·
              refine ⟨359909514764686205770183253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239939676509790803846788835 359909514764686205770183253)
              ·
                refine ⟨4217689626148666473869335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 359909514764686205770183253 4217689626148666473869335)
                ·
                  refine ⟨6326534439222999710804003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4217689626148666473869335 6326534439222999710804003)
                  ·
                    refine ⟨9489801658834499566206005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6326534439222999710804003 9489801658834499566206005)
                    ·
                      refine ⟨889668905515734334331813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9489801658834499566206005 889668905515734334331813)
                      ·
                        rfl

theorem cell23_1732624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_1732624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732624 prefixEnd_1732624 := by exact prefixLift 1732624
  have htrace : WordTrace (prefixWord ++ tailWord_1732624) baseStart_1732624 baseEnd_1732624 := by
    simpa [prefixWord, tailWord_1732624, baseEnd_1732624] using wordTrace_append hprefix tailTrace_1732624
  have hstable : (prefixWord ++ tailWord_1732624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732624).length < 2 ^ (prefixWord ++ tailWord_1732624).sum := by decide
  have hdescent : baseEnd_1732624 < baseStart_1732624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732655 : List Nat := [1, 1, 2, 1, 2, 1, 1, 9, 1, 2, 2]
def baseStart_1732655 : Nat := 118140960795 + 1732655 * 2 ^ 59
def prefixEnd_1732655 : Nat := 4983230072969 + 3 ^ 40 * 1732655 * 2
def baseEnd_1732655 : Nat := 889684823416023713044171

theorem tailTrace_1732655 : CollatzResearch.WordTrace tailWord_1732655 prefixEnd_1732655 889684823416023713044171 := by
  unfold tailWord_1732655
  simp only [CollatzResearch.WordTrace]
  refine ⟨63195119537894323760199419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42130079691929549173466279 63195119537894323760199419)
  ·
    refine ⟨94792679306841485640299129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63195119537894323760199419 94792679306841485640299129)
    ·
      refine ⟨71094509480131114230224347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94792679306841485640299129 71094509480131114230224347)
      ·
        refine ⟨106641764220196671345336521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71094509480131114230224347 106641764220196671345336521)
        ·
          refine ⟨79981323165147503509002391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106641764220196671345336521 79981323165147503509002391)
          ·
            refine ⟨119971984747721255263503587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79981323165147503509002391 119971984747721255263503587)
            ·
              refine ⟨179957977121581882895255381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119971984747721255263503587 179957977121581882895255381)
              ·
                refine ⟨1054441272196768845089387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 179957977121581882895255381 1054441272196768845089387)
                ·
                  refine ⟨1581661908295153267634081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054441272196768845089387 1581661908295153267634081)
                  ·
                    refine ⟨1186246431221364950725561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581661908295153267634081 1186246431221364950725561)
                    ·
                      refine ⟨889684823416023713044171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186246431221364950725561 889684823416023713044171)
                      ·
                        rfl

theorem cell23_1732655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 2, 2].length) (baseStart_1732655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732655 prefixEnd_1732655 := by exact prefixLift 1732655
  have htrace : WordTrace (prefixWord ++ tailWord_1732655) baseStart_1732655 baseEnd_1732655 := by
    simpa [prefixWord, tailWord_1732655, baseEnd_1732655] using wordTrace_append hprefix tailTrace_1732655
  have hstable : (prefixWord ++ tailWord_1732655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732655).length < 2 ^ (prefixWord ++ tailWord_1732655).sum := by decide
  have hdescent : baseEnd_1732655 < baseStart_1732655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732658 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_1732658 : Nat := 118140960795 + 1732658 * 2 ^ 59
def prefixEnd_1732658 : Nat := 4983230072969 + 3 ^ 40 * 1732658 * 2
def baseEnd_1732658 : Nat := 889686363857987201306657

theorem tailTrace_1732658 : CollatzResearch.WordTrace tailWord_1732658 prefixEnd_1732658 889686363857987201306657 := by
  unfold tailWord_1732658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15798807239220863818139657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42130152637922303515039085 15798807239220863818139657)
  ·
    refine ⟨11849105429415647863604743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15798807239220863818139657 11849105429415647863604743)
    ·
      refine ⟨17773658144123471795407115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11849105429415647863604743 17773658144123471795407115)
      ·
        refine ⟨26660487216185207693110673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17773658144123471795407115 26660487216185207693110673)
        ·
          refine ⟨19995365412138905769833005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26660487216185207693110673 19995365412138905769833005)
          ·
            refine ⟨7498262029552089663687377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19995365412138905769833005 7498262029552089663687377)
            ·
              refine ⟨5623696522164067247765533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498262029552089663687377 5623696522164067247765533)
              ·
                refine ⟨2108886195811525217912075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5623696522164067247765533 2108886195811525217912075)
                ·
                  refine ⟨3163329293717287826868113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108886195811525217912075 3163329293717287826868113)
                  ·
                    refine ⟨2372496970287965870151085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3163329293717287826868113 2372496970287965870151085)
                    ·
                      refine ⟨889686363857987201306657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2372496970287965870151085 889686363857987201306657)
                      ·
                        rfl

theorem cell23_1732658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_1732658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732658 prefixEnd_1732658 := by exact prefixLift 1732658
  have htrace : WordTrace (prefixWord ++ tailWord_1732658) baseStart_1732658 baseEnd_1732658 := by
    simpa [prefixWord, tailWord_1732658, baseEnd_1732658] using wordTrace_append hprefix tailTrace_1732658
  have hstable : (prefixWord ++ tailWord_1732658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732658).length < 2 ^ (prefixWord ++ tailWord_1732658).sum := by decide
  have hdescent : baseEnd_1732658 < baseStart_1732658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732678 : List Nat := [6, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1732678 : Nat := 118140960795 + 1732678 * 2 ^ 59
def prefixEnd_1732678 : Nat := 4983230072969 + 3 ^ 40 * 1732678 * 2
def baseEnd_1732678 : Nat := 32951727165595449002095

theorem tailTrace_1732678 : CollatzResearch.WordTrace tailWord_1732678 prefixEnd_1732678 32951727165595449002095 := by
  unfold tailWord_1732678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974873700525343709008959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42130638944540665792191125 1974873700525343709008959)
  ·
    refine ⟨2962310550788015563513439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974873700525343709008959 2962310550788015563513439)
    ·
      refine ⟨4443465826182023345270159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962310550788015563513439 4443465826182023345270159)
      ·
        refine ⟨6665198739273035017905239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4443465826182023345270159 6665198739273035017905239)
        ·
          refine ⟨9997798108909552526857859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6665198739273035017905239 9997798108909552526857859)
          ·
            refine ⟨14996697163364328790286789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9997798108909552526857859 14996697163364328790286789)
            ·
              refine ⟨2811880718130811648178773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14996697163364328790286789 2811880718130811648178773)
              ·
                refine ⟨32951727165595449002095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2811880718130811648178773 32951727165595449002095)
                ·
                  rfl

theorem cell23_1732678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1732678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732678 prefixEnd_1732678 := by exact prefixLift 1732678
  have htrace : WordTrace (prefixWord ++ tailWord_1732678) baseStart_1732678 baseEnd_1732678 := by
    simpa [prefixWord, tailWord_1732678, baseEnd_1732678] using wordTrace_append hprefix tailTrace_1732678
  have hstable : (prefixWord ++ tailWord_1732678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732678).length < 2 ^ (prefixWord ++ tailWord_1732678).sum := by decide
  have hdescent : baseEnd_1732678 < baseStart_1732678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732698 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2]
def baseStart_1732698 : Nat := 118140960795 + 1732698 * 2 ^ 59
def prefixEnd_1732698 : Nat := 4983230072969 + 3 ^ 40 * 1732698 * 2
def baseEnd_1732698 : Nat := 889706903084167044806473

theorem tailTrace_1732698 : CollatzResearch.WordTrace tailWord_1732698 prefixEnd_1732698 889706903084167044806473 := by
  unfold tailWord_1732698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799171969184635526003687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42131125251159028069343165 15799171969184635526003687)
  ·
    refine ⟨23698757953776953289005531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15799171969184635526003687 23698757953776953289005531)
    ·
      refine ⟨35548136930665429933508297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23698757953776953289005531 35548136930665429933508297)
      ·
        refine ⟨26661102697999072450131223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35548136930665429933508297 26661102697999072450131223)
        ·
          refine ⟨39991654046998608675196835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26661102697999072450131223 39991654046998608675196835)
          ·
            refine ⟨59987481070497913012795253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39991654046998608675196835 59987481070497913012795253)
            ·
              refine ⟨5623826350359179344949555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59987481070497913012795253 5623826350359179344949555)
              ·
                refine ⟨8435739525538769017424333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623826350359179344949555 8435739525538769017424333)
                ·
                  refine ⟨3163402322077038381534125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8435739525538769017424333 3163402322077038381534125)
                  ·
                    refine ⟨1186275870778889393075297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3163402322077038381534125 1186275870778889393075297)
                    ·
                      refine ⟨889706903084167044806473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186275870778889393075297 889706903084167044806473)
                      ·
                        rfl

theorem cell23_1732698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_1732698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732698 prefixEnd_1732698 := by exact prefixLift 1732698
  have htrace : WordTrace (prefixWord ++ tailWord_1732698) baseStart_1732698 baseEnd_1732698 := by
    simpa [prefixWord, tailWord_1732698, baseEnd_1732698] using wordTrace_append hprefix tailTrace_1732698
  have hstable : (prefixWord ++ tailWord_1732698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732698).length < 2 ^ (prefixWord ++ tailWord_1732698).sum := by decide
  have hdescent : baseEnd_1732698 < baseStart_1732698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732702 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1732702 : Nat := 118140960795 + 1732702 * 2 ^ 59
def prefixEnd_1732702 : Nat := 4983230072969 + 3 ^ 40 * 1732702 * 2
def baseEnd_1732702 : Nat := 889708957006785029156455

theorem tailTrace_1732702 : CollatzResearch.WordTrace tailWord_1732702 prefixEnd_1732702 889708957006785029156455 := by
  unfold tailWord_1732702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899604221090506348395045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42131222512482700524773573 7899604221090506348395045)
  ·
    refine ⟨1481175791454469940324071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7899604221090506348395045 1481175791454469940324071)
    ·
      refine ⟨2221763687181704910486107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1481175791454469940324071 2221763687181704910486107)
      ·
        refine ⟨3332645530772557365729161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221763687181704910486107 3332645530772557365729161)
        ·
          refine ⟨2499484148079418024296871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3332645530772557365729161 2499484148079418024296871)
          ·
            refine ⟨3749226222119127036445307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499484148079418024296871 3749226222119127036445307)
            ·
              refine ⟨5623839333178690554667961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749226222119127036445307 5623839333178690554667961)
              ·
                refine ⟨4217879499884017916000971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5623839333178690554667961 4217879499884017916000971)
                ·
                  refine ⟨6326819249826026874001457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4217879499884017916000971 6326819249826026874001457)
                  ·
                    refine ⟨4745114437369520155501093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6326819249826026874001457 4745114437369520155501093)
                    ·
                      refine ⟨889708957006785029156455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4745114437369520155501093 889708957006785029156455)
                      ·
                        rfl

theorem cell23_1732702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1732702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732702 prefixEnd_1732702 := by exact prefixLift 1732702
  have htrace : WordTrace (prefixWord ++ tailWord_1732702) baseStart_1732702 baseEnd_1732702 := by
    simpa [prefixWord, tailWord_1732702, baseEnd_1732702] using wordTrace_append hprefix tailTrace_1732702
  have hstable : (prefixWord ++ tailWord_1732702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732702).length < 2 ^ (prefixWord ++ tailWord_1732702).sum := by decide
  have hdescent : baseEnd_1732702 < baseStart_1732702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732741 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_1732741 : Nat := 118140960795 + 1732741 * 2 ^ 59
def prefixEnd_1732741 : Nat := 4983230072969 + 3 ^ 40 * 1732741 * 2
def baseEnd_1732741 : Nat := 889728982752310376568775

theorem tailTrace_1732741 : CollatzResearch.WordTrace tailWord_1732741 prefixEnd_1732741 889728982752310376568775 := by
  unfold tailWord_1732741
  simp only [CollatzResearch.WordTrace]
  refine ⟨63198256215582760447830077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42132170810388506965220051 63198256215582760447830077)
  ·
    refine ⟨23699346080843535167936279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63198256215582760447830077 23699346080843535167936279)
    ·
      refine ⟨35549019121265302751904419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23699346080843535167936279 35549019121265302751904419)
      ·
        refine ⟨53323528681897954127856629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35549019121265302751904419 53323528681897954127856629)
        ·
          refine ⟨4999080813927933199486559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53323528681897954127856629 4999080813927933199486559)
          ·
            refine ⟨7498621220891899799229839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999080813927933199486559 7498621220891899799229839)
            ·
              refine ⟨11247931831337849698844759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498621220891899799229839 11247931831337849698844759)
              ·
                refine ⟨16871897747006774548267139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11247931831337849698844759 16871897747006774548267139)
                ·
                  refine ⟨25307846620510161822400709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16871897747006774548267139 25307846620510161822400709)
                  ·
                    refine ⟨4745221241345655341700133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25307846620510161822400709 4745221241345655341700133)
                    ·
                      refine ⟨889728982752310376568775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4745221241345655341700133 889728982752310376568775)
                      ·
                        rfl

theorem cell23_1732741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_1732741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732741 prefixEnd_1732741 := by exact prefixLift 1732741
  have htrace : WordTrace (prefixWord ++ tailWord_1732741) baseStart_1732741 baseEnd_1732741 := by
    simpa [prefixWord, tailWord_1732741, baseEnd_1732741] using wordTrace_append hprefix tailTrace_1732741
  have hstable : (prefixWord ++ tailWord_1732741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732741).length < 2 ^ (prefixWord ++ tailWord_1732741).sum := by decide
  have hdescent : baseEnd_1732741 < baseStart_1732741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732745 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 2, 2, 2]
def baseStart_1732745 : Nat := 118140960795 + 1732745 * 2 ^ 59
def prefixEnd_1732745 : Nat := 4983230072969 + 3 ^ 40 * 1732745 * 2
def baseEnd_1732745 : Nat := 889731036674928360918757

theorem tailTrace_1732745 : CollatzResearch.WordTrace tailWord_1732745 prefixEnd_1732745 889731036674928360918757 := by
  unfold tailWord_1732745
  simp only [CollatzResearch.WordTrace]
  refine ⟨63198402107568269130975689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42132268071712179420650459 63198402107568269130975689)
  ·
    refine ⟨47398801580676201848231767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63198402107568269130975689 47398801580676201848231767)
    ·
      refine ⟨71098202371014302772347651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47398801580676201848231767 71098202371014302772347651)
      ·
        refine ⟨106647303556521454158521477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71098202371014302772347651 106647303556521454158521477)
        ·
          refine ⟨19996369416847772654722777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106647303556521454158521477 19996369416847772654722777)
          ·
            refine ⟨14997277062635829491042083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19996369416847772654722777 14997277062635829491042083)
            ·
              refine ⟨22495915593953744236563125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14997277062635829491042083 22495915593953744236563125)
              ·
                refine ⟨2108992086933163522177793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22495915593953744236563125 2108992086933163522177793)
                ·
                  refine ⟨1581744065199872641633345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108992086933163522177793 1581744065199872641633345)
                  ·
                    refine ⟨1186308048899904481225009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581744065199872641633345 1186308048899904481225009)
                    ·
                      refine ⟨889731036674928360918757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186308048899904481225009 889731036674928360918757)
                      ·
                        rfl

theorem cell23_1732745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 2, 2].length) (baseStart_1732745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732745 prefixEnd_1732745 := by exact prefixLift 1732745
  have htrace : WordTrace (prefixWord ++ tailWord_1732745) baseStart_1732745 baseEnd_1732745 := by
    simpa [prefixWord, tailWord_1732745, baseEnd_1732745] using wordTrace_append hprefix tailTrace_1732745
  have hstable : (prefixWord ++ tailWord_1732745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732745).length < 2 ^ (prefixWord ++ tailWord_1732745).sum := by decide
  have hdescent : baseEnd_1732745 < baseStart_1732745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732766 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_1732766 : Nat := 118140960795 + 1732766 * 2 ^ 59
def prefixEnd_1732766 : Nat := 4983230072969 + 3 ^ 40 * 1732766 * 2
def baseEnd_1732766 : Nat := 889741819768672778756161

theorem tailTrace_1732766 : CollatzResearch.WordTrace tailWord_1732766 prefixEnd_1732766 889741819768672778756161 := by
  unfold tailWord_1732766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899896005061523714686269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42132778693661459811660101 7899896005061523714686269)
  ·
    refine ⟨2962461001898071393007351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7899896005061523714686269 2962461001898071393007351)
    ·
      refine ⟨4443691502847107089511027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962461001898071393007351 4443691502847107089511027)
      ·
        refine ⟨6665537254270660634266541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4443691502847107089511027 6665537254270660634266541)
        ·
          refine ⟨2499576470351497737849953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6665537254270660634266541 2499576470351497737849953)
          ·
            refine ⟨1874682352763623303387465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2499576470351497737849953 1874682352763623303387465)
            ·
              refine ⟨1406011764572717477540599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874682352763623303387465 1406011764572717477540599)
              ·
                refine ⟨2109017646859076216310899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406011764572717477540599 2109017646859076216310899)
                ·
                  refine ⟨3163526470288614324466349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109017646859076216310899 3163526470288614324466349)
                  ·
                    refine ⟨1186322426358230371674881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3163526470288614324466349 1186322426358230371674881)
                    ·
                      refine ⟨889741819768672778756161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186322426358230371674881 889741819768672778756161)
                      ·
                        rfl

theorem cell23_1732766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_1732766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732766 prefixEnd_1732766 := by exact prefixLift 1732766
  have htrace : WordTrace (prefixWord ++ tailWord_1732766) baseStart_1732766 baseEnd_1732766 := by
    simpa [prefixWord, tailWord_1732766, baseEnd_1732766] using wordTrace_append hprefix tailTrace_1732766
  have hstable : (prefixWord ++ tailWord_1732766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732766).length < 2 ^ (prefixWord ++ tailWord_1732766).sum := by decide
  have hdescent : baseEnd_1732766 < baseStart_1732766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732768 : List Nat := [2, 1, 1, 4, 2, 2, 1, 5, 5]
def baseStart_1732768 : Nat := 118140960795 + 1732768 * 2 ^ 59
def prefixEnd_1732768 : Nat := 4983230072969 + 3 ^ 40 * 1732768 * 2
def baseEnd_1732768 : Nat := 98860316303331307881239

theorem tailTrace_1732768 : CollatzResearch.WordTrace tailWord_1732768 prefixEnd_1732768 98860316303331307881239 := by
  unfold tailWord_1732768
  simp only [CollatzResearch.WordTrace]
  refine ⟨31599620493242472029531479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42132827324323296039375305 31599620493242472029531479)
  ·
    refine ⟨47399430739863708044297219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31599620493242472029531479 47399430739863708044297219)
    ·
      refine ⟨71099146109795562066445829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47399430739863708044297219 71099146109795562066445829)
      ·
        refine ⟨13331089895586667887458593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71099146109795562066445829 13331089895586667887458593)
        ·
          refine ⟨9998317421690000915593945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13331089895586667887458593 9998317421690000915593945)
          ·
            refine ⟨7498738066267500686695459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9998317421690000915593945 7498738066267500686695459)
            ·
              refine ⟨11248107099401251030043189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498738066267500686695459 11248107099401251030043189)
              ·
                refine ⟨1054510040568867284066549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11248107099401251030043189 1054510040568867284066549)
                ·
                  refine ⟨98860316303331307881239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1054510040568867284066549 98860316303331307881239)
                  ·
                    rfl

theorem cell23_1732768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 5].length) (baseStart_1732768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732768 prefixEnd_1732768 := by exact prefixLift 1732768
  have htrace : WordTrace (prefixWord ++ tailWord_1732768) baseStart_1732768 baseEnd_1732768 := by
    simpa [prefixWord, tailWord_1732768, baseEnd_1732768] using wordTrace_append hprefix tailTrace_1732768
  have hstable : (prefixWord ++ tailWord_1732768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732768).length < 2 ^ (prefixWord ++ tailWord_1732768).sum := by decide
  have hdescent : baseEnd_1732768 < baseStart_1732768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732818 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1732818 : Nat := 118140960795 + 1732818 * 2 ^ 59
def prefixEnd_1732818 : Nat := 4983230072969 + 3 ^ 40 * 1732818 * 2
def baseEnd_1732818 : Nat := 889768520762706575305921

theorem tailTrace_1732818 : CollatzResearch.WordTrace tailWord_1732818 prefixEnd_1732818 889768520762706575305921 := by
  unfold tailWord_1732818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15800266159075950649595777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42134043090869201732255405 15800266159075950649595777)
  ·
    refine ⟨11850199619306962987196833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15800266159075950649595777 11850199619306962987196833)
    ·
      refine ⟨8887649714480222240397625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11850199619306962987196833 8887649714480222240397625)
      ·
        refine ⟨6665737285860166680298219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8887649714480222240397625 6665737285860166680298219)
        ·
          refine ⟨9998605928790250020447329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6665737285860166680298219 9998605928790250020447329)
          ·
            refine ⟨7498954446592687515335497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9998605928790250020447329 7498954446592687515335497)
            ·
              refine ⟨5624215834944515636501623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498954446592687515335497 5624215834944515636501623)
              ·
                refine ⟨8436323752416773454752435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624215834944515636501623 8436323752416773454752435)
                ·
                  refine ⟨12654485628625160182128653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8436323752416773454752435 12654485628625160182128653)
                  ·
                    refine ⟨4745432110734435068298245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12654485628625160182128653 4745432110734435068298245)
                    ·
                      refine ⟨889768520762706575305921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4745432110734435068298245 889768520762706575305921)
                      ·
                        rfl

theorem cell23_1732818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1732818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732818 prefixEnd_1732818 := by exact prefixLift 1732818
  have htrace : WordTrace (prefixWord ++ tailWord_1732818) baseStart_1732818 baseEnd_1732818 := by
    simpa [prefixWord, tailWord_1732818, baseEnd_1732818] using wordTrace_append hprefix tailTrace_1732818
  have hstable : (prefixWord ++ tailWord_1732818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732818).length < 2 ^ (prefixWord ++ tailWord_1732818).sum := by decide
  have hdescent : baseEnd_1732818 < baseStart_1732818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732858 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 6]
def baseStart_1732858 : Nat := 118140960795 + 1732858 * 2 ^ 59
def prefixEnd_1732858 : Nat := 4983230072969 + 3 ^ 40 * 1732858 * 2
def baseEnd_1732858 : Nat := 98865451109876268756193

theorem tailTrace_1732858 : CollatzResearch.WordTrace tailWord_1732858 prefixEnd_1732858 98865451109876268756193 := by
  unfold tailWord_1732858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15800630889039722357459807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42135015704105926286559485 15800630889039722357459807)
  ·
    refine ⟨23700946333559583536189711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15800630889039722357459807 23700946333559583536189711)
    ·
      refine ⟨35551419500339375304284567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23700946333559583536189711 35551419500339375304284567)
      ·
        refine ⟨53327129250509062956426851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35551419500339375304284567 53327129250509062956426851)
        ·
          refine ⟨79990693875763594434640277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53327129250509062956426851 79990693875763594434640277)
          ·
            refine ⟨3749563775426418489123763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79990693875763594434640277 3749563775426418489123763)
            ·
              refine ⟨5624345663139627733685645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749563775426418489123763 5624345663139627733685645)
              ·
                refine ⟨2109129623677360400132117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5624345663139627733685645 2109129623677360400132117)
                ·
                  refine ⟨98865451109876268756193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2109129623677360400132117 98865451109876268756193)
                  ·
                    rfl

theorem cell23_1732858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_1732858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732858 prefixEnd_1732858 := by exact prefixLift 1732858
  have htrace : WordTrace (prefixWord ++ tailWord_1732858) baseStart_1732858 baseEnd_1732858 := by
    simpa [prefixWord, tailWord_1732858, baseEnd_1732858] using wordTrace_append hprefix tailTrace_1732858
  have hstable : (prefixWord ++ tailWord_1732858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732858).length < 2 ^ (prefixWord ++ tailWord_1732858).sum := by decide
  have hdescent : baseEnd_1732858 < baseStart_1732858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732861 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1732861 : Nat := 118140960795 + 1732861 * 2 ^ 59
def prefixEnd_1732861 : Nat := 4983230072969 + 3 ^ 40 * 1732861 * 2
def baseEnd_1732861 : Nat := 889790600430849907068223

theorem tailTrace_1732861 : CollatzResearch.WordTrace tailWord_1732861 prefixEnd_1732861 889790600430849907068223 := by
  unfold tailWord_1732861
  simp only [CollatzResearch.WordTrace]
  refine ⟨63202632975148020942198437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42135088650098680628132291 63202632975148020942198437)
  ·
    refine ⟨11850493682840253926662207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63202632975148020942198437 11850493682840253926662207)
    ·
      refine ⟨17775740524260380889993311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11850493682840253926662207 17775740524260380889993311)
      ·
        refine ⟨26663610786390571334989967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17775740524260380889993311 26663610786390571334989967)
        ·
          refine ⟨39995416179585857002484951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26663610786390571334989967 39995416179585857002484951)
          ·
            refine ⟨59993124269378785503727427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39995416179585857002484951 59993124269378785503727427)
            ·
              refine ⟨89989686404068178255591141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59993124269378785503727427 89989686404068178255591141)
              ·
                refine ⟨16873066200762783422923339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89989686404068178255591141 16873066200762783422923339)
                ·
                  refine ⟨25309599301144175134385009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16873066200762783422923339 25309599301144175134385009)
                  ·
                    refine ⟨18982199475858131350788757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25309599301144175134385009 18982199475858131350788757)
                    ·
                      refine ⟨889790600430849907068223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18982199475858131350788757 889790600430849907068223)
                      ·
                        rfl

theorem cell23_1732861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1732861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732861 prefixEnd_1732861 := by exact prefixLift 1732861
  have htrace : WordTrace (prefixWord ++ tailWord_1732861) baseStart_1732861 baseEnd_1732861 := by
    simpa [prefixWord, tailWord_1732861, baseEnd_1732861] using wordTrace_append hprefix tailTrace_1732861
  have hstable : (prefixWord ++ tailWord_1732861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732861).length < 2 ^ (prefixWord ++ tailWord_1732861).sum := by decide
  have hdescent : baseEnd_1732861 < baseStart_1732861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732908 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_1732908 : Nat := 118140960795 + 1732908 * 2 ^ 59
def prefixEnd_1732908 : Nat := 4983230072969 + 3 ^ 40 * 1732908 * 2
def baseEnd_1732908 : Nat := 889814734021611223180507

theorem tailTrace_1732908 : CollatzResearch.WordTrace tailWord_1732908 prefixEnd_1732908 889814734021611223180507 := by
  unfold tailWord_1732908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31602173602988873984579689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42136231470651831979439585 31602173602988873984579689)
  ·
    refine ⟨23701630202241655488434767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31602173602988873984579689 23701630202241655488434767)
    ·
      refine ⟨35552445303362483232652151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23701630202241655488434767 35552445303362483232652151)
      ·
        refine ⟨53328667955043724848978227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35552445303362483232652151 53328667955043724848978227)
        ·
          refine ⟨79993001932565587273467341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53328667955043724848978227 79993001932565587273467341)
          ·
            refine ⟨29997375724712095227550253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79993001932565587273467341 29997375724712095227550253)
            ·
              refine ⟨11249015896767035710331345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29997375724712095227550253 11249015896767035710331345)
              ·
                refine ⟨8436761922575276782748509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11249015896767035710331345 8436761922575276782748509)
                ·
                  refine ⟨3163785720965728793530691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8436761922575276782748509 3163785720965728793530691)
                  ·
                    refine ⟨4745678581448593190296037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3163785720965728793530691 4745678581448593190296037)
                    ·
                      refine ⟨889814734021611223180507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4745678581448593190296037 889814734021611223180507)
                      ·
                        rfl

theorem cell23_1732908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_1732908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732908 prefixEnd_1732908 := by exact prefixLift 1732908
  have htrace : WordTrace (prefixWord ++ tailWord_1732908) baseStart_1732908 baseEnd_1732908 := by
    simpa [prefixWord, tailWord_1732908, baseEnd_1732908] using wordTrace_append hprefix tailTrace_1732908
  have hstable : (prefixWord ++ tailWord_1732908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732908).length < 2 ^ (prefixWord ++ tailWord_1732908).sum := by decide
  have hdescent : baseEnd_1732908 < baseStart_1732908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732931 : List Nat := [1, 1, 1, 3, 1, 3, 2, 11]
def baseStart_1732931 : Nat := 118140960795 + 1732931 * 2 ^ 59
def prefixEnd_1732931 : Nat := 4983230072969 + 3 ^ 40 * 1732931 * 2
def baseEnd_1732931 : Nat := 32956538669506097525663

theorem tailTrace_1732931 : CollatzResearch.WordTrace tailWord_1732931 prefixEnd_1732931 32956538669506097525663 := by
  unfold tailWord_1732931
  simp only [CollatzResearch.WordTrace]
  refine ⟨63205186084894422897246647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42136790723262948598164431 63205186084894422897246647)
  ·
    refine ⟨94807779127341634345869971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63205186084894422897246647 94807779127341634345869971)
    ·
      refine ⟨142211668691012451518804957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94807779127341634345869971 142211668691012451518804957)
      ·
        refine ⟨53329375759129669319551859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142211668691012451518804957 53329375759129669319551859)
        ·
          refine ⟨79994063638694503979327789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53329375759129669319551859 79994063638694503979327789)
          ·
            refine ⟨29997773864510438992247921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79994063638694503979327789 29997773864510438992247921)
            ·
              refine ⟨22498330398382829244185941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29997773864510438992247921 22498330398382829244185941)
              ·
                refine ⟨32956538669506097525663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22498330398382829244185941 32956538669506097525663)
                ·
                  rfl

theorem cell23_1732931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 11].length) (baseStart_1732931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732931 prefixEnd_1732931 := by exact prefixLift 1732931
  have htrace : WordTrace (prefixWord ++ tailWord_1732931) baseStart_1732931 baseEnd_1732931 := by
    simpa [prefixWord, tailWord_1732931, baseEnd_1732931] using wordTrace_append hprefix tailTrace_1732931
  have hstable : (prefixWord ++ tailWord_1732931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732931).length < 2 ^ (prefixWord ++ tailWord_1732931).sum := by decide
  have hdescent : baseEnd_1732931 < baseStart_1732931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732948 : List Nat := [2, 4, 1, 1, 2, 3, 10]
def baseStart_1732948 : Nat := 118140960795 + 1732948 * 2 ^ 59
def prefixEnd_1732948 : Nat := 4983230072969 + 3 ^ 40 * 1732948 * 2
def baseEnd_1732948 : Nat := 10985620657380136625683

theorem tailTrace_1732948 : CollatzResearch.WordTrace tailWord_1732948 prefixEnd_1732948 10985620657380136625683 := by
  unfold tailWord_1732948
  simp only [CollatzResearch.WordTrace]
  refine ⟨31602903062916417400307749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42137204083888556533743665 31602903062916417400307749)
  ·
    refine ⟨5925544324296828262557703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31602903062916417400307749 5925544324296828262557703)
    ·
      refine ⟨8888316486445242393836555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5925544324296828262557703 8888316486445242393836555)
      ·
        refine ⟨13332474729667863590754833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8888316486445242393836555 13332474729667863590754833)
        ·
          refine ⟨9999356047250897693066125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13332474729667863590754833 9999356047250897693066125)
          ·
            refine ⟨3749758517719086634899797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9999356047250897693066125 3749758517719086634899797)
            ·
              refine ⟨10985620657380136625683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3749758517719086634899797 10985620657380136625683)
              ·
                rfl

theorem cell23_1732948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 10].length) (baseStart_1732948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732948 prefixEnd_1732948 := by exact prefixLift 1732948
  have htrace : WordTrace (prefixWord ++ tailWord_1732948) baseStart_1732948 baseEnd_1732948 := by
    simpa [prefixWord, tailWord_1732948, baseEnd_1732948] using wordTrace_append hprefix tailTrace_1732948
  have hstable : (prefixWord ++ tailWord_1732948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732948).length < 2 ^ (prefixWord ++ tailWord_1732948).sum := by decide
  have hdescent : baseEnd_1732948 < baseStart_1732948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732959 : List Nat := [1, 1, 2, 3, 1, 2, 4, 4, 1, 2, 2]
def baseStart_1732959 : Nat := 118140960795 + 1732959 * 2 ^ 59
def prefixEnd_1732959 : Nat := 4983230072969 + 3 ^ 40 * 1732959 * 2
def baseEnd_1732959 : Nat := 889840921534990523642773

theorem tailTrace_1732959 : CollatzResearch.WordTrace tailWord_1732959 prefixEnd_1732959 889840921534990523642773 := by
  unfold tailWord_1732959
  simp only [CollatzResearch.WordTrace]
  refine ⟨63206207328792983679265931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42137471552528655786177287 63206207328792983679265931)
  ·
    refine ⟨94809310993189475518898897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63206207328792983679265931 94809310993189475518898897)
    ·
      refine ⟨71106983244892106639174173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94809310993189475518898897 71106983244892106639174173)
      ·
        refine ⟨26665118716834539989690315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71106983244892106639174173 26665118716834539989690315)
        ·
          refine ⟨39997678075251809984535473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26665118716834539989690315 39997678075251809984535473)
          ·
            refine ⟨29998258556438857488401605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39997678075251809984535473 29998258556438857488401605)
            ·
              refine ⟨5624673479332285779075301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29998258556438857488401605 5624673479332285779075301)
              ·
                refine ⟨1054626277374803583576619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5624673479332285779075301 1054626277374803583576619)
                ·
                  refine ⟨1581939416062205375364929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054626277374803583576619 1581939416062205375364929)
                  ·
                    refine ⟨1186454562046654031523697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581939416062205375364929 1186454562046654031523697)
                    ·
                      refine ⟨889840921534990523642773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186454562046654031523697 889840921534990523642773)
                      ·
                        rfl

theorem cell23_1732959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_1732959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732959 prefixEnd_1732959 := by exact prefixLift 1732959
  have htrace : WordTrace (prefixWord ++ tailWord_1732959) baseStart_1732959 baseEnd_1732959 := by
    simpa [prefixWord, tailWord_1732959, baseEnd_1732959] using wordTrace_append hprefix tailTrace_1732959
  have hstable : (prefixWord ++ tailWord_1732959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732959).length < 2 ^ (prefixWord ++ tailWord_1732959).sum := by decide
  have hdescent : baseEnd_1732959 < baseStart_1732959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732972 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_1732972 : Nat := 118140960795 + 1732972 * 2 ^ 59
def prefixEnd_1732972 : Nat := 4983230072969 + 3 ^ 40 * 1732972 * 2
def baseEnd_1732972 : Nat := 889847596783498972780213

theorem tailTrace_1732972 : CollatzResearch.WordTrace tailWord_1732972 prefixEnd_1732972 889847596783498972780213 := by
  unfold tailWord_1732972
  simp only [CollatzResearch.WordTrace]
  refine ⟨31603340738872943449744585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42137787651830591266326113 31603340738872943449744585)
  ·
    refine ⟨23702505554154707587308439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31603340738872943449744585 23702505554154707587308439)
    ·
      refine ⟨35553758331232061380962659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23702505554154707587308439 35553758331232061380962659)
      ·
        refine ⟨53330637496848092071443989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35553758331232061380962659 53330637496848092071443989)
        ·
          refine ⟨2499873632664754315848937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53330637496848092071443989 2499873632664754315848937)
          ·
            refine ⟨1874905224498565736886703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2499873632664754315848937 1874905224498565736886703)
            ·
              refine ⟨2812357836747848605330055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874905224498565736886703 2812357836747848605330055)
              ·
                refine ⟨4218536755121772907995083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812357836747848605330055 4218536755121772907995083)
                ·
                  refine ⟨6327805132682659361992625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218536755121772907995083 6327805132682659361992625)
                  ·
                    refine ⟨4745853849511994521494469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327805132682659361992625 4745853849511994521494469)
                    ·
                      refine ⟨889847596783498972780213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4745853849511994521494469 889847596783498972780213)
                      ·
                        rfl

theorem cell23_1732972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_1732972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732972 prefixEnd_1732972 := by exact prefixLift 1732972
  have htrace : WordTrace (prefixWord ++ tailWord_1732972) baseStart_1732972 baseEnd_1732972 := by
    simpa [prefixWord, tailWord_1732972, baseEnd_1732972] using wordTrace_append hprefix tailTrace_1732972
  have hstable : (prefixWord ++ tailWord_1732972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732972).length < 2 ^ (prefixWord ++ tailWord_1732972).sum := by decide
  have hdescent : baseEnd_1732972 < baseStart_1732972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732982 : List Nat := [5, 1, 1, 4, 1, 1, 1, 9]
def baseStart_1732982 : Nat := 118140960795 + 1732982 * 2 ^ 59
def prefixEnd_1732982 : Nat := 4983230072969 + 3 ^ 40 * 1732982 * 2
def baseEnd_1732982 : Nat := 32957508577409034579821

theorem tailTrace_1732982 : CollatzResearch.WordTrace tailWord_1732982 prefixEnd_1732982 32957508577409034579821 := by
  unfold tailWord_1732982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950440387981853662959575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42138030805139772404902133 3950440387981853662959575)
  ·
    refine ⟨5925660581972780494439363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3950440387981853662959575 5925660581972780494439363)
    ·
      refine ⟨8888490872959170741659045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5925660581972780494439363 8888490872959170741659045)
      ·
        refine ⟨1666592038679844514061071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8888490872959170741659045 1666592038679844514061071)
        ·
          refine ⟨2499888058019766771091607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666592038679844514061071 2499888058019766771091607)
          ·
            refine ⟨3749832087029650156637411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499888058019766771091607 3749832087029650156637411)
            ·
              refine ⟨5624748130544475234956117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749832087029650156637411 5624748130544475234956117)
              ·
                refine ⟨32957508577409034579821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5624748130544475234956117 32957508577409034579821)
                ·
                  rfl

theorem cell23_1732982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_1732982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732982 prefixEnd_1732982 := by exact prefixLift 1732982
  have htrace : WordTrace (prefixWord ++ tailWord_1732982) baseStart_1732982 baseEnd_1732982 := by
    simpa [prefixWord, tailWord_1732982, baseEnd_1732982] using wordTrace_append hprefix tailTrace_1732982
  have hstable : (prefixWord ++ tailWord_1732982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732982).length < 2 ^ (prefixWord ++ tailWord_1732982).sum := by decide
  have hdescent : baseEnd_1732982 < baseStart_1732982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732993 : List Nat := [1, 2, 4, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_1732993 : Nat := 118140960795 + 1732993 * 2 ^ 59
def prefixEnd_1732993 : Nat := 4983230072969 + 3 ^ 40 * 1732993 * 2
def baseEnd_1732993 : Nat := 889858379877243390617617

theorem tailTrace_1732993 : CollatzResearch.WordTrace tailWord_1732993 prefixEnd_1732993 889858379877243390617617 := by
  unfold tailWord_1732993
  simp only [CollatzResearch.WordTrace]
  refine ⟨63207447410669807486003633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42138298273779871657335755 63207447410669807486003633)
  ·
    refine ⟨47405585558002355614502725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63207447410669807486003633 47405585558002355614502725)
    ·
      refine ⟨8888547292125441677719261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47405585558002355614502725 8888547292125441677719261)
      ·
        refine ⟨3333205234547040629144723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8888547292125441677719261 3333205234547040629144723)
        ·
          refine ⟨4999807851820560943717085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333205234547040629144723 4999807851820560943717085)
          ·
            refine ⟨1874927944432710353893907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4999807851820560943717085 1874927944432710353893907)
            ·
              refine ⟨2812391916649065530840861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874927944432710353893907 2812391916649065530840861)
              ·
                refine ⟨1054646968743399574065323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2812391916649065530840861 1054646968743399574065323)
                ·
                  refine ⟨1581970453115099361097985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054646968743399574065323 1581970453115099361097985)
                  ·
                    refine ⟨1186477839836324520823489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581970453115099361097985 1186477839836324520823489)
                    ·
                      refine ⟨889858379877243390617617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1186477839836324520823489 889858379877243390617617)
                      ·
                        rfl

theorem cell23_1732993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_1732993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1732993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1732993 prefixEnd_1732993 := by exact prefixLift 1732993
  have htrace : WordTrace (prefixWord ++ tailWord_1732993) baseStart_1732993 baseEnd_1732993 := by
    simpa [prefixWord, tailWord_1732993, baseEnd_1732993] using wordTrace_append hprefix tailTrace_1732993
  have hstable : (prefixWord ++ tailWord_1732993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732993).length < 2 ^ (prefixWord ++ tailWord_1732993).sum := by decide
  have hdescent : baseEnd_1732993 < baseStart_1732993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733085 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1733085 : Nat := 118140960795 + 1733085 * 2 ^ 59
def prefixEnd_1733085 : Nat := 4983230072969 + 3 ^ 40 * 1733085 * 2
def baseEnd_1733085 : Nat := 296635206699152343555731

theorem tailTrace_1733085 : CollatzResearch.WordTrace tailWord_1733085 prefixEnd_1733085 296635206699152343555731 := by
  unfold tailWord_1733085
  simp only [CollatzResearch.WordTrace]
  refine ⟨63210802926336507198352709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42140535284224338132235139 63210802926336507198352709)
  ·
    refine ⟨11852025548688095099691133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63210802926336507198352709 11852025548688095099691133)
    ·
      refine ⟨4444509580758035662384175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11852025548688095099691133 4444509580758035662384175)
      ·
        refine ⟨6666764371137053493576263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444509580758035662384175 6666764371137053493576263)
        ·
          refine ⟨10000146556705580240364395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6666764371137053493576263 10000146556705580240364395)
          ·
            refine ⟨15000219835058370360546593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10000146556705580240364395 15000219835058370360546593)
            ·
              refine ⟨11250164876293777770409945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15000219835058370360546593 11250164876293777770409945)
              ·
                refine ⟨8437623657220333327807459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11250164876293777770409945 8437623657220333327807459)
                ·
                  refine ⟨12656435485830499991711189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8437623657220333327807459 12656435485830499991711189)
                  ·
                    refine ⟨296635206699152343555731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12656435485830499991711189 296635206699152343555731)
                    ·
                      rfl

theorem cell23_1733085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1733085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733085 prefixEnd_1733085 := by exact prefixLift 1733085
  have htrace : WordTrace (prefixWord ++ tailWord_1733085) baseStart_1733085 baseEnd_1733085 := by
    simpa [prefixWord, tailWord_1733085, baseEnd_1733085] using wordTrace_append hprefix tailTrace_1733085
  have hstable : (prefixWord ++ tailWord_1733085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733085).length < 2 ^ (prefixWord ++ tailWord_1733085).sum := by decide
  have hdescent : baseEnd_1733085 < baseStart_1733085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733102 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1733102 : Nat := 118140960795 + 1733102 * 2 ^ 59
def prefixEnd_1733102 : Nat := 4983230072969 + 3 ^ 40 * 1733102 * 2
def baseEnd_1733102 : Nat := 296638116422861154718205

theorem tailTrace_1733102 : CollatzResearch.WordTrace tailWord_1733102 prefixEnd_1733102 296638116422861154718205 := by
  unfold tailWord_1733102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7901427870909364887715195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42140948644849946067814373 7901427870909364887715195)
  ·
    refine ⟨11852141806364047331572793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7901427870909364887715195 11852141806364047331572793)
    ·
      refine ⟨8889106354773035498679595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11852141806364047331572793 8889106354773035498679595)
      ·
        refine ⟨13333659532159553248019393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8889106354773035498679595 13333659532159553248019393)
        ·
          refine ⟨10000244649119664936014545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13333659532159553248019393 10000244649119664936014545)
          ·
            refine ⟨7500183486839748702010909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10000244649119664936014545 7500183486839748702010909)
            ·
              refine ⟨2812568807564905763254091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7500183486839748702010909 2812568807564905763254091)
              ·
                refine ⟨4218853211347358644881137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812568807564905763254091 4218853211347358644881137)
                ·
                  refine ⟨3164139908510518983660853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4218853211347358644881137 3164139908510518983660853)
                  ·
                    refine ⟨296638116422861154718205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3164139908510518983660853 296638116422861154718205)
                    ·
                      rfl

theorem cell23_1733102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1733102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733102 prefixEnd_1733102 := by exact prefixLift 1733102
  have htrace : WordTrace (prefixWord ++ tailWord_1733102) baseStart_1733102 baseEnd_1733102 := by
    simpa [prefixWord, tailWord_1733102, baseEnd_1733102] using wordTrace_append hprefix tailTrace_1733102
  have hstable : (prefixWord ++ tailWord_1733102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733102).length < 2 ^ (prefixWord ++ tailWord_1733102).sum := by decide
  have hdescent : baseEnd_1733102 < baseStart_1733102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733105 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_1733105 : Nat := 118140960795 + 1733105 * 2 ^ 59
def prefixEnd_1733105 : Nat := 4983230072969 + 3 ^ 40 * 1733105 * 2
def baseEnd_1733105 : Nat := 889915889710546952417101

theorem tailTrace_1733105 : CollatzResearch.WordTrace tailWord_1733105 prefixEnd_1733105 889915889710546952417101 := by
  unfold tailWord_1733105
  simp only [CollatzResearch.WordTrace]
  refine ⟨63211532386264050614080769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42141021590842700409387179 63211532386264050614080769)
  ·
    refine ⟨47408649289698037960560577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63211532386264050614080769 47408649289698037960560577)
    ·
      refine ⟨35556486967273528470420433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47408649289698037960560577 35556486967273528470420433)
      ·
        refine ⟨26667365225455146352815325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35556486967273528470420433 26667365225455146352815325)
        ·
          refine ⟨10000261959545679882305747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26667365225455146352815325 10000261959545679882305747)
          ·
            refine ⟨15000392939318519823458621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10000261959545679882305747 15000392939318519823458621)
            ·
              refine ⟨5625147352244444933796983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15000392939318519823458621 5625147352244444933796983)
              ·
                refine ⟨8437721028366667400695475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625147352244444933796983 8437721028366667400695475)
                ·
                  refine ⟨12656581542550001101043213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8437721028366667400695475 12656581542550001101043213)
                  ·
                    refine ⟨4746218078456250412891205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12656581542550001101043213 4746218078456250412891205)
                    ·
                      refine ⟨889915889710546952417101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4746218078456250412891205 889915889710546952417101)
                      ·
                        rfl

theorem cell23_1733105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_1733105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733105 prefixEnd_1733105 := by exact prefixLift 1733105
  have htrace : WordTrace (prefixWord ++ tailWord_1733105) baseStart_1733105 baseEnd_1733105 := by
    simpa [prefixWord, tailWord_1733105, baseEnd_1733105] using wordTrace_append hprefix tailTrace_1733105
  have hstable : (prefixWord ++ tailWord_1733105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733105).length < 2 ^ (prefixWord ++ tailWord_1733105).sum := by decide
  have hdescent : baseEnd_1733105 < baseStart_1733105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733132 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_1733132 : Nat := 118140960795 + 1733132 * 2 ^ 59
def prefixEnd_1733132 : Nat := 4983230072969 + 3 ^ 40 * 1733132 * 2
def baseEnd_1733132 : Nat := 296643251229406115593159

theorem tailTrace_1733132 : CollatzResearch.WordTrace tailWord_1733132 prefixEnd_1733132 296643251229406115593159 := by
  unfold tailWord_1733132
  simp only [CollatzResearch.WordTrace]
  refine ⟨31606258578583117112656825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42141678104777489483542433 31606258578583117112656825)
  ·
    refine ⟨23704693933937337834492619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31606258578583117112656825 23704693933937337834492619)
    ·
      refine ⟨35557040900906006751738929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23704693933937337834492619 35557040900906006751738929)
      ·
        refine ⟨26667780675679505063804197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35557040900906006751738929 26667780675679505063804197)
        ·
          refine ⟨5000208876689907199463287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26667780675679505063804197 5000208876689907199463287)
          ·
            refine ⟨7500313315034860799194931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000208876689907199463287 7500313315034860799194931)
            ·
              refine ⟨11250469972552291198792397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7500313315034860799194931 11250469972552291198792397)
              ·
                refine ⟨4218926239707109199547149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11250469972552291198792397 4218926239707109199547149)
                ·
                  refine ⟨1582097339890165949830181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4218926239707109199547149 1582097339890165949830181)
                  ·
                    refine ⟨296643251229406115593159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1582097339890165949830181 296643251229406115593159)
                    ·
                      rfl

theorem cell23_1733132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_1733132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733132 prefixEnd_1733132 := by exact prefixLift 1733132
  have htrace : WordTrace (prefixWord ++ tailWord_1733132) baseStart_1733132 baseEnd_1733132 := by
    simpa [prefixWord, tailWord_1733132, baseEnd_1733132] using wordTrace_append hprefix tailTrace_1733132
  have hstable : (prefixWord ++ tailWord_1733132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733132).length < 2 ^ (prefixWord ++ tailWord_1733132).sum := by decide
  have hdescent : baseEnd_1733132 < baseStart_1733132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733189 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_1733189 : Nat := 118140960795 + 1733189 * 2 ^ 59
def prefixEnd_1733189 : Nat := 4983230072969 + 3 ^ 40 * 1733189 * 2
def baseEnd_1733189 : Nat := 889959022085524623766715

theorem tailTrace_1733189 : CollatzResearch.WordTrace tailWord_1733189 prefixEnd_1733189 889959022085524623766715 := by
  unfold tailWord_1733189
  simp only [CollatzResearch.WordTrace]
  refine ⟨63214596117959732960138621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42143064078639821973425747 63214596117959732960138621)
  ·
    refine ⟨23705473544234899860051983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63214596117959732960138621 23705473544234899860051983)
    ·
      refine ⟨35558210316352349790077975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23705473544234899860051983 35558210316352349790077975)
      ·
        refine ⟨53337315474528524685116963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35558210316352349790077975 53337315474528524685116963)
        ·
          refine ⟨80005973211792787027675445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53337315474528524685116963 80005973211792787027675445)
          ·
            refine ⟨7500559988605573783844573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80005973211792787027675445 7500559988605573783844573)
            ·
              refine ⟨2812709995727090168941715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7500559988605573783844573 2812709995727090168941715)
              ·
                refine ⟨4219064993590635253412573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812709995727090168941715 4219064993590635253412573)
                ·
                  refine ⟨1582149372596488220029715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4219064993590635253412573 1582149372596488220029715)
                  ·
                    refine ⟨2373224058894732330044573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582149372596488220029715 2373224058894732330044573)
                    ·
                      refine ⟨889959022085524623766715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2373224058894732330044573 889959022085524623766715)
                      ·
                        rfl

theorem cell23_1733189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_1733189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733189 prefixEnd_1733189 := by exact prefixLift 1733189
  have htrace : WordTrace (prefixWord ++ tailWord_1733189) baseStart_1733189 baseEnd_1733189 := by
    simpa [prefixWord, tailWord_1733189, baseEnd_1733189] using wordTrace_append hprefix tailTrace_1733189
  have hstable : (prefixWord ++ tailWord_1733189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733189).length < 2 ^ (prefixWord ++ tailWord_1733189).sum := by decide
  have hdescent : baseEnd_1733189 < baseStart_1733189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733215 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1733215 : Nat := 118140960795 + 1733215 * 2 ^ 59
def prefixEnd_1733215 : Nat := 4983230072969 + 3 ^ 40 * 1733215 * 2
def baseEnd_1733215 : Nat := 889972372582541522041595

theorem tailTrace_1733215 : CollatzResearch.WordTrace tailWord_1733215 prefixEnd_1733215 889972372582541522041595 := by
  unfold tailWord_1733215
  simp only [CollatzResearch.WordTrace]
  refine ⟨63215544415865539400585099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42143696277243692933723399 63215544415865539400585099)
  ·
    refine ⟨94823316623798309100877649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63215544415865539400585099 94823316623798309100877649)
    ·
      refine ⟨71117487467848731825658237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94823316623798309100877649 71117487467848731825658237)
      ·
        refine ⟨26669057800443274434621839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71117487467848731825658237 26669057800443274434621839)
        ·
          refine ⟨40003586700664911651932759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26669057800443274434621839 40003586700664911651932759)
          ·
            refine ⟨60005380050997367477899139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40003586700664911651932759 60005380050997367477899139)
            ·
              refine ⟨90008070076496051216848709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60005380050997367477899139 90008070076496051216848709)
              ·
                refine ⟨16876513139343009603159133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90008070076496051216848709 16876513139343009603159133)
                ·
                  refine ⟨6328692427253628601184675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16876513139343009603159133 6328692427253628601184675)
                  ·
                    refine ⟨9493038640880442901777013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6328692427253628601184675 9493038640880442901777013)
                    ·
                      refine ⟨889972372582541522041595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9493038640880442901777013 889972372582541522041595)
                      ·
                        rfl

theorem cell23_1733215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1733215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733215 prefixEnd_1733215 := by exact prefixLift 1733215
  have htrace : WordTrace (prefixWord ++ tailWord_1733215) baseStart_1733215 baseEnd_1733215 := by
    simpa [prefixWord, tailWord_1733215, baseEnd_1733215] using wordTrace_append hprefix tailTrace_1733215
  have hstable : (prefixWord ++ tailWord_1733215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733215).length < 2 ^ (prefixWord ++ tailWord_1733215).sum := by decide
  have hdescent : baseEnd_1733215 < baseStart_1733215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733252 : List Nat := [2, 3, 2, 1, 3, 1, 3, 8]
def baseStart_1733252 : Nat := 118140960795 + 1733252 * 2 ^ 59
def prefixEnd_1733252 : Nat := 4983230072969 + 3 ^ 40 * 1733252 * 2
def baseEnd_1733252 : Nat := 32962643383953995454775

theorem tailTrace_1733252 : CollatzResearch.WordTrace tailWord_1733252 prefixEnd_1733252 32962643383953995454775 := by
  unfold tailWord_1733252
  simp only [CollatzResearch.WordTrace]
  refine ⟨31608446958365747359841005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42144595944487663146454673 31608446958365747359841005)
  ·
    refine ⟨11853167609387155259940377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31608446958365747359841005 11853167609387155259940377)
    ·
      refine ⟨8889875707040366444955283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11853167609387155259940377 8889875707040366444955283)
      ·
        refine ⟨13334813560560549667432925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8889875707040366444955283 13334813560560549667432925)
        ·
          refine ⟨5000555085210206125287347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13334813560560549667432925 5000555085210206125287347)
          ·
            refine ⟨7500832627815309187931021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000555085210206125287347 7500832627815309187931021)
            ·
              refine ⟨2812812235430740945474133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7500832627815309187931021 2812812235430740945474133)
              ·
                refine ⟨32962643383953995454775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2812812235430740945474133 32962643383953995454775)
                ·
                  rfl

theorem cell23_1733252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 8].length) (baseStart_1733252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1733252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1733252 prefixEnd_1733252 := by exact prefixLift 1733252
  have htrace : WordTrace (prefixWord ++ tailWord_1733252) baseStart_1733252 baseEnd_1733252 := by
    simpa [prefixWord, tailWord_1733252, baseEnd_1733252] using wordTrace_append hprefix tailTrace_1733252
  have hstable : (prefixWord ++ tailWord_1733252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733252).length < 2 ^ (prefixWord ++ tailWord_1733252).sum := by decide
  have hdescent : baseEnd_1733252 < baseStart_1733252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
