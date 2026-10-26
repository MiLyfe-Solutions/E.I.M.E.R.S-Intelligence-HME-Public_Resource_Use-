import V185TrunkScan23Chunk0605

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3582439 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 2, 4]
def baseStart_3582439 : Nat := 118140960795 + 3582439 * 2 ^ 59
def prefixEnd_3582439 : Nat := 4983230072969 + 3 ^ 40 * 3582439 * 2
def baseEnd_3582439 : Nat := 613171040804138141545723

theorem tailTrace_3582439 : CollatzResearch.WordTrace tailWord_3582439 prefixEnd_3582439 613171040804138141545723 := by
  unfold tailWord_3582439
  simp only [CollatzResearch.WordTrace]
  refine ⟨130662284668442809715886371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87108189778961873143924247 130662284668442809715886371)
  ·
    refine ⟨195993427002664214573829557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130662284668442809715886371 195993427002664214573829557)
    ·
      refine ⟨18374383781499770116296521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195993427002664214573829557 18374383781499770116296521)
      ·
        refine ⟨13780787836124827587222391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18374383781499770116296521 13780787836124827587222391)
        ·
          refine ⟨20671181754187241380833587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13780787836124827587222391 20671181754187241380833587)
          ·
            refine ⟨31006772631280862071250381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20671181754187241380833587 31006772631280862071250381)
            ·
              refine ⟨11627539736730323276718893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31006772631280862071250381 11627539736730323276718893)
              ·
                refine ⟨4360327401273871228769585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11627539736730323276718893 4360327401273871228769585)
                ·
                  refine ⟨3270245550955403421577189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360327401273871228769585 3270245550955403421577189)
                  ·
                    refine ⟨613171040804138141545723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270245550955403421577189 613171040804138141545723)
                    ·
                      rfl

theorem cell23_3582439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_3582439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582439 prefixEnd_3582439 := by exact prefixLift 3582439
  have htrace : WordTrace (prefixWord ++ tailWord_3582439) baseStart_3582439 baseEnd_3582439 := by
    simpa [prefixWord, tailWord_3582439, baseEnd_3582439] using wordTrace_append hprefix tailTrace_3582439
  have hstable : (prefixWord ++ tailWord_3582439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582439).length < 2 ^ (prefixWord ++ tailWord_3582439).sum := by decide
  have hdescent : baseEnd_3582439 < baseStart_3582439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582442 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_3582442 : Nat := 118140960795 + 3582442 * 2 ^ 59
def prefixEnd_3582442 : Nat := 4983230072969 + 3 ^ 40 * 3582442 * 2
def baseEnd_3582442 : Nat := 1839514662854377912899655

theorem tailTrace_3582442 : CollatzResearch.WordTrace tailWord_3582442 prefixEnd_3582442 1839514662854377912899655 := by
  unfold tailWord_3582442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32665598521857985307061395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87108262724954627485497053 32665598521857985307061395)
  ·
    refine ⟨48998397782786977960592093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32665598521857985307061395 48998397782786977960592093)
    ·
      refine ⟨18374399168545116735222035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48998397782786977960592093 18374399168545116735222035)
      ·
        refine ⟨27561598752817675102833053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18374399168545116735222035 27561598752817675102833053)
        ·
          refine ⟨10335599532306628163562395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27561598752817675102833053 10335599532306628163562395)
          ·
            refine ⟨15503399298459942245343593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10335599532306628163562395 15503399298459942245343593)
            ·
              refine ⟨11627549473844956684007695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15503399298459942245343593 11627549473844956684007695)
              ·
                refine ⟨17441324210767435026011543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627549473844956684007695 17441324210767435026011543)
                ·
                  refine ⟨26161986316151152539017315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17441324210767435026011543 26161986316151152539017315)
                  ·
                    refine ⟨39242979474226728808525973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26161986316151152539017315 39242979474226728808525973)
                    ·
                      refine ⟨1839514662854377912899655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39242979474226728808525973 1839514662854377912899655)
                      ·
                        rfl

theorem cell23_3582442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_3582442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582442 prefixEnd_3582442 := by exact prefixLift 3582442
  have htrace : WordTrace (prefixWord ++ tailWord_3582442) baseStart_3582442 baseEnd_3582442 := by
    simpa [prefixWord, tailWord_3582442, baseEnd_3582442] using wordTrace_append hprefix tailTrace_3582442
  have hstable : (prefixWord ++ tailWord_3582442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582442).length < 2 ^ (prefixWord ++ tailWord_3582442).sum := by decide
  have hdescent : baseEnd_3582442 < baseStart_3582442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582446 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_3582446 : Nat := 118140960795 + 3582446 * 2 ^ 59
def prefixEnd_3582446 : Nat := 4983230072969 + 3 ^ 40 * 3582446 * 2
def baseEnd_3582446 : Nat := 1839516716776995897249637

theorem tailTrace_3582446 : CollatzResearch.WordTrace tailWord_3582446 prefixEnd_3582446 1839516716776995897249637 := by
  unfold tailWord_3582446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16332817497427181238923899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87108359986278299940927461 16332817497427181238923899)
  ·
    refine ⟨24499226246140771858385849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16332817497427181238923899 24499226246140771858385849)
    ·
      refine ⟨18374419684605578893789387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24499226246140771858385849 18374419684605578893789387)
      ·
        refine ⟨27561629526908368340684081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18374419684605578893789387 27561629526908368340684081)
        ·
          refine ⟨20671222145181276255513061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27561629526908368340684081 20671222145181276255513061)
          ·
            refine ⟨3875854152221489297908699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20671222145181276255513061 3875854152221489297908699)
            ·
              refine ⟨5813781228332233946863049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875854152221489297908699 5813781228332233946863049)
              ·
                refine ⟨4360335921249175460147287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5813781228332233946863049 4360335921249175460147287)
                ·
                  refine ⟨6540503881873763190220931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360335921249175460147287 6540503881873763190220931)
                  ·
                    refine ⟨9810755822810644785331397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6540503881873763190220931 9810755822810644785331397)
                    ·
                      refine ⟨1839516716776995897249637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9810755822810644785331397 1839516716776995897249637)
                      ·
                        rfl

theorem cell23_3582446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_3582446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582446 prefixEnd_3582446 := by exact prefixLift 3582446
  have htrace : WordTrace (prefixWord ++ tailWord_3582446) baseStart_3582446 baseEnd_3582446 := by
    simpa [prefixWord, tailWord_3582446, baseEnd_3582446] using wordTrace_append hprefix tailTrace_3582446
  have hstable : (prefixWord ++ tailWord_3582446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582446).length < 2 ^ (prefixWord ++ tailWord_3582446).sum := by decide
  have hdescent : baseEnd_3582446 < baseStart_3582446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582479 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 3]
def baseStart_3582479 : Nat := 118140960795 + 3582479 * 2 ^ 59
def prefixEnd_3582479 : Nat := 4983230072969 + 3 ^ 40 * 3582479 * 2
def baseEnd_3582479 : Nat := 1839533661638594268136985

theorem tailTrace_3582479 : CollatzResearch.WordTrace tailWord_3582479 prefixEnd_3582479 1839533661638594268136985 := by
  unfold tailWord_3582479
  simp only [CollatzResearch.WordTrace]
  refine ⟨130663743588297896547342491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87109162392198597698228327 130663743588297896547342491)
  ·
    refine ⟨195995615382446844821013737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130663743588297896547342491 195995615382446844821013737)
    ·
      refine ⟨146996711536835133615760303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195995615382446844821013737 146996711536835133615760303)
      ·
        refine ⟨220495067305252700423640455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146996711536835133615760303 220495067305252700423640455)
        ·
          refine ⟨330742600957879050635460683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220495067305252700423640455 330742600957879050635460683)
          ·
            refine ⟨496113901436818575953191025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330742600957879050635460683 496113901436818575953191025)
            ·
              refine ⟨372085426077613931964893269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496113901436818575953191025 372085426077613931964893269)
              ·
                refine ⟨4360376086847038265213593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 372085426077613931964893269 4360376086847038265213593)
                ·
                  refine ⟨3270282065135278698910195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360376086847038265213593 3270282065135278698910195)
                  ·
                    refine ⟨4905423097702918048365293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3270282065135278698910195 4905423097702918048365293)
                    ·
                      refine ⟨1839533661638594268136985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4905423097702918048365293 1839533661638594268136985)
                      ·
                        rfl

theorem cell23_3582479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 3].length) (baseStart_3582479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582479 prefixEnd_3582479 := by exact prefixLift 3582479
  have htrace : WordTrace (prefixWord ++ tailWord_3582479) baseStart_3582479 baseEnd_3582479 := by
    simpa [prefixWord, tailWord_3582479, baseEnd_3582479] using wordTrace_append hprefix tailTrace_3582479
  have hstable : (prefixWord ++ tailWord_3582479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582479).length < 2 ^ (prefixWord ++ tailWord_3582479).sum := by decide
  have hdescent : baseEnd_3582479 < baseStart_3582479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582496 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3582496 : Nat := 118140960795 + 3582496 * 2 ^ 59
def prefixEnd_3582496 : Nat := 4983230072969 + 3 ^ 40 * 3582496 * 2
def baseEnd_3582496 : Nat := 1839542390809720701624407

theorem tailTrace_3582496 : CollatzResearch.WordTrace tailWord_3582496 prefixEnd_3582496 1839542390809720701624407 := by
  unfold tailWord_3582496
  simp only [CollatzResearch.WordTrace]
  refine ⟨65332181814618154225355671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87109575752824205633807561 65332181814618154225355671)
  ·
    refine ⟨97998272721927231338033507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65332181814618154225355671 97998272721927231338033507)
    ·
      refine ⟨146997409082890847007050261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97998272721927231338033507 146997409082890847007050261)
      ·
        refine ⟨6890503550760508453455481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146997409082890847007050261 6890503550760508453455481)
        ·
          refine ⟨5167877663070381340091611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6890503550760508453455481 5167877663070381340091611)
          ·
            refine ⟨7751816494605572010137417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167877663070381340091611 7751816494605572010137417)
            ·
              refine ⟨5813862370954179007603063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7751816494605572010137417 5813862370954179007603063)
              ·
                refine ⟨8720793556431268511404595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813862370954179007603063 8720793556431268511404595)
                ·
                  refine ⟨13081190334646902767106893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8720793556431268511404595 13081190334646902767106893)
                  ·
                    refine ⟨4905446375492588537665085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13081190334646902767106893 4905446375492588537665085)
                    ·
                      refine ⟨1839542390809720701624407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4905446375492588537665085 1839542390809720701624407)
                      ·
                        rfl

theorem cell23_3582496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3582496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582496 prefixEnd_3582496 := by exact prefixLift 3582496
  have htrace : WordTrace (prefixWord ++ tailWord_3582496) baseStart_3582496 baseEnd_3582496 := by
    simpa [prefixWord, tailWord_3582496, baseEnd_3582496] using wordTrace_append hprefix tailTrace_3582496
  have hstable : (prefixWord ++ tailWord_3582496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582496).length < 2 ^ (prefixWord ++ tailWord_3582496).sum := by decide
  have hdescent : baseEnd_3582496 < baseStart_3582496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582506 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_3582506 : Nat := 118140960795 + 3582506 * 2 ^ 59
def prefixEnd_3582506 : Nat := 4983230072969 + 3 ^ 40 * 3582506 * 2
def baseEnd_3582506 : Nat := 1839547525616265662499361

theorem tailTrace_3582506 : CollatzResearch.WordTrace tailWord_3582506 prefixEnd_3582506 1839547525616265662499361 := by
  unfold tailWord_3582506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666182089800020039643843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87109818906133386772383581 32666182089800020039643843)
  ·
    refine ⟨48999273134700030059465765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32666182089800020039643843 48999273134700030059465765)
    ·
      refine ⟨9187363712756255636149831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48999273134700030059465765 9187363712756255636149831)
      ·
        refine ⟨13781045569134383454224747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9187363712756255636149831 13781045569134383454224747)
        ·
          refine ⟨20671568353701575181337121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13781045569134383454224747 20671568353701575181337121)
          ·
            refine ⟨15503676265276181386002841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20671568353701575181337121 15503676265276181386002841)
            ·
              refine ⟨11627757198957136039502131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15503676265276181386002841 11627757198957136039502131)
              ·
                refine ⟨17441635798435704059253197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627757198957136039502131 17441635798435704059253197)
                ·
                  refine ⟨6540613424413389022219949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17441635798435704059253197 6540613424413389022219949)
                  ·
                    refine ⟨2452730034155020883332481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6540613424413389022219949 2452730034155020883332481)
                    ·
                      refine ⟨1839547525616265662499361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452730034155020883332481 1839547525616265662499361)
                      ·
                        rfl

theorem cell23_3582506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_3582506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582506 prefixEnd_3582506 := by exact prefixLift 3582506
  have htrace : WordTrace (prefixWord ++ tailWord_3582506) baseStart_3582506 baseEnd_3582506 := by
    simpa [prefixWord, tailWord_3582506, baseEnd_3582506] using wordTrace_append hprefix tailTrace_3582506
  have hstable : (prefixWord ++ tailWord_3582506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582506).length < 2 ^ (prefixWord ++ tailWord_3582506).sum := by decide
  have hdescent : baseEnd_3582506 < baseStart_3582506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582519 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 1, 4, 2]
def baseStart_3582519 : Nat := 118140960795 + 3582519 * 2 ^ 59
def prefixEnd_3582519 : Nat := 4983230072969 + 3 ^ 40 * 3582519 * 2
def baseEnd_3582519 : Nat := 1839554200864774111636801

theorem tailTrace_3582519 : CollatzResearch.WordTrace tailWord_3582519 prefixEnd_3582519 1839554200864774111636801 := by
  unfold tailWord_3582519
  simp only [CollatzResearch.WordTrace]
  refine ⟨130665202508152983378798611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87110135005435322252532407 130665202508152983378798611)
  ·
    refine ⟨195997803762229475068197917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130665202508152983378798611 195997803762229475068197917)
    ·
      refine ⟨73499176410836053150574219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195997803762229475068197917 73499176410836053150574219)
      ·
        refine ⟨110248764616254079725861329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73499176410836053150574219 110248764616254079725861329)
        ·
          refine ⟨82686573462190559794395997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110248764616254079725861329 82686573462190559794395997)
          ·
            refine ⟨31007465048321459922898499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82686573462190559794395997 31007465048321459922898499)
            ·
              refine ⟨46511197572482189884347749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31007465048321459922898499 46511197572482189884347749)
              ·
                refine ⟨8720849544840410603315203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46511197572482189884347749 8720849544840410603315203)
                ·
                  refine ⟨13081274317260615904972805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8720849544840410603315203 13081274317260615904972805)
                  ·
                    refine ⟨2452738934486365482182401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13081274317260615904972805 2452738934486365482182401)
                    ·
                      refine ⟨1839554200864774111636801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452738934486365482182401 1839554200864774111636801)
                      ·
                        rfl

theorem cell23_3582519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_3582519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582519 prefixEnd_3582519 := by exact prefixLift 3582519
  have htrace : WordTrace (prefixWord ++ tailWord_3582519) baseStart_3582519 baseEnd_3582519 := by
    simpa [prefixWord, tailWord_3582519, baseEnd_3582519] using wordTrace_append hprefix tailTrace_3582519
  have hstable : (prefixWord ++ tailWord_3582519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582519).length < 2 ^ (prefixWord ++ tailWord_3582519).sum := by decide
  have hdescent : baseEnd_3582519 < baseStart_3582519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582542 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_3582542 : Nat := 118140960795 + 3582542 * 2 ^ 59
def prefixEnd_3582542 : Nat := 4983230072969 + 3 ^ 40 * 3582542 * 2
def baseEnd_3582542 : Nat := 204396223435536391294355

theorem tailTrace_3582542 : CollatzResearch.WordTrace tailWord_3582542 prefixEnd_3582542 204396223435536391294355 := by
  unfold tailWord_3582542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16333255173383707288360735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87110694258046438871257253 16333255173383707288360735)
  ·
    refine ⟨24499882760075560932541103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16333255173383707288360735 24499882760075560932541103)
    ·
      refine ⟨36749824140113341398811655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24499882760075560932541103 36749824140113341398811655)
      ·
        refine ⟨55124736210170012098217483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36749824140113341398811655 55124736210170012098217483)
        ·
          refine ⟨82687104315255018147326225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55124736210170012098217483 82687104315255018147326225)
          ·
            refine ⟨62015328236441263610494669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82687104315255018147326225 62015328236441263610494669)
            ·
              refine ⟨23255748088665473853935501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62015328236441263610494669 23255748088665473853935501)
              ·
                refine ⟨8720905533249552695225813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23255748088665473853935501 8720905533249552695225813)
                ·
                  refine ⟨204396223435536391294355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8720905533249552695225813 204396223435536391294355)
                  ·
                    rfl

theorem cell23_3582542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_3582542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582542 prefixEnd_3582542 := by exact prefixLift 3582542
  have htrace : WordTrace (prefixWord ++ tailWord_3582542) baseStart_3582542 baseEnd_3582542 := by
    simpa [prefixWord, tailWord_3582542, baseEnd_3582542] using wordTrace_append hprefix tailTrace_3582542
  have hstable : (prefixWord ++ tailWord_3582542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582542).length < 2 ^ (prefixWord ++ tailWord_3582542).sum := by decide
  have hdescent : baseEnd_3582542 < baseStart_3582542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582572 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_3582572 : Nat := 118140960795 + 3582572 * 2 ^ 59
def prefixEnd_3582572 : Nat := 4983230072969 + 3 ^ 40 * 3582572 * 2
def baseEnd_3582572 : Nat := 613193805113154134758019

theorem tailTrace_3582572 : CollatzResearch.WordTrace tailWord_3582572 prefixEnd_3582572 613193805113154134758019 := by
  unfold tailWord_3582572
  simp only [CollatzResearch.WordTrace]
  refine ⟨65333567788480486715238985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87111423717973982286985313 65333567788480486715238985)
  ·
    refine ⟨49000175841360365036429239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65333567788480486715238985 49000175841360365036429239)
    ·
      refine ⟨73500263762040547554643859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49000175841360365036429239 73500263762040547554643859)
      ·
        refine ⟨110250395643060821331965789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73500263762040547554643859 110250395643060821331965789)
        ·
          refine ⟨41343898366147807999487171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110250395643060821331965789 41343898366147807999487171)
          ·
            refine ⟨62015847549221711999230757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41343898366147807999487171 62015847549221711999230757)
            ·
              refine ⟨11627971415479070999855767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62015847549221711999230757 11627971415479070999855767)
              ·
                refine ⟨17441957123218606499783651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627971415479070999855767 17441957123218606499783651)
                ·
                  refine ⟨26162935684827909749675477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17441957123218606499783651 26162935684827909749675477)
                  ·
                    refine ⟨613193805113154134758019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26162935684827909749675477 613193805113154134758019)
                    ·
                      rfl

theorem cell23_3582572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_3582572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582572 prefixEnd_3582572 := by exact prefixLift 3582572
  have htrace : WordTrace (prefixWord ++ tailWord_3582572) baseStart_3582572 baseEnd_3582572 := by
    simpa [prefixWord, tailWord_3582572, baseEnd_3582572] using wordTrace_append hprefix tailTrace_3582572
  have hstable : (prefixWord ++ tailWord_3582572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582572).length < 2 ^ (prefixWord ++ tailWord_3582572).sum := by decide
  have hdescent : baseEnd_3582572 < baseStart_3582572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582609 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 6, 4, 2]
def baseStart_3582609 : Nat := 118140960795 + 3582609 * 2 ^ 59
def prefixEnd_3582609 : Nat := 4983230072969 + 3 ^ 40 * 3582609 * 2
def baseEnd_3582609 : Nat := 1839600414123678759511387

theorem tailTrace_3582609 : CollatzResearch.WordTrace tailWord_3582609 prefixEnd_3582609 1839600414123678759511387 := by
  unfold tailWord_3582609
  simp only [CollatzResearch.WordTrace]
  refine ⟨130668485077826928749574881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87112323385217952499716587 130668485077826928749574881)
  ·
    refine ⟨98001363808370196562181161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130668485077826928749574881 98001363808370196562181161)
    ·
      refine ⟨73501022856277647421635871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98001363808370196562181161 73501022856277647421635871)
      ·
        refine ⟨110251534284416471132453807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73501022856277647421635871 110251534284416471132453807)
        ·
          refine ⟨165377301426624706698680711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110251534284416471132453807 165377301426624706698680711)
          ·
            refine ⟨248065952139937060048021067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165377301426624706698680711 248065952139937060048021067)
            ·
              refine ⟨372098928209905590072031601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248065952139937060048021067 372098928209905590072031601)
              ·
                refine ⟨279074196157429192554023701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372098928209905590072031601 279074196157429192554023701)
                ·
                  refine ⟨13081602944879493400969861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 279074196157429192554023701 13081602944879493400969861)
                  ·
                    refine ⟨2452800552164905012681849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13081602944879493400969861 2452800552164905012681849)
                    ·
                      refine ⟨1839600414123678759511387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452800552164905012681849 1839600414123678759511387)
                      ·
                        rfl

theorem cell23_3582609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_3582609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582609 prefixEnd_3582609 := by exact prefixLift 3582609
  have htrace : WordTrace (prefixWord ++ tailWord_3582609) baseStart_3582609 baseEnd_3582609 := by
    simpa [prefixWord, tailWord_3582609, baseEnd_3582609] using wordTrace_append hprefix tailTrace_3582609
  have hstable : (prefixWord ++ tailWord_3582609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582609).length < 2 ^ (prefixWord ++ tailWord_3582609).sum := by decide
  have hdescent : baseEnd_3582609 < baseStart_3582609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582653 : List Nat := [1, 4, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_3582653 : Nat := 118140960795 + 3582653 * 2 ^ 59
def prefixEnd_3582653 : Nat := 4983230072969 + 3 ^ 40 * 3582653 * 2
def baseEnd_3582653 : Nat := 613207669090825529120395

theorem tailTrace_3582653 : CollatzResearch.WordTrace tailWord_3582653 prefixEnd_3582653 613207669090825529120395 := by
  unfold tailWord_3582653
  simp only [CollatzResearch.WordTrace]
  refine ⟨130670089889667524264176613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87113393259778349509451075 130670089889667524264176613)
  ·
    refine ⟨24500641854312660799533115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130670089889667524264176613 24500641854312660799533115)
    ·
      refine ⟨36750962781468991199299673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24500641854312660799533115 36750962781468991199299673)
      ·
        refine ⟨27563222086101743399474755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36750962781468991199299673 27563222086101743399474755)
        ·
          refine ⟨41344833129152615099212133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27563222086101743399474755 41344833129152615099212133)
          ·
            refine ⟨7752156211716115331102275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41344833129152615099212133 7752156211716115331102275)
            ·
              refine ⟨11628234317574172996653413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7752156211716115331102275 11628234317574172996653413)
              ·
                refine ⟨2180293934545157436872515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11628234317574172996653413 2180293934545157436872515)
                ·
                  refine ⟨3270440901817736155308773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180293934545157436872515 3270440901817736155308773)
                  ·
                    refine ⟨613207669090825529120395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270440901817736155308773 613207669090825529120395)
                    ·
                      rfl

theorem cell23_3582653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_3582653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582653 prefixEnd_3582653 := by exact prefixLift 3582653
  have htrace : WordTrace (prefixWord ++ tailWord_3582653) baseStart_3582653 baseEnd_3582653 := by
    simpa [prefixWord, tailWord_3582653, baseEnd_3582653] using wordTrace_append hprefix tailTrace_3582653
  have hstable : (prefixWord ++ tailWord_3582653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582653).length < 2 ^ (prefixWord ++ tailWord_3582653).sum := by decide
  have hdescent : baseEnd_3582653 < baseStart_3582653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582672 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_3582672 : Nat := 118140960795 + 3582672 * 2 ^ 59
def prefixEnd_3582672 : Nat := 4983230072969 + 3 ^ 40 * 3582672 * 2
def baseEnd_3582672 : Nat := 1839632763404912013023597

theorem tailTrace_3582672 : CollatzResearch.WordTrace tailWord_3582672 prefixEnd_3582672 1839632763404912013023597 := by
  unfold tailWord_3582672
  simp only [CollatzResearch.WordTrace]
  refine ⟨65335391438299345254559135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87113855251065793672745513 65335391438299345254559135)
  ·
    refine ⟨98003087157449017881838703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65335391438299345254559135 98003087157449017881838703)
    ·
      refine ⟨147004630736173526822758055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98003087157449017881838703 147004630736173526822758055)
      ·
        refine ⟨220506946104260290234137083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147004630736173526822758055 220506946104260290234137083)
        ·
          refine ⟨330760419156390435351205625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220506946104260290234137083 330760419156390435351205625)
          ·
            refine ⟨248070314367292826513404219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330760419156390435351205625 248070314367292826513404219)
            ·
              refine ⟨372105471550939239770106329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248070314367292826513404219 372105471550939239770106329)
              ·
                refine ⟨279079103663204429827579747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372105471550939239770106329 279079103663204429827579747)
                ·
                  refine ⟨418618655494806644741369621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279079103663204429827579747 418618655494806644741369621)
                  ·
                    refine ⟨19622749476319061472251701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 418618655494806644741369621 19622749476319061472251701)
                    ·
                      refine ⟨1839632763404912013023597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19622749476319061472251701 1839632763404912013023597)
                      ·
                        rfl

theorem cell23_3582672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_3582672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582672 prefixEnd_3582672 := by exact prefixLift 3582672
  have htrace : WordTrace (prefixWord ++ tailWord_3582672) baseStart_3582672 baseEnd_3582672 := by
    simpa [prefixWord, tailWord_3582672, baseEnd_3582672] using wordTrace_append hprefix tailTrace_3582672
  have hstable : (prefixWord ++ tailWord_3582672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582672).length < 2 ^ (prefixWord ++ tailWord_3582672).sum := by decide
  have hdescent : baseEnd_3582672 < baseStart_3582672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582679 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 3, 5]
def baseStart_3582679 : Nat := 118140960795 + 3582679 * 2 ^ 59
def prefixEnd_3582679 : Nat := 4983230072969 + 3 ^ 40 * 3582679 * 2
def baseEnd_3582679 : Nat := 613212119256497828545355

theorem tailTrace_3582679 : CollatzResearch.WordTrace tailWord_3582679 prefixEnd_3582679 613212119256497828545355 := by
  unfold tailWord_3582679
  simp only [CollatzResearch.WordTrace]
  refine ⟨130671038187573330704623091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87114025458382220469748727 130671038187573330704623091)
  ·
    refine ⟨196006557281359996056934637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130671038187573330704623091 196006557281359996056934637)
    ·
      refine ⟨73502458980509998521350489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196006557281359996056934637 73502458980509998521350489)
      ·
        refine ⟨55126844235382498891012867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73502458980509998521350489 55126844235382498891012867)
        ·
          refine ⟨82690266353073748336519301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55126844235382498891012867 82690266353073748336519301)
          ·
            refine ⟨15504424941201327813097369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82690266353073748336519301 15504424941201327813097369)
            ·
              refine ⟨11628318705900995859823027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15504424941201327813097369 11628318705900995859823027)
              ·
                refine ⟨17442478058851493789734541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11628318705900995859823027 17442478058851493789734541)
                ·
                  refine ⟨6540929272069310171150453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17442478058851493789734541 6540929272069310171150453)
                  ·
                    refine ⟨613212119256497828545355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6540929272069310171150453 613212119256497828545355)
                    ·
                      rfl

theorem cell23_3582679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_3582679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582679 prefixEnd_3582679 := by exact prefixLift 3582679
  have htrace : WordTrace (prefixWord ++ tailWord_3582679) baseStart_3582679 baseEnd_3582679 := by
    simpa [prefixWord, tailWord_3582679, baseEnd_3582679] using wordTrace_append hprefix tailTrace_3582679
  have hstable : (prefixWord ++ tailWord_3582679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582679).length < 2 ^ (prefixWord ++ tailWord_3582679).sum := by decide
  have hdescent : baseEnd_3582679 < baseStart_3582679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582710 : List Nat := [5, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_3582710 : Nat := 118140960795 + 3582710 * 2 ^ 59
def prefixEnd_3582710 : Nat := 4983230072969 + 3 ^ 40 * 3582710 * 2
def baseEnd_3582710 : Nat := 1839652275669782864348423

theorem tailTrace_3582710 : CollatzResearch.WordTrace tailWord_3582710 prefixEnd_3582710 1839652275669782864348423 := by
  unfold tailWord_3582710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167010553153813937437599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87114779233640681999334389 8167010553153813937437599)
  ·
    refine ⟨12250515829730720906156399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8167010553153813937437599 12250515829730720906156399)
    ·
      refine ⟨18375773744596081359234599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12250515829730720906156399 18375773744596081359234599)
      ·
        refine ⟨27563660616894122038851899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18375773744596081359234599 27563660616894122038851899)
        ·
          refine ⟨41345490925341183058277849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27563660616894122038851899 41345490925341183058277849)
          ·
            refine ⟨31009118194005887293708387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41345490925341183058277849 31009118194005887293708387)
            ·
              refine ⟨46513677291008830940562581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31009118194005887293708387 46513677291008830940562581)
              ·
                refine ⟨2180328623016038950338871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46513677291008830940562581 2180328623016038950338871)
                ·
                  refine ⟨3270492934524058425508307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180328623016038950338871 3270492934524058425508307)
                  ·
                    refine ⟨4905739401786087638262461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3270492934524058425508307 4905739401786087638262461)
                    ·
                      refine ⟨1839652275669782864348423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4905739401786087638262461 1839652275669782864348423)
                      ·
                        rfl

theorem cell23_3582710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_3582710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582710 prefixEnd_3582710 := by exact prefixLift 3582710
  have htrace : WordTrace (prefixWord ++ tailWord_3582710) baseStart_3582710 baseEnd_3582710 := by
    simpa [prefixWord, tailWord_3582710, baseEnd_3582710] using wordTrace_append hprefix tailTrace_3582710
  have hstable : (prefixWord ++ tailWord_3582710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582710).length < 2 ^ (prefixWord ++ tailWord_3582710).sum := by decide
  have hdescent : baseEnd_3582710 < baseStart_3582710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582756 : List Nat := [2, 3, 1, 3, 3, 2, 9]
def baseStart_3582756 : Nat := 118140960795 + 3582756 * 2 ^ 59
def prefixEnd_3582756 : Nat := 4983230072969 + 3 ^ 40 * 3582756 * 2
def baseEnd_3582756 : Nat := 22712048096048020794731

theorem tailTrace_3582756 : CollatzResearch.WordTrace tailWord_3582756 prefixEnd_3582756 22712048096048020794731 := by
  unfold tailWord_3582756
  simp only [CollatzResearch.WordTrace]
  refine ⟨65336923304147186427588061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87115897738862915236784081 65336923304147186427588061)
  ·
    refine ⟨24501346239055194910345523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65336923304147186427588061 24501346239055194910345523)
    ·
      refine ⟨36752019358582792365518285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24501346239055194910345523 36752019358582792365518285)
      ·
        refine ⟨13782007259468547137069357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36752019358582792365518285 13782007259468547137069357)
        ·
          refine ⟨5168252722300705176401009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13782007259468547137069357 5168252722300705176401009)
          ·
            refine ⟨3876189541725528882300757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5168252722300705176401009 3876189541725528882300757)
            ·
              refine ⟨22712048096048020794731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3876189541725528882300757 22712048096048020794731)
              ·
                rfl

theorem cell23_3582756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 9].length) (baseStart_3582756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582756 prefixEnd_3582756 := by exact prefixLift 3582756
  have htrace : WordTrace (prefixWord ++ tailWord_3582756) baseStart_3582756 baseEnd_3582756 := by
    simpa [prefixWord, tailWord_3582756, baseEnd_3582756] using wordTrace_append hprefix tailTrace_3582756
  have hstable : (prefixWord ++ tailWord_3582756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582756).length < 2 ^ (prefixWord ++ tailWord_3582756).sum := by decide
  have hdescent : baseEnd_3582756 < baseStart_3582756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582769 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 2, 7]
def baseStart_3582769 : Nat := 118140960795 + 3582769 * 2 ^ 59
def prefixEnd_3582769 : Nat := 4983230072969 + 3 ^ 40 * 3582769 * 2
def baseEnd_3582769 : Nat := 613227523676132711170217

theorem tailTrace_3582769 : CollatzResearch.WordTrace tailWord_3582769 prefixEnd_3582769 613227523676132711170217 := by
  unfold tailWord_3582769
  simp only [CollatzResearch.WordTrace]
  refine ⟨130674320757247276075399361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87116213838164850716932907 130674320757247276075399361)
  ·
    refine ⟨98005740567935457056549521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130674320757247276075399361 98005740567935457056549521)
    ·
      refine ⟨73504305425951592792412141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98005740567935457056549521 73504305425951592792412141)
      ·
        refine ⟨27564114534731847297154553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73504305425951592792412141 27564114534731847297154553)
        ·
          refine ⟨20673085901048885472865915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27564114534731847297154553 20673085901048885472865915)
          ·
            refine ⟨31009628851573328209298873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20673085901048885472865915 31009628851573328209298873)
            ·
              refine ⟨23257221638679996156974155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31009628851573328209298873 23257221638679996156974155)
              ·
                refine ⟨34885832458019994235461233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23257221638679996156974155 34885832458019994235461233)
                ·
                  refine ⟨26164374343514995676595925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34885832458019994235461233 26164374343514995676595925)
                  ·
                    refine ⟨613227523676132711170217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26164374343514995676595925 613227523676132711170217)
                    ·
                      rfl

theorem cell23_3582769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_3582769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582769 prefixEnd_3582769 := by exact prefixLift 3582769
  have htrace : WordTrace (prefixWord ++ tailWord_3582769) baseStart_3582769 baseEnd_3582769 := by
    simpa [prefixWord, tailWord_3582769, baseEnd_3582769] using wordTrace_append hprefix tailTrace_3582769
  have hstable : (prefixWord ++ tailWord_3582769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582769).length < 2 ^ (prefixWord ++ tailWord_3582769).sum := by decide
  have hdescent : baseEnd_3582769 < baseStart_3582769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582789 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3582789 : Nat := 118140960795 + 3582789 * 2 ^ 59
def prefixEnd_3582789 : Nat := 4983230072969 + 3 ^ 40 * 3582789 * 2
def baseEnd_3582789 : Nat := 1839692840641488055260559

theorem tailTrace_3582789 : CollatzResearch.WordTrace tailWord_3582789 prefixEnd_3582789 1839692840641488055260559 := by
  unfold tailWord_3582789
  simp only [CollatzResearch.WordTrace]
  refine ⟨130675050217174819491127421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87116700144783212994084947 130675050217174819491127421)
  ·
    refine ⟨49003143831440557309172783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130675050217174819491127421 49003143831440557309172783)
    ·
      refine ⟨73504715747160835963759175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49003143831440557309172783 73504715747160835963759175)
      ·
        refine ⟨110257073620741253945638763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73504715747160835963759175 110257073620741253945638763)
        ·
          refine ⟨165385610431111880918458145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110257073620741253945638763 165385610431111880918458145)
          ·
            refine ⟨124039207823333910688843609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165385610431111880918458145 124039207823333910688843609)
            ·
              refine ⟨93029405867500433016632707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124039207823333910688843609 93029405867500433016632707)
              ·
                refine ⟨139544108801250649524949061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93029405867500433016632707 139544108801250649524949061)
                ·
                  refine ⟨26164520400234496785927949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139544108801250649524949061 26164520400234496785927949)
                  ·
                    refine ⟨9811695150087936294722981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26164520400234496785927949 9811695150087936294722981)
                    ·
                      refine ⟨1839692840641488055260559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9811695150087936294722981 1839692840641488055260559)
                      ·
                        rfl

theorem cell23_3582789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3582789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582789 prefixEnd_3582789 := by exact prefixLift 3582789
  have htrace : WordTrace (prefixWord ++ tailWord_3582789) baseStart_3582789 baseEnd_3582789 := by
    simpa [prefixWord, tailWord_3582789, baseEnd_3582789] using wordTrace_append hprefix tailTrace_3582789
  have hstable : (prefixWord ++ tailWord_3582789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582789).length < 2 ^ (prefixWord ++ tailWord_3582789).sum := by decide
  have hdescent : baseEnd_3582789 < baseStart_3582789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582793 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 3, 3, 2]
def baseStart_3582793 : Nat := 118140960795 + 3582793 * 2 ^ 59
def prefixEnd_3582793 : Nat := 4983230072969 + 3 ^ 40 * 3582793 * 2
def baseEnd_3582793 : Nat := 1839694894564106039610541

theorem tailTrace_3582793 : CollatzResearch.WordTrace tailWord_3582793 prefixEnd_3582793 1839694894564106039610541 := by
  unfold tailWord_3582793
  simp only [CollatzResearch.WordTrace]
  refine ⟨130675196109160328174273033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87116797406106885449515355 130675196109160328174273033)
  ·
    refine ⟨98006397081870246130704775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130675196109160328174273033 98006397081870246130704775)
    ·
      refine ⟨147009595622805369196057163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98006397081870246130704775 147009595622805369196057163)
      ·
        refine ⟨220514393434208053794085745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147009595622805369196057163 220514393434208053794085745)
        ·
          refine ⟨165385795075656040345564309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220514393434208053794085745 165385795075656040345564309)
          ·
            refine ⟨7752459144171376891198327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165385795075656040345564309 7752459144171376891198327)
            ·
              refine ⟨11628688716257065336797491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7752459144171376891198327 11628688716257065336797491)
              ·
                refine ⟨17443033074385598005196237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11628688716257065336797491 17443033074385598005196237)
                ·
                  refine ⟨6541137402894599251948589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17443033074385598005196237 6541137402894599251948589)
                  ·
                    refine ⟨2452926526085474719480721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6541137402894599251948589 2452926526085474719480721)
                    ·
                      refine ⟨1839694894564106039610541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452926526085474719480721 1839694894564106039610541)
                      ·
                        rfl

theorem cell23_3582793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 3, 2].length) (baseStart_3582793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582793 prefixEnd_3582793 := by exact prefixLift 3582793
  have htrace : WordTrace (prefixWord ++ tailWord_3582793) baseStart_3582793 baseEnd_3582793 := by
    simpa [prefixWord, tailWord_3582793, baseEnd_3582793] using wordTrace_append hprefix tailTrace_3582793
  have hstable : (prefixWord ++ tailWord_3582793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582793).length < 2 ^ (prefixWord ++ tailWord_3582793).sum := by decide
  have hdescent : baseEnd_3582793 < baseStart_3582793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582818 : List Nat := [3, 3, 2, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_3582818 : Nat := 118140960795 + 3582818 * 2 ^ 59
def prefixEnd_3582818 : Nat := 4983230072969 + 3 ^ 40 * 3582818 * 2
def baseEnd_3582818 : Nat := 1839707731580468441797927

theorem tailTrace_3582818 : CollatzResearch.WordTrace tailWord_3582818 prefixEnd_3582818 1839707731580468441797927 := by
  unfold tailWord_3582818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32669026983517439360983277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87117405289379838295955405 32669026983517439360983277)
  ·
    refine ⟨12250885118819039760368729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32669026983517439360983277 12250885118819039760368729)
    ·
      refine ⟨9188163839114279820276547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12250885118819039760368729 9188163839114279820276547)
      ·
        refine ⟨13782245758671419730414821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9188163839114279820276547 13782245758671419730414821)
        ·
          refine ⟨2584171079750891199452779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13782245758671419730414821 2584171079750891199452779)
          ·
            refine ⟨3876256619626336799179169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584171079750891199452779 3876256619626336799179169)
            ·
              refine ⟨2907192464719752599384377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3876256619626336799179169 2907192464719752599384377)
              ·
                refine ⟨2180394348539814449538283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907192464719752599384377 2180394348539814449538283)
                ·
                  refine ⟨3270591522809721674307425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180394348539814449538283 3270591522809721674307425)
                  ·
                    refine ⟨2452943642107291255730569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3270591522809721674307425 2452943642107291255730569)
                    ·
                      refine ⟨1839707731580468441797927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452943642107291255730569 1839707731580468441797927)
                      ·
                        rfl

theorem cell23_3582818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_3582818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582818 prefixEnd_3582818 := by exact prefixLift 3582818
  have htrace : WordTrace (prefixWord ++ tailWord_3582818) baseStart_3582818 baseEnd_3582818 := by
    simpa [prefixWord, tailWord_3582818, baseEnd_3582818] using wordTrace_append hprefix tailTrace_3582818
  have hstable : (prefixWord ++ tailWord_3582818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582818).length < 2 ^ (prefixWord ++ tailWord_3582818).sum := by decide
  have hdescent : baseEnd_3582818 < baseStart_3582818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582874 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2]
def baseStart_3582874 : Nat := 118140960795 + 3582874 * 2 ^ 59
def prefixEnd_3582874 : Nat := 4983230072969 + 3 ^ 40 * 3582874 * 2
def baseEnd_3582874 : Nat := 1839736486497120222697669

theorem tailTrace_3582874 : CollatzResearch.WordTrace tailWord_3582874 prefixEnd_3582874 1839736486497120222697669 := by
  unfold tailWord_3582874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32669537605466719751992919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87118766947911252671981117 32669537605466719751992919)
  ·
    refine ⟨49004306408200079627989379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32669537605466719751992919 49004306408200079627989379)
    ·
      refine ⟨73506459612300119441984069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49004306408200079627989379 73506459612300119441984069)
      ·
        refine ⟨13782461177306272395372013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73506459612300119441984069 13782461177306272395372013)
        ·
          refine ⟨5168422941489852148264505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13782461177306272395372013 5168422941489852148264505)
          ·
            refine ⟨3876317206117389111198379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5168422941489852148264505 3876317206117389111198379)
            ·
              refine ⟨5814475809176083666797569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876317206117389111198379 5814475809176083666797569)
              ·
                refine ⟨4360856856882062750098177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814475809176083666797569 4360856856882062750098177)
                ·
                  refine ⟨3270642642661547062573633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360856856882062750098177 3270642642661547062573633)
                  ·
                    refine ⟨2452981981996160296930225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3270642642661547062573633 2452981981996160296930225)
                    ·
                      refine ⟨1839736486497120222697669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2452981981996160296930225 1839736486497120222697669)
                      ·
                        rfl

theorem cell23_3582874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_3582874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582874 prefixEnd_3582874 := by exact prefixLift 3582874
  have htrace : WordTrace (prefixWord ++ tailWord_3582874) baseStart_3582874 baseEnd_3582874 := by
    simpa [prefixWord, tailWord_3582874, baseEnd_3582874] using wordTrace_append hprefix tailTrace_3582874
  have hstable : (prefixWord ++ tailWord_3582874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582874).length < 2 ^ (prefixWord ++ tailWord_3582874).sum := by decide
  have hdescent : baseEnd_3582874 < baseStart_3582874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582930 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3582930 : Nat := 118140960795 + 3582930 * 2 ^ 59
def prefixEnd_3582930 : Nat := 4983230072969 + 3 ^ 40 * 3582930 * 2
def baseEnd_3582930 : Nat := 1839765241413772003597411

theorem tailTrace_3582930 : CollatzResearch.WordTrace tailWord_3582930 prefixEnd_3582930 1839765241413772003597411 := by
  unfold tailWord_3582930
  simp only [CollatzResearch.WordTrace]
  refine ⟨32670048227416000143002561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87120128606442667048006829 32670048227416000143002561)
  ·
    refine ⟨24502536170562000107251921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32670048227416000143002561 24502536170562000107251921)
    ·
      refine ⟨18376902127921500080438941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24502536170562000107251921 18376902127921500080438941)
      ·
        refine ⟨6891338297970562530164603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18376902127921500080438941 6891338297970562530164603)
        ·
          refine ⟨10337007446955843795246905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891338297970562530164603 10337007446955843795246905)
          ·
            refine ⟨7752755585216882846435179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10337007446955843795246905 7752755585216882846435179)
            ·
              refine ⟨11629133377825324269652769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7752755585216882846435179 11629133377825324269652769)
              ·
                refine ⟨8721850033368993202239577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11629133377825324269652769 8721850033368993202239577)
                ·
                  refine ⟨6541387525026744901679683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8721850033368993202239577 6541387525026744901679683)
                  ·
                    refine ⟨9812081287540117352519525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6541387525026744901679683 9812081287540117352519525)
                    ·
                      refine ⟨1839765241413772003597411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9812081287540117352519525 1839765241413772003597411)
                      ·
                        rfl

theorem cell23_3582930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3582930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582930 prefixEnd_3582930 := by exact prefixLift 3582930
  have htrace : WordTrace (prefixWord ++ tailWord_3582930) baseStart_3582930 baseEnd_3582930 := by
    simpa [prefixWord, tailWord_3582930, baseEnd_3582930] using wordTrace_append hprefix tailTrace_3582930
  have hstable : (prefixWord ++ tailWord_3582930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582930).length < 2 ^ (prefixWord ++ tailWord_3582930).sum := by decide
  have hdescent : baseEnd_3582930 < baseStart_3582930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582936 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 8]
def baseStart_3582936 : Nat := 118140960795 + 3582936 * 2 ^ 59
def prefixEnd_3582936 : Nat := 4983230072969 + 3 ^ 40 * 3582936 * 2
def baseEnd_3582936 : Nat := 204418702477522108902487

theorem tailTrace_3582936 : CollatzResearch.WordTrace tailWord_3582936 prefixEnd_3582936 204418702477522108902487 := by
  unfold tailWord_3582936
  simp only [CollatzResearch.WordTrace]
  refine ⟨65340205873821131798364331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87120274498428175731152441 65340205873821131798364331)
  ·
    refine ⟨98010308810731697697546497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65340205873821131798364331 98010308810731697697546497)
    ·
      refine ⟨73507731608048773273159873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98010308810731697697546497 73507731608048773273159873)
      ·
        refine ⟨55130798706036579954869905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73507731608048773273159873 55130798706036579954869905)
        ·
          refine ⟨41348099029527434966152429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55130798706036579954869905 41348099029527434966152429)
          ·
            refine ⟨15505537136072788112307161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41348099029527434966152429 15505537136072788112307161)
            ·
              refine ⟨11629152852054591084230371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15505537136072788112307161 11629152852054591084230371)
              ·
                refine ⟨17443729278081886626345557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11629152852054591084230371 17443729278081886626345557)
                ·
                  refine ⟨204418702477522108902487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17443729278081886626345557 204418702477522108902487)
                  ·
                    rfl

theorem cell23_3582936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 8].length) (baseStart_3582936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3582936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3582936 prefixEnd_3582936 := by exact prefixLift 3582936
  have htrace : WordTrace (prefixWord ++ tailWord_3582936) baseStart_3582936 baseEnd_3582936 := by
    simpa [prefixWord, tailWord_3582936, baseEnd_3582936] using wordTrace_append hprefix tailTrace_3582936
  have hstable : (prefixWord ++ tailWord_3582936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582936).length < 2 ^ (prefixWord ++ tailWord_3582936).sum := by decide
  have hdescent : baseEnd_3582936 < baseStart_3582936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583013 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_3583013 : Nat := 118140960795 + 3583013 * 2 ^ 59
def prefixEnd_3583013 : Nat := 4983230072969 + 3 ^ 40 * 3583013 * 2
def baseEnd_3583013 : Nat := 613269286769365059619843

theorem tailTrace_3583013 : CollatzResearch.WordTrace tailWord_3583013 prefixEnd_3583013 613269286769365059619843 := by
  unfold tailWord_3583013
  simp only [CollatzResearch.WordTrace]
  refine ⟨130683220168363305747281693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87122146778908870498187795 130683220168363305747281693)
  ·
    refine ⟨49006207563136239655230635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130683220168363305747281693 49006207563136239655230635)
    ·
      refine ⟨73509311344704359482845953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49006207563136239655230635 73509311344704359482845953)
      ·
        refine ⟨55131983508528269612134465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73509311344704359482845953 55131983508528269612134465)
        ·
          refine ⟨41348987631396202209100849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55131983508528269612134465 41348987631396202209100849)
          ·
            refine ⟨31011740723547151656825637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41348987631396202209100849 31011740723547151656825637)
            ·
              refine ⟨5814701385665090935654807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31011740723547151656825637 5814701385665090935654807)
              ·
                refine ⟨8722052078497636403482211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5814701385665090935654807 8722052078497636403482211)
                ·
                  refine ⟨13083078117746454605223317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8722052078497636403482211 13083078117746454605223317)
                  ·
                    refine ⟨613269286769365059619843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13083078117746454605223317 613269286769365059619843)
                    ·
                      rfl

theorem cell23_3583013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_3583013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583013 prefixEnd_3583013 := by exact prefixLift 3583013
  have htrace : WordTrace (prefixWord ++ tailWord_3583013) baseStart_3583013 baseEnd_3583013 := by
    simpa [prefixWord, tailWord_3583013, baseEnd_3583013] using wordTrace_append hprefix tailTrace_3583013
  have hstable : (prefixWord ++ tailWord_3583013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583013).length < 2 ^ (prefixWord ++ tailWord_3583013).sum := by decide
  have hdescent : baseEnd_3583013 < baseStart_3583013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583030 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3583030 : Nat := 118140960795 + 3583030 * 2 ^ 59
def prefixEnd_3583030 : Nat := 4983230072969 + 3 ^ 40 * 3583030 * 2
def baseEnd_3583030 : Nat := 613272196493073870782317

theorem tailTrace_3583030 : CollatzResearch.WordTrace tailWord_3583030 prefixEnd_3583030 613272196493073870782317 := by
  unfold tailWord_3583030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167740013081357353165659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87122560139534478433767029 8167740013081357353165659)
  ·
    refine ⟨12251610019622036029748489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8167740013081357353165659 12251610019622036029748489)
    ·
      refine ⟨9188707514716527022311367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12251610019622036029748489 9188707514716527022311367)
      ·
        refine ⟨13783061272074790533467051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9188707514716527022311367 13783061272074790533467051)
        ·
          refine ⟨20674591908112185800200577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13783061272074790533467051 20674591908112185800200577)
          ·
            refine ⟨15505943931084139350150433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20674591908112185800200577 15505943931084139350150433)
            ·
              refine ⟨11629457948313104512612825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15505943931084139350150433 11629457948313104512612825)
              ·
                refine ⟨8722093461234828384459619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11629457948313104512612825 8722093461234828384459619)
                ·
                  refine ⟨13083140191852242576689429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8722093461234828384459619 13083140191852242576689429)
                  ·
                    refine ⟨613272196493073870782317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13083140191852242576689429 613272196493073870782317)
                    ·
                      rfl

theorem cell23_3583030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3583030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583030 prefixEnd_3583030 := by exact prefixLift 3583030
  have htrace : WordTrace (prefixWord ++ tailWord_3583030) baseStart_3583030 baseEnd_3583030 := by
    simpa [prefixWord, tailWord_3583030, baseEnd_3583030] using wordTrace_append hprefix tailTrace_3583030
  have hstable : (prefixWord ++ tailWord_3583030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583030).length < 2 ^ (prefixWord ++ tailWord_3583030).sum := by decide
  have hdescent : baseEnd_3583030 < baseStart_3583030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583037 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_3583037 : Nat := 118140960795 + 3583037 * 2 ^ 59
def prefixEnd_3583037 : Nat := 4983230072969 + 3 ^ 40 * 3583037 * 2
def baseEnd_3583037 : Nat := 1839820183843803084959419

theorem tailTrace_3583037 : CollatzResearch.WordTrace tailWord_3583037 prefixEnd_3583037 1839820183843803084959419 := by
  unfold tailWord_3583037
  simp only [CollatzResearch.WordTrace]
  refine ⟨130684095520276357846155365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87122730346850905230770243 130684095520276357846155365)
  ·
    refine ⟨24503267910051817096154131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130684095520276357846155365 24503267910051817096154131)
    ·
      refine ⟨36754901865077725644231197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24503267910051817096154131 36754901865077725644231197)
      ·
        refine ⟨13783088199404147116586699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36754901865077725644231197 13783088199404147116586699)
        ·
          refine ⟨20674632299106220674880049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13783088199404147116586699 20674632299106220674880049)
          ·
            refine ⟨15505974224329665506160037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20674632299106220674880049 15505974224329665506160037)
            ·
              refine ⟨2907370167061812282405007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15505974224329665506160037 2907370167061812282405007)
              ·
                refine ⟨4361055250592718423607511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907370167061812282405007 4361055250592718423607511)
                ·
                  refine ⟨6541582875889077635411267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361055250592718423607511 6541582875889077635411267)
                  ·
                    refine ⟨9812374313833616453116901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6541582875889077635411267 9812374313833616453116901)
                    ·
                      refine ⟨1839820183843803084959419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9812374313833616453116901 1839820183843803084959419)
                      ·
                        rfl

theorem cell23_3583037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_3583037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583037 prefixEnd_3583037 := by exact prefixLift 3583037
  have htrace : WordTrace (prefixWord ++ tailWord_3583037) baseStart_3583037 baseEnd_3583037 := by
    simpa [prefixWord, tailWord_3583037, baseEnd_3583037] using wordTrace_append hprefix tailTrace_3583037
  have hstable : (prefixWord ++ tailWord_3583037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583037).length < 2 ^ (prefixWord ++ tailWord_3583037).sum := by decide
  have hdescent : baseEnd_3583037 < baseStart_3583037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583040 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3]
def baseStart_3583040 : Nat := 118140960795 + 3583040 * 2 ^ 59
def prefixEnd_3583040 : Nat := 4983230072969 + 3 ^ 40 * 3583040 * 2
def baseEnd_3583040 : Nat := 1839821724285766573221905

theorem tailTrace_3583040 : CollatzResearch.WordTrace tailWord_3583040 prefixEnd_3583040 1839821724285766573221905 := by
  unfold tailWord_3583040
  simp only [CollatzResearch.WordTrace]
  refine ⟨65342102469632744679257287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87122803292843659572343049 65342102469632744679257287)
  ·
    refine ⟨98013153704449117018885931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65342102469632744679257287 98013153704449117018885931)
    ·
      refine ⟨147019730556673675528328897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98013153704449117018885931 147019730556673675528328897)
      ·
        refine ⟨110264797917505256646246673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147019730556673675528328897 110264797917505256646246673)
        ·
          refine ⟨82698598438128942484685005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110264797917505256646246673 82698598438128942484685005)
          ·
            refine ⟨31011974414298353431756877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82698598438128942484685005 31011974414298353431756877)
            ·
              refine ⟨11629490405361882536908829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31011974414298353431756877 11629490405361882536908829)
              ·
                refine ⟨4361058902010705951340811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11629490405361882536908829 4361058902010705951340811)
                ·
                  refine ⟨6541588353016058927011217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361058902010705951340811 6541588353016058927011217)
                  ·
                    refine ⟨4906191264762044195258413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6541588353016058927011217 4906191264762044195258413)
                    ·
                      refine ⟨1839821724285766573221905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4906191264762044195258413 1839821724285766573221905)
                      ·
                        rfl

theorem cell23_3583040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_3583040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583040 prefixEnd_3583040 := by exact prefixLift 3583040
  have htrace : WordTrace (prefixWord ++ tailWord_3583040) baseStart_3583040 baseEnd_3583040 := by
    simpa [prefixWord, tailWord_3583040, baseEnd_3583040] using wordTrace_append hprefix tailTrace_3583040
  have hstable : (prefixWord ++ tailWord_3583040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583040).length < 2 ^ (prefixWord ++ tailWord_3583040).sum := by decide
  have hdescent : baseEnd_3583040 < baseStart_3583040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583047 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 2, 4]
def baseStart_3583047 : Nat := 118140960795 + 3583047 * 2 ^ 59
def prefixEnd_3583047 : Nat := 4983230072969 + 3 ^ 40 * 3583047 * 2
def baseEnd_3583047 : Nat := 613275106216782681944791

theorem tailTrace_3583047 : CollatzResearch.WordTrace tailWord_3583047 prefixEnd_3583047 613275106216782681944791 := by
  unfold tailWord_3583047
  simp only [CollatzResearch.WordTrace]
  refine ⟨130684460250240129554019395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87122973500160086369346263 130684460250240129554019395)
  ·
    refine ⟨196026690375360194331029093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130684460250240129554019395 196026690375360194331029093)
    ·
      refine ⟨36755004445380036437067955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196026690375360194331029093 36755004445380036437067955)
      ·
        refine ⟨55132506668070054655601933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36755004445380036437067955 55132506668070054655601933)
        ·
          refine ⟨20674690000526270495850725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55132506668070054655601933 20674690000526270495850725)
          ·
            refine ⟨3876504375098675717972011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20674690000526270495850725 3876504375098675717972011)
            ·
              refine ⟨5814756562648013576958017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876504375098675717972011 5814756562648013576958017)
              ·
                refine ⟨4361067421986010182718513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814756562648013576958017 4361067421986010182718513)
                ·
                  refine ⟨3270800566489507637038885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361067421986010182718513 3270800566489507637038885)
                  ·
                    refine ⟨613275106216782681944791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270800566489507637038885 613275106216782681944791)
                    ·
                      rfl

theorem cell23_3583047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_3583047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583047 prefixEnd_3583047 := by exact prefixLift 3583047
  have htrace : WordTrace (prefixWord ++ tailWord_3583047) baseStart_3583047 baseEnd_3583047 := by
    simpa [prefixWord, tailWord_3583047, baseEnd_3583047] using wordTrace_append hprefix tailTrace_3583047
  have hstable : (prefixWord ++ tailWord_3583047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583047).length < 2 ^ (prefixWord ++ tailWord_3583047).sum := by decide
  have hdescent : baseEnd_3583047 < baseStart_3583047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583054 : List Nat := [4, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_3583054 : Nat := 118140960795 + 3583054 * 2 ^ 59
def prefixEnd_3583054 : Nat := 4983230072969 + 3 ^ 40 * 3583054 * 2
def baseEnd_3583054 : Nat := 1839828913014929518446841

theorem tailTrace_3583054 : CollatzResearch.WordTrace tailWord_3583054 prefixEnd_3583054 1839828913014929518446841 := by
  unfold tailWord_3583054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335589445151846218690527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87123143707476513166349477 16335589445151846218690527)
  ·
    refine ⟨24503384167727769328035791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16335589445151846218690527 24503384167727769328035791)
    ·
      refine ⟨36755076251591653992053687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24503384167727769328035791 36755076251591653992053687)
      ·
        refine ⟨55132614377387480988080531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36755076251591653992053687 55132614377387480988080531)
        ·
          refine ⟨82698921566081221482120797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55132614377387480988080531 82698921566081221482120797)
          ·
            refine ⟨31012095587280458055795299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82698921566081221482120797 31012095587280458055795299)
            ·
              refine ⟨46518143380920687083692949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31012095587280458055795299 46518143380920687083692949)
              ·
                refine ⟨2180537970980657207048107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46518143380920687083692949 2180537970980657207048107)
                ·
                  refine ⟨3270806956470985810572161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180537970980657207048107 3270806956470985810572161)
                  ·
                    refine ⟨2453105217353239357929121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3270806956470985810572161 2453105217353239357929121)
                    ·
                      refine ⟨1839828913014929518446841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2453105217353239357929121 1839828913014929518446841)
                      ·
                        rfl

theorem cell23_3583054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_3583054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583054 prefixEnd_3583054 := by exact prefixLift 3583054
  have htrace : WordTrace (prefixWord ++ tailWord_3583054) baseStart_3583054 baseEnd_3583054 := by
    simpa [prefixWord, tailWord_3583054, baseEnd_3583054] using wordTrace_append hprefix tailTrace_3583054
  have hstable : (prefixWord ++ tailWord_3583054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583054).length < 2 ^ (prefixWord ++ tailWord_3583054).sum := by decide
  have hdescent : baseEnd_3583054 < baseStart_3583054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583056 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 9]
def baseStart_3583056 : Nat := 118140960795 + 3583056 * 2 ^ 59
def prefixEnd_3583056 : Nat := 4983230072969 + 3 ^ 40 * 3583056 * 2
def baseEnd_3583056 : Nat := 613276646658746170207277

theorem tailTrace_3583056 : CollatzResearch.WordTrace tailWord_3583056 prefixEnd_3583056 613276646658746170207277 := by
  unfold tailWord_3583056
  simp only [CollatzResearch.WordTrace]
  refine ⟨65342394253603762045548511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87123192338138349394064681 65342394253603762045548511)
  ·
    refine ⟨98013591380405643068322767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65342394253603762045548511 98013591380405643068322767)
    ·
      refine ⟨147020387070608464602484151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98013591380405643068322767 147020387070608464602484151)
      ·
        refine ⟨220530580605912696903726227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147020387070608464602484151 220530580605912696903726227)
        ·
          refine ⟨330795870908869045355589341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220530580605912696903726227 330795870908869045355589341)
          ·
            refine ⟨124048451590825892008346003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330795870908869045355589341 124048451590825892008346003)
            ·
              refine ⟨186072677386238838012519005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124048451590825892008346003 186072677386238838012519005)
              ·
                refine ⟨69777254019839564254694627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186072677386238838012519005 69777254019839564254694627)
                ·
                  refine ⟨104665881029759346382041941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69777254019839564254694627 104665881029759346382041941)
                  ·
                    refine ⟨613276646658746170207277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 104665881029759346382041941 613276646658746170207277)
                    ·
                      rfl

theorem cell23_3583056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_3583056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583056 prefixEnd_3583056 := by exact prefixLift 3583056
  have htrace : WordTrace (prefixWord ++ tailWord_3583056) baseStart_3583056 baseEnd_3583056 := by
    simpa [prefixWord, tailWord_3583056, baseEnd_3583056] using wordTrace_append hprefix tailTrace_3583056
  have hstable : (prefixWord ++ tailWord_3583056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583056).length < 2 ^ (prefixWord ++ tailWord_3583056).sum := by decide
  have hdescent : baseEnd_3583056 < baseStart_3583056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583074 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3583074 : Nat := 118140960795 + 3583074 * 2 ^ 59
def prefixEnd_3583074 : Nat := 4983230072969 + 3 ^ 40 * 3583074 * 2
def baseEnd_3583074 : Nat := 1839839182628019440196749

theorem tailTrace_3583074 : CollatzResearch.WordTrace tailWord_3583074 prefixEnd_3583074 1839839182628019440196749 := by
  unfold tailWord_3583074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32671361255285578291313069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87123630014094875443501517 32671361255285578291313069)
  ·
    refine ⟨12251760470732091859242401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32671361255285578291313069 12251760470732091859242401)
    ·
      refine ⟨9188820353049068894431801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12251760470732091859242401 9188820353049068894431801)
      ·
        refine ⟨6891615264786801670823851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9188820353049068894431801 6891615264786801670823851)
        ·
          refine ⟨10337422897180202506235777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891615264786801670823851 10337422897180202506235777)
          ·
            refine ⟨7753067172885151879676833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10337422897180202506235777 7753067172885151879676833)
            ·
              refine ⟨5814800379663863909757625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753067172885151879676833 5814800379663863909757625)
              ·
                refine ⟨4361100284747897932318219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814800379663863909757625 4361100284747897932318219)
                ·
                  refine ⟨6541650427121846898477329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361100284747897932318219 6541650427121846898477329)
                  ·
                    refine ⟨4906237820341385173857997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6541650427121846898477329 4906237820341385173857997)
                    ·
                      refine ⟨1839839182628019440196749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4906237820341385173857997 1839839182628019440196749)
                      ·
                        rfl

theorem cell23_3583074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3583074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583074 prefixEnd_3583074 := by exact prefixLift 3583074
  have htrace : WordTrace (prefixWord ++ tailWord_3583074) baseStart_3583074 baseEnd_3583074 := by
    simpa [prefixWord, tailWord_3583074, baseEnd_3583074] using wordTrace_append hprefix tailTrace_3583074
  have hstable : (prefixWord ++ tailWord_3583074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583074).length < 2 ^ (prefixWord ++ tailWord_3583074).sum := by decide
  have hdescent : baseEnd_3583074 < baseStart_3583074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583123 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4]
def baseStart_3583123 : Nat := 118140960795 + 3583123 * 2 ^ 59
def prefixEnd_3583123 : Nat := 4983230072969 + 3 ^ 40 * 3583123 * 2
def baseEnd_3583123 : Nat := 1839864343180089748484023

theorem tailTrace_3583123 : CollatzResearch.WordTrace tailWord_3583123 prefixEnd_3583123 1839864343180089748484023 := by
  unfold tailWord_3583123
  simp only [CollatzResearch.WordTrace]
  refine ⟨130687232197964794533786023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87124821465309863022524015 130687232197964794533786023)
  ·
    refine ⟨196030848296947191800679035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130687232197964794533786023 196030848296947191800679035)
    ·
      refine ⟨294046272445420787701018553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196030848296947191800679035 294046272445420787701018553)
      ·
        refine ⟨220534704334065590775763915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294046272445420787701018553 220534704334065590775763915)
        ·
          refine ⟨330802056501098386163645873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220534704334065590775763915 330802056501098386163645873)
          ·
            refine ⟨248101542375823789622734405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330802056501098386163645873 248101542375823789622734405)
            ·
              refine ⟨46519039195466960554262701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248101542375823789622734405 46519039195466960554262701)
              ·
                refine ⟨17444639698300110207848513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46519039195466960554262701 17444639698300110207848513)
                ·
                  refine ⟨13083479773725082655886385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17444639698300110207848513 13083479773725082655886385)
                  ·
                    refine ⟨9812609830293811991914789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13083479773725082655886385 9812609830293811991914789)
                    ·
                      refine ⟨1839864343180089748484023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9812609830293811991914789 1839864343180089748484023)
                      ·
                        rfl

theorem cell23_3583123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_3583123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583123 prefixEnd_3583123 := by exact prefixLift 3583123
  have htrace : WordTrace (prefixWord ++ tailWord_3583123) baseStart_3583123 baseEnd_3583123 := by
    simpa [prefixWord, tailWord_3583123, baseEnd_3583123] using wordTrace_append hprefix tailTrace_3583123
  have hstable : (prefixWord ++ tailWord_3583123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583123).length < 2 ^ (prefixWord ++ tailWord_3583123).sum := by decide
  have hdescent : baseEnd_3583123 < baseStart_3583123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583130 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3583130 : Nat := 118140960795 + 3583130 * 2 ^ 59
def prefixEnd_3583130 : Nat := 4983230072969 + 3 ^ 40 * 3583130 * 2
def baseEnd_3583130 : Nat := 1839867937544671221096491

theorem tailTrace_3583130 : CollatzResearch.WordTrace tailWord_3583130 prefixEnd_3583130 1839867937544671221096491 := by
  unfold tailWord_3583130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32671871877234858682322711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87124991672626289819527229 32671871877234858682322711)
  ·
    refine ⟨49007807815852288023484067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32671871877234858682322711 49007807815852288023484067)
    ·
      refine ⟨73511711723778432035226101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49007807815852288023484067 73511711723778432035226101)
      ·
        refine ⟨6891722974104228003302447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73511711723778432035226101 6891722974104228003302447)
        ·
          refine ⟨10337584461156342004953671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891722974104228003302447 10337584461156342004953671)
          ·
            refine ⟨15506376691734513007430507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337584461156342004953671 15506376691734513007430507)
            ·
              refine ⟨23259565037601769511145761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15506376691734513007430507 23259565037601769511145761)
              ·
                refine ⟨17444673778201327133359321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23259565037601769511145761 17444673778201327133359321)
                ·
                  refine ⟨13083505333650995350019491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17444673778201327133359321 13083505333650995350019491)
                  ·
                    refine ⟨19625258000476493025029237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13083505333650995350019491 19625258000476493025029237)
                    ·
                      refine ⟨1839867937544671221096491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19625258000476493025029237 1839867937544671221096491)
                      ·
                        rfl

theorem cell23_3583130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3583130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583130 prefixEnd_3583130 := by exact prefixLift 3583130
  have htrace : WordTrace (prefixWord ++ tailWord_3583130) baseStart_3583130 baseEnd_3583130 := by
    simpa [prefixWord, tailWord_3583130, baseEnd_3583130] using wordTrace_append hprefix tailTrace_3583130
  have hstable : (prefixWord ++ tailWord_3583130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583130).length < 2 ^ (prefixWord ++ tailWord_3583130).sum := by decide
  have hdescent : baseEnd_3583130 < baseStart_3583130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583133 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 9]
def baseStart_3583133 : Nat := 118140960795 + 3583133 * 2 ^ 59
def prefixEnd_3583133 : Nat := 4983230072969 + 3 ^ 40 * 3583133 * 2
def baseEnd_3583133 : Nat := 204429941998514967706553

theorem tailTrace_3583133 : CollatzResearch.WordTrace tailWord_3583133 prefixEnd_3583133 204429941998514967706553 := by
  unfold tailWord_3583133
  simp only [CollatzResearch.WordTrace]
  refine ⟨130687596927928566241650053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87125064618619044161100035 130687596927928566241650053)
  ·
    refine ⟨24503924423986606170309385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130687596927928566241650053 24503924423986606170309385)
    ·
      refine ⟨18377943317989954627732039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24503924423986606170309385 18377943317989954627732039)
      ·
        refine ⟨27566914976984931941598059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18377943317989954627732039 27566914976984931941598059)
        ·
          refine ⟨41350372465477397912397089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27566914976984931941598059 41350372465477397912397089)
          ·
            refine ⟨31012779349108048434297817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41350372465477397912397089 31012779349108048434297817)
            ·
              refine ⟨23259584511831036325723363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31012779349108048434297817 23259584511831036325723363)
              ·
                refine ⟨34889376767746554488585045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23259584511831036325723363 34889376767746554488585045)
                ·
                  refine ⟨204429941998514967706553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34889376767746554488585045 204429941998514967706553)
                  ·
                    rfl

theorem cell23_3583133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_3583133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583133 prefixEnd_3583133 := by exact prefixLift 3583133
  have htrace : WordTrace (prefixWord ++ tailWord_3583133) baseStart_3583133 baseEnd_3583133 := by
    simpa [prefixWord, tailWord_3583133, baseEnd_3583133] using wordTrace_append hprefix tailTrace_3583133
  have hstable : (prefixWord ++ tailWord_3583133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583133).length < 2 ^ (prefixWord ++ tailWord_3583133).sum := by decide
  have hdescent : baseEnd_3583133 < baseStart_3583133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583163 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 4, 5]
def baseStart_3583163 : Nat := 118140960795 + 3583163 * 2 ^ 59
def prefixEnd_3583163 : Nat := 4983230072969 + 3 ^ 40 * 3583163 * 2
def baseEnd_3583163 : Nat := 613294960802089863994613

theorem tailTrace_3583163 : CollatzResearch.WordTrace tailWord_3583163 prefixEnd_3583163 613294960802089863994613 := by
  unfold tailWord_3583163
  simp only [CollatzResearch.WordTrace]
  refine ⟨130688691117819881365242143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87125794078546587576828095 130688691117819881365242143)
  ·
    refine ⟨196033036676729822047863215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130688691117819881365242143 196033036676729822047863215)
    ·
      refine ⟨294049555015094733071794823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196033036676729822047863215 294049555015094733071794823)
      ·
        refine ⟨441074332522642099607692235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294049555015094733071794823 441074332522642099607692235)
        ·
          refine ⟨661611498783963149411538353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441074332522642099607692235 661611498783963149411538353)
          ·
            refine ⟨496208624087972362058653765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661611498783963149411538353 496208624087972362058653765)
            ·
              refine ⟨93039117016494817885997581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 496208624087972362058653765 93039117016494817885997581)
              ·
                refine ⟨34889668881185556707249093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93039117016494817885997581 34889668881185556707249093)
                ·
                  refine ⟨6541812915222291882609205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34889668881185556707249093 6541812915222291882609205)
                  ·
                    refine ⟨613294960802089863994613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6541812915222291882609205 613294960802089863994613)
                    ·
                      rfl

theorem cell23_3583163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 5].length) (baseStart_3583163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583163 prefixEnd_3583163 := by exact prefixLift 3583163
  have htrace : WordTrace (prefixWord ++ tailWord_3583163) baseStart_3583163 baseEnd_3583163 := by
    simpa [prefixWord, tailWord_3583163, baseEnd_3583163] using wordTrace_append hprefix tailTrace_3583163
  have hstable : (prefixWord ++ tailWord_3583163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583163).length < 2 ^ (prefixWord ++ tailWord_3583163).sum := by decide
  have hdescent : baseEnd_3583163 < baseStart_3583163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583167 : List Nat := [1, 1, 2, 2, 2, 2, 6, 2, 5]
def baseStart_3583167 : Nat := 118140960795 + 3583167 * 2 ^ 59
def prefixEnd_3583167 : Nat := 4983230072969 + 3 ^ 40 * 3583167 * 2
def baseEnd_3583167 : Nat := 204431881814320841814869

theorem tailTrace_3583167 : CollatzResearch.WordTrace tailWord_3583167 prefixEnd_3583167 204431881814320841814869 := by
  unfold tailWord_3583167
  simp only [CollatzResearch.WordTrace]
  refine ⟨130688837009805390048387755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87125891339870260032258503 130688837009805390048387755)
  ·
    refine ⟨196033255514708085072581633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130688837009805390048387755 196033255514708085072581633)
    ·
      refine ⟨147024941636031063804436225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196033255514708085072581633 147024941636031063804436225)
      ·
        refine ⟨110268706227023297853327169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147024941636031063804436225 110268706227023297853327169)
        ·
          refine ⟨82701529670267473389995377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110268706227023297853327169 82701529670267473389995377)
          ·
            refine ⟨62026147252700605042496533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82701529670267473389995377 62026147252700605042496533)
            ·
              refine ⟨2907475652470340861367025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62026147252700605042496533 2907475652470340861367025)
              ·
                refine ⟨2180606739352755646025269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907475652470340861367025 2180606739352755646025269)
                ·
                  refine ⟨204431881814320841814869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2180606739352755646025269 204431881814320841814869)
                  ·
                    rfl

theorem cell23_3583167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 5].length) (baseStart_3583167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583167 prefixEnd_3583167 := by exact prefixLift 3583167
  have htrace : WordTrace (prefixWord ++ tailWord_3583167) baseStart_3583167 baseEnd_3583167 := by
    simpa [prefixWord, tailWord_3583167, baseEnd_3583167] using wordTrace_append hprefix tailTrace_3583167
  have hstable : (prefixWord ++ tailWord_3583167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583167).length < 2 ^ (prefixWord ++ tailWord_3583167).sum := by decide
  have hdescent : baseEnd_3583167 < baseStart_3583167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583197 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3583197 : Nat := 118140960795 + 3583197 * 2 ^ 59
def prefixEnd_3583197 : Nat := 4983230072969 + 3 ^ 40 * 3583197 * 2
def baseEnd_3583197 : Nat := 613300780249507486319561

theorem tailTrace_3583197 : CollatzResearch.WordTrace tailWord_3583197 prefixEnd_3583197 613300780249507486319561 := by
  unfold tailWord_3583197
  simp only [CollatzResearch.WordTrace]
  refine ⟨130689931199696705171979845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87126620799797803447986563 130689931199696705171979845)
  ·
    refine ⟨24504362099943132219746221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130689931199696705171979845 24504362099943132219746221)
    ·
      refine ⟨9189135787478674582404833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24504362099943132219746221 9189135787478674582404833)
      ·
        refine ⟨6891851840609005936803625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9189135787478674582404833 6891851840609005936803625)
        ·
          refine ⟨5168888880456754452602719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6891851840609005936803625 5168888880456754452602719)
          ·
            refine ⟨7753333320685131678904079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168888880456754452602719 7753333320685131678904079)
            ·
              refine ⟨11629999981027697518356119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753333320685131678904079 11629999981027697518356119)
              ·
                refine ⟨17444999971541546277534179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11629999981027697518356119 17444999971541546277534179)
                ·
                  refine ⟨26167499957312319416301269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17444999971541546277534179 26167499957312319416301269)
                  ·
                    refine ⟨613300780249507486319561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26167499957312319416301269 613300780249507486319561)
                    ·
                      rfl

theorem cell23_3583197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3583197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583197 prefixEnd_3583197 := by exact prefixLift 3583197
  have htrace : WordTrace (prefixWord ++ tailWord_3583197) baseStart_3583197 baseEnd_3583197 := by
    simpa [prefixWord, tailWord_3583197, baseEnd_3583197] using wordTrace_append hprefix tailTrace_3583197
  have hstable : (prefixWord ++ tailWord_3583197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583197).length < 2 ^ (prefixWord ++ tailWord_3583197).sum := by decide
  have hdescent : baseEnd_3583197 < baseStart_3583197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583200 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_3583200 : Nat := 118140960795 + 3583200 * 2 ^ 59
def prefixEnd_3583200 : Nat := 4983230072969 + 3 ^ 40 * 3583200 * 2
def baseEnd_3583200 : Nat := 1839903881190485947221169

theorem tailTrace_3583200 : CollatzResearch.WordTrace tailWord_3583200 prefixEnd_3583200 1839903881190485947221169 := by
  unfold tailWord_3583200
  simp only [CollatzResearch.WordTrace]
  refine ⟨65345020309342918342169527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87126693745790557789559369 65345020309342918342169527)
  ·
    refine ⟨98017530464014377513254291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65345020309342918342169527 98017530464014377513254291)
    ·
      refine ⟨147026295696021566269881437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98017530464014377513254291 147026295696021566269881437)
      ·
        refine ⟨55134860886008087351205539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147026295696021566269881437 55134860886008087351205539)
        ·
          refine ⟨82702291329012131026808309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55134860886008087351205539 82702291329012131026808309)
          ·
            refine ⟨7753339812094887283763279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82702291329012131026808309 7753339812094887283763279)
            ·
              refine ⟨11630009718142330925644919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753339812094887283763279 11630009718142330925644919)
              ·
                refine ⟨17445014577213496388467379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11630009718142330925644919 17445014577213496388467379)
                ·
                  refine ⟨26167521865820244582701069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17445014577213496388467379 26167521865820244582701069)
                  ·
                    refine ⟨9812820699682591718512901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26167521865820244582701069 9812820699682591718512901)
                    ·
                      refine ⟨1839903881190485947221169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9812820699682591718512901 1839903881190485947221169)
                      ·
                        rfl

theorem cell23_3583200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_3583200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583200 prefixEnd_3583200 := by exact prefixLift 3583200
  have htrace : WordTrace (prefixWord ++ tailWord_3583200) baseStart_3583200 baseEnd_3583200 := by
    simpa [prefixWord, tailWord_3583200, baseEnd_3583200] using wordTrace_append hprefix tailTrace_3583200
  have hstable : (prefixWord ++ tailWord_3583200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583200).length < 2 ^ (prefixWord ++ tailWord_3583200).sum := by decide
  have hdescent : baseEnd_3583200 < baseStart_3583200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583223 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 8]
def baseStart_3583223 : Nat := 118140960795 + 3583223 * 2 ^ 59
def prefixEnd_3583223 : Nat := 4983230072969 + 3 ^ 40 * 3583223 * 2
def baseEnd_3583223 : Nat := 204435076805059928581507

theorem tailTrace_3583223 : CollatzResearch.WordTrace tailWord_3583223 prefixEnd_3583223 204435076805059928581507 := by
  unfold tailWord_3583223
  simp only [CollatzResearch.WordTrace]
  refine ⟨130690879497602511612426323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87127252998401674408284215 130690879497602511612426323)
  ·
    refine ⟨196036319246403767418639485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130690879497602511612426323 196036319246403767418639485)
    ·
      refine ⟨73513619717401412781989807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196036319246403767418639485 73513619717401412781989807)
      ·
        refine ⟨110270429576102119172984711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73513619717401412781989807 110270429576102119172984711)
        ·
          refine ⟨165405644364153178759477067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110270429576102119172984711 165405644364153178759477067)
          ·
            refine ⟨248108466546229768139215601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165405644364153178759477067 248108466546229768139215601)
            ·
              refine ⟨186081349909672326104411701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248108466546229768139215601 186081349909672326104411701)
              ·
                refine ⟨17445126554031780572288597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186081349909672326104411701 17445126554031780572288597)
                ·
                  refine ⟨204435076805059928581507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17445126554031780572288597 204435076805059928581507)
                  ·
                    rfl

theorem cell23_3583223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 8].length) (baseStart_3583223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583223 prefixEnd_3583223 := by exact prefixLift 3583223
  have htrace : WordTrace (prefixWord ++ tailWord_3583223) baseStart_3583223 baseEnd_3583223 := by
    simpa [prefixWord, tailWord_3583223, baseEnd_3583223] using wordTrace_append hprefix tailTrace_3583223
  have hstable : (prefixWord ++ tailWord_3583223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583223).length < 2 ^ (prefixWord ++ tailWord_3583223).sum := by decide
  have hdescent : baseEnd_3583223 < baseStart_3583223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583261 : List Nat := [1, 4, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_3583261 : Nat := 118140960795 + 3583261 * 2 ^ 59
def prefixEnd_3583261 : Nat := 4983230072969 + 3 ^ 40 * 3583261 * 2
def baseEnd_3583261 : Nat := 613311734503470069519463

theorem tailTrace_3583261 : CollatzResearch.WordTrace tailWord_3583261 prefixEnd_3583261 613311734503470069519463 := by
  unfold tailWord_3583261
  simp only [CollatzResearch.WordTrace]
  refine ⟨130692265471464844102309637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87128176980976562734873091 130692265471464844102309637)
  ·
    refine ⟨24504799775899658269183057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130692265471464844102309637 24504799775899658269183057)
    ·
      refine ⟨18378599831924743701887293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24504799775899658269183057 18378599831924743701887293)
      ·
        refine ⟨6891974936971778888207735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18378599831924743701887293 6891974936971778888207735)
        ·
          refine ⟨10337962405457668332311603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891974936971778888207735 10337962405457668332311603)
          ·
            refine ⟨15506943608186502498467405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337962405457668332311603 15506943608186502498467405)
            ·
              refine ⟨5815103853069938436925277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15506943608186502498467405 5815103853069938436925277)
              ·
                refine ⟨2180663944901226913846979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5815103853069938436925277 2180663944901226913846979)
                ·
                  refine ⟨3270995917351840370770469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180663944901226913846979 3270995917351840370770469)
                  ·
                    refine ⟨613311734503470069519463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270995917351840370770469 613311734503470069519463)
                    ·
                      rfl

theorem cell23_3583261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_3583261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583261 prefixEnd_3583261 := by exact prefixLift 3583261
  have htrace : WordTrace (prefixWord ++ tailWord_3583261) baseStart_3583261 baseEnd_3583261 := by
    simpa [prefixWord, tailWord_3583261, baseEnd_3583261] using wordTrace_append hprefix tailTrace_3583261
  have hstable : (prefixWord ++ tailWord_3583261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583261).length < 2 ^ (prefixWord ++ tailWord_3583261).sum := by decide
  have hdescent : baseEnd_3583261 < baseStart_3583261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583294 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_3583294 : Nat := 118140960795 + 3583294 * 2 ^ 59
def prefixEnd_3583294 : Nat := 4983230072969 + 3 ^ 40 * 3583294 * 2
def baseEnd_3583294 : Nat := 1839952148372008579445737

theorem tailTrace_3583294 : CollatzResearch.WordTrace tailWord_3583294 prefixEnd_3583294 1839952148372008579445737 := by
  unfold tailWord_3583294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16336683635043161342282617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87128979386896860492173957 16336683635043161342282617)
  ·
    refine ⟨12252512726282371006711963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16336683635043161342282617 12252512726282371006711963)
    ·
      refine ⟨18378769089423556510067945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12252512726282371006711963 18378769089423556510067945)
      ·
        refine ⟨13784076817067667382550959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18378769089423556510067945 13784076817067667382550959)
        ·
          refine ⟨20676115225601501073826439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13784076817067667382550959 20676115225601501073826439)
          ·
            refine ⟨31014172838402251610739659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20676115225601501073826439 31014172838402251610739659)
            ·
              refine ⟨46521259257603377416109489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31014172838402251610739659 46521259257603377416109489)
              ·
                refine ⟨34890944443202533062082117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46521259257603377416109489 34890944443202533062082117)
                ·
                  refine ⟨6542052083100474949140397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34890944443202533062082117 6542052083100474949140397)
                  ·
                    refine ⟨2453269531162678105927649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6542052083100474949140397 2453269531162678105927649)
                    ·
                      refine ⟨1839952148372008579445737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2453269531162678105927649 1839952148372008579445737)
                      ·
                        rfl

theorem cell23_3583294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_3583294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583294 prefixEnd_3583294 := by exact prefixLift 3583294
  have htrace : WordTrace (prefixWord ++ tailWord_3583294) baseStart_3583294 baseEnd_3583294 := by
    simpa [prefixWord, tailWord_3583294, baseEnd_3583294] using wordTrace_append hprefix tailTrace_3583294
  have hstable : (prefixWord ++ tailWord_3583294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583294).length < 2 ^ (prefixWord ++ tailWord_3583294).sum := by decide
  have hdescent : baseEnd_3583294 < baseStart_3583294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583317 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3583317 : Nat := 118140960795 + 3583317 * 2 ^ 59
def prefixEnd_3583317 : Nat := 4983230072969 + 3 ^ 40 * 3583317 * 2
def baseEnd_3583317 : Nat := 613321319475687329819377

theorem tailTrace_3583317 : CollatzResearch.WordTrace tailWord_3583317 prefixEnd_3583317 613321319475687329819377 := by
  unfold tailWord_3583317
  simp only [CollatzResearch.WordTrace]
  refine ⟨130694307959261965666348205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87129538639507977110898803 130694307959261965666348205)
  ·
    refine ⟨49010365484723237124880577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130694307959261965666348205 49010365484723237124880577)
    ·
      refine ⟨36757774113542427843660433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49010365484723237124880577 36757774113542427843660433)
      ·
        refine ⟨27568330585156820882745325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36757774113542427843660433 27568330585156820882745325)
        ·
          refine ⟨10338123969433807831029497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27568330585156820882745325 10338123969433807831029497)
          ·
            refine ⟨7753592977075355873272123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10338123969433807831029497 7753592977075355873272123)
            ·
              refine ⟨11630389465613033809908185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753592977075355873272123 11630389465613033809908185)
              ·
                refine ⟨8722792099209775357431139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11630389465613033809908185 8722792099209775357431139)
                ·
                  refine ⟨13084188148814663036146709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8722792099209775357431139 13084188148814663036146709)
                  ·
                    refine ⟨613321319475687329819377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13084188148814663036146709 613321319475687329819377)
                    ·
                      rfl

theorem cell23_3583317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3583317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583317 prefixEnd_3583317 := by exact prefixLift 3583317
  have htrace : WordTrace (prefixWord ++ tailWord_3583317) baseStart_3583317 baseEnd_3583317 := by
    simpa [prefixWord, tailWord_3583317, baseEnd_3583317] using wordTrace_append hprefix tailTrace_3583317
  have hstable : (prefixWord ++ tailWord_3583317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583317).length < 2 ^ (prefixWord ++ tailWord_3583317).sum := by decide
  have hdescent : baseEnd_3583317 < baseStart_3583317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583335 : List Nat := [1, 1, 5, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_3583335 : Nat := 118140960795 + 3583335 * 2 ^ 59
def prefixEnd_3583335 : Nat := 4983230072969 + 3 ^ 40 * 3583335 * 2
def baseEnd_3583335 : Nat := 1839973201078842919033049

theorem tailTrace_3583335 : CollatzResearch.WordTrace tailWord_3583335 prefixEnd_3583335 1839973201078842919033049 := by
  unfold tailWord_3583335
  simp only [CollatzResearch.WordTrace]
  refine ⟨130694964473196754740503459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87129976315464503160335639 130694964473196754740503459)
  ·
    refine ⟨196042446709795132110755189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130694964473196754740503459 196042446709795132110755189)
    ·
      refine ⟨18378979379043293635383299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196042446709795132110755189 18378979379043293635383299)
      ·
        refine ⟨27568469068564940453074949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18378979379043293635383299 27568469068564940453074949)
        ·
          refine ⟨5169087950355926334951553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27568469068564940453074949 5169087950355926334951553)
          ·
            refine ⟨3876815962766944751213665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5169087950355926334951553 3876815962766944751213665)
            ·
              refine ⟨2907611972075208563410249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3876815962766944751213665 2907611972075208563410249)
              ·
                refine ⟨2180708979056406422557687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907611972075208563410249 2180708979056406422557687)
                ·
                  refine ⟨3271063468584609633836531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180708979056406422557687 3271063468584609633836531)
                  ·
                    refine ⟨4906595202876914450754797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3271063468584609633836531 4906595202876914450754797)
                    ·
                      refine ⟨1839973201078842919033049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4906595202876914450754797 1839973201078842919033049)
                      ·
                        rfl

theorem cell23_3583335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_3583335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583335 prefixEnd_3583335 := by exact prefixLift 3583335
  have htrace : WordTrace (prefixWord ++ tailWord_3583335) baseStart_3583335 baseEnd_3583335 := by
    simpa [prefixWord, tailWord_3583335, baseEnd_3583335] using wordTrace_append hprefix tailTrace_3583335
  have hstable : (prefixWord ++ tailWord_3583335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583335).length < 2 ^ (prefixWord ++ tailWord_3583335).sum := by decide
  have hdescent : baseEnd_3583335 < baseStart_3583335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583378 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3583378 : Nat := 118140960795 + 3583378 * 2 ^ 59
def prefixEnd_3583378 : Nat := 4983230072969 + 3 ^ 40 * 3583378 * 2
def baseEnd_3583378 : Nat := 1839995280746986250795351

theorem tailTrace_3583378 : CollatzResearch.WordTrace tailWord_3583378 prefixEnd_3583378 1839995280746986250795351 := by
  unfold tailWord_3583378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32674133203010243271079697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87131021874693982056212525 32674133203010243271079697)
  ·
    refine ⟨24505599902257682453309773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32674133203010243271079697 24505599902257682453309773)
    ·
      refine ⟨9189599963346630919991165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24505599902257682453309773 9189599963346630919991165)
      ·
        refine ⟨3446099986254986594996687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9189599963346630919991165 3446099986254986594996687)
        ·
          refine ⟨5169149979382479892495031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446099986254986594996687 5169149979382479892495031)
          ·
            refine ⟨7753724969073719838742547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169149979382479892495031 7753724969073719838742547)
            ·
              refine ⟨11630587453610579758113821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753724969073719838742547 11630587453610579758113821)
              ·
                refine ⟨4361470295103967409292683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11630587453610579758113821 4361470295103967409292683)
                ·
                  refine ⟨6542205442655951113939025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361470295103967409292683 6542205442655951113939025)
                  ·
                    refine ⟨4906654081991963335454269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542205442655951113939025 4906654081991963335454269)
                    ·
                      refine ⟨1839995280746986250795351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4906654081991963335454269 1839995280746986250795351)
                      ·
                        rfl

theorem cell23_3583378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3583378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583378 prefixEnd_3583378 := by exact prefixLift 3583378
  have htrace : WordTrace (prefixWord ++ tailWord_3583378) baseStart_3583378 baseEnd_3583378 := by
    simpa [prefixWord, tailWord_3583378, baseEnd_3583378] using wordTrace_append hprefix tailTrace_3583378
  have hstable : (prefixWord ++ tailWord_3583378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583378).length < 2 ^ (prefixWord ++ tailWord_3583378).sum := by decide
  have hdescent : baseEnd_3583378 < baseStart_3583378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583391 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3583391 : Nat := 118140960795 + 3583391 * 2 ^ 59
def prefixEnd_3583391 : Nat := 4983230072969 + 3 ^ 40 * 3583391 * 2
def baseEnd_3583391 : Nat := 1840001955995494699932791

theorem tailTrace_3583391 : CollatzResearch.WordTrace tailWord_3583391 prefixEnd_3583391 1840001955995494699932791 := by
  unfold tailWord_3583391
  simp only [CollatzResearch.WordTrace]
  refine ⟨130697006960993876304542027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87131337973995917536361351 130697006960993876304542027)
  ·
    refine ⟨196045510441490814456813041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130697006960993876304542027 196045510441490814456813041)
    ·
      refine ⟨147034132831118110842609781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196045510441490814456813041 147034132831118110842609781)
      ·
        refine ⟨13784449952917322891494667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147034132831118110842609781 13784449952917322891494667)
        ·
          refine ⟨20676674929375984337242001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13784449952917322891494667 20676674929375984337242001)
          ·
            refine ⟨15507506197031988252931501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20676674929375984337242001 15507506197031988252931501)
            ·
              refine ⟨5815314823886995594849313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15507506197031988252931501 5815314823886995594849313)
              ·
                refine ⟨4361486117915246696136985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815314823886995594849313 4361486117915246696136985)
                ·
                  refine ⟨3271114588436435022102739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361486117915246696136985 3271114588436435022102739)
                  ·
                    refine ⟨4906671882654652533154109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3271114588436435022102739 4906671882654652533154109)
                    ·
                      refine ⟨1840001955995494699932791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4906671882654652533154109 1840001955995494699932791)
                      ·
                        rfl

theorem cell23_3583391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3583391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583391 prefixEnd_3583391 := by exact prefixLift 3583391
  have htrace : WordTrace (prefixWord ++ tailWord_3583391) baseStart_3583391 baseEnd_3583391 := by
    simpa [prefixWord, tailWord_3583391, baseEnd_3583391] using wordTrace_append hprefix tailTrace_3583391
  have hstable : (prefixWord ++ tailWord_3583391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583391).length < 2 ^ (prefixWord ++ tailWord_3583391).sum := by decide
  have hdescent : baseEnd_3583391 < baseStart_3583391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583447 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_3583447 : Nat := 118140960795 + 3583447 * 2 ^ 59
def prefixEnd_3583447 : Nat := 4983230072969 + 3 ^ 40 * 3583447 * 2
def baseEnd_3583447 : Nat := 1840030710912146480832533

theorem tailTrace_3583447 : CollatzResearch.WordTrace tailWord_3583447 prefixEnd_3583447 1840030710912146480832533 := by
  unfold tailWord_3583447
  simp only [CollatzResearch.WordTrace]
  refine ⟨130699049448790997868580595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87132699632527331912387063 130699049448790997868580595)
  ·
    refine ⟨196048574173186496802870893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130699049448790997868580595 196048574173186496802870893)
    ·
      refine ⟨73518215314944936301076585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196048574173186496802870893 73518215314944936301076585)
      ·
        refine ⟨55138661486208702225807439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73518215314944936301076585 55138661486208702225807439)
        ·
          refine ⟨82707992229313053338711159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55138661486208702225807439 82707992229313053338711159)
          ·
            refine ⟨124061988343969580008066739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82707992229313053338711159 124061988343969580008066739)
            ·
              refine ⟨186092982515954370012100109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124061988343969580008066739 186092982515954370012100109)
              ·
                refine ⟨69784868443482888754537541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186092982515954370012100109 69784868443482888754537541)
                ·
                  refine ⟨13084662833153041641475789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69784868443482888754537541 13084662833153041641475789)
                  ·
                    refine ⟨4906748562432390615553421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13084662833153041641475789 4906748562432390615553421)
                    ·
                      refine ⟨1840030710912146480832533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4906748562432390615553421 1840030710912146480832533)
                      ·
                        rfl

theorem cell23_3583447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_3583447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583447 prefixEnd_3583447 := by exact prefixLift 3583447
  have htrace : WordTrace (prefixWord ++ tailWord_3583447) baseStart_3583447 baseEnd_3583447 := by
    simpa [prefixWord, tailWord_3583447, baseEnd_3583447] using wordTrace_append hprefix tailTrace_3583447
  have hstable : (prefixWord ++ tailWord_3583447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583447).length < 2 ^ (prefixWord ++ tailWord_3583447).sum := by decide
  have hdescent : baseEnd_3583447 < baseStart_3583447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583514 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_3583514 : Nat := 118140960795 + 3583514 * 2 ^ 59
def prefixEnd_3583514 : Nat := 4983230072969 + 3 ^ 40 * 3583514 * 2
def baseEnd_3583514 : Nat := 613355038038665906231575

theorem tailTrace_3583514 : CollatzResearch.WordTrace tailWord_3583514 prefixEnd_3583514 613355038038665906231575 := by
  unfold tailWord_3583514
  simp only [CollatzResearch.WordTrace]
  refine ⟨32675373284887067077817399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87134328759698845540846397 32675373284887067077817399)
  ·
    refine ⟨49013059927330600616726099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32675373284887067077817399 49013059927330600616726099)
    ·
      refine ⟨73519589890995900925089149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49013059927330600616726099 73519589890995900925089149)
      ·
        refine ⟨27569846209123462846908431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73519589890995900925089149 27569846209123462846908431)
        ·
          refine ⟨41354769313685194270362647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27569846209123462846908431 41354769313685194270362647)
          ·
            refine ⟨62032153970527791405543971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41354769313685194270362647 62032153970527791405543971)
            ·
              refine ⟨93048230955791687108315957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62032153970527791405543971 93048230955791687108315957)
              ·
                refine ⟨8723271652105470666404621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93048230955791687108315957 8723271652105470666404621)
                ·
                  refine ⟨3271226869539551499901733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8723271652105470666404621 3271226869539551499901733)
                  ·
                    refine ⟨613355038038665906231575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271226869539551499901733 613355038038665906231575)
                    ·
                      rfl

theorem cell23_3583514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_3583514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583514 prefixEnd_3583514 := by exact prefixLift 3583514
  have htrace : WordTrace (prefixWord ++ tailWord_3583514) baseStart_3583514 baseEnd_3583514 := by
    simpa [prefixWord, tailWord_3583514, baseEnd_3583514] using wordTrace_append hprefix tailTrace_3583514
  have hstable : (prefixWord ++ tailWord_3583514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583514).length < 2 ^ (prefixWord ++ tailWord_3583514).sum := by decide
  have hdescent : baseEnd_3583514 < baseStart_3583514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583521 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_3583521 : Nat := 118140960795 + 3583521 * 2 ^ 59
def prefixEnd_3583521 : Nat := 4983230072969 + 3 ^ 40 * 3583521 * 2
def baseEnd_3583521 : Nat := 1840068708480579191307193

theorem tailTrace_3583521 : CollatzResearch.WordTrace tailWord_3583521 prefixEnd_3583521 1840068708480579191307193 := by
  unfold tailWord_3583521
  simp only [CollatzResearch.WordTrace]
  refine ⟨130701748450522908506774417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87134498967015272337849611 130701748450522908506774417)
  ·
    refine ⟨98026311337892181380080813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130701748450522908506774417 98026311337892181380080813)
    ·
      refine ⟨36759866751709568017530305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98026311337892181380080813 36759866751709568017530305)
      ·
        refine ⟨27569900063782176013147729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36759866751709568017530305 27569900063782176013147729)
        ·
          refine ⟨20677425047836632009860797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27569900063782176013147729 20677425047836632009860797)
          ·
            refine ⟨7754034392938737003697799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20677425047836632009860797 7754034392938737003697799)
            ·
              refine ⟨11631051589408105505546699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754034392938737003697799 11631051589408105505546699)
              ·
                refine ⟨17446577384112158258320049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11631051589408105505546699 17446577384112158258320049)
                ·
                  refine ⟨13084933038084118693740037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17446577384112158258320049 13084933038084118693740037)
                  ·
                    refine ⟨2453424944640772255076257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13084933038084118693740037 2453424944640772255076257)
                    ·
                      refine ⟨1840068708480579191307193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2453424944640772255076257 1840068708480579191307193)
                      ·
                        rfl

theorem cell23_3583521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_3583521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583521 prefixEnd_3583521 := by exact prefixLift 3583521
  have htrace : WordTrace (prefixWord ++ tailWord_3583521) baseStart_3583521 baseEnd_3583521 := by
    simpa [prefixWord, tailWord_3583521, baseEnd_3583521] using wordTrace_append hprefix tailTrace_3583521
  have hstable : (prefixWord ++ tailWord_3583521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583521).length < 2 ^ (prefixWord ++ tailWord_3583521).sum := by decide
  have hdescent : baseEnd_3583521 < baseStart_3583521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583541 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_3583541 : Nat := 118140960795 + 3583541 * 2 ^ 59
def prefixEnd_3583541 : Nat := 4983230072969 + 3 ^ 40 * 3583541 * 2
def baseEnd_3583541 : Nat := 1840078978093669113057101

theorem tailTrace_3583541 : CollatzResearch.WordTrace tailWord_3583541 prefixEnd_3583541 1840078978093669113057101 := by
  unfold tailWord_3583541
  simp only [CollatzResearch.WordTrace]
  refine ⟨130702477910450451922502477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87134985273633634615001651 130702477910450451922502477)
  ·
    refine ⟨49013429216418919470938429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130702477910450451922502477 49013429216418919470938429)
    ·
      refine ⟨18380035956157094801601911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49013429216418919470938429 18380035956157094801601911)
      ·
        refine ⟨27570053934235642202402867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18380035956157094801601911 27570053934235642202402867)
        ·
          refine ⟨41355080901353463303604301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27570053934235642202402867 41355080901353463303604301)
          ·
            refine ⟨15508155338007548738851613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41355080901353463303604301 15508155338007548738851613)
            ·
              refine ⟨5815558251752830777069355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15508155338007548738851613 5815558251752830777069355)
              ·
                refine ⟨8723337377629246165604033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815558251752830777069355 8723337377629246165604033)
                ·
                  refine ⟨6542503033221934624203025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8723337377629246165604033 6542503033221934624203025)
                  ·
                    refine ⟨4906877274916450968152269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542503033221934624203025 4906877274916450968152269)
                    ·
                      refine ⟨1840078978093669113057101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4906877274916450968152269 1840078978093669113057101)
                      ·
                        rfl

theorem cell23_3583541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_3583541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583541 prefixEnd_3583541 := by exact prefixLift 3583541
  have htrace : WordTrace (prefixWord ++ tailWord_3583541) baseStart_3583541 baseEnd_3583541 := by
    simpa [prefixWord, tailWord_3583541, baseEnd_3583541] using wordTrace_append hprefix tailTrace_3583541
  have hstable : (prefixWord ++ tailWord_3583541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583541).length < 2 ^ (prefixWord ++ tailWord_3583541).sum := by decide
  have hdescent : baseEnd_3583541 < baseStart_3583541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583621 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_3583621 : Nat := 118140960795 + 3583621 * 2 ^ 59
def prefixEnd_3583621 : Nat := 4983230072969 + 3 ^ 40 * 3583621 * 2
def baseEnd_3583621 : Nat := 613373352182009600018911

theorem tailTrace_3583621 : CollatzResearch.WordTrace tailWord_3583621 prefixEnd_3583621 613373352182009600018911 := by
  unfold tailWord_3583621
  simp only [CollatzResearch.WordTrace]
  refine ⟨130705395750160625585414717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87136930500107083723609811 130705395750160625585414717)
  ·
    refine ⟨49014523406310234594530519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130705395750160625585414717 49014523406310234594530519)
    ·
      refine ⟨73521785109465351891795779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49014523406310234594530519 73521785109465351891795779)
      ·
        refine ⟨110282677664198027837693669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73521785109465351891795779 110282677664198027837693669)
        ·
          refine ⟨20678002062037130219567563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110282677664198027837693669 20678002062037130219567563)
          ·
            refine ⟨31017003093055695329351345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20678002062037130219567563 31017003093055695329351345)
            ·
              refine ⟨23262752319791771497013509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31017003093055695329351345 23262752319791771497013509)
              ·
                refine ⟨4361766059960957155690033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23262752319791771497013509 4361766059960957155690033)
                ·
                  refine ⟨3271324544970717866767525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361766059960957155690033 3271324544970717866767525)
                  ·
                    refine ⟨613373352182009600018911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271324544970717866767525 613373352182009600018911)
                    ·
                      rfl

theorem cell23_3583621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_3583621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583621 prefixEnd_3583621 := by exact prefixLift 3583621
  have htrace : WordTrace (prefixWord ++ tailWord_3583621) baseStart_3583621 baseEnd_3583621 := by
    simpa [prefixWord, tailWord_3583621, baseEnd_3583621] using wordTrace_append hprefix tailTrace_3583621
  have hstable : (prefixWord ++ tailWord_3583621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583621).length < 2 ^ (prefixWord ++ tailWord_3583621).sum := by decide
  have hdescent : baseEnd_3583621 < baseStart_3583621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583648 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3]
def baseStart_3583648 : Nat := 118140960795 + 3583648 * 2 ^ 59
def prefixEnd_3583648 : Nat := 4983230072969 + 3 ^ 40 * 3583648 * 2
def baseEnd_3583648 : Nat := 1840133920523700194419109

theorem tailTrace_3583648 : CollatzResearch.WordTrace tailWord_3583648 prefixEnd_3583648 1840133920523700194419109 := by
  unfold tailWord_3583648
  simp only [CollatzResearch.WordTrace]
  refine ⟨65353190260531404598323799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87137587014041872797765065 65353190260531404598323799)
  ·
    refine ⟨98029785390797106897485699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65353190260531404598323799 98029785390797106897485699)
    ·
      refine ⟨147044678086195660346228549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98029785390797106897485699 147044678086195660346228549)
      ·
        refine ⟨27570877141161686314917853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147044678086195660346228549 27570877141161686314917853)
        ·
          refine ⟨10339078927935632368094195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27570877141161686314917853 10339078927935632368094195)
          ·
            refine ⟨15508618391903448552141293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10339078927935632368094195 15508618391903448552141293)
            ·
              refine ⟨5815731896963793207052985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15508618391903448552141293 5815731896963793207052985)
              ·
                refine ⟨4361798922722844905289739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815731896963793207052985 4361798922722844905289739)
                ·
                  refine ⟨6542698384084267357934609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361798922722844905289739 6542698384084267357934609)
                  ·
                    refine ⟨4907023788063200518450957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542698384084267357934609 4907023788063200518450957)
                    ·
                      refine ⟨1840133920523700194419109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4907023788063200518450957 1840133920523700194419109)
                      ·
                        rfl

theorem cell23_3583648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_3583648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583648 prefixEnd_3583648 := by exact prefixLift 3583648
  have htrace : WordTrace (prefixWord ++ tailWord_3583648) baseStart_3583648 baseEnd_3583648 := by
    simpa [prefixWord, tailWord_3583648, baseEnd_3583648] using wordTrace_append hprefix tailTrace_3583648
  have hstable : (prefixWord ++ tailWord_3583648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583648).length < 2 ^ (prefixWord ++ tailWord_3583648).sum := by decide
  have hdescent : baseEnd_3583648 < baseStart_3583648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583662 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_3583662 : Nat := 118140960795 + 3583662 * 2 ^ 59
def prefixEnd_3583662 : Nat := 4983230072969 + 3 ^ 40 * 3583662 * 2
def baseEnd_3583662 : Nat := 1840141109252863139644045

theorem tailTrace_3583662 : CollatzResearch.WordTrace tailWord_3583662 prefixEnd_3583662 1840141109252863139644045 := by
  unfold tailWord_3583662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16338361392876511198457155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87137927428674726391771493 16338361392876511198457155)
  ·
    refine ⟨24507542089314766797685733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16338361392876511198457155 24507542089314766797685733)
    ·
      refine ⟨4595164141746518774566075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24507542089314766797685733 4595164141746518774566075)
      ·
        refine ⟨6892746212619778161849113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595164141746518774566075 6892746212619778161849113)
        ·
          refine ⟨5169559659464833621386835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6892746212619778161849113 5169559659464833621386835)
          ·
            refine ⟨7754339489197250432080253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169559659464833621386835 7754339489197250432080253)
            ·
              refine ⟨2907877308448968912030095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7754339489197250432080253 2907877308448968912030095)
              ·
                refine ⟨4361815962673453368045143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907877308448968912030095 4361815962673453368045143)
                ·
                  refine ⟨6542723944010180052067715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361815962673453368045143 6542723944010180052067715)
                  ·
                    refine ⟨9814085916015270078101573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542723944010180052067715 9814085916015270078101573)
                    ·
                      refine ⟨1840141109252863139644045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9814085916015270078101573 1840141109252863139644045)
                      ·
                        rfl

theorem cell23_3583662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_3583662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583662 prefixEnd_3583662 := by exact prefixLift 3583662
  have htrace : WordTrace (prefixWord ++ tailWord_3583662) baseStart_3583662 baseEnd_3583662 := by
    simpa [prefixWord, tailWord_3583662, baseEnd_3583662] using wordTrace_append hprefix tailTrace_3583662
  have hstable : (prefixWord ++ tailWord_3583662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583662).length < 2 ^ (prefixWord ++ tailWord_3583662).sum := by decide
  have hdescent : baseEnd_3583662 < baseStart_3583662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583735 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 2, 2, 2]
def baseStart_3583735 : Nat := 118140960795 + 3583735 * 2 ^ 59
def prefixEnd_3583735 : Nat := 4983230072969 + 3 ^ 40 * 3583735 * 2
def baseEnd_3583735 : Nat := 1840178593340641354031209

theorem tailTrace_3583735 : CollatzResearch.WordTrace tailWord_3583735 prefixEnd_3583735 1840178593340641354031209 := by
  unfold tailWord_3583735
  simp only [CollatzResearch.WordTrace]
  refine ⟨130709553671747623055064659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87139702447831748703376439 130709553671747623055064659)
  ·
    refine ⟨196064330507621434582596989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130709553671747623055064659 196064330507621434582596989)
    ·
      refine ⟨73524123940358037968473871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196064330507621434582596989 73524123940358037968473871)
      ·
        refine ⟨110286185910537056952710807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73524123940358037968473871 110286185910537056952710807)
        ·
          refine ⟨165429278865805585429066211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110286185910537056952710807 165429278865805585429066211)
          ·
            refine ⟨248143918298708378143599317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165429278865805585429066211 248143918298708378143599317)
            ·
              refine ⟨5815873085125977612740609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 248143918298708378143599317 5815873085125977612740609)
              ·
                refine ⟨4361904813844483209555457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815873085125977612740609 4361904813844483209555457)
                ·
                  refine ⟨3271428610383362407166593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361904813844483209555457 3271428610383362407166593)
                  ·
                    refine ⟨2453571457787521805374945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3271428610383362407166593 2453571457787521805374945)
                    ·
                      refine ⟨1840178593340641354031209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2453571457787521805374945 1840178593340641354031209)
                      ·
                        rfl

theorem cell23_3583735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_3583735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583735 prefixEnd_3583735 := by exact prefixLift 3583735
  have htrace : WordTrace (prefixWord ++ tailWord_3583735) baseStart_3583735 baseEnd_3583735 := by
    simpa [prefixWord, tailWord_3583735, baseEnd_3583735] using wordTrace_append hprefix tailTrace_3583735
  have hstable : (prefixWord ++ tailWord_3583735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583735).length < 2 ^ (prefixWord ++ tailWord_3583735).sum := by decide
  have hdescent : baseEnd_3583735 < baseStart_3583735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583752 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_3583752 : Nat := 118140960795 + 3583752 * 2 ^ 59
def prefixEnd_3583752 : Nat := 4983230072969 + 3 ^ 40 * 3583752 * 2
def baseEnd_3583752 : Nat := 1840187322511767787518631

theorem tailTrace_3583752 : CollatzResearch.WordTrace tailWord_3583752 prefixEnd_3583752 1840187322511767787518631 := by
  unfold tailWord_3583752
  simp only [CollatzResearch.WordTrace]
  refine ⟨65355086856343017479216755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87140115808457356638955673 65355086856343017479216755)
  ·
    refine ⟨98032630284514526218825133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65355086856343017479216755 98032630284514526218825133)
    ·
      refine ⟨36762236356692947332059425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98032630284514526218825133 36762236356692947332059425)
      ·
        refine ⟨27571677267519710499044569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36762236356692947332059425 27571677267519710499044569)
        ·
          refine ⟨20678757950639782874283427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27571677267519710499044569 20678757950639782874283427)
          ·
            refine ⟨31018136925959674311425141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20678757950639782874283427 31018136925959674311425141)
            ·
              refine ⟨2907950336808719466696107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31018136925959674311425141 2907950336808719466696107)
              ·
                refine ⟨4361925505213079200044161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907950336808719466696107 4361925505213079200044161)
                ·
                  refine ⟨3271444128909809400033121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361925505213079200044161 3271444128909809400033121)
                  ·
                    refine ⟨2453583096682357050024841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3271444128909809400033121 2453583096682357050024841)
                    ·
                      refine ⟨1840187322511767787518631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2453583096682357050024841 1840187322511767787518631)
                      ·
                        rfl

theorem cell23_3583752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_3583752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583752 prefixEnd_3583752 := by exact prefixLift 3583752
  have htrace : WordTrace (prefixWord ++ tailWord_3583752) baseStart_3583752 baseEnd_3583752 := by
    simpa [prefixWord, tailWord_3583752, baseEnd_3583752] using wordTrace_append hprefix tailTrace_3583752
  have hstable : (prefixWord ++ tailWord_3583752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583752).length < 2 ^ (prefixWord ++ tailWord_3583752).sum := by decide
  have hdescent : baseEnd_3583752 < baseStart_3583752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583791 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_3583791 : Nat := 118140960795 + 3583791 * 2 ^ 59
def prefixEnd_3583791 : Nat := 4983230072969 + 3 ^ 40 * 3583791 * 2
def baseEnd_3583791 : Nat := 1840207348257293134930951

theorem tailTrace_3583791 : CollatzResearch.WordTrace tailWord_3583791 prefixEnd_3583791 1840207348257293134930951 := by
  unfold tailWord_3583791
  simp only [CollatzResearch.WordTrace]
  refine ⟨130711596159544744619103227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87141064106363163079402151 130711596159544744619103227)
  ·
    refine ⟨196067394239317116928654841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130711596159544744619103227 196067394239317116928654841)
    ·
      refine ⟨147050545679487837696491131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196067394239317116928654841 147050545679487837696491131)
      ·
        refine ⟨220575818519231756544736697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147050545679487837696491131 220575818519231756544736697)
        ·
          refine ⟨165431863889423817408552523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220575818519231756544736697 165431863889423817408552523)
          ·
            refine ⟨248147795834135726112828785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165431863889423817408552523 248147795834135726112828785)
            ·
              refine ⟨186110846875601794584621589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248147795834135726112828785 186110846875601794584621589)
              ·
                refine ⟨8723945947293834121154137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186110846875601794584621589 8723945947293834121154137)
                ·
                  refine ⟨6542959460470375590865603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8723945947293834121154137 6542959460470375590865603)
                  ·
                    refine ⟨9814439190705563386298405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6542959460470375590865603 9814439190705563386298405)
                    ·
                      refine ⟨1840207348257293134930951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9814439190705563386298405 1840207348257293134930951)
                      ·
                        rfl

theorem cell23_3583791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_3583791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583791 prefixEnd_3583791 := by exact prefixLift 3583791
  have htrace : WordTrace (prefixWord ++ tailWord_3583791) baseStart_3583791 baseEnd_3583791 := by
    simpa [prefixWord, tailWord_3583791, baseEnd_3583791] using wordTrace_append hprefix tailTrace_3583791
  have hstable : (prefixWord ++ tailWord_3583791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583791).length < 2 ^ (prefixWord ++ tailWord_3583791).sum := by decide
  have hdescent : baseEnd_3583791 < baseStart_3583791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583798 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3583798 : Nat := 118140960795 + 3583798 * 2 ^ 59
def prefixEnd_3583798 : Nat := 4983230072969 + 3 ^ 40 * 3583798 * 2
def baseEnd_3583798 : Nat := 1840210942621874607543419

theorem tailTrace_3583798 : CollatzResearch.WordTrace tailWord_3583798 prefixEnd_3583798 1840210942621874607543419 := by
  unfold tailWord_3583798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8169490716907461550913003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87141234313679589876405365 8169490716907461550913003)
  ·
    refine ⟨12254236075361192326369505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8169490716907461550913003 12254236075361192326369505)
    ·
      refine ⟨9190677056520894244777129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12254236075361192326369505 9190677056520894244777129)
      ·
        refine ⟨6893007792390670683582847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9190677056520894244777129 6893007792390670683582847)
        ·
          refine ⟨10339511688586006025374271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6893007792390670683582847 10339511688586006025374271)
          ·
            refine ⟨15509267532879009038061407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10339511688586006025374271 15509267532879009038061407)
            ·
              refine ⟨23263901299318513557092111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15509267532879009038061407 23263901299318513557092111)
              ·
                refine ⟨34895851948977770335638167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23263901299318513557092111 34895851948977770335638167)
                ·
                  refine ⟨52343777923466655503457251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34895851948977770335638167 52343777923466655503457251)
                  ·
                    refine ⟨78515666885199983255185877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52343777923466655503457251 78515666885199983255185877)
                    ·
                      refine ⟨1840210942621874607543419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78515666885199983255185877 1840210942621874607543419)
                      ·
                        rfl

theorem cell23_3583798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3583798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583798 prefixEnd_3583798 := by exact prefixLift 3583798
  have htrace : WordTrace (prefixWord ++ tailWord_3583798) baseStart_3583798 baseEnd_3583798 := by
    simpa [prefixWord, tailWord_3583798, baseEnd_3583798] using wordTrace_append hprefix tailTrace_3583798
  have hstable : (prefixWord ++ tailWord_3583798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583798).length < 2 ^ (prefixWord ++ tailWord_3583798).sum := by decide
  have hdescent : baseEnd_3583798 < baseStart_3583798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583848 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 6]
def baseStart_3583848 : Nat := 118140960795 + 3583848 * 2 ^ 59
def prefixEnd_3583848 : Nat := 4983230072969 + 3 ^ 40 * 3583848 * 2
def baseEnd_3583848 : Nat := 204470735183844379102021

theorem tailTrace_3583848 : CollatzResearch.WordTrace tailWord_3583848 prefixEnd_3583848 204470735183844379102021 := by
  unfold tailWord_3583848
  simp only [CollatzResearch.WordTrace]
  refine ⟨65356837560169121676964099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87142450080225495569285465 65356837560169121676964099)
  ·
    refine ⟨98035256340253682515446149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65356837560169121676964099 98035256340253682515446149)
    ·
      refine ⟨18381610563797565471646153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98035256340253682515446149 18381610563797565471646153)
      ·
        refine ⟨13786207922848174103734615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18381610563797565471646153 13786207922848174103734615)
        ·
          refine ⟨20679311884272261155601923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13786207922848174103734615 20679311884272261155601923)
          ·
            refine ⟨31018967826408391733402885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20679311884272261155601923 31018967826408391733402885)
            ·
              refine ⟨5816056467451573450013041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31018967826408391733402885 5816056467451573450013041)
              ·
                refine ⟨4362042350588680087509781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5816056467451573450013041 4362042350588680087509781)
                ·
                  refine ⟨204470735183844379102021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4362042350588680087509781 204470735183844379102021)
                  ·
                    rfl

theorem cell23_3583848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 6].length) (baseStart_3583848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583848 prefixEnd_3583848 := by exact prefixLift 3583848
  have htrace : WordTrace (prefixWord ++ tailWord_3583848) baseStart_3583848 baseEnd_3583848 := by
    simpa [prefixWord, tailWord_3583848, baseEnd_3583848] using wordTrace_append hprefix tailTrace_3583848
  have hstable : (prefixWord ++ tailWord_3583848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583848).length < 2 ^ (prefixWord ++ tailWord_3583848).sum := by decide
  have hdescent : baseEnd_3583848 < baseStart_3583848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583852 : List Nat := [2, 2, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_3583852 : Nat := 118140960795 + 3583852 * 2 ^ 59
def prefixEnd_3583852 : Nat := 4983230072969 + 3 ^ 40 * 3583852 * 2
def baseEnd_3583852 : Nat := 613412890192405798756057

theorem tailTrace_3583852 : CollatzResearch.WordTrace tailWord_3583852 prefixEnd_3583852 613412890192405798756057 := by
  unfold tailWord_3583852
  simp only [CollatzResearch.WordTrace]
  refine ⟨65356910506161876018536905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87142547341549168024715873 65356910506161876018536905)
  ·
    refine ⟨49017682879621407013902679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65356910506161876018536905 49017682879621407013902679)
    ·
      refine ⟨73526524319432110520854019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49017682879621407013902679 73526524319432110520854019)
      ·
        refine ⟨110289786479148165781281029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73526524319432110520854019 110289786479148165781281029)
        ·
          refine ⟨20679334964840281083990193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110289786479148165781281029 20679334964840281083990193)
          ·
            refine ⟨15509501223630210812992645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20679334964840281083990193 15509501223630210812992645)
            ·
              refine ⟨2908031479430664527436121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15509501223630210812992645 2908031479430664527436121)
              ·
                refine ⟨2181023609572998395577091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908031479430664527436121 2181023609572998395577091)
                ·
                  refine ⟨3271535414359497593365637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181023609572998395577091 3271535414359497593365637)
                  ·
                    refine ⟨613412890192405798756057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271535414359497593365637 613412890192405798756057)
                    ·
                      rfl

theorem cell23_3583852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_3583852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583852 prefixEnd_3583852 := by exact prefixLift 3583852
  have htrace : WordTrace (prefixWord ++ tailWord_3583852) baseStart_3583852 baseEnd_3583852 := by
    simpa [prefixWord, tailWord_3583852, baseEnd_3583852] using wordTrace_append hprefix tailTrace_3583852
  have hstable : (prefixWord ++ tailWord_3583852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583852).length < 2 ^ (prefixWord ++ tailWord_3583852).sum := by decide
  have hdescent : baseEnd_3583852 < baseStart_3583852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583875 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 3]
def baseStart_3583875 : Nat := 118140960795 + 3583875 * 2 ^ 59
def prefixEnd_3583875 : Nat := 4983230072969 + 3 ^ 40 * 3583875 * 2
def baseEnd_3583875 : Nat := 1840250480632270806280565

theorem tailTrace_3583875 : CollatzResearch.WordTrace tailWord_3583875 prefixEnd_3583875 1840250480632270806280565 := by
  unfold tailWord_3583875
  simp only [CollatzResearch.WordTrace]
  refine ⟨130714659891240426965161079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87143106594160284643440719 130714659891240426965161079)
  ·
    refine ⟨196071989836860640447741619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130714659891240426965161079 196071989836860640447741619)
    ·
      refine ⟨294107984755290960671612429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196071989836860640447741619 294107984755290960671612429)
      ·
        refine ⟨110290494283234110251854661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294107984755290960671612429 110290494283234110251854661)
        ·
          refine ⟨20679467678106395672222749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110290494283234110251854661 20679467678106395672222749)
          ·
            refine ⟨7754800379289898377083531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20679467678106395672222749 7754800379289898377083531)
            ·
              refine ⟨11632200568934847565625297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754800379289898377083531 11632200568934847565625297)
              ·
                refine ⟨8724150426701135674218973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11632200568934847565625297 8724150426701135674218973)
                ·
                  refine ⟨3271556410012925877832115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8724150426701135674218973 3271556410012925877832115)
                  ·
                    refine ⟨4907334615019388816748173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3271556410012925877832115 4907334615019388816748173)
                    ·
                      refine ⟨1840250480632270806280565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4907334615019388816748173 1840250480632270806280565)
                      ·
                        rfl

theorem cell23_3583875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_3583875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583875 prefixEnd_3583875 := by exact prefixLift 3583875
  have htrace : WordTrace (prefixWord ++ tailWord_3583875) baseStart_3583875 baseEnd_3583875 := by
    simpa [prefixWord, tailWord_3583875, baseEnd_3583875] using wordTrace_append hprefix tailTrace_3583875
  have hstable : (prefixWord ++ tailWord_3583875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583875).length < 2 ^ (prefixWord ++ tailWord_3583875).sum := by decide
  have hdescent : baseEnd_3583875 < baseStart_3583875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583895 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 1, 5]
def baseStart_3583895 : Nat := 118140960795 + 3583895 * 2 ^ 59
def prefixEnd_3583895 : Nat := 4983230072969 + 3 ^ 40 * 3583895 * 2
def baseEnd_3583895 : Nat := 613420250081786909343491

theorem tailTrace_3583895 : CollatzResearch.WordTrace tailWord_3583895 prefixEnd_3583895 613420250081786909343491 := by
  unfold tailWord_3583895
  simp only [CollatzResearch.WordTrace]
  refine ⟨130715389351167970380889139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87143592900778646920592759 130715389351167970380889139)
  ·
    refine ⟨196073084026751955571333709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130715389351167970380889139 196073084026751955571333709)
    ·
      refine ⟨73527406510031983339250141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196073084026751955571333709 73527406510031983339250141)
      ·
        refine ⟨27572777441261993752218803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73527406510031983339250141 27572777441261993752218803)
        ·
          refine ⟨41359166161892990628328205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27572777441261993752218803 41359166161892990628328205)
          ·
            refine ⟨15509687310709871485623077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41359166161892990628328205 15509687310709871485623077)
            ·
              refine ⟨2908066370758100903554327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15509687310709871485623077 2908066370758100903554327)
              ·
                refine ⟨4362099556137151355331491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908066370758100903554327 4362099556137151355331491)
                ·
                  refine ⟨6543149334205727032997237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362099556137151355331491 6543149334205727032997237)
                  ·
                    refine ⟨613420250081786909343491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6543149334205727032997237 613420250081786909343491)
                    ·
                      rfl

theorem cell23_3583895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_3583895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583895 prefixEnd_3583895 := by exact prefixLift 3583895
  have htrace : WordTrace (prefixWord ++ tailWord_3583895) baseStart_3583895 baseEnd_3583895 := by
    simpa [prefixWord, tailWord_3583895, baseEnd_3583895] using wordTrace_append hprefix tailTrace_3583895
  have hstable : (prefixWord ++ tailWord_3583895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583895).length < 2 ^ (prefixWord ++ tailWord_3583895).sum := by decide
  have hdescent : baseEnd_3583895 < baseStart_3583895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583925 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3583925 : Nat := 118140960795 + 3583925 * 2 ^ 59
def prefixEnd_3583925 : Nat := 4983230072969 + 3 ^ 40 * 3583925 * 2
def baseEnd_3583925 : Nat := 613425384888331870218445

theorem tailTrace_3583925 : CollatzResearch.WordTrace tailWord_3583925 prefixEnd_3583925 613425384888331870218445 := by
  unfold tailWord_3583925
  simp only [CollatzResearch.WordTrace]
  refine ⟨130716483541059285504481229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87144322360706190336320819 130716483541059285504481229)
  ·
    refine ⟨49018681327897232064180461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130716483541059285504481229 49018681327897232064180461)
    ·
      refine ⟨18382005497961462024067673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49018681327897232064180461 18382005497961462024067673)
      ·
        refine ⟨13786504123471096518050755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18382005497961462024067673 13786504123471096518050755)
        ·
          refine ⟨20679756185206644777076133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13786504123471096518050755 20679756185206644777076133)
          ·
            refine ⟨3877454284726245895701775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20679756185206644777076133 3877454284726245895701775)
            ·
              refine ⟨5816181427089368843552663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877454284726245895701775 5816181427089368843552663)
              ·
                refine ⟨8724272140634053265328995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816181427089368843552663 8724272140634053265328995)
                ·
                  refine ⟨13086408210951079897993493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8724272140634053265328995 13086408210951079897993493)
                  ·
                    refine ⟨613425384888331870218445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13086408210951079897993493 613425384888331870218445)
                    ·
                      rfl

theorem cell23_3583925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3583925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583925 prefixEnd_3583925 := by exact prefixLift 3583925
  have htrace : WordTrace (prefixWord ++ tailWord_3583925) baseStart_3583925 baseEnd_3583925 := by
    simpa [prefixWord, tailWord_3583925, baseEnd_3583925] using wordTrace_append hprefix tailTrace_3583925
  have hstable : (prefixWord ++ tailWord_3583925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583925).length < 2 ^ (prefixWord ++ tailWord_3583925).sum := by decide
  have hdescent : baseEnd_3583925 < baseStart_3583925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583935 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 3]
def baseStart_3583935 : Nat := 118140960795 + 3583935 * 2 ^ 59
def prefixEnd_3583935 : Nat := 4983230072969 + 3 ^ 40 * 3583935 * 2
def baseEnd_3583935 : Nat := 1840281289471540571530289

theorem tailTrace_3583935 : CollatzResearch.WordTrace tailWord_3583935 prefixEnd_3583935 1840281289471540571530289 := by
  unfold tailWord_3583935
  simp only [CollatzResearch.WordTrace]
  refine ⟨130716848271023057212345259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87144565514015371474896839 130716848271023057212345259)
  ·
    refine ⟨196075272406534585818517889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130716848271023057212345259 196075272406534585818517889)
    ·
      refine ⟨147056454304900939363888417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196075272406534585818517889 147056454304900939363888417)
      ·
        refine ⟨110292340728675704522916313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147056454304900939363888417 110292340728675704522916313)
        ·
          refine ⟨82719255546506778392187235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110292340728675704522916313 82719255546506778392187235)
          ·
            refine ⟨124078883319760167588280853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82719255546506778392187235 124078883319760167588280853)
            ·
              refine ⟨5816197655613757855700665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124078883319760167588280853 5816197655613757855700665)
              ·
                refine ⟨4362148241710318391775499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5816197655613757855700665 4362148241710318391775499)
                ·
                  refine ⟨6543222362565477587663249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362148241710318391775499 6543222362565477587663249)
                  ·
                    refine ⟨4907416771924108190747437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6543222362565477587663249 4907416771924108190747437)
                    ·
                      refine ⟨1840281289471540571530289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4907416771924108190747437 1840281289471540571530289)
                      ·
                        rfl

theorem cell23_3583935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_3583935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583935 prefixEnd_3583935 := by exact prefixLift 3583935
  have htrace : WordTrace (prefixWord ++ tailWord_3583935) baseStart_3583935 baseEnd_3583935 := by
    simpa [prefixWord, tailWord_3583935, baseEnd_3583935] using wordTrace_append hprefix tailTrace_3583935
  have hstable : (prefixWord ++ tailWord_3583935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583935).length < 2 ^ (prefixWord ++ tailWord_3583935).sum := by decide
  have hdescent : baseEnd_3583935 < baseStart_3583935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583991 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_3583991 : Nat := 118140960795 + 3583991 * 2 ^ 59
def prefixEnd_3583991 : Nat := 4983230072969 + 3 ^ 40 * 3583991 * 2
def baseEnd_3583991 : Nat := 1840310044388192352430031

theorem tailTrace_3583991 : CollatzResearch.WordTrace tailWord_3583991 prefixEnd_3583991 1840310044388192352430031 := by
  unfold tailWord_3583991
  simp only [CollatzResearch.WordTrace]
  refine ⟨130718890758820178776383827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87145927172546785850922551 130718890758820178776383827)
  ·
    refine ⟨196078336138230268164575741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130718890758820178776383827 196078336138230268164575741)
    ·
      refine ⟨73529376051836350561715903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196078336138230268164575741 73529376051836350561715903)
      ·
        refine ⟨110294064077754525842573855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73529376051836350561715903 110294064077754525842573855)
        ·
          refine ⟨165441096116631788763860783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110294064077754525842573855 165441096116631788763860783)
          ·
            refine ⟨248161644174947683145791175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165441096116631788763860783 248161644174947683145791175)
            ·
              refine ⟨372242466262421524718686763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248161644174947683145791175 372242466262421524718686763)
              ·
                refine ⟨558363699393632287078030145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372242466262421524718686763 558363699393632287078030145)
                ·
                  refine ⟨418772774545224215308522609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558363699393632287078030145 418772774545224215308522609)
                  ·
                    refine ⟨314079580908918161481391957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 418772774545224215308522609 314079580908918161481391957)
                    ·
                      refine ⟨1840310044388192352430031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 314079580908918161481391957 1840310044388192352430031)
                      ·
                        rfl

theorem cell23_3583991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_3583991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583991 prefixEnd_3583991 := by exact prefixLift 3583991
  have htrace : WordTrace (prefixWord ++ tailWord_3583991) baseStart_3583991 baseEnd_3583991 := by
    simpa [prefixWord, tailWord_3583991, baseEnd_3583991] using wordTrace_append hprefix tailTrace_3583991
  have hstable : (prefixWord ++ tailWord_3583991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583991).length < 2 ^ (prefixWord ++ tailWord_3583991).sum := by decide
  have hdescent : baseEnd_3583991 < baseStart_3583991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583992 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 1, 3, 2]
def baseStart_3583992 : Nat := 118140960795 + 3583992 * 2 ^ 59
def prefixEnd_3583992 : Nat := 4983230072969 + 3 ^ 40 * 3583992 * 2
def baseEnd_3583992 : Nat := 1840310557868846848517527

theorem tailTrace_3583992 : CollatzResearch.WordTrace tailWord_3583992 prefixEnd_3583992 1840310557868846848517527 := by
  unfold tailWord_3583992
  simp only [CollatzResearch.WordTrace]
  refine ⟨65359463615908277973585115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87145951487877703964780153 65359463615908277973585115)
  ·
    refine ⟨98039195423862416960377673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65359463615908277973585115 98039195423862416960377673)
    ·
      refine ⟨73529396567896812720283255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98039195423862416960377673 73529396567896812720283255)
      ·
        refine ⟨110294094851845219080424883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73529396567896812720283255 110294094851845219080424883)
        ·
          refine ⟨165441142277767828620637325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110294094851845219080424883 165441142277767828620637325)
          ·
            refine ⟨62040428354162935732738997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165441142277767828620637325 62040428354162935732738997)
            ·
              refine ⟨5816290158202775224944281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62040428354162935732738997 5816290158202775224944281)
              ·
                refine ⟨4362217618652081418708211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5816290158202775224944281 4362217618652081418708211)
                ·
                  refine ⟨6543326427978122128062317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362217618652081418708211 6543326427978122128062317)
                  ·
                    refine ⟨2453747410491795798023369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6543326427978122128062317 2453747410491795798023369)
                    ·
                      refine ⟨1840310557868846848517527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2453747410491795798023369 1840310557868846848517527)
                      ·
                        rfl

theorem cell23_3583992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_3583992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3583992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3583992 prefixEnd_3583992 := by exact prefixLift 3583992
  have htrace : WordTrace (prefixWord ++ tailWord_3583992) baseStart_3583992 baseEnd_3583992 := by
    simpa [prefixWord, tailWord_3583992, baseEnd_3583992] using wordTrace_append hprefix tailTrace_3583992
  have hstable : (prefixWord ++ tailWord_3583992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583992).length < 2 ^ (prefixWord ++ tailWord_3583992).sum := by decide
  have hdescent : baseEnd_3583992 < baseStart_3583992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584005 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 3, 4, 2]
def baseStart_3584005 : Nat := 118140960795 + 3584005 * 2 ^ 59
def prefixEnd_3584005 : Nat := 4983230072969 + 3 ^ 40 * 3584005 * 2
def baseEnd_3584005 : Nat := 1840317233117355297654967

theorem tailTrace_3584005 : CollatzResearch.WordTrace tailWord_3584005 prefixEnd_3584005 1840317233117355297654967 := by
  unfold tailWord_3584005
  simp only [CollatzResearch.WordTrace]
  refine ⟨130719401380769459167393469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87146267587179639444928979 130719401380769459167393469)
  ·
    refine ⟨49019775517788547187772551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130719401380769459167393469 49019775517788547187772551)
    ·
      refine ⟨73529663276682820781658827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49019775517788547187772551 73529663276682820781658827)
      ·
        refine ⟨110294494915024231172488241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73529663276682820781658827 110294494915024231172488241)
        ·
          refine ⟨82720871186268173379366181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110294494915024231172488241 82720871186268173379366181)
          ·
            refine ⟨15510163347425282508631159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82720871186268173379366181 15510163347425282508631159)
            ·
              refine ⟨23265245021137923762946739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15510163347425282508631159 23265245021137923762946739)
              ·
                refine ⟨34897867531706885644420109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23265245021137923762946739 34897867531706885644420109)
                ·
                  refine ⟨13086700324390082116657541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34897867531706885644420109 13086700324390082116657541)
                  ·
                    refine ⟨2453756310823140396873289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13086700324390082116657541 2453756310823140396873289)
                    ·
                      refine ⟨1840317233117355297654967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2453756310823140396873289 1840317233117355297654967)
                      ·
                        rfl

theorem cell23_3584005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_3584005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584005 prefixEnd_3584005 := by exact prefixLift 3584005
  have htrace : WordTrace (prefixWord ++ tailWord_3584005) baseStart_3584005 baseEnd_3584005 := by
    simpa [prefixWord, tailWord_3584005, baseEnd_3584005] using wordTrace_append hprefix tailTrace_3584005
  have hstable : (prefixWord ++ tailWord_3584005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584005).length < 2 ^ (prefixWord ++ tailWord_3584005).sum := by decide
  have hdescent : baseEnd_3584005 < baseStart_3584005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584008 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3584008 : Nat := 118140960795 + 3584008 * 2 ^ 59
def prefixEnd_3584008 : Nat := 4983230072969 + 3 ^ 40 * 3584008 * 2
def baseEnd_3584008 : Nat := 1840318773559318785917453

theorem tailTrace_3584008 : CollatzResearch.WordTrace tailWord_3584008 prefixEnd_3584008 1840318773559318785917453 := by
  unfold tailWord_3584008
  simp only [CollatzResearch.WordTrace]
  refine ⟨65359755399879295339876339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87146340533172393786501785 65359755399879295339876339)
  ·
    refine ⟨98039633099818943009814509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65359755399879295339876339 98039633099818943009814509)
    ·
      refine ⟨36764862412432103628680441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98039633099818943009814509 36764862412432103628680441)
      ·
        refine ⟨27573646809324077721510331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36764862412432103628680441 27573646809324077721510331)
        ·
          refine ⟨41360470213986116582265497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27573646809324077721510331 41360470213986116582265497)
          ·
            refine ⟨31020352660489587436699123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41360470213986116582265497 31020352660489587436699123)
            ·
              refine ⟨46530528990734381155048685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31020352660489587436699123 46530528990734381155048685)
              ·
                refine ⟨17448948371525392933143257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46530528990734381155048685 17448948371525392933143257)
                ·
                  refine ⟨13086711278644044699857443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17448948371525392933143257 13086711278644044699857443)
                  ·
                    refine ⟨19630066917966067049786165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13086711278644044699857443 19630066917966067049786165)
                    ·
                      refine ⟨1840318773559318785917453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19630066917966067049786165 1840318773559318785917453)
                      ·
                        rfl

theorem cell23_3584008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3584008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584008 prefixEnd_3584008 := by exact prefixLift 3584008
  have htrace : WordTrace (prefixWord ++ tailWord_3584008) baseStart_3584008 baseEnd_3584008 := by
    simpa [prefixWord, tailWord_3584008, baseEnd_3584008] using wordTrace_append hprefix tailTrace_3584008
  have hstable : (prefixWord ++ tailWord_3584008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584008).length < 2 ^ (prefixWord ++ tailWord_3584008).sum := by decide
  have hdescent : baseEnd_3584008 < baseStart_3584008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584095 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 1, 6, 2]
def baseStart_3584095 : Nat := 118140960795 + 3584095 * 2 ^ 59
def prefixEnd_3584095 : Nat := 4983230072969 + 3 ^ 40 * 3584095 * 2
def baseEnd_3584095 : Nat := 1840363446376259945529553

theorem tailTrace_3584095 : CollatzResearch.WordTrace tailWord_3584095 prefixEnd_3584095 1840363446376259945529553 := by
  unfold tailWord_3584095
  simp only [CollatzResearch.WordTrace]
  refine ⟨130722683950443404538169739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87148455966962269692113159 130722683950443404538169739)
  ·
    refine ⟨196084025925665106807254609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130722683950443404538169739 196084025925665106807254609)
    ·
      refine ⟨147063019444248830105440957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196084025925665106807254609 147063019444248830105440957)
      ·
        refine ⟨55148632291593311289540359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147063019444248830105440957 55148632291593311289540359)
        ·
          refine ⟨82722948437389966934310539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55148632291593311289540359 82722948437389966934310539)
          ·
            refine ⟨124084422656084950401465809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82722948437389966934310539 124084422656084950401465809)
            ·
              refine ⟨93063316992063712801099357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124084422656084950401465809 93063316992063712801099357)
              ·
                refine ⟨34898743872023892300412259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93063316992063712801099357 34898743872023892300412259)
                ·
                  refine ⟨52348115808035838450618389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34898743872023892300412259 52348115808035838450618389)
                  ·
                    refine ⟨2453817928501679927372737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52348115808035838450618389 2453817928501679927372737)
                    ·
                      refine ⟨1840363446376259945529553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2453817928501679927372737 1840363446376259945529553)
                      ·
                        rfl

theorem cell23_3584095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_3584095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584095 prefixEnd_3584095 := by exact prefixLift 3584095
  have htrace : WordTrace (prefixWord ++ tailWord_3584095) baseStart_3584095 baseEnd_3584095 := by
    simpa [prefixWord, tailWord_3584095, baseEnd_3584095] using wordTrace_append hprefix tailTrace_3584095
  have hstable : (prefixWord ++ tailWord_3584095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584095).length < 2 ^ (prefixWord ++ tailWord_3584095).sum := by decide
  have hdescent : baseEnd_3584095 < baseStart_3584095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584105 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 3, 4]
def baseStart_3584105 : Nat := 118140960795 + 3584105 * 2 ^ 59
def prefixEnd_3584105 : Nat := 4983230072969 + 3 ^ 40 * 3584105 * 2
def baseEnd_3584105 : Nat := 613456193727601635468169

theorem tailTrace_3584105 : CollatzResearch.WordTrace tailWord_3584105 prefixEnd_3584105 613456193727601635468169 := by
  unfold tailWord_3584105
  simp only [CollatzResearch.WordTrace]
  refine ⟨130723048680407176246033769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87148699120271450830689179 130723048680407176246033769)
  ·
    refine ⟨98042286510305382184525327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130723048680407176246033769 98042286510305382184525327)
    ·
      refine ⟨147063429765458073276787991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98042286510305382184525327 147063429765458073276787991)
      ·
        refine ⟨220595144648187109915181987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147063429765458073276787991 220595144648187109915181987)
        ·
          refine ⟨330892716972280664872772981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220595144648187109915181987 330892716972280664872772981)
          ·
            refine ⟨31021192216151312331822467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330892716972280664872772981 31021192216151312331822467)
            ·
              refine ⟨46531788324226968497733701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31021192216151312331822467 46531788324226968497733701)
              ·
                refine ⟨8724710310792556593325069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46531788324226968497733701 8724710310792556593325069)
                ·
                  refine ⟨3271766366547208722496901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8724710310792556593325069 3271766366547208722496901)
                  ·
                    refine ⟨613456193727601635468169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271766366547208722496901 613456193727601635468169)
                    ·
                      rfl

theorem cell23_3584105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_3584105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584105 prefixEnd_3584105 := by exact prefixLift 3584105
  have htrace : WordTrace (prefixWord ++ tailWord_3584105) baseStart_3584105 baseEnd_3584105 := by
    simpa [prefixWord, tailWord_3584105, baseEnd_3584105] using wordTrace_append hprefix tailTrace_3584105
  have hstable : (prefixWord ++ tailWord_3584105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584105).length < 2 ^ (prefixWord ++ tailWord_3584105).sum := by decide
  have hdescent : baseEnd_3584105 < baseStart_3584105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584132 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_3584132 : Nat := 118140960795 + 3584132 * 2 ^ 59
def prefixEnd_3584132 : Nat := 4983230072969 + 3 ^ 40 * 3584132 * 2
def baseEnd_3584132 : Nat := 1840382445160476300766883

theorem tailTrace_3584132 : CollatzResearch.WordTrace tailWord_3584132 prefixEnd_3584132 1840382445160476300766883 := by
  unfold tailWord_3584132
  simp only [CollatzResearch.WordTrace]
  refine ⟨65362016725654679928633325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87149355634206239904844433 65362016725654679928633325)
  ·
    refine ⟨24510756272120504973237497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65362016725654679928633325 24510756272120504973237497)
    ·
      refine ⟨18383067204090378729928123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24510756272120504973237497 18383067204090378729928123)
      ·
        refine ⟨27574600806135568094892185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18383067204090378729928123 27574600806135568094892185)
        ·
          refine ⟨20680950604601676071169139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27574600806135568094892185 20680950604601676071169139)
          ·
            refine ⟨31021425906902514106753709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20680950604601676071169139 31021425906902514106753709)
            ·
              refine ⟨11633034715088442790032641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31021425906902514106753709 11633034715088442790032641)
              ·
                refine ⟨8724776036316332092524481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11633034715088442790032641 8724776036316332092524481)
                ·
                  refine ⟨6543582027237249069393361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8724776036316332092524481 6543582027237249069393361)
                  ·
                    refine ⟨4907686520427936802045021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6543582027237249069393361 4907686520427936802045021)
                    ·
                      refine ⟨1840382445160476300766883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4907686520427936802045021 1840382445160476300766883)
                      ·
                        rfl

theorem cell23_3584132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_3584132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584132 prefixEnd_3584132 := by exact prefixLift 3584132
  have htrace : WordTrace (prefixWord ++ tailWord_3584132) baseStart_3584132 baseEnd_3584132 := by
    simpa [prefixWord, tailWord_3584132, baseEnd_3584132] using wordTrace_append hprefix tailTrace_3584132
  have hstable : (prefixWord ++ tailWord_3584132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584132).length < 2 ^ (prefixWord ++ tailWord_3584132).sum := by decide
  have hdescent : baseEnd_3584132 < baseStart_3584132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584152 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 6]
def baseStart_3584152 : Nat := 118140960795 + 3584152 * 2 ^ 59
def prefixEnd_3584152 : Nat := 4983230072969 + 3 ^ 40 * 3584152 * 2
def baseEnd_3584152 : Nat := 204488079419285135835199

theorem tailTrace_3584152 : CollatzResearch.WordTrace tailWord_3584152 prefixEnd_3584152 204488079419285135835199 := by
  unfold tailWord_3584152
  simp only [CollatzResearch.WordTrace]
  refine ⟨65362381455618451636497355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87149841940824602181996473 65362381455618451636497355)
  ·
    refine ⟨98043572183427677454746033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65362381455618451636497355 98043572183427677454746033)
    ·
      refine ⟨73532679137570758091059525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98043572183427677454746033 73532679137570758091059525)
      ·
        refine ⟨13787377338294517142073661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73532679137570758091059525 13787377338294517142073661)
        ·
          refine ⟨5170266501860443928277623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13787377338294517142073661 5170266501860443928277623)
          ·
            refine ⟨7755399752790665892416435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170266501860443928277623 7755399752790665892416435)
            ·
              refine ⟨11633099629185998838624653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755399752790665892416435 11633099629185998838624653)
              ·
                refine ⟨4362412360944749564484245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11633099629185998838624653 4362412360944749564484245)
                ·
                  refine ⟨204488079419285135835199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4362412360944749564484245 204488079419285135835199)
                  ·
                    rfl

theorem cell23_3584152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 6].length) (baseStart_3584152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584152 prefixEnd_3584152 := by exact prefixLift 3584152
  have htrace : WordTrace (prefixWord ++ tailWord_3584152) baseStart_3584152 baseEnd_3584152 := by
    simpa [prefixWord, tailWord_3584152, baseEnd_3584152] using wordTrace_append hprefix tailTrace_3584152
  have hstable : (prefixWord ++ tailWord_3584152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584152).length < 2 ^ (prefixWord ++ tailWord_3584152).sum := by decide
  have hdescent : baseEnd_3584152 < baseStart_3584152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584165 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_3584165 : Nat := 118140960795 + 3584165 * 2 ^ 59
def prefixEnd_3584165 : Nat := 4983230072969 + 3 ^ 40 * 3584165 * 2
def baseEnd_3584165 : Nat := 613466463340691557218077

theorem tailTrace_3584165 : CollatzResearch.WordTrace tailWord_3584165 prefixEnd_3584165 613466463340691557218077 := by
  unfold tailWord_3584165
  simp only [CollatzResearch.WordTrace]
  refine ⟨130725237060189806493217949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87150158040126537662145299 130725237060189806493217949)
  ·
    refine ⟨49021963897571177434956731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130725237060189806493217949 49021963897571177434956731)
    ·
      refine ⟨73532945846356766152435097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49021963897571177434956731 73532945846356766152435097)
      ·
        refine ⟨55149709384767574614326323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73532945846356766152435097 55149709384767574614326323)
        ·
          refine ⟨82724564077151361921489485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55149709384767574614326323 82724564077151361921489485)
          ·
            refine ⟨31021711528931760720558557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82724564077151361921489485 31021711528931760720558557)
            ·
              refine ⟨11633141823349410270209459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31021711528931760720558557 11633141823349410270209459)
              ·
                refine ⟨17449712735024115405314189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11633141823349410270209459 17449712735024115405314189)
                ·
                  refine ⟨6543642275634043276992821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17449712735024115405314189 6543642275634043276992821)
                  ·
                    refine ⟨613466463340691557218077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6543642275634043276992821 613466463340691557218077)
                    ·
                      rfl

theorem cell23_3584165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_3584165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584165 prefixEnd_3584165 := by exact prefixLift 3584165
  have htrace : WordTrace (prefixWord ++ tailWord_3584165) baseStart_3584165 baseEnd_3584165 := by
    simpa [prefixWord, tailWord_3584165, baseEnd_3584165] using wordTrace_append hprefix tailTrace_3584165
  have hstable : (prefixWord ++ tailWord_3584165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584165).length < 2 ^ (prefixWord ++ tailWord_3584165).sum := by decide
  have hdescent : baseEnd_3584165 < baseStart_3584165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584179 : List Nat := [1, 1, 1, 2, 3, 2, 1, 7, 1, 1, 3]
def baseStart_3584179 : Nat := 118140960795 + 3584179 * 2 ^ 59
def prefixEnd_3584179 : Nat := 4983230072969 + 3 ^ 40 * 3584179 * 2
def baseEnd_3584179 : Nat := 1840406578751237616879167

theorem tailTrace_3584179 : CollatzResearch.WordTrace tailWord_3584179 prefixEnd_3584179 1840406578751237616879167 := by
  unfold tailWord_3584179
  simp only [CollatzResearch.WordTrace]
  refine ⟨130725747682139086884227591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87150498454759391256151727 130725747682139086884227591)
  ·
    refine ⟨196088621523208630326341387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130725747682139086884227591 196088621523208630326341387)
    ·
      refine ⟨294132932284812945489512081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196088621523208630326341387 294132932284812945489512081)
      ·
        refine ⟨220599699213609709117134061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294132932284812945489512081 220599699213609709117134061)
        ·
          refine ⟨82724887205103640918925273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220599699213609709117134061 82724887205103640918925273)
          ·
            refine ⟨62043665403827730689193955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82724887205103640918925273 62043665403827730689193955)
            ·
              refine ⟨93065498105741596033790933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62043665403827730689193955 93065498105741596033790933)
              ·
                refine ⟨2181222611853318657041975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93065498105741596033790933 2181222611853318657041975)
                ·
                  refine ⟨3271833917779977985562963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181222611853318657041975 3271833917779977985562963)
                  ·
                    refine ⟨4907750876669966978344445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3271833917779977985562963 4907750876669966978344445)
                    ·
                      refine ⟨1840406578751237616879167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4907750876669966978344445 1840406578751237616879167)
                      ·
                        rfl

theorem cell23_3584179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 1, 3].length) (baseStart_3584179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584179 prefixEnd_3584179 := by exact prefixLift 3584179
  have htrace : WordTrace (prefixWord ++ tailWord_3584179) baseStart_3584179 baseEnd_3584179 := by
    simpa [prefixWord, tailWord_3584179, baseEnd_3584179] using wordTrace_append hprefix tailTrace_3584179
  have hstable : (prefixWord ++ tailWord_3584179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584179).length < 2 ^ (prefixWord ++ tailWord_3584179).sum := by decide
  have hdescent : baseEnd_3584179 < baseStart_3584179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584190 : List Nat := [4, 2, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_3584190 : Nat := 118140960795 + 3584190 * 2 ^ 59
def prefixEnd_3584190 : Nat := 4983230072969 + 3 ^ 40 * 3584190 * 2
def baseEnd_3584190 : Nat := 613470742346145691280539

theorem tailTrace_3584190 : CollatzResearch.WordTrace tailWord_3584190 prefixEnd_3584190 613470742346145691280539 := by
  unfold tailWord_3584190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16340768610637404470359753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87150765923399490508585349 16340768610637404470359753)
  ·
    refine ⟨12255576457978053352769815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16340768610637404470359753 12255576457978053352769815)
    ·
      refine ⟨18383364686967080029154723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12255576457978053352769815 18383364686967080029154723)
      ·
        refine ⟨27575047030450620043732085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18383364686967080029154723 27575047030450620043732085)
        ·
          refine ⟨2585160659104745629099883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27575047030450620043732085 2585160659104745629099883)
          ·
            refine ⟨3877740988657118443649825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585160659104745629099883 3877740988657118443649825)
            ·
              refine ⟨2908305741492838832737369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877740988657118443649825 2908305741492838832737369)
              ·
                refine ⟨2181229306119629124553027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908305741492838832737369 2181229306119629124553027)
                ·
                  refine ⟨3271843959179443686829541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181229306119629124553027 3271843959179443686829541)
                  ·
                    refine ⟨613470742346145691280539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271843959179443686829541 613470742346145691280539)
                    ·
                      rfl

theorem cell23_3584190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_3584190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584190 prefixEnd_3584190 := by exact prefixLift 3584190
  have htrace : WordTrace (prefixWord ++ tailWord_3584190) baseStart_3584190 baseEnd_3584190 := by
    simpa [prefixWord, tailWord_3584190, baseEnd_3584190] using wordTrace_append hprefix tailTrace_3584190
  have hstable : (prefixWord ++ tailWord_3584190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584190).length < 2 ^ (prefixWord ++ tailWord_3584190).sum := by decide
  have hdescent : baseEnd_3584190 < baseStart_3584190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584195 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 8, 4]
def baseStart_3584195 : Nat := 118140960795 + 3584195 * 2 ^ 59
def prefixEnd_3584195 : Nat := 4983230072969 + 3 ^ 40 * 3584195 * 2
def baseEnd_3584195 : Nat := 613471598147236518093031

theorem tailTrace_3584195 : CollatzResearch.WordTrace tailWord_3584195 prefixEnd_3584195 613471598147236518093031 := by
  unfold tailWord_3584195
  simp only [CollatzResearch.WordTrace]
  refine ⟨130726331250081121616810039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87150887500054081077873359 130726331250081121616810039)
  ·
    refine ⟨196089496875121682425215059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130726331250081121616810039 196089496875121682425215059)
    ·
      refine ⟨294134245312682523637822589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196089496875121682425215059 294134245312682523637822589)
      ·
        refine ⟨110300341992255946364183471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294134245312682523637822589 110300341992255946364183471)
        ·
          refine ⟨165450512988383919546275207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110300341992255946364183471 165450512988383919546275207)
          ·
            refine ⟨248175769482575879319412811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165450512988383919546275207 248175769482575879319412811)
            ·
              refine ⟨372263654223863818979119217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248175769482575879319412811 372263654223863818979119217)
              ·
                refine ⟨279197740667897864234339413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372263654223863818979119217 279197740667897864234339413)
                ·
                  refine ⟨3271848523451928096496165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 279197740667897864234339413 3271848523451928096496165)
                  ·
                    refine ⟨613471598147236518093031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271848523451928096496165 613471598147236518093031)
                    ·
                      rfl

theorem cell23_3584195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 4].length) (baseStart_3584195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584195 prefixEnd_3584195 := by exact prefixLift 3584195
  have htrace : WordTrace (prefixWord ++ tailWord_3584195) baseStart_3584195 baseEnd_3584195 := by
    simpa [prefixWord, tailWord_3584195, baseEnd_3584195] using wordTrace_append hprefix tailTrace_3584195
  have hstable : (prefixWord ++ tailWord_3584195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584195).length < 2 ^ (prefixWord ++ tailWord_3584195).sum := by decide
  have hdescent : baseEnd_3584195 < baseStart_3584195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584232 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3584232 : Nat := 118140960795 + 3584232 * 2 ^ 59
def prefixEnd_3584232 : Nat := 4983230072969 + 3 ^ 40 * 3584232 * 2
def baseEnd_3584232 : Nat := 1840433793225925909516423

theorem tailTrace_3584232 : CollatzResearch.WordTrace tailWord_3584232 prefixEnd_3584232 1840433793225925909516423 := by
  unfold tailWord_3584232
  simp only [CollatzResearch.WordTrace]
  refine ⟨65363840375473538467953475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87151787167298051290604633 65363840375473538467953475)
  ·
    refine ⟨98045760563210307701930213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65363840375473538467953475 98045760563210307701930213)
    ·
      refine ⟨18383580105601932694111915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98045760563210307701930213 18383580105601932694111915)
      ·
        refine ⟨27575370158402899041167873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18383580105601932694111915 27575370158402899041167873)
        ·
          refine ⟨20681527618802174280875905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27575370158402899041167873 20681527618802174280875905)
          ·
            refine ⟨15511145714101630710656929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20681527618802174280875905 15511145714101630710656929)
            ·
              refine ⟨11633359285576223032992697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15511145714101630710656929 11633359285576223032992697)
              ·
                refine ⟨8725019464182167274744523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11633359285576223032992697 8725019464182167274744523)
                ·
                  refine ⟨13087529196273250912116785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725019464182167274744523 13087529196273250912116785)
                  ·
                    refine ⟨9815646897204938184087589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13087529196273250912116785 9815646897204938184087589)
                    ·
                      refine ⟨1840433793225925909516423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9815646897204938184087589 1840433793225925909516423)
                      ·
                        rfl

theorem cell23_3584232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3584232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584232 prefixEnd_3584232 := by exact prefixLift 3584232
  have htrace : WordTrace (prefixWord ++ tailWord_3584232) baseStart_3584232 baseEnd_3584232 := by
    simpa [prefixWord, tailWord_3584232, baseEnd_3584232] using wordTrace_append hprefix tailTrace_3584232
  have hstable : (prefixWord ++ tailWord_3584232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584232).length < 2 ^ (prefixWord ++ tailWord_3584232).sum := by decide
  have hdescent : baseEnd_3584232 < baseStart_3584232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584239 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 3]
def baseStart_3584239 : Nat := 118140960795 + 3584239 * 2 ^ 59
def prefixEnd_3584239 : Nat := 4983230072969 + 3 ^ 40 * 3584239 * 2
def baseEnd_3584239 : Nat := 1840437387590507382128891

theorem tailTrace_3584239 : CollatzResearch.WordTrace tailWord_3584239 prefixEnd_3584239 1840437387590507382128891 := by
  unfold tailWord_3584239
  simp only [CollatzResearch.WordTrace]
  refine ⟨130727936061921717131411771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87151957374614478087607847 130727936061921717131411771)
  ·
    refine ⟨196091904092882575697117657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130727936061921717131411771 196091904092882575697117657)
    ·
      refine ⟨147068928069661931772838243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196091904092882575697117657 147068928069661931772838243)
      ·
        refine ⟨220603392104492897659257365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147068928069661931772838243 220603392104492897659257365)
        ·
          refine ⟨10340784004898104577777689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220603392104492897659257365 10340784004898104577777689)
          ·
            refine ⟨7755588003673578433333267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10340784004898104577777689 7755588003673578433333267)
            ·
              refine ⟨11633382005510367649999901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755588003673578433333267 11633382005510367649999901)
              ·
                refine ⟨4362518252066387868749963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11633382005510367649999901 4362518252066387868749963)
                ·
                  refine ⟨6543777378099581803124945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362518252066387868749963 6543777378099581803124945)
                  ·
                    refine ⟨4907833033574686352343709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6543777378099581803124945 4907833033574686352343709)
                    ·
                      refine ⟨1840437387590507382128891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4907833033574686352343709 1840437387590507382128891)
                      ·
                        rfl

theorem cell23_3584239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_3584239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584239 prefixEnd_3584239 := by exact prefixLift 3584239
  have htrace : WordTrace (prefixWord ++ tailWord_3584239) baseStart_3584239 baseEnd_3584239 := by
    simpa [prefixWord, tailWord_3584239, baseEnd_3584239] using wordTrace_append hprefix tailTrace_3584239
  have hstable : (prefixWord ++ tailWord_3584239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584239).length < 2 ^ (prefixWord ++ tailWord_3584239).sum := by decide
  have hdescent : baseEnd_3584239 < baseStart_3584239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584263 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 2, 4]
def baseStart_3584263 : Nat := 118140960795 + 3584263 * 2 ^ 59
def prefixEnd_3584263 : Nat := 4983230072969 + 3 ^ 40 * 3584263 * 2
def baseEnd_3584263 : Nat := 613483237042071762742927

theorem tailTrace_3584263 : CollatzResearch.WordTrace tailWord_3584263 prefixEnd_3584263 613483237042071762742927 := by
  unfold tailWord_3584263
  simp only [CollatzResearch.WordTrace]
  refine ⟨130728811413834769230285443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87152540942556512820190295 130728811413834769230285443)
  ·
    refine ⟨196093217120752153845428165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130728811413834769230285443 196093217120752153845428165)
    ·
      refine ⟨36767478210141028846017781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196093217120752153845428165 36767478210141028846017781)
      ·
        refine ⟨3446951082200721454314167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36767478210141028846017781 3446951082200721454314167)
        ·
          refine ⟨5170426623301082181471251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446951082200721454314167 5170426623301082181471251)
          ·
            refine ⟨7755639934951623272206877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170426623301082181471251 7755639934951623272206877)
            ·
              refine ⟨2908364975606858727077579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7755639934951623272206877 2908364975606858727077579)
              ·
                refine ⟨4362547463410288090616369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908364975606858727077579 4362547463410288090616369)
                ·
                  refine ⟨3271910597557716067962277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4362547463410288090616369 3271910597557716067962277)
                  ·
                    refine ⟨613483237042071762742927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271910597557716067962277 613483237042071762742927)
                    ·
                      rfl

theorem cell23_3584263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_3584263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584263 prefixEnd_3584263 := by exact prefixLift 3584263
  have htrace : WordTrace (prefixWord ++ tailWord_3584263) baseStart_3584263 baseEnd_3584263 := by
    simpa [prefixWord, tailWord_3584263, baseEnd_3584263] using wordTrace_append hprefix tailTrace_3584263
  have hstable : (prefixWord ++ tailWord_3584263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584263).length < 2 ^ (prefixWord ++ tailWord_3584263).sum := by decide
  have hdescent : baseEnd_3584263 < baseStart_3584263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584275 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4]
def baseStart_3584275 : Nat := 118140960795 + 3584275 * 2 ^ 59
def prefixEnd_3584275 : Nat := 4983230072969 + 3 ^ 40 * 3584275 * 2
def baseEnd_3584275 : Nat := 1840455872894069241278725

theorem tailTrace_3584275 : CollatzResearch.WordTrace tailWord_3584275 prefixEnd_3584275 1840455872894069241278725 := by
  unfold tailWord_3584275
  simp only [CollatzResearch.WordTrace]
  refine ⟨130729249089791295279722279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87152832726527530186481519 130729249089791295279722279)
  ·
    refine ⟨196093873634686942919583419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130729249089791295279722279 196093873634686942919583419)
    ·
      refine ⟨294140810452030414379375129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196093873634686942919583419 294140810452030414379375129)
      ·
        refine ⟨220605607839022810784531347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294140810452030414379375129 220605607839022810784531347)
        ·
          refine ⟨330908411758534216176797021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220605607839022810784531347 330908411758534216176797021)
          ·
            refine ⟨124090654409450331066298883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330908411758534216176797021 124090654409450331066298883)
            ·
              refine ⟨186135981614175496599448325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124090654409450331066298883 186135981614175496599448325)
              ·
                refine ⟨34900496552657905612396561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186135981614175496599448325 34900496552657905612396561)
                ·
                  refine ⟨26175372414493429209297421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34900496552657905612396561 26175372414493429209297421)
                  ·
                    refine ⟨9815764655435035953486533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26175372414493429209297421 9815764655435035953486533)
                    ·
                      refine ⟨1840455872894069241278725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9815764655435035953486533 1840455872894069241278725)
                      ·
                        rfl

theorem cell23_3584275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_3584275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584275 prefixEnd_3584275 := by exact prefixLift 3584275
  have htrace : WordTrace (prefixWord ++ tailWord_3584275) baseStart_3584275 baseEnd_3584275 := by
    simpa [prefixWord, tailWord_3584275, baseEnd_3584275] using wordTrace_append hprefix tailTrace_3584275
  have hstable : (prefixWord ++ tailWord_3584275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584275).length < 2 ^ (prefixWord ++ tailWord_3584275).sum := by decide
  have hdescent : baseEnd_3584275 < baseStart_3584275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584460 : List Nat := [2, 2, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_3584460 : Nat := 118140960795 + 3584460 * 2 ^ 59
def prefixEnd_3584460 : Nat := 4983230072969 + 3 ^ 40 * 3584460 * 2
def baseEnd_3584460 : Nat := 613516955605050339155125

theorem tailTrace_3584460 : CollatzResearch.WordTrace tailWord_3584460 prefixEnd_3584460 613516955605050339155125 := by
  unfold tailWord_3584460
  simp only [CollatzResearch.WordTrace]
  refine ⟨65367998297060535937603417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87157331062747381250137889 65367998297060535937603417)
  ·
    refine ⟨49025998722795401953202563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65367998297060535937603417 49025998722795401953202563)
    ·
      refine ⟨73538998084193102929803845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49025998722795401953202563 73538998084193102929803845)
      ·
        refine ⟨13788562140786206799338221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73538998084193102929803845 13788562140786206799338221)
        ·
          refine ⟨5170710802794827549751833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13788562140786206799338221 5170710802794827549751833)
          ·
            refine ⟨3878033102096120662313875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5170710802794827549751833 3878033102096120662313875)
            ·
              refine ⟨5817049653144180993470813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878033102096120662313875 5817049653144180993470813)
              ·
                refine ⟨2181393619929067872551555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5817049653144180993470813 2181393619929067872551555)
                ·
                  refine ⟨3272090429893601808827333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181393619929067872551555 3272090429893601808827333)
                  ·
                    refine ⟨613516955605050339155125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3272090429893601808827333 613516955605050339155125)
                    ·
                      rfl

theorem cell23_3584460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_3584460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584460 prefixEnd_3584460 := by exact prefixLift 3584460
  have htrace : WordTrace (prefixWord ++ tailWord_3584460) baseStart_3584460 baseEnd_3584460 := by
    simpa [prefixWord, tailWord_3584460, baseEnd_3584460] using wordTrace_append hprefix tailTrace_3584460
  have hstable : (prefixWord ++ tailWord_3584460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584460).length < 2 ^ (prefixWord ++ tailWord_3584460).sum := by decide
  have hdescent : baseEnd_3584460 < baseStart_3584460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584489 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 2, 6, 2]
def baseStart_3584489 : Nat := 118140960795 + 3584489 * 2 ^ 59
def prefixEnd_3584489 : Nat := 4983230072969 + 3 ^ 40 * 3584489 * 2
def baseEnd_3584489 : Nat := 1840565757754131404002741

theorem tailTrace_3584489 : CollatzResearch.WordTrace tailWord_3584489 prefixEnd_3584489 1840565757754131404002741 := by
  unfold tailWord_3584489
  simp only [CollatzResearch.WordTrace]
  refine ⟨130737054311016009828012521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87158036207344006552008347 130737054311016009828012521)
  ·
    refine ⟨98052790733262007371009391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130737054311016009828012521 98052790733262007371009391)
    ·
      refine ⟨147079186099893011056514087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98052790733262007371009391 147079186099893011056514087)
      ·
        refine ⟨220618779149839516584771131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147079186099893011056514087 220618779149839516584771131)
        ·
          refine ⟨330928168724759274877156697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220618779149839516584771131 330928168724759274877156697)
          ·
            refine ⟨248196126543569456157867523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330928168724759274877156697 248196126543569456157867523)
            ·
              refine ⟨372294189815354184236801285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248196126543569456157867523 372294189815354184236801285)
              ·
                refine ⟨69805160590378909544400241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372294189815354184236801285 69805160590378909544400241)
                ·
                  refine ⟨52353870442784182158300181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69805160590378909544400241 52353870442784182158300181)
                  ·
                    refine ⟨2454087677005508538670321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52353870442784182158300181 2454087677005508538670321)
                    ·
                      refine ⟨1840565757754131404002741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2454087677005508538670321 1840565757754131404002741)
                      ·
                        rfl

theorem cell23_3584489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 6, 2].length) (baseStart_3584489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584489 prefixEnd_3584489 := by exact prefixLift 3584489
  have htrace : WordTrace (prefixWord ++ tailWord_3584489) baseStart_3584489 baseEnd_3584489 := by
    simpa [prefixWord, tailWord_3584489, baseEnd_3584489] using wordTrace_append hprefix tailTrace_3584489
  have hstable : (prefixWord ++ tailWord_3584489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584489).length < 2 ^ (prefixWord ++ tailWord_3584489).sum := by decide
  have hdescent : baseEnd_3584489 < baseStart_3584489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584516 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_3584516 : Nat := 118140960795 + 3584516 * 2 ^ 59
def prefixEnd_3584516 : Nat := 4983230072969 + 3 ^ 40 * 3584516 * 2
def baseEnd_3584516 : Nat := 613526540577267599455039

theorem tailTrace_3584516 : CollatzResearch.WordTrace tailWord_3584516 prefixEnd_3584516 613526540577267599455039 := by
  unfold tailWord_3584516
  simp only [CollatzResearch.WordTrace]
  refine ⟨65369019540959096719622701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87158692721278795626163601 65369019540959096719622701)
  ·
    refine ⟨24513382327859661269858513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65369019540959096719622701 24513382327859661269858513)
    ·
      refine ⟨18385036745894745952393885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24513382327859661269858513 18385036745894745952393885)
      ·
        refine ⟨6894388779710529732147707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18385036745894745952393885 6894388779710529732147707)
        ·
          refine ⟨10341583169565794598221561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894388779710529732147707 10341583169565794598221561)
          ·
            refine ⟨7756187377174345948666171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10341583169565794598221561 7756187377174345948666171)
            ·
              refine ⟨11634281065761518922999257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7756187377174345948666171 11634281065761518922999257)
              ·
                refine ⟨8725710799321139192249443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11634281065761518922999257 8725710799321139192249443)
                ·
                  refine ⟨13088566198981708788374165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725710799321139192249443 13088566198981708788374165)
                  ·
                    refine ⟨613526540577267599455039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13088566198981708788374165 613526540577267599455039)
                    ·
                      rfl

theorem cell23_3584516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_3584516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584516 prefixEnd_3584516 := by exact prefixLift 3584516
  have htrace : WordTrace (prefixWord ++ tailWord_3584516) baseStart_3584516 baseEnd_3584516 := by
    simpa [prefixWord, tailWord_3584516, baseEnd_3584516] using wordTrace_append hprefix tailTrace_3584516
  have hstable : (prefixWord ++ tailWord_3584516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584516).length < 2 ^ (prefixWord ++ tailWord_3584516).sum := by decide
  have hdescent : baseEnd_3584516 < baseStart_3584516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584523 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 1, 1, 4]
def baseStart_3584523 : Nat := 118140960795 + 3584523 * 2 ^ 59
def prefixEnd_3584523 : Nat := 4983230072969 + 3 ^ 40 * 3584523 * 2
def baseEnd_3584523 : Nat := 1840583216096384270977585

theorem tailTrace_3584523 : CollatzResearch.WordTrace tailWord_3584523 prefixEnd_3584523 1840583216096384270977585 := by
  unfold tailWord_3584523
  simp only [CollatzResearch.WordTrace]
  refine ⟨130738294392892833634750223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87158862928595222423166815 130738294392892833634750223)
  ·
    refine ⟨196107441589339250452125335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130738294392892833634750223 196107441589339250452125335)
    ·
      refine ⟨294161162384008875678188003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196107441589339250452125335 294161162384008875678188003)
      ·
        refine ⟨441241743576013313517282005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294161162384008875678188003 441241743576013313517282005)
        ·
          refine ⟨10341603365062812035561297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 441241743576013313517282005 10341603365062812035561297)
          ·
            refine ⟨7756202523797109026670973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10341603365062812035561297 7756202523797109026670973)
            ·
              refine ⟨2908575946423915885001615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7756202523797109026670973 2908575946423915885001615)
              ·
                refine ⟨4362863919635873827502423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908575946423915885001615 4362863919635873827502423)
                ·
                  refine ⟨6544295879453810741253635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362863919635873827502423 6544295879453810741253635)
                  ·
                    refine ⟨9816443819180716111880453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6544295879453810741253635 9816443819180716111880453)
                    ·
                      refine ⟨1840583216096384270977585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9816443819180716111880453 1840583216096384270977585)
                      ·
                        rfl

theorem cell23_3584523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 1, 4].length) (baseStart_3584523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584523 prefixEnd_3584523 := by exact prefixLift 3584523
  have htrace : WordTrace (prefixWord ++ tailWord_3584523) baseStart_3584523 baseEnd_3584523 := by
    simpa [prefixWord, tailWord_3584523, baseEnd_3584523] using wordTrace_append hprefix tailTrace_3584523
  have hstable : (prefixWord ++ tailWord_3584523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584523).length < 2 ^ (prefixWord ++ tailWord_3584523).sum := by decide
  have hdescent : baseEnd_3584523 < baseStart_3584523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584526 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3584526 : Nat := 118140960795 + 3584526 * 2 ^ 59
def prefixEnd_3584526 : Nat := 4983230072969 + 3 ^ 40 * 3584526 * 2
def baseEnd_3584526 : Nat := 1840584756538347759240071

theorem tailTrace_3584526 : CollatzResearch.WordTrace tailWord_3584526 prefixEnd_3584526 1840584756538347759240071 := by
  unfold tailWord_3584526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342300476485245643388679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87158935874587976764739621 16342300476485245643388679)
  ·
    refine ⟨24513450714727868465083019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16342300476485245643388679 24513450714727868465083019)
    ·
      refine ⟨36770176072091802697624529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24513450714727868465083019 36770176072091802697624529)
      ·
        refine ⟨27577632054068852023218397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36770176072091802697624529 27577632054068852023218397)
        ·
          refine ⟨10341612020275819508706899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27577632054068852023218397 10341612020275819508706899)
          ·
            refine ⟨15512418030413729263060349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10341612020275819508706899 15512418030413729263060349)
            ·
              refine ⟨5817156761405148473647631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15512418030413729263060349 5817156761405148473647631)
              ·
                refine ⟨8725735142107722710471447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817156761405148473647631 8725735142107722710471447)
                ·
                  refine ⟨13088602713161584065707171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8725735142107722710471447 13088602713161584065707171)
                  ·
                    refine ⟨19632904069742376098560757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13088602713161584065707171 19632904069742376098560757)
                    ·
                      refine ⟨1840584756538347759240071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19632904069742376098560757 1840584756538347759240071)
                      ·
                        rfl

theorem cell23_3584526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3584526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584526 prefixEnd_3584526 := by exact prefixLift 3584526
  have htrace : WordTrace (prefixWord ++ tailWord_3584526) baseStart_3584526 baseEnd_3584526 := by
    simpa [prefixWord, tailWord_3584526, baseEnd_3584526] using wordTrace_append hprefix tailTrace_3584526
  have hstable : (prefixWord ++ tailWord_3584526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584526).length < 2 ^ (prefixWord ++ tailWord_3584526).sum := by decide
  have hdescent : baseEnd_3584526 < baseStart_3584526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584569 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3584569 : Nat := 118140960795 + 3584569 * 2 ^ 59
def prefixEnd_3584569 : Nat := 4983230072969 + 3 ^ 40 * 3584569 * 2
def baseEnd_3584569 : Nat := 1840606836206491091002373

theorem tailTrace_3584569 : CollatzResearch.WordTrace tailWord_3584569 prefixEnd_3584569 1840606836206491091002373 := by
  unfold tailWord_3584569
  simp only [CollatzResearch.WordTrace]
  refine ⟨130739972150726183490924761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87159981433817455660616507 130739972150726183490924761)
  ·
    refine ⟨98054979113044637618193571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130739972150726183490924761 98054979113044637618193571)
    ·
      refine ⟨147082468669566956427290357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98054979113044637618193571 147082468669566956427290357)
      ·
        refine ⟨13788981437771902165058471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147082468669566956427290357 13788981437771902165058471)
        ·
          refine ⟨20683472156657853247587707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13788981437771902165058471 20683472156657853247587707)
          ·
            refine ⟨31025208234986779871381561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20683472156657853247587707 31025208234986779871381561)
            ·
              refine ⟨23268906176240084903536171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31025208234986779871381561 23268906176240084903536171)
              ·
                refine ⟨34903359264360127355304257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23268906176240084903536171 34903359264360127355304257)
                ·
                  refine ⟨26177519448270095516478193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34903359264360127355304257 26177519448270095516478193)
                  ·
                    refine ⟨19633139586202571637358645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26177519448270095516478193 19633139586202571637358645)
                    ·
                      refine ⟨1840606836206491091002373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19633139586202571637358645 1840606836206491091002373)
                      ·
                        rfl

theorem cell23_3584569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3584569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584569 prefixEnd_3584569 := by exact prefixLift 3584569
  have htrace : WordTrace (prefixWord ++ tailWord_3584569) baseStart_3584569 baseEnd_3584569 := by
    simpa [prefixWord, tailWord_3584569, baseEnd_3584569] using wordTrace_append hprefix tailTrace_3584569
  have hstable : (prefixWord ++ tailWord_3584569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584569).length < 2 ^ (prefixWord ++ tailWord_3584569).sum := by decide
  have hdescent : baseEnd_3584569 < baseStart_3584569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584574 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3584574 : Nat := 118140960795 + 3584574 * 2 ^ 59
def prefixEnd_3584574 : Nat := 4983230072969 + 3 ^ 40 * 3584574 * 2
def baseEnd_3584574 : Nat := 1840609403609763571439851

theorem tailTrace_3584574 : CollatzResearch.WordTrace tailWord_3584574 prefixEnd_3584574 1840609403609763571439851 := by
  unfold tailWord_3584574
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342519314463508668107097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87160103010472046229904517 16342519314463508668107097)
  ·
    refine ⟨12256889485847631501080323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16342519314463508668107097 12256889485847631501080323)
    ·
      refine ⟨18385334228771447251620485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12256889485847631501080323 18385334228771447251620485)
      ·
        refine ⟨3447250167894646359678841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18385334228771447251620485 3447250167894646359678841)
        ·
          refine ⟨2585437625920984769759131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3447250167894646359678841 2585437625920984769759131)
          ·
            refine ⟨3878156438881477154638697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585437625920984769759131 3878156438881477154638697)
            ·
              refine ⟨2908617329161107865979023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3878156438881477154638697 2908617329161107865979023)
              ·
                refine ⟨4362925993741661798968535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908617329161107865979023 4362925993741661798968535)
                ·
                  refine ⟨6544388990612492698452803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362925993741661798968535 6544388990612492698452803)
                  ·
                    refine ⟨9816583485918739047679205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6544388990612492698452803 9816583485918739047679205)
                    ·
                      refine ⟨1840609403609763571439851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9816583485918739047679205 1840609403609763571439851)
                      ·
                        rfl

theorem cell23_3584574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3584574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584574 prefixEnd_3584574 := by exact prefixLift 3584574
  have htrace : WordTrace (prefixWord ++ tailWord_3584574) baseStart_3584574 baseEnd_3584574 := by
    simpa [prefixWord, tailWord_3584574, baseEnd_3584574] using wordTrace_append hprefix tailTrace_3584574
  have hstable : (prefixWord ++ tailWord_3584574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584574).length < 2 ^ (prefixWord ++ tailWord_3584574).sum := by decide
  have hdescent : baseEnd_3584574 < baseStart_3584574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584659 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5]
def baseStart_3584659 : Nat := 118140960795 + 3584659 * 2 ^ 59
def prefixEnd_3584659 : Nat := 4983230072969 + 3 ^ 40 * 3584659 * 2
def baseEnd_3584659 : Nat := 1840653049465395738876959

theorem tailTrace_3584659 : CollatzResearch.WordTrace tailWord_3584659 prefixEnd_3584659 1840653049465395738876959 := by
  unfold tailWord_3584659
  simp only [CollatzResearch.WordTrace]
  refine ⟨130743254720400128861701031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87162169813600085907800687 130743254720400128861701031)
  ·
    refine ⟨196114882080600193292551547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130743254720400128861701031 196114882080600193292551547)
    ·
      refine ⟨294172323120900289938827321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196114882080600193292551547 294172323120900289938827321)
      ·
        refine ⟨220629242340675217454120491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294172323120900289938827321 220629242340675217454120491)
        ·
          refine ⟨330943863511012826181180737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220629242340675217454120491 330943863511012826181180737)
          ·
            refine ⟨248207897633259619635885553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330943863511012826181180737 248207897633259619635885553)
            ·
              refine ⟨186155923224944714726914165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248207897633259619635885553 186155923224944714726914165)
              ·
                refine ⟨17452117802338567005648203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186155923224944714726914165 17452117802338567005648203)
                ·
                  refine ⟨26178176703507850508472305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17452117802338567005648203 26178176703507850508472305)
                  ·
                    refine ⟨19633632527630887881354229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26178176703507850508472305 19633632527630887881354229)
                    ·
                      refine ⟨1840653049465395738876959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19633632527630887881354229 1840653049465395738876959)
                      ·
                        rfl

theorem cell23_3584659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_3584659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584659 prefixEnd_3584659 := by exact prefixLift 3584659
  have htrace : WordTrace (prefixWord ++ tailWord_3584659) baseStart_3584659 baseEnd_3584659 := by
    simpa [prefixWord, tailWord_3584659, baseEnd_3584659] using wordTrace_append hprefix tailTrace_3584659
  have hstable : (prefixWord ++ tailWord_3584659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584659).length < 2 ^ (prefixWord ++ tailWord_3584659).sum := by decide
  have hdescent : baseEnd_3584659 < baseStart_3584659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584740 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_3584740 : Nat := 118140960795 + 3584740 * 2 ^ 59
def prefixEnd_3584740 : Nat := 4983230072969 + 3 ^ 40 * 3584740 * 2
def baseEnd_3584740 : Nat := 1840694641398409921964087

theorem tailTrace_3584740 : CollatzResearch.WordTrace tailWord_3584740 prefixEnd_3584740 1840694641398409921964087 := by
  unfold tailWord_3584740
  simp only [CollatzResearch.WordTrace]
  refine ⟨65373104516553339847699837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87164139355404453130266449 65373104516553339847699837)
  ·
    refine ⟨24514914193707502442887439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65373104516553339847699837 24514914193707502442887439)
    ·
      refine ⟨36772371290561253664331159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24514914193707502442887439 36772371290561253664331159)
      ·
        refine ⟨55158556935841880496496739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36772371290561253664331159 55158556935841880496496739)
        ·
          refine ⟨82737835403762820744745109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55158556935841880496496739 82737835403762820744745109)
          ·
            refine ⟨3878336034551382222409927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82737835403762820744745109 3878336034551382222409927)
            ·
              refine ⟨5817504051827073333614891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878336034551382222409927 5817504051827073333614891)
              ·
                refine ⟨8726256077740610000422337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817504051827073333614891 8726256077740610000422337)
                ·
                  refine ⟨6544692058305457500316753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8726256077740610000422337 6544692058305457500316753)
                  ·
                    refine ⟨4908519043729093125237565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6544692058305457500316753 4908519043729093125237565)
                    ·
                      refine ⟨1840694641398409921964087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4908519043729093125237565 1840694641398409921964087)
                      ·
                        rfl

theorem cell23_3584740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_3584740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584740 prefixEnd_3584740 := by exact prefixLift 3584740
  have htrace : WordTrace (prefixWord ++ tailWord_3584740) baseStart_3584740 baseEnd_3584740 := by
    simpa [prefixWord, tailWord_3584740, baseEnd_3584740] using wordTrace_append hprefix tailTrace_3584740
  have hstable : (prefixWord ++ tailWord_3584740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584740).length < 2 ^ (prefixWord ++ tailWord_3584740).sum := by decide
  have hdescent : baseEnd_3584740 < baseStart_3584740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584753 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_3584753 : Nat := 118140960795 + 3584753 * 2 ^ 59
def prefixEnd_3584753 : Nat := 4983230072969 + 3 ^ 40 * 3584753 * 2
def baseEnd_3584753 : Nat := 1840701316646918371101527

theorem tailTrace_3584753 : CollatzResearch.WordTrace tailWord_3584753 prefixEnd_3584753 1840701316646918371101527 := by
  unfold tailWord_3584753
  simp only [CollatzResearch.WordTrace]
  refine ⟨130746683182059582915622913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87164455454706388610415275 130746683182059582915622913)
  ·
    refine ⟨98060012386544687186717185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130746683182059582915622913 98060012386544687186717185)
    ·
      refine ⟨73545009289908515390037889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98060012386544687186717185 73545009289908515390037889)
      ·
        refine ⟨55158756967431386542528417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73545009289908515390037889 55158756967431386542528417)
        ·
          refine ⟨41369067725573539906896313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55158756967431386542528417 41369067725573539906896313)
          ·
            refine ⟨31026800794180154930172235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41369067725573539906896313 31026800794180154930172235)
            ·
              refine ⟨46540201191270232395258353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31026800794180154930172235 46540201191270232395258353)
              ·
                refine ⟨34905150893452674296443765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46540201191270232395258353 34905150893452674296443765)
                ·
                  refine ⟨3272357896261188215291603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34905150893452674296443765 3272357896261188215291603)
                  ·
                    refine ⟨4908536844391782322937405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3272357896261188215291603 4908536844391782322937405)
                    ·
                      refine ⟨1840701316646918371101527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4908536844391782322937405 1840701316646918371101527)
                      ·
                        rfl

theorem cell23_3584753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_3584753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584753 prefixEnd_3584753 := by exact prefixLift 3584753
  have htrace : WordTrace (prefixWord ++ tailWord_3584753) baseStart_3584753 baseEnd_3584753 := by
    simpa [prefixWord, tailWord_3584753, baseEnd_3584753] using wordTrace_append hprefix tailTrace_3584753
  have hstable : (prefixWord ++ tailWord_3584753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584753).length < 2 ^ (prefixWord ++ tailWord_3584753).sum := by decide
  have hdescent : baseEnd_3584753 < baseStart_3584753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584856 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3584856 : Nat := 118140960795 + 3584856 * 2 ^ 59
def prefixEnd_3584856 : Nat := 4983230072969 + 3 ^ 40 * 3584856 * 2
def baseEnd_3584856 : Nat := 1840754205154331468113553

theorem tailTrace_3584856 : CollatzResearch.WordTrace tailWord_3584856 prefixEnd_3584856 1840754205154331468113553 := by
  unfold tailWord_3584856
  simp only [CollatzResearch.WordTrace]
  refine ⟨65375219950343215753311211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87166959933790954337748281 65375219950343215753311211)
  ·
    refine ⟨98062829925514823629966817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65375219950343215753311211 98062829925514823629966817)
    ·
      refine ⟨73547122444136117722475113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98062829925514823629966817 73547122444136117722475113)
      ·
        refine ⟨55160341833102088291856335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73547122444136117722475113 55160341833102088291856335)
        ·
          refine ⟨82740512749653132437784503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55160341833102088291856335 82740512749653132437784503)
          ·
            refine ⟨124110769124479698656676755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82740512749653132437784503 124110769124479698656676755)
            ·
              refine ⟨186166153686719547985015133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124110769124479698656676755 186166153686719547985015133)
              ·
                refine ⟨69812307632519830494380675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186166153686719547985015133 69812307632519830494380675)
                ·
                  refine ⟨104718461448779745741571013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69812307632519830494380675 104718461448779745741571013)
                  ·
                    refine ⟨19634711521646202326544565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104718461448779745741571013 19634711521646202326544565)
                    ·
                      refine ⟨1840754205154331468113553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19634711521646202326544565 1840754205154331468113553)
                      ·
                        rfl

theorem cell23_3584856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3584856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584856 prefixEnd_3584856 := by exact prefixLift 3584856
  have htrace : WordTrace (prefixWord ++ tailWord_3584856) baseStart_3584856 baseEnd_3584856 := by
    simpa [prefixWord, tailWord_3584856, baseEnd_3584856] using wordTrace_append hprefix tailTrace_3584856
  have hstable : (prefixWord ++ tailWord_3584856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584856).length < 2 ^ (prefixWord ++ tailWord_3584856).sum := by decide
  have hdescent : baseEnd_3584856 < baseStart_3584856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584860 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3584860 : Nat := 118140960795 + 3584860 * 2 ^ 59
def prefixEnd_3584860 : Nat := 4983230072969 + 3 ^ 40 * 3584860 * 2
def baseEnd_3584860 : Nat := 1840756259076949452463535

theorem tailTrace_3584860 : CollatzResearch.WordTrace tailWord_3584860 prefixEnd_3584860 1840756259076949452463535 := by
  unfold tailWord_3584860
  simp only [CollatzResearch.WordTrace]
  refine ⟨65375292896335970094884017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87167057195114626793178689 65375292896335970094884017)
  ·
    refine ⟨49031469672251977571163013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65375292896335970094884017 49031469672251977571163013)
    ·
      refine ⟨9193400563547245794593065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49031469672251977571163013 9193400563547245794593065)
      ·
        refine ⟨6895050422660434345944799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9193400563547245794593065 6895050422660434345944799)
        ·
          refine ⟨10342575633990651518917199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895050422660434345944799 10342575633990651518917199)
          ·
            refine ⟨15513863450985977278375799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342575633990651518917199 15513863450985977278375799)
            ·
              refine ⟨23270795176478965917563699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513863450985977278375799 23270795176478965917563699)
              ·
                refine ⟨34906192764718448876345549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23270795176478965917563699 34906192764718448876345549)
                ·
                  refine ⟨13089822286769418328629581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34906192764718448876345549 13089822286769418328629581)
                  ·
                    refine ⟨4908683357538531873236093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13089822286769418328629581 4908683357538531873236093)
                    ·
                      refine ⟨1840756259076949452463535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4908683357538531873236093 1840756259076949452463535)
                      ·
                        rfl

theorem cell23_3584860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3584860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584860 prefixEnd_3584860 := by exact prefixLift 3584860
  have htrace : WordTrace (prefixWord ++ tailWord_3584860) baseStart_3584860 baseEnd_3584860 := by
    simpa [prefixWord, tailWord_3584860, baseEnd_3584860] using wordTrace_append hprefix tailTrace_3584860
  have hstable : (prefixWord ++ tailWord_3584860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584860).length < 2 ^ (prefixWord ++ tailWord_3584860).sum := by decide
  have hdescent : baseEnd_3584860 < baseStart_3584860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584894 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3584894 : Nat := 118140960795 + 3584894 * 2 ^ 59
def prefixEnd_3584894 : Nat := 4983230072969 + 3 ^ 40 * 3584894 * 2
def baseEnd_3584894 : Nat := 1840773717419202319438379

theorem tailTrace_3584894 : CollatzResearch.WordTrace tailWord_3584894 prefixEnd_3584894 1840773717419202319438379 := by
  unfold tailWord_3584894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16343978234318595499563217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87167883916365842664337157 16343978234318595499563217)
  ·
    refine ⟨12257983675738946624672413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16343978234318595499563217 12257983675738946624672413)
    ·
      refine ⟨4596743878402104984252155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12257983675738946624672413 4596743878402104984252155)
      ·
        refine ⟨6895115817603157476378233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596743878402104984252155 6895115817603157476378233)
        ·
          refine ⟨5171336863202368107283675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6895115817603157476378233 5171336863202368107283675)
          ·
            refine ⟨7757005294803552160925513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171336863202368107283675 7757005294803552160925513)
            ·
              refine ⟨5817753971102664120694135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7757005294803552160925513 5817753971102664120694135)
              ·
                refine ⟨8726630956653996181041203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817753971102664120694135 8726630956653996181041203)
                ·
                  refine ⟨13089946434980994271561805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8726630956653996181041203 13089946434980994271561805)
                  ·
                    refine ⟨4908729913117872851835677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13089946434980994271561805 4908729913117872851835677)
                    ·
                      refine ⟨1840773717419202319438379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4908729913117872851835677 1840773717419202319438379)
                      ·
                        rfl

theorem cell23_3584894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3584894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584894 prefixEnd_3584894 := by exact prefixLift 3584894
  have htrace : WordTrace (prefixWord ++ tailWord_3584894) baseStart_3584894 baseEnd_3584894 := by
    simpa [prefixWord, tailWord_3584894, baseEnd_3584894] using wordTrace_append hprefix tailTrace_3584894
  have hstable : (prefixWord ++ tailWord_3584894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584894).length < 2 ^ (prefixWord ++ tailWord_3584894).sum := by decide
  have hdescent : baseEnd_3584894 < baseStart_3584894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584930 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3584930 : Nat := 118140960795 + 3584930 * 2 ^ 59
def prefixEnd_3584930 : Nat := 4983230072969 + 3 ^ 40 * 3584930 * 2
def baseEnd_3584930 : Nat := 1840792202722764178588213

theorem tailTrace_3584930 : CollatzResearch.WordTrace tailWord_3584930 prefixEnd_3584930 1840792202722764178588213 := by
  unfold tailWord_3584930
  simp only [CollatzResearch.WordTrace]
  refine ⟨32688284725604585536204061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87168759268278894763210829 32688284725604585536204061)
  ·
    refine ⟨12258106772101719576076523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32688284725604585536204061 12258106772101719576076523)
    ·
      refine ⟨18387160158152579364114785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12258106772101719576076523 18387160158152579364114785)
      ·
        refine ⟨13790370118614434523086089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18387160158152579364114785 13790370118614434523086089)
        ·
          refine ⟨10342777588960825892314567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13790370118614434523086089 10342777588960825892314567)
          ·
            refine ⟨15514166383441238838471851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342777588960825892314567 15514166383441238838471851)
            ·
              refine ⟨23271249575161858257707777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15514166383441238838471851 23271249575161858257707777)
              ·
                refine ⟨17453437181371393693280833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23271249575161858257707777 17453437181371393693280833)
                ·
                  refine ⟨13090077886028545269960625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17453437181371393693280833 13090077886028545269960625)
                  ·
                    refine ⟨9817558414521408952470469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13090077886028545269960625 9817558414521408952470469)
                    ·
                      refine ⟨1840792202722764178588213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9817558414521408952470469 1840792202722764178588213)
                      ·
                        rfl

theorem cell23_3584930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3584930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584930 prefixEnd_3584930 := by exact prefixLift 3584930
  have htrace : WordTrace (prefixWord ++ tailWord_3584930) baseStart_3584930 baseEnd_3584930 := by
    simpa [prefixWord, tailWord_3584930, baseEnd_3584930] using wordTrace_append hprefix tailTrace_3584930
  have hstable : (prefixWord ++ tailWord_3584930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584930).length < 2 ^ (prefixWord ++ tailWord_3584930).sum := by decide
  have hdescent : baseEnd_3584930 < baseStart_3584930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584953 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 1, 7]
def baseStart_3584953 : Nat := 118140960795 + 3584953 * 2 ^ 59
def prefixEnd_3584953 : Nat := 4983230072969 + 3 ^ 40 * 3584953 * 2
def baseEnd_3584953 : Nat := 613601337592605862866869

theorem tailTrace_3584953 : CollatzResearch.WordTrace tailWord_3584953 prefixEnd_3584953 613601337592605862866869 := by
  unfold tailWord_3584953
  simp only [CollatzResearch.WordTrace]
  refine ⟨130753977781335017072903513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87169318520890011381935675 130753977781335017072903513)
  ·
    refine ⟨98065483336001262804677635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130753977781335017072903513 98065483336001262804677635)
    ·
      refine ⟨147098225004001894207016453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98065483336001262804677635 147098225004001894207016453)
      ·
        refine ⟨27580917188250355163815585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147098225004001894207016453 27580917188250355163815585)
        ·
          refine ⟨20685687891187766372861689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27580917188250355163815585 20685687891187766372861689)
          ·
            refine ⟨15514265918390824779646267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20685687891187766372861689 15514265918390824779646267)
            ·
              refine ⟨23271398877586237169469401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15514265918390824779646267 23271398877586237169469401)
              ·
                refine ⟨17453549158189677877102051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23271398877586237169469401 17453549158189677877102051)
                ·
                  refine ⟨26180323737284516815653077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17453549158189677877102051 26180323737284516815653077)
                  ·
                    refine ⟨613601337592605862866869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26180323737284516815653077 613601337592605862866869)
                    ·
                      rfl

theorem cell23_3584953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_3584953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584953 prefixEnd_3584953 := by exact prefixLift 3584953
  have htrace : WordTrace (prefixWord ++ tailWord_3584953) baseStart_3584953 baseEnd_3584953 := by
    simpa [prefixWord, tailWord_3584953, baseEnd_3584953] using wordTrace_append hprefix tailTrace_3584953
  have hstable : (prefixWord ++ tailWord_3584953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584953).length < 2 ^ (prefixWord ++ tailWord_3584953).sum := by decide
  have hdescent : baseEnd_3584953 < baseStart_3584953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584997 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3584997 : Nat := 118140960795 + 3584997 * 2 ^ 59
def prefixEnd_3584997 : Nat := 4983230072969 + 3 ^ 40 * 3584997 * 2
def baseEnd_3584997 : Nat := 1840826605926615416450405

theorem tailTrace_3584997 : CollatzResearch.WordTrace tailWord_3584997 prefixEnd_3584997 1840826605926615416450405 := by
  unfold tailWord_3584997
  simp only [CollatzResearch.WordTrace]
  refine ⟨130755582593175612587505245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87170388395450408391670163 130755582593175612587505245)
  ·
    refine ⟨49033343472440854720314467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130755582593175612587505245 49033343472440854720314467)
    ·
      refine ⟨73550015208661282080471701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49033343472440854720314467 73550015208661282080471701)
      ·
        refine ⟨3447656962905997597522111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73550015208661282080471701 3447656962905997597522111)
        ·
          refine ⟨5171485444358996396283167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3447656962905997597522111 5171485444358996396283167)
          ·
            refine ⟨7757228166538494594424751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171485444358996396283167 7757228166538494594424751)
            ·
              refine ⟨11635842249807741891637127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7757228166538494594424751 11635842249807741891637127)
              ·
                refine ⟨17453763374711612837455691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635842249807741891637127 17453763374711612837455691)
                ·
                  refine ⟨26180645062067419256183537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17453763374711612837455691 26180645062067419256183537)
                  ·
                    refine ⟨19635483796550564442137653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26180645062067419256183537 19635483796550564442137653)
                    ·
                      refine ⟨1840826605926615416450405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19635483796550564442137653 1840826605926615416450405)
                      ·
                        rfl

theorem cell23_3584997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3584997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3584997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3584997 prefixEnd_3584997 := by exact prefixLift 3584997
  have htrace : WordTrace (prefixWord ++ tailWord_3584997) baseStart_3584997 baseEnd_3584997 := by
    simpa [prefixWord, tailWord_3584997, baseEnd_3584997] using wordTrace_append hprefix tailTrace_3584997
  have hstable : (prefixWord ++ tailWord_3584997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584997).length < 2 ^ (prefixWord ++ tailWord_3584997).sum := by decide
  have hdescent : baseEnd_3584997 < baseStart_3584997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585047 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 6]
def baseStart_3585047 : Nat := 118140960795 + 3585047 * 2 ^ 59
def prefixEnd_3585047 : Nat := 4983230072969 + 3 ^ 40 * 3585047 * 2
def baseEnd_3585047 : Nat := 204539142217704468980575

theorem tailTrace_3585047 : CollatzResearch.WordTrace tailWord_3585047 prefixEnd_3585047 204539142217704468980575 := by
  unfold tailWord_3585047
  simp only [CollatzResearch.WordTrace]
  refine ⟨130757406242994471126825395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87171604161996314084550263 130757406242994471126825395)
  ·
    refine ⟨196136109364491706690238093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130757406242994471126825395 196136109364491706690238093)
    ·
      refine ⟨73551041011684390008839285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196136109364491706690238093 73551041011684390008839285)
      ·
        refine ⟨6895410094845411563328683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73551041011684390008839285 6895410094845411563328683)
        ·
          refine ⟨10343115142268117344993025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895410094845411563328683 10343115142268117344993025)
          ·
            refine ⟨7757336356701088008744769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10343115142268117344993025 7757336356701088008744769)
            ·
              refine ⟨5818002267525816006558577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7757336356701088008744769 5818002267525816006558577)
              ·
                refine ⟨4363501700644362004918933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818002267525816006558577 4363501700644362004918933)
                ·
                  refine ⟨204539142217704468980575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4363501700644362004918933 204539142217704468980575)
                  ·
                    rfl

theorem cell23_3585047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 6].length) (baseStart_3585047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585047 prefixEnd_3585047 := by exact prefixLift 3585047
  have htrace : WordTrace (prefixWord ++ tailWord_3585047) baseStart_3585047 baseEnd_3585047 := by
    simpa [prefixWord, tailWord_3585047, baseEnd_3585047] using wordTrace_append hprefix tailTrace_3585047
  have hstable : (prefixWord ++ tailWord_3585047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585047).length < 2 ^ (prefixWord ++ tailWord_3585047).sum := by decide
  have hdescent : baseEnd_3585047 < baseStart_3585047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585070 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3585070 : Nat := 118140960795 + 3585070 * 2 ^ 59
def prefixEnd_3585070 : Nat := 4983230072969 + 3 ^ 40 * 3585070 * 2
def baseEnd_3585070 : Nat := 1840864090014393630837569

theorem tailTrace_3585070 : CollatzResearch.WordTrace tailWord_3585070 prefixEnd_3585070 1840864090014393630837569 := by
  unfold tailWord_3585070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16344780640238893256864083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87172163414607430703275109 16344780640238893256864083)
  ·
    refine ⟨24517170960358339885296125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16344780640238893256864083 24517170960358339885296125)
    ·
      refine ⟨9193939110134377456986047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24517170960358339885296125 9193939110134377456986047)
      ·
        refine ⟨13790908665201566185479071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9193939110134377456986047 13790908665201566185479071)
        ·
          refine ⟨20686362997802349278218607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13790908665201566185479071 20686362997802349278218607)
          ·
            refine ⟨31029544496703523917327911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20686362997802349278218607 31029544496703523917327911)
            ·
              refine ⟨46544316745055285875991867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31029544496703523917327911 46544316745055285875991867)
              ·
                refine ⟨69816475117582928813987801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46544316745055285875991867 69816475117582928813987801)
                ·
                  refine ⟨52362356338187196610490851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69816475117582928813987801 52362356338187196610490851)
                  ·
                    refine ⟨78543534507280794915736277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52362356338187196610490851 78543534507280794915736277)
                    ·
                      refine ⟨1840864090014393630837569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78543534507280794915736277 1840864090014393630837569)
                      ·
                        rfl

theorem cell23_3585070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3585070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585070 prefixEnd_3585070 := by exact prefixLift 3585070
  have htrace : WordTrace (prefixWord ++ tailWord_3585070) baseStart_3585070 baseEnd_3585070 := by
    simpa [prefixWord, tailWord_3585070, baseEnd_3585070] using wordTrace_append hprefix tailTrace_3585070
  have hstable : (prefixWord ++ tailWord_3585070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585070).length < 2 ^ (prefixWord ++ tailWord_3585070).sum := by decide
  have hdescent : baseEnd_3585070 < baseStart_3585070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585083 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5]
def baseStart_3585083 : Nat := 118140960795 + 3585083 * 2 ^ 59
def prefixEnd_3585083 : Nat := 4983230072969 + 3 ^ 40 * 3585083 * 2
def baseEnd_3585083 : Nat := 1840870765262902079975009

theorem tailTrace_3585083 : CollatzResearch.WordTrace tailWord_3585083 prefixEnd_3585083 1840870765262902079975009 := by
  unfold tailWord_3585083
  simp only [CollatzResearch.WordTrace]
  refine ⟨130758719270864049275135903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87172479513909366183423935 130758719270864049275135903)
  ·
    refine ⟨196138078906296073912703855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130758719270864049275135903 196138078906296073912703855)
    ·
      refine ⟨294207118359444110869055783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196138078906296073912703855 294207118359444110869055783)
      ·
        refine ⟨441310677539166166303583675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294207118359444110869055783 441310677539166166303583675)
        ·
          refine ⟨661966016308749249455375513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441310677539166166303583675 661966016308749249455375513)
          ·
            refine ⟨496474512231561937091531635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661966016308749249455375513 496474512231561937091531635)
            ·
              refine ⟨744711768347342905637297453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496474512231561937091531635 744711768347342905637297453)
              ·
                refine ⟨279266913130253589613986545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 744711768347342905637297453 279266913130253589613986545)
                ·
                  refine ⟨209450184847690192210489909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279266913130253589613986545 209450184847690192210489909)
                  ·
                    refine ⟨19635954829470955519733429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209450184847690192210489909 19635954829470955519733429)
                    ·
                      refine ⟨1840870765262902079975009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19635954829470955519733429 1840870765262902079975009)
                      ·
                        rfl

theorem cell23_3585083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_3585083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585083 prefixEnd_3585083 := by exact prefixLift 3585083
  have htrace : WordTrace (prefixWord ++ tailWord_3585083) baseStart_3585083 baseEnd_3585083 := by
    simpa [prefixWord, tailWord_3585083, baseEnd_3585083] using wordTrace_append hprefix tailTrace_3585083
  have hstable : (prefixWord ++ tailWord_3585083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585083).length < 2 ^ (prefixWord ++ tailWord_3585083).sum := by decide
  have hdescent : baseEnd_3585083 < baseStart_3585083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585084 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_3585084 : Nat := 118140960795 + 3585084 * 2 ^ 59
def prefixEnd_3585084 : Nat := 4983230072969 + 3 ^ 40 * 3585084 * 2
def baseEnd_3585084 : Nat := 1840871278743556576062505

theorem tailTrace_3585084 : CollatzResearch.WordTrace tailWord_3585084 prefixEnd_3585084 1840871278743556576062505 := by
  unfold tailWord_3585084
  simp only [CollatzResearch.WordTrace]
  refine ⟨65379377871930213222961153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87172503829240284297281537 65379377871930213222961153)
  ·
    refine ⟨49034533403947659917220865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65379377871930213222961153 49034533403947659917220865)
    ·
      refine ⟨36775900052960744937915649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49034533403947659917220865 36775900052960744937915649)
      ·
        refine ⟨27581925039720558703436737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36775900052960744937915649 27581925039720558703436737)
        ·
          refine ⟨20686443779790419027577553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27581925039720558703436737 20686443779790419027577553)
          ·
            refine ⟨15514832834842814270683165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20686443779790419027577553 15514832834842814270683165)
            ·
              refine ⟨5818062313066055351506187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15514832834842814270683165 5818062313066055351506187)
              ·
                refine ⟨8727093469599083027259281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818062313066055351506187 8727093469599083027259281)
                ·
                  refine ⟨6545320102199312270444461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8727093469599083027259281 6545320102199312270444461)
                  ·
                    refine ⟨2454495038324742101416673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6545320102199312270444461 2454495038324742101416673)
                    ·
                      refine ⟨1840871278743556576062505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2454495038324742101416673 1840871278743556576062505)
                      ·
                        rfl

theorem cell23_3585084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_3585084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585084 prefixEnd_3585084 := by exact prefixLift 3585084
  have htrace : WordTrace (prefixWord ++ tailWord_3585084) baseStart_3585084 baseEnd_3585084 := by
    simpa [prefixWord, tailWord_3585084, baseEnd_3585084] using wordTrace_append hprefix tailTrace_3585084
  have hstable : (prefixWord ++ tailWord_3585084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585084).length < 2 ^ (prefixWord ++ tailWord_3585084).sum := by decide
  have hdescent : baseEnd_3585084 < baseStart_3585084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585100 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3585100 : Nat := 118140960795 + 3585100 * 2 ^ 59
def prefixEnd_3585100 : Nat := 4983230072969 + 3 ^ 40 * 3585100 * 2
def baseEnd_3585100 : Nat := 1840879494434028513462431

theorem tailTrace_3585100 : CollatzResearch.WordTrace tailWord_3585100 prefixEnd_3585100 1840879494434028513462431 := by
  unfold tailWord_3585100
  simp only [CollatzResearch.WordTrace]
  refine ⟨65379669655901230589252377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87172892874534974119003169 65379669655901230589252377)
  ·
    refine ⟨49034752241925922941939283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65379669655901230589252377 49034752241925922941939283)
    ·
      refine ⟨73552128362888884412908925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49034752241925922941939283 73552128362888884412908925)
      ·
        refine ⟨27582048136083331654840847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73552128362888884412908925 27582048136083331654840847)
        ·
          refine ⟨41373072204124997482261271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27582048136083331654840847 41373072204124997482261271)
          ·
            refine ⟨62059608306187496223391907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41373072204124997482261271 62059608306187496223391907)
            ·
              refine ⟨93089412459281244335087861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62059608306187496223391907 93089412459281244335087861)
              ·
                refine ⟨8727132418057616656414487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93089412459281244335087861 8727132418057616656414487)
                ·
                  refine ⟨13090698627086424984621731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727132418057616656414487 13090698627086424984621731)
                  ·
                    refine ⟨19636047940629637476932597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13090698627086424984621731 19636047940629637476932597)
                    ·
                      refine ⟨1840879494434028513462431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19636047940629637476932597 1840879494434028513462431)
                      ·
                        rfl

theorem cell23_3585100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3585100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585100 prefixEnd_3585100 := by exact prefixLift 3585100
  have htrace : WordTrace (prefixWord ++ tailWord_3585100) baseStart_3585100 baseEnd_3585100 := by
    simpa [prefixWord, tailWord_3585100, baseEnd_3585100] using wordTrace_append hprefix tailTrace_3585100
  have hstable : (prefixWord ++ tailWord_3585100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585100).length < 2 ^ (prefixWord ++ tailWord_3585100).sum := by decide
  have hdescent : baseEnd_3585100 < baseStart_3585100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585127 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_3585127 : Nat := 118140960795 + 3585127 * 2 ^ 59
def prefixEnd_3585127 : Nat := 4983230072969 + 3 ^ 40 * 3585127 * 2
def baseEnd_3585127 : Nat := 1840893358411699907824807

theorem tailTrace_3585127 : CollatzResearch.WordTrace tailWord_3585127 prefixEnd_3585127 1840893358411699907824807 := by
  unfold tailWord_3585127
  simp only [CollatzResearch.WordTrace]
  refine ⟨130760324082704644789737635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87173549388469763193158423 130760324082704644789737635)
  ·
    refine ⟨196140486124056967184606453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130760324082704644789737635 196140486124056967184606453)
    ·
      refine ⟨18388170574130340673556855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196140486124056967184606453 18388170574130340673556855)
      ·
        refine ⟨27582255861195511010335283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18388170574130340673556855 27582255861195511010335283)
        ·
          refine ⟨41373383791793266515502925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27582255861195511010335283 41373383791793266515502925)
          ·
            refine ⟨15515018921922474943313597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41373383791793266515502925 15515018921922474943313597)
            ·
              refine ⟨5818132095720928103742599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15515018921922474943313597 5818132095720928103742599)
              ·
                refine ⟨8727198143581392155613899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818132095720928103742599 8727198143581392155613899)
                ·
                  refine ⟨13090797215372088233420849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727198143581392155613899 13090797215372088233420849)
                  ·
                    refine ⟨9818097911529066175065637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13090797215372088233420849 9818097911529066175065637)
                    ·
                      refine ⟨1840893358411699907824807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9818097911529066175065637 1840893358411699907824807)
                      ·
                        rfl

theorem cell23_3585127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_3585127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585127 prefixEnd_3585127 := by exact prefixLift 3585127
  have htrace : WordTrace (prefixWord ++ tailWord_3585127) baseStart_3585127 baseEnd_3585127 := by
    simpa [prefixWord, tailWord_3585127, baseEnd_3585127] using wordTrace_append hprefix tailTrace_3585127
  have hstable : (prefixWord ++ tailWord_3585127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585127).length < 2 ^ (prefixWord ++ tailWord_3585127).sum := by decide
  have hdescent : baseEnd_3585127 < baseStart_3585127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585134 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3585134 : Nat := 118140960795 + 3585134 * 2 ^ 59
def prefixEnd_3585134 : Nat := 4983230072969 + 3 ^ 40 * 3585134 * 2
def baseEnd_3585134 : Nat := 1840896952776281380437275

theorem tailTrace_3585134 : CollatzResearch.WordTrace tailWord_3585134 prefixEnd_3585134 1840896952776281380437275 := by
  unfold tailWord_3585134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16345072424209910623155307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87173719595786189990161637 16345072424209910623155307)
  ·
    refine ⟨24517608636314865934732961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16345072424209910623155307 24517608636314865934732961)
    ·
      refine ⟨18388206477236149451049721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24517608636314865934732961 18388206477236149451049721)
      ·
        refine ⟨13791154857927112088287291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18388206477236149451049721 13791154857927112088287291)
        ·
          refine ⟨20686732286890668132430937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13791154857927112088287291 20686732286890668132430937)
          ·
            refine ⟨15515049215168001099323203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20686732286890668132430937 15515049215168001099323203)
            ·
              refine ⟨23272573822752001648984805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15515049215168001099323203 23272573822752001648984805)
              ·
                refine ⟨4363607591766000309184651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23272573822752001648984805 4363607591766000309184651)
                ·
                  refine ⟨6545411387649000463776977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363607591766000309184651 6545411387649000463776977)
                  ·
                    refine ⟨4909058540736750347832733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6545411387649000463776977 4909058540736750347832733)
                    ·
                      refine ⟨1840896952776281380437275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4909058540736750347832733 1840896952776281380437275)
                      ·
                        rfl

theorem cell23_3585134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3585134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585134 prefixEnd_3585134 := by exact prefixLift 3585134
  have htrace : WordTrace (prefixWord ++ tailWord_3585134) baseStart_3585134 baseEnd_3585134 := by
    simpa [prefixWord, tailWord_3585134, baseEnd_3585134] using wordTrace_append hprefix tailTrace_3585134
  have hstable : (prefixWord ++ tailWord_3585134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585134).length < 2 ^ (prefixWord ++ tailWord_3585134).sum := by decide
  have hdescent : baseEnd_3585134 < baseStart_3585134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585187 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 5, 4, 2]
def baseStart_3585187 : Nat := 118140960795 + 3585187 * 2 ^ 59
def prefixEnd_3585187 : Nat := 4983230072969 + 3 ^ 40 * 3585187 * 2
def baseEnd_3585187 : Nat := 1840924167250969673074531

theorem tailTrace_3585187 : CollatzResearch.WordTrace tailWord_3585187 prefixEnd_3585187 1840924167250969673074531 := by
  unfold tailWord_3585187
  simp only [CollatzResearch.WordTrace]
  refine ⟨130762512462487275036921815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87175008308324850024614543 130762512462487275036921815)
  ·
    refine ⟨196143768693730912555382723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130762512462487275036921815 196143768693730912555382723)
    ·
      refine ⟨294215653040596368833074085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196143768693730912555382723 294215653040596368833074085)
      ·
        refine ⟨55165434945111819156201391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294215653040596368833074085 55165434945111819156201391)
        ·
          refine ⟨82748152417667728734302087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55165434945111819156201391 82748152417667728734302087)
          ·
            refine ⟨124122228626501593101453131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82748152417667728734302087 124122228626501593101453131)
            ·
              refine ⟨186183342939752389652179697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124122228626501593101453131 186183342939752389652179697)
              ·
                refine ⟨139637507204814292239134773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186183342939752389652179697 139637507204814292239134773)
                ·
                  refine ⟨13091016300451339897418885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139637507204814292239134773 13091016300451339897418885)
                  ·
                    refine ⟨2454565556334626230766041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13091016300451339897418885 2454565556334626230766041)
                    ·
                      refine ⟨1840924167250969673074531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2454565556334626230766041 1840924167250969673074531)
                      ·
                        rfl

theorem cell23_3585187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_3585187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585187 prefixEnd_3585187 := by exact prefixLift 3585187
  have htrace : WordTrace (prefixWord ++ tailWord_3585187) baseStart_3585187 baseEnd_3585187 := by
    simpa [prefixWord, tailWord_3585187, baseEnd_3585187] using wordTrace_append hprefix tailTrace_3585187
  have hstable : (prefixWord ++ tailWord_3585187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585187).length < 2 ^ (prefixWord ++ tailWord_3585187).sum := by decide
  have hdescent : baseEnd_3585187 < baseStart_3585187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585191 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3585191 : Nat := 118140960795 + 3585191 * 2 ^ 59
def prefixEnd_3585191 : Nat := 4983230072969 + 3 ^ 40 * 3585191 * 2
def baseEnd_3585191 : Nat := 1840926221173587657424513

theorem tailTrace_3585191 : CollatzResearch.WordTrace tailWord_3585191 prefixEnd_3585191 1840926221173587657424513 := by
  unfold tailWord_3585191
  simp only [CollatzResearch.WordTrace]
  refine ⟨130762658354472783720067427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87175105569648522480044951 130762658354472783720067427)
  ·
    refine ⟨196143987531709175580101141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130762658354472783720067427 196143987531709175580101141)
    ·
      refine ⟨9194249415548867605317241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196143987531709175580101141 9194249415548867605317241)
      ·
        refine ⟨6895687061661650703987931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9194249415548867605317241 6895687061661650703987931)
        ·
          refine ⟨10343530592492476055981897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895687061661650703987931 10343530592492476055981897)
          ·
            refine ⟨7757647944369357041986423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10343530592492476055981897 7757647944369357041986423)
            ·
              refine ⟨11636471916554035562979635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7757647944369357041986423 11636471916554035562979635)
              ·
                refine ⟨17454707874831053344469453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11636471916554035562979635 17454707874831053344469453)
                ·
                  refine ⟨6545515453061645004176045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17454707874831053344469453 6545515453061645004176045)
                  ·
                    refine ⟨2454568294898116876566017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6545515453061645004176045 2454568294898116876566017)
                    ·
                      refine ⟨1840926221173587657424513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2454568294898116876566017 1840926221173587657424513)
                      ·
                        rfl

theorem cell23_3585191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3585191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585191 prefixEnd_3585191 := by exact prefixLift 3585191
  have htrace : WordTrace (prefixWord ++ tailWord_3585191) baseStart_3585191 baseEnd_3585191 := by
    simpa [prefixWord, tailWord_3585191, baseEnd_3585191] using wordTrace_append hprefix tailTrace_3585191
  have hstable : (prefixWord ++ tailWord_3585191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585191).length < 2 ^ (prefixWord ++ tailWord_3585191).sum := by decide
  have hdescent : baseEnd_3585191 < baseStart_3585191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585200 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_3585200 : Nat := 118140960795 + 3585200 * 2 ^ 59
def prefixEnd_3585200 : Nat := 4983230072969 + 3 ^ 40 * 3585200 * 2
def baseEnd_3585200 : Nat := 1840930842499478122211971

theorem tailTrace_3585200 : CollatzResearch.WordTrace tailWord_3585200 prefixEnd_3585200 1840930842499478122211971 := by
  unfold tailWord_3585200
  simp only [CollatzResearch.WordTrace]
  refine ⟨65381493305720089128572527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87175324407626785504763369 65381493305720089128572527)
  ·
    refine ⟨98072239958580133692858791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65381493305720089128572527 98072239958580133692858791)
    ·
      refine ⟨147108359937870200539288187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98072239958580133692858791 147108359937870200539288187)
      ·
        refine ⟨220662539906805300808932281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147108359937870200539288187 220662539906805300808932281)
        ·
          refine ⟨165496904930103975606699211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220662539906805300808932281 165496904930103975606699211)
          ·
            refine ⟨248245357395155963410048817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165496904930103975606699211 248245357395155963410048817)
            ·
              refine ⟨186184018046366972557536613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248245357395155963410048817 186184018046366972557536613)
              ·
                refine ⟨34909503383693807354538115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186184018046366972557536613 34909503383693807354538115)
                ·
                  refine ⟨52364255075540711031807173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34909503383693807354538115 52364255075540711031807173)
                  ·
                    refine ⟨9818297826663883318463845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52364255075540711031807173 9818297826663883318463845)
                    ·
                      refine ⟨1840930842499478122211971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9818297826663883318463845 1840930842499478122211971)
                      ·
                        rfl

theorem cell23_3585200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_3585200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585200 prefixEnd_3585200 := by exact prefixLift 3585200
  have htrace : WordTrace (prefixWord ++ tailWord_3585200) baseStart_3585200 baseEnd_3585200 := by
    simpa [prefixWord, tailWord_3585200, baseEnd_3585200] using wordTrace_append hprefix tailTrace_3585200
  have hstable : (prefixWord ++ tailWord_3585200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585200).length < 2 ^ (prefixWord ++ tailWord_3585200).sum := by decide
  have hdescent : baseEnd_3585200 < baseStart_3585200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585261 : List Nat := [1, 5, 1, 2, 2, 2, 2, 3, 5]
def baseStart_3585261 : Nat := 118140960795 + 3585261 * 2 ^ 59
def prefixEnd_3585261 : Nat := 4983230072969 + 3 ^ 40 * 3585261 * 2
def baseEnd_3585261 : Nat := 204551351646600264838799

theorem tailTrace_3585261 : CollatzResearch.WordTrace tailWord_3585261 prefixEnd_3585261 204551351646600264838799 := by
  unfold tailWord_3585261
  simp only [CollatzResearch.WordTrace]
  refine ⟨130765211464219185675115637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87176807642812790450077091 130765211464219185675115637)
  ·
    refine ⟨12259238574770548657042091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130765211464219185675115637 12259238574770548657042091)
    ·
      refine ⟨18388857862155822985563137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12259238574770548657042091 18388857862155822985563137)
      ·
        refine ⟨13791643396616867239172353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18388857862155822985563137 13791643396616867239172353)
        ·
          refine ⟨10343732547462650429379265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13791643396616867239172353 10343732547462650429379265)
          ·
            refine ⟨7757799410596987822034449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10343732547462650429379265 7757799410596987822034449)
            ·
              refine ⟨5818349557947740866525837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7757799410596987822034449 5818349557947740866525837)
              ·
                refine ⟨2181881084230402824947189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5818349557947740866525837 2181881084230402824947189)
                ·
                  refine ⟨204551351646600264838799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2181881084230402824947189 204551351646600264838799)
                  ·
                    rfl

theorem cell23_3585261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_3585261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585261 prefixEnd_3585261 := by exact prefixLift 3585261
  have htrace : WordTrace (prefixWord ++ tailWord_3585261) baseStart_3585261 baseEnd_3585261 := by
    simpa [prefixWord, tailWord_3585261, baseEnd_3585261] using wordTrace_append hprefix tailTrace_3585261
  have hstable : (prefixWord ++ tailWord_3585261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585261).length < 2 ^ (prefixWord ++ tailWord_3585261).sum := by decide
  have hdescent : baseEnd_3585261 < baseStart_3585261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585297 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_3585297 : Nat := 118140960795 + 3585297 * 2 ^ 59
def prefixEnd_3585297 : Nat := 4983230072969 + 3 ^ 40 * 3585297 * 2
def baseEnd_3585297 : Nat := 1840980650122964242699025

theorem tailTrace_3585297 : CollatzResearch.WordTrace tailWord_3585297 prefixEnd_3585297 1840980650122964242699025 := by
  unfold tailWord_3585297
  simp only [CollatzResearch.WordTrace]
  refine ⟨130766524492088763823426145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87177682994725842548950763 130766524492088763823426145)
  ·
    refine ⟨98074893369066572867569609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130766524492088763823426145 98074893369066572867569609)
    ·
      refine ⟨73556170026799929650677207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98074893369066572867569609 73556170026799929650677207)
      ·
        refine ⟨110334255040199894476015811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73556170026799929650677207 110334255040199894476015811)
        ·
          refine ⟨165501382560299841714023717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110334255040199894476015811 165501382560299841714023717)
          ·
            refine ⟨31031509230056220321379447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165501382560299841714023717 31031509230056220321379447)
            ·
              refine ⟨46547263845084330482069171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31031509230056220321379447 46547263845084330482069171)
              ·
                refine ⟨69820895767626495723103757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46547263845084330482069171 69820895767626495723103757)
                ·
                  refine ⟨26182835912859935896163909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69820895767626495723103757 26182835912859935896163909)
                  ·
                    refine ⟨4909281733661237980530733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26182835912859935896163909 4909281733661237980530733)
                    ·
                      refine ⟨1840980650122964242699025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4909281733661237980530733 1840980650122964242699025)
                      ·
                        rfl

theorem cell23_3585297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_3585297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585297 prefixEnd_3585297 := by exact prefixLift 3585297
  have htrace : WordTrace (prefixWord ++ tailWord_3585297) baseStart_3585297 baseEnd_3585297 := by
    simpa [prefixWord, tailWord_3585297, baseEnd_3585297] using wordTrace_append hprefix tailTrace_3585297
  have hstable : (prefixWord ++ tailWord_3585297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585297).length < 2 ^ (prefixWord ++ tailWord_3585297).sum := by decide
  have hdescent : baseEnd_3585297 < baseStart_3585297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585304 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 3, 4]
def baseStart_3585304 : Nat := 118140960795 + 3585304 * 2 ^ 59
def prefixEnd_3585304 : Nat := 4983230072969 + 3 ^ 40 * 3585304 * 2
def baseEnd_3585304 : Nat := 613661414829181905103831

theorem tailTrace_3585304 : CollatzResearch.WordTrace tailWord_3585304 prefixEnd_3585304 613661414829181905103831 := by
  unfold tailWord_3585304
  simp only [CollatzResearch.WordTrace]
  refine ⟨65383389901531702009465483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87177853202042269345953977 65383389901531702009465483)
  ·
    refine ⟨98075084852297553014198225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65383389901531702009465483 98075084852297553014198225)
    ·
      refine ⟨73556313639223164760648669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98075084852297553014198225 73556313639223164760648669)
      ·
        refine ⟨27583617614708686785243251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73556313639223164760648669 27583617614708686785243251)
        ·
          refine ⟨41375426422063030177864877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27583617614708686785243251 41375426422063030177864877)
          ·
            refine ⟨15515784908273636316699329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41375426422063030177864877 15515784908273636316699329)
            ·
              refine ⟨11636838681205227237524497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15515784908273636316699329 11636838681205227237524497)
              ·
                refine ⟨8727629010903920428143373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11636838681205227237524497 8727629010903920428143373)
                ·
                  refine ⟨3272860879088970160553765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8727629010903920428143373 3272860879088970160553765)
                  ·
                    refine ⟨613661414829181905103831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3272860879088970160553765 613661414829181905103831)
                    ·
                      rfl

theorem cell23_3585304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_3585304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585304 prefixEnd_3585304 := by exact prefixLift 3585304
  have htrace : WordTrace (prefixWord ++ tailWord_3585304) baseStart_3585304 baseEnd_3585304 := by
    simpa [prefixWord, tailWord_3585304, baseEnd_3585304] using wordTrace_append hprefix tailTrace_3585304
  have hstable : (prefixWord ++ tailWord_3585304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585304).length < 2 ^ (prefixWord ++ tailWord_3585304).sum := by decide
  have hdescent : baseEnd_3585304 < baseStart_3585304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585317 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 8]
def baseStart_3585317 : Nat := 118140960795 + 3585317 * 2 ^ 59
def prefixEnd_3585317 : Nat := 4983230072969 + 3 ^ 40 * 3585317 * 2
def baseEnd_3585317 : Nat := 204554546637339351605437

theorem tailTrace_3585317 : CollatzResearch.WordTrace tailWord_3585317 prefixEnd_3585317 204554546637339351605437 := by
  unfold tailWord_3585317
  simp only [CollatzResearch.WordTrace]
  refine ⟨130767253952016307239154205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87178169301344204826102803 130767253952016307239154205)
  ·
    refine ⟨49037720232006115214682827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130767253952016307239154205 49037720232006115214682827)
    ·
      refine ⟨73556580348009172822024241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49037720232006115214682827 73556580348009172822024241)
      ·
        refine ⟨55167435261006879616518181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73556580348009172822024241 55167435261006879616518181)
        ·
          refine ⟨10343894111438789928097159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55167435261006879616518181 10343894111438789928097159)
          ·
            refine ⟨15515841167158184892145739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10343894111438789928097159 15515841167158184892145739)
            ·
              refine ⟨23273761750737277338218609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15515841167158184892145739 23273761750737277338218609)
              ·
                refine ⟨17455321313052958003663957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23273761750737277338218609 17455321313052958003663957)
                ·
                  refine ⟨204554546637339351605437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17455321313052958003663957 204554546637339351605437)
                  ·
                    rfl

theorem cell23_3585317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_3585317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585317 prefixEnd_3585317 := by exact prefixLift 3585317
  have htrace : WordTrace (prefixWord ++ tailWord_3585317) baseStart_3585317 baseEnd_3585317 := by
    simpa [prefixWord, tailWord_3585317, baseEnd_3585317] using wordTrace_append hprefix tailTrace_3585317
  have hstable : (prefixWord ++ tailWord_3585317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585317).length < 2 ^ (prefixWord ++ tailWord_3585317).sum := by decide
  have hdescent : baseEnd_3585317 < baseStart_3585317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585338 : List Nat := [3, 1, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_3585338 : Nat := 118140960795 + 3585338 * 2 ^ 59
def prefixEnd_3585338 : Nat := 4983230072969 + 3 ^ 40 * 3585338 * 2
def baseEnd_3585338 : Nat := 613667234276599527428779

theorem tailTrace_3585338 : CollatzResearch.WordTrace tailWord_3585338 prefixEnd_3585338 613667234276599527428779 := by
  unfold tailWord_3585338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32692004971235056956417167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87178679923293485217112445 32692004971235056956417167)
  ·
    refine ⟨49038007456852585434625751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32692004971235056956417167 49038007456852585434625751)
    ·
      refine ⟨73557011185278878151938627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49038007456852585434625751 73557011185278878151938627)
      ·
        refine ⟨110335516777918317227907941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73557011185278878151938627 110335516777918317227907941)
        ·
          refine ⟨20687909395859684480232739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110335516777918317227907941 20687909395859684480232739)
          ·
            refine ⟨31031864093789526720349109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20687909395859684480232739 31031864093789526720349109)
            ·
              refine ⟨2909237258792768130032729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31031864093789526720349109 2909237258792768130032729)
              ·
                refine ⟨2181927944094576097524547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909237258792768130032729 2181927944094576097524547)
                ·
                  refine ⟨3272891916141864146286821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181927944094576097524547 3272891916141864146286821)
                  ·
                    refine ⟨613667234276599527428779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3272891916141864146286821 613667234276599527428779)
                    ·
                      rfl

theorem cell23_3585338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_3585338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585338 prefixEnd_3585338 := by exact prefixLift 3585338
  have htrace : WordTrace (prefixWord ++ tailWord_3585338) baseStart_3585338 baseEnd_3585338 := by
    simpa [prefixWord, tailWord_3585338, baseEnd_3585338] using wordTrace_append hprefix tailTrace_3585338
  have hstable : (prefixWord ++ tailWord_3585338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585338).length < 2 ^ (prefixWord ++ tailWord_3585338).sum := by decide
  have hdescent : baseEnd_3585338 < baseStart_3585338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585347 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 3, 5]
def baseStart_3585347 : Nat := 118140960795 + 3585347 * 2 ^ 59
def prefixEnd_3585347 : Nat := 4983230072969 + 3 ^ 40 * 3585347 * 2
def baseEnd_3585347 : Nat := 613668774718563015691265

theorem tailTrace_3585347 : CollatzResearch.WordTrace tailWord_3585347 prefixEnd_3585347 613668774718563015691265 := by
  unfold tailWord_3585347
  simp only [CollatzResearch.WordTrace]
  refine ⟨130768348141907622362746295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87178898761271748241830863 130768348141907622362746295)
  ·
    refine ⟨196152522212861433544119443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130768348141907622362746295 196152522212861433544119443)
    ·
      refine ⟨294228783319292150316179165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196152522212861433544119443 294228783319292150316179165)
      ·
        refine ⟨110335793744734556368567187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294228783319292150316179165 110335793744734556368567187)
        ·
          refine ⟨165503690617101834552850781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110335793744734556368567187 165503690617101834552850781)
          ·
            refine ⟨62063883981413187957319043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165503690617101834552850781 62063883981413187957319043)
            ·
              refine ⟨93095825972119781935978565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62063883981413187957319043 93095825972119781935978565)
              ·
                refine ⟨17455467369772459112995981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93095825972119781935978565 17455467369772459112995981)
                ·
                  refine ⟨6545800263664672167373493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17455467369772459112995981 6545800263664672167373493)
                  ·
                    refine ⟨613668774718563015691265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6545800263664672167373493 613668774718563015691265)
                    ·
                      rfl

theorem cell23_3585347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 5].length) (baseStart_3585347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585347 prefixEnd_3585347 := by exact prefixLift 3585347
  have htrace : WordTrace (prefixWord ++ tailWord_3585347) baseStart_3585347 baseEnd_3585347 := by
    simpa [prefixWord, tailWord_3585347, baseEnd_3585347] using wordTrace_append hprefix tailTrace_3585347
  have hstable : (prefixWord ++ tailWord_3585347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585347).length < 2 ^ (prefixWord ++ tailWord_3585347).sum := by decide
  have hdescent : baseEnd_3585347 < baseStart_3585347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585351 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 6]
def baseStart_3585351 : Nat := 118140960795 + 3585351 * 2 ^ 59
def prefixEnd_3585351 : Nat := 4983230072969 + 3 ^ 40 * 3585351 * 2
def baseEnd_3585351 : Nat := 204556486453145225713753

theorem tailTrace_3585351 : CollatzResearch.WordTrace tailWord_3585351 prefixEnd_3585351 204556486453145225713753 := by
  unfold tailWord_3585351
  simp only [CollatzResearch.WordTrace]
  refine ⟨130768494033893131045891907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87178996022595420697261271 130768494033893131045891907)
  ·
    refine ⟨196152741050839696568837861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130768494033893131045891907 196152741050839696568837861)
    ·
      refine ⟨36778638947032443106657099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196152741050839696568837861 36778638947032443106657099)
      ·
        refine ⟨55167958420548664659985649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36778638947032443106657099 55167958420548664659985649)
        ·
          refine ⟨41375968815411498494989237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55167958420548664659985649 41375968815411498494989237)
          ·
            refine ⟨3878997076444827983905241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41375968815411498494989237 3878997076444827983905241)
            ·
              refine ⟨2909247807333620987928931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3878997076444827983905241 2909247807333620987928931)
              ·
                refine ⟨4363871711000431481893397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909247807333620987928931 4363871711000431481893397)
                ·
                  refine ⟨204556486453145225713753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4363871711000431481893397 204556486453145225713753)
                  ·
                    rfl

theorem cell23_3585351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 6].length) (baseStart_3585351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585351 prefixEnd_3585351 := by exact prefixLift 3585351
  have htrace : WordTrace (prefixWord ++ tailWord_3585351) baseStart_3585351 baseEnd_3585351 := by
    simpa [prefixWord, tailWord_3585351, baseEnd_3585351] using wordTrace_append hprefix tailTrace_3585351
  have hstable : (prefixWord ++ tailWord_3585351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585351).length < 2 ^ (prefixWord ++ tailWord_3585351).sum := by decide
  have hdescent : baseEnd_3585351 < baseStart_3585351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585354 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_3585354 : Nat := 118140960795 + 3585354 * 2 ^ 59
def prefixEnd_3585354 : Nat := 4983230072969 + 3 ^ 40 * 3585354 * 2
def baseEnd_3585354 : Nat := 1841009918520270519686263

theorem tailTrace_3585354 : CollatzResearch.WordTrace tailWord_3585354 prefixEnd_3585354 1841009918520270519686263 := by
  unfold tailWord_3585354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32692150863220565639562779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87179068968588175038834077 32692150863220565639562779)
  ·
    refine ⟨49038226294830848459344169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32692150863220565639562779 49038226294830848459344169)
    ·
      refine ⟨36778669721123136344508127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49038226294830848459344169 36778669721123136344508127)
      ·
        refine ⟨55168004581684704516762191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36778669721123136344508127 55168004581684704516762191)
        ·
          refine ⟨82752006872527056775143287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55168004581684704516762191 82752006872527056775143287)
          ·
            refine ⟨124128010308790585162714931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82752006872527056775143287 124128010308790585162714931)
            ·
              refine ⟨186192015463185877744072397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124128010308790585162714931 186192015463185877744072397)
              ·
                refine ⟨69822005798694704154027149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186192015463185877744072397 69822005798694704154027149)
                ·
                  refine ⟨26183252174510514057760181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69822005798694704154027149 26183252174510514057760181)
                  ·
                    refine ⟨2454679891360360692915017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26183252174510514057760181 2454679891360360692915017)
                    ·
                      refine ⟨1841009918520270519686263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2454679891360360692915017 1841009918520270519686263)
                      ·
                        rfl

theorem cell23_3585354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_3585354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585354 prefixEnd_3585354 := by exact prefixLift 3585354
  have htrace : WordTrace (prefixWord ++ tailWord_3585354) baseStart_3585354 baseEnd_3585354 := by
    simpa [prefixWord, tailWord_3585354, baseEnd_3585354] using wordTrace_append hprefix tailTrace_3585354
  have hstable : (prefixWord ++ tailWord_3585354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585354).length < 2 ^ (prefixWord ++ tailWord_3585354).sum := by decide
  have hdescent : baseEnd_3585354 < baseStart_3585354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585364 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_3585364 : Nat := 118140960795 + 3585364 * 2 ^ 59
def prefixEnd_3585364 : Nat := 4983230072969 + 3 ^ 40 * 3585364 * 2
def baseEnd_3585364 : Nat := 613671684442271826853739

theorem tailTrace_3585364 : CollatzResearch.WordTrace tailWord_3585364 prefixEnd_3585364 613671684442271826853739 := by
  unfold tailWord_3585364
  simp only [CollatzResearch.WordTrace]
  refine ⟨65384484091423017133057573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87179312121897356177410097 65384484091423017133057573)
  ·
    refine ⟨12259590767141815712448295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65384484091423017133057573 12259590767141815712448295)
    ·
      refine ⟨18389386150712723568672443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12259590767141815712448295 18389386150712723568672443)
      ·
        refine ⟨27584079226069085353008665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18389386150712723568672443 27584079226069085353008665)
        ·
          refine ⟨20688059419551814014756499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27584079226069085353008665 20688059419551814014756499)
          ·
            refine ⟨31032089129327721022134749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20688059419551814014756499 31032089129327721022134749)
            ·
              refine ⟨11637033423497895383300531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31032089129327721022134749 11637033423497895383300531)
              ·
                refine ⟨17455550135246843074950797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11637033423497895383300531 17455550135246843074950797)
                ·
                  refine ⟨6545831300717566153106549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17455550135246843074950797 6545831300717566153106549)
                  ·
                    refine ⟨613671684442271826853739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6545831300717566153106549 613671684442271826853739)
                    ·
                      rfl

theorem cell23_3585364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_3585364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585364 prefixEnd_3585364 := by exact prefixLift 3585364
  have htrace : WordTrace (prefixWord ++ tailWord_3585364) baseStart_3585364 baseEnd_3585364 := by
    simpa [prefixWord, tailWord_3585364, baseEnd_3585364] using wordTrace_append hprefix tailTrace_3585364
  have hstable : (prefixWord ++ tailWord_3585364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585364).length < 2 ^ (prefixWord ++ tailWord_3585364).sum := by decide
  have hdescent : baseEnd_3585364 < baseStart_3585364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585381 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_3585381 : Nat := 118140960795 + 3585381 * 2 ^ 59
def prefixEnd_3585381 : Nat := 4983230072969 + 3 ^ 40 * 3585381 * 2
def baseEnd_3585381 : Nat := 613674594165980638016213

theorem tailTrace_3585381 : CollatzResearch.WordTrace tailWord_3585381 prefixEnd_3585381 613674594165980638016213 := by
  unfold tailWord_3585381
  simp only [CollatzResearch.WordTrace]
  refine ⟨130769588223784446169483997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87179725482522964112989331 130769588223784446169483997)
  ·
    refine ⟨49038595583919167313556499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130769588223784446169483997 49038595583919167313556499)
    ·
      refine ⟨73557893375878750970334749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49038595583919167313556499 73557893375878750970334749)
      ·
        refine ⟨27584210015954531613875531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73557893375878750970334749 27584210015954531613875531)
        ·
          refine ⟨41376315023931797420813297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27584210015954531613875531 41376315023931797420813297)
          ·
            refine ⟨31032236267948848065609973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41376315023931797420813297 31032236267948848065609973)
            ·
              refine ⟨2909272150120204506150935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31032236267948848065609973 2909272150120204506150935)
              ·
                refine ⟨4363908225180306759226403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909272150120204506150935 4363908225180306759226403)
                ·
                  refine ⟨6545862337770460138839605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363908225180306759226403 6545862337770460138839605)
                  ·
                    refine ⟨613674594165980638016213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6545862337770460138839605 613674594165980638016213)
                    ·
                      rfl

theorem cell23_3585381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_3585381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585381 prefixEnd_3585381 := by exact prefixLift 3585381
  have htrace : WordTrace (prefixWord ++ tailWord_3585381) baseStart_3585381 baseEnd_3585381 := by
    simpa [prefixWord, tailWord_3585381, baseEnd_3585381] using wordTrace_append hprefix tailTrace_3585381
  have hstable : (prefixWord ++ tailWord_3585381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585381).length < 2 ^ (prefixWord ++ tailWord_3585381).sum := by decide
  have hdescent : baseEnd_3585381 < baseStart_3585381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585404 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_3585404 : Nat := 118140960795 + 3585404 * 2 ^ 59
def prefixEnd_3585404 : Nat := 4983230072969 + 3 ^ 40 * 3585404 * 2
def baseEnd_3585404 : Nat := 1841035592552995324061033

theorem tailTrace_3585404 : CollatzResearch.WordTrace tailWord_3585404 prefixEnd_3585404 1841035592552995324061033 := by
  unfold tailWord_3585404
  simp only [CollatzResearch.WordTrace]
  refine ⟨65385213551350560548785633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87180284735134080731714177 65385213551350560548785633)
  ·
    refine ⟨49038910163512920411589225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65385213551350560548785633 49038910163512920411589225)
    ·
      refine ⟨36779182622634690308691919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49038910163512920411589225 36779182622634690308691919)
      ·
        refine ⟨55168773933952035463037879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36779182622634690308691919 55168773933952035463037879)
        ·
          refine ⟨82753160900928053194556819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55168773933952035463037879 82753160900928053194556819)
          ·
            refine ⟨124129741351392079791835229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82753160900928053194556819 124129741351392079791835229)
            ·
              refine ⟨46548653006772029921938211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124129741351392079791835229 46548653006772029921938211)
              ·
                refine ⟨69822979510158044882907317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46548653006772029921938211 69822979510158044882907317)
                ·
                  refine ⟨6545904329077316707772561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69822979510158044882907317 6545904329077316707772561)
                  ·
                    refine ⟨4909428246807987530829421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6545904329077316707772561 4909428246807987530829421)
                    ·
                      refine ⟨1841035592552995324061033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4909428246807987530829421 1841035592552995324061033)
                      ·
                        rfl

theorem cell23_3585404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_3585404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585404 prefixEnd_3585404 := by exact prefixLift 3585404
  have htrace : WordTrace (prefixWord ++ tailWord_3585404) baseStart_3585404 baseEnd_3585404 := by
    simpa [prefixWord, tailWord_3585404, baseEnd_3585404] using wordTrace_append hprefix tailTrace_3585404
  have hstable : (prefixWord ++ tailWord_3585404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585404).length < 2 ^ (prefixWord ++ tailWord_3585404).sum := by decide
  have hdescent : baseEnd_3585404 < baseStart_3585404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585411 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 2, 4]
def baseStart_3585411 : Nat := 118140960795 + 3585411 * 2 ^ 59
def prefixEnd_3585411 : Nat := 4983230072969 + 3 ^ 40 * 3585411 * 2
def baseEnd_3585411 : Nat := 613679728972525598891167

theorem tailTrace_3585411 : CollatzResearch.WordTrace tailWord_3585411 prefixEnd_3585411 613679728972525598891167 := by
  unfold tailWord_3585411
  simp only [CollatzResearch.WordTrace]
  refine ⟨130770682413675761293076087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87180454942450507528717391 130770682413675761293076087)
  ·
    refine ⟨196156023620513641939614131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130770682413675761293076087 196156023620513641939614131)
    ·
      refine ⟨294234035430770462909421197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196156023620513641939614131 294234035430770462909421197)
      ·
        refine ⟨110337763286538923591032949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294234035430770462909421197 110337763286538923591032949)
        ·
          refine ⟨10344165308113024086659339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110337763286538923591032949 10344165308113024086659339)
          ·
            refine ⟨15516247962169536129989009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10344165308113024086659339 15516247962169536129989009)
            ·
              refine ⟨11637185971627152097491757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15516247962169536129989009 11637185971627152097491757)
              ·
                refine ⟨4363944739360182036559409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11637185971627152097491757 4363944739360182036559409)
                ·
                  refine ⟨3272958554520136527419557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4363944739360182036559409 3272958554520136527419557)
                  ·
                    refine ⟨613679728972525598891167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3272958554520136527419557 613679728972525598891167)
                    ·
                      rfl

theorem cell23_3585411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 4].length) (baseStart_3585411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585411 prefixEnd_3585411 := by exact prefixLift 3585411
  have htrace : WordTrace (prefixWord ++ tailWord_3585411) baseStart_3585411 baseEnd_3585411 := by
    simpa [prefixWord, tailWord_3585411, baseEnd_3585411] using wordTrace_append hprefix tailTrace_3585411
  have hstable : (prefixWord ++ tailWord_3585411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585411).length < 2 ^ (prefixWord ++ tailWord_3585411).sum := by decide
  have hdescent : baseEnd_3585411 < baseStart_3585411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585422 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3585422 : Nat := 118140960795 + 3585422 * 2 ^ 59
def prefixEnd_3585422 : Nat := 4983230072969 + 3 ^ 40 * 3585422 * 2
def baseEnd_3585422 : Nat := 1841044835204776253635951

theorem tailTrace_3585422 : CollatzResearch.WordTrace tailWord_3585422 prefixEnd_3585422 1841044835204776253635951 := by
  unfold tailWord_3585422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16346385452079488771465815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87180722411090606781151013 16346385452079488771465815)
  ·
    refine ⟨24519578178119233157198723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16346385452079488771465815 24519578178119233157198723)
    ·
      refine ⟨36779367267178849735798085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24519578178119233157198723 36779367267178849735798085)
      ·
        refine ⟨6896131362596034325462141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36779367267178849735798085 6896131362596034325462141)
        ·
          refine ⟨2586049260973512872048303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6896131362596034325462141 2586049260973512872048303)
          ·
            refine ⟨3879073891460269308072455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586049260973512872048303 3879073891460269308072455)
            ·
              refine ⟨5818610837190403962108683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3879073891460269308072455 5818610837190403962108683)
              ·
                refine ⟨8727916255785605943163025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818610837190403962108683 8727916255785605943163025)
                ·
                  refine ⟨6545937191839204457372269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8727916255785605943163025 6545937191839204457372269)
                  ·
                    refine ⟨2454726446939701671514601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6545937191839204457372269 2454726446939701671514601)
                    ·
                      refine ⟨1841044835204776253635951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2454726446939701671514601 1841044835204776253635951)
                      ·
                        rfl

theorem cell23_3585422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3585422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585422 prefixEnd_3585422 := by exact prefixLift 3585422
  have htrace : WordTrace (prefixWord ++ tailWord_3585422) baseStart_3585422 baseEnd_3585422 := by
    simpa [prefixWord, tailWord_3585422, baseEnd_3585422] using wordTrace_append hprefix tailTrace_3585422
  have hstable : (prefixWord ++ tailWord_3585422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585422).length < 2 ^ (prefixWord ++ tailWord_3585422).sum := by decide
  have hdescent : baseEnd_3585422 < baseStart_3585422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585504 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_3585504 : Nat := 118140960795 + 3585504 * 2 ^ 59
def prefixEnd_3585504 : Nat := 4983230072969 + 3 ^ 40 * 3585504 * 2
def baseEnd_3585504 : Nat := 1841086940618444932810573

theorem tailTrace_3585504 : CollatzResearch.WordTrace tailWord_3585504 prefixEnd_3585504 1841086940618444932810573 := by
  unfold tailWord_3585504
  simp only [CollatzResearch.WordTrace]
  refine ⟨65387037201169419088105783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87182716268225892117474377 65387037201169419088105783)
  ·
    refine ⟨98080555801754128632158675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65387037201169419088105783 98080555801754128632158675)
    ·
      refine ⟨147120833702631192948238013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98080555801754128632158675 147120833702631192948238013)
      ·
        refine ⟨55170312638486697355589255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147120833702631192948238013 55170312638486697355589255)
        ·
          refine ⟨82755468957730046033383883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55170312638486697355589255 82755468957730046033383883)
          ·
            refine ⟨124133203436595069050075825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82755468957730046033383883 124133203436595069050075825)
            ·
              refine ⟨93099902577446301787556869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124133203436595069050075825 93099902577446301787556869)
              ·
                refine ⟨17456231733271181585166913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93099902577446301787556869 17456231733271181585166913)
                ·
                  refine ⟨13092173799953386188875185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17456231733271181585166913 13092173799953386188875185)
                  ·
                    refine ⟨9819130349965039641656389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13092173799953386188875185 9819130349965039641656389)
                    ·
                      refine ⟨1841086940618444932810573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9819130349965039641656389 1841086940618444932810573)
                      ·
                        rfl

theorem cell23_3585504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_3585504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585504 prefixEnd_3585504 := by exact prefixLift 3585504
  have htrace : WordTrace (prefixWord ++ tailWord_3585504) baseStart_3585504 baseEnd_3585504 := by
    simpa [prefixWord, tailWord_3585504, baseEnd_3585504] using wordTrace_append hprefix tailTrace_3585504
  have hstable : (prefixWord ++ tailWord_3585504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585504).length < 2 ^ (prefixWord ++ tailWord_3585504).sum := by decide
  have hdescent : baseEnd_3585504 < baseStart_3585504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585544 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 1, 7]
def baseStart_3585544 : Nat := 118140960795 + 3585544 * 2 ^ 59
def prefixEnd_3585544 : Nat := 4983230072969 + 3 ^ 40 * 3585544 * 2
def baseEnd_3585544 : Nat := 613702493281541592103463

theorem tailTrace_3585544 : CollatzResearch.WordTrace tailWord_3585544 prefixEnd_3585544 613702493281541592103463 := by
  unfold tailWord_3585544
  simp only [CollatzResearch.WordTrace]
  refine ⟨65387766661096962503833843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87183688881462616671778457 65387766661096962503833843)
  ·
    refine ⟨98081649991645443755750765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65387766661096962503833843 98081649991645443755750765)
    ·
      refine ⟨36780618746867041408406537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98081649991645443755750765 36780618746867041408406537)
      ·
        refine ⟨27585464060150281056304903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36780618746867041408406537 27585464060150281056304903)
        ·
          refine ⟨41378196090225421584457355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27585464060150281056304903 41378196090225421584457355)
          ·
            refine ⟨62067294135338132376686033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41378196090225421584457355 62067294135338132376686033)
            ·
              refine ⟨46550470601503599282514525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62067294135338132376686033 46550470601503599282514525)
              ·
                refine ⟨17456426475563849730942947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46550470601503599282514525 17456426475563849730942947)
                ·
                  refine ⟨26184639713345774596414421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17456426475563849730942947 26184639713345774596414421)
                  ·
                    refine ⟨613702493281541592103463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26184639713345774596414421 613702493281541592103463)
                    ·
                      rfl

theorem cell23_3585544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_3585544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585544 prefixEnd_3585544 := by exact prefixLift 3585544
  have htrace : WordTrace (prefixWord ++ tailWord_3585544) baseStart_3585544 baseEnd_3585544 := by
    simpa [prefixWord, tailWord_3585544, baseEnd_3585544] using wordTrace_append hprefix tailTrace_3585544
  have hstable : (prefixWord ++ tailWord_3585544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585544).length < 2 ^ (prefixWord ++ tailWord_3585544).sum := by decide
  have hdescent : baseEnd_3585544 < baseStart_3585544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585568 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3585568 : Nat := 118140960795 + 3585568 * 2 ^ 59
def prefixEnd_3585568 : Nat := 4983230072969 + 3 ^ 40 * 3585568 * 2
def baseEnd_3585568 : Nat := 1841119803380332682410279

theorem tailTrace_3585568 : CollatzResearch.WordTrace tailWord_3585568 prefixEnd_3585568 1841119803380332682410279 := by
  unfold tailWord_3585568
  simp only [CollatzResearch.WordTrace]
  refine ⟨65388204337053488553270679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87184272449404651404360905 65388204337053488553270679)
  ·
    refine ⟨98082306505580232829906019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65388204337053488553270679 98082306505580232829906019)
    ·
      refine ⟨147123459758370349244859029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98082306505580232829906019 147123459758370349244859029)
      ·
        refine ⟨6896412176173610120852767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147123459758370349244859029 6896412176173610120852767)
        ·
          refine ⟨10344618264260415181279151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6896412176173610120852767 10344618264260415181279151)
          ·
            refine ⟨15516927396390622771918727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10344618264260415181279151 15516927396390622771918727)
            ·
              refine ⟨23275391094585934157878091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15516927396390622771918727 23275391094585934157878091)
              ·
                refine ⟨34913086641878901236817137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23275391094585934157878091 34913086641878901236817137)
                ·
                  refine ⟨26184814981409175927612853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34913086641878901236817137 26184814981409175927612853)
                  ·
                    refine ⟨2454826404507110243213705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26184814981409175927612853 2454826404507110243213705)
                    ·
                      refine ⟨1841119803380332682410279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2454826404507110243213705 1841119803380332682410279)
                      ·
                        rfl

theorem cell23_3585568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3585568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585568 prefixEnd_3585568 := by exact prefixLift 3585568
  have htrace : WordTrace (prefixWord ++ tailWord_3585568) baseStart_3585568 baseEnd_3585568 := by
    simpa [prefixWord, tailWord_3585568, baseEnd_3585568] using wordTrace_append hprefix tailTrace_3585568
  have hstable : (prefixWord ++ tailWord_3585568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585568).length < 2 ^ (prefixWord ++ tailWord_3585568).sum := by decide
  have hdescent : baseEnd_3585568 < baseStart_3585568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585591 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 5, 4]
def baseStart_3585591 : Nat := 118140960795 + 3585591 * 2 ^ 59
def prefixEnd_3585591 : Nat := 4983230072969 + 3 ^ 40 * 3585591 * 2
def baseEnd_3585591 : Nat := 613710537811795364140891

theorem tailTrace_3585591 : CollatzResearch.WordTrace tailWord_3585591 prefixEnd_3585591 613710537811795364140891 := by
  unfold tailWord_3585591
  simp only [CollatzResearch.WordTrace]
  refine ⟨130777247553023652034628627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87184831702015768023085751 130777247553023652034628627)
  ·
    refine ⟨196165871329535478051942941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130777247553023652034628627 196165871329535478051942941)
    ·
      refine ⟨73562201748575804269478603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196165871329535478051942941 73562201748575804269478603)
      ·
        refine ⟨110343302622863706404217905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73562201748575804269478603 110343302622863706404217905)
        ·
          refine ⟨82757476967147779803163429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110343302622863706404217905 82757476967147779803163429)
          ·
            refine ⟨15517026931340208713093143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82757476967147779803163429 15517026931340208713093143)
            ·
              refine ⟨23275540397010313069639715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15517026931340208713093143 23275540397010313069639715)
              ·
                refine ⟨34913310595515469604459573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23275540397010313069639715 34913310595515469604459573)
                ·
                  refine ⟨3273122868329575275418085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34913310595515469604459573 3273122868329575275418085)
                  ·
                    refine ⟨613710537811795364140891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3273122868329575275418085 613710537811795364140891)
                    ·
                      rfl

theorem cell23_3585591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_3585591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585591 prefixEnd_3585591 := by exact prefixLift 3585591
  have htrace : WordTrace (prefixWord ++ tailWord_3585591) baseStart_3585591 baseEnd_3585591 := by
    simpa [prefixWord, tailWord_3585591, baseEnd_3585591] using wordTrace_append hprefix tailTrace_3585591
  have hstable : (prefixWord ++ tailWord_3585591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585591).length < 2 ^ (prefixWord ++ tailWord_3585591).sum := by decide
  have hdescent : baseEnd_3585591 < baseStart_3585591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585701 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3585701 : Nat := 118140960795 + 3585701 * 2 ^ 59
def prefixEnd_3585701 : Nat := 4983230072969 + 3 ^ 40 * 3585701 * 2
def baseEnd_3585701 : Nat := 1841188096307380662047167

theorem tailTrace_3585701 : CollatzResearch.WordTrace tailWord_3585701 prefixEnd_3585701 1841188096307380662047167 := by
  unfold tailWord_3585701
  simp only [CollatzResearch.WordTrace]
  refine ⟨130781259582625140821132957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87187506388416760547421971 130781259582625140821132957)
  ·
    refine ⟨49042972343484427807924859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130781259582625140821132957 49042972343484427807924859)
    ·
      refine ⟨73564458515226641711887289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49042972343484427807924859 73564458515226641711887289)
      ·
        refine ⟨55173343886419981283915467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73564458515226641711887289 55173343886419981283915467)
        ·
          refine ⟨82760015829629971925873201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55173343886419981283915467 82760015829629971925873201)
          ·
            refine ⟨62070011872222478944404901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82760015829629971925873201 62070011872222478944404901)
            ·
              refine ⟨11638127226041714802075919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62070011872222478944404901 11638127226041714802075919)
              ·
                refine ⟨17457190839062572203113879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11638127226041714802075919 17457190839062572203113879)
                ·
                  refine ⟨26185786258593858304670819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17457190839062572203113879 26185786258593858304670819)
                  ·
                    refine ⟨39278679387890787457006229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26185786258593858304670819 39278679387890787457006229)
                    ·
                      refine ⟨1841188096307380662047167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39278679387890787457006229 1841188096307380662047167)
                      ·
                        rfl

theorem cell23_3585701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3585701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585701 prefixEnd_3585701 := by exact prefixLift 3585701
  have htrace : WordTrace (prefixWord ++ tailWord_3585701) baseStart_3585701 baseEnd_3585701 := by
    simpa [prefixWord, tailWord_3585701, baseEnd_3585701] using wordTrace_append hprefix tailTrace_3585701
  have hstable : (prefixWord ++ tailWord_3585701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585701).length < 2 ^ (prefixWord ++ tailWord_3585701).sum := by decide
  have hdescent : baseEnd_3585701 < baseStart_3585701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585765 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 3, 3, 2]
def baseStart_3585765 : Nat := 118140960795 + 3585765 * 2 ^ 59
def prefixEnd_3585765 : Nat := 4983230072969 + 3 ^ 40 * 3585765 * 2
def baseEnd_3585765 : Nat := 1841220959069268411646873

theorem tailTrace_3585765 : CollatzResearch.WordTrace tailWord_3585765 prefixEnd_3585765 1841220959069268411646873 := by
  unfold tailWord_3585765
  simp only [CollatzResearch.WordTrace]
  refine ⟨130783593854393279751462749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87189062569595519834308499 130783593854393279751462749)
  ·
    refine ⟨49043847695397479906798531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130783593854393279751462749 49043847695397479906798531)
    ·
      refine ⟨73565771543096219860197797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49043847695397479906798531 73565771543096219860197797)
      ·
        refine ⟨13793582164330541223787087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73565771543096219860197797 13793582164330541223787087)
        ·
          refine ⟨20690373246495811835680631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13793582164330541223787087 20690373246495811835680631)
          ·
            refine ⟨31035559869743717753520947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20690373246495811835680631 31035559869743717753520947)
            ·
              refine ⟨46553339804615576630281421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31035559869743717753520947 46553339804615576630281421)
              ·
                refine ⟨17457502426730841236355533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46553339804615576630281421 17457502426730841236355533)
                ·
                  refine ⟨6546563410024065463633325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17457502426730841236355533 6546563410024065463633325)
                  ·
                    refine ⟨2454961278759024548862497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6546563410024065463633325 2454961278759024548862497)
                    ·
                      refine ⟨1841220959069268411646873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2454961278759024548862497 1841220959069268411646873)
                      ·
                        rfl

theorem cell23_3585765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_3585765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585765 prefixEnd_3585765 := by exact prefixLift 3585765
  have htrace : WordTrace (prefixWord ++ tailWord_3585765) baseStart_3585765 baseEnd_3585765 := by
    simpa [prefixWord, tailWord_3585765, baseEnd_3585765] using wordTrace_append hprefix tailTrace_3585765
  have hstable : (prefixWord ++ tailWord_3585765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585765).length < 2 ^ (prefixWord ++ tailWord_3585765).sum := by decide
  have hdescent : baseEnd_3585765 < baseStart_3585765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585818 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 7]
def baseStart_3585818 : Nat := 118140960795 + 3585818 * 2 ^ 59
def prefixEnd_3585818 : Nat := 4983230072969 + 3 ^ 40 * 3585818 * 2
def baseEnd_3585818 : Nat := 204583130393772967142681

theorem tailTrace_3585818 : CollatzResearch.WordTrace tailWord_3585818 prefixEnd_3585818 204583130393772967142681 := by
  unfold tailWord_3585818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32696381730800317450785527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87190351282134179868761405 32696381730800317450785527)
  ·
    refine ⟨49044572596200476176178291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32696381730800317450785527 49044572596200476176178291)
    ·
      refine ⟨73566858894300714264267437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49044572596200476176178291 73566858894300714264267437)
      ·
        refine ⟨27587572085362767849100289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73566858894300714264267437 27587572085362767849100289)
        ·
          refine ⟨20690679064022075886825217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27587572085362767849100289 20690679064022075886825217)
          ·
            refine ⟨15518009298016556915118913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20690679064022075886825217 15518009298016556915118913)
            ·
              refine ⟨11638506973512417686339185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15518009298016556915118913 11638506973512417686339185)
              ·
                refine ⟨8728880230134313264754389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11638506973512417686339185 8728880230134313264754389)
                ·
                  refine ⟨204583130393772967142681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8728880230134313264754389 204583130393772967142681)
                  ·
                    rfl

theorem cell23_3585818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_3585818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585818 prefixEnd_3585818 := by exact prefixLift 3585818
  have htrace : WordTrace (prefixWord ++ tailWord_3585818) baseStart_3585818 baseEnd_3585818 := by
    simpa [prefixWord, tailWord_3585818, baseEnd_3585818] using wordTrace_append hprefix tailTrace_3585818
  have hstable : (prefixWord ++ tailWord_3585818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585818).length < 2 ^ (prefixWord ++ tailWord_3585818).sum := by decide
  have hdescent : baseEnd_3585818 < baseStart_3585818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585848 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 4, 5]
def baseStart_3585848 : Nat := 118140960795 + 3585848 * 2 ^ 59
def prefixEnd_3585848 : Nat := 4983230072969 + 3 ^ 40 * 3585848 * 2
def baseEnd_3585848 : Nat := 613754525987863862302997

theorem tailTrace_3585848 : CollatzResearch.WordTrace tailWord_3585848 prefixEnd_3585848 613754525987863862302997 := by
  unfold tailWord_3585848
  simp only [CollatzResearch.WordTrace]
  refine ⟨65393310556546292463367099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87191080742061723284489465 65393310556546292463367099)
  ·
    refine ⟨98089965834819438695050649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65393310556546292463367099 98089965834819438695050649)
    ·
      refine ⟨73567474376114579021287987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98089965834819438695050649 73567474376114579021287987)
      ·
        refine ⟨110351211564171868531931981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73567474376114579021287987 110351211564171868531931981)
        ·
          refine ⟨41381704336564450699474493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110351211564171868531931981 41381704336564450699474493)
          ·
            refine ⟨15518139126211669012302935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41381704336564450699474493 15518139126211669012302935)
            ·
              refine ⟨23277208689317503518454403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15518139126211669012302935 23277208689317503518454403)
              ·
                refine ⟨34915813033976255277681605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23277208689317503518454403 34915813033976255277681605)
                ·
                  refine ⟨6546714943870547864565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34915813033976255277681605 6546714943870547864565301)
                  ·
                    refine ⟨613754525987863862302997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6546714943870547864565301 613754525987863862302997)
                    ·
                      rfl

theorem cell23_3585848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_3585848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585848 prefixEnd_3585848 := by exact prefixLift 3585848
  have htrace : WordTrace (prefixWord ++ tailWord_3585848) baseStart_3585848 baseEnd_3585848 := by
    simpa [prefixWord, tailWord_3585848, baseEnd_3585848] using wordTrace_append hprefix tailTrace_3585848
  have hstable : (prefixWord ++ tailWord_3585848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585848).length < 2 ^ (prefixWord ++ tailWord_3585848).sum := by decide
  have hdescent : baseEnd_3585848 < baseStart_3585848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585902 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3585902 : Nat := 118140960795 + 3585902 * 2 ^ 59
def prefixEnd_3585902 : Nat := 4983230072969 + 3 ^ 40 * 3585902 * 2
def baseEnd_3585902 : Nat := 1841291305918934375633743

theorem tailTrace_3585902 : CollatzResearch.WordTrace tailWord_3585902 prefixEnd_3585902 1841291305918934375633743 := by
  unfold tailWord_3585902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16348573831862119018649995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87192393769931301432799973 16348573831862119018649995)
  ·
    refine ⟨24522860747793178527974993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16348573831862119018649995 24522860747793178527974993)
    ·
      refine ⟨18392145560844883895981245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24522860747793178527974993 18392145560844883895981245)
      ·
        refine ⟨6897054585316831460992967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18392145560844883895981245 6897054585316831460992967)
        ·
          refine ⟨10345581877975247191489451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6897054585316831460992967 10345581877975247191489451)
          ·
            refine ⟨15518372816962870787234177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345581877975247191489451 15518372816962870787234177)
            ·
              refine ⟨11638779612722153090425633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15518372816962870787234177 11638779612722153090425633)
              ·
                refine ⟨8729084709541614817819225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11638779612722153090425633 8729084709541614817819225)
                ·
                  refine ⟨6546813532156211113364419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8729084709541614817819225 6546813532156211113364419)
                  ·
                    refine ⟨9820220298234316670046629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6546813532156211113364419 9820220298234316670046629)
                    ·
                      refine ⟨1841291305918934375633743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9820220298234316670046629 1841291305918934375633743)
                      ·
                        rfl

theorem cell23_3585902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3585902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585902 prefixEnd_3585902 := by exact prefixLift 3585902
  have htrace : WordTrace (prefixWord ++ tailWord_3585902) baseStart_3585902 baseEnd_3585902 := by
    simpa [prefixWord, tailWord_3585902, baseEnd_3585902] using wordTrace_append hprefix tailTrace_3585902
  have hstable : (prefixWord ++ tailWord_3585902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585902).length < 2 ^ (prefixWord ++ tailWord_3585902).sum := by decide
  have hdescent : baseEnd_3585902 < baseStart_3585902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585905 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_3585905 : Nat := 118140960795 + 3585905 * 2 ^ 59
def prefixEnd_3585905 : Nat := 4983230072969 + 3 ^ 40 * 3585905 * 2
def baseEnd_3585905 : Nat := 1841292846360897863896229

theorem tailTrace_3585905 : CollatzResearch.WordTrace tailWord_3585905 prefixEnd_3585905 1841292846360897863896229 := by
  unfold tailWord_3585905
  simp only [CollatzResearch.WordTrace]
  refine ⟨130788700073886083661559169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87192466715924055774372779 130788700073886083661559169)
  ·
    refine ⟨98091525055414562746169377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130788700073886083661559169 98091525055414562746169377)
    ·
      refine ⟨73568643791560922059627033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98091525055414562746169377 73568643791560922059627033)
      ·
        refine ⟨55176482843670691544720275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73568643791560922059627033 55176482843670691544720275)
        ·
          refine ⟨82764724265506037317080413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55176482843670691544720275 82764724265506037317080413)
          ·
            refine ⟨31036771599564763993905155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82764724265506037317080413 31036771599564763993905155)
            ·
              refine ⟨46555157399347145990857733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31036771599564763993905155 46555157399347145990857733)
              ·
                refine ⟨8729092012377589873285825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46555157399347145990857733 8729092012377589873285825)
                ·
                  refine ⟨6546819009283192404964369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8729092012377589873285825 6546819009283192404964369)
                  ·
                    refine ⟨4910114256962394303723277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6546819009283192404964369 4910114256962394303723277)
                    ·
                      refine ⟨1841292846360897863896229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4910114256962394303723277 1841292846360897863896229)
                      ·
                        rfl

theorem cell23_3585905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_3585905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585905 prefixEnd_3585905 := by exact prefixLift 3585905
  have htrace : WordTrace (prefixWord ++ tailWord_3585905) baseStart_3585905 baseEnd_3585905 := by
    simpa [prefixWord, tailWord_3585905, baseEnd_3585905] using wordTrace_append hprefix tailTrace_3585905
  have hstable : (prefixWord ++ tailWord_3585905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585905).length < 2 ^ (prefixWord ++ tailWord_3585905).sum := by decide
  have hdescent : baseEnd_3585905 < baseStart_3585905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585969 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3585969 : Nat := 118140960795 + 3585969 * 2 ^ 59
def prefixEnd_3585969 : Nat := 4983230072969 + 3 ^ 40 * 3585969 * 2
def baseEnd_3585969 : Nat := 1841325709122785613495935

theorem tailTrace_3585969 : CollatzResearch.WordTrace tailWord_3585969 prefixEnd_3585969 1841325709122785613495935 := by
  unfold tailWord_3585969
  simp only [CollatzResearch.WordTrace]
  refine ⟨130791034345654222591888961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87194022897102815061259307 130791034345654222591888961)
  ·
    refine ⟨98093275759240666943916721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130791034345654222591888961 98093275759240666943916721)
    ·
      refine ⟨73569956819430500207937541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98093275759240666943916721 73569956819430500207937541)
      ·
        refine ⟨13794366903643218788988289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73569956819430500207937541 13794366903643218788988289)
        ·
          refine ⟨10345775177732414091741217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13794366903643218788988289 10345775177732414091741217)
          ·
            refine ⟨7759331383299310568805913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10345775177732414091741217 7759331383299310568805913)
            ·
              refine ⟨5819498537474482926604435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7759331383299310568805913 5819498537474482926604435)
              ·
                refine ⟨8729247806211724389906653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5819498537474482926604435 8729247806211724389906653)
                ·
                  refine ⟨3273467927329396646214995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8729247806211724389906653 3273467927329396646214995)
                  ·
                    refine ⟨4910201890994094969322493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3273467927329396646214995 4910201890994094969322493)
                    ·
                      refine ⟨1841325709122785613495935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4910201890994094969322493 1841325709122785613495935)
                      ·
                        rfl

theorem cell23_3585969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3585969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585969 prefixEnd_3585969 := by exact prefixLift 3585969
  have htrace : WordTrace (prefixWord ++ tailWord_3585969) baseStart_3585969 baseEnd_3585969 := by
    simpa [prefixWord, tailWord_3585969, baseEnd_3585969] using wordTrace_append hprefix tailTrace_3585969
  have hstable : (prefixWord ++ tailWord_3585969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585969).length < 2 ^ (prefixWord ++ tailWord_3585969).sum := by decide
  have hdescent : baseEnd_3585969 < baseStart_3585969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585992 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_3585992 : Nat := 118140960795 + 3585992 * 2 ^ 59
def prefixEnd_3585992 : Nat := 4983230072969 + 3 ^ 40 * 3585992 * 2
def baseEnd_3585992 : Nat := 1841337519177839023508329

theorem tailTrace_3585992 : CollatzResearch.WordTrace tailWord_3585992 prefixEnd_3585992 1841337519177839023508329 := by
  unfold tailWord_3585992
  simp only [CollatzResearch.WordTrace]
  refine ⟨65395936612285448759988115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87194582149713931679984153 65395936612285448759988115)
  ·
    refine ⟨98093904918428173139982173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65395936612285448759988115 98093904918428173139982173)
    ·
      refine ⟨36785214344410564927493315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98093904918428173139982173 36785214344410564927493315)
      ·
        refine ⟨55177821516615847391239973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36785214344410564927493315 55177821516615847391239973)
        ·
          refine ⟨10345841534365471385857495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55177821516615847391239973 10345841534365471385857495)
          ·
            refine ⟨15518762301548207078786243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345841534365471385857495 15518762301548207078786243)
            ·
              refine ⟨23278143452322310618179365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15518762301548207078786243 23278143452322310618179365)
              ·
                refine ⟨4364651897310433240908631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23278143452322310618179365 4364651897310433240908631)
                ·
                  refine ⟨6546977845965649861362947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364651897310433240908631 6546977845965649861362947)
                  ·
                    refine ⟨9820466768948474792044421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6546977845965649861362947 9820466768948474792044421)
                    ·
                      refine ⟨1841337519177839023508329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9820466768948474792044421 1841337519177839023508329)
                      ·
                        rfl

theorem cell23_3585992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_3585992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3585992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3585992 prefixEnd_3585992 := by exact prefixLift 3585992
  have htrace : WordTrace (prefixWord ++ tailWord_3585992) baseStart_3585992 baseEnd_3585992 := by
    simpa [prefixWord, tailWord_3585992, baseEnd_3585992] using wordTrace_append hprefix tailTrace_3585992
  have hstable : (prefixWord ++ tailWord_3585992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585992).length < 2 ^ (prefixWord ++ tailWord_3585992).sum := by decide
  have hdescent : baseEnd_3585992 < baseStart_3585992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586015 : List Nat := [1, 1, 2, 3, 4, 3, 9]
def baseStart_3586015 : Nat := 118140960795 + 3586015 * 2 ^ 59
def prefixEnd_3586015 : Nat := 4983230072969 + 3 ^ 40 * 3586015 * 2
def baseEnd_3586015 : Nat := 22732707768307313994083

theorem tailTrace_3586015 : CollatzResearch.WordTrace tailWord_3586015 prefixEnd_3586015 22732707768307313994083 := by
  unfold tailWord_3586015
  simp only [CollatzResearch.WordTrace]
  refine ⟨130792712103487572448063499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87195141402325048298708999 130792712103487572448063499)
  ·
    refine ⟨196189068155231358672095249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130792712103487572448063499 196189068155231358672095249)
    ·
      refine ⟨147141801116423519004071437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196189068155231358672095249 147141801116423519004071437)
      ·
        refine ⟨55178175418658819626526789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147141801116423519004071437 55178175418658819626526789)
        ·
          refine ⟨10345907890998528679973773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55178175418658819626526789 10345907890998528679973773)
          ·
            refine ⟨3879715459124448254990165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10345907890998528679973773 3879715459124448254990165)
            ·
              refine ⟨22732707768307313994083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3879715459124448254990165 22732707768307313994083)
              ·
                rfl

theorem cell23_3586015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 9].length) (baseStart_3586015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586015 prefixEnd_3586015 := by exact prefixLift 3586015
  have htrace : WordTrace (prefixWord ++ tailWord_3586015) baseStart_3586015 baseEnd_3586015 := by
    simpa [prefixWord, tailWord_3586015, baseEnd_3586015] using wordTrace_append hprefix tailTrace_3586015
  have hstable : (prefixWord ++ tailWord_3586015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586015).length < 2 ^ (prefixWord ++ tailWord_3586015).sum := by decide
  have hdescent : baseEnd_3586015 < baseStart_3586015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586046 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3586046 : Nat := 118140960795 + 3586046 * 2 ^ 59
def prefixEnd_3586046 : Nat := 4983230072969 + 3 ^ 40 * 3586046 * 2
def baseEnd_3586046 : Nat := 1841365247133181812233081

theorem tailTrace_3586046 : CollatzResearch.WordTrace tailWord_3586046 prefixEnd_3586046 1841365247133181812233081 := by
  unfold tailWord_3586046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16349230345796908092805249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87195895177583509828294661 16349230345796908092805249)
  ·
    refine ⟨12261922759347681069603937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16349230345796908092805249 12261922759347681069603937)
    ·
      refine ⟨9196442069510760802202953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12261922759347681069603937 9196442069510760802202953)
      ·
        refine ⟨6897331552133070601652215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9196442069510760802202953 6897331552133070601652215)
        ·
          refine ⟨10345997328199605902478323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6897331552133070601652215 10345997328199605902478323)
          ·
            refine ⟨15518995992299408853717485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345997328199605902478323 15518995992299408853717485)
            ·
              refine ⟨5819623497112278320144057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15518995992299408853717485 5819623497112278320144057)
              ·
                refine ⟨4364717622834208740108043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5819623497112278320144057 4364717622834208740108043)
                ·
                  refine ⟨6547076434251313110162065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364717622834208740108043 6547076434251313110162065)
                  ·
                    refine ⟨4910307325688484832621549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6547076434251313110162065 4910307325688484832621549)
                    ·
                      refine ⟨1841365247133181812233081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4910307325688484832621549 1841365247133181812233081)
                      ·
                        rfl

theorem cell23_3586046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3586046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586046 prefixEnd_3586046 := by exact prefixLift 3586046
  have htrace : WordTrace (prefixWord ++ tailWord_3586046) baseStart_3586046 baseEnd_3586046 := by
    simpa [prefixWord, tailWord_3586046, baseEnd_3586046] using wordTrace_append hprefix tailTrace_3586046
  have hstable : (prefixWord ++ tailWord_3586046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586046).length < 2 ^ (prefixWord ++ tailWord_3586046).sum := by decide
  have hdescent : baseEnd_3586046 < baseStart_3586046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586076 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_3586076 : Nat := 118140960795 + 3586076 * 2 ^ 59
def prefixEnd_3586076 : Nat := 4983230072969 + 3 ^ 40 * 3586076 * 2
def baseEnd_3586076 : Nat := 1841380651552816694857943

theorem tailTrace_3586076 : CollatzResearch.WordTrace tailWord_3586076 prefixEnd_3586076 1841380651552816694857943 := by
  unfold tailWord_3586076
  simp only [CollatzResearch.WordTrace]
  refine ⟨65397468478133289933017041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87196624637511053244022721 65397468478133289933017041)
  ·
    refine ⟨49048101358599967449762781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65397468478133289933017041 49048101358599967449762781)
    ·
      refine ⟨18393038009474987793661043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49048101358599967449762781 18393038009474987793661043)
      ·
        refine ⟨27589557014212481690491565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18393038009474987793661043 27589557014212481690491565)
        ·
          refine ⟨10346083880329680633934337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27589557014212481690491565 10346083880329680633934337)
          ·
            refine ⟨7759562910247260475450753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10346083880329680633934337 7759562910247260475450753)
            ·
              refine ⟨5819672182685445356588065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7759562910247260475450753 5819672182685445356588065)
              ·
                refine ⟨4364754137014084017441049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5819672182685445356588065 4364754137014084017441049)
                ·
                  refine ⟨3273565602760563013080787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4364754137014084017441049 3273565602760563013080787)
                  ·
                    refine ⟨4910348404140844519621181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3273565602760563013080787 4910348404140844519621181)
                    ·
                      refine ⟨1841380651552816694857943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4910348404140844519621181 1841380651552816694857943)
                      ·
                        rfl

theorem cell23_3586076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_3586076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586076 prefixEnd_3586076 := by exact prefixLift 3586076
  have htrace : WordTrace (prefixWord ++ tailWord_3586076) baseStart_3586076 baseEnd_3586076 := by
    simpa [prefixWord, tailWord_3586076, baseEnd_3586076] using wordTrace_append hprefix tailTrace_3586076
  have hstable : (prefixWord ++ tailWord_3586076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586076).length < 2 ^ (prefixWord ++ tailWord_3586076).sum := by decide
  have hdescent : baseEnd_3586076 < baseStart_3586076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586133 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_3586133 : Nat := 118140960795 + 3586133 * 2 ^ 59
def prefixEnd_3586133 : Nat := 4983230072969 + 3 ^ 40 * 3586133 * 2
def baseEnd_3586133 : Nat := 1841409919950122971845181

theorem tailTrace_3586133 : CollatzResearch.WordTrace tailWord_3586133 prefixEnd_3586133 1841409919950122971845181 := by
  unfold tailWord_3586133
  simp only [CollatzResearch.WordTrace]
  refine ⟨130797015917060078600859053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87198010611373385733906035 130797015917060078600859053)
  ·
    refine ⟨49048880968897529475322145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130797015917060078600859053 49048880968897529475322145)
    ·
      refine ⟨36786660726673147106491609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49048880968897529475322145 36786660726673147106491609)
      ·
        refine ⟨27589995545004860329868707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36786660726673147106491609 27589995545004860329868707)
        ·
          refine ⟨41384993317507290494803061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27589995545004860329868707 41384993317507290494803061)
          ·
            refine ⟨3879843123516308483887787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41384993317507290494803061 3879843123516308483887787)
            ·
              refine ⟨5819764685274462725831681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3879843123516308483887787 5819764685274462725831681)
              ·
                refine ⟨4364823513955847044373761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5819764685274462725831681 4364823513955847044373761)
                ·
                  refine ⟨3273617635466885283280321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4364823513955847044373761 3273617635466885283280321)
                  ·
                    refine ⟨2455213226600163962460241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3273617635466885283280321 2455213226600163962460241)
                    ·
                      refine ⟨1841409919950122971845181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455213226600163962460241 1841409919950122971845181)
                      ·
                        rfl

theorem cell23_3586133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_3586133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586133 prefixEnd_3586133 := by exact prefixLift 3586133
  have htrace : WordTrace (prefixWord ++ tailWord_3586133) baseStart_3586133 baseEnd_3586133 := by
    simpa [prefixWord, tailWord_3586133, baseEnd_3586133] using wordTrace_append hprefix tailTrace_3586133
  have hstable : (prefixWord ++ tailWord_3586133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586133).length < 2 ^ (prefixWord ++ tailWord_3586133).sum := by decide
  have hdescent : baseEnd_3586133 < baseStart_3586133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586145 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3586145 : Nat := 118140960795 + 3586145 * 2 ^ 59
def prefixEnd_3586145 : Nat := 4983230072969 + 3 ^ 40 * 3586145 * 2
def baseEnd_3586145 : Nat := 1841416081717976924895125

theorem tailTrace_3586145 : CollatzResearch.WordTrace tailWord_3586145 prefixEnd_3586145 1841416081717976924895125 := by
  unfold tailWord_3586145
  simp only [CollatzResearch.WordTrace]
  refine ⟨130797453593016604650295889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87198302395344403100197259 130797453593016604650295889)
  ·
    refine ⟨98098090194762453487721917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130797453593016604650295889 98098090194762453487721917)
    ·
      refine ⟨36786783823035920057895719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98098090194762453487721917 36786783823035920057895719)
      ·
        refine ⟨55180175734553880086843579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36786783823035920057895719 55180175734553880086843579)
        ·
          refine ⟨82770263601830820130265369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55180175734553880086843579 82770263601830820130265369)
          ·
            refine ⟨62077697701373115097699027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82770263601830820130265369 62077697701373115097699027)
            ·
              refine ⟨93116546552059672646548541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62077697701373115097699027 93116546552059672646548541)
              ·
                refine ⟨34918704957022377242455703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93116546552059672646548541 34918704957022377242455703)
                ·
                  refine ⟨52378057435533565863683555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34918704957022377242455703 52378057435533565863683555)
                  ·
                    refine ⟨78567086153300348795525333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52378057435533565863683555 78567086153300348795525333)
                    ·
                      refine ⟨1841416081717976924895125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78567086153300348795525333 1841416081717976924895125)
                      ·
                        rfl

theorem cell23_3586145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3586145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586145 prefixEnd_3586145 := by exact prefixLift 3586145
  have htrace : WordTrace (prefixWord ++ tailWord_3586145) baseStart_3586145 baseEnd_3586145 := by
    simpa [prefixWord, tailWord_3586145, baseEnd_3586145] using wordTrace_append hprefix tailTrace_3586145
  have hstable : (prefixWord ++ tailWord_3586145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586145).length < 2 ^ (prefixWord ++ tailWord_3586145).sum := by decide
  have hdescent : baseEnd_3586145 < baseStart_3586145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586172 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3586172 : Nat := 118140960795 + 3586172 * 2 ^ 59
def prefixEnd_3586172 : Nat := 4983230072969 + 3 ^ 40 * 3586172 * 2
def baseEnd_3586172 : Nat := 1841429945695648319257501

theorem tailTrace_3586172 : CollatzResearch.WordTrace tailWord_3586172 prefixEnd_3586172 1841429945695648319257501 := by
  unfold tailWord_3586172
  simp only [CollatzResearch.WordTrace]
  refine ⟨65399219181959394130764385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87198958909279192174352513 65399219181959394130764385)
  ·
    refine ⟨49049414386469545598073289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65399219181959394130764385 49049414386469545598073289)
    ·
      refine ⟨36787060789852159198554967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49049414386469545598073289 36787060789852159198554967)
      ·
        refine ⟨55180591184778238797832451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36787060789852159198554967 55180591184778238797832451)
        ·
          refine ⟨82770886777167358196748677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55180591184778238797832451 82770886777167358196748677)
          ·
            refine ⟨15519541270718879661890377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82770886777167358196748677 15519541270718879661890377)
            ·
              refine ⟨11639655953039159746417783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15519541270718879661890377 11639655953039159746417783)
              ·
                refine ⟨17459483929558739619626675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11639655953039159746417783 17459483929558739619626675)
                ·
                  refine ⟨26189225894338109429440013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17459483929558739619626675 26189225894338109429440013)
                  ·
                    refine ⟨9820959710376791036040005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26189225894338109429440013 9820959710376791036040005)
                    ·
                      refine ⟨1841429945695648319257501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9820959710376791036040005 1841429945695648319257501)
                      ·
                        rfl

theorem cell23_3586172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3586172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586172 prefixEnd_3586172 := by exact prefixLift 3586172
  have htrace : WordTrace (prefixWord ++ tailWord_3586172) baseStart_3586172 baseEnd_3586172 := by
    simpa [prefixWord, tailWord_3586172, baseEnd_3586172] using wordTrace_append hprefix tailTrace_3586172
  have hstable : (prefixWord ++ tailWord_3586172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586172).length < 2 ^ (prefixWord ++ tailWord_3586172).sum := by decide
  have hdescent : baseEnd_3586172 < baseStart_3586172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586196 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3586196 : Nat := 118140960795 + 3586196 * 2 ^ 59
def prefixEnd_3586196 : Nat := 4983230072969 + 3 ^ 40 * 3586196 * 2
def baseEnd_3586196 : Nat := 1841442269231356225357391

theorem tailTrace_3586196 : CollatzResearch.WordTrace tailWord_3586196 prefixEnd_3586196 1841442269231356225357391 := by
  unfold tailWord_3586196
  simp only [CollatzResearch.WordTrace]
  refine ⟨65399656857915920180201221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87199542477221226906934961 65399656857915920180201221)
  ·
    refine ⟨12262435660859235033787729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65399656857915920180201221 12262435660859235033787729)
    ·
      refine ⟨9196826745644426275340797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12262435660859235033787729 9196826745644426275340797)
      ·
        refine ⟨3448810029616659853252799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9196826745644426275340797 3448810029616659853252799)
        ·
          refine ⟨5173215044424989779879199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448810029616659853252799 5173215044424989779879199)
          ·
            refine ⟨7759822566637484669818799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173215044424989779879199 7759822566637484669818799)
            ·
              refine ⟨11639733849956227004728199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759822566637484669818799 11639733849956227004728199)
              ·
                refine ⟨17459600774934340507092299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11639733849956227004728199 17459600774934340507092299)
                ·
                  refine ⟨26189401162401510760638449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17459600774934340507092299 26189401162401510760638449)
                  ·
                    refine ⟨19642050871801133070478837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26189401162401510760638449 19642050871801133070478837)
                    ·
                      refine ⟨1841442269231356225357391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19642050871801133070478837 1841442269231356225357391)
                      ·
                        rfl

theorem cell23_3586196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3586196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586196 prefixEnd_3586196 := by exact prefixLift 3586196
  have htrace : WordTrace (prefixWord ++ tailWord_3586196) baseStart_3586196 baseEnd_3586196 := by
    simpa [prefixWord, tailWord_3586196, baseEnd_3586196] using wordTrace_append hprefix tailTrace_3586196
  have hstable : (prefixWord ++ tailWord_3586196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586196).length < 2 ^ (prefixWord ++ tailWord_3586196).sum := by decide
  have hdescent : baseEnd_3586196 < baseStart_3586196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586249 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 4, 3, 2]
def baseStart_3586249 : Nat := 118140960795 + 3586249 * 2 ^ 59
def prefixEnd_3586249 : Nat := 4983230072969 + 3 ^ 40 * 3586249 * 2
def baseEnd_3586249 : Nat := 1841469483706044517994647

theorem tailTrace_3586249 : CollatzResearch.WordTrace tailWord_3586249 prefixEnd_3586249 1841469483706044517994647 := by
  unfold tailWord_3586249
  simp only [CollatzResearch.WordTrace]
  refine ⟨130801246784639830412081801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87200831189759886941387867 130801246784639830412081801)
  ·
    refine ⟨98100935088479872809061351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130801246784639830412081801 98100935088479872809061351)
    ·
      refine ⟨147151402632719809213592027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98100935088479872809061351 147151402632719809213592027)
      ·
        refine ⟨220727103949079713820388041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147151402632719809213592027 220727103949079713820388041)
        ·
          refine ⟨165545327961809785365291031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220727103949079713820388041 165545327961809785365291031)
          ·
            refine ⟨248317991942714678047936547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165545327961809785365291031 248317991942714678047936547)
            ·
              refine ⟨372476987914072017071904821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248317991942714678047936547 372476987914072017071904821)
              ·
                refine ⟨34919717616944251600491077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 372476987914072017071904821 34919717616944251600491077)
                ·
                  refine ⟨6547447053177047175092077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34919717616944251600491077 6547447053177047175092077)
                  ·
                    refine ⟨2455292644941392690659529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6547447053177047175092077 2455292644941392690659529)
                    ·
                      refine ⟨1841469483706044517994647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455292644941392690659529 1841469483706044517994647)
                      ·
                        rfl

theorem cell23_3586249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 3, 2].length) (baseStart_3586249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586249 prefixEnd_3586249 := by exact prefixLift 3586249
  have htrace : WordTrace (prefixWord ++ tailWord_3586249) baseStart_3586249 baseEnd_3586249 := by
    simpa [prefixWord, tailWord_3586249, baseEnd_3586249] using wordTrace_append hprefix tailTrace_3586249
  have hstable : (prefixWord ++ tailWord_3586249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586249).length < 2 ^ (prefixWord ++ tailWord_3586249).sum := by decide
  have hdescent : baseEnd_3586249 < baseStart_3586249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586290 : List Nat := [3, 2, 1, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_3586290 : Nat := 118140960795 + 3586290 * 2 ^ 59
def prefixEnd_3586290 : Nat := 4983230072969 + 3 ^ 40 * 3586290 * 2
def baseEnd_3586290 : Nat := 1841490536412878857581959

theorem tailTrace_3586290 : CollatzResearch.WordTrace tailWord_3586290 prefixEnd_3586290 1841490536412878857581959 := by
  unfold tailWord_3586290
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700685544372823603581081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87201828118327529609549549 32700685544372823603581081)
  ·
    refine ⟨24525514158279617702685811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32700685544372823603581081 24525514158279617702685811)
    ·
      refine ⟨36788271237419426554028717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24525514158279617702685811 36788271237419426554028717)
      ·
        refine ⟨13795601714032284957760769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36788271237419426554028717 13795601714032284957760769)
        ·
          refine ⟨10346701285524213718320577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13795601714032284957760769 10346701285524213718320577)
          ·
            refine ⟨7760025964143160288740433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10346701285524213718320577 7760025964143160288740433)
            ·
              refine ⟨5820019473107370216555325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760025964143160288740433 5820019473107370216555325)
              ·
                refine ⟨2182507302415263831208247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820019473107370216555325 2182507302415263831208247)
                ·
                  refine ⟨3273760953622895746812371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182507302415263831208247 3273760953622895746812371)
                  ·
                    refine ⟨4910641430434343620218557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3273760953622895746812371 4910641430434343620218557)
                    ·
                      refine ⟨1841490536412878857581959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4910641430434343620218557 1841490536412878857581959)
                      ·
                        rfl

theorem cell23_3586290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_3586290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586290 prefixEnd_3586290 := by exact prefixLift 3586290
  have htrace : WordTrace (prefixWord ++ tailWord_3586290) baseStart_3586290 baseEnd_3586290 := by
    simpa [prefixWord, tailWord_3586290, baseEnd_3586290] using wordTrace_append hprefix tailTrace_3586290
  have hstable : (prefixWord ++ tailWord_3586290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586290).length < 2 ^ (prefixWord ++ tailWord_3586290).sum := by decide
  have hdescent : baseEnd_3586290 < baseStart_3586290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586313 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 3, 2, 2]
def baseStart_3586313 : Nat := 118140960795 + 3586313 * 2 ^ 59
def prefixEnd_3586313 : Nat := 4983230072969 + 3 ^ 40 * 3586313 * 2
def baseEnd_3586313 : Nat := 1841502346467932267594353

theorem tailTrace_3586313 : CollatzResearch.WordTrace tailWord_3586313 prefixEnd_3586313 1841502346467932267594353 := by
  unfold tailWord_3586313
  simp only [CollatzResearch.WordTrace]
  refine ⟨130803581056407969342411593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87202387370938646228274395 130803581056407969342411593)
  ·
    refine ⟨98102685792305977006808695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130803581056407969342411593 98102685792305977006808695)
    ·
      refine ⟨147154028688458965510213043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98102685792305977006808695 147154028688458965510213043)
      ·
        refine ⟨220731043032688448265319565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147154028688458965510213043 220731043032688448265319565)
        ·
          refine ⟨82774141137258168099494837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220731043032688448265319565 82774141137258168099494837)
          ·
            refine ⟨7760075731617953259327641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82774141137258168099494837 7760075731617953259327641)
            ·
              refine ⟨5820056798713464944495731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760075731617953259327641 5820056798713464944495731)
              ·
                refine ⟨8730085198070197416743597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5820056798713464944495731 8730085198070197416743597)
                ·
                  refine ⟨3273781949276324031278849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8730085198070197416743597 3273781949276324031278849)
                  ·
                    refine ⟨2455336461957243023459137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3273781949276324031278849 2455336461957243023459137)
                    ·
                      refine ⟨1841502346467932267594353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455336461957243023459137 1841502346467932267594353)
                      ·
                        rfl

theorem cell23_3586313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 2, 2].length) (baseStart_3586313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586313 prefixEnd_3586313 := by exact prefixLift 3586313
  have htrace : WordTrace (prefixWord ++ tailWord_3586313) baseStart_3586313 baseEnd_3586313 := by
    simpa [prefixWord, tailWord_3586313, baseEnd_3586313] using wordTrace_append hprefix tailTrace_3586313
  have hstable : (prefixWord ++ tailWord_3586313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586313).length < 2 ^ (prefixWord ++ tailWord_3586313).sum := by decide
  have hdescent : baseEnd_3586313 < baseStart_3586313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586336 : List Nat := [2, 1, 1, 5, 2, 3, 2, 7]
def baseStart_3586336 : Nat := 118140960795 + 3586336 * 2 ^ 59
def prefixEnd_3586336 : Nat := 4983230072969 + 3 ^ 40 * 3586336 * 2
def baseEnd_3586336 : Nat := 68204228019369839911361

theorem tailTrace_3586336 : CollatzResearch.WordTrace tailWord_3586336 prefixEnd_3586336 68204228019369839911361 := by
  unfold tailWord_3586336
  simp only [CollatzResearch.WordTrace]
  refine ⟨65402209967662322135249431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87202946623549762846999241 65402209967662322135249431)
  ·
    refine ⟨98103314951493483202874147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65402209967662322135249431 98103314951493483202874147)
    ·
      refine ⟨147154972427240224804311221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98103314951493483202874147 147154972427240224804311221)
      ·
        refine ⟨13795778665053771075404177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147154972427240224804311221 13795778665053771075404177)
        ·
          refine ⟨10346833998790328306553133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13795778665053771075404177 10346833998790328306553133)
          ·
            refine ⟨3880062749546373114957425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10346833998790328306553133 3880062749546373114957425)
            ·
              refine ⟨2910047062159779836218069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880062749546373114957425 2910047062159779836218069)
              ·
                refine ⟨68204228019369839911361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2910047062159779836218069 68204228019369839911361)
                ·
                  rfl

theorem cell23_3586336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 7].length) (baseStart_3586336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586336 prefixEnd_3586336 := by exact prefixLift 3586336
  have htrace : WordTrace (prefixWord ++ tailWord_3586336) baseStart_3586336 baseEnd_3586336 := by
    simpa [prefixWord, tailWord_3586336, baseEnd_3586336] using wordTrace_append hprefix tailTrace_3586336
  have hstable : (prefixWord ++ tailWord_3586336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586336).length < 2 ^ (prefixWord ++ tailWord_3586336).sum := by decide
  have hdescent : baseEnd_3586336 < baseStart_3586336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586419 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 3]
def baseStart_3586419 : Nat := 118140960795 + 3586419 * 2 ^ 59
def prefixEnd_3586419 : Nat := 4983230072969 + 3 ^ 40 * 3586419 * 2
def baseEnd_3586419 : Nat := 1841556775417308852868865

theorem tailTrace_3586419 : CollatzResearch.WordTrace tailWord_3586419 prefixEnd_3586419 1841556775417308852868865 := by
  unfold tailWord_3586419
  simp only [CollatzResearch.WordTrace]
  refine ⟨130807447194023949445770311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87204964796015966297180207 130807447194023949445770311)
  ·
    refine ⟨196211170791035924168655467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130807447194023949445770311 196211170791035924168655467)
    ·
      refine ⟨294316756186553886252983201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196211170791035924168655467 294316756186553886252983201)
      ·
        refine ⟨220737567139915414689737401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294316756186553886252983201 220737567139915414689737401)
        ·
          refine ⟨165553175354936561017303051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220737567139915414689737401 165553175354936561017303051)
          ·
            refine ⟨248329763032404841525954577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165553175354936561017303051 248329763032404841525954577)
            ·
              refine ⟨186247322274303631144465933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248329763032404841525954577 186247322274303631144465933)
              ·
                refine ⟨69842745852863861679174725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186247322274303631144465933 69842745852863861679174725)
                ·
                  refine ⟨13095514847411974064845261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69842745852863861679174725 13095514847411974064845261)
                  ·
                    refine ⟨4910818067779490274316973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13095514847411974064845261 4910818067779490274316973)
                    ·
                      refine ⟨1841556775417308852868865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4910818067779490274316973 1841556775417308852868865)
                      ·
                        rfl

theorem cell23_3586419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_3586419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586419 prefixEnd_3586419 := by exact prefixLift 3586419
  have htrace : WordTrace (prefixWord ++ tailWord_3586419) baseStart_3586419 baseEnd_3586419 := by
    simpa [prefixWord, tailWord_3586419, baseEnd_3586419] using wordTrace_append hprefix tailTrace_3586419
  have hstable : (prefixWord ++ tailWord_3586419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586419).length < 2 ^ (prefixWord ++ tailWord_3586419).sum := by decide
  have hdescent : baseEnd_3586419 < baseStart_3586419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586436 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_3586436 : Nat := 118140960795 + 3586436 * 2 ^ 59
def prefixEnd_3586436 : Nat := 4983230072969 + 3 ^ 40 * 3586436 * 2
def baseEnd_3586436 : Nat := 1841565504588435286356287

theorem tailTrace_3586436 : CollatzResearch.WordTrace tailWord_3586436 prefixEnd_3586436 1841565504588435286356287 := by
  unfold tailWord_3586436
  simp only [CollatzResearch.WordTrace]
  refine ⟨65404033617481180674569581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87205378156641574232759441 65404033617481180674569581)
  ·
    refine ⟨24526512606555442752963593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65404033617481180674569581 24526512606555442752963593)
    ·
      refine ⟨18394884454916582064722695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24526512606555442752963593 18394884454916582064722695)
      ·
        refine ⟨27592326682374873097084043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18394884454916582064722695 27592326682374873097084043)
        ·
          refine ⟨41388490023562309645626065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27592326682374873097084043 41388490023562309645626065)
          ·
            refine ⟨31041367517671732234219549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41388490023562309645626065 31041367517671732234219549)
            ·
              refine ⟨11640512819126899587832331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31041367517671732234219549 11640512819126899587832331)
              ·
                refine ⟨17460769228690349381748497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11640512819126899587832331 17460769228690349381748497)
                ·
                  refine ⟨13095576921517762036311373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17460769228690349381748497 13095576921517762036311373)
                  ·
                    refine ⟨4910841345569160763616765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13095576921517762036311373 4910841345569160763616765)
                    ·
                      refine ⟨1841565504588435286356287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4910841345569160763616765 1841565504588435286356287)
                      ·
                        rfl

theorem cell23_3586436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_3586436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586436 prefixEnd_3586436 := by exact prefixLift 3586436
  have htrace : WordTrace (prefixWord ++ tailWord_3586436) baseStart_3586436 baseEnd_3586436 := by
    simpa [prefixWord, tailWord_3586436, baseEnd_3586436] using wordTrace_append hprefix tailTrace_3586436
  have hstable : (prefixWord ++ tailWord_3586436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586436).length < 2 ^ (prefixWord ++ tailWord_3586436).sum := by decide
  have hdescent : baseEnd_3586436 < baseStart_3586436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586439 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 1, 7]
def baseStart_3586439 : Nat := 118140960795 + 3586439 * 2 ^ 59
def prefixEnd_3586439 : Nat := 4983230072969 + 3 ^ 40 * 3586439 * 2
def baseEnd_3586439 : Nat := 613855681676799591539591

theorem tailTrace_3586439 : CollatzResearch.WordTrace tailWord_3586439 prefixEnd_3586439 613855681676799591539591 := by
  unfold tailWord_3586439
  simp only [CollatzResearch.WordTrace]
  refine ⟨130808176653951492861498371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87205451102634328574332247 130808176653951492861498371)
  ·
    refine ⟨196212264980927239292247557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130808176653951492861498371 196212264980927239292247557)
    ·
      refine ⟨36789799683923857367296417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196212264980927239292247557 36789799683923857367296417)
      ·
        refine ⟨27592349762942893025472313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36789799683923857367296417 27592349762942893025472313)
        ·
          refine ⟨20694262322207169769104235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27592349762942893025472313 20694262322207169769104235)
          ·
            refine ⟨31041393483310754653656353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20694262322207169769104235 31041393483310754653656353)
            ·
              refine ⟨23281045112483065990242265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31041393483310754653656353 23281045112483065990242265)
              ·
                refine ⟨17460783834362299492681699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23281045112483065990242265 17460783834362299492681699)
                ·
                  refine ⟨26191175751543449239022549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17460783834362299492681699 26191175751543449239022549)
                  ·
                    refine ⟨613855681676799591539591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26191175751543449239022549 613855681676799591539591)
                    ·
                      rfl

theorem cell23_3586439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_3586439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586439 prefixEnd_3586439 := by exact prefixLift 3586439
  have htrace : WordTrace (prefixWord ++ tailWord_3586439) baseStart_3586439 baseEnd_3586439 := by
    simpa [prefixWord, tailWord_3586439, baseEnd_3586439] using wordTrace_append hprefix tailTrace_3586439
  have hstable : (prefixWord ++ tailWord_3586439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586439).length < 2 ^ (prefixWord ++ tailWord_3586439).sum := by decide
  have hdescent : baseEnd_3586439 < baseStart_3586439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586456 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 1, 7]
def baseStart_3586456 : Nat := 118140960795 + 3586456 * 2 ^ 59
def prefixEnd_3586456 : Nat := 4983230072969 + 3 ^ 40 * 3586456 * 2
def baseEnd_3586456 : Nat := 613858591400508402702065

theorem tailTrace_3586456 : CollatzResearch.WordTrace tailWord_3586456 prefixEnd_3586456 613858591400508402702065 := by
  unfold tailWord_3586456
  simp only [CollatzResearch.WordTrace]
  refine ⟨65404398347444952382433611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87205864463259936509911481 65404398347444952382433611)
  ·
    refine ⟨98106597521167428573650417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65404398347444952382433611 98106597521167428573650417)
    ·
      refine ⟨73579948140875571430237813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98106597521167428573650417 73579948140875571430237813)
      ·
        refine ⟨6898120138207084821584795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73579948140875571430237813 6898120138207084821584795)
        ·
          refine ⟨10347180207310627232377193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6898120138207084821584795 10347180207310627232377193)
          ·
            refine ⟨7760385155482970424282895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10347180207310627232377193 7760385155482970424282895)
            ·
              refine ⟨11640577733224455636424343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7760385155482970424282895 11640577733224455636424343)
              ·
                refine ⟨17460866599836683454636515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11640577733224455636424343 17460866599836683454636515)
                ·
                  refine ⟨26191299899755025181954773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17460866599836683454636515 26191299899755025181954773)
                  ·
                    refine ⟨613858591400508402702065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26191299899755025181954773 613858591400508402702065)
                    ·
                      rfl

theorem cell23_3586456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_3586456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586456 prefixEnd_3586456 := by exact prefixLift 3586456
  have htrace : WordTrace (prefixWord ++ tailWord_3586456) baseStart_3586456 baseEnd_3586456 := by
    simpa [prefixWord, tailWord_3586456, baseEnd_3586456] using wordTrace_append hprefix tailTrace_3586456
  have hstable : (prefixWord ++ tailWord_3586456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586456).length < 2 ^ (prefixWord ++ tailWord_3586456).sum := by decide
  have hdescent : baseEnd_3586456 < baseStart_3586456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586493 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_3586493 : Nat := 118140960795 + 3586493 * 2 ^ 59
def prefixEnd_3586493 : Nat := 4983230072969 + 3 ^ 40 * 3586493 * 2
def baseEnd_3586493 : Nat := 1841594772985741563343525

theorem tailTrace_3586493 : CollatzResearch.WordTrace tailWord_3586493 prefixEnd_3586493 1841594772985741563343525 := by
  unfold tailWord_3586493
  simp only [CollatzResearch.WordTrace]
  refine ⟨130810146195755860083964133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87206764130503906722642755 130810146195755860083964133)
  ·
    refine ⟨24526902411704223765743275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130810146195755860083964133 24526902411704223765743275)
    ·
      refine ⟨36790353617556335648614913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24526902411704223765743275 36790353617556335648614913)
      ·
        refine ⟨27592765213167251736461185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36790353617556335648614913 27592765213167251736461185)
        ·
          refine ⟨20694573909875438802345889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27592765213167251736461185 20694573909875438802345889)
          ·
            refine ⟨15520930432406579101759417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20694573909875438802345889 15520930432406579101759417)
            ·
              refine ⟨11640697824304934326319563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15520930432406579101759417 11640697824304934326319563)
              ·
                refine ⟨17461046736457401489479345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11640697824304934326319563 17461046736457401489479345)
                ·
                  refine ⟨13095785052343051117109509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17461046736457401489479345 13095785052343051117109509)
                  ·
                    refine ⟨2455459697314322084458033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13095785052343051117109509 2455459697314322084458033)
                    ·
                      refine ⟨1841594772985741563343525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455459697314322084458033 1841594772985741563343525)
                      ·
                        rfl

theorem cell23_3586493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_3586493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586493 prefixEnd_3586493 := by exact prefixLift 3586493
  have htrace : WordTrace (prefixWord ++ tailWord_3586493) baseStart_3586493 baseEnd_3586493 := by
    simpa [prefixWord, tailWord_3586493, baseEnd_3586493] using wordTrace_append hprefix tailTrace_3586493
  have hstable : (prefixWord ++ tailWord_3586493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586493).length < 2 ^ (prefixWord ++ tailWord_3586493).sum := by decide
  have hdescent : baseEnd_3586493 < baseStart_3586493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586516 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 8]
def baseStart_3586516 : Nat := 118140960795 + 3586516 * 2 ^ 59
def prefixEnd_3586516 : Nat := 4983230072969 + 3 ^ 40 * 3586516 * 2
def baseEnd_3586516 : Nat := 204622953671199441483991

theorem tailTrace_3586516 : CollatzResearch.WordTrace tailWord_3586516 prefixEnd_3586516 204622953671199441483991 := by
  unfold tailWord_3586516
  simp only [CollatzResearch.WordTrace]
  refine ⟨65405492537336267506025701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87207323383115023341367601 65405492537336267506025701)
  ·
    refine ⟨12263529850750550157379819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65405492537336267506025701 12263529850750550157379819)
    ·
      refine ⟨18395294776125825236069729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12263529850750550157379819 18395294776125825236069729)
      ·
        refine ⟨13796471082094368927052297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18395294776125825236069729 13796471082094368927052297)
        ·
          refine ⟨10347353311570776695289223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13796471082094368927052297 10347353311570776695289223)
          ·
            refine ⟨15521029967356165042933835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10347353311570776695289223 15521029967356165042933835)
            ·
              refine ⟨23281544951034247564400753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15521029967356165042933835 23281544951034247564400753)
              ·
                refine ⟨17461158713275685673300565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23281544951034247564400753 17461158713275685673300565)
                ·
                  refine ⟨204622953671199441483991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17461158713275685673300565 204622953671199441483991)
                  ·
                    rfl

theorem cell23_3586516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_3586516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586516 prefixEnd_3586516 := by exact prefixLift 3586516
  have htrace : WordTrace (prefixWord ++ tailWord_3586516) baseStart_3586516 baseEnd_3586516 := by
    simpa [prefixWord, tailWord_3586516, baseEnd_3586516] using wordTrace_append hprefix tailTrace_3586516
  have hstable : (prefixWord ++ tailWord_3586516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586516).length < 2 ^ (prefixWord ++ tailWord_3586516).sum := by decide
  have hdescent : baseEnd_3586516 < baseStart_3586516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586570 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_3586570 : Nat := 118140960795 + 3586570 * 2 ^ 59
def prefixEnd_3586570 : Nat := 4983230072969 + 3 ^ 40 * 3586570 * 2
def baseEnd_3586570 : Nat := 1841634310996137762080671

theorem tailTrace_3586570 : CollatzResearch.WordTrace tailWord_3586570 prefixEnd_3586570 1841634310996137762080671 := by
  unfold tailWord_3586570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32703238654119225558629291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87208636410984601489678109 32703238654119225558629291)
  ·
    refine ⟨49054857981178838337943937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32703238654119225558629291 49054857981178838337943937)
    ·
      refine ⟨36791143485884128753457953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49054857981178838337943937 36791143485884128753457953)
      ·
        refine ⟨27593357614413096565093465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36791143485884128753457953 27593357614413096565093465)
        ·
          refine ⟨20695018210809822423820099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27593357614413096565093465 20695018210809822423820099)
          ·
            refine ⟨31042527316214733635730149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20695018210809822423820099 31042527316214733635730149)
            ·
              refine ⟨5820473871790262556699403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31042527316214733635730149 5820473871790262556699403)
              ·
                refine ⟨8730710807685393835049105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5820473871790262556699403 8730710807685393835049105)
                ·
                  refine ⟨6548033105764045376286829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8730710807685393835049105 6548033105764045376286829)
                  ·
                    refine ⟨2455512414661517016107561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6548033105764045376286829 2455512414661517016107561)
                    ·
                      refine ⟨1841634310996137762080671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455512414661517016107561 1841634310996137762080671)
                      ·
                        rfl

theorem cell23_3586570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_3586570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586570 prefixEnd_3586570 := by exact prefixLift 3586570
  have htrace : WordTrace (prefixWord ++ tailWord_3586570) baseStart_3586570 baseEnd_3586570 := by
    simpa [prefixWord, tailWord_3586570, baseEnd_3586570] using wordTrace_append hprefix tailTrace_3586570
  have hstable : (prefixWord ++ tailWord_3586570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586570).length < 2 ^ (prefixWord ++ tailWord_3586570).sum := by decide
  have hdescent : baseEnd_3586570 < baseStart_3586570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586613 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_3586613 : Nat := 118140960795 + 3586613 * 2 ^ 59
def prefixEnd_3586613 : Nat := 4983230072969 + 3 ^ 40 * 3586613 * 2
def baseEnd_3586613 : Nat := 1841656390664281093842973

theorem tailTrace_3586613 : CollatzResearch.WordTrace tailWord_3586613 prefixEnd_3586613 1841656390664281093842973 := by
  unfold tailWord_3586613
  simp only [CollatzResearch.WordTrace]
  refine ⟨130814522955321120578332493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87209681970214080385554995 130814522955321120578332493)
  ·
    refine ⟨49055446108245420216874685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130814522955321120578332493 49055446108245420216874685)
    ·
      refine ⟨18395792290592032581328007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49055446108245420216874685 18395792290592032581328007)
      ·
        refine ⟨27593688435888048871992011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18395792290592032581328007 27593688435888048871992011)
        ·
          refine ⟨41390532653832073307988017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27593688435888048871992011 41390532653832073307988017)
          ·
            refine ⟨31042899490374054980991013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41390532653832073307988017 31042899490374054980991013)
            ·
              refine ⟨5820543654445135308935815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31042899490374054980991013 5820543654445135308935815)
              ·
                refine ⟨8730815481667702963403723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5820543654445135308935815 8730815481667702963403723)
                ·
                  refine ⟨13096223222501554445105585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730815481667702963403723 13096223222501554445105585)
                  ·
                    refine ⟨9822167416876165833829189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13096223222501554445105585 9822167416876165833829189)
                    ·
                      refine ⟨1841656390664281093842973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9822167416876165833829189 1841656390664281093842973)
                      ·
                        rfl

theorem cell23_3586613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_3586613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586613 prefixEnd_3586613 := by exact prefixLift 3586613
  have htrace : WordTrace (prefixWord ++ tailWord_3586613) baseStart_3586613 baseEnd_3586613 := by
    simpa [prefixWord, tailWord_3586613, baseEnd_3586613] using wordTrace_append hprefix tailTrace_3586613
  have hstable : (prefixWord ++ tailWord_3586613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586613).length < 2 ^ (prefixWord ++ tailWord_3586613).sum := by decide
  have hdescent : baseEnd_3586613 < baseStart_3586613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586628 : List Nat := [2, 3, 5, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3586628 : Nat := 118140960795 + 3586628 * 2 ^ 59
def prefixEnd_3586628 : Nat := 4983230072969 + 3 ^ 40 * 3586628 * 2
def baseEnd_3586628 : Nat := 1841664092874098535155405

theorem tailTrace_3586628 : CollatzResearch.WordTrace tailWord_3586628 prefixEnd_3586628 1841664092874098535155405 := by
  unfold tailWord_3586628
  simp only [CollatzResearch.WordTrace]
  refine ⟨65407535025133389070064269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87210046700177852093419025 65407535025133389070064269)
  ·
    refine ⟨24527825634425020901274101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65407535025133389070064269 24527825634425020901274101)
    ·
      refine ⟨2299483653227345709494447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24527825634425020901274101 2299483653227345709494447)
      ·
        refine ⟨3449225479841018564241671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299483653227345709494447 3449225479841018564241671)
        ·
          refine ⟨5173838219761527846362507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449225479841018564241671 5173838219761527846362507)
          ·
            refine ⟨7760757329642291769543761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173838219761527846362507 7760757329642291769543761)
            ·
              refine ⟨5820567997231718827157821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760757329642291769543761 5820567997231718827157821)
              ·
                refine ⟨2182712998961894560184183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820567997231718827157821 2182712998961894560184183)
                ·
                  refine ⟨3274069498442841840276275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182712998961894560184183 3274069498442841840276275)
                  ·
                    refine ⟨4911104247664262760414413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3274069498442841840276275 4911104247664262760414413)
                    ·
                      refine ⟨1841664092874098535155405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4911104247664262760414413 1841664092874098535155405)
                      ·
                        rfl

theorem cell23_3586628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3586628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586628 prefixEnd_3586628 := by exact prefixLift 3586628
  have htrace : WordTrace (prefixWord ++ tailWord_3586628) baseStart_3586628 baseEnd_3586628 := by
    simpa [prefixWord, tailWord_3586628, baseEnd_3586628] using wordTrace_append hprefix tailTrace_3586628
  have hstable : (prefixWord ++ tailWord_3586628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586628).length < 2 ^ (prefixWord ++ tailWord_3586628).sum := by decide
  have hdescent : baseEnd_3586628 < baseStart_3586628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586634 : List Nat := [3, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_3586634 : Nat := 118140960795 + 3586634 * 2 ^ 59
def prefixEnd_3586634 : Nat := 4983230072969 + 3 ^ 40 * 3586634 * 2
def baseEnd_3586634 : Nat := 1841667173758025511680377

theorem tailTrace_3586634 : CollatzResearch.WordTrace tailWord_3586634 prefixEnd_3586634 1841667173758025511680377 := by
  unfold tailWord_3586634
  simp only [CollatzResearch.WordTrace]
  refine ⟨32703822222061260291211739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87210192592163360776564637 32703822222061260291211739)
  ·
    refine ⟨49055733333091890436817609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32703822222061260291211739 49055733333091890436817609)
    ·
      refine ⟨36791799999818917827613207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49055733333091890436817609 36791799999818917827613207)
      ·
        refine ⟨55187699999728376741419811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36791799999818917827613207 55187699999728376741419811)
        ·
          refine ⟨82781549999592565112129717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55187699999728376741419811 82781549999592565112129717)
          ·
            refine ⟨7760770312461802979262161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82781549999592565112129717 7760770312461802979262161)
            ·
              refine ⟨5820577734346352234446621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760770312461802979262161 5820577734346352234446621)
              ·
                refine ⟨2182716650379882087917483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820577734346352234446621 2182716650379882087917483)
                ·
                  refine ⟨3274074975569823131876225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182716650379882087917483 3274074975569823131876225)
                  ·
                    refine ⟨2455556231677367348907169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274074975569823131876225 2455556231677367348907169)
                    ·
                      refine ⟨1841667173758025511680377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455556231677367348907169 1841667173758025511680377)
                      ·
                        rfl

theorem cell23_3586634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_3586634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586634 prefixEnd_3586634 := by exact prefixLift 3586634
  have htrace : WordTrace (prefixWord ++ tailWord_3586634) baseStart_3586634 baseEnd_3586634 := by
    simpa [prefixWord, tailWord_3586634, baseEnd_3586634] using wordTrace_append hprefix tailTrace_3586634
  have hstable : (prefixWord ++ tailWord_3586634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586634).length < 2 ^ (prefixWord ++ tailWord_3586634).sum := by decide
  have hdescent : baseEnd_3586634 < baseStart_3586634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586637 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3586637 : Nat := 118140960795 + 3586637 * 2 ^ 59
def prefixEnd_3586637 : Nat := 4983230072969 + 3 ^ 40 * 3586637 * 2
def baseEnd_3586637 : Nat := 1841668714199988999942863

theorem tailTrace_3586637 : CollatzResearch.WordTrace tailWord_3586637 prefixEnd_3586637 1841668714199988999942863 := by
  unfold tailWord_3586637
  simp only [CollatzResearch.WordTrace]
  refine ⟨130815398307234172677206165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87210265538156115118137443 130815398307234172677206165)
  ·
    refine ⟨6131971795651601844244039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130815398307234172677206165 6131971795651601844244039)
    ·
      refine ⟨9197957693477402766366059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6131971795651601844244039 9197957693477402766366059)
      ·
        refine ⟨13796936540216104149549089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197957693477402766366059 13796936540216104149549089)
        ·
          refine ⟨10347702405162078112161817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13796936540216104149549089 10347702405162078112161817)
          ·
            refine ⟨7760776803871558584121363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10347702405162078112161817 7760776803871558584121363)
            ·
              refine ⟨11641165205807337876182045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7760776803871558584121363 11641165205807337876182045)
              ·
                refine ⟨4365436952177751703568267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11641165205807337876182045 4365436952177751703568267)
                ·
                  refine ⟨6548155428266627555352401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365436952177751703568267 6548155428266627555352401)
                  ·
                    refine ⟨4911116571199970666514301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548155428266627555352401 4911116571199970666514301)
                    ·
                      refine ⟨1841668714199988999942863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4911116571199970666514301 1841668714199988999942863)
                      ·
                        rfl

theorem cell23_3586637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3586637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586637 prefixEnd_3586637 := by exact prefixLift 3586637
  have htrace : WordTrace (prefixWord ++ tailWord_3586637) baseStart_3586637 baseEnd_3586637 := by
    simpa [prefixWord, tailWord_3586637, baseEnd_3586637] using wordTrace_append hprefix tailTrace_3586637
  have hstable : (prefixWord ++ tailWord_3586637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586637).length < 2 ^ (prefixWord ++ tailWord_3586637).sum := by decide
  have hdescent : baseEnd_3586637 < baseStart_3586637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586654 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3586654 : Nat := 118140960795 + 3586654 * 2 ^ 59
def prefixEnd_3586654 : Nat := 4983230072969 + 3 ^ 40 * 3586654 * 2
def baseEnd_3586654 : Nat := 1841677443371115433430285

theorem tailTrace_3586654 : CollatzResearch.WordTrace tailWord_3586654 prefixEnd_3586654 1841677443371115433430285 := by
  unfold tailWord_3586654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352002293521573072571877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87210678898781723053716677 16352002293521573072571877)
  ·
    refine ⟨3066000430035294951107227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16352002293521573072571877 3066000430035294951107227)
    ·
      refine ⟨4599000645052942426660841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066000430035294951107227 4599000645052942426660841)
      ·
        refine ⟨3449250483789706819995631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4599000645052942426660841 3449250483789706819995631)
        ·
          refine ⟨5173875725684560229993447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449250483789706819995631 5173875725684560229993447)
          ·
            refine ⟨7760813588526840344990171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173875725684560229993447 7760813588526840344990171)
            ·
              refine ⟨11641220382790260517485257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7760813588526840344990171 11641220382790260517485257)
              ·
                refine ⟨8730915287092695388113943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11641220382790260517485257 8730915287092695388113943)
                ·
                  refine ⟨13096372930639043082170915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730915287092695388113943 13096372930639043082170915)
                  ·
                    refine ⟨19644559395958564623256373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13096372930639043082170915 19644559395958564623256373)
                    ·
                      refine ⟨1841677443371115433430285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19644559395958564623256373 1841677443371115433430285)
                      ·
                        rfl

theorem cell23_3586654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3586654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586654 prefixEnd_3586654 := by exact prefixLift 3586654
  have htrace : WordTrace (prefixWord ++ tailWord_3586654) baseStart_3586654 baseEnd_3586654 := by
    simpa [prefixWord, tailWord_3586654, baseEnd_3586654] using wordTrace_append hprefix tailTrace_3586654
  have hstable : (prefixWord ++ tailWord_3586654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586654).length < 2 ^ (prefixWord ++ tailWord_3586654).sum := by decide
  have hdescent : baseEnd_3586654 < baseStart_3586654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586656 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_3586656 : Nat := 118140960795 + 3586656 * 2 ^ 59
def prefixEnd_3586656 : Nat := 4983230072969 + 3 ^ 40 * 3586656 * 2
def baseEnd_3586656 : Nat := 1841678470332424425605275

theorem tailTrace_3586656 : CollatzResearch.WordTrace tailWord_3586656 prefixEnd_3586656 1841678470332424425605275 := by
  unfold tailWord_3586656
  simp only [CollatzResearch.WordTrace]
  refine ⟨65408045647082669461073911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87210727529443559281431881 65408045647082669461073911)
  ·
    refine ⟨98112068470624004191610867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65408045647082669461073911 98112068470624004191610867)
    ·
      refine ⟨147168102705936006287416301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98112068470624004191610867 147168102705936006287416301)
      ·
        refine ⟨55188038514726002357781113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147168102705936006287416301 55188038514726002357781113)
        ·
          refine ⟨41391028886044501768335835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55188038514726002357781113 41391028886044501768335835)
          ·
            refine ⟨62086543329066752652503753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41391028886044501768335835 62086543329066752652503753)
            ·
              refine ⟨46564907496800064489377815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62086543329066752652503753 46564907496800064489377815)
              ·
                refine ⟨69847361245200096734066723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46564907496800064489377815 69847361245200096734066723)
                ·
                  refine ⟨104771041867800145101100085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69847361245200096734066723 104771041867800145101100085)
                  ·
                    refine ⟨9822285175106263603228133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104771041867800145101100085 9822285175106263603228133)
                    ·
                      refine ⟨1841678470332424425605275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9822285175106263603228133 1841678470332424425605275)
                      ·
                        rfl

theorem cell23_3586656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_3586656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586656 prefixEnd_3586656 := by exact prefixLift 3586656
  have htrace : WordTrace (prefixWord ++ tailWord_3586656) baseStart_3586656 baseEnd_3586656 := by
    simpa [prefixWord, tailWord_3586656, baseEnd_3586656] using wordTrace_append hprefix tailTrace_3586656
  have hstable : (prefixWord ++ tailWord_3586656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586656).length < 2 ^ (prefixWord ++ tailWord_3586656).sum := by decide
  have hdescent : baseEnd_3586656 < baseStart_3586656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586693 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_3586693 : Nat := 118140960795 + 3586693 * 2 ^ 59
def prefixEnd_3586693 : Nat := 4983230072969 + 3 ^ 40 * 3586693 * 2
def baseEnd_3586693 : Nat := 1841697469116640780842605

theorem tailTrace_3586693 : CollatzResearch.WordTrace tailWord_3586693 prefixEnd_3586693 1841697469116640780842605 := by
  unfold tailWord_3586693
  simp only [CollatzResearch.WordTrace]
  refine ⟨130817440795031294241244733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87211627196687529494163155 130817440795031294241244733)
  ·
    refine ⟨49056540298136735340466775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130817440795031294241244733 49056540298136735340466775)
    ·
      refine ⟨73584810447205103010700163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49056540298136735340466775 73584810447205103010700163)
      ·
        refine ⟨110377215670807654516050245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73584810447205103010700163 110377215670807654516050245)
        ·
          refine ⟨20695727938276435221759421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110377215670807654516050245 20695727938276435221759421)
          ·
            refine ⟨7760897976853663208159783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20695727938276435221759421 7760897976853663208159783)
            ·
              refine ⟨11641346965280494812239675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7760897976853663208159783 11641346965280494812239675)
              ·
                refine ⟨17462020447920742218359513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11641346965280494812239675 17462020447920742218359513)
                ·
                  refine ⟨13096515335940556663769635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17462020447920742218359513 13096515335940556663769635)
                  ·
                    refine ⟨19644773003910834995654453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13096515335940556663769635 19644773003910834995654453)
                    ·
                      refine ⟨1841697469116640780842605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19644773003910834995654453 1841697469116640780842605)
                      ·
                        rfl

theorem cell23_3586693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_3586693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586693 prefixEnd_3586693 := by exact prefixLift 3586693
  have htrace : WordTrace (prefixWord ++ tailWord_3586693) baseStart_3586693 baseEnd_3586693 := by
    simpa [prefixWord, tailWord_3586693, baseEnd_3586693] using wordTrace_append hprefix tailTrace_3586693
  have hstable : (prefixWord ++ tailWord_3586693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586693).length < 2 ^ (prefixWord ++ tailWord_3586693).sum := by decide
  have hdescent : baseEnd_3586693 < baseStart_3586693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586736 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_3586736 : Nat := 118140960795 + 3586736 * 2 ^ 59
def prefixEnd_3586736 : Nat := 4983230072969 + 3 ^ 40 * 3586736 * 2
def baseEnd_3586736 : Nat := 1841719548784784112604907

theorem tailTrace_3586736 : CollatzResearch.WordTrace tailWord_3586736 prefixEnd_3586736 1841719548784784112604907 := by
  unfold tailWord_3586736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65409504566937756292530031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87212672755917008390040041 65409504566937756292530031)
  ·
    refine ⟨98114256850406634438795047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65409504566937756292530031 98114256850406634438795047)
    ·
      refine ⟨147171385275609951658192571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98114256850406634438795047 147171385275609951658192571)
      ·
        refine ⟨220757077913414927487288857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147171385275609951658192571 220757077913414927487288857)
        ·
          refine ⟨165567808435061195615466643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220757077913414927487288857 165567808435061195615466643)
          ·
            refine ⟨248351712652591793423199965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165567808435061195615466643 248351712652591793423199965)
            ·
              refine ⟨93131892244721922533699987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248351712652591793423199965 93131892244721922533699987)
              ·
                refine ⟨139697838367082883800549981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93131892244721922533699987 139697838367082883800549981)
                ·
                  refine ⟨52386689387656081425206243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139697838367082883800549981 52386689387656081425206243)
                  ·
                    refine ⟨78580034081484122137809365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52386689387656081425206243 78580034081484122137809365)
                    ·
                      refine ⟨1841719548784784112604907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78580034081484122137809365 1841719548784784112604907)
                      ·
                        rfl

theorem cell23_3586736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_3586736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586736 prefixEnd_3586736 := by exact prefixLift 3586736
  have htrace : WordTrace (prefixWord ++ tailWord_3586736) baseStart_3586736 baseEnd_3586736 := by
    simpa [prefixWord, tailWord_3586736, baseEnd_3586736] using wordTrace_append hprefix tailTrace_3586736
  have hstable : (prefixWord ++ tailWord_3586736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586736).length < 2 ^ (prefixWord ++ tailWord_3586736).sum := by decide
  have hdescent : baseEnd_3586736 < baseStart_3586736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586764 : List Nat := [2, 2, 1, 5, 1, 3, 2, 2, 5]
def baseStart_3586764 : Nat := 118140960795 + 3586764 * 2 ^ 59
def prefixEnd_3586764 : Nat := 4983230072969 + 3 ^ 40 * 3586764 * 2
def baseEnd_3586764 : Nat := 204637102915901111450531

theorem tailTrace_3586764 : CollatzResearch.WordTrace tailWord_3586764 prefixEnd_3586764 204637102915901111450531 := by
  unfold tailWord_3586764
  simp only [CollatzResearch.WordTrace]
  refine ⟨65410015188887036683539673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87213353585182715578052897 65410015188887036683539673)
  ·
    refine ⟨49057511391665277512654755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65410015188887036683539673 49057511391665277512654755)
    ·
      refine ⟨73586267087497916268982133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49057511391665277512654755 73586267087497916268982133)
      ·
        refine ⟨6898712539452929650217075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73586267087497916268982133 6898712539452929650217075)
        ·
          refine ⟨10348068809179394475325613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6898712539452929650217075 10348068809179394475325613)
          ·
            refine ⟨3880525803442272928247105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10348068809179394475325613 3880525803442272928247105)
            ·
              refine ⟨2910394352581704696185329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880525803442272928247105 2910394352581704696185329)
              ·
                refine ⟨2182795764436278522138997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910394352581704696185329 2182795764436278522138997)
                ·
                  refine ⟨204637102915901111450531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2182795764436278522138997 204637102915901111450531)
                  ·
                    rfl

theorem cell23_3586764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_3586764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586764 prefixEnd_3586764 := by exact prefixLift 3586764
  have htrace : WordTrace (prefixWord ++ tailWord_3586764) baseStart_3586764 baseEnd_3586764 := by
    simpa [prefixWord, tailWord_3586764, baseEnd_3586764] using wordTrace_append hprefix tailTrace_3586764
  have hstable : (prefixWord ++ tailWord_3586764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586764).length < 2 ^ (prefixWord ++ tailWord_3586764).sum := by decide
  have hdescent : baseEnd_3586764 < baseStart_3586764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586833 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 5, 5]
def baseStart_3586833 : Nat := 118140960795 + 3586833 * 2 ^ 59
def prefixEnd_3586833 : Nat := 4983230072969 + 3 ^ 40 * 3586833 * 2
def baseEnd_3586833 : Nat := 613923118802756744363987

theorem tailTrace_3586833 : CollatzResearch.WordTrace tailWord_3586833 prefixEnd_3586833 613923118802756744363987 := by
  unfold tailWord_3586833
  simp only [CollatzResearch.WordTrace]
  refine ⟨130822547014524098151341153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87215031343016065434227435 130822547014524098151341153)
  ·
    refine ⟨98116910260893073613505865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130822547014524098151341153 98116910260893073613505865)
    ·
      refine ⟨73587682695669805210129399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98116910260893073613505865 73587682695669805210129399)
      ·
        refine ⟨110381524043504707815194099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73587682695669805210129399 110381524043504707815194099)
        ·
          refine ⟨165572286065257061722791149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110381524043504707815194099 165572286065257061722791149)
          ·
            refine ⟨62089607274471398146046681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165572286065257061722791149 62089607274471398146046681)
            ·
              refine ⟨46567205455853548609535011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62089607274471398146046681 46567205455853548609535011)
              ·
                refine ⟨69850808183780322914302517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46567205455853548609535011 69850808183780322914302517)
                ·
                  refine ⟨6548513267229405273215861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69850808183780322914302517 6548513267229405273215861)
                  ·
                    refine ⟨613923118802756744363987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6548513267229405273215861 613923118802756744363987)
                    ·
                      rfl

theorem cell23_3586833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_3586833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586833 prefixEnd_3586833 := by exact prefixLift 3586833
  have htrace : WordTrace (prefixWord ++ tailWord_3586833) baseStart_3586833 baseEnd_3586833 := by
    simpa [prefixWord, tailWord_3586833, baseEnd_3586833] using wordTrace_append hprefix tailTrace_3586833
  have hstable : (prefixWord ++ tailWord_3586833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586833).length < 2 ^ (prefixWord ++ tailWord_3586833).sum := by decide
  have hdescent : baseEnd_3586833 < baseStart_3586833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586847 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 3]
def baseStart_3586847 : Nat := 118140960795 + 3586847 * 2 ^ 59
def prefixEnd_3586847 : Nat := 4983230072969 + 3 ^ 40 * 3586847 * 2
def baseEnd_3586847 : Nat := 1841776545137433178316897

theorem tailTrace_3586847 : CollatzResearch.WordTrace tailWord_3586847 prefixEnd_3586847 1841776545137433178316897 := by
  unfold tailWord_3586847
  simp only [CollatzResearch.WordTrace]
  refine ⟨130823057636473378542350795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87215371757648919028233863 130823057636473378542350795)
  ·
    refine ⟨196234586454710067813526193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130823057636473378542350795 196234586454710067813526193)
    ·
      refine ⟨147175939841032550860144645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196234586454710067813526193 147175939841032550860144645)
      ·
        refine ⟨27595488720193603286277121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147175939841032550860144645 27595488720193603286277121)
        ·
          refine ⟨20696616540145202464707841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27595488720193603286277121 20696616540145202464707841)
          ·
            refine ⟨15522462405108901848530881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20696616540145202464707841 15522462405108901848530881)
            ·
              refine ⟨11641846803831676386398161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15522462405108901848530881 11641846803831676386398161)
              ·
                refine ⟨8731385102873757289798621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11641846803831676386398161 8731385102873757289798621)
                ·
                  refine ⟨3274269413577658983674483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8731385102873757289798621 3274269413577658983674483)
                  ·
                    refine ⟨4911404120366488475511725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3274269413577658983674483 4911404120366488475511725)
                    ·
                      refine ⟨1841776545137433178316897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4911404120366488475511725 1841776545137433178316897)
                      ·
                        rfl

theorem cell23_3586847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_3586847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586847 prefixEnd_3586847 := by exact prefixLift 3586847
  have htrace : WordTrace (prefixWord ++ tailWord_3586847) baseStart_3586847 baseEnd_3586847 := by
    simpa [prefixWord, tailWord_3586847, baseEnd_3586847] using wordTrace_append hprefix tailTrace_3586847
  have hstable : (prefixWord ++ tailWord_3586847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586847).length < 2 ^ (prefixWord ++ tailWord_3586847).sum := by decide
  have hdescent : baseEnd_3586847 < baseStart_3586847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586858 : List Nat := [3, 1, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3586858 : Nat := 118140960795 + 3586858 * 2 ^ 59
def prefixEnd_3586858 : Nat := 4983230072969 + 3 ^ 40 * 3586858 * 2
def baseEnd_3586858 : Nat := 613927397808210878426449

theorem tailTrace_3586858 : CollatzResearch.WordTrace tailWord_3586858 prefixEnd_3586858 613927397808210878426449 := by
  unfold tailWord_3586858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32705864709858381855250307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87215639226289018280667485 32705864709858381855250307)
  ·
    refine ⟨49058797064787572782875461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32705864709858381855250307 49058797064787572782875461)
    ·
      refine ⟨9198524449647669896789149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49058797064787572782875461 9198524449647669896789149)
      ·
        refine ⟨3449446668617876211295931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9198524449647669896789149 3449446668617876211295931)
        ·
          refine ⟨5174170002926814316943897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449446668617876211295931 5174170002926814316943897)
          ·
            refine ⟨3880627502195110737707923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5174170002926814316943897 3880627502195110737707923)
            ·
              refine ⟨5820941253292666106561885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3880627502195110737707923 5820941253292666106561885)
              ·
                refine ⟨2182852969984749789960707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820941253292666106561885 2182852969984749789960707)
                ·
                  refine ⟨3274279454977124684941061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182852969984749789960707 3274279454977124684941061)
                  ·
                    refine ⟨613927397808210878426449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3274279454977124684941061 613927397808210878426449)
                    ·
                      rfl

theorem cell23_3586858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3586858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586858 prefixEnd_3586858 := by exact prefixLift 3586858
  have htrace : WordTrace (prefixWord ++ tailWord_3586858) baseStart_3586858 baseEnd_3586858 := by
    simpa [prefixWord, tailWord_3586858, baseEnd_3586858] using wordTrace_append hprefix tailTrace_3586858
  have hstable : (prefixWord ++ tailWord_3586858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586858).length < 2 ^ (prefixWord ++ tailWord_3586858).sum := by decide
  have hdescent : baseEnd_3586858 < baseStart_3586858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586874 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2]
def baseStart_3586874 : Nat := 118140960795 + 3586874 * 2 ^ 59
def prefixEnd_3586874 : Nat := 4983230072969 + 3 ^ 40 * 3586874 * 2
def baseEnd_3586874 : Nat := 1841790409115104572679273

theorem tailTrace_3586874 : CollatzResearch.WordTrace tailWord_3586874 prefixEnd_3586874 1841790409115104572679273 := by
  unfold tailWord_3586874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32706010601843890538395919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87216028271583708102389117 32706010601843890538395919)
  ·
    refine ⟨49059015902765835807593879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32706010601843890538395919 49059015902765835807593879)
    ·
      refine ⟨73588523854148753711390819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49059015902765835807593879 73588523854148753711390819)
      ·
        refine ⟨110382785781223130567086229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73588523854148753711390819 110382785781223130567086229)
        ·
          refine ⟨5174193083494834245332167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110382785781223130567086229 5174193083494834245332167)
          ·
            refine ⟨7761289625242251367998251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174193083494834245332167 7761289625242251367998251)
            ·
              refine ⟨11641934437863377051997377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761289625242251367998251 11641934437863377051997377)
              ·
                refine ⟨8731450828397532788998033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11641934437863377051997377 8731450828397532788998033)
                ·
                  refine ⟨6548588121298149591748525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8731450828397532788998033 6548588121298149591748525)
                  ·
                    refine ⟨2455720545486806096905697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6548588121298149591748525 2455720545486806096905697)
                    ·
                      refine ⟨1841790409115104572679273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455720545486806096905697 1841790409115104572679273)
                      ·
                        rfl

theorem cell23_3586874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_3586874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586874 prefixEnd_3586874 := by exact prefixLift 3586874
  have htrace : WordTrace (prefixWord ++ tailWord_3586874) baseStart_3586874 baseEnd_3586874 := by
    simpa [prefixWord, tailWord_3586874, baseEnd_3586874] using wordTrace_append hprefix tailTrace_3586874
  have hstable : (prefixWord ++ tailWord_3586874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586874).length < 2 ^ (prefixWord ++ tailWord_3586874).sum := by decide
  have hdescent : baseEnd_3586874 < baseStart_3586874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586883 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6]
def baseStart_3586883 : Nat := 118140960795 + 3586883 * 2 ^ 59
def prefixEnd_3586883 : Nat := 4983230072969 + 3 ^ 40 * 3586883 * 2
def baseEnd_3586883 : Nat := 1841795030440995037466731

theorem tailTrace_3586883 : CollatzResearch.WordTrace tailWord_3586883 prefixEnd_3586883 1841795030440995037466731 := by
  unfold tailWord_3586883
  simp only [CollatzResearch.WordTrace]
  refine ⟨130824370664342956690661303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87216247109561971127107535 130824370664342956690661303)
  ·
    refine ⟨196236555996514435035991955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130824370664342956690661303 196236555996514435035991955)
    ·
      refine ⟨294354833994771652553987933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196236555996514435035991955 294354833994771652553987933)
      ·
        refine ⟨110383062748039369707745475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294354833994771652553987933 110383062748039369707745475)
        ·
          refine ⟨165574594122059054561618213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110383062748039369707745475 165574594122059054561618213)
          ·
            refine ⟨31045236397886072730303415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165574594122059054561618213 31045236397886072730303415)
            ·
              refine ⟨46567854596829109095455123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31045236397886072730303415 46567854596829109095455123)
              ·
                refine ⟨69851781895243663643182685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46567854596829109095455123 69851781895243663643182685)
                ·
                  refine ⟨26194418210716373866193507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69851781895243663643182685 26194418210716373866193507)
                  ·
                    refine ⟨39291627316074560799290261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26194418210716373866193507 39291627316074560799290261)
                    ·
                      refine ⟨1841795030440995037466731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39291627316074560799290261 1841795030440995037466731)
                      ·
                        rfl

theorem cell23_3586883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_3586883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586883 prefixEnd_3586883 := by exact prefixLift 3586883
  have htrace : WordTrace (prefixWord ++ tailWord_3586883) baseStart_3586883 baseEnd_3586883 := by
    simpa [prefixWord, tailWord_3586883, baseEnd_3586883] using wordTrace_append hprefix tailTrace_3586883
  have hstable : (prefixWord ++ tailWord_3586883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586883).length < 2 ^ (prefixWord ++ tailWord_3586883).sum := by decide
  have hdescent : baseEnd_3586883 < baseStart_3586883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586924 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 3]
def baseStart_3586924 : Nat := 118140960795 + 3586924 * 2 ^ 59
def prefixEnd_3586924 : Nat := 4983230072969 + 3 ^ 40 * 3586924 * 2
def baseEnd_3586924 : Nat := 1841816083147829377054043

theorem tailTrace_3586924 : CollatzResearch.WordTrace tailWord_3586924 prefixEnd_3586924 1841816083147829377054043 := by
  unfold tailWord_3586924
  simp only [CollatzResearch.WordTrace]
  refine ⟨65412933028597210346451913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87217244038129613795269217 65412933028597210346451913)
  ·
    refine ⟨49059699771447907759838935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65412933028597210346451913 49059699771447907759838935)
    ·
      refine ⟨73589549657171861639758403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49059699771447907759838935 73589549657171861639758403)
      ·
        refine ⟨110384324485757792459637605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73589549657171861639758403 110384324485757792459637605)
        ·
          refine ⟨20697060841079586086182051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110384324485757792459637605 20697060841079586086182051)
          ·
            refine ⟨31045591261619379129273077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20697060841079586086182051 31045591261619379129273077)
            ·
              refine ⟨2910524180776816793369351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31045591261619379129273077 2910524180776816793369351)
              ·
                refine ⟨4365786271165225190054027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910524180776816793369351 4365786271165225190054027)
                ·
                  refine ⟨6548679406747837785081041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365786271165225190054027 6548679406747837785081041)
                  ·
                    refine ⟨4911509555060878338810781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6548679406747837785081041 4911509555060878338810781)
                    ·
                      refine ⟨1841816083147829377054043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4911509555060878338810781 1841816083147829377054043)
                      ·
                        rfl

theorem cell23_3586924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_3586924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586924 prefixEnd_3586924 := by exact prefixLift 3586924
  have htrace : WordTrace (prefixWord ++ tailWord_3586924) baseStart_3586924 baseEnd_3586924 := by
    simpa [prefixWord, tailWord_3586924, baseEnd_3586924] using wordTrace_append hprefix tailTrace_3586924
  have hstable : (prefixWord ++ tailWord_3586924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586924).length < 2 ^ (prefixWord ++ tailWord_3586924).sum := by decide
  have hdescent : baseEnd_3586924 < baseStart_3586924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586947 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 5, 3, 2]
def baseStart_3586947 : Nat := 118140960795 + 3586947 * 2 ^ 59
def prefixEnd_3586947 : Nat := 4983230072969 + 3 ^ 40 * 3586947 * 2
def baseEnd_3586947 : Nat := 1841827893202882787066437

theorem tailTrace_3586947 : CollatzResearch.WordTrace tailWord_3586947 prefixEnd_3586947 1841827893202882787066437 := by
  unfold tailWord_3586947
  simp only [CollatzResearch.WordTrace]
  refine ⟨130826704936111095620991095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87217803290740730413994063 130826704936111095620991095)
  ·
    refine ⟨196240057404166643431486643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130826704936111095620991095 196240057404166643431486643)
    ·
      refine ⟨294360086106249965147229965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196240057404166643431486643 294360086106249965147229965)
      ·
        refine ⟨110385032289843736930211237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294360086106249965147229965 110385032289843736930211237)
        ·
          refine ⟨20697193554345700674414607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110385032289843736930211237 20697193554345700674414607)
          ·
            refine ⟨31045790331518551011621911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20697193554345700674414607 31045790331518551011621911)
            ·
              refine ⟨46568685497277826517432867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31045790331518551011621911 46568685497277826517432867)
              ·
                refine ⟨69853028245916739776149301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46568685497277826517432867 69853028245916739776149301)
                ·
                  refine ⟨6548721398054694354013997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69853028245916739776149301 6548721398054694354013997)
                  ·
                    refine ⟨2455770524270510382755249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6548721398054694354013997 2455770524270510382755249)
                    ·
                      refine ⟨1841827893202882787066437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455770524270510382755249 1841827893202882787066437)
                      ·
                        rfl

theorem cell23_3586947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_3586947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586947 prefixEnd_3586947 := by exact prefixLift 3586947
  have htrace : WordTrace (prefixWord ++ tailWord_3586947) baseStart_3586947 baseEnd_3586947 := by
    simpa [prefixWord, tailWord_3586947, baseEnd_3586947] using wordTrace_append hprefix tailTrace_3586947
  have hstable : (prefixWord ++ tailWord_3586947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586947).length < 2 ^ (prefixWord ++ tailWord_3586947).sum := by decide
  have hdescent : baseEnd_3586947 < baseStart_3586947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586954 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3586954 : Nat := 118140960795 + 3586954 * 2 ^ 59
def prefixEnd_3586954 : Nat := 4983230072969 + 3 ^ 40 * 3586954 * 2
def baseEnd_3586954 : Nat := 1841831487567464259678905

theorem tailTrace_3586954 : CollatzResearch.WordTrace tailWord_3586954 prefixEnd_3586954 1841831487567464259678905 := by
  unfold tailWord_3586954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32706740061771433954123979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87217973498057157210997277 32706740061771433954123979)
  ·
    refine ⟨49060110092657150931185969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32706740061771433954123979 49060110092657150931185969)
    ·
      refine ⟨36795082569492863198389477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49060110092657150931185969 36795082569492863198389477)
      ·
        refine ⟨6899077981779911849698027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36795082569492863198389477 6899077981779911849698027)
        ·
          refine ⟨10348616972669867774547041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899077981779911849698027 10348616972669867774547041)
          ·
            refine ⟨7761462729502400830910281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10348616972669867774547041 7761462729502400830910281)
            ·
              refine ⟨5821097047126800623182711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7761462729502400830910281 5821097047126800623182711)
              ·
                refine ⟨8731645570690200934774067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821097047126800623182711 8731645570690200934774067)
                ·
                  refine ⟨13097468356035301402161101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8731645570690200934774067 13097468356035301402161101)
                  ·
                    refine ⟨4911550633513238025810413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13097468356035301402161101 4911550633513238025810413)
                    ·
                      refine ⟨1841831487567464259678905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4911550633513238025810413 1841831487567464259678905)
                      ·
                        rfl

theorem cell23_3586954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3586954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586954 prefixEnd_3586954 := by exact prefixLift 3586954
  have htrace : WordTrace (prefixWord ++ tailWord_3586954) baseStart_3586954 baseEnd_3586954 := by
    simpa [prefixWord, tailWord_3586954, baseEnd_3586954] using wordTrace_append hprefix tailTrace_3586954
  have hstable : (prefixWord ++ tailWord_3586954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586954).length < 2 ^ (prefixWord ++ tailWord_3586954).sum := by decide
  have hdescent : baseEnd_3586954 < baseStart_3586954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586964 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_3586964 : Nat := 118140960795 + 3586964 * 2 ^ 59
def prefixEnd_3586964 : Nat := 4983230072969 + 3 ^ 40 * 3586964 * 2
def baseEnd_3586964 : Nat := 1841836622374009220553859

theorem tailTrace_3586964 : CollatzResearch.WordTrace tailWord_3586964 prefixEnd_3586964 1841836622374009220553859 := by
  unfold tailWord_3586964
  simp only [CollatzResearch.WordTrace]
  refine ⟨65413662488524753762179973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87218216651366338349573297 65413662488524753762179973)
  ·
    refine ⟨12265061716598391330408745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65413662488524753762179973 12265061716598391330408745)
    ·
      refine ⟨9198796287448793497806559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12265061716598391330408745 9198796287448793497806559)
      ·
        refine ⟨13798194431173190246709839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9198796287448793497806559 13798194431173190246709839)
        ·
          refine ⟨20697291646759785370064759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13798194431173190246709839 20697291646759785370064759)
          ·
            refine ⟨31045937470139678055097139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20697291646759785370064759 31045937470139678055097139)
            ·
              refine ⟨46568906205209517082645709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31045937470139678055097139 46568906205209517082645709)
              ·
                refine ⟨17463339826953568905992141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46568906205209517082645709 17463339826953568905992141)
                ·
                  refine ⟨6548752435107588339747053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17463339826953568905992141 6548752435107588339747053)
                  ·
                    refine ⟨2455782163165345627405145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6548752435107588339747053 2455782163165345627405145)
                    ·
                      refine ⟨1841836622374009220553859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455782163165345627405145 1841836622374009220553859)
                      ·
                        rfl

theorem cell23_3586964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_3586964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586964 prefixEnd_3586964 := by exact prefixLift 3586964
  have htrace : WordTrace (prefixWord ++ tailWord_3586964) baseStart_3586964 baseEnd_3586964 := by
    simpa [prefixWord, tailWord_3586964, baseEnd_3586964] using wordTrace_append hprefix tailTrace_3586964
  have hstable : (prefixWord ++ tailWord_3586964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586964).length < 2 ^ (prefixWord ++ tailWord_3586964).sum := by decide
  have hdescent : baseEnd_3586964 < baseStart_3586964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586980 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3586980 : Nat := 118140960795 + 3586980 * 2 ^ 59
def prefixEnd_3586980 : Nat := 4983230072969 + 3 ^ 40 * 3586980 * 2
def baseEnd_3586980 : Nat := 1841844838064481157953785

theorem tailTrace_3586980 : CollatzResearch.WordTrace tailWord_3586980 prefixEnd_3586980 1841844838064481157953785 := by
  unfold tailWord_3586980
  simp only [CollatzResearch.WordTrace]
  refine ⟨65413954272495771128471197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87218605696661028171294929 65413954272495771128471197)
  ·
    refine ⟨24530232852185914173176699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65413954272495771128471197 24530232852185914173176699)
    ·
      refine ⟨36795349278278871259765049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24530232852185914173176699 36795349278278871259765049)
      ·
        refine ⟨27596511958709153444823787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36795349278278871259765049 27596511958709153444823787)
        ·
          refine ⟨41394767938063730167235681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27596511958709153444823787 41394767938063730167235681)
          ·
            refine ⟨31046075953547797625426761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41394767938063730167235681 31046075953547797625426761)
            ·
              refine ⟨23284556965160848219070071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31046075953547797625426761 23284556965160848219070071)
              ·
                refine ⟨34926835447741272328605107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23284556965160848219070071 34926835447741272328605107)
                ·
                  refine ⟨52390253171611908492907661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34926835447741272328605107 52390253171611908492907661)
                  ·
                    refine ⟨19646344939354465684840373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52390253171611908492907661 19646344939354465684840373)
                    ·
                      refine ⟨1841844838064481157953785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19646344939354465684840373 1841844838064481157953785)
                      ·
                        rfl

theorem cell23_3586980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3586980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3586980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3586980 prefixEnd_3586980 := by exact prefixLift 3586980
  have htrace : WordTrace (prefixWord ++ tailWord_3586980) baseStart_3586980 baseEnd_3586980 := by
    simpa [prefixWord, tailWord_3586980, baseEnd_3586980] using wordTrace_append hprefix tailTrace_3586980
  have hstable : (prefixWord ++ tailWord_3586980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586980).length < 2 ^ (prefixWord ++ tailWord_3586980).sum := by decide
  have hdescent : baseEnd_3586980 < baseStart_3586980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587000 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 7]
def baseStart_3587000 : Nat := 118140960795 + 3587000 * 2 ^ 59
def prefixEnd_3587000 : Nat := 4983230072969 + 3 ^ 40 * 3587000 * 2
def baseEnd_3587000 : Nat := 204650567519730119967077

theorem tailTrace_3587000 : CollatzResearch.WordTrace tailWord_3587000 prefixEnd_3587000 204650567519730119967077 := by
  unfold tailWord_3587000
  simp only [CollatzResearch.WordTrace]
  refine ⟨65414319002459542836335227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87219092003279390448446969 65414319002459542836335227)
  ·
    refine ⟨98121478503689314254502841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65414319002459542836335227 98121478503689314254502841)
    ·
      refine ⟨73591108877766985690877131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98121478503689314254502841 73591108877766985690877131)
      ·
        refine ⟨110386663316650478536315697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73591108877766985690877131 110386663316650478536315697)
        ·
          refine ⟨82789997487487858902236773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110386663316650478536315697 82789997487487858902236773)
          ·
            refine ⟨15523124528903973544169395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82789997487487858902236773 15523124528903973544169395)
            ·
              refine ⟨23284686793355960316254093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15523124528903973544169395 23284686793355960316254093)
              ·
                refine ⟨8731757547508485118595285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23284686793355960316254093 8731757547508485118595285)
                ·
                  refine ⟨204650567519730119967077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8731757547508485118595285 204650567519730119967077)
                  ·
                    rfl

theorem cell23_3587000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 7].length) (baseStart_3587000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587000 prefixEnd_3587000 := by exact prefixLift 3587000
  have htrace : WordTrace (prefixWord ++ tailWord_3587000) baseStart_3587000 baseEnd_3587000 := by
    simpa [prefixWord, tailWord_3587000, baseEnd_3587000] using wordTrace_append hprefix tailTrace_3587000
  have hstable : (prefixWord ++ tailWord_3587000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587000).length < 2 ^ (prefixWord ++ tailWord_3587000).sum := by decide
  have hdescent : baseEnd_3587000 < baseStart_3587000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587034 : List Nat := [3, 1, 1, 2, 4, 1, 3, 3, 5]
def baseStart_3587034 : Nat := 118140960795 + 3587034 * 2 ^ 59
def prefixEnd_3587034 : Nat := 4983230072969 + 3 ^ 40 * 3587034 * 2
def baseEnd_3587034 : Nat := 204652507335535994075393

theorem tailTrace_3587034 : CollatzResearch.WordTrace tailWord_3587034 prefixEnd_3587034 204652507335535994075393 := by
  unfold tailWord_3587034
  simp only [CollatzResearch.WordTrace]
  refine ⟨32707469521698977369852039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87219918724530606319605437 32707469521698977369852039)
  ·
    refine ⟨49061204282548466054778059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32707469521698977369852039 49061204282548466054778059)
    ·
      refine ⟨73591806423822699082167089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49061204282548466054778059 73591806423822699082167089)
      ·
        refine ⟨55193854817867024311625317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73591806423822699082167089 55193854817867024311625317)
        ·
          refine ⟨10348847778350067058429747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55193854817867024311625317 10348847778350067058429747)
          ·
            refine ⟨15523271667525100587644621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10348847778350067058429747 15523271667525100587644621)
            ·
              refine ⟨5821226875321912720366733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15523271667525100587644621 5821226875321912720366733)
              ·
                refine ⟨2182960078245717270137525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5821226875321912720366733 2182960078245717270137525)
                ·
                  refine ⟨204652507335535994075393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2182960078245717270137525 204652507335535994075393)
                  ·
                    rfl

theorem cell23_3587034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_3587034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587034 prefixEnd_3587034 := by exact prefixLift 3587034
  have htrace : WordTrace (prefixWord ++ tailWord_3587034) baseStart_3587034 baseEnd_3587034 := by
    simpa [prefixWord, tailWord_3587034, baseEnd_3587034] using wordTrace_append hprefix tailTrace_3587034
  have hstable : (prefixWord ++ tailWord_3587034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587034).length < 2 ^ (prefixWord ++ tailWord_3587034).sum := by decide
  have hdescent : baseEnd_3587034 < baseStart_3587034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587047 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3587047 : Nat := 118140960795 + 3587047 * 2 ^ 59
def prefixEnd_3587047 : Nat := 4983230072969 + 3 ^ 40 * 3587047 * 2
def baseEnd_3587047 : Nat := 613959747089444131938659

theorem tailTrace_3587047 : CollatzResearch.WordTrace tailWord_3587047 prefixEnd_3587047 613959747089444131938659 := by
  unfold tailWord_3587047
  simp only [CollatzResearch.WordTrace]
  refine ⟨130830352235748812699631395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87220234823832541799754263 130830352235748812699631395)
  ·
    refine ⟨196245528353623219049447093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130830352235748812699631395 196245528353623219049447093)
    ·
      refine ⟨18398018283152176785885665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196245528353623219049447093 18398018283152176785885665)
      ·
        refine ⟨13798513712364132589414249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18398018283152176785885665 13798513712364132589414249)
        ·
          refine ⟨10348885284273099442060687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13798513712364132589414249 10348885284273099442060687)
          ·
            refine ⟨15523327926409649163091031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10348885284273099442060687 15523327926409649163091031)
            ·
              refine ⟨23284991889614473744636547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15523327926409649163091031 23284991889614473744636547)
              ·
                refine ⟨34927487834421710616954821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23284991889614473744636547 34927487834421710616954821)
                ·
                  refine ⟨6548903968954070740679029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34927487834421710616954821 6548903968954070740679029)
                  ·
                    refine ⟨613959747089444131938659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6548903968954070740679029 613959747089444131938659)
                    ·
                      rfl

theorem cell23_3587047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3587047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587047 prefixEnd_3587047 := by exact prefixLift 3587047
  have htrace : WordTrace (prefixWord ++ tailWord_3587047) baseStart_3587047 baseEnd_3587047 := by
    simpa [prefixWord, tailWord_3587047, baseEnd_3587047] using wordTrace_append hprefix tailTrace_3587047
  have hstable : (prefixWord ++ tailWord_3587047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587047).length < 2 ^ (prefixWord ++ tailWord_3587047).sum := by decide
  have hdescent : baseEnd_3587047 < baseStart_3587047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587057 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_3587057 : Nat := 118140960795 + 3587057 * 2 ^ 59
def prefixEnd_3587057 : Nat := 4983230072969 + 3 ^ 40 * 3587057 * 2
def baseEnd_3587057 : Nat := 1841884376074877356690931

theorem tailTrace_3587057 : CollatzResearch.WordTrace tailWord_3587057 prefixEnd_3587057 1841884376074877356690931 := by
  unfold tailWord_3587057
  simp only [CollatzResearch.WordTrace]
  refine ⟨130830716965712584407495425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87220477977141722938330283 130830716965712584407495425)
  ·
    refine ⟨98123037724284438305621569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130830716965712584407495425 98123037724284438305621569)
    ·
      refine ⟨73592278293213328729216177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98123037724284438305621569 73592278293213328729216177)
      ·
        refine ⟨55194208719909996546912133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73592278293213328729216177 55194208719909996546912133)
        ·
          refine ⟨10348914134983124352546025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55194208719909996546912133 10348914134983124352546025)
          ·
            refine ⟨7761685601237343264409519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10348914134983124352546025 7761685601237343264409519)
            ·
              refine ⟨11642528401856014896614279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761685601237343264409519 11642528401856014896614279)
              ·
                refine ⟨17463792602784022344921419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11642528401856014896614279 17463792602784022344921419)
                ·
                  refine ⟨26195688904176033517382129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17463792602784022344921419 26195688904176033517382129)
                  ·
                    refine ⟨19646766678132025138036597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26195688904176033517382129 19646766678132025138036597)
                    ·
                      refine ⟨1841884376074877356690931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19646766678132025138036597 1841884376074877356690931)
                      ·
                        rfl

theorem cell23_3587057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_3587057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587057 prefixEnd_3587057 := by exact prefixLift 3587057
  have htrace : WordTrace (prefixWord ++ tailWord_3587057) baseStart_3587057 baseEnd_3587057 := by
    simpa [prefixWord, tailWord_3587057, baseEnd_3587057] using wordTrace_append hprefix tailTrace_3587057
  have hstable : (prefixWord ++ tailWord_3587057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587057).length < 2 ^ (prefixWord ++ tailWord_3587057).sum := by decide
  have hdescent : baseEnd_3587057 < baseStart_3587057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587067 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 1, 6, 2]
def baseStart_3587067 : Nat := 118140960795 + 3587067 * 2 ^ 59
def prefixEnd_3587067 : Nat := 4983230072969 + 3 ^ 40 * 3587067 * 2
def baseEnd_3587067 : Nat := 1841889510881422317565885

theorem tailTrace_3587067 : CollatzResearch.WordTrace tailWord_3587067 prefixEnd_3587067 1841889510881422317565885 := by
  unfold tailWord_3587067
  simp only [CollatzResearch.WordTrace]
  refine ⟨130831081695676356115359455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87220721130450904076906303 130831081695676356115359455)
  ·
    refine ⟨196246622543514534173039183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130831081695676356115359455 196246622543514534173039183)
    ·
      refine ⟨294369933815271801259558775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196246622543514534173039183 294369933815271801259558775)
      ·
        refine ⟨441554900722907701889338163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294369933815271801259558775 441554900722907701889338163)
        ·
          refine ⟨662332351084361552834007245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441554900722907701889338163 662332351084361552834007245)
          ·
            refine ⟨248374631656635582312752717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 662332351084361552834007245 248374631656635582312752717)
            ·
              refine ⟨93140486871238343367282269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248374631656635582312752717 93140486871238343367282269)
              ·
                refine ⟨34927682576714378762730851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93140486871238343367282269 34927682576714378762730851)
                ·
                  refine ⟨52391523865071568144096277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34927682576714378762730851 52391523865071568144096277)
                  ·
                    refine ⟨2455852681175229756754513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52391523865071568144096277 2455852681175229756754513)
                    ·
                      refine ⟨1841889510881422317565885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455852681175229756754513 1841889510881422317565885)
                      ·
                        rfl

theorem cell23_3587067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 6, 2].length) (baseStart_3587067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587067 prefixEnd_3587067 := by exact prefixLift 3587067
  have htrace : WordTrace (prefixWord ++ tailWord_3587067) baseStart_3587067 baseEnd_3587067 := by
    simpa [prefixWord, tailWord_3587067, baseEnd_3587067] using wordTrace_append hprefix tailTrace_3587067
  have hstable : (prefixWord ++ tailWord_3587067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587067).length < 2 ^ (prefixWord ++ tailWord_3587067).sum := by decide
  have hdescent : baseEnd_3587067 < baseStart_3587067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587077 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_3587077 : Nat := 118140960795 + 3587077 * 2 ^ 59
def prefixEnd_3587077 : Nat := 4983230072969 + 3 ^ 40 * 3587077 * 2
def baseEnd_3587077 : Nat := 613964881895989092813613

theorem tailTrace_3587077 : CollatzResearch.WordTrace tailWord_3587077 prefixEnd_3587077 613964881895989092813613 := by
  unfold tailWord_3587077
  simp only [CollatzResearch.WordTrace]
  refine ⟨130831446425640127823223485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87220964283760085215482323 130831446425640127823223485)
  ·
    refine ⟨49061792409615047933708807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130831446425640127823223485 49061792409615047933708807)
    ·
      refine ⟨73592688614422571900563211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49061792409615047933708807 73592688614422571900563211)
      ·
        refine ⟨110389032921633857850844817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73592688614422571900563211 110389032921633857850844817)
        ·
          refine ⟨82791774691225393388133613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110389032921633857850844817 82791774691225393388133613)
          ·
            refine ⟨31046915509209522520550105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82791774691225393388133613 31046915509209522520550105)
            ·
              refine ⟨23285186631907141890412579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31046915509209522520550105 23285186631907141890412579)
              ·
                refine ⟨34927779947860712835618869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23285186631907141890412579 34927779947860712835618869)
                ·
                  refine ⟨3274479370111941828339269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34927779947860712835618869 3274479370111941828339269)
                  ·
                    refine ⟨613964881895989092813613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3274479370111941828339269 613964881895989092813613)
                    ·
                      rfl

theorem cell23_3587077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_3587077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587077 prefixEnd_3587077 := by exact prefixLift 3587077
  have htrace : WordTrace (prefixWord ++ tailWord_3587077) baseStart_3587077 baseEnd_3587077 := by
    simpa [prefixWord, tailWord_3587077, baseEnd_3587077] using wordTrace_append hprefix tailTrace_3587077
  have hstable : (prefixWord ++ tailWord_3587077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587077).length < 2 ^ (prefixWord ++ tailWord_3587077).sum := by decide
  have hdescent : baseEnd_3587077 < baseStart_3587077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587084 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3587084 : Nat := 118140960795 + 3587084 * 2 ^ 59
def prefixEnd_3587084 : Nat := 4983230072969 + 3 ^ 40 * 3587084 * 2
def baseEnd_3587084 : Nat := 1841898240052548751053307

theorem tailTrace_3587084 : CollatzResearch.WordTrace tailWord_3587084 prefixEnd_3587084 1841898240052548751053307 := by
  unfold tailWord_3587084
  simp only [CollatzResearch.WordTrace]
  refine ⟨65415850868307384009364153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87221134491076512012485537 65415850868307384009364153)
  ·
    refine ⟨49061888151230538007023115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65415850868307384009364153 49061888151230538007023115)
    ·
      refine ⟨73592832226845807010534673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49061888151230538007023115 73592832226845807010534673)
      ·
        refine ⟨55194624170134355257901005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73592832226845807010534673 55194624170134355257901005)
        ·
          refine ⟨20697984063800383221712877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55194624170134355257901005 20697984063800383221712877)
          ·
            refine ⟨7761744023925143708142329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20697984063800383221712877 7761744023925143708142329)
            ·
              refine ⟨5821308017943857781106747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7761744023925143708142329 5821308017943857781106747)
              ·
                refine ⟨8731962026915786671660121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821308017943857781106747 8731962026915786671660121)
                ·
                  refine ⟨6548971520186840003745091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8731962026915786671660121 6548971520186840003745091)
                  ·
                    refine ⟨9823457280280260005617637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548971520186840003745091 9823457280280260005617637)
                    ·
                      refine ⟨1841898240052548751053307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9823457280280260005617637 1841898240052548751053307)
                      ·
                        rfl

theorem cell23_3587084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3587084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587084 prefixEnd_3587084 := by exact prefixLift 3587084
  have htrace : WordTrace (prefixWord ++ tailWord_3587084) baseStart_3587084 baseEnd_3587084 := by
    simpa [prefixWord, tailWord_3587084, baseEnd_3587084] using wordTrace_append hprefix tailTrace_3587084
  have hstable : (prefixWord ++ tailWord_3587084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587084).length < 2 ^ (prefixWord ++ tailWord_3587084).sum := by decide
  have hdescent : baseEnd_3587084 < baseStart_3587084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587107 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 6]
def baseStart_3587107 : Nat := 118140960795 + 3587107 * 2 ^ 59
def prefixEnd_3587107 : Nat := 4983230072969 + 3 ^ 40 * 3587107 * 2
def baseEnd_3587107 : Nat := 204656672234178017896189

theorem tailTrace_3587107 : CollatzResearch.WordTrace tailWord_3587107 prefixEnd_3587107 204656672234178017896189 := by
  unfold tailWord_3587107
  simp only [CollatzResearch.WordTrace]
  refine ⟨130832540615531442946815575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87221693743687628631210383 130832540615531442946815575)
  ·
    refine ⟨196248810923297164420223363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130832540615531442946815575 196248810923297164420223363)
    ·
      refine ⟨294373216384945746630335045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196248810923297164420223363 294373216384945746630335045)
      ·
        refine ⟨55194978072177327493187821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294373216384945746630335045 55194978072177327493187821)
        ·
          refine ⟨20698116777066497809945433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55194978072177327493187821 20698116777066497809945433)
          ·
            refine ⟨15523587582799873357459075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20698116777066497809945433 15523587582799873357459075)
            ·
              refine ⟨23285381374199810036188613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15523587582799873357459075 23285381374199810036188613)
              ·
                refine ⟨4366009007662464381785365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23285381374199810036188613 4366009007662464381785365)
                ·
                  refine ⟨204656672234178017896189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4366009007662464381785365 204656672234178017896189)
                  ·
                    rfl

theorem cell23_3587107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 6].length) (baseStart_3587107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587107 prefixEnd_3587107 := by exact prefixLift 3587107
  have htrace : WordTrace (prefixWord ++ tailWord_3587107) baseStart_3587107 baseEnd_3587107 := by
    simpa [prefixWord, tailWord_3587107, baseEnd_3587107] using wordTrace_append hprefix tailTrace_3587107
  have hstable : (prefixWord ++ tailWord_3587107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587107).length < 2 ^ (prefixWord ++ tailWord_3587107).sum := by decide
  have hdescent : baseEnd_3587107 < baseStart_3587107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587144 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_3587144 : Nat := 118140960795 + 3587144 * 2 ^ 59
def prefixEnd_3587144 : Nat := 4983230072969 + 3 ^ 40 * 3587144 * 2
def baseEnd_3587144 : Nat := 1841929048891818516303031

theorem tailTrace_3587144 : CollatzResearch.WordTrace tailWord_3587144 prefixEnd_3587144 1841929048891818516303031 := by
  unfold tailWord_3587144
  simp only [CollatzResearch.WordTrace]
  refine ⟨65416945058198699132956243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87222593410931598843941657 65416945058198699132956243)
  ·
    refine ⟨98125417587298048699434365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65416945058198699132956243 98125417587298048699434365)
    ·
      refine ⟨36797031595236768262287887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98125417587298048699434365 36797031595236768262287887)
      ·
        refine ⟨55195547392855152393431831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36797031595236768262287887 55195547392855152393431831)
        ·
          refine ⟨82793321089282728590147747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55195547392855152393431831 82793321089282728590147747)
          ·
            refine ⟨124189981633924092885221621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82793321089282728590147747 124189981633924092885221621)
            ·
              refine ⟨11642810778180383707989527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124189981633924092885221621 11642810778180383707989527)
              ·
                refine ⟨17464216167270575561984291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11642810778180383707989527 17464216167270575561984291)
                ·
                  refine ⟨26196324250905863342976437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17464216167270575561984291 26196324250905863342976437)
                  ·
                    refine ⟨2455905398522424688404041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26196324250905863342976437 2455905398522424688404041)
                    ·
                      refine ⟨1841929048891818516303031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455905398522424688404041 1841929048891818516303031)
                      ·
                        rfl

theorem cell23_3587144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_3587144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587144 prefixEnd_3587144 := by exact prefixLift 3587144
  have htrace : WordTrace (prefixWord ++ tailWord_3587144) baseStart_3587144 baseEnd_3587144 := by
    simpa [prefixWord, tailWord_3587144, baseEnd_3587144] using wordTrace_append hprefix tailTrace_3587144
  have hstable : (prefixWord ++ tailWord_3587144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587144).length < 2 ^ (prefixWord ++ tailWord_3587144).sum := by decide
  have hdescent : baseEnd_3587144 < baseStart_3587144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587177 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_3587177 : Nat := 118140960795 + 3587177 * 2 ^ 59
def prefixEnd_3587177 : Nat := 4983230072969 + 3 ^ 40 * 3587177 * 2
def baseEnd_3587177 : Nat := 1841945993753416887190379

theorem tailTrace_3587177 : CollatzResearch.WordTrace tailWord_3587177 prefixEnd_3587177 1841945993753416887190379 := by
  unfold tailWord_3587177
  simp only [CollatzResearch.WordTrace]
  refine ⟨130835093725277844901863785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87223395816851896601242523 130835093725277844901863785)
  ·
    refine ⟨98126320293958383676397839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130835093725277844901863785 98126320293958383676397839)
    ·
      refine ⟨147189480440937575514596759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98126320293958383676397839 147189480440937575514596759)
      ·
        refine ⟨220784220661406363271895139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147189480440937575514596759 220784220661406363271895139)
        ·
          refine ⟨331176330992109544907842709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220784220661406363271895139 331176330992109544907842709)
          ·
            refine ⟨15523890515255134917555127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 331176330992109544907842709 15523890515255134917555127)
            ·
              refine ⟨23285835772882702376332691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15523890515255134917555127 23285835772882702376332691)
              ·
                refine ⟨34928753659324053564499037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23285835772882702376332691 34928753659324053564499037)
                ·
                  refine ⟨13098282622246520086687139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34928753659324053564499037 13098282622246520086687139)
                  ·
                    refine ⟨19647423933369780130030709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13098282622246520086687139 19647423933369780130030709)
                    ·
                      refine ⟨1841945993753416887190379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19647423933369780130030709 1841945993753416887190379)
                      ·
                        rfl

theorem cell23_3587177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_3587177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587177 prefixEnd_3587177 := by exact prefixLift 3587177
  have htrace : WordTrace (prefixWord ++ tailWord_3587177) baseStart_3587177 baseEnd_3587177 := by
    simpa [prefixWord, tailWord_3587177, baseEnd_3587177] using wordTrace_append hprefix tailTrace_3587177
  have hstable : (prefixWord ++ tailWord_3587177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587177).length < 2 ^ (prefixWord ++ tailWord_3587177).sum := by decide
  have hdescent : baseEnd_3587177 < baseStart_3587177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587191 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 3, 2, 2]
def baseStart_3587191 : Nat := 118140960795 + 3587191 * 2 ^ 59
def prefixEnd_3587191 : Nat := 4983230072969 + 3 ^ 40 * 3587191 * 2
def baseEnd_3587191 : Nat := 1841953182482579832415315

theorem tailTrace_3587191 : CollatzResearch.WordTrace tailWord_3587191 prefixEnd_3587191 1841953182482579832415315 := by
  unfold tailWord_3587191
  simp only [CollatzResearch.WordTrace]
  refine ⟨130835604347227125292873427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87223736231484750195248951 130835604347227125292873427)
  ·
    refine ⟨196253406520840687939310141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130835604347227125292873427 196253406520840687939310141)
    ·
      refine ⟨73595027445315257977241303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196253406520840687939310141 73595027445315257977241303)
      ·
        refine ⟨110392541167972886965861955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73595027445315257977241303 110392541167972886965861955)
        ·
          refine ⟨165588811751959330448792933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110392541167972886965861955 165588811751959330448792933)
          ·
            refine ⟨31047902203492374459148675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165588811751959330448792933 31047902203492374459148675)
            ·
              refine ⟨46571853305238561688723013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31047902203492374459148675 46571853305238561688723013)
              ·
                refine ⟨8732222494732230316635565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46571853305238561688723013 8732222494732230316635565)
                ·
                  refine ⟨3274583435524586368738337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8732222494732230316635565 3274583435524586368738337)
                  ·
                    refine ⟨2455937576643439776553753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274583435524586368738337 2455937576643439776553753)
                    ·
                      refine ⟨1841953182482579832415315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2455937576643439776553753 1841953182482579832415315)
                      ·
                        rfl

theorem cell23_3587191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_3587191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587191 prefixEnd_3587191 := by exact prefixLift 3587191
  have htrace : WordTrace (prefixWord ++ tailWord_3587191) baseStart_3587191 baseEnd_3587191 := by
    simpa [prefixWord, tailWord_3587191, baseEnd_3587191] using wordTrace_append hprefix tailTrace_3587191
  have hstable : (prefixWord ++ tailWord_3587191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587191).length < 2 ^ (prefixWord ++ tailWord_3587191).sum := by decide
  have hdescent : baseEnd_3587191 < baseStart_3587191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587197 : List Nat := [1, 4, 1, 1, 3, 1, 3, 9]
def baseStart_3587197 : Nat := 118140960795 + 3587197 * 2 ^ 59
def prefixEnd_3587197 : Nat := 4983230072969 + 3 ^ 40 * 3587197 * 2
def baseEnd_3587197 : Nat := 68220602346907659590381

theorem tailTrace_3587197 : CollatzResearch.WordTrace tailWord_3587197 prefixEnd_3587197 68220602346907659590381 := by
  unfold tailWord_3587197
  simp only [CollatzResearch.WordTrace]
  refine ⟨130835823185205388317591845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87223882123470258878394563 130835823185205388317591845)
  ·
    refine ⟨24531716847226010309548471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130835823185205388317591845 24531716847226010309548471)
    ·
      refine ⟨36797575270839015464322707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24531716847226010309548471 36797575270839015464322707)
      ·
        refine ⟨55196362906258523196484061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36797575270839015464322707 55196362906258523196484061)
        ·
          refine ⟨20698636089846946198681523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55196362906258523196484061 20698636089846946198681523)
          ·
            refine ⟨31047954134770419298022285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20698636089846946198681523 31047954134770419298022285)
            ·
              refine ⟨11642982800538907236758357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31047954134770419298022285 11642982800538907236758357)
              ·
                refine ⟨68220602346907659590381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11642982800538907236758357 68220602346907659590381)
                ·
                  rfl

theorem cell23_3587197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 9].length) (baseStart_3587197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587197 prefixEnd_3587197 := by exact prefixLift 3587197
  have htrace : WordTrace (prefixWord ++ tailWord_3587197) baseStart_3587197 baseEnd_3587197 := by
    simpa [prefixWord, tailWord_3587197, baseEnd_3587197] using wordTrace_append hprefix tailTrace_3587197
  have hstable : (prefixWord ++ tailWord_3587197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587197).length < 2 ^ (prefixWord ++ tailWord_3587197).sum := by decide
  have hdescent : baseEnd_3587197 < baseStart_3587197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587214 : List Nat := [4, 1, 1, 3, 2, 3, 9]
def baseStart_3587214 : Nat := 118140960795 + 3587214 * 2 ^ 59
def prefixEnd_3587214 : Nat := 4983230072969 + 3 ^ 40 * 3587214 * 2
def baseEnd_3587214 : Nat := 22740308549847323980589

theorem tailTrace_3587214 : CollatzResearch.WordTrace tailWord_3587214 prefixEnd_3587214 22740308549847323980589 := by
  unfold tailWord_3587214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16354555403267975027620087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87224295484095866813973797 16354555403267975027620087)
  ·
    refine ⟨24531833104901962541430131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16354555403267975027620087 24531833104901962541430131)
    ·
      refine ⟨36797749657352943812145197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24531833104901962541430131 36797749657352943812145197)
      ·
        refine ⟨13799156121507353929554449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36797749657352943812145197 13799156121507353929554449)
        ·
          refine ⟨10349367091130515447165837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13799156121507353929554449 10349367091130515447165837)
          ·
            refine ⟨3881012659173943292687189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10349367091130515447165837 3881012659173943292687189)
            ·
              refine ⟨22740308549847323980589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3881012659173943292687189 22740308549847323980589)
              ·
                rfl

theorem cell23_3587214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 9].length) (baseStart_3587214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587214 prefixEnd_3587214 := by exact prefixLift 3587214
  have htrace : WordTrace (prefixWord ++ tailWord_3587214) baseStart_3587214 baseEnd_3587214 := by
    simpa [prefixWord, tailWord_3587214, baseEnd_3587214] using wordTrace_append hprefix tailTrace_3587214
  have hstable : (prefixWord ++ tailWord_3587214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587214).length < 2 ^ (prefixWord ++ tailWord_3587214).sum := by decide
  have hdescent : baseEnd_3587214 < baseStart_3587214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587245 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_3587245 : Nat := 118140960795 + 3587245 * 2 ^ 59
def prefixEnd_3587245 : Nat := 4983230072969 + 3 ^ 40 * 3587245 * 2
def baseEnd_3587245 : Nat := 1841980910437922621140067

theorem tailTrace_3587245 : CollatzResearch.WordTrace tailWord_3587245 prefixEnd_3587245 1841980910437922621140067 := by
  unfold tailWord_3587245
  simp only [CollatzResearch.WordTrace]
  refine ⟨130837573889031492515339189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87225049259354328343559459 130837573889031492515339189)
  ·
    refine ⟨12266022552096702423313049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130837573889031492515339189 12266022552096702423313049)
    ·
      refine ⟨9199516914072526817484787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12266022552096702423313049 9199516914072526817484787)
      ·
        refine ⟨13799275371108790226227181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199516914072526817484787 13799275371108790226227181)
        ·
          refine ⟨5174728264165796334835193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13799275371108790226227181 5174728264165796334835193)
          ·
            refine ⟨3881046198124347251126395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5174728264165796334835193 3881046198124347251126395)
            ·
              refine ⟨5821569297186520876689593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881046198124347251126395 5821569297186520876689593)
              ·
                refine ⟨4366176972889890657517195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821569297186520876689593 4366176972889890657517195)
                ·
                  refine ⟨6549265459334835986275793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366176972889890657517195 6549265459334835986275793)
                  ·
                    refine ⟨4911949094501126989706845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549265459334835986275793 4911949094501126989706845)
                    ·
                      refine ⟨1841980910437922621140067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4911949094501126989706845 1841980910437922621140067)
                      ·
                        rfl

theorem cell23_3587245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_3587245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587245 prefixEnd_3587245 := by exact prefixLift 3587245
  have htrace : WordTrace (prefixWord ++ tailWord_3587245) baseStart_3587245 baseEnd_3587245 := by
    simpa [prefixWord, tailWord_3587245, baseEnd_3587245] using wordTrace_append hprefix tailTrace_3587245
  have hstable : (prefixWord ++ tailWord_3587245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587245).length < 2 ^ (prefixWord ++ tailWord_3587245).sum := by decide
  have hdescent : baseEnd_3587245 < baseStart_3587245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587267 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5]
def baseStart_3587267 : Nat := 118140960795 + 3587267 * 2 ^ 59
def prefixEnd_3587267 : Nat := 4983230072969 + 3 ^ 40 * 3587267 * 2
def baseEnd_3587267 : Nat := 1841992207012321535064965

theorem tailTrace_3587267 : CollatzResearch.WordTrace tailWord_3587267 prefixEnd_3587267 1841992207012321535064965 := by
  unfold tailWord_3587267
  simp only [CollatzResearch.WordTrace]
  refine ⟨130838376294951790272640055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87225584196634526848426703 130838376294951790272640055)
  ·
    refine ⟨196257564442427685408960083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130838376294951790272640055 196257564442427685408960083)
    ·
      refine ⟨294386346663641528113440125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196257564442427685408960083 294386346663641528113440125)
      ·
        refine ⟨110394879998865573042540047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294386346663641528113440125 110394879998865573042540047)
        ·
          refine ⟨165592319998298359563810071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110394879998865573042540047 165592319998298359563810071)
          ·
            refine ⟨248388479997447539345715107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165592319998298359563810071 248388479997447539345715107)
            ·
              refine ⟨372582719996171309018572661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248388479997447539345715107 372582719996171309018572661)
              ·
                refine ⟨34929629999641060220491187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 372582719996171309018572661 34929629999641060220491187)
                ·
                  refine ⟨52394444999461590330736781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34929629999641060220491187 52394444999461590330736781)
                  ·
                    refine ⟨19647916874798096374026293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52394444999461590330736781 19647916874798096374026293)
                    ·
                      refine ⟨1841992207012321535064965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19647916874798096374026293 1841992207012321535064965)
                      ·
                        rfl

theorem cell23_3587267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_3587267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587267 prefixEnd_3587267 := by exact prefixLift 3587267
  have htrace : WordTrace (prefixWord ++ tailWord_3587267) baseStart_3587267 baseEnd_3587267 := by
    simpa [prefixWord, tailWord_3587267, baseEnd_3587267] using wordTrace_append hprefix tailTrace_3587267
  have hstable : (prefixWord ++ tailWord_3587267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587267).length < 2 ^ (prefixWord ++ tailWord_3587267).sum := by decide
  have hdescent : baseEnd_3587267 < baseStart_3587267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587304 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 7]
def baseStart_3587304 : Nat := 118140960795 + 3587304 * 2 ^ 59
def prefixEnd_3587304 : Nat := 4983230072969 + 3 ^ 40 * 3587304 * 2
def baseEnd_3587304 : Nat := 204667911755170876700255

theorem tailTrace_3587304 : CollatzResearch.WordTrace tailWord_3587304 prefixEnd_3587304 204667911755170876700255 := by
  unfold tailWord_3587304
  simp only [CollatzResearch.WordTrace]
  refine ⟨65419862897908872795868483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87226483863878497061157977 65419862897908872795868483)
  ·
    refine ⟨98129794346863309193802725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65419862897908872795868483 98129794346863309193802725)
    ·
      refine ⟨18399336440036870473838011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98129794346863309193802725 18399336440036870473838011)
      ·
        refine ⟨27599004660055305710757017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18399336440036870473838011 27599004660055305710757017)
        ·
          refine ⟨20699253495041479283067763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27599004660055305710757017 20699253495041479283067763)
          ·
            refine ⟨31048880242562218924601645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20699253495041479283067763 31048880242562218924601645)
            ·
              refine ⟨11643330090960832096725617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31048880242562218924601645 11643330090960832096725617)
              ·
                refine ⟨8732497568220624072544213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11643330090960832096725617 8732497568220624072544213)
                ·
                  refine ⟨204667911755170876700255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8732497568220624072544213 204667911755170876700255)
                  ·
                    rfl

theorem cell23_3587304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 7].length) (baseStart_3587304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587304 prefixEnd_3587304 := by exact prefixLift 3587304
  have htrace : WordTrace (prefixWord ++ tailWord_3587304) baseStart_3587304 baseEnd_3587304 := by
    simpa [prefixWord, tailWord_3587304, baseEnd_3587304] using wordTrace_append hprefix tailTrace_3587304
  have hstable : (prefixWord ++ tailWord_3587304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587304).length < 2 ^ (prefixWord ++ tailWord_3587304).sum := by decide
  have hdescent : baseEnd_3587304 < baseStart_3587304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587321 : List Nat := [1, 2, 1, 3, 1, 1, 6, 3, 5]
def baseStart_3587321 : Nat := 118140960795 + 3587321 * 2 ^ 59
def prefixEnd_3587321 : Nat := 4983230072969 + 3 ^ 40 * 3587321 * 2
def baseEnd_3587321 : Nat := 204668881663073813754413

theorem tailTrace_3587321 : CollatzResearch.WordTrace tailWord_3587321 prefixEnd_3587321 204668881663073813754413 := by
  unfold tailWord_3587321
  simp only [CollatzResearch.WordTrace]
  refine ⟨130840345836756157495105817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87226897224504104996737211 130840345836756157495105817)
  ·
    refine ⟨98130259377567118121329363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130840345836756157495105817 98130259377567118121329363)
    ·
      refine ⟨147195389066350677181994045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98130259377567118121329363 147195389066350677181994045)
      ·
        refine ⟨55198270899881503943247767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147195389066350677181994045 55198270899881503943247767)
        ·
          refine ⟨82797406349822255914871651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55198270899881503943247767 82797406349822255914871651)
          ·
            refine ⟨124196109524733383872307477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82797406349822255914871651 124196109524733383872307477)
            ·
              refine ⟨5821692633971877369014413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124196109524733383872307477 5821692633971877369014413)
              ·
                refine ⟨2183134737739454013380405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5821692633971877369014413 2183134737739454013380405)
                ·
                  refine ⟨204668881663073813754413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2183134737739454013380405 204668881663073813754413)
                  ·
                    rfl

theorem cell23_3587321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 5].length) (baseStart_3587321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587321 prefixEnd_3587321 := by exact prefixLift 3587321
  have htrace : WordTrace (prefixWord ++ tailWord_3587321) baseStart_3587321 baseEnd_3587321 := by
    simpa [prefixWord, tailWord_3587321, baseEnd_3587321] using wordTrace_append hprefix tailTrace_3587321
  have hstable : (prefixWord ++ tailWord_3587321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587321).length < 2 ^ (prefixWord ++ tailWord_3587321).sum := by decide
  have hdescent : baseEnd_3587321 < baseStart_3587321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587332 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_3587332 : Nat := 118140960795 + 3587332 * 2 ^ 59
def prefixEnd_3587332 : Nat := 4983230072969 + 3 ^ 40 * 3587332 * 2
def baseEnd_3587332 : Nat := 1842025583254863780752167

theorem tailTrace_3587332 : CollatzResearch.WordTrace tailWord_3587332 prefixEnd_3587332 1842025583254863780752167 := by
  unfold tailWord_3587332
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420373519858153186878125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87227164693144204249170833 65420373519858153186878125)
  ·
    refine ⟨24532640069946807445079297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65420373519858153186878125 24532640069946807445079297)
    ·
      refine ⟨18399480052460105583809473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24532640069946807445079297 18399480052460105583809473)
      ·
        refine ⟨13799610039345079187857105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18399480052460105583809473 13799610039345079187857105)
        ·
          refine ⟨10349707529508809390892829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13799610039345079187857105 10349707529508809390892829)
          ·
            refine ⟨3881140323565803521584811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10349707529508809390892829 3881140323565803521584811)
            ·
              refine ⟨5821710485348705282377217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881140323565803521584811 5821710485348705282377217)
              ·
                refine ⟨4366282864011528961782913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821710485348705282377217 4366282864011528961782913)
                ·
                  refine ⟨3274712148008646721337185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4366282864011528961782913 3274712148008646721337185)
                  ·
                    refine ⟨2456034111006485041002889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274712148008646721337185 2456034111006485041002889)
                    ·
                      refine ⟨1842025583254863780752167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456034111006485041002889 1842025583254863780752167)
                      ·
                        rfl

theorem cell23_3587332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_3587332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587332 prefixEnd_3587332 := by exact prefixLift 3587332
  have htrace : WordTrace (prefixWord ++ tailWord_3587332) baseStart_3587332 baseEnd_3587332 := by
    simpa [prefixWord, tailWord_3587332, baseEnd_3587332] using wordTrace_append hprefix tailTrace_3587332
  have hstable : (prefixWord ++ tailWord_3587332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587332).length < 2 ^ (prefixWord ++ tailWord_3587332).sum := by decide
  have hdescent : baseEnd_3587332 < baseStart_3587332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587364 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_3587364 : Nat := 118140960795 + 3587364 * 2 ^ 59
def prefixEnd_3587364 : Nat := 4983230072969 + 3 ^ 40 * 3587364 * 2
def baseEnd_3587364 : Nat := 614014004878602551850673

theorem tailTrace_3587364 : CollatzResearch.WordTrace tailWord_3587364 prefixEnd_3587364 614014004878602551850673 := by
  unfold tailWord_3587364
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420957087800187919460573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87227942783733583892614097 65420957087800187919460573)
  ·
    refine ⟨24532858907925070469797715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65420957087800187919460573 24532858907925070469797715)
    ·
      refine ⟨36799288361887605704696573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24532858907925070469797715 36799288361887605704696573)
      ·
        refine ⟨13799733135707852139261215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36799288361887605704696573 13799733135707852139261215)
        ·
          refine ⟨20699599703561778208891823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13799733135707852139261215 20699599703561778208891823)
          ·
            refine ⟨31049399555342667313337735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20699599703561778208891823 31049399555342667313337735)
            ·
              refine ⟨46574099333014000970006603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31049399555342667313337735 46574099333014000970006603)
              ·
                refine ⟨69861148999521001455009905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46574099333014000970006603 69861148999521001455009905)
                ·
                  refine ⟨52395861749640751091257429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69861148999521001455009905 52395861749640751091257429)
                  ·
                    refine ⟨614014004878602551850673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52395861749640751091257429 614014004878602551850673)
                    ·
                      rfl

theorem cell23_3587364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_3587364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587364 prefixEnd_3587364 := by exact prefixLift 3587364
  have htrace : WordTrace (prefixWord ++ tailWord_3587364) baseStart_3587364 baseEnd_3587364 := by
    simpa [prefixWord, tailWord_3587364, baseEnd_3587364] using wordTrace_append hprefix tailTrace_3587364
  have hstable : (prefixWord ++ tailWord_3587364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587364).length < 2 ^ (prefixWord ++ tailWord_3587364).sum := by decide
  have hdescent : baseEnd_3587364 < baseStart_3587364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587391 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 3]
def baseStart_3587391 : Nat := 118140960795 + 3587391 * 2 ^ 59
def prefixEnd_3587391 : Nat := 4983230072969 + 3 ^ 40 * 3587391 * 2
def baseEnd_3587391 : Nat := 1842055878613479049914395

theorem tailTrace_3587391 : CollatzResearch.WordTrace tailWord_3587391 prefixEnd_3587391 1842055878613479049914395 := by
  unfold tailWord_3587391
  simp only [CollatzResearch.WordTrace]
  refine ⟨130842898946502559450154027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87228599297668372966769351 130842898946502559450154027)
  ·
    refine ⟨196264348419753839175231041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130842898946502559450154027 196264348419753839175231041)
    ·
      refine ⟨147198261314815379381423281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196264348419753839175231041 147198261314815379381423281)
      ·
        refine ⟨110398695986111534536067461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147198261314815379381423281 110398695986111534536067461)
        ·
          refine ⟨20699755497395912725512649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110398695986111534536067461 20699755497395912725512649)
          ·
            refine ⟨15524816623046934544134487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20699755497395912725512649 15524816623046934544134487)
            ·
              refine ⟨23287224934570401816201731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15524816623046934544134487 23287224934570401816201731)
              ·
                refine ⟨34930837401855602724302597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23287224934570401816201731 34930837401855602724302597)
                ·
                  refine ⟨6549532012847925510806737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34930837401855602724302597 6549532012847925510806737)
                  ·
                    refine ⟨4912149009635944133105053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549532012847925510806737 4912149009635944133105053)
                    ·
                      refine ⟨1842055878613479049914395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4912149009635944133105053 1842055878613479049914395)
                      ·
                        rfl

theorem cell23_3587391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_3587391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587391 prefixEnd_3587391 := by exact prefixLift 3587391
  have htrace : WordTrace (prefixWord ++ tailWord_3587391) baseStart_3587391 baseEnd_3587391 := by
    simpa [prefixWord, tailWord_3587391, baseEnd_3587391] using wordTrace_append hprefix tailTrace_3587391
  have hstable : (prefixWord ++ tailWord_3587391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587391).length < 2 ^ (prefixWord ++ tailWord_3587391).sum := by decide
  have hdescent : baseEnd_3587391 < baseStart_3587391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587441 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 1, 5]
def baseStart_3587441 : Nat := 118140960795 + 3587441 * 2 ^ 59
def prefixEnd_3587441 : Nat := 4983230072969 + 3 ^ 40 * 3587441 * 2
def baseEnd_3587441 : Nat := 614027184215401284763055

theorem tailTrace_3587441 : CollatzResearch.WordTrace tailWord_3587441 prefixEnd_3587441 614027184215401284763055 := by
  unfold tailWord_3587441
  simp only [CollatzResearch.WordTrace]
  refine ⟨130844722596321417989474177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87229815064214278659649451 130844722596321417989474177)
  ·
    refine ⟨98133541947241063492105633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130844722596321417989474177 98133541947241063492105633)
    ·
      refine ⟨73600156460430797619079225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98133541947241063492105633 73600156460430797619079225)
      ·
        refine ⟨55200117345323098214309419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73600156460430797619079225 55200117345323098214309419)
        ·
          refine ⟨82800176017984647321464129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55200117345323098214309419 82800176017984647321464129)
          ·
            refine ⟨62100132013488485491098097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82800176017984647321464129 62100132013488485491098097)
            ·
              refine ⟨46575099010116364118323573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62100132013488485491098097 46575099010116364118323573)
              ·
                refine ⟨4366415532198409136092835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46575099010116364118323573 4366415532198409136092835)
                ·
                  refine ⟨6549623298297613704139253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366415532198409136092835 6549623298297613704139253)
                  ·
                    refine ⟨614027184215401284763055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6549623298297613704139253 614027184215401284763055)
                    ·
                      rfl

theorem cell23_3587441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_3587441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587441 prefixEnd_3587441 := by exact prefixLift 3587441
  have htrace : WordTrace (prefixWord ++ tailWord_3587441) baseStart_3587441 baseEnd_3587441 := by
    simpa [prefixWord, tailWord_3587441, baseEnd_3587441] using wordTrace_append hprefix tailTrace_3587441
  have hstable : (prefixWord ++ tailWord_3587441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587441).length < 2 ^ (prefixWord ++ tailWord_3587441).sum := by decide
  have hdescent : baseEnd_3587441 < baseStart_3587441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587461 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_3587461 : Nat := 118140960795 + 3587461 * 2 ^ 59
def prefixEnd_3587461 : Nat := 4983230072969 + 3 ^ 40 * 3587461 * 2
def baseEnd_3587461 : Nat := 1842091822259293776039073

theorem tailTrace_3587461 : CollatzResearch.WordTrace tailWord_3587461 prefixEnd_3587461 1842091822259293776039073 := by
  unfold tailWord_3587461
  simp only [CollatzResearch.WordTrace]
  refine ⟨130845452056248961405202237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87230301370832640936801491 130845452056248961405202237)
  ·
    refine ⟨49067044521093360526950839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130845452056248961405202237 49067044521093360526950839)
    ·
      refine ⟨73600566781640040790426259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49067044521093360526950839 73600566781640040790426259)
      ·
        refine ⟨110400850172460061185639389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73600566781640040790426259 110400850172460061185639389)
        ·
          refine ⟨41400318814672522944614771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110400850172460061185639389 41400318814672522944614771)
          ·
            refine ⟨62100478222008784416922157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41400318814672522944614771 62100478222008784416922157)
            ·
              refine ⟨23287679333253294156345809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62100478222008784416922157 23287679333253294156345809)
              ·
                refine ⟨17465759499939970617259357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23287679333253294156345809 17465759499939970617259357)
                ·
                  refine ⟨6549659812477488981472259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17465759499939970617259357 6549659812477488981472259)
                  ·
                    refine ⟨9824489718716233472208389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6549659812477488981472259 9824489718716233472208389)
                    ·
                      refine ⟨1842091822259293776039073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9824489718716233472208389 1842091822259293776039073)
                      ·
                        rfl

theorem cell23_3587461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_3587461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587461 prefixEnd_3587461 := by exact prefixLift 3587461
  have htrace : WordTrace (prefixWord ++ tailWord_3587461) baseStart_3587461 baseEnd_3587461 := by
    simpa [prefixWord, tailWord_3587461, baseEnd_3587461] using wordTrace_append hprefix tailTrace_3587461
  have hstable : (prefixWord ++ tailWord_3587461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587461).length < 2 ^ (prefixWord ++ tailWord_3587461).sum := by decide
  have hdescent : baseEnd_3587461 < baseStart_3587461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587491 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4]
def baseStart_3587491 : Nat := 118140960795 + 3587491 * 2 ^ 59
def prefixEnd_3587491 : Nat := 4983230072969 + 3 ^ 40 * 3587491 * 2
def baseEnd_3587491 : Nat := 1842107226678928658663935

theorem tailTrace_3587491 : CollatzResearch.WordTrace tailWord_3587491 prefixEnd_3587491 1842107226678928658663935 := by
  unfold tailWord_3587491
  simp only [CollatzResearch.WordTrace]
  refine ⟨130846546246140276528794327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87231030830760184352529551 130846546246140276528794327)
  ·
    refine ⟨196269819369210414793191491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130846546246140276528794327 196269819369210414793191491)
    ·
      refine ⟨294404729053815622189787237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196269819369210414793191491 294404729053815622189787237)
      ·
        refine ⟨55200886697590429160585107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294404729053815622189787237 55200886697590429160585107)
        ·
          refine ⟨82801330046385643740877661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55200886697590429160585107 82801330046385643740877661)
          ·
            refine ⟨31050498767394616402829123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82801330046385643740877661 31050498767394616402829123)
            ·
              refine ⟨46575748151091924604243685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31050498767394616402829123 46575748151091924604243685)
              ·
                refine ⟨8732952778329735863295691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46575748151091924604243685 8732952778329735863295691)
                ·
                  refine ⟨13099429167494603794943537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8732952778329735863295691 13099429167494603794943537)
                  ·
                    refine ⟨9824571875620952846207653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13099429167494603794943537 9824571875620952846207653)
                    ·
                      refine ⟨1842107226678928658663935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9824571875620952846207653 1842107226678928658663935)
                      ·
                        rfl

theorem cell23_3587491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_3587491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587491 prefixEnd_3587491 := by exact prefixLift 3587491
  have htrace : WordTrace (prefixWord ++ tailWord_3587491) baseStart_3587491 baseEnd_3587491 := by
    simpa [prefixWord, tailWord_3587491, baseEnd_3587491] using wordTrace_append hprefix tailTrace_3587491
  have hstable : (prefixWord ++ tailWord_3587491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587491).length < 2 ^ (prefixWord ++ tailWord_3587491).sum := by decide
  have hdescent : baseEnd_3587491 < baseStart_3587491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587495 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_3587495 : Nat := 118140960795 + 3587495 * 2 ^ 59
def prefixEnd_3587495 : Nat := 4983230072969 + 3 ^ 40 * 3587495 * 2
def baseEnd_3587495 : Nat := 1842109280601546643013917

theorem tailTrace_3587495 : CollatzResearch.WordTrace tailWord_3587495 prefixEnd_3587495 1842109280601546643013917 := by
  unfold tailWord_3587495
  simp only [CollatzResearch.WordTrace]
  refine ⟨130846692138125785211939939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87231128092083856807959959 130846692138125785211939939)
  ·
    refine ⟨196270038207188677817909909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130846692138125785211939939 196270038207188677817909909)
    ·
      refine ⟨9200158040961969272714527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196270038207188677817909909 9200158040961969272714527)
      ·
        refine ⟨13800237061442953909071791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9200158040961969272714527 13800237061442953909071791)
        ·
          refine ⟨20700355592164430863607687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13800237061442953909071791 20700355592164430863607687)
          ·
            refine ⟨31050533388246646295411531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20700355592164430863607687 31050533388246646295411531)
            ·
              refine ⟨46575800082369969443117297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31050533388246646295411531 46575800082369969443117297)
              ·
                refine ⟨34931850061777477082337973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46575800082369969443117297 34931850061777477082337973)
                ·
                  refine ⟨3274860943291638476469185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34931850061777477082337973 3274860943291638476469185)
                  ·
                    refine ⟨2456145707468728857351889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274860943291638476469185 2456145707468728857351889)
                    ·
                      refine ⟨1842109280601546643013917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456145707468728857351889 1842109280601546643013917)
                      ·
                        rfl

theorem cell23_3587495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_3587495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587495 prefixEnd_3587495 := by exact prefixLift 3587495
  have htrace : WordTrace (prefixWord ++ tailWord_3587495) baseStart_3587495 baseEnd_3587495 := by
    simpa [prefixWord, tailWord_3587495, baseEnd_3587495] using wordTrace_append hprefix tailTrace_3587495
  have hstable : (prefixWord ++ tailWord_3587495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587495).length < 2 ^ (prefixWord ++ tailWord_3587495).sum := by decide
  have hdescent : baseEnd_3587495 < baseStart_3587495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587512 : List Nat := [2, 1, 2, 1, 2, 2, 4, 4, 1, 2, 2]
def baseStart_3587512 : Nat := 118140960795 + 3587512 * 2 ^ 59
def prefixEnd_3587512 : Nat := 4983230072969 + 3 ^ 40 * 3587512 * 2
def baseEnd_3587512 : Nat := 1842118009772673076501339

theorem tailTrace_3587512 : CollatzResearch.WordTrace tailWord_3587512 prefixEnd_3587512 1842118009772673076501339 := by
  unfold tailWord_3587512
  simp only [CollatzResearch.WordTrace]
  refine ⟨65423656089532098557654395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87231541452709464743539193 65423656089532098557654395)
  ·
    refine ⟨98135484134298147836481593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65423656089532098557654395 98135484134298147836481593)
    ·
      refine ⟨73601613100723610877361195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98135484134298147836481593 73601613100723610877361195)
      ·
        refine ⟨110402419651085416316041793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73601613100723610877361195 110402419651085416316041793)
        ·
          refine ⟨82801814738314062237031345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110402419651085416316041793 82801814738314062237031345)
          ·
            refine ⟨62101361053735546677773509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82801814738314062237031345 62101361053735546677773509)
            ·
              refine ⟨11644005197575415002082533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62101361053735546677773509 11644005197575415002082533)
              ·
                refine ⟨2183250974545390312890475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11644005197575415002082533 2183250974545390312890475)
                ·
                  refine ⟨3274876461818085469335713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183250974545390312890475 3274876461818085469335713)
                  ·
                    refine ⟨2456157346363564102001785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274876461818085469335713 2456157346363564102001785)
                    ·
                      refine ⟨1842118009772673076501339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456157346363564102001785 1842118009772673076501339)
                      ·
                        rfl

theorem cell23_3587512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_3587512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587512 prefixEnd_3587512 := by exact prefixLift 3587512
  have htrace : WordTrace (prefixWord ++ tailWord_3587512) baseStart_3587512 baseEnd_3587512 := by
    simpa [prefixWord, tailWord_3587512, baseEnd_3587512] using wordTrace_append hprefix tailTrace_3587512
  have hstable : (prefixWord ++ tailWord_3587512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587512).length < 2 ^ (prefixWord ++ tailWord_3587512).sum := by decide
  have hdescent : baseEnd_3587512 < baseStart_3587512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587541 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3587541 : Nat := 118140960795 + 3587541 * 2 ^ 59
def prefixEnd_3587541 : Nat := 4983230072969 + 3 ^ 40 * 3587541 * 2
def baseEnd_3587541 : Nat := 1842132900711653463038705

theorem tailTrace_3587541 : CollatzResearch.WordTrace tailWord_3587541 prefixEnd_3587541 1842132900711653463038705 := by
  unfold tailWord_3587541
  simp only [CollatzResearch.WordTrace]
  refine ⟨130848369895959135068114477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87232246597306090045409651 130848369895959135068114477)
  ·
    refine ⟨49068138710984675650542929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130848369895959135068114477 49068138710984675650542929)
    ·
      refine ⟨36801104033238506737907197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49068138710984675650542929 36801104033238506737907197)
      ·
        refine ⟨13800414012464440026715199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36801104033238506737907197 13800414012464440026715199)
        ·
          refine ⟨20700621018696660040072799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13800414012464440026715199 20700621018696660040072799)
          ·
            refine ⟨31050931528044990060109199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20700621018696660040072799 31050931528044990060109199)
            ·
              refine ⟨46576397292067485090163799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31050931528044990060109199 46576397292067485090163799)
              ·
                refine ⟨69864595938101227635245699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46576397292067485090163799 69864595938101227635245699)
                ·
                  refine ⟨104796893907151841452868549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69864595938101227635245699 104796893907151841452868549)
                  ·
                    refine ⟨19649417607590970272412853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104796893907151841452868549 19649417607590970272412853)
                    ·
                      refine ⟨1842132900711653463038705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19649417607590970272412853 1842132900711653463038705)
                      ·
                        rfl

theorem cell23_3587541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3587541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587541 prefixEnd_3587541 := by exact prefixLift 3587541
  have htrace : WordTrace (prefixWord ++ tailWord_3587541) baseStart_3587541 baseEnd_3587541 := by
    simpa [prefixWord, tailWord_3587541, baseEnd_3587541] using wordTrace_append hprefix tailTrace_3587541
  have hstable : (prefixWord ++ tailWord_3587541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587541).length < 2 ^ (prefixWord ++ tailWord_3587541).sum := by decide
  have hdescent : baseEnd_3587541 < baseStart_3587541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587614 : List Nat := [4, 3, 3, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3587614 : Nat := 118140960795 + 3587614 * 2 ^ 59
def prefixEnd_3587614 : Nat := 4983230072969 + 3 ^ 40 * 3587614 * 2
def baseEnd_3587614 : Nat := 1842170384799431677425871

theorem tailTrace_3587614 : CollatzResearch.WordTrace tailWord_3587614 prefixEnd_3587614 1842170384799431677425871 := by
  unfold tailWord_3587614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16356379053086833566940237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87234021616463112357014597 16356379053086833566940237)
  ·
    refine ⟨6133642144907562587602589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16356379053086833566940237 6133642144907562587602589)
    ·
      refine ⟨2300115804340335970350971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6133642144907562587602589 2300115804340335970350971)
      ·
        refine ⟨3450173706510503955526457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300115804340335970350971 3450173706510503955526457)
        ·
          refine ⟨2587630279882877966644843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3450173706510503955526457 2587630279882877966644843)
          ·
            refine ⟨3881445419824316949967265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587630279882877966644843 3881445419824316949967265)
            ·
              refine ⟨2911084064868237712475449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881445419824316949967265 2911084064868237712475449)
              ·
                refine ⟨2183313048651178284356587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911084064868237712475449 2183313048651178284356587)
                ·
                  refine ⟨3274969572976767426534881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183313048651178284356587 3274969572976767426534881)
                  ·
                    refine ⟨2456227179732575569901161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274969572976767426534881 2456227179732575569901161)
                    ·
                      refine ⟨1842170384799431677425871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456227179732575569901161 1842170384799431677425871)
                      ·
                        rfl

theorem cell23_3587614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3587614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587614 prefixEnd_3587614 := by exact prefixLift 3587614
  have htrace : WordTrace (prefixWord ++ tailWord_3587614) baseStart_3587614 baseEnd_3587614 := by
    simpa [prefixWord, tailWord_3587614, baseEnd_3587614] using wordTrace_append hprefix tailTrace_3587614
  have hstable : (prefixWord ++ tailWord_3587614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587614).length < 2 ^ (prefixWord ++ tailWord_3587614).sum := by decide
  have hdescent : baseEnd_3587614 < baseStart_3587614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587619 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 2, 2, 2]
def baseStart_3587619 : Nat := 118140960795 + 3587619 * 2 ^ 59
def prefixEnd_3587619 : Nat := 4983230072969 + 3 ^ 40 * 3587619 * 2
def baseEnd_3587619 : Nat := 1842172952202704157863347

theorem tailTrace_3587619 : CollatzResearch.WordTrace tailWord_3587619 prefixEnd_3587619 1842172952202704157863347 := by
  unfold tailWord_3587619
  simp only [CollatzResearch.WordTrace]
  refine ⟨130851214789676554389453911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87234143193117702926302607 130851214789676554389453911)
  ·
    refine ⟨196276822184514831584180867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130851214789676554389453911 196276822184514831584180867)
    ·
      refine ⟨294415233276772247376271301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196276822184514831584180867 294415233276772247376271301)
      ·
        refine ⟨55202856239394796383050869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294415233276772247376271301 55202856239394796383050869)
        ·
          refine ⟨5175267772443262160911019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55202856239394796383050869 5175267772443262160911019)
          ·
            refine ⟨7762901658664893241366529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175267772443262160911019 7762901658664893241366529)
            ·
              refine ⟨5822176243998669931024897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7762901658664893241366529 5822176243998669931024897)
              ·
                refine ⟨4366632182999002448268673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5822176243998669931024897 4366632182999002448268673)
                ·
                  refine ⟨3274974137249251836201505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4366632182999002448268673 3274974137249251836201505)
                  ·
                    refine ⟨2456230602936938877151129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274974137249251836201505 2456230602936938877151129)
                    ·
                      refine ⟨1842172952202704157863347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456230602936938877151129 1842172952202704157863347)
                      ·
                        rfl

theorem cell23_3587619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_3587619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587619 prefixEnd_3587619 := by exact prefixLift 3587619
  have htrace : WordTrace (prefixWord ++ tailWord_3587619) baseStart_3587619 baseEnd_3587619 := by
    simpa [prefixWord, tailWord_3587619, baseEnd_3587619] using wordTrace_append hprefix tailTrace_3587619
  have hstable : (prefixWord ++ tailWord_3587619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587619).length < 2 ^ (prefixWord ++ tailWord_3587619).sum := by decide
  have hdescent : baseEnd_3587619 < baseStart_3587619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587621 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_3587621 : Nat := 118140960795 + 3587621 * 2 ^ 59
def prefixEnd_3587621 : Nat := 4983230072969 + 3 ^ 40 * 3587621 * 2
def baseEnd_3587621 : Nat := 614057993054671050012779

theorem tailTrace_3587621 : CollatzResearch.WordTrace tailWord_3587621 prefixEnd_3587621 614057993054671050012779 := by
  unfold tailWord_3587621
  simp only [CollatzResearch.WordTrace]
  refine ⟨130851287735669308731026717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87234191823779539154017811 130851287735669308731026717)
  ·
    refine ⟨49069232900875990774135019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130851287735669308731026717 49069232900875990774135019)
    ·
      refine ⟨73603849351313986161202529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49069232900875990774135019 73603849351313986161202529)
      ·
        refine ⟨55202887013485489620901897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73603849351313986161202529 55202887013485489620901897)
        ·
          refine ⟨41402165260114117215676423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55202887013485489620901897 41402165260114117215676423)
          ·
            refine ⟨62103247890171175823514635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41402165260114117215676423 62103247890171175823514635)
            ·
              refine ⟨93154871835256763735271953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62103247890171175823514635 93154871835256763735271953)
              ·
                refine ⟨69866153876442572801453965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93154871835256763735271953 69866153876442572801453965)
                ·
                  refine ⟨26199807703665964800545237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69866153876442572801453965 26199807703665964800545237)
                  ·
                    refine ⟨614057993054671050012779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26199807703665964800545237 614057993054671050012779)
                    ·
                      rfl

theorem cell23_3587621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_3587621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587621 prefixEnd_3587621 := by exact prefixLift 3587621
  have htrace : WordTrace (prefixWord ++ tailWord_3587621) baseStart_3587621 baseEnd_3587621 := by
    simpa [prefixWord, tailWord_3587621, baseEnd_3587621] using wordTrace_append hprefix tailTrace_3587621
  have hstable : (prefixWord ++ tailWord_3587621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587621).length < 2 ^ (prefixWord ++ tailWord_3587621).sum := by decide
  have hdescent : baseEnd_3587621 < baseStart_3587621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587658 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_3587658 : Nat := 118140960795 + 3587658 * 2 ^ 59
def prefixEnd_3587658 : Nat := 4983230072969 + 3 ^ 40 * 3587658 * 2
def baseEnd_3587658 : Nat := 1842192977948229505275667

theorem tailTrace_3587658 : CollatzResearch.WordTrace tailWord_3587658 prefixEnd_3587658 1842192977948229505275667 := by
  unfold tailWord_3587658
  simp only [CollatzResearch.WordTrace]
  refine ⟨32713159309133816012530907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87235091491023509366749085 32713159309133816012530907)
  ·
    refine ⟨49069738963700724018796361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32713159309133816012530907 49069738963700724018796361)
    ·
      refine ⟨36802304222775543014097271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49069738963700724018796361 36802304222775543014097271)
      ·
        refine ⟨55203456334163314521145907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36802304222775543014097271 55203456334163314521145907)
        ·
          refine ⟨82805184501244971781718861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55203456334163314521145907 82805184501244971781718861)
          ·
            refine ⟨31051944187966864418144573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82805184501244971781718861 31051944187966864418144573)
            ·
              refine ⟨11644479070487574156804215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31051944187966864418144573 11644479070487574156804215)
              ·
                refine ⟨17466718605731361235206323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11644479070487574156804215 17466718605731361235206323)
                ·
                  refine ⟨26200077908597041852809485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17466718605731361235206323 26200077908597041852809485)
                  ·
                    refine ⟨9825029215723890694803557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26200077908597041852809485 9825029215723890694803557)
                    ·
                      refine ⟨1842192977948229505275667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9825029215723890694803557 1842192977948229505275667)
                      ·
                        rfl

theorem cell23_3587658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_3587658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587658 prefixEnd_3587658 := by exact prefixLift 3587658
  have htrace : WordTrace (prefixWord ++ tailWord_3587658) baseStart_3587658 baseEnd_3587658 := by
    simpa [prefixWord, tailWord_3587658, baseEnd_3587658] using wordTrace_append hprefix tailTrace_3587658
  have hstable : (prefixWord ++ tailWord_3587658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587658).length < 2 ^ (prefixWord ++ tailWord_3587658).sum := by decide
  have hdescent : baseEnd_3587658 < baseStart_3587658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587670 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_3587670 : Nat := 118140960795 + 3587670 * 2 ^ 59
def prefixEnd_3587670 : Nat := 4983230072969 + 3 ^ 40 * 3587670 * 2
def baseEnd_3587670 : Nat := 1842199139716083458325613

theorem tailTrace_3587670 : CollatzResearch.WordTrace tailWord_3587670 prefixEnd_3587670 1842199139716083458325613 := by
  unfold tailWord_3587670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178317182030736881222529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87235383274994526733040309 8178317182030736881222529)
  ·
    refine ⟨6133737886523052660916897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8178317182030736881222529 6133737886523052660916897)
    ·
      refine ⟨4600303414892289495687673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6133737886523052660916897 4600303414892289495687673)
      ·
        refine ⟨3450227561169217121765755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4600303414892289495687673 3450227561169217121765755)
        ·
          refine ⟨5175341341753825682648633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450227561169217121765755 5175341341753825682648633)
          ·
            refine ⟨3881506006315369261986475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175341341753825682648633 3881506006315369261986475)
            ·
              refine ⟨5822259009473053892979713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881506006315369261986475 5822259009473053892979713)
              ·
                refine ⟨4366694257104790419734785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5822259009473053892979713 4366694257104790419734785)
                ·
                  refine ⟨3275020692828592814801089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4366694257104790419734785 3275020692828592814801089)
                  ·
                    refine ⟨2456265519621444611100817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3275020692828592814801089 2456265519621444611100817)
                    ·
                      refine ⟨1842199139716083458325613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456265519621444611100817 1842199139716083458325613)
                      ·
                        rfl

theorem cell23_3587670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_3587670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587670 prefixEnd_3587670 := by exact prefixLift 3587670
  have htrace : WordTrace (prefixWord ++ tailWord_3587670) baseStart_3587670 baseEnd_3587670 := by
    simpa [prefixWord, tailWord_3587670, baseEnd_3587670] using wordTrace_append hprefix tailTrace_3587670
  have hstable : (prefixWord ++ tailWord_3587670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587670).length < 2 ^ (prefixWord ++ tailWord_3587670).sum := by decide
  have hdescent : baseEnd_3587670 < baseStart_3587670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587685 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_3587685 : Nat := 118140960795 + 3587685 * 2 ^ 59
def prefixEnd_3587685 : Nat := 4983230072969 + 3 ^ 40 * 3587685 * 2
def baseEnd_3587685 : Nat := 614068947308633633212681

theorem tailTrace_3587685 : CollatzResearch.WordTrace tailWord_3587685 prefixEnd_3587685 614068947308633633212681 := by
  unfold tailWord_3587685
  simp only [CollatzResearch.WordTrace]
  refine ⟨130853622007437447661356509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87235748004958298440904339 130853622007437447661356509)
  ·
    refine ⟨49070108252789042873008691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130853622007437447661356509 49070108252789042873008691)
    ·
      refine ⟨73605162379183564309513037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49070108252789042873008691 73605162379183564309513037)
      ·
        refine ⟨27601935892193836616067389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73605162379183564309513037 27601935892193836616067389)
        ·
          refine ⟨10350725959572688731025271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27601935892193836616067389 10350725959572688731025271)
          ·
            refine ⟨15526088939359033096537907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350725959572688731025271 15526088939359033096537907)
            ·
              refine ⟨23289133409038549644806861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15526088939359033096537907 23289133409038549644806861)
              ·
                refine ⟨8733425028389456116802573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23289133409038549644806861 8733425028389456116802573)
                ·
                  refine ⟨3275034385646046043800965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8733425028389456116802573 3275034385646046043800965)
                  ·
                    refine ⟨614068947308633633212681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3275034385646046043800965 614068947308633633212681)
                    ·
                      rfl

theorem cell23_3587685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_3587685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587685 prefixEnd_3587685 := by exact prefixLift 3587685
  have htrace : WordTrace (prefixWord ++ tailWord_3587685) baseStart_3587685 baseEnd_3587685 := by
    simpa [prefixWord, tailWord_3587685, baseEnd_3587685] using wordTrace_append hprefix tailTrace_3587685
  have hstable : (prefixWord ++ tailWord_3587685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587685).length < 2 ^ (prefixWord ++ tailWord_3587685).sum := by decide
  have hdescent : baseEnd_3587685 < baseStart_3587685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587691 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9]
def baseStart_3587691 : Nat := 118140960795 + 3587691 * 2 ^ 59
def prefixEnd_3587691 : Nat := 4983230072969 + 3 ^ 40 * 3587691 * 2
def baseEnd_3587691 : Nat := 1842209922809827876163015

theorem tailTrace_3587691 : CollatzResearch.WordTrace tailWord_3587691 prefixEnd_3587691 1842209922809827876163015 := by
  unfold tailWord_3587691
  simp only [CollatzResearch.WordTrace]
  refine ⟨130853840845415710686074927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87235893896943807124049951 130853840845415710686074927)
  ·
    refine ⟨196280761268123566029112391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130853840845415710686074927 196280761268123566029112391)
    ·
      refine ⟨294421141902185349043668587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196280761268123566029112391 294421141902185349043668587)
      ·
        refine ⟨441631712853278023565502881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294421141902185349043668587 441631712853278023565502881)
        ·
          refine ⟨331223784639958517674127161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441631712853278023565502881 331223784639958517674127161)
          ·
            refine ⟨248417838479968888255595371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331223784639958517674127161 248417838479968888255595371)
            ·
              refine ⟨372626757719953332383393057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248417838479968888255595371 372626757719953332383393057)
              ·
                refine ⟨279470068289964999287544793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372626757719953332383393057 279470068289964999287544793)
                ·
                  refine ⟨209602551217473749465658595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279470068289964999287544793 209602551217473749465658595)
                  ·
                    refine ⟨314403826826210624198487893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 209602551217473749465658595 314403826826210624198487893)
                    ·
                      refine ⟨1842209922809827876163015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 314403826826210624198487893 1842209922809827876163015)
                      ·
                        rfl

theorem cell23_3587691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_3587691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587691 prefixEnd_3587691 := by exact prefixLift 3587691
  have htrace : WordTrace (prefixWord ++ tailWord_3587691) baseStart_3587691 baseEnd_3587691 := by
    simpa [prefixWord, tailWord_3587691, baseEnd_3587691] using wordTrace_append hprefix tailTrace_3587691
  have hstable : (prefixWord ++ tailWord_3587691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587691).length < 2 ^ (prefixWord ++ tailWord_3587691).sum := by decide
  have hdescent : baseEnd_3587691 < baseStart_3587691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587702 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_3587702 : Nat := 118140960795 + 3587702 * 2 ^ 59
def prefixEnd_3587702 : Nat := 4983230072969 + 3 ^ 40 * 3587702 * 2
def baseEnd_3587702 : Nat := 614071857032342444375155

theorem tailTrace_3587702 : CollatzResearch.WordTrace tailWord_3587702 prefixEnd_3587702 614071857032342444375155 := by
  unfold tailWord_3587702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178390128023491222795335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87236161365583906376483573 8178390128023491222795335)
  ·
    refine ⟨12267585192035236834193003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8178390128023491222795335 12267585192035236834193003)
    ·
      refine ⟨18401377788052855251289505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12267585192035236834193003 18401377788052855251289505)
      ·
        refine ⟨13801033341039641438467129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18401377788052855251289505 13801033341039641438467129)
        ·
          refine ⟨10350775005779731078850347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13801033341039641438467129 10350775005779731078850347)
          ·
            refine ⟨15526162508669596618275521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350775005779731078850347 15526162508669596618275521)
            ·
              refine ⟨11644621881502197463706641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15526162508669596618275521 11644621881502197463706641)
              ·
                refine ⟨8733466411126648097779981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11644621881502197463706641 8733466411126648097779981)
                ·
                  refine ⟨3275049904172493036667493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8733466411126648097779981 3275049904172493036667493)
                  ·
                    refine ⟨614071857032342444375155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3275049904172493036667493 614071857032342444375155)
                    ·
                      rfl

theorem cell23_3587702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_3587702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587702 prefixEnd_3587702 := by exact prefixLift 3587702
  have htrace : WordTrace (prefixWord ++ tailWord_3587702) baseStart_3587702 baseEnd_3587702 := by
    simpa [prefixWord, tailWord_3587702, baseEnd_3587702] using wordTrace_append hprefix tailTrace_3587702
  have hstable : (prefixWord ++ tailWord_3587702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587702).length < 2 ^ (prefixWord ++ tailWord_3587702).sum := by decide
  have hdescent : baseEnd_3587702 < baseStart_3587702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587708 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_3587708 : Nat := 118140960795 + 3587708 * 2 ^ 59
def prefixEnd_3587708 : Nat := 4983230072969 + 3 ^ 40 * 3587708 * 2
def baseEnd_3587708 : Nat := 1842218651980954309650437

theorem tailTrace_3587708 : CollatzResearch.WordTrace tailWord_3587708 prefixEnd_3587708 1842218651980954309650437 := by
  unfold tailWord_3587708
  simp only [CollatzResearch.WordTrace]
  refine ⟨65427230443177061294721889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87236307257569415059629185 65427230443177061294721889)
  ·
    refine ⟨49070422832382795971041417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65427230443177061294721889 49070422832382795971041417)
    ·
      refine ⟨36802817124287096978281063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49070422832382795971041417 36802817124287096978281063)
      ·
        refine ⟨55204225686430645467421595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36802817124287096978281063 55204225686430645467421595)
        ·
          refine ⟨82806338529645968201132393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55204225686430645467421595 82806338529645968201132393)
          ·
            refine ⟨62104753897234476150849295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82806338529645968201132393 62104753897234476150849295)
            ·
              refine ⟨93157130845851714226273943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62104753897234476150849295 93157130845851714226273943)
              ·
                refine ⟨139735696268777571339410915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93157130845851714226273943 139735696268777571339410915)
                ·
                  refine ⟨209603544403166357009116373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139735696268777571339410915 209603544403166357009116373)
                  ·
                    refine ⟨4912583071949211492401165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 209603544403166357009116373 4912583071949211492401165)
                    ·
                      refine ⟨1842218651980954309650437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4912583071949211492401165 1842218651980954309650437)
                      ·
                        rfl

theorem cell23_3587708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_3587708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587708 prefixEnd_3587708 := by exact prefixLift 3587708
  have htrace : WordTrace (prefixWord ++ tailWord_3587708) baseStart_3587708 baseEnd_3587708 := by
    simpa [prefixWord, tailWord_3587708, baseEnd_3587708] using wordTrace_append hprefix tailTrace_3587708
  have hstable : (prefixWord ++ tailWord_3587708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587708).length < 2 ^ (prefixWord ++ tailWord_3587708).sum := by decide
  have hdescent : baseEnd_3587708 < baseStart_3587708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587719 : List Nat := [1, 1, 4, 2, 1, 5, 1, 3, 1, 4]
def baseStart_3587719 : Nat := 118140960795 + 3587719 * 2 ^ 59
def prefixEnd_3587719 : Nat := 4983230072969 + 3 ^ 40 * 3587719 * 2
def baseEnd_3587719 : Nat := 614074766756051255537629

theorem tailTrace_3587719 : CollatzResearch.WordTrace tailWord_3587719 prefixEnd_3587719 614074766756051255537629 := by
  unfold tailWord_3587719
  simp only [CollatzResearch.WordTrace]
  refine ⟨130854862089314271468094211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87236574726209514312062807 130854862089314271468094211)
  ·
    refine ⟨196282293133971407202141317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130854862089314271468094211 196282293133971407202141317)
    ·
      refine ⟨36802929962619638850401497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196282293133971407202141317 36802929962619638850401497)
      ·
        refine ⟨27602197471964729137801123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36802929962619638850401497 27602197471964729137801123)
        ·
          refine ⟨41403296207947093706701685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27602197471964729137801123 41403296207947093706701685)
          ·
            refine ⟨3881559019495040035003283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41403296207947093706701685 3881559019495040035003283)
            ·
              refine ⟨5822338529242560052504925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881559019495040035003283 5822338529242560052504925)
              ·
                refine ⟨2183376948465960019689347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5822338529242560052504925 2183376948465960019689347)
                ·
                  refine ⟨3275065422698940029534021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183376948465960019689347 3275065422698940029534021)
                  ·
                    refine ⟨614074766756051255537629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3275065422698940029534021 614074766756051255537629)
                    ·
                      rfl

theorem cell23_3587719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_3587719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587719 prefixEnd_3587719 := by exact prefixLift 3587719
  have htrace : WordTrace (prefixWord ++ tailWord_3587719) baseStart_3587719 baseEnd_3587719 := by
    simpa [prefixWord, tailWord_3587719, baseEnd_3587719] using wordTrace_append hprefix tailTrace_3587719
  have hstable : (prefixWord ++ tailWord_3587719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587719).length < 2 ^ (prefixWord ++ tailWord_3587719).sum := by decide
  have hdescent : baseEnd_3587719 < baseStart_3587719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587768 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_3587768 : Nat := 118140960795 + 3587768 * 2 ^ 59
def prefixEnd_3587768 : Nat := 4983230072969 + 3 ^ 40 * 3587768 * 2
def baseEnd_3587768 : Nat := 1842249460820224074900161

theorem tailTrace_3587768 : CollatzResearch.WordTrace tailWord_3587768 prefixEnd_3587768 1842249460820224074900161 := by
  unfold tailWord_3587768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65428324633068376418313979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87237766177424501891085305 65428324633068376418313979)
  ·
    refine ⟨98142486949602564627470969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65428324633068376418313979 98142486949602564627470969)
    ·
      refine ⟨73606865212201923470603227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98142486949602564627470969 73606865212201923470603227)
      ·
        refine ⟨110410297818302885205904841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73606865212201923470603227 110410297818302885205904841)
        ·
          refine ⟨82807723363727163904428631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110410297818302885205904841 82807723363727163904428631)
          ·
            refine ⟨124211585045590745856642947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82807723363727163904428631 124211585045590745856642947)
            ·
              refine ⟨186317377568386118784964421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124211585045590745856642947 186317377568386118784964421)
              ·
                refine ⟨34934508294072397272180829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186317377568386118784964421 34934508294072397272180829)
                ·
                  refine ⟨13100440610277148977067811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34934508294072397272180829 13100440610277148977067811)
                  ·
                    refine ⟨19650660915415723465601717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13100440610277148977067811 19650660915415723465601717)
                    ·
                      refine ⟨1842249460820224074900161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19650660915415723465601717 1842249460820224074900161)
                      ·
                        rfl

theorem cell23_3587768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_3587768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587768 prefixEnd_3587768 := by exact prefixLift 3587768
  have htrace : WordTrace (prefixWord ++ tailWord_3587768) baseStart_3587768 baseEnd_3587768 := by
    simpa [prefixWord, tailWord_3587768, baseEnd_3587768] using wordTrace_append hprefix tailTrace_3587768
  have hstable : (prefixWord ++ tailWord_3587768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587768).length < 2 ^ (prefixWord ++ tailWord_3587768).sum := by decide
  have hdescent : baseEnd_3587768 < baseStart_3587768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587788 : List Nat := [2, 2, 1, 5, 13]
def baseStart_3587788 : Nat := 118140960795 + 3587788 * 2 ^ 59
def prefixEnd_3587788 : Nat := 4983230072969 + 3 ^ 40 * 3587788 * 2
def baseEnd_3587788 : Nat := 2527105254366685866461

theorem tailTrace_3587788 : CollatzResearch.WordTrace tailWord_3587788 prefixEnd_3587788 2527105254366685866461 := by
  unfold tailWord_3587788
  simp only [CollatzResearch.WordTrace]
  refine ⟨65428689363032148126178009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87238252484042864168237345 65428689363032148126178009)
  ·
    refine ⟨49071517022274111094633507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65428689363032148126178009 49071517022274111094633507)
    ·
      refine ⟨73607275533411166641950261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49071517022274111094633507 73607275533411166641950261)
      ·
        refine ⟨6900682081257296872682837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73607275533411166641950261 6900682081257296872682837)
        ·
          refine ⟨2527105254366685866461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6900682081257296872682837 2527105254366685866461)
          ·
            rfl

theorem cell23_3587788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 13].length) (baseStart_3587788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587788 prefixEnd_3587788 := by exact prefixLift 3587788
  have htrace : WordTrace (prefixWord ++ tailWord_3587788) baseStart_3587788 baseEnd_3587788 := by
    simpa [prefixWord, tailWord_3587788, baseEnd_3587788] using wordTrace_append hprefix tailTrace_3587788
  have hstable : (prefixWord ++ tailWord_3587788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587788).length < 2 ^ (prefixWord ++ tailWord_3587788).sum := by decide
  have hdescent : baseEnd_3587788 < baseStart_3587788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587808 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_3587808 : Nat := 118140960795 + 3587808 * 2 ^ 59
def prefixEnd_3587808 : Nat := 4983230072969 + 3 ^ 40 * 3587808 * 2
def baseEnd_3587808 : Nat := 1842270000046403918399977

theorem tailTrace_3587808 : CollatzResearch.WordTrace tailWord_3587808 prefixEnd_3587808 1842270000046403918399977 := by
  unfold tailWord_3587808
  simp only [CollatzResearch.WordTrace]
  refine ⟨65429054092995919834042039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87238738790661226445389385 65429054092995919834042039)
  ·
    refine ⟨98143581139493879751063059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65429054092995919834042039 98143581139493879751063059)
    ·
      refine ⟨147215371709240819626594589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98143581139493879751063059 147215371709240819626594589)
      ·
        refine ⟨55205764390965307359972971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147215371709240819626594589 55205764390965307359972971)
        ·
          refine ⟨82808646586447961039959457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55205764390965307359972971 82808646586447961039959457)
          ·
            refine ⟨62106484939835970779969593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82808646586447961039959457 62106484939835970779969593)
            ·
              refine ⟨46579863704876978084977195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62106484939835970779969593 46579863704876978084977195)
              ·
                refine ⟨69869795557315467127465793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46579863704876978084977195 69869795557315467127465793)
                ·
                  refine ⟨52402346667986600345599345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69869795557315467127465793 52402346667986600345599345)
                  ·
                    refine ⟨39301760000989950259199509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52402346667986600345599345 39301760000989950259199509)
                    ·
                      refine ⟨1842270000046403918399977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39301760000989950259199509 1842270000046403918399977)
                      ·
                        rfl

theorem cell23_3587808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_3587808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587808 prefixEnd_3587808 := by exact prefixLift 3587808
  have htrace : WordTrace (prefixWord ++ tailWord_3587808) baseStart_3587808 baseEnd_3587808 := by
    simpa [prefixWord, tailWord_3587808, baseEnd_3587808] using wordTrace_append hprefix tailTrace_3587808
  have hstable : (prefixWord ++ tailWord_3587808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587808).length < 2 ^ (prefixWord ++ tailWord_3587808).sum := by decide
  have hdescent : baseEnd_3587808 < baseStart_3587808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587853 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3587853 : Nat := 118140960795 + 3587853 * 2 ^ 59
def prefixEnd_3587853 : Nat := 4983230072969 + 3 ^ 40 * 3587853 * 2
def baseEnd_3587853 : Nat := 1842293106675856242337271

theorem tailTrace_3587853 : CollatzResearch.WordTrace tailWord_3587853 prefixEnd_3587853 1842293106675856242337271 := by
  unfold tailWord_3587853
  simp only [CollatzResearch.WordTrace]
  refine ⟨130859749470828812353472213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87239832980552541568981475 130859749470828812353472213)
  ·
    refine ⟨3067025378222550289534505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 130859749470828812353472213 3067025378222550289534505)
    ·
      refine ⟨2300269033666912717150879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3067025378222550289534505 2300269033666912717150879)
      ·
        refine ⟨3450403550500369075726319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300269033666912717150879 3450403550500369075726319)
        ·
          refine ⟨5175605325750553613589479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450403550500369075726319 5175605325750553613589479)
          ·
            refine ⟨7763407988625830420384219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175605325750553613589479 7763407988625830420384219)
            ·
              refine ⟨11645111982938745630576329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763407988625830420384219 11645111982938745630576329)
              ·
                refine ⟨8733833987204059222932247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11645111982938745630576329 8733833987204059222932247)
                ·
                  refine ⟨13100750980806088834398371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733833987204059222932247 13100750980806088834398371)
                  ·
                    refine ⟨19651126471209133251597557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13100750980806088834398371 19651126471209133251597557)
                    ·
                      refine ⟨1842293106675856242337271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19651126471209133251597557 1842293106675856242337271)
                      ·
                        rfl

theorem cell23_3587853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3587853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587853 prefixEnd_3587853 := by exact prefixLift 3587853
  have htrace : WordTrace (prefixWord ++ tailWord_3587853) baseStart_3587853 baseEnd_3587853 := by
    simpa [prefixWord, tailWord_3587853, baseEnd_3587853] using wordTrace_append hprefix tailTrace_3587853
  have hstable : (prefixWord ++ tailWord_3587853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587853).length < 2 ^ (prefixWord ++ tailWord_3587853).sum := by decide
  have hdescent : baseEnd_3587853 < baseStart_3587853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587860 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3587860 : Nat := 118140960795 + 3587860 * 2 ^ 59
def prefixEnd_3587860 : Nat := 4983230072969 + 3 ^ 40 * 3587860 * 2
def baseEnd_3587860 : Nat := 614098900346812571649913

theorem tailTrace_3587860 : CollatzResearch.WordTrace tailWord_3587860 prefixEnd_3587860 614098900346812571649913 := by
  unfold tailWord_3587860
  simp only [CollatzResearch.WordTrace]
  refine ⟨65430002390901726274488517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87240003187868968365984689 65430002390901726274488517)
  ·
    refine ⟨12268125448294073676466597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65430002390901726274488517 12268125448294073676466597)
    ·
      refine ⟨2300273521555138814337487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12268125448294073676466597 2300273521555138814337487)
      ·
        refine ⟨3450410282332708221506231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300273521555138814337487 3450410282332708221506231)
        ·
          refine ⟨5175615423499062332259347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450410282332708221506231 5175615423499062332259347)
          ·
            refine ⟨7763423135248593498389021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175615423499062332259347 7763423135248593498389021)
            ·
              refine ⟨2911283675718222561895883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7763423135248593498389021 2911283675718222561895883)
              ·
                refine ⟨4366925513577333842843825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911283675718222561895883 4366925513577333842843825)
                ·
                  refine ⟨3275194135183000382132869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4366925513577333842843825 3275194135183000382132869)
                  ·
                    refine ⟨614098900346812571649913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3275194135183000382132869 614098900346812571649913)
                    ·
                      rfl

theorem cell23_3587860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3587860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587860 prefixEnd_3587860 := by exact prefixLift 3587860
  have htrace : WordTrace (prefixWord ++ tailWord_3587860) baseStart_3587860 baseEnd_3587860 := by
    simpa [prefixWord, tailWord_3587860, baseEnd_3587860] using wordTrace_append hprefix tailTrace_3587860
  have hstable : (prefixWord ++ tailWord_3587860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587860).length < 2 ^ (prefixWord ++ tailWord_3587860).sum := by decide
  have hdescent : baseEnd_3587860 < baseStart_3587860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587866 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3]
def baseStart_3587866 : Nat := 118140960795 + 3587866 * 2 ^ 59
def prefixEnd_3587866 : Nat := 4983230072969 + 3 ^ 40 * 3587866 * 2
def baseEnd_3587866 : Nat := 1842299781924364691474711

theorem tailTrace_3587866 : CollatzResearch.WordTrace tailWord_3587866 prefixEnd_3587866 1842299781924364691474711 := by
  unfold tailWord_3587866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32715055904945428893423863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87240149079854477049130301 32715055904945428893423863)
  ·
    refine ⟨49072583857418143340135795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32715055904945428893423863 49072583857418143340135795)
    ·
      refine ⟨73608875786127215010203693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49072583857418143340135795 73608875786127215010203693)
      ·
        refine ⟨27603328419797705628826385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73608875786127215010203693 27603328419797705628826385)
        ·
          refine ⟨20702496314848279221619789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27603328419797705628826385 20702496314848279221619789)
          ·
            refine ⟨7763436118068104708107421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20702496314848279221619789 7763436118068104708107421)
            ·
              refine ⟨2911288544275539265540283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7763436118068104708107421 2911288544275539265540283)
              ·
                refine ⟨4366932816413308898310425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911288544275539265540283 4366932816413308898310425)
                ·
                  refine ⟨3275199612309981673732819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4366932816413308898310425 3275199612309981673732819)
                  ·
                    refine ⟨4912799418464972510599229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3275199612309981673732819 4912799418464972510599229)
                    ·
                      refine ⟨1842299781924364691474711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4912799418464972510599229 1842299781924364691474711)
                      ·
                        rfl

theorem cell23_3587866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_3587866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587866 prefixEnd_3587866 := by exact prefixLift 3587866
  have htrace : WordTrace (prefixWord ++ tailWord_3587866) baseStart_3587866 baseEnd_3587866 := by
    simpa [prefixWord, tailWord_3587866, baseEnd_3587866] using wordTrace_append hprefix tailTrace_3587866
  have hstable : (prefixWord ++ tailWord_3587866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587866).length < 2 ^ (prefixWord ++ tailWord_3587866).sum := by decide
  have hdescent : baseEnd_3587866 < baseStart_3587866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587875 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 3]
def baseStart_3587875 : Nat := 118140960795 + 3587875 * 2 ^ 59
def prefixEnd_3587875 : Nat := 4983230072969 + 3 ^ 40 * 3587875 * 2
def baseEnd_3587875 : Nat := 1842304403250255156262169

theorem tailTrace_3587875 : CollatzResearch.WordTrace tailWord_3587875 prefixEnd_3587875 1842304403250255156262169 := by
  unfold tailWord_3587875
  simp only [CollatzResearch.WordTrace]
  refine ⟨130860551876749110110773079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87240367917832740073848719 130860551876749110110773079)
  ·
    refine ⟨196290827815123665166159619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130860551876749110110773079 196290827815123665166159619)
    ·
      refine ⟨294436241722685497749239429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196290827815123665166159619 294436241722685497749239429)
      ·
        refine ⟨55206795323003530827982393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294436241722685497749239429 55206795323003530827982393)
        ·
          refine ⟨41405096492252648120986795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55206795323003530827982393 41405096492252648120986795)
          ·
            refine ⟨62107644738378972181480193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41405096492252648120986795 62107644738378972181480193)
            ·
              refine ⟨46580733553784229136110145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62107644738378972181480193 46580733553784229136110145)
              ·
                refine ⟨34935550165338171852082609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46580733553784229136110145 34935550165338171852082609)
                ·
                  refine ⟨26201662624003628889061957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34935550165338171852082609 26201662624003628889061957)
                  ·
                    refine ⟨4912811742000680416699117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26201662624003628889061957 4912811742000680416699117)
                    ·
                      refine ⟨1842304403250255156262169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4912811742000680416699117 1842304403250255156262169)
                      ·
                        rfl

theorem cell23_3587875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_3587875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587875 prefixEnd_3587875 := by exact prefixLift 3587875
  have htrace : WordTrace (prefixWord ++ tailWord_3587875) baseStart_3587875 baseEnd_3587875 := by
    simpa [prefixWord, tailWord_3587875, baseEnd_3587875] using wordTrace_append hprefix tailTrace_3587875
  have hstable : (prefixWord ++ tailWord_3587875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587875).length < 2 ^ (prefixWord ++ tailWord_3587875).sum := by decide
  have hdescent : baseEnd_3587875 < baseStart_3587875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587876 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_3587876 : Nat := 118140960795 + 3587876 * 2 ^ 59
def prefixEnd_3587876 : Nat := 4983230072969 + 3 ^ 40 * 3587876 * 2
def baseEnd_3587876 : Nat := 1842304916730909652349665

theorem tailTrace_3587876 : CollatzResearch.WordTrace tailWord_3587876 prefixEnd_3587876 1842304916730909652349665 := by
  unfold tailWord_3587876
  simp only [CollatzResearch.WordTrace]
  refine ⟨65430294174872743640779741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87240392233163658187706321 65430294174872743640779741)
  ·
    refine ⟨24536360315577278865292403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65430294174872743640779741 24536360315577278865292403)
    ·
      refine ⟨36804540473365918297938605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24536360315577278865292403 36804540473365918297938605)
      ·
        refine ⟨13801702677512219361726977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36804540473365918297938605 13801702677512219361726977)
        ·
          refine ⟨10351277008134164521295233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13801702677512219361726977 10351277008134164521295233)
          ·
            refine ⟨7763457756100623390971425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10351277008134164521295233 7763457756100623390971425)
            ·
              refine ⟨5822593317075467543228569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7763457756100623390971425 5822593317075467543228569)
              ·
                refine ⟨4366944987806600657421427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5822593317075467543228569 4366944987806600657421427)
                ·
                  refine ⟨6550417481709900986132141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366944987806600657421427 6550417481709900986132141)
                  ·
                    refine ⟨2456406555641212869799553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6550417481709900986132141 2456406555641212869799553)
                    ·
                      refine ⟨1842304916730909652349665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456406555641212869799553 1842304916730909652349665)
                      ·
                        rfl

theorem cell23_3587876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_3587876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587876 prefixEnd_3587876 := by exact prefixLift 3587876
  have htrace : WordTrace (prefixWord ++ tailWord_3587876) baseStart_3587876 baseEnd_3587876 := by
    simpa [prefixWord, tailWord_3587876, baseEnd_3587876] using wordTrace_append hprefix tailTrace_3587876
  have hstable : (prefixWord ++ tailWord_3587876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587876).length < 2 ^ (prefixWord ++ tailWord_3587876).sum := by decide
  have hdescent : baseEnd_3587876 < baseStart_3587876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587889 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 4, 2, 2]
def baseStart_3587889 : Nat := 118140960795 + 3587889 * 2 ^ 59
def prefixEnd_3587889 : Nat := 4983230072969 + 3 ^ 40 * 3587889 * 2
def baseEnd_3587889 : Nat := 1842311591979418101487105

theorem tailTrace_3587889 : CollatzResearch.WordTrace tailWord_3587889 prefixEnd_3587889 1842311591979418101487105 := by
  unfold tailWord_3587889
  simp only [CollatzResearch.WordTrace]
  refine ⟨130861062498698390501782721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87240708332465593667855147 130861062498698390501782721)
  ·
    refine ⟨98145796874023792876337041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130861062498698390501782721 98145796874023792876337041)
    ·
      refine ⟨73609347655517844657252781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98145796874023792876337041 73609347655517844657252781)
      ·
        refine ⟨27603505370819191746469793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73609347655517844657252781 27603505370819191746469793)
        ·
          refine ⟨20702629028114393809852345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27603505370819191746469793 20702629028114393809852345)
          ·
            refine ⟨15526971771085795357389259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20702629028114393809852345 15526971771085795357389259)
            ·
              refine ⟨23290457656628693036083889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15526971771085795357389259 23290457656628693036083889)
              ·
                refine ⟨17467843242471519777062917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23290457656628693036083889 17467843242471519777062917)
                ·
                  refine ⟨3275220607963409958199297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17467843242471519777062917 3275220607963409958199297)
                  ·
                    refine ⟨2456415455972557468649473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3275220607963409958199297 2456415455972557468649473)
                    ·
                      refine ⟨1842311591979418101487105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456415455972557468649473 1842311591979418101487105)
                      ·
                        rfl

theorem cell23_3587889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_3587889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587889 prefixEnd_3587889 := by exact prefixLift 3587889
  have htrace : WordTrace (prefixWord ++ tailWord_3587889) baseStart_3587889 baseEnd_3587889 := by
    simpa [prefixWord, tailWord_3587889, baseEnd_3587889] using wordTrace_append hprefix tailTrace_3587889
  have hstable : (prefixWord ++ tailWord_3587889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587889).length < 2 ^ (prefixWord ++ tailWord_3587889).sum := by decide
  have hdescent : baseEnd_3587889 < baseStart_3587889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587892 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3587892 : Nat := 118140960795 + 3587892 * 2 ^ 59
def prefixEnd_3587892 : Nat := 4983230072969 + 3 ^ 40 * 3587892 * 2
def baseEnd_3587892 : Nat := 1842313132421381589749591

theorem tailTrace_3587892 : CollatzResearch.WordTrace tailWord_3587892 prefixEnd_3587892 1842313132421381589749591 := by
  unfold tailWord_3587892
  simp only [CollatzResearch.WordTrace]
  refine ⟨65430585958843761007070965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87240781278458348009427953 65430585958843761007070965)
  ·
    refine ⟨6134117433641602594412903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65430585958843761007070965 6134117433641602594412903)
    ·
      refine ⟨9201176150462403891619355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6134117433641602594412903 9201176150462403891619355)
      ·
        refine ⟨13801764225693605837429033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201176150462403891619355 13801764225693605837429033)
        ·
          refine ⟨10351323169270204378071775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13801764225693605837429033 10351323169270204378071775)
          ·
            refine ⟨15526984753905306567107663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10351323169270204378071775 15526984753905306567107663)
            ·
              refine ⟨23290477130857959850661495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15526984753905306567107663 23290477130857959850661495)
              ·
                refine ⟨34935715696286939775992243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23290477130857959850661495 34935715696286939775992243)
                ·
                  refine ⟨52403573544430409663988365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34935715696286939775992243 52403573544430409663988365)
                  ·
                    refine ⟨19651340079161403623995637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52403573544430409663988365 19651340079161403623995637)
                    ·
                      refine ⟨1842313132421381589749591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19651340079161403623995637 1842313132421381589749591)
                      ·
                        rfl

theorem cell23_3587892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3587892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587892 prefixEnd_3587892 := by exact prefixLift 3587892
  have htrace : WordTrace (prefixWord ++ tailWord_3587892) baseStart_3587892 baseEnd_3587892 := by
    simpa [prefixWord, tailWord_3587892, baseEnd_3587892] using wordTrace_append hprefix tailTrace_3587892
  have hstable : (prefixWord ++ tailWord_3587892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587892).length < 2 ^ (prefixWord ++ tailWord_3587892).sum := by decide
  have hdescent : baseEnd_3587892 < baseStart_3587892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587912 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 7]
def baseStart_3587912 : Nat := 118140960795 + 3587912 * 2 ^ 59
def prefixEnd_3587912 : Nat := 4983230072969 + 3 ^ 40 * 3587912 * 2
def baseEnd_3587912 : Nat := 204702600226052390166611

theorem tailTrace_3587912 : CollatzResearch.WordTrace tailWord_3587912 prefixEnd_3587912 204702600226052390166611 := by
  unfold tailWord_3587912
  simp only [CollatzResearch.WordTrace]
  refine ⟨65430950688807532714934995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87241267585076710286579993 65430950688807532714934995)
  ·
    refine ⟨98146426033211299072402493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65430950688807532714934995 98146426033211299072402493)
    ·
      refine ⟨36804909762454237152150935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98146426033211299072402493 36804909762454237152150935)
      ·
        refine ⟨55207364643681355728226403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36804909762454237152150935 55207364643681355728226403)
        ·
          refine ⟨82811046965522033592339605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55207364643681355728226403 82811046965522033592339605)
          ·
            refine ⟨3881767826508845324640919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82811046965522033592339605 3881767826508845324640919)
            ·
              refine ⟨5822651739763267986961379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881767826508845324640919 5822651739763267986961379)
              ·
                refine ⟨8733977609644901980442069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822651739763267986961379 8733977609644901980442069)
                ·
                  refine ⟨204702600226052390166611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8733977609644901980442069 204702600226052390166611)
                  ·
                    rfl

theorem cell23_3587912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 7].length) (baseStart_3587912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587912 prefixEnd_3587912 := by exact prefixLift 3587912
  have htrace : WordTrace (prefixWord ++ tailWord_3587912) baseStart_3587912 baseEnd_3587912 := by
    simpa [prefixWord, tailWord_3587912, baseEnd_3587912] using wordTrace_append hprefix tailTrace_3587912
  have hstable : (prefixWord ++ tailWord_3587912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587912).length < 2 ^ (prefixWord ++ tailWord_3587912).sum := by decide
  have hdescent : baseEnd_3587912 < baseStart_3587912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587945 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_3587945 : Nat := 118140960795 + 3587945 * 2 ^ 59
def prefixEnd_3587945 : Nat := 4983230072969 + 3 ^ 40 * 3587945 * 2
def baseEnd_3587945 : Nat := 1842340346896069882386847

theorem tailTrace_3587945 : CollatzResearch.WordTrace tailWord_3587945 prefixEnd_3587945 1842340346896069882386847 := by
  unfold tailWord_3587945
  simp only [CollatzResearch.WordTrace]
  refine ⟨130863104986495512065821289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87242069990997008043880859 130863104986495512065821289)
  ·
    refine ⟨98147328739871634049365967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130863104986495512065821289 98147328739871634049365967)
    ·
      refine ⟨147220993109807451074048951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98147328739871634049365967 147220993109807451074048951)
      ·
        refine ⟨220831489664711176611073427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147220993109807451074048951 220831489664711176611073427)
        ·
          refine ⟨331247234497066764916610141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220831489664711176611073427 331247234497066764916610141)
          ·
            refine ⟨124217712936400036843728803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331247234497066764916610141 124217712936400036843728803)
            ·
              refine ⟨186326569404600055265593205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124217712936400036843728803 186326569404600055265593205)
              ·
                refine ⟨17468115881681255181149363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186326569404600055265593205 17468115881681255181149363)
                ·
                  refine ⟨26202173822521882771724045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17468115881681255181149363 26202173822521882771724045)
                  ·
                    refine ⟨9825815183445706039396517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26202173822521882771724045 9825815183445706039396517)
                    ·
                      refine ⟨1842340346896069882386847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9825815183445706039396517 1842340346896069882386847)
                      ·
                        rfl

theorem cell23_3587945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_3587945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587945 prefixEnd_3587945 := by exact prefixLift 3587945
  have htrace : WordTrace (prefixWord ++ tailWord_3587945) baseStart_3587945 baseEnd_3587945 := by
    simpa [prefixWord, tailWord_3587945, baseEnd_3587945] using wordTrace_append hprefix tailTrace_3587945
  have hstable : (prefixWord ++ tailWord_3587945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587945).length < 2 ^ (prefixWord ++ tailWord_3587945).sum := by decide
  have hdescent : baseEnd_3587945 < baseStart_3587945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587962 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_3587962 : Nat := 118140960795 + 3587962 * 2 ^ 59
def prefixEnd_3587962 : Nat := 4983230072969 + 3 ^ 40 * 3587962 * 2
def baseEnd_3587962 : Nat := 1842349076067196315874269

theorem tailTrace_3587962 : CollatzResearch.WordTrace tailWord_3587962 prefixEnd_3587962 1842349076067196315874269 := by
  unfold tailWord_3587962
  simp only [CollatzResearch.WordTrace]
  refine ⟨32715931256858480992297535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87242483351622615979460093 32715931256858480992297535)
  ·
    refine ⟨49073896885287721488446303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32715931256858480992297535 49073896885287721488446303)
    ·
      refine ⟨73610845327931582232669455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49073896885287721488446303 73610845327931582232669455)
      ·
        refine ⟨110416267991897373349004183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73610845327931582232669455 110416267991897373349004183)
        ·
          refine ⟨165624401987846060023506275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110416267991897373349004183 165624401987846060023506275)
          ·
            refine ⟨248436602981769090035259413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165624401987846060023506275 248436602981769090035259413)
            ·
              refine ⟨11645465764770426095402785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248436602981769090035259413 11645465764770426095402785)
              ·
                refine ⟨8734099323577819571552089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11645465764770426095402785 8734099323577819571552089)
                ·
                  refine ⟨6550574492683364678664067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8734099323577819571552089 6550574492683364678664067)
                  ·
                    refine ⟨9825861739025047017996101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6550574492683364678664067 9825861739025047017996101)
                    ·
                      refine ⟨1842349076067196315874269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9825861739025047017996101 1842349076067196315874269)
                      ·
                        rfl

theorem cell23_3587962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_3587962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587962 prefixEnd_3587962 := by exact prefixLift 3587962
  have htrace : WordTrace (prefixWord ++ tailWord_3587962) baseStart_3587962 baseEnd_3587962 := by
    simpa [prefixWord, tailWord_3587962, baseEnd_3587962] using wordTrace_append hprefix tailTrace_3587962
  have hstable : (prefixWord ++ tailWord_3587962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587962).length < 2 ^ (prefixWord ++ tailWord_3587962).sum := by decide
  have hdescent : baseEnd_3587962 < baseStart_3587962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587965 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_3587965 : Nat := 118140960795 + 3587965 * 2 ^ 59
def prefixEnd_3587965 : Nat := 4983230072969 + 3 ^ 40 * 3587965 * 2
def baseEnd_3587965 : Nat := 1842350616509159804136755

theorem tailTrace_3587965 : CollatzResearch.WordTrace tailWord_3587965 prefixEnd_3587965 1842350616509159804136755 := by
  unfold tailWord_3587965
  simp only [CollatzResearch.WordTrace]
  refine ⟨130863834446423055481549349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87242556297615370321032899 130863834446423055481549349)
  ·
    refine ⟨24536968958704322902790503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130863834446423055481549349 24536968958704322902790503)
    ·
      refine ⟨36805453438056484354185755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24536968958704322902790503 36805453438056484354185755)
      ·
        refine ⟨55208180157084726531278633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36805453438056484354185755 55208180157084726531278633)
        ·
          refine ⟨41406135117813544898458975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55208180157084726531278633 41406135117813544898458975)
          ·
            refine ⟨62109202676720317347688463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41406135117813544898458975 62109202676720317347688463)
            ·
              refine ⟨93163804015080476021532695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62109202676720317347688463 93163804015080476021532695)
              ·
                refine ⟨139745706022620714032299043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93163804015080476021532695 139745706022620714032299043)
                ·
                  refine ⟨209618559033931071048448565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139745706022620714032299043 209618559033931071048448565)
                  ·
                    refine ⟨19651739909431037910792053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209618559033931071048448565 19651739909431037910792053)
                    ·
                      refine ⟨1842350616509159804136755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19651739909431037910792053 1842350616509159804136755)
                      ·
                        rfl

theorem cell23_3587965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_3587965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587965 prefixEnd_3587965 := by exact prefixLift 3587965
  have htrace : WordTrace (prefixWord ++ tailWord_3587965) baseStart_3587965 baseEnd_3587965 := by
    simpa [prefixWord, tailWord_3587965, baseEnd_3587965] using wordTrace_append hprefix tailTrace_3587965
  have hstable : (prefixWord ++ tailWord_3587965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587965).length < 2 ^ (prefixWord ++ tailWord_3587965).sum := by decide
  have hdescent : baseEnd_3587965 < baseStart_3587965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587966 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3587966 : Nat := 118140960795 + 3587966 * 2 ^ 59
def prefixEnd_3587966 : Nat := 4983230072969 + 3 ^ 40 * 3587966 * 2
def baseEnd_3587966 : Nat := 1842351129989814300224251

theorem tailTrace_3587966 : CollatzResearch.WordTrace tailWord_3587966 prefixEnd_3587966 1842351129989814300224251 := by
  unfold tailWord_3587966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357983864927429081541969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87242580612946288434890501 16357983864927429081541969)
  ·
    refine ⟨12268487898695571811156477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16357983864927429081541969 12268487898695571811156477)
    ·
      refine ⟨4600682962010839429183679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12268487898695571811156477 4600682962010839429183679)
      ·
        refine ⟨6901024443016259143775519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4600682962010839429183679 6901024443016259143775519)
        ·
          refine ⟨10351536664524388715663279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901024443016259143775519 10351536664524388715663279)
          ·
            refine ⟨15527304996786583073494919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10351536664524388715663279 15527304996786583073494919)
            ·
              refine ⟨23290957495179874610242379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15527304996786583073494919 23290957495179874610242379)
              ·
                refine ⟨34936436242769811915363569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23290957495179874610242379 34936436242769811915363569)
                ·
                  refine ⟨26202327182077358936522677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34936436242769811915363569 26202327182077358936522677)
                  ·
                    refine ⟨2456468173319752400299001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26202327182077358936522677 2456468173319752400299001)
                    ·
                      refine ⟨1842351129989814300224251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456468173319752400299001 1842351129989814300224251)
                      ·
                        rfl

theorem cell23_3587966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3587966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587966 prefixEnd_3587966 := by exact prefixLift 3587966
  have htrace : WordTrace (prefixWord ++ tailWord_3587966) baseStart_3587966 baseEnd_3587966 := by
    simpa [prefixWord, tailWord_3587966, baseEnd_3587966] using wordTrace_append hprefix tailTrace_3587966
  have hstable : (prefixWord ++ tailWord_3587966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587966).length < 2 ^ (prefixWord ++ tailWord_3587966).sum := by decide
  have hdescent : baseEnd_3587966 < baseStart_3587966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587996 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3587996 : Nat := 118140960795 + 3587996 * 2 ^ 59
def prefixEnd_3587996 : Nat := 4983230072969 + 3 ^ 40 * 3587996 * 2
def baseEnd_3587996 : Nat := 1842366534409449182849113

theorem tailTrace_3587996 : CollatzResearch.WordTrace tailWord_3587996 prefixEnd_3587996 1842366534409449182849113 := by
  unfold tailWord_3587996
  simp only [CollatzResearch.WordTrace]
  refine ⟨65432482554655373887963921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87243310072873831850618561 65432482554655373887963921)
  ·
    refine ⟨49074361915991530415972941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65432482554655373887963921 49074361915991530415972941)
    ·
      refine ⟨18402885718496823905989853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49074361915991530415972941 18402885718496823905989853)
      ·
        refine ⟨6901082144436308964746195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18402885718496823905989853 6901082144436308964746195)
        ·
          refine ⟨10351623216654463447119293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901082144436308964746195 10351623216654463447119293)
          ·
            refine ⟨3881858706245423792669735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10351623216654463447119293 3881858706245423792669735)
            ·
              refine ⟨5822788059368135689004603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881858706245423792669735 5822788059368135689004603)
              ·
                refine ⟨8734182089052203533506905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822788059368135689004603 8734182089052203533506905)
                ·
                  refine ⟨6550636566789152650130179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8734182089052203533506905 6550636566789152650130179)
                  ·
                    refine ⟨9825954850183728975195269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6550636566789152650130179 9825954850183728975195269)
                    ·
                      refine ⟨1842366534409449182849113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9825954850183728975195269 1842366534409449182849113)
                      ·
                        rfl

theorem cell23_3587996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3587996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587996 prefixEnd_3587996 := by exact prefixLift 3587996
  have htrace : WordTrace (prefixWord ++ tailWord_3587996) baseStart_3587996 baseEnd_3587996 := by
    simpa [prefixWord, tailWord_3587996, baseEnd_3587996] using wordTrace_append hprefix tailTrace_3587996
  have hstable : (prefixWord ++ tailWord_3587996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587996).length < 2 ^ (prefixWord ++ tailWord_3587996).sum := by decide
  have hdescent : baseEnd_3587996 < baseStart_3587996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587999 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3587999 : Nat := 118140960795 + 3587999 * 2 ^ 59
def prefixEnd_3587999 : Nat := 4983230072969 + 3 ^ 40 * 3587999 * 2
def baseEnd_3587999 : Nat := 1842368074851412671111599

theorem tailTrace_3587999 : CollatzResearch.WordTrace tailWord_3587999 prefixEnd_3587999 1842368074851412671111599 := by
  unfold tailWord_3587999
  simp only [CollatzResearch.WordTrace]
  refine ⟨130865074528299879288287051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87243383018866586192191367 130865074528299879288287051)
  ·
    refine ⟨196297611792449818932430577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130865074528299879288287051 196297611792449818932430577)
    ·
      refine ⟨147223208844337364199322933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196297611792449818932430577 147223208844337364199322933)
      ·
        refine ⟨13802175829156627893686525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147223208844337364199322933 13802175829156627893686525)
        ·
          refine ⟨5175815935933735460132447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13802175829156627893686525 5175815935933735460132447)
          ·
            refine ⟨7763723903900603190198671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175815935933735460132447 7763723903900603190198671)
            ·
              refine ⟨11645585855850904785298007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763723903900603190198671 11645585855850904785298007)
              ·
                refine ⟨17468378783776357177947011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645585855850904785298007 17468378783776357177947011)
                ·
                  refine ⟨26202568175664535766920517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17468378783776357177947011 26202568175664535766920517)
                  ·
                    refine ⟨4912981532937100456297597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26202568175664535766920517 4912981532937100456297597)
                    ·
                      refine ⟨1842368074851412671111599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4912981532937100456297597 1842368074851412671111599)
                      ·
                        rfl

theorem cell23_3587999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3587999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3587999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3587999 prefixEnd_3587999 := by exact prefixLift 3587999
  have htrace : WordTrace (prefixWord ++ tailWord_3587999) baseStart_3587999 baseEnd_3587999 := by
    simpa [prefixWord, tailWord_3587999, baseEnd_3587999] using wordTrace_append hprefix tailTrace_3587999
  have hstable : (prefixWord ++ tailWord_3587999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587999).length < 2 ^ (prefixWord ++ tailWord_3587999).sum := by decide
  have hdescent : baseEnd_3587999 < baseStart_3587999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588005 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3588005 : Nat := 118140960795 + 3588005 * 2 ^ 59
def prefixEnd_3588005 : Nat := 4983230072969 + 3 ^ 40 * 3588005 * 2
def baseEnd_3588005 : Nat := 1842371155735339647636571

theorem tailTrace_3588005 : CollatzResearch.WordTrace tailWord_3588005 prefixEnd_3588005 1842371155735339647636571 := by
  unfold tailWord_3588005
  simp only [CollatzResearch.WordTrace]
  refine ⟨130865293366278142313005469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87243528910852094875336979 130865293366278142313005469)
  ·
    refine ⟨49074485012354303367377051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130865293366278142313005469 49074485012354303367377051)
    ·
      refine ⟨73611727518531455051065577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49074485012354303367377051 73611727518531455051065577)
      ·
        refine ⟨55208795638898591288299183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73611727518531455051065577 55208795638898591288299183)
        ·
          refine ⟨82813193458347886932448775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55208795638898591288299183 82813193458347886932448775)
          ·
            refine ⟨124219790187521830398673163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82813193458347886932448775 124219790187521830398673163)
            ·
              refine ⟨186329685281282745598009745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124219790187521830398673163 186329685281282745598009745)
              ·
                refine ⟨139747263960962059198507309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186329685281282745598009745 139747263960962059198507309)
                ·
                  refine ⟨52405223985360772199440241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139747263960962059198507309 52405223985360772199440241)
                  ·
                    refine ⟨39303917989020579149580181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52405223985360772199440241 39303917989020579149580181)
                    ·
                      refine ⟨1842371155735339647636571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39303917989020579149580181 1842371155735339647636571)
                      ·
                        rfl

theorem cell23_3588005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3588005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588005 prefixEnd_3588005 := by exact prefixLift 3588005
  have htrace : WordTrace (prefixWord ++ tailWord_3588005) baseStart_3588005 baseEnd_3588005 := by
    simpa [prefixWord, tailWord_3588005, baseEnd_3588005] using wordTrace_append hprefix tailTrace_3588005
  have hstable : (prefixWord ++ tailWord_3588005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588005).length < 2 ^ (prefixWord ++ tailWord_3588005).sum := by decide
  have hdescent : baseEnd_3588005 < baseStart_3588005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588063 : List Nat := [1, 1, 2, 3, 4, 1, 3, 3, 1, 1, 3]
def baseStart_3588063 : Nat := 118140960795 + 3588063 * 2 ^ 59
def prefixEnd_3588063 : Nat := 4983230072969 + 3 ^ 40 * 3588063 * 2
def baseEnd_3588063 : Nat := 1842400937613300420711305

theorem tailTrace_3588063 : CollatzResearch.WordTrace tailWord_3588063 prefixEnd_3588063 1842400937613300420711305 := by
  unfold tailWord_3588063
  simp only [CollatzResearch.WordTrace]
  refine ⟨130867408800068018218616843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87244939200045345479077895 130867408800068018218616843)
  ·
    refine ⟨196301113200102027327925265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130867408800068018218616843 196301113200102027327925265)
    ·
      refine ⟨147225834900076520495943949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196301113200102027327925265 147225834900076520495943949)
      ·
        refine ⟨55209688087528695185978981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147225834900076520495943949 55209688087528695185978981)
        ·
          refine ⟨10351816516411630347371059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55209688087528695185978981 10351816516411630347371059)
          ·
            refine ⟨15527724774617445521056589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10351816516411630347371059 15527724774617445521056589)
            ·
              refine ⟨5822896790481542070396221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15527724774617445521056589 5822896790481542070396221)
              ·
                refine ⟨2183586296430578276398583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5822896790481542070396221 2183586296430578276398583)
                ·
                  refine ⟨3275379444645867414597875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183586296430578276398583 3275379444645867414597875)
                  ·
                    refine ⟨4913069166968801121896813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3275379444645867414597875 4913069166968801121896813)
                    ·
                      refine ⟨1842400937613300420711305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4913069166968801121896813 1842400937613300420711305)
                      ·
                        rfl

theorem cell23_3588063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_3588063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588063 prefixEnd_3588063 := by exact prefixLift 3588063
  have htrace : WordTrace (prefixWord ++ tailWord_3588063) baseStart_3588063 baseEnd_3588063 := by
    simpa [prefixWord, tailWord_3588063, baseEnd_3588063] using wordTrace_append hprefix tailTrace_3588063
  have hstable : (prefixWord ++ tailWord_3588063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588063).length < 2 ^ (prefixWord ++ tailWord_3588063).sum := by decide
  have hdescent : baseEnd_3588063 < baseStart_3588063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588079 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 2, 4]
def baseStart_3588079 : Nat := 118140960795 + 3588079 * 2 ^ 59
def prefixEnd_3588079 : Nat := 4983230072969 + 3 ^ 40 * 3588079 * 2
def baseEnd_3588079 : Nat := 614136384434590786037077

theorem tailTrace_3588079 : CollatzResearch.WordTrace tailWord_3588079 prefixEnd_3588079 614136384434590786037077 := by
  unfold tailWord_3588079
  simp only [CollatzResearch.WordTrace]
  refine ⟨130867992368010052951199291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87245328245340035300799527 130867992368010052951199291)
  ·
    refine ⟨196301988552015079426798937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130867992368010052951199291 196301988552015079426798937)
    ·
      refine ⟨147226491414011309570099203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196301988552015079426798937 147226491414011309570099203)
      ·
        refine ⟨220839737121016964355148805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147226491414011309570099203 220839737121016964355148805)
        ·
          refine ⟨41407450710190680816590401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220839737121016964355148805 41407450710190680816590401)
          ·
            refine ⟨31055588032643010612442801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41407450710190680816590401 31055588032643010612442801)
            ·
              refine ⟨23291691024482257959332101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31055588032643010612442801 23291691024482257959332101)
              ·
                refine ⟨4367192067090423367374769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23291691024482257959332101 4367192067090423367374769)
                ·
                  refine ⟨3275394050317817525531077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4367192067090423367374769 3275394050317817525531077)
                  ·
                    refine ⟨614136384434590786037077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3275394050317817525531077 614136384434590786037077)
                    ·
                      rfl

theorem cell23_3588079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_3588079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588079 prefixEnd_3588079 := by exact prefixLift 3588079
  have htrace : WordTrace (prefixWord ++ tailWord_3588079) baseStart_3588079 baseEnd_3588079 := by
    simpa [prefixWord, tailWord_3588079, baseEnd_3588079] using wordTrace_append hprefix tailTrace_3588079
  have hstable : (prefixWord ++ tailWord_3588079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588079).length < 2 ^ (prefixWord ++ tailWord_3588079).sum := by decide
  have hdescent : baseEnd_3588079 < baseStart_3588079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588092 : List Nat := [2, 2, 2, 1, 2, 2, 4, 8]
def baseStart_3588092 : Nat := 118140960795 + 3588092 * 2 ^ 59
def prefixEnd_3588092 : Nat := 4983230072969 + 3 ^ 40 * 3588092 * 2
def baseEnd_3588092 : Nat := 68237623279714103972173

theorem tailTrace_3588092 : CollatzResearch.WordTrace tailWord_3588092 prefixEnd_3588092 68237623279714103972173 := by
  unfold tailWord_3588092
  simp only [CollatzResearch.WordTrace]
  refine ⟨65434233258481478085711265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87245644344641970780948353 65434233258481478085711265)
  ·
    refine ⟨49075674943861108564283449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65434233258481478085711265 49075674943861108564283449)
    ·
      refine ⟨36806756207895831423212587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49075674943861108564283449 36806756207895831423212587)
      ·
        refine ⟨55210134311843747134818881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36806756207895831423212587 55210134311843747134818881)
        ·
          refine ⟨41407600733882810351114161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55210134311843747134818881 41407600733882810351114161)
          ·
            refine ⟨31055700550412107763335621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41407600733882810351114161 31055700550412107763335621)
            ·
              refine ⟨5822943853202270205625429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31055700550412107763335621 5822943853202270205625429)
              ·
                refine ⟨68237623279714103972173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5822943853202270205625429 68237623279714103972173)
                ·
                  rfl

theorem cell23_3588092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 8].length) (baseStart_3588092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588092 prefixEnd_3588092 := by exact prefixLift 3588092
  have htrace : WordTrace (prefixWord ++ tailWord_3588092) baseStart_3588092 baseEnd_3588092 := by
    simpa [prefixWord, tailWord_3588092, baseEnd_3588092] using wordTrace_append hprefix tailTrace_3588092
  have hstable : (prefixWord ++ tailWord_3588092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588092).length < 2 ^ (prefixWord ++ tailWord_3588092).sum := by decide
  have hdescent : baseEnd_3588092 < baseStart_3588092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588100 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_3588100 : Nat := 118140960795 + 3588100 * 2 ^ 59
def prefixEnd_3588100 : Nat := 4983230072969 + 3 ^ 40 * 3588100 * 2
def baseEnd_3588100 : Nat := 614139978799172258649545

theorem tailTrace_3588100 : CollatzResearch.WordTrace tailWord_3588100 prefixEnd_3588100 614139978799172258649545 := by
  unfold tailWord_3588100
  simp only [CollatzResearch.WordTrace]
  refine ⟨65434379150466986768856877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87245838867289315691809169 65434379150466986768856877)
  ·
    refine ⟨24537892181425120038321329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65434379150466986768856877 24537892181425120038321329)
    ·
      refine ⟨18403419136068840028740997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24537892181425120038321329 18403419136068840028740997)
      ·
        refine ⟨3450641088012907505388937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18403419136068840028740997 3450641088012907505388937)
        ·
          refine ⟨2587980816009680629041703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3450641088012907505388937 2587980816009680629041703)
          ·
            refine ⟨3881971224014520943562555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587980816009680629041703 3881971224014520943562555)
            ·
              refine ⟨5822956836021781415343833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881971224014520943562555 5822956836021781415343833)
              ·
                refine ⟨4367217627016336061507875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5822956836021781415343833 4367217627016336061507875)
                ·
                  refine ⟨6550826440524504092261813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367217627016336061507875 6550826440524504092261813)
                  ·
                    refine ⟨614139978799172258649545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6550826440524504092261813 614139978799172258649545)
                    ·
                      rfl

theorem cell23_3588100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_3588100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588100 prefixEnd_3588100 := by exact prefixLift 3588100
  have htrace : WordTrace (prefixWord ++ tailWord_3588100) baseStart_3588100 baseEnd_3588100 := by
    simpa [prefixWord, tailWord_3588100, baseEnd_3588100] using wordTrace_append hprefix tailTrace_3588100
  have hstable : (prefixWord ++ tailWord_3588100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588100).length < 2 ^ (prefixWord ++ tailWord_3588100).sum := by decide
  have hdescent : baseEnd_3588100 < baseStart_3588100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588106 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_3588106 : Nat := 118140960795 + 3588106 * 2 ^ 59
def prefixEnd_3588106 : Nat := 4983230072969 + 3 ^ 40 * 3588106 * 2
def baseEnd_3588106 : Nat := 1842423017281443752473607

theorem tailTrace_3588106 : CollatzResearch.WordTrace tailWord_3588106 prefixEnd_3588106 1842423017281443752473607 := by
  unfold tailWord_3588106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32717244284728059140608043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87245984759274824374954781 32717244284728059140608043)
  ·
    refine ⟨49075866427092088710912065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32717244284728059140608043 49075866427092088710912065)
    ·
      refine ⟨36806899820319066533184049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49075866427092088710912065 36806899820319066533184049)
      ·
        refine ⟨27605174865239299899888037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36806899820319066533184049 27605174865239299899888037)
        ·
          refine ⟨5175970287232368731229007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27605174865239299899888037 5175970287232368731229007)
          ·
            refine ⟨7763955430848553096843511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175970287232368731229007 7763955430848553096843511)
            ·
              refine ⟨11645933146272829645265267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763955430848553096843511 11645933146272829645265267)
              ·
                refine ⟨17468899719409244467897901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645933146272829645265267 17468899719409244467897901)
                ·
                  refine ⟨6550837394778466675461713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17468899719409244467897901 6550837394778466675461713)
                  ·
                    refine ⟨4913128046083850006596285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6550837394778466675461713 4913128046083850006596285)
                    ·
                      refine ⟨1842423017281443752473607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4913128046083850006596285 1842423017281443752473607)
                      ·
                        rfl

theorem cell23_3588106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_3588106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588106 prefixEnd_3588106 := by exact prefixLift 3588106
  have htrace : WordTrace (prefixWord ++ tailWord_3588106) baseStart_3588106 baseEnd_3588106 := by
    simpa [prefixWord, tailWord_3588106, baseEnd_3588106] using wordTrace_append hprefix tailTrace_3588106
  have hstable : (prefixWord ++ tailWord_3588106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588106).length < 2 ^ (prefixWord ++ tailWord_3588106).sum := by decide
  have hdescent : baseEnd_3588106 < baseStart_3588106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588146 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_3588146 : Nat := 118140960795 + 3588146 * 2 ^ 59
def prefixEnd_3588146 : Nat := 4983230072969 + 3 ^ 40 * 3588146 * 2
def baseEnd_3588146 : Nat := 1842443556507623595973423

theorem tailTrace_3588146 : CollatzResearch.WordTrace tailWord_3588146 prefixEnd_3588146 1842443556507623595973423 := by
  unfold tailWord_3588146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32717609014691830848472073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87246957372511548929258861 32717609014691830848472073)
  ·
    refine ⟨24538206761018873136354055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32717609014691830848472073 24538206761018873136354055)
    ·
      refine ⟨36807310141528309704531083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24538206761018873136354055 36807310141528309704531083)
      ·
        refine ⟨55210965212292464556796625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36807310141528309704531083 55210965212292464556796625)
        ·
          refine ⟨41408223909219348417597469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55210965212292464556796625 41408223909219348417597469)
          ·
            refine ⟨15528083965957255656599051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41408223909219348417597469 15528083965957255656599051)
            ·
              refine ⟨23292125948935883484898577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15528083965957255656599051 23292125948935883484898577)
              ·
                refine ⟨17469094461701912613673933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23292125948935883484898577 17469094461701912613673933)
                ·
                  refine ⟨6550910423138217230127725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17469094461701912613673933 6550910423138217230127725)
                  ·
                    refine ⟨2456591408676831461297897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6550910423138217230127725 2456591408676831461297897)
                    ·
                      refine ⟨1842443556507623595973423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456591408676831461297897 1842443556507623595973423)
                      ·
                        rfl

theorem cell23_3588146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_3588146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588146 prefixEnd_3588146 := by exact prefixLift 3588146
  have htrace : WordTrace (prefixWord ++ tailWord_3588146) baseStart_3588146 baseEnd_3588146 := by
    simpa [prefixWord, tailWord_3588146, baseEnd_3588146] using wordTrace_append hprefix tailTrace_3588146
  have hstable : (prefixWord ++ tailWord_3588146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588146).length < 2 ^ (prefixWord ++ tailWord_3588146).sum := by decide
  have hdescent : baseEnd_3588146 < baseStart_3588146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588166 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3588166 : Nat := 118140960795 + 3588166 * 2 ^ 59
def prefixEnd_3588166 : Nat := 4983230072969 + 3 ^ 40 * 3588166 * 2
def baseEnd_3588166 : Nat := 1842453826120713517723331

theorem tailTrace_3588166 : CollatzResearch.WordTrace tailWord_3588166 prefixEnd_3588166 1842453826120713517723331 := by
  unfold tailWord_3588166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089723922459214587800511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87247443679129911206410901 4089723922459214587800511)
  ·
    refine ⟨6134585883688821881700767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4089723922459214587800511 6134585883688821881700767)
    ·
      refine ⟨9201878825533232822551151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6134585883688821881700767 9201878825533232822551151)
      ·
        refine ⟨13802818238299849233826727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201878825533232822551151 13802818238299849233826727)
        ·
          refine ⟨20704227357449773850740091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13802818238299849233826727 20704227357449773850740091)
          ·
            refine ⟨31056341036174660776110137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20704227357449773850740091 31056341036174660776110137)
            ·
              refine ⟨23292255777130995582082603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31056341036174660776110137 23292255777130995582082603)
              ·
                refine ⟨34938383665696493373123905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23292255777130995582082603 34938383665696493373123905)
                ·
                  refine ⟨26203787749272370029842929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34938383665696493373123905 26203787749272370029842929)
                  ·
                    refine ⟨19652840811954277522382197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26203787749272370029842929 19652840811954277522382197)
                    ·
                      refine ⟨1842453826120713517723331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19652840811954277522382197 1842453826120713517723331)
                      ·
                        rfl

theorem cell23_3588166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3588166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588166 prefixEnd_3588166 := by exact prefixLift 3588166
  have htrace : WordTrace (prefixWord ++ tailWord_3588166) baseStart_3588166 baseEnd_3588166 := by
    simpa [prefixWord, tailWord_3588166, baseEnd_3588166] using wordTrace_append hprefix tailTrace_3588166
  have hstable : (prefixWord ++ tailWord_3588166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588166).length < 2 ^ (prefixWord ++ tailWord_3588166).sum := by decide
  have hdescent : baseEnd_3588166 < baseStart_3588166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588199 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 7]
def baseStart_3588199 : Nat := 118140960795 + 3588199 * 2 ^ 59
def prefixEnd_3588199 : Nat := 4983230072969 + 3 ^ 40 * 3588199 * 2
def baseEnd_3588199 : Nat := 204718974553590209845631

theorem tailTrace_3588199 : CollatzResearch.WordTrace tailWord_3588199 prefixEnd_3588199 204718974553590209845631 := by
  unfold tailWord_3588199
  simp only [CollatzResearch.WordTrace]
  refine ⟨130872369127575313445567651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87248246085050208963711767 130872369127575313445567651)
  ·
    refine ⟨196308553691362970168351477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130872369127575313445567651 196308553691362970168351477)
    ·
      refine ⟨18403926908565278453282951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196308553691362970168351477 18403926908565278453282951)
      ·
        refine ⟨27605890362847917679924427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18403926908565278453282951 27605890362847917679924427)
        ·
          refine ⟨41408835544271876519886641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27605890362847917679924427 41408835544271876519886641)
          ·
            refine ⟨31056626658203907389914981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41408835544271876519886641 31056626658203907389914981)
            ·
              refine ⟨5823117498413232635609059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31056626658203907389914981 5823117498413232635609059)
              ·
                refine ⟨8734676247619848953413589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823117498413232635609059 8734676247619848953413589)
                ·
                  refine ⟨204718974553590209845631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8734676247619848953413589 204718974553590209845631)
                  ·
                    rfl

theorem cell23_3588199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 7].length) (baseStart_3588199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588199 prefixEnd_3588199 := by exact prefixLift 3588199
  have htrace : WordTrace (prefixWord ++ tailWord_3588199) baseStart_3588199 baseEnd_3588199 := by
    simpa [prefixWord, tailWord_3588199, baseEnd_3588199] using wordTrace_append hprefix tailTrace_3588199
  have hstable : (prefixWord ++ tailWord_3588199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588199).length < 2 ^ (prefixWord ++ tailWord_3588199).sum := by decide
  have hdescent : baseEnd_3588199 < baseStart_3588199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588209 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_3588209 : Nat := 118140960795 + 3588209 * 2 ^ 59
def prefixEnd_3588209 : Nat := 4983230072969 + 3 ^ 40 * 3588209 * 2
def baseEnd_3588209 : Nat := 1842475905788856849485633

theorem tailTrace_3588209 : CollatzResearch.WordTrace tailWord_3588209 prefixEnd_3588209 1842475905788856849485633 := by
  unfold tailWord_3588209
  simp only [CollatzResearch.WordTrace]
  refine ⟨130872733857539085153431681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87248489238359390102287787 130872733857539085153431681)
  ·
    refine ⟨98154550393154313865073761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130872733857539085153431681 98154550393154313865073761)
    ·
      refine ⟨73615912794865735398805321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98154550393154313865073761 73615912794865735398805321)
      ·
        refine ⟨55211934596149301549103991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73615912794865735398805321 55211934596149301549103991)
        ·
          refine ⟨82817901894223952323655987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55211934596149301549103991 82817901894223952323655987)
          ·
            refine ⟨124226852841335928485483981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82817901894223952323655987 124226852841335928485483981)
            ·
              refine ⟨46585069815500973182056493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124226852841335928485483981 46585069815500973182056493)
              ·
                refine ⟨17469401180812864943271185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46585069815500973182056493 17469401180812864943271185)
                ·
                  refine ⟨13102050885609648707453389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17469401180812864943271185 13102050885609648707453389)
                  ·
                    refine ⟨4913269082103618265295021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13102050885609648707453389 4913269082103618265295021)
                    ·
                      refine ⟨1842475905788856849485633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4913269082103618265295021 1842475905788856849485633)
                      ·
                        rfl

theorem cell23_3588209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_3588209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588209 prefixEnd_3588209 := by exact prefixLift 3588209
  have htrace : WordTrace (prefixWord ++ tailWord_3588209) baseStart_3588209 baseEnd_3588209 := by
    simpa [prefixWord, tailWord_3588209, baseEnd_3588209] using wordTrace_append hprefix tailTrace_3588209
  have hstable : (prefixWord ++ tailWord_3588209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588209).length < 2 ^ (prefixWord ++ tailWord_3588209).sum := by decide
  have hdescent : baseEnd_3588209 < baseStart_3588209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588229 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_3588229 : Nat := 118140960795 + 3588229 * 2 ^ 59
def prefixEnd_3588229 : Nat := 4983230072969 + 3 ^ 40 * 3588229 * 2
def baseEnd_3588229 : Nat := 614162058467315590411847

theorem tailTrace_3588229 : CollatzResearch.WordTrace tailWord_3588229 prefixEnd_3588229 614162058467315590411847 := by
  unfold tailWord_3588229
  simp only [CollatzResearch.WordTrace]
  refine ⟨130873463317466628569159741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87248975544977752379439827 130873463317466628569159741)
  ·
    refine ⟨49077548744049985713434903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130873463317466628569159741 49077548744049985713434903)
    ·
      refine ⟨73616323116074978570152355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49077548744049985713434903 73616323116074978570152355)
      ·
        refine ⟨110424484674112467855228533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73616323116074978570152355 110424484674112467855228533)
        ·
          refine ⟨10352295438198043861427675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110424484674112467855228533 10352295438198043861427675)
          ·
            refine ⟨15528443157297065792141513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10352295438198043861427675 15528443157297065792141513)
            ·
              refine ⟨11646332367972799344106135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15528443157297065792141513 11646332367972799344106135)
              ·
                refine ⟨17469498551959199016159203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11646332367972799344106135 17469498551959199016159203)
                ·
                  refine ⟨26204247827938798524238805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17469498551959199016159203 26204247827938798524238805)
                  ·
                    refine ⟨614162058467315590411847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26204247827938798524238805 614162058467315590411847)
                    ·
                      rfl

theorem cell23_3588229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_3588229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588229 prefixEnd_3588229 := by exact prefixLift 3588229
  have htrace : WordTrace (prefixWord ++ tailWord_3588229) baseStart_3588229 baseEnd_3588229 := by
    simpa [prefixWord, tailWord_3588229, baseEnd_3588229] using wordTrace_append hprefix tailTrace_3588229
  have hstable : (prefixWord ++ tailWord_3588229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588229).length < 2 ^ (prefixWord ++ tailWord_3588229).sum := by decide
  have hdescent : baseEnd_3588229 < baseStart_3588229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588250 : List Nat := [3, 1, 1, 5, 2, 1, 3, 2, 5]
def baseStart_3588250 : Nat := 118140960795 + 3588250 * 2 ^ 59
def prefixEnd_3588250 : Nat := 4983230072969 + 3 ^ 40 * 3588250 * 2
def baseEnd_3588250 : Nat := 204721884277299021008105

theorem tailTrace_3588250 : CollatzResearch.WordTrace tailWord_3588250 prefixEnd_3588250 204721884277299021008105 := by
  unfold tailWord_3588250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32718557312597637288918551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87249486166927032770449469 32718557312597637288918551)
  ·
    refine ⟨49077835968896455933377827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32718557312597637288918551 49077835968896455933377827)
    ·
      refine ⟨73616753953344683900066741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49077835968896455933377827 73616753953344683900066741)
      ·
        refine ⟨6901570683126064115631257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73616753953344683900066741 6901570683126064115631257)
        ·
          refine ⟨5176178012344548086723443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6901570683126064115631257 5176178012344548086723443)
          ·
            refine ⟨7764267018516822130085165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176178012344548086723443 7764267018516822130085165)
            ·
              refine ⟨2911600131943808298781937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7764267018516822130085165 2911600131943808298781937)
              ·
                refine ⟨2183700098957856224086453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911600131943808298781937 2183700098957856224086453)
                ·
                  refine ⟨204721884277299021008105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2183700098957856224086453 204721884277299021008105)
                  ·
                    rfl

theorem cell23_3588250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_3588250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588250 prefixEnd_3588250 := by exact prefixLift 3588250
  have htrace : WordTrace (prefixWord ++ tailWord_3588250) baseStart_3588250 baseEnd_3588250 := by
    simpa [prefixWord, tailWord_3588250, baseEnd_3588250] using wordTrace_append hprefix tailTrace_3588250
  have hstable : (prefixWord ++ tailWord_3588250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588250).length < 2 ^ (prefixWord ++ tailWord_3588250).sum := by decide
  have hdescent : baseEnd_3588250 < baseStart_3588250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588306 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 6]
def baseStart_3588306 : Nat := 118140960795 + 3588306 * 2 ^ 59
def prefixEnd_3588306 : Nat := 4983230072969 + 3 ^ 40 * 3588306 * 2
def baseEnd_3588306 : Nat := 204725079268038107774743

theorem tailTrace_3588306 : CollatzResearch.WordTrace tailWord_3588306 prefixEnd_3588306 204725079268038107774743 := by
  unfold tailWord_3588306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32719067934546917679928193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87250847825458447146475181 32719067934546917679928193)
  ·
    refine ⟨24539300950910188259946145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32719067934546917679928193 24539300950910188259946145)
    ·
      refine ⟨18404475713182641194959609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24539300950910188259946145 18404475713182641194959609)
      ·
        refine ⟨13803356784886980896219707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18404475713182641194959609 13803356784886980896219707)
        ·
          refine ⟨20705035177330471344329561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13803356784886980896219707 20705035177330471344329561)
          ·
            refine ⟨15528776382997853508247171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20705035177330471344329561 15528776382997853508247171)
            ·
              refine ⟨23293164574496780262370757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15528776382997853508247171 23293164574496780262370757)
              ·
                refine ⟨4367468357718146299194517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23293164574496780262370757 4367468357718146299194517)
                ·
                  refine ⟨204725079268038107774743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4367468357718146299194517 204725079268038107774743)
                  ·
                    rfl

theorem cell23_3588306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_3588306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588306 prefixEnd_3588306 := by exact prefixLift 3588306
  have htrace : WordTrace (prefixWord ++ tailWord_3588306) baseStart_3588306 baseEnd_3588306 := by
    simpa [prefixWord, tailWord_3588306, baseEnd_3588306] using wordTrace_append hprefix tailTrace_3588306
  have hstable : (prefixWord ++ tailWord_3588306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588306).length < 2 ^ (prefixWord ++ tailWord_3588306).sum := by decide
  have hdescent : baseEnd_3588306 < baseStart_3588306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588376 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3588376 : Nat := 118140960795 + 3588376 * 2 ^ 59
def prefixEnd_3588376 : Nat := 4983230072969 + 3 ^ 40 * 3588376 * 2
def baseEnd_3588376 : Nat := 1842561657058157696097365

theorem tailTrace_3588376 : CollatzResearch.WordTrace tailWord_3588376 prefixEnd_3588376 1842561657058157696097365 := by
  unfold tailWord_3588376
  simp only [CollatzResearch.WordTrace]
  refine ⟨65439412423967036337380491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87252549898622715116507321 65439412423967036337380491)
  ·
    refine ⟨98159118635950554506070737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65439412423967036337380491 98159118635950554506070737)
    ·
      refine ⟨73619338976962915879553053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98159118635950554506070737 73619338976962915879553053)
      ·
        refine ⟨27607252116361093454832395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73619338976962915879553053 27607252116361093454832395)
        ·
          refine ⟨41410878174541640182248593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27607252116361093454832395 41410878174541640182248593)
          ·
            refine ⟨31058158630906230136686445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41410878174541640182248593 31058158630906230136686445)
            ·
              refine ⟨11646809486589836301257417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31058158630906230136686445 11646809486589836301257417)
              ·
                refine ⟨8735107114942377225943063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11646809486589836301257417 8735107114942377225943063)
                ·
                  refine ⟨13102660672413565838914595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735107114942377225943063 13102660672413565838914595)
                  ·
                    refine ⟨19653991008620348758371893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13102660672413565838914595 19653991008620348758371893)
                    ·
                      refine ⟨1842561657058157696097365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19653991008620348758371893 1842561657058157696097365)
                      ·
                        rfl

theorem cell23_3588376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3588376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588376 prefixEnd_3588376 := by exact prefixLift 3588376
  have htrace : WordTrace (prefixWord ++ tailWord_3588376) baseStart_3588376 baseEnd_3588376 := by
    simpa [prefixWord, tailWord_3588376, baseEnd_3588376] using wordTrace_append hprefix tailTrace_3588376
  have hstable : (prefixWord ++ tailWord_3588376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588376).length < 2 ^ (prefixWord ++ tailWord_3588376).sum := by decide
  have hdescent : baseEnd_3588376 < baseStart_3588376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588383 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 1, 6]
def baseStart_3588383 : Nat := 118140960795 + 3588383 * 2 ^ 59
def prefixEnd_3588383 : Nat := 4983230072969 + 3 ^ 40 * 3588383 * 2
def baseEnd_3588383 : Nat := 614188417140913056236611

theorem tailTrace_3588383 : CollatzResearch.WordTrace tailWord_3588383 prefixEnd_3588383 614188417140913056236611 := by
  unfold tailWord_3588383
  simp only [CollatzResearch.WordTrace]
  refine ⟨130879080158908712870265803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87252720105939141913510535 130879080158908712870265803)
  ·
    refine ⟨196318620238363069305398705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130879080158908712870265803 196318620238363069305398705)
    ·
      refine ⟨147238965178772301979049029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196318620238363069305398705 147238965178772301979049029)
      ·
        refine ⟨27607305971019806621071693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147238965178772301979049029 27607305971019806621071693)
        ·
          refine ⟨10352739739132427482901885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27607305971019806621071693 10352739739132427482901885)
          ·
            refine ⟨3882277402174660306088207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10352739739132427482901885 3882277402174660306088207)
            ·
              refine ⟨5823416103261990459132311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882277402174660306088207 5823416103261990459132311)
              ·
                refine ⟨8735124154892985688698467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823416103261990459132311 8735124154892985688698467)
                ·
                  refine ⟨13102686232339478533047701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735124154892985688698467 13102686232339478533047701)
                  ·
                    refine ⟨614188417140913056236611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13102686232339478533047701 614188417140913056236611)
                    ·
                      rfl

theorem cell23_3588383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_3588383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588383 prefixEnd_3588383 := by exact prefixLift 3588383
  have htrace : WordTrace (prefixWord ++ tailWord_3588383) baseStart_3588383 baseEnd_3588383 := by
    simpa [prefixWord, tailWord_3588383, baseEnd_3588383] using wordTrace_append hprefix tailTrace_3588383
  have hstable : (prefixWord ++ tailWord_3588383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588383).length < 2 ^ (prefixWord ++ tailWord_3588383).sum := by decide
  have hdescent : baseEnd_3588383 < baseStart_3588383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588396 : List Nat := [2, 2, 1, 1, 1, 3, 6, 7]
def baseStart_3588396 : Nat := 118140960795 + 3588396 * 2 ^ 59
def prefixEnd_3588396 : Nat := 4983230072969 + 3 ^ 40 * 3588396 * 2
def baseEnd_3588396 : Nat := 68243404691527689549899

theorem tailTrace_3588396 : CollatzResearch.WordTrace tailWord_3588396 prefixEnd_3588396 68243404691527689549899 := by
  unfold tailWord_3588396
  simp only [CollatzResearch.WordTrace]
  refine ⟨65439777153930808045244521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87253036205241077393659361 65439777153930808045244521)
  ·
    refine ⟨49079832865448106033933391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65439777153930808045244521 49079832865448106033933391)
    ·
      refine ⟨73619749298172159050900087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49079832865448106033933391 73619749298172159050900087)
      ·
        refine ⟨110429623947258238576350131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73619749298172159050900087 110429623947258238576350131)
        ·
          refine ⟨165644435920887357864525197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110429623947258238576350131 165644435920887357864525197)
          ·
            refine ⟨62116663470332759199196949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165644435920887357864525197 62116663470332759199196949)
            ·
              refine ⟨2911718600171848087462357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62116663470332759199196949 2911718600171848087462357)
              ·
                refine ⟨68243404691527689549899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2911718600171848087462357 68243404691527689549899)
                ·
                  rfl

theorem cell23_3588396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 7].length) (baseStart_3588396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588396 prefixEnd_3588396 := by exact prefixLift 3588396
  have htrace : WordTrace (prefixWord ++ tailWord_3588396) baseStart_3588396 baseEnd_3588396 := by
    simpa [prefixWord, tailWord_3588396, baseEnd_3588396] using wordTrace_append hprefix tailTrace_3588396
  have hstable : (prefixWord ++ tailWord_3588396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588396).length < 2 ^ (prefixWord ++ tailWord_3588396).sum := by decide
  have hdescent : baseEnd_3588396 < baseStart_3588396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588423 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_3588423 : Nat := 118140960795 + 3588423 * 2 ^ 59
def prefixEnd_3588423 : Nat := 4983230072969 + 3 ^ 40 * 3588423 * 2
def baseEnd_3588423 : Nat := 1842585790648919012209649

theorem tailTrace_3588423 : CollatzResearch.WordTrace tailWord_3588423 prefixEnd_3588423 1842585790648919012209649 := by
  unfold tailWord_3588423
  simp only [CollatzResearch.WordTrace]
  refine ⟨130880539078763799701721923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87253692719175866467814615 130880539078763799701721923)
  ·
    refine ⟨196320808618145699552582885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130880539078763799701721923 196320808618145699552582885)
    ·
      refine ⟨36810151615902318666109291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196320808618145699552582885 36810151615902318666109291)
      ·
        refine ⟨55215227423853477999163937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36810151615902318666109291 55215227423853477999163937)
        ·
          refine ⟨41411420567890108499372953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55215227423853477999163937 41411420567890108499372953)
          ·
            refine ⟨31058565425917581374529715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41411420567890108499372953 31058565425917581374529715)
            ·
              refine ⟨46587848138876372061794573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31058565425917581374529715 46587848138876372061794573)
              ·
                refine ⟨17470443052078639523172965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46587848138876372061794573 17470443052078639523172965)
                ·
                  refine ⟨3275708072264744910594931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17470443052078639523172965 3275708072264744910594931)
                  ·
                    refine ⟨4913562108397117365892397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3275708072264744910594931 4913562108397117365892397)
                    ·
                      refine ⟨1842585790648919012209649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4913562108397117365892397 1842585790648919012209649)
                      ·
                        rfl

theorem cell23_3588423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_3588423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588423 prefixEnd_3588423 := by exact prefixLift 3588423
  have htrace : WordTrace (prefixWord ++ tailWord_3588423) baseStart_3588423 baseEnd_3588423 := by
    simpa [prefixWord, tailWord_3588423, baseEnd_3588423] using wordTrace_append hprefix tailTrace_3588423
  have hstable : (prefixWord ++ tailWord_3588423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588423).length < 2 ^ (prefixWord ++ tailWord_3588423).sum := by decide
  have hdescent : baseEnd_3588423 < baseStart_3588423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588444 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3588444 : Nat := 118140960795 + 3588444 * 2 ^ 59
def prefixEnd_3588444 : Nat := 4983230072969 + 3 ^ 40 * 3588444 * 2
def baseEnd_3588444 : Nat := 1842596573742663430047053

theorem tailTrace_3588444 : CollatzResearch.WordTrace tailWord_3588444 prefixEnd_3588444 1842596573742663430047053 := by
  unfold tailWord_3588444
  simp only [CollatzResearch.WordTrace]
  refine ⟨65440652505843860144118193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87254203341125146858824257 65440652505843860144118193)
  ·
    refine ⟨49080489379382895108088645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65440652505843860144118193 49080489379382895108088645)
    ·
      refine ⟨9202591758634292832766621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49080489379382895108088645 9202591758634292832766621)
      ·
        refine ⟨3450971909487859812287483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9202591758634292832766621 3450971909487859812287483)
        ·
          refine ⟨5176457864231789718431225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450971909487859812287483 5176457864231789718431225)
          ·
            refine ⟨3882343398173842288823419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5176457864231789718431225 3882343398173842288823419)
            ·
              refine ⟨5823515097260763433235129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882343398173842288823419 5823515097260763433235129)
              ·
                refine ⟨4367636322945572574926347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5823515097260763433235129 4367636322945572574926347)
                ·
                  refine ⟨6551454484418358862389521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367636322945572574926347 6551454484418358862389521)
                  ·
                    refine ⟨4913590863313769146792141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6551454484418358862389521 4913590863313769146792141)
                    ·
                      refine ⟨1842596573742663430047053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4913590863313769146792141 1842596573742663430047053)
                      ·
                        rfl

theorem cell23_3588444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3588444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588444 prefixEnd_3588444 := by exact prefixLift 3588444
  have htrace : WordTrace (prefixWord ++ tailWord_3588444) baseStart_3588444 baseEnd_3588444 := by
    simpa [prefixWord, tailWord_3588444, baseEnd_3588444] using wordTrace_append hprefix tailTrace_3588444
  have hstable : (prefixWord ++ tailWord_3588444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588444).length < 2 ^ (prefixWord ++ tailWord_3588444).sum := by decide
  have hdescent : baseEnd_3588444 < baseStart_3588444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588490 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_3588490 : Nat := 118140960795 + 3588490 * 2 ^ 59
def prefixEnd_3588490 : Nat := 4983230072969 + 3 ^ 40 * 3588490 * 2
def baseEnd_3588490 : Nat := 614206731284256750023947

theorem tailTrace_3588490 : CollatzResearch.WordTrace tailWord_3588490 prefixEnd_3588490 614206731284256750023947 := by
  unfold tailWord_3588490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32720745692380267536102731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87255321846347380096273949 32720745692380267536102731)
  ·
    refine ⟨49081118538570401304154097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32720745692380267536102731 49081118538570401304154097)
    ·
      refine ⟨36810838903927800978115573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49081118538570401304154097 36810838903927800978115573)
      ·
        refine ⟨3451016147243231341698335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36810838903927800978115573 3451016147243231341698335)
        ·
          refine ⟨5176524220864847012547503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451016147243231341698335 5176524220864847012547503)
          ·
            refine ⟨7764786331297270518821255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176524220864847012547503 7764786331297270518821255)
            ·
              refine ⟨11647179496945905778231883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764786331297270518821255 11647179496945905778231883)
              ·
                refine ⟨17470769245418858667347825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11647179496945905778231883 17470769245418858667347825)
                ·
                  refine ⟨13103076934064144000510869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17470769245418858667347825 13103076934064144000510869)
                  ·
                    refine ⟨614206731284256750023947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13103076934064144000510869 614206731284256750023947)
                    ·
                      rfl

theorem cell23_3588490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_3588490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588490 prefixEnd_3588490 := by exact prefixLift 3588490
  have htrace : WordTrace (prefixWord ++ tailWord_3588490) baseStart_3588490 baseEnd_3588490 := by
    simpa [prefixWord, tailWord_3588490, baseEnd_3588490] using wordTrace_append hprefix tailTrace_3588490
  have hstable : (prefixWord ++ tailWord_3588490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588490).length < 2 ^ (prefixWord ++ tailWord_3588490).sum := by decide
  have hdescent : baseEnd_3588490 < baseStart_3588490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588576 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 10]
def baseStart_3588576 : Nat := 118140960795 + 3588576 * 2 ^ 59
def prefixEnd_3588576 : Nat := 4983230072969 + 3 ^ 40 * 3588576 * 2
def baseEnd_3588576 : Nat := 204740483687672990399605

theorem tailTrace_3588576 : CollatzResearch.WordTrace tailWord_3588576 prefixEnd_3588576 204740483687672990399605 := by
  unfold tailWord_3588576
  simp only [CollatzResearch.WordTrace]
  refine ⟨65443059723604753416020791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87257412964806337888027721 65443059723604753416020791)
  ·
    refine ⟨98164589585407130124031187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65443059723604753416020791 98164589585407130124031187)
    ·
      refine ⟨147246884378110695186046781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98164589585407130124031187 147246884378110695186046781)
      ·
        refine ⟨55217581641791510694767543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147246884378110695186046781 55217581641791510694767543)
        ·
          refine ⟨82826372462687266042151315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55217581641791510694767543 82826372462687266042151315)
          ·
            refine ⟨124239558694030899063226973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82826372462687266042151315 124239558694030899063226973)
            ·
              refine ⟨46589834510261587148710115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124239558694030899063226973 46589834510261587148710115)
              ·
                refine ⟨69884751765392380723065173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46589834510261587148710115 69884751765392380723065173)
                ·
                  refine ⟨204740483687672990399605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 69884751765392380723065173 204740483687672990399605)
                  ·
                    rfl

theorem cell23_3588576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_3588576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588576 prefixEnd_3588576 := by exact prefixLift 3588576
  have htrace : WordTrace (prefixWord ++ tailWord_3588576) baseStart_3588576 baseEnd_3588576 := by
    simpa [prefixWord, tailWord_3588576, baseEnd_3588576] using wordTrace_append hprefix tailTrace_3588576
  have hstable : (prefixWord ++ tailWord_3588576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588576).length < 2 ^ (prefixWord ++ tailWord_3588576).sum := by decide
  have hdescent : baseEnd_3588576 < baseStart_3588576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588590 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_3588590 : Nat := 118140960795 + 3588590 * 2 ^ 59
def prefixEnd_3588590 : Nat := 4983230072969 + 3 ^ 40 * 3588590 * 2
def baseEnd_3588590 : Nat := 1842671541918219858821381

theorem tailTrace_3588590 : CollatzResearch.WordTrace tailWord_3588590 prefixEnd_3588590 1842671541918219858821381 := by
  unfold tailWord_3588590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16360828758644848402881403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87257753379439191482034149 16360828758644848402881403)
  ·
    refine ⟨24541243137967272604322105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16360828758644848402881403 24541243137967272604322105)
    ·
      refine ⟨18405932353475454453241579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24541243137967272604322105 18405932353475454453241579)
      ·
        refine ⟨27608898530213181679862369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18405932353475454453241579 27608898530213181679862369)
        ·
          refine ⟨20706673897659886259896777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27608898530213181679862369 20706673897659886259896777)
          ·
            refine ⟨15530005423244914694922583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20706673897659886259896777 15530005423244914694922583)
            ·
              refine ⟨23295008134867372042383875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15530005423244914694922583 23295008134867372042383875)
              ·
                refine ⟨34942512202301058063575813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23295008134867372042383875 34942512202301058063575813)
                ·
                  refine ⟨6551721037931448386920465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34942512202301058063575813 6551721037931448386920465)
                  ·
                    refine ⟨4913790778448586290190349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6551721037931448386920465 4913790778448586290190349)
                    ·
                      refine ⟨1842671541918219858821381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4913790778448586290190349 1842671541918219858821381)
                      ·
                        rfl

theorem cell23_3588590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_3588590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588590 prefixEnd_3588590 := by exact prefixLift 3588590
  have htrace : WordTrace (prefixWord ++ tailWord_3588590) baseStart_3588590 baseEnd_3588590 := by
    simpa [prefixWord, tailWord_3588590, baseEnd_3588590] using wordTrace_append hprefix tailTrace_3588590
  have hstable : (prefixWord ++ tailWord_3588590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588590).length < 2 ^ (prefixWord ++ tailWord_3588590).sum := by decide
  have hdescent : baseEnd_3588590 < baseStart_3588590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588593 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 6]
def baseStart_3588593 : Nat := 118140960795 + 3588593 * 2 ^ 59
def prefixEnd_3588593 : Nat := 4983230072969 + 3 ^ 40 * 3588593 * 2
def baseEnd_3588593 : Nat := 204741453595575927453763

theorem tailTrace_3588593 : CollatzResearch.WordTrace tailWord_3588593 prefixEnd_3588593 204741453595575927453763 := by
  unfold tailWord_3588593
  simp only [CollatzResearch.WordTrace]
  refine ⟨130886739488147918735410433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87257826325431945823606955 130886739488147918735410433)
  ·
    refine ⟨98165054616110939051557825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130886739488147918735410433 98165054616110939051557825)
    ·
      refine ⟨73623790962083204288668369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98165054616110939051557825 73623790962083204288668369)
      ·
        refine ⟨55217843221562403216501277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73623790962083204288668369 55217843221562403216501277)
        ·
          refine ⟨20706691208085901206187979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55217843221562403216501277 20706691208085901206187979)
          ·
            refine ⟨31060036812128851809281969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20706691208085901206187979 31060036812128851809281969)
            ·
              refine ⟨23295027609096638856961477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31060036812128851809281969 23295027609096638856961477)
              ·
                refine ⟨4367817676705619785680277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23295027609096638856961477 4367817676705619785680277)
                ·
                  refine ⟨204741453595575927453763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4367817676705619785680277 204741453595575927453763)
                  ·
                    rfl

theorem cell23_3588593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 6].length) (baseStart_3588593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588593 prefixEnd_3588593 := by exact prefixLift 3588593
  have htrace : WordTrace (prefixWord ++ tailWord_3588593) baseStart_3588593 baseEnd_3588593 := by
    simpa [prefixWord, tailWord_3588593, baseEnd_3588593] using wordTrace_append hprefix tailTrace_3588593
  have hstable : (prefixWord ++ tailWord_3588593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588593).length < 2 ^ (prefixWord ++ tailWord_3588593).sum := by decide
  have hdescent : baseEnd_3588593 < baseStart_3588593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588663 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_3588663 : Nat := 118140960795 + 3588663 * 2 ^ 59
def prefixEnd_3588663 : Nat := 4983230072969 + 3 ^ 40 * 3588663 * 2
def baseEnd_3588663 : Nat := 1842709026005998073208545

theorem tailTrace_3588663 : CollatzResearch.WordTrace tailWord_3588663 prefixEnd_3588663 1842709026005998073208545 := by
  unfold tailWord_3588663
  simp only [CollatzResearch.WordTrace]
  refine ⟨130889292597894320690458643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87259528398596213793639095 130889292597894320690458643)
  ·
    refine ⟨196333938896841481035687965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130889292597894320690458643 196333938896841481035687965)
    ·
      refine ⟨73625227086315555388382987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196333938896841481035687965 73625227086315555388382987)
      ·
        refine ⟨110437840629473333082574481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73625227086315555388382987 110437840629473333082574481)
        ·
          refine ⟨82828380472104999811930861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110437840629473333082574481 82828380472104999811930861)
          ·
            refine ⟨31060642677039374929474073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82828380472104999811930861 31060642677039374929474073)
            ·
              refine ⟨23295482007779531197105555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31060642677039374929474073 23295482007779531197105555)
              ·
                refine ⟨34943223011669296795658333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23295482007779531197105555 34943223011669296795658333)
                ·
                  refine ⟨13103708629375986298371875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34943223011669296795658333 13103708629375986298371875)
                  ·
                    refine ⟨19655562944063979447557813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13103708629375986298371875 19655562944063979447557813)
                    ·
                      refine ⟨1842709026005998073208545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19655562944063979447557813 1842709026005998073208545)
                      ·
                        rfl

theorem cell23_3588663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_3588663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588663 prefixEnd_3588663 := by exact prefixLift 3588663
  have htrace : WordTrace (prefixWord ++ tailWord_3588663) baseStart_3588663 baseEnd_3588663 := by
    simpa [prefixWord, tailWord_3588663, baseEnd_3588663] using wordTrace_append hprefix tailTrace_3588663
  have hstable : (prefixWord ++ tailWord_3588663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588663).length < 2 ^ (prefixWord ++ tailWord_3588663).sum := by decide
  have hdescent : baseEnd_3588663 < baseStart_3588663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588677 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 5, 2, 2]
def baseStart_3588677 : Nat := 118140960795 + 3588677 * 2 ^ 59
def prefixEnd_3588677 : Nat := 4983230072969 + 3 ^ 40 * 3588677 * 2
def baseEnd_3588677 : Nat := 1842716214735161018433481

theorem tailTrace_3588677 : CollatzResearch.WordTrace tailWord_3588677 prefixEnd_3588677 1842716214735161018433481 := by
  unfold tailWord_3588677
  simp only [CollatzResearch.WordTrace]
  refine ⟨130889803219843601081468285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87259868813229067387645523 130889803219843601081468285)
  ·
    refine ⟨49083676207441350405550607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130889803219843601081468285 49083676207441350405550607)
    ·
      refine ⟨73625514311162025608325911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49083676207441350405550607 73625514311162025608325911)
      ·
        refine ⟨110438271466743038412488867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73625514311162025608325911 110438271466743038412488867)
        ·
          refine ⟨165657407200114557618733301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110438271466743038412488867 165657407200114557618733301)
          ·
            refine ⟨15530381925010739776756247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165657407200114557618733301 15530381925010739776756247)
            ·
              refine ⟨23295572887516109665134371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15530381925010739776756247 23295572887516109665134371)
              ·
                refine ⟨34943359331274164497701557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23295572887516109665134371 34943359331274164497701557)
                ·
                  refine ⟨3275939937306952921659521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34943359331274164497701557 3275939937306952921659521)
                  ·
                    refine ⟨2456954952980214691244641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3275939937306952921659521 2456954952980214691244641)
                    ·
                      refine ⟨1842716214735161018433481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2456954952980214691244641 1842716214735161018433481)
                      ·
                        rfl

theorem cell23_3588677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_3588677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588677 prefixEnd_3588677 := by exact prefixLift 3588677
  have htrace : WordTrace (prefixWord ++ tailWord_3588677) baseStart_3588677 baseEnd_3588677 := by
    simpa [prefixWord, tailWord_3588677, baseEnd_3588677] using wordTrace_append hprefix tailTrace_3588677
  have hstable : (prefixWord ++ tailWord_3588677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588677).length < 2 ^ (prefixWord ++ tailWord_3588677).sum := by decide
  have hdescent : baseEnd_3588677 < baseStart_3588677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588690 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3588690 : Nat := 118140960795 + 3588690 * 2 ^ 59
def prefixEnd_3588690 : Nat := 4983230072969 + 3 ^ 40 * 3588690 * 2
def baseEnd_3588690 : Nat := 1842722889983669467570921

theorem tailTrace_3588690 : CollatzResearch.WordTrace tailWord_3588690 prefixEnd_3588690 1842722889983669467570921 := by
  unfold tailWord_3588690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32722569342199126075422881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87260184912531002867794349 32722569342199126075422881)
  ·
    refine ⟨24541927006649344556567161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32722569342199126075422881 24541927006649344556567161)
    ·
      refine ⟨18406445254987008417425371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24541927006649344556567161 18406445254987008417425371)
      ·
        refine ⟨27609667882480512626138057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18406445254987008417425371 27609667882480512626138057)
        ·
          refine ⟨20707250911860384469603543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27609667882480512626138057 20707250911860384469603543)
          ·
            refine ⟨31060876367790576704405315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20707250911860384469603543 31060876367790576704405315)
            ·
              refine ⟨46591314551685865056607973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31060876367790576704405315 46591314551685865056607973)
              ·
                refine ⟨8735871478441099698113995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46591314551685865056607973 8735871478441099698113995)
                ·
                  refine ⟨13103807217661649547170993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735871478441099698113995 13103807217661649547170993)
                  ·
                    refine ⟨9827855413246237160378245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13103807217661649547170993 9827855413246237160378245)
                    ·
                      refine ⟨1842722889983669467570921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9827855413246237160378245 1842722889983669467570921)
                      ·
                        rfl

theorem cell23_3588690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3588690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588690 prefixEnd_3588690 := by exact prefixLift 3588690
  have htrace : WordTrace (prefixWord ++ tailWord_3588690) baseStart_3588690 baseEnd_3588690 := by
    simpa [prefixWord, tailWord_3588690, baseEnd_3588690] using wordTrace_append hprefix tailTrace_3588690
  have hstable : (prefixWord ++ tailWord_3588690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588690).length < 2 ^ (prefixWord ++ tailWord_3588690).sum := by decide
  have hdescent : baseEnd_3588690 < baseStart_3588690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588700 : List Nat := [2, 2, 4, 1, 3, 1, 10]
def baseStart_3588700 : Nat := 118140960795 + 3588700 * 2 ^ 59
def prefixEnd_3588700 : Nat := 4983230072969 + 3 ^ 40 * 3588700 * 2
def baseEnd_3588700 : Nat := 22749728701113758375875

theorem tailTrace_3588700 : CollatzResearch.WordTrace tailWord_3588700 prefixEnd_3588700 22749728701113758375875 := by
  unfold tailWord_3588700
  simp only [CollatzResearch.WordTrace]
  refine ⟨65445321049380138004777777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87260428065840184006370369 65445321049380138004777777)
  ·
    refine ⟨49083990787035103503583333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65445321049380138004777777 49083990787035103503583333)
    ·
      refine ⟨9203248272569081906921875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49083990787035103503583333 9203248272569081906921875)
      ·
        refine ⟨13804872408853622860382813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9203248272569081906921875 13804872408853622860382813)
        ·
          refine ⟨5176827153320108572643555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13804872408853622860382813 5176827153320108572643555)
          ·
            refine ⟨7765240729980162858965333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176827153320108572643555 7765240729980162858965333)
            ·
              refine ⟨22749728701113758375875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7765240729980162858965333 22749728701113758375875)
              ·
                rfl

theorem cell23_3588700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 10].length) (baseStart_3588700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588700 prefixEnd_3588700 := by exact prefixLift 3588700
  have htrace : WordTrace (prefixWord ++ tailWord_3588700) baseStart_3588700 baseEnd_3588700 := by
    simpa [prefixWord, tailWord_3588700, baseEnd_3588700] using wordTrace_append hprefix tailTrace_3588700
  have hstable : (prefixWord ++ tailWord_3588700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588700).length < 2 ^ (prefixWord ++ tailWord_3588700).sum := by decide
  have hdescent : baseEnd_3588700 < baseStart_3588700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588727 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_3588727 : Nat := 118140960795 + 3588727 * 2 ^ 59
def prefixEnd_3588727 : Nat := 4983230072969 + 3 ^ 40 * 3588727 * 2
def baseEnd_3588727 : Nat := 1842741888767885822808251

theorem tailTrace_3588727 : CollatzResearch.WordTrace tailWord_3588727 prefixEnd_3588727 1842741888767885822808251 := by
  unfold tailWord_3588727
  simp only [CollatzResearch.WordTrace]
  refine ⟨130891626869662459620788435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87261084579774973080525623 130891626869662459620788435)
  ·
    refine ⟨196337440304493689431182653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130891626869662459620788435 196337440304493689431182653)
    ·
      refine ⟨73626540114185133536693495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196337440304493689431182653 73626540114185133536693495)
      ·
        refine ⟨110439810171277700305040243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73626540114185133536693495 110439810171277700305040243)
        ·
          refine ⟨165659715256916550457560365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110439810171277700305040243 165659715256916550457560365)
          ·
            refine ⟨62122393221343706421585137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165659715256916550457560365 62122393221343706421585137)
            ·
              refine ⟨46591794916007779816188853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62122393221343706421585137 46591794916007779816188853)
              ·
                refine ⟨4367980773375729357767705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46591794916007779816188853 4367980773375729357767705)
                ·
                  refine ⟨3275985580031797018325779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4367980773375729357767705 3275985580031797018325779)
                  ·
                    refine ⟨4913978370047695527488669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3275985580031797018325779 4913978370047695527488669)
                    ·
                      refine ⟨1842741888767885822808251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4913978370047695527488669 1842741888767885822808251)
                      ·
                        rfl

theorem cell23_3588727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_3588727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588727 prefixEnd_3588727 := by exact prefixLift 3588727
  have htrace : WordTrace (prefixWord ++ tailWord_3588727) baseStart_3588727 baseEnd_3588727 := by
    simpa [prefixWord, tailWord_3588727, baseEnd_3588727] using wordTrace_append hprefix tailTrace_3588727
  have hstable : (prefixWord ++ tailWord_3588727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588727).length < 2 ^ (prefixWord ++ tailWord_3588727).sum := by decide
  have hdescent : baseEnd_3588727 < baseStart_3588727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588740 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3588740 : Nat := 118140960795 + 3588740 * 2 ^ 59
def prefixEnd_3588740 : Nat := 4983230072969 + 3 ^ 40 * 3588740 * 2
def baseEnd_3588740 : Nat := 1842748564016394271945691

theorem tailTrace_3588740 : CollatzResearch.WordTrace tailWord_3588740 prefixEnd_3588740 1842748564016394271945691 := by
  unfold tailWord_3588740
  simp only [CollatzResearch.WordTrace]
  refine ⟨65446050509307681420505837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87261400679076908560674449 65446050509307681420505837)
  ·
    refine ⟨24542268940990380532689689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65446050509307681420505837 24542268940990380532689689)
    ·
      refine ⟨18406701705742785399517267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24542268940990380532689689 18406701705742785399517267)
      ·
        refine ⟨27610052558614178099275901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18406701705742785399517267 27610052558614178099275901)
        ·
          refine ⟨10353769709480316787228463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27610052558614178099275901 10353769709480316787228463)
          ·
            refine ⟨15530654564220475180842695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10353769709480316787228463 15530654564220475180842695)
            ·
              refine ⟨23295981846330712771264043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15530654564220475180842695 23295981846330712771264043)
              ·
                refine ⟨34943972769496069156896065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23295981846330712771264043 34943972769496069156896065)
                ·
                  refine ⟨26207979577122051867672049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34943972769496069156896065 26207979577122051867672049)
                  ·
                    refine ⟨19655984682841538900754037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26207979577122051867672049 19655984682841538900754037)
                    ·
                      refine ⟨1842748564016394271945691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19655984682841538900754037 1842748564016394271945691)
                      ·
                        rfl

theorem cell23_3588740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3588740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588740 prefixEnd_3588740 := by exact prefixLift 3588740
  have htrace : WordTrace (prefixWord ++ tailWord_3588740) baseStart_3588740 baseEnd_3588740 := by
    simpa [prefixWord, tailWord_3588740, baseEnd_3588740] using wordTrace_append hprefix tailTrace_3588740
  have hstable : (prefixWord ++ tailWord_3588740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588740).length < 2 ^ (prefixWord ++ tailWord_3588740).sum := by decide
  have hdescent : baseEnd_3588740 < baseStart_3588740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588778 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3588778 : Nat := 118140960795 + 3588778 * 2 ^ 59
def prefixEnd_3588778 : Nat := 4983230072969 + 3 ^ 40 * 3588778 * 2
def baseEnd_3588778 : Nat := 1842768076281265123270517

theorem tailTrace_3588778 : CollatzResearch.WordTrace tailWord_3588778 prefixEnd_3588778 1842768076281265123270517 := by
  unfold tailWord_3588778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32723371748119423832723747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87262324661651796887263325 32723371748119423832723747)
  ·
    refine ⟨49085057622179135749085621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32723371748119423832723747 49085057622179135749085621)
    ·
      refine ⟨4601724152079293976476777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49085057622179135749085621 4601724152079293976476777)
      ·
        refine ⟨3451293114059470482357583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4601724152079293976476777 3451293114059470482357583)
        ·
          refine ⟨5176939671089205723536375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451293114059470482357583 5176939671089205723536375)
          ·
            refine ⟨7765409506633808585304563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176939671089205723536375 7765409506633808585304563)
            ·
              refine ⟨11648114259950712877956845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7765409506633808585304563 11648114259950712877956845)
              ·
                refine ⟨4368042847481517329233817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11648114259950712877956845 4368042847481517329233817)
                ·
                  refine ⟨3276032135611137996925363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4368042847481517329233817 3276032135611137996925363)
                  ·
                    refine ⟨4914048203416706995388045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276032135611137996925363 4914048203416706995388045)
                    ·
                      refine ⟨1842768076281265123270517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4914048203416706995388045 1842768076281265123270517)
                      ·
                        rfl

theorem cell23_3588778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3588778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588778 prefixEnd_3588778 := by exact prefixLift 3588778
  have htrace : WordTrace (prefixWord ++ tailWord_3588778) baseStart_3588778 baseEnd_3588778 := by
    simpa [prefixWord, tailWord_3588778, baseEnd_3588778] using wordTrace_append hprefix tailTrace_3588778
  have hstable : (prefixWord ++ tailWord_3588778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588778).length < 2 ^ (prefixWord ++ tailWord_3588778).sum := by decide
  have hdescent : baseEnd_3588778 < baseStart_3588778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588818 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_3588818 : Nat := 118140960795 + 3588818 * 2 ^ 59
def prefixEnd_3588818 : Nat := 4983230072969 + 3 ^ 40 * 3588818 * 2
def baseEnd_3588818 : Nat := 1842788615507444966770333

theorem tailTrace_3588818 : CollatzResearch.WordTrace tailWord_3588818 prefixEnd_3588818 1842788615507444966770333 := by
  unfold tailWord_3588818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32723736478083195540587777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87263297274888521441567405 32723736478083195540587777)
  ·
    refine ⟨24542802358562396655440833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32723736478083195540587777 24542802358562396655440833)
    ·
      refine ⟨18407101768921797491580625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24542802358562396655440833 18407101768921797491580625)
      ·
        refine ⟨13805326326691348118685469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18407101768921797491580625 13805326326691348118685469)
        ·
          refine ⟨5176997372509255544507051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13805326326691348118685469 5176997372509255544507051)
          ·
            refine ⟨7765496058763883316760577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176997372509255544507051 7765496058763883316760577)
            ·
              refine ⟨5824122044072912487570433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7765496058763883316760577 5824122044072912487570433)
              ·
                refine ⟨4368091533054684365677825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5824122044072912487570433 4368091533054684365677825)
                ·
                  refine ⟨3276068649791013274258369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4368091533054684365677825 3276068649791013274258369)
                  ·
                    refine ⟨2457051487343259955693777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3276068649791013274258369 2457051487343259955693777)
                    ·
                      refine ⟨1842788615507444966770333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457051487343259955693777 1842788615507444966770333)
                      ·
                        rfl

theorem cell23_3588818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_3588818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588818 prefixEnd_3588818 := by exact prefixLift 3588818
  have htrace : WordTrace (prefixWord ++ tailWord_3588818) baseStart_3588818 baseEnd_3588818 := by
    simpa [prefixWord, tailWord_3588818, baseEnd_3588818] using wordTrace_append hprefix tailTrace_3588818
  have hstable : (prefixWord ++ tailWord_3588818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588818).length < 2 ^ (prefixWord ++ tailWord_3588818).sum := by decide
  have hdescent : baseEnd_3588818 < baseStart_3588818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588824 : List Nat := [2, 1, 2, 2, 3, 2, 4, 2, 5]
def baseStart_3588824 : Nat := 118140960795 + 3588824 * 2 ^ 59
def prefixEnd_3588824 : Nat := 4983230072969 + 3 ^ 40 * 3588824 * 2
def baseEnd_3588824 : Nat := 204754632932374660366145

theorem tailTrace_3588824 : CollatzResearch.WordTrace tailWord_3588824 prefixEnd_3588824 204754632932374660366145 := by
  unfold tailWord_3588824
  simp only [CollatzResearch.WordTrace]
  refine ⟨65447582375155522593534763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87263443166874030124713017 65447582375155522593534763)
  ·
    refine ⟨98171373562733283890302145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65447582375155522593534763 98171373562733283890302145)
    ·
      refine ⟨73628530172049962917726609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98171373562733283890302145 73628530172049962917726609)
      ·
        refine ⟨55221397629037472188294957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73628530172049962917726609 55221397629037472188294957)
        ·
          refine ⟨20708024110889052070610609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55221397629037472188294957 20708024110889052070610609)
          ·
            refine ⟨15531018083166789052957957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20708024110889052070610609 15531018083166789052957957)
            ·
              refine ⟨2912065890593772947429617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15531018083166789052957957 2912065890593772947429617)
              ·
                refine ⟨2184049417945329710572213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912065890593772947429617 2184049417945329710572213)
                ·
                  refine ⟨204754632932374660366145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2184049417945329710572213 204754632932374660366145)
                  ·
                    rfl

theorem cell23_3588824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 5].length) (baseStart_3588824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588824 prefixEnd_3588824 := by exact prefixLift 3588824
  have htrace : WordTrace (prefixWord ++ tailWord_3588824) baseStart_3588824 baseEnd_3588824 := by
    simpa [prefixWord, tailWord_3588824, baseEnd_3588824] using wordTrace_append hprefix tailTrace_3588824
  have hstable : (prefixWord ++ tailWord_3588824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588824).length < 2 ^ (prefixWord ++ tailWord_3588824).sum := by decide
  have hdescent : baseEnd_3588824 < baseStart_3588824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588948 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 6]
def baseStart_3588948 : Nat := 118140960795 + 3588948 * 2 ^ 59
def prefixEnd_3588948 : Nat := 4983230072969 + 3 ^ 40 * 3588948 * 2
def baseEnd_3588948 : Nat := 204761707554725495349415

theorem tailTrace_3588948 : CollatzResearch.WordTrace tailWord_3588948 prefixEnd_3588948 204761707554725495349415 := by
  unfold tailWord_3588948
  simp only [CollatzResearch.WordTrace]
  refine ⟨65449843700930907182291749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87266458267907876243055665 65449843700930907182291749)
  ·
    refine ⟨12271845693924545096679703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65449843700930907182291749 12271845693924545096679703)
    ·
      refine ⟨18407768540886817645019555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12271845693924545096679703 18407768540886817645019555)
      ·
        refine ⟨27611652811330226467529333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18407768540886817645019555 27611652811330226467529333)
        ·
          refine ⟨2588592451062208731330875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27611652811330226467529333 2588592451062208731330875)
          ·
            refine ⟨3882888676593313096996313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588592451062208731330875 3882888676593313096996313)
            ·
              refine ⟨2912166507444984822747235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3882888676593313096996313 2912166507444984822747235)
              ·
                refine ⟨4368249761167477234120853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912166507444984822747235 4368249761167477234120853)
                ·
                  refine ⟨204761707554725495349415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4368249761167477234120853 204761707554725495349415)
                  ·
                    rfl

theorem cell23_3588948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_3588948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588948 prefixEnd_3588948 := by exact prefixLift 3588948
  have htrace : WordTrace (prefixWord ++ tailWord_3588948) baseStart_3588948 baseEnd_3588948 := by
    simpa [prefixWord, tailWord_3588948, baseEnd_3588948] using wordTrace_append hprefix tailTrace_3588948
  have hstable : (prefixWord ++ tailWord_3588948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588948).length < 2 ^ (prefixWord ++ tailWord_3588948).sum := by decide
  have hdescent : baseEnd_3588948 < baseStart_3588948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588964 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_3588964 : Nat := 118140960795 + 3588964 * 2 ^ 59
def prefixEnd_3588964 : Nat := 4983230072969 + 3 ^ 40 * 3588964 * 2
def baseEnd_3588964 : Nat := 1842863583683001395544661

theorem tailTrace_3588964 : CollatzResearch.WordTrace tailWord_3588964 prefixEnd_3588964 1842863583683001395544661 := by
  unfold tailWord_3588964
  simp only [CollatzResearch.WordTrace]
  refine ⟨65450135484901924548582973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87266847313202566064777297 65450135484901924548582973)
  ·
    refine ⟨24543800806838221705718615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65450135484901924548582973 24543800806838221705718615)
    ·
      refine ⟨36815701210257332558577923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24543800806838221705718615 36815701210257332558577923)
      ·
        refine ⟨55223551815385998837866885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36815701210257332558577923 55223551815385998837866885)
        ·
          refine ⟨10354415965384874782100041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55223551815385998837866885 10354415965384874782100041)
          ·
            refine ⟨7765811974038656086575031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10354415965384874782100041 7765811974038656086575031)
            ·
              refine ⟨11648717961057984129862547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7765811974038656086575031 11648717961057984129862547)
              ·
                refine ⟨17473076941586976194793821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11648717961057984129862547 17473076941586976194793821)
                ·
                  refine ⟨6552403853095116073047683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17473076941586976194793821 6552403853095116073047683)
                  ·
                    refine ⟨9828605779642674109571525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552403853095116073047683 9828605779642674109571525)
                    ·
                      refine ⟨1842863583683001395544661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9828605779642674109571525 1842863583683001395544661)
                      ·
                        rfl

theorem cell23_3588964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_3588964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588964 prefixEnd_3588964 := by exact prefixLift 3588964
  have htrace : WordTrace (prefixWord ++ tailWord_3588964) baseStart_3588964 baseEnd_3588964 := by
    simpa [prefixWord, tailWord_3588964, baseEnd_3588964] using wordTrace_append hprefix tailTrace_3588964
  have hstable : (prefixWord ++ tailWord_3588964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588964).length < 2 ^ (prefixWord ++ tailWord_3588964).sum := by decide
  have hdescent : baseEnd_3588964 < baseStart_3588964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588977 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3588977 : Nat := 118140960795 + 3588977 * 2 ^ 59
def prefixEnd_3588977 : Nat := 4983230072969 + 3 ^ 40 * 3588977 * 2
def baseEnd_3588977 : Nat := 1842870258931509844682101

theorem tailTrace_3588977 : CollatzResearch.WordTrace tailWord_3588977 prefixEnd_3588977 1842870258931509844682101 := by
  unfold tailWord_3588977
  simp only [CollatzResearch.WordTrace]
  refine ⟨130900745118756752317389185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87267163412504501544926123 130900745118756752317389185)
  ·
    refine ⟨98175558839067564238041889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130900745118756752317389185 98175558839067564238041889)
    ·
      refine ⟨73631669129300673178531417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98175558839067564238041889 73631669129300673178531417)
      ·
        refine ⟨55223751846975504883898563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73631669129300673178531417 55223751846975504883898563)
        ·
          refine ⟨82835627770463257325847845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55223751846975504883898563 82835627770463257325847845)
          ·
            refine ⟨15531680206961860748596471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82835627770463257325847845 15531680206961860748596471)
            ·
              refine ⟨23297520310442791122894707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15531680206961860748596471 23297520310442791122894707)
              ·
                refine ⟨34946280465664186684342061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23297520310442791122894707 34946280465664186684342061)
                ·
                  refine ⟨13104855174624070006628273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34946280465664186684342061 13104855174624070006628273)
                  ·
                    refine ⟨9828641380968052504971205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13104855174624070006628273 9828641380968052504971205)
                    ·
                      refine ⟨1842870258931509844682101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9828641380968052504971205 1842870258931509844682101)
                      ·
                        rfl

theorem cell23_3588977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3588977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3588977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3588977 prefixEnd_3588977 := by exact prefixLift 3588977
  have htrace : WordTrace (prefixWord ++ tailWord_3588977) baseStart_3588977 baseEnd_3588977 := by
    simpa [prefixWord, tailWord_3588977, baseEnd_3588977] using wordTrace_append hprefix tailTrace_3588977
  have hstable : (prefixWord ++ tailWord_3588977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588977).length < 2 ^ (prefixWord ++ tailWord_3588977).sum := by decide
  have hdescent : baseEnd_3588977 < baseStart_3588977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589047 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 2, 6]
def baseStart_3589047 : Nat := 118140960795 + 3589047 * 2 ^ 59
def prefixEnd_3589047 : Nat := 4983230072969 + 3 ^ 40 * 3589047 * 2
def baseEnd_3589047 : Nat := 614302067525774856935593

theorem tailTrace_3589047 : CollatzResearch.WordTrace tailWord_3589047 prefixEnd_3589047 614302067525774856935593 := by
  unfold tailWord_3589047
  simp only [CollatzResearch.WordTrace]
  refine ⟨130903298228503154272437395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87268865485668769514958263 130903298228503154272437395)
  ·
    refine ⟨196354947342754731408656093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130903298228503154272437395 196354947342754731408656093)
    ·
      refine ⟨73633105253533024278246035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196354947342754731408656093 73633105253533024278246035)
      ·
        refine ⟨110449657880299536417369053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73633105253533024278246035 110449657880299536417369053)
        ·
          refine ⟨41418621705112326156513395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110449657880299536417369053 41418621705112326156513395)
          ·
            refine ⟨62127932557668489234770093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41418621705112326156513395 62127932557668489234770093)
            ·
              refine ⟨23297974709125683463038785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62127932557668489234770093 23297974709125683463038785)
              ·
                refine ⟨17473481031844262597279089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23297974709125683463038785 17473481031844262597279089)
                ·
                  refine ⟨13105110773883196947959317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17473481031844262597279089 13105110773883196947959317)
                  ·
                    refine ⟨614302067525774856935593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13105110773883196947959317 614302067525774856935593)
                    ·
                      rfl

theorem cell23_3589047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_3589047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589047 prefixEnd_3589047 := by exact prefixLift 3589047
  have htrace : WordTrace (prefixWord ++ tailWord_3589047) baseStart_3589047 baseEnd_3589047 := by
    simpa [prefixWord, tailWord_3589047, baseEnd_3589047] using wordTrace_append hprefix tailTrace_3589047
  have hstable : (prefixWord ++ tailWord_3589047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589047).length < 2 ^ (prefixWord ++ tailWord_3589047).sum := by decide
  have hdescent : baseEnd_3589047 < baseStart_3589047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589048 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_3589048 : Nat := 118140960795 + 3589048 * 2 ^ 59
def prefixEnd_3589048 : Nat := 4983230072969 + 3 ^ 40 * 3589048 * 2
def baseEnd_3589048 : Nat := 1842906716057979066894275

theorem tailTrace_3589048 : CollatzResearch.WordTrace tailWord_3589048 prefixEnd_3589048 1842906716057979066894275 := by
  unfold tailWord_3589048
  simp only [CollatzResearch.WordTrace]
  refine ⟨65451667350749765721611899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87268889800999687628815865 65451667350749765721611899)
  ·
    refine ⟨98177501026124648582417849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65451667350749765721611899 98177501026124648582417849)
    ·
      refine ⟨73633125769593486436813387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98177501026124648582417849 73633125769593486436813387)
      ·
        refine ⟨110449688654390229655220081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73633125769593486436813387 110449688654390229655220081)
        ·
          refine ⟨82837266490792672241415061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110449688654390229655220081 82837266490792672241415061)
          ·
            refine ⟨3882996866755906511316331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82837266490792672241415061 3882996866755906511316331)
            ·
              refine ⟨5824495300133859766974497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882996866755906511316331 5824495300133859766974497)
              ·
                refine ⟨4368371475100394825230873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5824495300133859766974497 4368371475100394825230873)
                ·
                  refine ⟨3276278606325296118923155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4368371475100394825230873 3276278606325296118923155)
                  ·
                    refine ⟨4914417909487944178384733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276278606325296118923155 4914417909487944178384733)
                    ·
                      refine ⟨1842906716057979066894275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4914417909487944178384733 1842906716057979066894275)
                      ·
                        rfl

theorem cell23_3589048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_3589048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589048 prefixEnd_3589048 := by exact prefixLift 3589048
  have htrace : WordTrace (prefixWord ++ tailWord_3589048) baseStart_3589048 baseEnd_3589048 := by
    simpa [prefixWord, tailWord_3589048, baseEnd_3589048] using wordTrace_append hprefix tailTrace_3589048
  have hstable : (prefixWord ++ tailWord_3589048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589048).length < 2 ^ (prefixWord ++ tailWord_3589048).sum := by decide
  have hdescent : baseEnd_3589048 < baseStart_3589048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589071 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 1, 4, 2]
def baseStart_3589071 : Nat := 118140960795 + 3589071 * 2 ^ 59
def prefixEnd_3589071 : Nat := 4983230072969 + 3 ^ 40 * 3589071 * 2
def baseEnd_3589071 : Nat := 1842918526113032476906669

theorem tailTrace_3589071 : CollatzResearch.WordTrace tailWord_3589071 prefixEnd_3589071 1842918526113032476906669 := by
  unfold tailWord_3589071
  simp only [CollatzResearch.WordTrace]
  refine ⟨130904173580416206371311067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87269449053610804247540711 130904173580416206371311067)
  ·
    refine ⟨196356260370624309556966601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130904173580416206371311067 196356260370624309556966601)
    ·
      refine ⟨147267195277968232167724951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196356260370624309556966601 147267195277968232167724951)
      ·
        refine ⟨220900792916952348251587427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147267195277968232167724951 220900792916952348251587427)
        ·
          refine ⟨331351189375428522377381141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220900792916952348251587427 331351189375428522377381141)
          ·
            refine ⟨15532087001973211986439741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 331351189375428522377381141 15532087001973211986439741)
            ·
              refine ⟨5824532625739954494914903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15532087001973211986439741 5824532625739954494914903)
              ·
                refine ⟨8736798938609931742372355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824532625739954494914903 8736798938609931742372355)
                ·
                  refine ⟨13105198407914897613558533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8736798938609931742372355 13105198407914897613558533)
                  ·
                    refine ⟨2457224701484043302542225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13105198407914897613558533 2457224701484043302542225)
                    ·
                      refine ⟨1842918526113032476906669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457224701484043302542225 1842918526113032476906669)
                      ·
                        rfl

theorem cell23_3589071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4, 2].length) (baseStart_3589071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589071 prefixEnd_3589071 := by exact prefixLift 3589071
  have htrace : WordTrace (prefixWord ++ tailWord_3589071) baseStart_3589071 baseEnd_3589071 := by
    simpa [prefixWord, tailWord_3589071, baseEnd_3589071] using wordTrace_append hprefix tailTrace_3589071
  have hstable : (prefixWord ++ tailWord_3589071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589071).length < 2 ^ (prefixWord ++ tailWord_3589071).sum := by decide
  have hdescent : baseEnd_3589071 < baseStart_3589071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589137 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 2, 8]
def baseStart_3589137 : Nat := 118140960795 + 3589137 * 2 ^ 59
def prefixEnd_3589137 : Nat := 4983230072969 + 3 ^ 40 * 3589137 * 2
def baseEnd_3589137 : Nat := 614317471945409739560455

theorem tailTrace_3589137 : CollatzResearch.WordTrace tailWord_3589137 prefixEnd_3589137 614317471945409739560455 := by
  unfold tailWord_3589137
  simp only [CollatzResearch.WordTrace]
  refine ⟨130906580798177099643213665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87271053865451399762142443 130906580798177099643213665)
  ·
    refine ⟨98179935598632824732410249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130906580798177099643213665 98179935598632824732410249)
    ·
      refine ⟨73634951698974618549307687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98179935598632824732410249 73634951698974618549307687)
      ·
        refine ⟨110452427548461927823961531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73634951698974618549307687 110452427548461927823961531)
        ·
          refine ⟨165678641322692891735942297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110452427548461927823961531 165678641322692891735942297)
          ·
            refine ⟨124258980992019668801956723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165678641322692891735942297 124258980992019668801956723)
            ·
              refine ⟨186388471488029503202935085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124258980992019668801956723 186388471488029503202935085)
              ·
                refine ⟨69895676808011063701100657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186388471488029503202935085 69895676808011063701100657)
                ·
                  refine ⟨52421757606008297775825493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69895676808011063701100657 52421757606008297775825493)
                  ·
                    refine ⟨614317471945409739560455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52421757606008297775825493 614317471945409739560455)
                    ·
                      rfl

theorem cell23_3589137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_3589137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589137 prefixEnd_3589137 := by exact prefixLift 3589137
  have htrace : WordTrace (prefixWord ++ tailWord_3589137) baseStart_3589137 baseEnd_3589137 := by
    simpa [prefixWord, tailWord_3589137, baseEnd_3589137] using wordTrace_append hprefix tailTrace_3589137
  have hstable : (prefixWord ++ tailWord_3589137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589137).length < 2 ^ (prefixWord ++ tailWord_3589137).sum := by decide
  have hdescent : baseEnd_3589137 < baseStart_3589137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
